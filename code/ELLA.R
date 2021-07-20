# MIT License
# 
# Copyright (c) 2021 Her Majesty the Queen in Right of Canada, Department of National Defence
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#   
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

require("dplyr")
require("ggplot2")
require("ggforce")
require("ggthemes")
# require("directlabels")
require("gghighlight")
require("concaveman")

# Create a single endurance-limited curve
# This is for a sub faster than the convoy
generateELLA <- function(s, k, R, t, minx = 0, maxx = 200, maxy = 300, granularity = 1) {
  
  if (minx== 0) {
    x = seq(-maxx,maxx,by=granularity) 
  } else {
    # Implementation note - if granularity is coarser than the minx or manx
    # value the result of this was not symmetric until adding the extra
    # step of producing the positive values from max downwards and then 
    # reversing them.  As minx is cac
    x = c(rev(seq(-minx, -maxx, by = -granularity)), seq(minx, maxx, by = granularity)) 
  }
  
  # first formula I derived - not as simple. Note there was a sign error in the SL.
  #y = s*t - x/tan(asin(x/(R+k*t)))
  
  # cleaner formula - simply a half circle shifted up by s*t
  y = -sqrt((R + k*t)^2 - x^2) + s*t
  
  
  ELLA = data.frame(x, y)
  
  ELLA = ELLA %>% mutate(y = replace(y, x == 0, -R - (k-s)*t)) %>% filter(!is.nan(y))
  
  endpoint = ELLA %>% tail(n=1)
  
  #print(endpoint$x)
  #print((R+k*t))
  #print(endpoint$x < (R+k*t))
  
  if((endpoint$y < maxy) & (endpoint$x > ((R+k*t)-.2))) {
    
    #print(endpoint$x)
    #print((R+k*t))
    #print(endpoint$x < (R+k*t))
    yPosTail = seq(endpoint$y, maxy, granularity)
    posTail = data.frame(x = rep(endpoint$x, length(yPosTail)), y = yPosTail)
    negTail = data.frame(x = rep(-endpoint$x, length(yPosTail)), y = yPosTail)
    ELLA = bind_rows(negTail,ELLA,posTail)
  }
  
  ELLA <- ELLA %>% filter(y < maxy)
  
  return(ELLA)
  
}

giveMeHull <- function (ELLAs) {
  X = data.matrix(ELLAs)
  # Plot (potentially with 0 size)
  #plot(X, cex = 0.1)
  # Find the convex hull of these points
  hpts <- chull(X)
  
  # hpts <- c(hpts, hpts[1]) # no longer add the last point to close the loop
  
  # Create a data frame from the convex hull of points, then order them by x
  # so that the lines trace in order from left to right
  dfY <- setNames(data.frame(X[hpts, ]), c("x","y"))
  dfY <- dfY[order(dfY$x),]
  
  # The above doesn't completely work if we've combined multiple ELLAs. 
  # What we want to keep is lowest x and highest x points on the top edge
  # These are the points in the top edge -  filter(y >= (max(y) - 1))
  # These are the lowest and highest -  filter(y >= (max(y) - 1)) %>% slice(1,n())
  # But really what we want is to keep all the points that aren't very close
  # to max y, while keep the lowest and highest x values, which gives us
  
  dfY <- dfY %>% filter(x == min(x) | x == max(x) | y <= (max(y) - 1))  

  
  # plot lines
  # lines(dfY)
  
  return(dfY)
}

giveMeTDZ <- function(R, granularity = 0.1) {
  
  circleX = seq(-R,R,granularity)
  negY <- data.frame(x=circleX, y=-sqrt(R^2-circleX^2))
  posY <- data.frame(x=rev(circleX), y=sqrt(R^2-circleX^2))
  
  return(bind_rows(negY,posY))
  
}

# This should be modified to account for maxy as well

giveMeStandardLLA <- function (s,k,R, maxx = 100, granularity = 0.1) {
  
  # find the y value where the standard LLA originate 
  b = -R*s/k
  
  LLAx = seq(-maxx, maxx, granularity)
  
  return(data.frame(x=LLAx, y= b + abs(LLAx)/(tan(asin(k/s)))))
  
} 

# For an endurance limited threat that is slower than the convoy,
# we have a LLA that is made up of four sections:
# - The TDZ itself directly behind the convoy,
# - The classical LLA from its intersection with the TDZ to its intersection 
#   with the isochron
# - The isochron from that tangent point to its maximum point in x
# - A line drawn directly forward from that point
#
# This is nearly equivalent to Fig. 2-9(c) (or (b) when s = k), except with
# the channel in front of the convoy (more pessimistic). It is however 
# more optimistic than simply considering the classical LLA.
giveMeASlowELLA <- function(s, k, R, t, maxx = 200, maxy = 300, granularity = 1) {
  if (k > s ) stop ("Sub faster than the convoy")
    
  # First we need to get the tangent intersection points, labelled
  # as point M'/N' and point M/N in Koopman.  
  
  n = giveMePointN(s,k,R,t)
  np = giveMePointNprime(s,k,R,t)

  
  # Take the TDZ portion by fitering for x lower than absolute value
  # of N' and negative y
  TDZ = giveMeTDZ(R, granularity) %>% filter(abs(x) <= np[1] & y < 0)
  
  
  # Take the classic LLA from M to M' and N to N' by giving the function N
  # as the maximum x value to use, then filtering out x values with absolute
  # value lower than that of N'
  #
  # If the point N is beyond the maximum x or y value, skip the
  # isochron and channel portion, as we're just looking at a classic
  # LLA situation within the bounds given
  
  if(n[1] < maxx & n[2] < maxy) {
    classic = giveMeStandardLLA(s,k,R,maxx = n[1], granularity) %>% filter(abs(x) >+ np[1])

    # Get the isochron portion plus channel portion
    theRest = generateELLA(s,k,R,t,minx = n[1], maxx = maxx, maxy = maxy, 
                         granularity = granularity)
  
    slowELLA = bind_rows(TDZ,classic,theRest) %>% arrange(x)
  } else {
    
    # This should be modified to take into account maxy as well
    classic = giveMeStandardLLA(s,k,R,maxx = maxx, granularity) %>% filter(abs(x) >+ np[1]) %>% filter(y <= maxy)
    slowELLA = bind_rows(TDZ,classic) %>% arrange(x)  
  }
  
  #return(n)
  return(slowELLA)
}



compareClassicToElla <- function(s, k, R, t, maxx = 200, maxy = 300, granularity = 1) {
  
  plot(giveMeStandardLLA(s,k,R, maxx = maxx, granularity = granularity),xlim=c(-maxx,maxx),ylim=c(-maxy,maxy), cex = 0.2)
  lines(giveMeTDZ(R, granularity = granularity))
  lines(generateELLA(s,k,R,t,maxx=maxx,maxy=maxy))
  

}

giveMePointN <- function (s,k,R,t){
  
  bigL = R*s/k + s*t
  angle = asin(k/s)
  distToN = bigL * cos(angle)
  x = distToN * cos(pi/2 - angle)
  y = distToN * sin(pi/2 - angle) - R * s/k
  
  return(c(x,y))
}

giveMePointNprime <- function (s,k,R,t){
  
  bigL = R*s/k
  angle = asin(k/s)
  distToN = bigL * cos(angle)
  x = distToN * cos(pi/2 - angle)
  y = distToN * sin(pi/2 - angle) - R * s/k
  
  return(c(x,y))
}

enduranceForSpeed <- function(k) {
  return(2000/k^2.5)
}

# Return the right zone for the speed
zoneForSpeed <- function(s, k, R, t, maxx = 200, maxy = 300, granularity = 1) {
  if (k < s) {
    return (giveMeASlowELLA(s,k,R,t,maxx=maxx,maxy=maxy,granularity=granularity))
  } else {
    return(generateELLA(s,k,R,t,maxx = maxx, maxy = maxy, granularity = granularity ))
  }
  
}

zoneForAShape <- function(s, mink, maxk, bag, maxx = 200, maxy = 300, granularity = 1) {
  
  eBase <- setOfELLAForSpeeds(s,mink,maxk,1,0,maxx,maxy,granularity)  
  
  eBase <- eBase %>% select(-k)
  
  for (i in 1:nrow(bag)) { 
    
    if(i == 1) {
      #first time through, make the current ELLA into a collection
      ELLAs <- eBase %>% mutate(x = x + bag[i,]$x, y = y + bag[i,]$y)
    } else {
      #otherwise, add to the collection
      temp <- eBase %>% mutate(x = x + bag[i,]$x, y = y + bag[i,]$y)
      ELLAs <- giveMeHull(bind_rows(ELLAs,temp))
    }
    
  } 
  
  return(giveMeHull(ELLAs))

}

zoneForACircle <- function(s, mink, maxk,R, maxx = 200, maxy = 300, granularity = 1) {
  
  radius = R
  theta = runif(1000, min = 0, max = 2*pi)
  x = radius * cos(theta)
  y = radius * sin(theta)
  
  bag <- data.frame(x=x, y=y)
  
  return(zoneForAShape(s,mink,maxk,bag,maxx = maxx, maxy=maxy, granularity=granularity))
  
  
}

zoneForASquare <- function(s, mink, maxk, L, maxx = 200, maxy = 300, granularity = 1) {
  
  maxValue = L/2
  points=seq(-maxValue,maxValue,granularity)
  steady = rep(maxValue,length(points))
  
  x=c(points,steady,-points,-steady)
  y=c(steady,-points,-steady,points)
  
  bag <- data.frame(x=x, y=y)
  
  return(zoneForAShape(s,mink,maxk,bag,maxx = maxx, maxy=maxy, granularity=granularity))
  
  
}

zoneForAMouse <- function(s, mink, maxk, R, maxx = 200, maxy = 300, granularity = 1) {
  
  
  
  # want to space 3 nm apart in a triangle
  # height of this triangle is 3 * sqrt(3)/2
  
  # top left corner
  x1 = -1.5
  y1 = (3*sqrt(3)/2)/2
  
  # top right corner
  x2 = -x1
  y2 = y1
  
  # bottom corner
  x3 = 0
  y3 = -y1
  
  
  eBase <- zoneForACircle(s,mink,maxk,R,maxx = maxx, maxy=maxy,granularity = granularity)
  
  e1 <- eBase %>% mutate(x = x + x1, y = y + y1)
  e2 <- eBase %>% mutate(x = x + x2, y = y + y2)
  e3 <- eBase %>% mutate(x = x + x3, y = y + y3)
  
  
  return(giveMeHull(bind_rows(e1,e2,e3)))
  
  
}


# This is really not working.
# Problem is that chull doesn't return actual data, it returns indicies of points.
# giveMeHull doesn't work as it discards a lot of data at the top end to deal with the ELLA
# Has to be an easier way to do this
makeAConvoy <- function(R) {
  
  radius = R
  theta = seq(0, 2*pi,0.01)
  x = radius * cos(theta)
  y = radius * sin(theta)
  
  baseCircle <- data.frame(x=x, y=y)
  
  # want to space 3 nm apart in a triangle
  # height of this triangle is 3 * sqrt(3)/2
  
  # top left corner
  x1 = -1.5
  y1 = (3*sqrt(3)/2)/2
  
  # top right corner
  x2 = -x1
  y2 = y1
  
  # bottom corner
  x3 = 0
  y3 = -y1
  
  
  
  e1 <- baseCircle %>% mutate(x = x + x1, y = y + y1)
  e2 <- baseCircle %>% mutate(x = x + x2, y = y + y2)
  e3 <- baseCircle %>% mutate(x = x + x3, y = y + y3)
  
  
  allCircles <- bind_rows(e1,e2,e3)
  
  hull <- concaveman(data.matrix(allCircles),concavity = 1)

  hull <- setNames(data.frame(hull), nm=c("x","y"))
  
  return(hull)
  
}


setOfELLAForSpeeds <- function(s, mink, maxk, kgran, R, maxx = 200, maxy = 300, granularity = 1) {
  for (k in seq(from = mink, to = maxk, by = kgran)) {
      eCurr <- zoneForSpeed(s,k,R,enduranceForSpeed(k),maxx=maxx,maxy=maxy, granularity = granularity) %>% mutate(k = k)
    
      if(k == mink) {
        #first time through, make the current ELLA into a collection
        ELLAs <- eCurr
      } else {
        #otherwise, add to the collection
        ELLAs <- bind_rows(ELLAs,eCurr)
      }
    
  } 
  
  return(ELLAs)
}


myELLA1 = generateELLA(10,11,5,enduranceForSpeed(11),maxy = 200, granularity = 0.1)
myELLA2 = generateELLA(10,12,5,enduranceForSpeed(12),maxy = 200, granularity = 0.1)
myELLA3 = generateELLA(10,13,5,enduranceForSpeed(13),maxy = 200, granularity = 0.1)
myELLAs = bind_rows(myELLA1, myELLA2, myELLA3)
overallHull <- giveMeHull(myELLAs)

#plot(overallHull, xlim=c(-100,100))
#lines(overallHull)
# plot(myELLA$x,myELLA$y)

overallHull %>% ggplot(aes(x=x, y=y)) + geom_line()

k = 8
s1 = giveMeASlowELLA(10,k,5,enduranceForSpeed(k), maxx = 75, maxy = 75, granularity = 0.01)
s1 <- s1 %>% mutate(k = k)
#s2 = giveMeASlowELLA(10,k,5,enduranceForSpeed(k), maxx = 100, maxy = 100, granularity = 0.01)
#s2 <- s2 %>% mutate(k = 11)

k = 12
f1 = generateELLA(10,k,5,enduranceForSpeed(k), maxx = 75, maxy = 75, granularity = 0.01)
f1 <- f1 %>% mutate(k = k)


bind_rows(s1,f1) %>% ggplot(aes(x = x, y = y, group=k, colour=k)) + geom_line()


ELLAs <- setOfELLAForSpeeds(10,4,20,1,5, maxx = 300, maxy = 200, granularity = 0.1)

ELLAs %>% ggplot(aes(x = x, y = y, group=k, colour=factor(k))) + geom_line() + 
  scale_colour_grey(start=0.6) + 
  gghighlight(k %in% c(17,4,8), unhighlighted_params = list(linetype = 3)) +
  coord_fixed() + theme_tufte() + theme(legend.position="none") +
  geom_circle(inherit.aes = FALSE, aes(x0 = x0, y0 = y0, r = r), 
              data = data.frame(x0 = c(0), y0 = c(0), r = c(5))) 

ggsave("output/Figure5.pdf", dpi=300, width=7,height = 4.5)


ELLAs %>% ggplot(aes(x = x, y = y, group=k, colour=factor(k))) + geom_line() + 
  gghighlight(k %in% c(17,4,8), unhighlighted_params = list(linetype = 3)) +
  coord_fixed() + theme_tufte() + theme(legend.position="none") +
  geom_circle(inherit.aes = FALSE, aes(x0 = x0, y0 = y0, r = r), 
              data = data.frame(x0 = c(0), y0 = c(0), r = c(5))) 

ggsave("output/Figure5.png", dpi=300, width=5,height = 5)

ELLAs %>% filter(abs(x) < 50) %>% filter(abs(y) < 50) %>% 
  ggplot(aes(x = x, y = y, group=k, colour=factor(k))) + geom_line() + 
  scale_colour_grey(start=0.6) + 
  gghighlight(k %in% c(17,4,8), unhighlighted_params = list(linetype = 3)) +
  coord_fixed() + theme_tufte() + theme(legend.position="none") +
  geom_circle(inherit.aes = FALSE, aes(x0 = x0, y0 = y0, r = r), 
              data = data.frame(x0 = c(0), y0 = c(0), r = c(5))) 

ggsave("output/Figure6.pdf", dpi=300, width=7,height = 4.5)

ELLAsk1 <- setOfELLAForSpeeds(10,4,20,1,5, maxx = 300, maxy = 600, granularity = 0.1)
ELLAskp5 <- setOfELLAForSpeeds(10,4,20,0.5,5, maxx = 300, maxy = 600, granularity = 0.1)
ELLAskp1 <- setOfELLAForSpeeds(10,4,20,0.1,5, maxx = 300, maxy = 600, granularity = 0.1)
bigHullk1 <- giveMeHull(select(ELLAsk1,-k)) %>% mutate(kgran = 1)
bigHullkp5 <- giveMeHull(select(ELLAskp5,-k)) %>% mutate(kgran = 0.5)
bigHullkp1 <- giveMeHull(select(ELLAskp1,-k)) %>% mutate(kgran = 0.1)
bigHulls <- bind_rows(bigHullk1,bigHullkp5,bigHullkp1)
bigHulls %>% ggplot(aes(x = x, y = y, group=kgran, colour=kgran)) + 
  geom_line() + coord_fixed() + theme_tufte()

bigHulls %>% ggplot(aes(x = x, y = y, group=kgran, linetype=factor(kgran))) + 
  scale_linetype_discrete(name="Granularity of k") + geom_line() + 
  theme_tufte() + coord_cartesian(xlim=c(-250,250),ylim=c(-25,500)) +
  geom_circle(inherit.aes = FALSE, aes(x0 = x0, y0 = y0, r = r), 
              data = data.frame(x0 = c(0), y0 = c(0), r = c(5))) + coord_fixed() 

ggsave("output/Figure8a.pdf",dpi=300,width=7.5,height=6.5,units="in")

bigHulls %>% ggplot(aes(x = x, y = y, group=kgran, linetype=factor(kgran))) + 
  scale_linetype_discrete(name="Granularity of k") + geom_line() +
  theme_tufte() + coord_fixed(xlim=c(-250,-200),ylim=c(425,475)) 

ggsave("output/Figure8b.pdf",dpi=300,width=7.5,height=6.5,units="in")

testk = seq(10,25,0.01)
#plot(testk,(2000*(testk-10)/testk^2.5))
#abline(v=(50/3))
ggplot() + geom_line(aes(x=testk,y=2000*(testk-10)/testk^2.5)) + 
  labs(x="Submarine speed (knots)", y = 'Maximum distance closed (nautical miles)') + 
  geom_vline(xintercept = 50/3, linetype = 2) + theme_tufte()

ggsave("output/Figure7.pdf",dpi=300,width=7.5,height=4.5,units="in")

#test4 <- zoneForAMouse(10,12,5,speedForEndurance(12),maxx=150,maxy=150)
worstConvoy = zoneForAMouse(10,4,20,5,maxx=150,maxy=150)
#test3 <- zoneForASquare(10,12,10,speedForEndurance(12),maxx=150,maxy=150,granularity =0.1)
worstSquare = zoneForASquare(10,4,20,5,maxx=150,maxy=150)
#test2 <- zoneForACircle(10,12,5,speedForEndurance(12),maxx=150,maxy=150)
worstCircle <- zoneForACircle(10,4,20,5,maxx=150,maxy=150)

t4 <- worstConvoy %>% mutate(k = 'three ships')
t3 <- worstSquare %>% mutate(k = 'square')
t2 <- worstCircle %>% mutate(k = 'circle')

convoyZone <- makeAConvoy(5)

bind_rows(t4,t3,t2) %>% ggplot(aes(x = x, y = y, group=k, linetype=k)) + 
  geom_line() + 
  scale_linetype_manual(name="Danger zone", breaks=c("circle","square","three ships",""), 
                        values=c(3,2,1,3)) + 
  geom_circle(inherit.aes = FALSE, linetype=3, aes(x0 = x0, y0 = y0, r = r), 
              data = data.frame(x0 = c(0), y0 = c(0), r = c(5))) + 
  coord_fixed(xlim=c(-35,35),ylim=c(-20,10)) + 
  geom_path(inherit.aes = FALSE, linetype = 2, aes(x=x,y=y), 
            data = data.frame(x=c(-5,5,5,-5,-5), y=c(5,5,-5,-5,5))) + 
  geom_path(inherit.aes = FALSE, linetype = 1, aes(x=x,y=y), data = convoyZone) +
  theme_tufte()

ggsave("output/Figure9.pdf",dpi=300,width=7.5,height=3.5,units="in")

makeAConvoy(5) %>% ggplot(aes(x=x, y=y)) + geom_path() + coord_fixed()

# geom_circle(inherit.aes = FALSE, aes(x0 = x0, y0 = y0, r = r), data = data.frame(x0 = c(0), y0 = c(0), r = c(5)))




#notionSub = data.frame(k=c(3:24),t=c(48.28,46.44,39.34,30.65,23.55,21.90,18.81,14.60,12.26,10.3,9.07,7.76,6.97,5.92,4.6,4.07,3.2,2.23,1.49,1.18,0.83,0.65))


notionSub = data.frame(k=c(3:24),t=c(48.28,46.44,39.34,30.65,23.55,21.90,18.81,14.60,12.26,10.3,9.07,7.76,6.97,5.92,4.6,4.07,3.2,2.23,1.49,1.18,0.83,0.65))
notionSub <- mutate(notionSub,Submarine="Akbori")

equationSub <- data.frame(k=c(3:24)) %>% mutate(t=2000/k^2.5,Submarine="Equation")


twoSubs <- bind_rows(notionSub,equationSub)
twoSubs %>% filter(k>3) %>% ggplot(aes(x=k,y=t,group=Submarine,linetype=Submarine)) + labs(x="Submarine Speed (knots)", y="Endurance (hours)") + geom_line() + theme_tufte()

