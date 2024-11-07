# Implementation of maximal coupling
#
# We are given two distributions on Omega = {1,2,3} 
# P(1)=0.3, P(2)=0.4, P(3)=0.3
# Q(1)=0.25, Q(2)=0.25, Q(3)=0.5
#
# The two lists pairs and dist implement the joint distribution

from numpy import random
from itertools import accumulate
import matplotlib.pyplot as plt

# joint distribution
pairs = [(1,1),(1,3),(2,2),(2,3),(3,3)]
dist = [0.25, 0.05, 0.25, 0.15, 0.3]   # prob. mass function

cum_dist = list(accumulate( dist, lambda x,y: x+y))

# sample from the joint distribution
def sample():
    u = random.uniform(0,1)     # generate uniform r.v.
    return pairs[sum([u > p for p in cum_dist])] 

# generate 10000 samples
samples = [sample() for _ in range(10000)]


# plot the two marginal distributions
fig, (ax1, ax2) = plt.subplots(2, sharex=True)
ax1.hist(list(map((lambda z : z[0]), samples)), bins=[1,2,3,4], edgecolor="yellow",)
ax2.hist(list(map((lambda z : z[1]), samples)), bins=[1,2,3,4], edgecolor="yellow",)

# the probability that X=Y is 0.8 in theory
print('P(X=Y) = ',sum(list(map(lambda z: z[0]==z[1], samples)))/10000)
