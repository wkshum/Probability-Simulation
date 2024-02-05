# -*- coding: utf-8 -*-
"""
Created on Mon Jan  2 12:58:20 2023

@author: User
"""
# Probability of a random string
from random import choices
from numpy import log2

A = ['a','b','c','d']   # alphabet
prob_dist = [1/2, 1/4, 1/8, 1/8]  # probability distribution
n= 100  # string length 

s = choices(A,weights=prob_dist, k = n)  # draw n letters randomly

count = [ sum([ x == y for x in s]) for y in A]
p = sum([log2(t[0]**t[1]) for t in zip(prob_dist,count)])

print(''.join(s)) # print random string
for x in zip(A,count):
    print(f"{x[0]} occurs {x[1]} times")
print('log_2(probability) = ',p)