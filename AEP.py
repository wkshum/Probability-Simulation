"""
Asymptotic Equipartition Property

Generate a random string with each letter generated independently according to 
a given distribution, and calculate the log of the probability that this particular
string is drawn.


A typical run of this program produces the following output:

acabcbabdabcaadaaaaaaababaabbaacaaaaaadaaccacababaababaababbbabbaababbcaadbaaabcbaaabbbacbaaaaadabab
a occurs 55 times
b occurs 30 times
c occurs 10 times
d occurs 5 times
log_2(probability) =  -160.0

Among the 100 random characters, 55 of them are 'a', 30 of them are 'b', 10 of them are 'c' and 5 of them are 'd'.
This is in accordance with the distribution [1/2, 1/4, 1/8, 1/8].
The log of the probability of this string (in base 2) is -160.

According to the weak law of large number, the log of probability is approximately equal to the entropy of the
distribution times the string length.
"""


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
