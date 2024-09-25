# Implementation of source coding for binary input strings
#
'''
Sample program output:
    
Block length = 20
Total number of codewords =  1352
Encode 20 bits to 11.0 bits.
Compression rate =  0.55
Source data bits : [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
Decoded bits     : [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] 
'''

from math import comb
from numpy import random, log2, ceil

# Transform a bit string to a number using combinatorial number system
# input c is a list of 0 and 1
def bits_to_number(c):
    n = len(c)
    k = sum(c)  # number of 1 in c
    a = [i for i , m in enumerate(c) if m==1]  # locations of 1
    s = sum([comb(m,i+1) for i,m in enumerate(a)])
    for i in range(k):
        s += comb(n,i)  # add binomial coefficient comb(n,i)
    return s


# Recover the original bits
# n is the block length and W is the integeral representation
def number_to_bits(n,W): 
    k = 0  # determine the number of 1
    while W >= comb(n,k):
        W -= comb(n,k)
        k += 1
    d = []  # determine the locations of 1
    for j in range(k):
        for i in range(n+1):
            if comb(i,k) > W:
                break
        d.append(i-1)
        W -= comb(d[-1],k)
        k -= 1
    return [1 if i in d else 0 for i in range(n)]


# encode bit string to an integer
def encode (bits, n, limit):  
    k = sum(bits)  # number of 1 in k
    if k > limit:  # if the number of 1 in c exceed limit
        return sum([comb(n,i) for i in range(limit+1)])
    else:
        return bits_to_number(bits) # encode c using combinatorial number system


p = 0.2   # probability of 1
n = 20   # block length
max_no_of_one = 3

# M is the the number of codewords
M = sum([comb(n,i) for i in range(max_no_of_one+1)])

# Generate n bits randomly
input_bits = [1 if random.uniform(0,1) < p else 0 for _ in range(n)] # random bits

# encode the input bits into integer W 
# when the maximum number of one is less than or equal to max_no_of_one
W = encode(input_bits, n, max_no_of_one)  # encode a list of 0 and 1 into integer W

# Decode the data bits from integer W
# we have encoding error when the number of 1 is more than max_no_of_one
decoded_bits = number_to_bits(n,W)    # recover the list of 0 and 1 from W

print("Block length =",n)
print("Total number of codewords = ", M+1)
print(f"Encode {n} bits to {ceil(log2(float(M)))} bits.")
print("Compression rate = ", ceil(log2(float(M)))/n)
print("Source data bits :", input_bits)
print("Decoded bits     :", decoded_bits)

