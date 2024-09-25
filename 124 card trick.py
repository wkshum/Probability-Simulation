# 124-card trick

from random import sample

print("Choose 5 numbers fom 0 to 123, without repetition")
samples = sample(range(124), 5) # generate 5 distinct numbers
samples.sort()  # sort the number in ascending order

print("The drawn numbers are ",samples)

###################
# Encoding

i = sum(samples)%5
L = samples[0:i]+samples[(i+1):5]

secret = samples[i]-i

print(f"Select {samples[i]} as the secret number")


p = secret//5   # p is between 0 to 23
d1 = p%2
d3 = p//6
d2 = (p - d1-d3*6)//2

L1 = [L[0]]
L2 =  L1[0:d1] + [L[1]] + L1[d1:]
L3 =  L2[0:d2] + [L[2]] + L2[d2:]
L4 =  L3[0:d3] + [L[3]] + L3[d3:]
# the numbers in L4 are displayed

print("Order the remaining four numbers as", L4)

########################
# decoding

D4 = L4.copy()
D4.sort()  # sort the numbers

# recover d1, d2 and d3
# e1 should equal to d1
# e2 should equal to d2
# e3 should equal to d3
e1 = sum([j<D4[1] for j in L4[0:L4.index(D4[1])]])
e2 = sum([j<D4[2] for j in L4[0:L4.index(D4[2])]])
e3 = sum([j<D4[3] for j in L4[0:L4.index(D4[3])]])
q = e1+2*e2+6*e3  # q should be the same as p

# sum of 4 numbers mod 5
s = sum(L4)%5

# secret1 is the smallestinteger larger than 5*p1 such that
# secret1 + s is divisible by 5
secret1 = q*5 + (-s)%5  

for i in range(5):
    D5 = L4+[secret1+i]
    D5.sort()
    if D5.index(secret1+i) == i:
        break
    
print(f"\nThe decoder obtains {secret1+i} from the four numbers and recover")
print(D5)
