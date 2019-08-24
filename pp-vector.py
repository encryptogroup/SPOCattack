#(c) 2019 Cryptography And Privacy Engineering Group, TU Darmstadt
#by Amos Treiber

import gmpy2
import os
import random
import math
from random import randrange, getrandbits, SystemRandom, randint
import matplotlib.pyplot as plt

def gen_prime(N):
	randfunc = SystemRandom()
	r = gmpy2.mpz(randfunc.getrandbits(N))
	r = gmpy2.bit_set(r, N - 1)
	return gmpy2.next_prime(r)

def eq_digits(n, A, B):
	res = True
	for i in range(n): #we just compare the first n digits here
		res = res and (A[i] == B[i])
	return res

#Parameters
iter = 1000 #amount of iterations for evaluating correctness and the attacks
eval_randoma = True #set to false to evaluate with a=0
eval_randomb = True #set to false to evaluate random b and b' s.t. |b'-b|=1
F = 256 #Vector dimension
k1 = 512
k2 = 200
k3 = 128
q = 32

n = F + 2
no_digits = 3 #no. of digits to compare for ditinguishing different b
if not eval_randomb:
	no_digits = 26 #decreases overall accuracy but increases efficiency for the case |b'-b|=1

correct_all = []
atk_correct_all = []
overflow_all = []
k4list = [128, 144, 160, 176, 192, 200, 216, 228, 230, 236, 240, 256, 272, 288, 304, 320, 326, 332, 334, 336, 352, 368, 384, 400, 416, 432, 448, 464, 480, 496, 512]

randfunc = SystemRandom()
seed = gmpy2.random_state(randfunc.randint(0, 2**64 - 1))

print("Starting the evaluation...")

#evaluate protocol correctness as well as attack success rate
#For the attack, generate random C mod p, a and two different random bs. The adversary will know b_0 and b_1, but will only receive a D_sum depending on b_choice, where choice is a random bit that the adversary will then try to guess.
for k4 in k4list:
	correct = 0
	atk_correct = 0
	overflow = 0

	for eval_correctness in [True, False]:
		for x in range(0,iter):
			alpha = gen_prime(k2)
			p = gen_prime(k1)

			c = []
			C = []
			b0 = []
			b1 = []
			a = []
			choice = randfunc.randint(0, 1)

			s = gmpy2.mpz_random(seed, p)

			for i in range(n):
				if eval_correctness:
					a.append(gmpy2.mpz_urandomb(seed,q))
					b0.append(0)
					b1.append(0)
				else:
					if eval_randoma:
						a.append(gmpy2.mpz_urandomb(seed,q)) 
					else:
						a.append(0)
					b0.append(gmpy2.mpz_urandomb(seed,q))
					if eval_randomb:
						b1.append(gmpy2.mpz_urandomb(seed,q))
					else:
						b1.append(b0[i])

			if not eval_randomb:
				b1[10] = b0[10] + 1 #b0 and b1 only differ by 1 at an arbitrary position

			a[F] = 0
			a[F+1] = 0
			b0[F] = 0
			b0[F+1] = 0
			b1[F] = 0
			b1[F+1] = 0

			b = [b0, b1]

			plain_res = 0
			for i in range(n):
				plain_res += a[i]*b[choice][i]

			#build C like in the protocol
			for i in range(0,n):
				c.append(gmpy2.mpz_urandomb(seed, k3))
				if a[i] == 0:
					C.append(gmpy2.mul(s, c[i]))
				else:
					C.append(gmpy2.mul(s, gmpy2.add(gmpy2.mul(alpha, a[i]), c[i])))

			#build D like in the protocol
			D = []
			for i in range(0,n):
				if b[choice][i] != 0:
					aC = gmpy2.mul(gmpy2.mul(b[choice][i], alpha), C[i])
					D.append(gmpy2.f_mod(aC, p))
				else:
					r = gmpy2.mpz_urandomb(seed,gmpy2.mpz(k4))
					#r = gmpy2.mpz(2)**k4
					#r = gmpy2.sub(r, gmpy2.mpz(1))
					D.append(gmpy2.f_mod(gmpy2.mul(r, C[i]), p))

			D_sum = gmpy2.mpz(0)
			for i in range(0,n):
				D_sum = gmpy2.add(D_sum, D[i])

			D_sum = gmpy2.f_mod(D_sum, p)

			#P_0 retrieves E:
			sI = gmpy2.invert(s, p)
			E = gmpy2.f_mod(gmpy2.mul(sI, D_sum), p)

			if eval_correctness:
				#Evaluate Correctness of Protocol
				res = gmpy2.sub(E, gmpy2.f_mod(E, gmpy2.mul(alpha,alpha)))
				res = gmpy2.t_div(res, gmpy2.mul(alpha,alpha))
				correct += abs(res - plain_res)
				#print("plaintext result:" + str(plain_res))
				#print("protocol result:" + str(res) + "\n")
			else:
				#Evaluate the Attack by computing E'=E/alpha
				Ep = gmpy2.t_div(E, alpha)

				s_Ep = gmpy2.digits(Ep)

				b0a = [gmpy2.mul(gmpy2.mul(ai,b),alpha) for b,ai in zip(b0, a)]
				b1a = [gmpy2.mul(gmpy2.mul(ai,b),alpha) for b,ai in zip(b1, a)]

				b0c = [gmpy2.mul(b,ci) for b,ci in zip(b0, c)]
				b1c = [gmpy2.mul(b,ci) for b,ci in zip(b1, c)]

				s_0b = gmpy2.mpz(0)
				s_1b = gmpy2.mpz(0)
				for j in range(n):
					if a[j]!= 0:
						s_0b = gmpy2.add(s_0b, b0a[j])
						s_1b = gmpy2.add(s_1b, b1a[j])
					else:
						s_0b = gmpy2.add(s_0b, b0c[j])
						s_1b = gmpy2.add(s_1b, b1c[j])

				diff0 = gmpy2.sub(Ep, s_0b)
				overflow0 = gmpy2.log2(diff0)
				diff1 = gmpy2.sub(Ep, s_1b)
				overflow1 = gmpy2.log2(diff1)
				s_0b = gmpy2.digits(s_0b)
				s_1b = gmpy2.digits(s_1b)

				#print("\na: " + str(a))
				#print("b0: " + str(b0))
				#print("b1: " + str(b1))
				#print("choice: " + str(choice))
				#print("s_Ep: " + s_Ep)
				#print("s_0b: " + s_0b)
				#print("s_1b: " + s_1b)

				guess = eq_digits(no_digits, s_Ep, s_1b)

				if not choice:
					#print("overflow was: " + str(overflow0) + " bits.")
					overflow += overflow0
				else:
					#print("overflow was: " + str(overflow1) + " bits.")
					overflow += overflow1

				atk_correct += choice == guess



	print("=> Evaluated " + str(iter) + " protocol executions with n=" + str(F) + " " + str(q) + "-bit vectors, k1=" + str(k1) + ", k2=" + str(k2) + ", k3=" + str(k3) + ", and k4=" + str(k4) + ".")
	print("=> Out of those executions, the average correctness error was " + str(correct/iter) + ".")
	print("=> Our attack successfully distinguished random vectors " + str(atk_correct) + " times. The average overflow was " + str(overflow/iter) + " bits.")

	correct_all.append(correct/iter)
	atk_correct_all.append(atk_correct/iter)
	overflow_all.append(overflow/iter)


fig, ax1 = plt.subplots()

color = 'tab:red'
ax1.set_xlabel('k4')
ax1.set_ylabel('attack success rate', color=color)
ax1.plot(k4list, atk_correct_all, color=color)
ax1.tick_params(axis='y', labelcolor=color)

ax2 = ax1.twinx()

color = 'tab:blue'
ax2.set_ylabel('protocol correctness error', color=color)
ax2.plot(k4list, correct_all, color=color)
#ax2.set_yscale('log')
ax2.tick_params(axis='y', labelcolor=color)

fig.tight_layout()

import tikzplotlib

tikzplotlib.save("protocol_eval_plot.tex")