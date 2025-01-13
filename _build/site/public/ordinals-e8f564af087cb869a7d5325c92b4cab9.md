# Ordinal numbers

It will be important for us to extend the usual counting process beyond the natural numbers. To give an example, let us return for a moment to perfect subsets of the reals. To show that every uncountable closed subset of $\mathbb{R}$ contains a perfect subset, we considered the *condensation points* of the set. There is another, more gradual way, to arrive at a perfect subset. When Cantor studied convergence of Fourier series, he introduced the **derivative** of a set: 
$$
A' = \{ x \in A \colon x \text{ is a limit point of } A\}
$$
We can iterate the derivative and consider $A^\prime, A^{\prime\prime}, A^{\prime\prime\prime}, \dots$. This yields a descending sequence of sets
$$
A^\prime \supseteq  A^{\prime\prime} \supseteq A^{\prime\prime\prime} \supseteq \dots \supseteq A^{(n)} \supseteq \dots
$$

```{exercise} 
:nonumber: true

Find a set $A$ such that for all $n$, $A^{(n)} \supsetneq A^{(n+1)}$.
```
As the sequence is nested, we can take a “limit”:
$$
A^{\infty} = \bigcap_n A^{(n)}
$$
But the process does not necessarily stop here. $A^\infty$ may have isolated points again, so that $A^\infty \supsetneq (A^\infty)^\prime$. 

```{exercise}
:nonumber: true

Find a set $A$ such that $A^\infty \supsetneq (A^\infty)^\prime$.
```
Let us introduce $\omega$ as a new number to be used in place of $\infty$ above. We can continue the counting process:
$$
1,2,3, \dots, \omega, \omega+1, \omega+2, \dots, \omega + \omega, \omega + \omega +1, \dots, \omega + \omega + \omega, \dots, \omega\cdot \omega, \dots
$$

We can then define, for example,
$A^{\omega+1} := (A^{\omega})'$. As intuitively clear from above, the new transfinite numbers come with a natural ordering, so we can also put $A^{\omega+\omega} := \bigcap_{\alpha < \omega+\omega} A^{\alpha}$

Another way to count into the transfinite is to reorder the natural numbers and first enumerate all powers of two, followed by all powers of three and so on:
\begin{gather*}
	1, 2, 4, 8, \ldots 3, 9, 27, \ldots 5, 25, 125, \ldots
\end{gather*}
This still leaves an infinite reservoir of numbers like $0, 6, 10, \dots$. 

A number of questions arises: 
- Can this process continued indefinitely?
- Is there a *unifying* principle behind the various ways to count into the transfinite?
- Can we define operations like $+$ and $\cdot$ on these infinite numbers independent of the way we represent these numbers, and without leading to contradictions?

These questions can be addressed by developing the theory of *ordinal numbers* via the concept of a *well-founded order*.

## Orders and well-orders


```{prf:definition}
:nonumber: true

A (**reflexive** or **non-strict**) **partial order** on a set $A$ is a binary relation $\leq$ on $A$ such that for all $a,b,c \in A$,
-  $a\leq a$ &emsp; (reflexive)
-  $a \leq b \; \wedge \; b \leq a \quad \Rightarrow \quad a = b$ &emsp; (anti-symmetric)
 
-  $a \leq b$ and $b \leq c$ implies $a \leq c$ &emsp; (transitive).

A **linear** (or **total**) **order** additionally satisfies for all $a,b \in A$,
-  $a \leq b$ or $b \leq a$  &emsp; (connected).
```
