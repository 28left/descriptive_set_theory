# Coding Borel Sets

In this chapter, we take a further look at Borel subsets of $\Baire$. As is common in this setting, we call the elements of $\Baire$ **reals**. This is motivated by the fact that, via the continued fration expansion, $\Baire$ [is homeomorphic to the set of irrational real numbers](#fact-paths-as-reals). Suppose $U \subseteq \Baire$ is open. Then there exists a set $W \subseteq \Nstr$ such that

$$ 
U = \bigcup_{\sigma \in W} \Cyl{\sigma}. 
$$

Using a standard (effective) coding procedure, we can identify a finite sequence of natural numbers with a natural number, and thus can see $W$ as a subset of $\Nat$.

If we provide a Turing machine with oracle $W$, we can semi-effectively test for membership in $U$ as follows. Assume we want to determine whether some $\alpha \in \Baire$ is in $U$. Write ${}\alpha$ on another oracle tape, and start scanning the $W$ oracle. If we retrieve a ${}\sigma$ that coincides with an initial segment of ${}\alpha$, we know $\alpha \in U$. On the other hand, if $\alpha \in U$, then we will eventually find some $\alpha\Rest{n}$ in $W$. If $\alpha \not\in U$, then the search will run forever. In other words, given $W$, $U$ is **semi-decidable**, or, extending terminology from subsets of $\Nat$ to subsets of $\Baire$, $U$ is
**recusively enumerable** (r.e.) relative to $W$.

Similarly, we can identify a closed set $F$ with the code for the tree

$$ 
T_F = \{\alpha\Rest{n} \colon \alpha\in F,\, n\in \Nat \}.
$$

Then determining whether $\alpha \in F$ is **co-r.e.** in (the code of) $T_F$. If $\alpha \not\in F$ we will learn so after a finite amount of time.

These simple observations suggest the following general approach to Borel sets.

> - Borel sets can be coded by a single infinite sequence in $\Baire$ (or $\Cant$).
> - Given the code, we can recover the Borel set effectively, by means of oracle computations.
> - The connection between degrees of unsolvability and definability results in a close correspondence between arithmetical sets ($\Sigma^0_n$) and Borel sets of finite order ($\bSigma^0_n$). 

In this lecture we will fully develop this correspondence. Later, we will see that it even extends beyond the finite level. 

## Some notation for reals, strings, and numbers

We fix a computable bijection $\pi: \Nat \to \Nstr$. In general, we will often use string and their images under ${}\pi$ interchangeably, that is, for example, if $A \subset \Nat$, we will write $\sigma \in A$ to denote $\pi(\sigma) \in A$.
We will also freely identify infinite binary sequences with the set of natural numbers they represent as their characteristic function. 

Furthermore, let $\Tup{.,.}$ be the standard coding function for pairs,

$$ 
\Tup{x,y} = \frac{(x+y)(x+y+1)}{2}+y.
$$

Finally, let us define the following operations on elements of Baire (or Cantor) space: Given $\beta\in \Baire$, 
- Let $\beta'$ be the real defined by $\beta'(n) = \beta(n+1)$. (*We cut the first entry.*)
- On the other hand, if $k \in \Nat$ and $\beta \in \Baire$, we obtain a new element of $\Baire$, which we denote by $(k, \beta)$, by **concatenating** $k$ and ${}\beta$.
- For $m \geq 0$, let $(\beta)_m$ be the **$m$-th column** of ${}\beta$, $(\beta)_m(n) = \beta(\Tup{m,n})$.


## Borel codes of finite order


Borel codes are defined inductively. 

```{prf:definition}
:label: def-Borel-codes
:nonumber: true

Let $\gamma \in \Baire$.

- Suppose $\gamma \in \Baire$ is such that $\gamma(0) = 1$. ${}\gamma$ **is a $\bSigma^0_1$ code** for the open set 
\begin{equation*}
    U = \bigcup_{\gamma(\sigma) = 0} \Cyl{\sigma}
\end{equation*}

- If ${}\gamma$ is such that $\gamma(0)=2$ and $\gamma'$ is a $\bSigma^0_n$ code for $A \subseteq \Baire$, we say ${}\gamma$ **is a $\bPi^0_n$ code** for $\Co{A}$.

- If ${}\gamma$ is such that $\gamma(0)=3$ and for each $m$, $(\gamma')_m$ is a $\bPi^0_n$ code of a set $A_m$, we say ${}\gamma$ **is a $\bSigma^0_{n+1}$ code** for $\bigcup_n A_n$.
```

The first position in each code indicates the kind of set it codes - an open set, a complement, or a union. 

Note that the definition of Borel code actually assigns codes to **representations of sets**. A Borel set can have (and has) multiple codes, just as it has multiple representations. We can, for example, represent an open set by different sets $W$ of initial segments. 

Moreover, every $\bSigma^0_1$ set is also $\bSigma^0_2$, and thus a set has codes which reflect the more complicated definition of the $\bSigma^0_1$ set as a union of closed sets. It is useful to keep this distinction between a Borel set and its Borel representation in mind.

The following is a straightforward induction.

```{prf:proposition}
:label: prop-Borel-codes

Every $\bSigma^0_n$ ($\bPi^0_n$) set has a $\bSigma^0_n$ ($\bPi^0_n$) Borel code, and every $\bSigma^0_n$ ($\bPi^0_n$) code represents a $\bSigma^0_n$ ($\bPi^0_n$) set.
```

<!-- The proposition actually holds for *all* Borel sets, which can be proved by **transfinite induction**. However, we have not introduced Borel sets of transfinite order yet, so we state the existence of codes only for $\bPi^0_n$ ($\bSigma^0_n$) sets. In the next chapter, we will study the *full* Borel hierarchy, and then it should be clear that the above proposition extends to all Borel sets.  -->


<!-- ## The tree structure of Borel codes

Each Borel code induces a tree structure that reflects how the corresponding Borel set is built up from closed sets.
The terminal nodes are given by codes for closed sets (the ones starting with "$2$"), since they are the ``building blocks'' of the Borel sets and hence are not extend/split further. A "$3$-code" represents a node  with just one immediate successor, while a "$4$-code" corresponds to a node with infinitely many immediate successors. Given a Borel code ${}\gamma$, we **denote the corresponding tree by $T_\gamma$**.

The tree of a Borel code defined this way **is always well-founded** (i.e. has no infinite path), since a Borel code is defined via a well-founded recursion. The rank of the tree is a countable ordinal. 

How hard is it to decide whether a given real is a Borel code? We will see later that this question is quite difficult. More precisely, we will see that the **set $\Op{Bc}$ of all Borel codes is not Borel**. Deciding whether a tree on $\Nat$ is well-founded will play a fundamental role in this regard.

The tree structure of a code also lets us assign levels to a Borel code similar to the levels of the Borel hierarchy:

- Trees with a single node $(2)$ correspond to **$\bPi^0_1$ codes**. 
- If $T$ is a $\bPi^0_n$ ($\bSigma^0_n$) code, then the tree with new top node $(3)$ represents a $\bSigma^0_n$ ($\bPi^0_n$) code. 
- And if $T_n$ is a sequence of $\bPi^0_n$ codes, then the tree with new top node $(4)$ and each $T_n$ directly below it corresponds to a **$\bSigma^0_{n+1}$ code**.
 -->


## Computing with Borel codes

Suppose ${}\gamma$ is a **computable** code for an $F_\sigma$ set $B$. We may assume ${}\gamma$ is of the form $(3,\gamma')$, with each column $(\gamma')_m$ being of the form $(2,1,(\alpha)_m)$, coding a closed set $F_m$.

With this, we can express membership in $B$ as follows:

\begin{align*}
    \beta \in B \quad & \Leftrightarrow \quad \exists m \: [\text{$\beta$ is in the set coded by $(\gamma')_m$}] \\
        & \Leftrightarrow \quad \exists m \forall n \: [\beta\Rest{n} \text{ is not in the set coded by } (\alpha)_m]. \\
        & \Leftrightarrow \quad \exists m \forall n \: [(\alpha)_m(\beta\Rest{n}) \neq 0 ].
\end{align*}

Note that, since we assume ${}\gamma$ to be computable, the **inner predicate** $R(m,\sigma)$ given by

$$
R(m,\sigma) :\iff (\alpha)_m(\sigma) \neq 0
$$

is **decidable**, that is, it can be decided by a Turing machine.

Hence any $\bSigma^0_2$ set $B$ with a computable code can be represented in the following form:

> There exists a decidable predicate $R(m,\sigma)$ such that
> $$\beta \in B \quad \iff \quad \exists m \: \forall n \; R(m, \beta\Rest{n}).$$ 

Conversely, if $R(m,\sigma)$ is a (decidable) predicate, let

$$
F_m = \{ \beta \colon \forall n \: R(m,\beta\Rest{n}) \}.
$$

We claim that $F_m$ is closed: Define a tree $T_m$ by letting

$$
\sigma \in T_m : \iff \forall \tau \Sleq \sigma \: R(m, \tau).
$$

Then $[T_m] = F_m$. Moreover, 

$$
\beta \in \bigcup_m F_m \iff \exists m \forall n \: R(m,\beta\Rest{n})
$$

Thus, there seems to be a close connection between $F_\sigma$ sets with computable Borel codes and sets definable by $\Sigma^0_2$ formulas over computable predicates. Given that we introduced the notation $\bSigma^0_2$ for $F_\sigma$ sets earlier, this is perhaps not very surprising.

In this analysis, there seems to be nothing specific about the $F_\sigma$ set used in the example. Indeed, it can be extended to Borel sets of finite order, which we will do next. 

We will introduce the 
**lightface** Borel hierarchy and show that it corresponds to Borel sets of finite order with recursive codes. Using **relativization**, we then obtain a complete characterization of Borel sets of finite order: *They are precisely those sets definable by arithmetical formulas, relative to a real parameter.*

But before we do that, we observe a basic fact about how we can compute with codes.


## The effective Borel hierarchy

```{prf:remark}
:nonumber: true

You may notice some sloppy notation in the third item here, since as written the set $P$ should technically be a subset of $\Nat\times \Baire$. We will put this on more solid footing in the next chapter. For now, you can think of $\Nat \times \Baire$ as the same as $\Baire$ -- just "merge" the pair into one real.
```
```{prf:definition} The Lightface Hierarchy
:nonumber: true 
:label: def-effective-Borel

A set $A \subseteq \Baire$ is 
- (lightface) $\Sigma^0_1$ if there exists a computable predicate $R(\sigma)$ such that
\begin{equation*}
    \alpha \in A \iff \exists k \: R(\alpha\Rest{k}),
\end{equation*}
- (lightface) $\Pi^0_n$ if $\Co{A}$ is $\Sigma^0_n$,
- (lightface) $\Sigma^0_{n+1}$ if there exists a $\Pi^0_n$ set $P$ such that
\begin{equation*}
    \alpha \in A \iff \exists n \; (n,\alpha) \in P. 
\end{equation*}
```
The following is an easy induction.

```{prf:proposition}

A set $A \subseteq \Baire$ is $\Sigma^0_n$ if and only if there exists a computable relation $R \subseteq \Nat^n$ such that
$$
  \alpha \in A \; \iff \; \exists k_1 \forall k_2 \exists k_3 \dots Q k_n \; R(k_1, k_2, k_3 \dots, \alpha\Rest{k_n}).
$$ 
Similarly, a set $A \subseteq \Baire$ is $\Pi^0_n$ if and only if there exists a computable relation $R \subseteq \Nat^n$ such that

$$
  \alpha \in A \; \iff \; \forall k_1 \exists k_2 \forall k_3 \dots Q k_n \; R(k_1, k_2, k_3 \dots, \alpha\Rest{k_n}).
$$ 
```

The following result is at the heart of the effective theory. 

```{prf:proposition}
:label: prop-computable-codes 
A set $A \subseteq \Baire$
is (lightface) $\Sigma^0_n$ ($\Pi^0_n$) if and only if it has a computable $\bSigma^0_n$ ($\bPi^0_n$) code.
```

````{prf:proof}
:class: dropdown
:nonumber: true

($\Rightarrow$) We proceed by induction on the Borel complexity. 

Suppose $A$ is $\Sigma^0_1$. Let $R$ be computable such that $A = \{ \alpha \colon \exists n \: R(\alpha\Rest{n})\}$. Let

$$
    W = \{ \sigma \in \Nstr \colon R(\sigma)\}.
$$

We have $\alpha \in A$ if and only if $\alpha \in \bigcup_{\sigma \in W} \Cyl{\sigma}$.
Since $R$ is decidable, $W$ is computable and $\gamma \in \Baire$ given by

$$
\gamma(n) = 
	\begin{cases}
		1 & n = 0, \\
		0 & n \geq 1 \: \& \: \pi(n-1) \in W,\\
		17 & n \geq 1 \: \& \: \pi(n-1) \notin W, 
	\end{cases}
$$

is a computable $\bSigma^0_1$ code for $A$. 

If $A$ is $\Pi^0_n$, then $A = \Co{B}$ for some $\Sigma^0_n$ $B$. By inductive hypothesis, $B$ has a computable $\bSigma^0_n$ code ${}\gamma$. Then $(2,\gamma)$ is a computable $\bPi^0_n$ code for $A$.

Finally, assume that $A$ is $\Sigma^0_{n+1}$. Let $P$ be $\Pi^0_n$ such that $\alpha \in A \iff \exists n \; (n,\alpha) \in P$.

By inductive hypothesis, $P$ has a computable $\bPi^0_n$ code ${}\gamma$.
If we let $P_m = \{\beta \colon (m,\beta) \in P\}$, then $A = \bigcup P_m$. Thus, it suffices to show that we can uniformly obtain codes for $P_m$. 

```{prf:lemma}
:label: lem-Borel-codes-shift

Suppose ${}\gamma$ is a Borel code of finite order representing a set $B \subseteq \Baire$. Then can, uniformly in ${}\gamma$ and $k$, compute Borel codes of the same Borel complexity as ${}\gamma$ for the set

$$
B'_k = \{ \delta \colon (k, \delta) \in B\}
$$
```

We leave the proof as an exercise. Proceed by induction on the Borel complexity of ${}\gamma$. 




($\Leftarrow$) We proceed by induction on the complexity of the code ${}\gamma$.

If ${}\gamma$ is of the form $(1,\alpha)$, with ${}\alpha$ coding an open set $U$. Then 

$$
\beta \in U \iff \exists n \: \alpha(\beta\Rest{n})= 0.
$$

Since ${}\gamma$ is assumed to be computable, the computable relation 

$$
R(\sigma) :\iff \alpha(\sigma) = 0
$$

witnesses that $U$ is $\Pi^0_1$. 

If $\gamma = (2, \alpha)$ is a $\bPi^0_n$ code, then ${}\alpha$ is a $\bSigma^0_n$ code. By inductive hypothesis, the set coded by ${}\alpha$ is $\Sigma^0_n$, so by definition of the effective hierarchy and the Borel codes, ${}\gamma$ codes a $\Pi^0_n$ set.

Finally, assume $\gamma = (3,\alpha)$ is a $\bSigma^0_{n+1}$ code for a set $B$. Then each $(\alpha)_m$ is a $\bPi^0_n$ code for a set $A_m$.

```{prf:lemma}
:label: lem-Borel-codes-inverse-shift

If $(\alpha_m)$ is a uniformly computable sequence of $\bPi^0_n$ codes for sets $A_m$, respectively, then there exists a $\bPi^0_n$ code ${}\alpha$ for the set

$$
    A = \{(m,\beta) \colon \beta \in A_m\}
$$
```

The proof is similar to {prf:ref}`lem-Borel-codes-shift`

By inductive hypothesis, the set $A$ as in the Lemma is $\Pi^0_n$ and we have

$$
    \beta \in B \iff \exists m (m, \beta )\in A,
$$

which implies $B$ is $\Sigma^0_{n+1}$.
````


## Relativization

Using relativized computations via oracles, we can define a relativized version of the effective Borel hierarchy. This way we can capture *all* Borel sets of finite order, not just the ones with computable codes.

```{prf:definition}
:nonumber: true
Let $\gamma \in \Baire$. A set $A \subseteq \Baire$ is 
-  $\Sigma^0_1(\gamma)$ &nbsp; if there exists a predicate $R(x)$ computable in ${}\gamma$ such that
\begin{equation*}
\alpha \in A \iff \exists n \: R(\alpha\Rest{n}),
\end{equation*}
-  $\Pi^0_n(\gamma)$ &nbsp; if $\Co{A}$ is $\Sigma^0_n(\gamma)$,
-  $\Sigma^0_{n+1}(\gamma)$ &nbsp; if there exists a $\Pi^0_n(\gamma)$ set $P$ such that
\begin{equation*}
\alpha \in A \iff \exists n \;[(n,\alpha) \in P].
\end{equation*}
```

A straightforward relativization gives the following analogue of {prf:ref}`prop-computable-codes`.

```{prf:proposition}
:label: prop-relative-codes 

Let $A \subseteq \Baire$ and $\gamma \in \Baire$. 
$A$ is $\Sigma^0_n(\gamma)$ ($\Pi^0_n(\gamma)$) if and only if $A$ has a $\bSigma^0_n$ ($\bPi^0_n$) code computable in ${}\gamma$. 
```

We can now present the **fundamental theorem of effective descriptive set theory**.

```{prf:theorem}
:label: thm-fundamental 

A set $A \subseteq \Baire$ is $\bSigma^0_n$ ($\bPi^0_n$) if and only if it is $\Sigma^0_n(\gamma)$ $(\Pi^0_n(\gamma))$ for some $\gamma \in \Baire$. 
```

```{prf:proof}
:class: dropdown
:nonumber: true

If $A$ is $\bSigma^0_n$, then by {prf:ref}`prop-Borel-codes` it has a $\bSigma^0_n$-code ${}\gamma$, and by {prf:ref}`prop-relative-codes`, $A$ is $\Sigma^0_n(\gamma)$. The other direction follows immediately from {prf:ref}`prop-relative-codes`.

The argument for $\bPi^0_n$ is analogous. 
```

The theorem facilitates working with Borel sets considerably. As an example, consider the set

$$
	A = \{ \alpha \colon \text{${}\alpha$ eventually constant} \}.
$$

We have

$$
	\alpha \in A \iff \exists n \forall m [ m \geq n \: \Rightarrow \: \alpha(n) = \alpha(m) ]
$$

The predicate in the square brackets is computable and depends only on $\alpha\Rest{m}$. Therefore, $A$ is $\Sigma^0_2$ Borel set.

