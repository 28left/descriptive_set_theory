# Effective Borel Sets
```{math}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\Integer}{\mathbb{Z}}
\newcommand{\Rat}{\mathbb{Q}}
\newcommand{\Pow}{\mathcal{P}}
\newcommand{\Baire}{\Nat^{\Nat}}
\newcommand{\Rest}[1]{\mid_{#1}}
\newcommand{\bPi}{\pmb{\Pi}}
\newcommand{\bSigma}{\pmb{\Sigma}}
\newcommand{\bDelta}{\pmb{\Delta}}
\newcommand{\Cyl}[1]{N_{#1}}
\newcommand{\Cant}{2^{\Nat}}
\newcommand{\Nstr}{\Nat^{<\Nat}}
\newcommand{\Tup}[1]{\langle #1 \rangle}
\newcommand{\Co}[1]{\neg \,#1}
\newcommand{\Op}[1]{\operatorname{#1}}
\newcommand{\Rest}[1]{\mid_{#1}}
```

Suppose $U \subseteq \Baire$ is open. Then there exists a set $W \subseteq \Nstr$ such that

$$ 
U = \bigcup_{\sigma \in W} \Cyl{\sigma}. 
$$

Using a standard (effective) coding procedure, we can identify a finite sequence of natural numbers with a natural number, and thus can see $W$ as a subset of $\Nat$.

If we provide a Turing machine with oracle $W$, we can semi-effectively test for membership in $U$ as follows. Assume we want to determine whether some $\alpha \in \Baire$ is in $U$. Write $\alpha$ on another oracle tape, and start scanning the $W$ oracle. If we retrieve a $\sigma$ that coincides with an initial segment of $\alpha$, we know $\alpha \in U$. On the other hand, if $\alpha \in U$, then we will eventually find some $\alpha\Rest{n}$ in $W$. If $\alpha \not\in U$, then the search will run forever. In other words, given $W$, $U$ is **semi-decidable**, or, extending terminology from subsets of $\Nat$ to subsets of $\Baire$, $U$ is 
**recusively enumerable** relative to $W$.

Similarly, we can identify a closed set $F$ with the code for the tree

$$ 
T_F = \{\alpha\Rest{n} \colon \alpha\in F,\, n\in \Nat \}.
$$

Then determining whether $\alpha \in F$ is **co-r.e.** in (the code of) $T_F$. If $\alpha \not\in F$ we will learn so after a finite amount of time.

These simple observations suggest the following general approach to Borel sets.

````{panels}
:column: col-lg-12 p-2

- Borel sets can be coded by a single infinite sequence in $\Baire$ (or $\Cant$).
- Given the code, we can describe the Borel set effectively, by means of oracle computations.
- The connection between degrees of unsolvability and definability results in a close correspondence between arithmetical sets ($\Sigma^0_n$) and Borel sets of finite order ($\bSigma^0_n$). 
````

In this lecture we will fully develop this correspondence. Later, we will see that it even extends beyond the finite level. 



## Borel codes

We fix a computable bijection $\pi: \Nat \to \Nstr$. Furthermore, let $\Tup{.,.}$ be the standard coding function for pairs,

$$ 
\Tup{x,y} = \frac{(x+y)(x+y+1)}{2}+y.
$$

Borel codes are defined inductively.

```{prf:definition}
:label: def-Borel-codes
Let $\gamma \in \Baire$.

- $\gamma$ is a $\bSigma^0_1$-**code** if $\gamma(0) = 2$ and $\gamma(n) \in \{0,1\}$ for all $n \geq 1$ . In this case we say that $\gamma$ **codes the open set**
\begin{equation*}
U_\gamma = \bigcup_{n \geq 1, \gamma(n) = 1} \Cyl{\pi(n-1)}.
\end{equation*}

- $\gamma$ is a $\bPi^0_n$-**code** if $\gamma(0)=3$ and $\alpha$ given by $\alpha(n) = \gamma(n+1)$ is a $\bSigma^0_n$-code for a set $A \subseteq \Baire$. In this case, we say $\gamma$ **codes the set $\Co{A}$**.

- $$\gamma$ is a $\bSigma^0_{n+1}$-**code** if $\gamma(0)=4$ and for each $m$, $\alpha_m$ given by $\alpha_m(j) = \gamma(\Tup{m,j}+1)$ is a $\bPi$-code of a set $A_m$. In this case, we say $\gamma$ **codes the set $\bigcup_n A_n$**.
```

The first position in each code indicates the kind of set it codes -- an open set, a complement, or a union.

We also define the **set of Borel codes of finite order**

$$
\Op{Bc}_\omega = \{\gamma \in \Baire \colon \gamma \text{ is a $\bSigma^0_n$- or $\bPi^0_n$-code, for some $n \geq 1$}\}\}. 
$$

The following is a straightforward induction.

```{prf:proposition}
:label: prop-Borel-codes

A set is $\bSigma^0_n$ $(\bPi^0_n)$ if and only if it has a $\bSigma^0_n$ $(\bPi^0_n)$ code.
```

Note that the definition actually assigns codes to **representations of sets**. A Borel set can have (and has) multiple codes, just as it has multiple representations. We can, for example, represent an open set by different sets $W$ of initial segments. 

Moreover, every $\bSigma^0_1$ set is also $\bSigma^0_2$, and thus a set has codes which reflect the ``more complicated'' definition of the $\bSigma^0_1$ set as a union of closed sets. It is useful to keep this distinction between a Borel set and its Borel representation in mind.

Each Borel code induces a tree structure that reflects how the corresponding Borel set is built up from open sets. A $3$ corresponds to a node with infinitely many nodes immediately below it, a $2$ to a node with just one immediate extension, and a $1$ represents a terminal node, since the open sets are the ``building blocks'' of the Borel sets and hence are not split further.

The tree of a Borel code is well-founded (i.e.\ has no infinite path), since a Borel code is defined via a well-founded recursion. The rank of the tree is a countable ordinal. 

How hard is it to decide whether a given real is a Borel code? We will see later that this question is quite difficult. In particular, we will extend the set of Borel codes to transfinite orders and see that the **set of all Borel codes is not Borel**. Deciding whether a tree on $\Nat$ is well-founded will play a fundamental role in this regard.



## Borel sets with computable codes

Suppose $\gamma$ is a computable code for an $F_\sigma$ set $F$. Then $\gamma$ is of the form $(4,\gamma')$, where, for $m \geq 0$, the **m-th column** of $\gamma'$,

$$
(\gamma')_m(n) = \gamma'(\Tup{m,n}) = \gamma(\Tup{m,n}+1)
$$ 
is of the form $(3,\alpha_m)$, each $\alpha_m$ in turn being a $\bSigma^0_1$-code for an open set. Observe that $\gamma'$ as well as the $\alpha_m$ are uniformly computable in $\gamma$.

With this, we can express membership in $F$ as follows:

\begin{align*}
    \beta \in F \quad & \Leftrightarrow \quad \exists m \: [\text{$\beta$ is in the set coded by $(\gamma')_m$}] \\
        & \Leftrightarrow \quad \exists m \forall n \: [\alpha_m(n+1) = 1 \; \Rightarrow \; \pi(n) \not\subset \beta ]. \\
        & \Leftrightarrow \quad \exists m \forall n \forall k \: \neg [\alpha_m(n+1) = 1 \;  \& \; \pi(n) = \beta\Rest{k} ].
\end{align*}

Note that the **inner predicate** $R(m,n,\tau)$ given by

$$
R(m,n, \tau) :\iff \alpha_m(n+1) = 1 \; \& \; \pi(n) = \tau
$$

is **decidable** (as is its negation $\neg R$). Hence an $\bPi^0_2$ set $F$ with a computable code can be represented in the following form:

>There exists a decidable predicate $R(m,n,\tau)$ such that
\begin{equation*}
    \beta \in F \quad \Leftrightarrow \quad \exists m \: \forall n,k \; \neg R(m, n, \beta\Rest{k}). 
\end{equation*}

On the other hand, if $R(m,n,\tau)$ is a recursive predicate, we can define the set

$$
W_m = \{ \sigma \colon \exists n \: R(m,n,\sigma) \}.
$$

Then the set $U_m = \bigcup_{\sigma \in W_m} \Cyl{\sigma}$ is open, and the set $F$ given by

\begin{align*} 
\alpha \in F : & \iff \exists m \: \alpha \in \Co{U_m} \\
    & \iff \exists m \: \forall n,k \: \neg R(m,n,\alpha\Rest{k})
\end{align*}

is $F_\sigma$.

Thus, there seems to be a close connection between $F_\sigma$ sets with computable Borel codes and sets definable by $\Sigma^0_2$ formulas over computable predicates. Given that we introduced the notation $\bSigma^0_2$ for $F_\sigma$ sets earlier, this is perhaps not very surprising.

In this analysis, there seems to be nothing specific about the $F_\sigma$ used in the example. Indeed, it can be extended to Borel sets of finite order, which we will do next. 

We will next introduce the 
**lightface** Borel hierarchy and show that it corresponds to Borel sets of finite order with recursive codes. Using **relativization**, we then obtain a complete characterization of Borel sets of finite order: *They are precisely those sets definable by arithmetical formulas, relative to a real parameter.*


## The effective Borel hierarchy

```{prf:definition} The Lightface Hierarchy
:label: def-effective-Borel
A set $A \subseteq \Baire$ is 
- (lightface) $\Sigma^0_1$ if there exists a computable predicate $R(n,\sigma)$ such that
\begin{equation*}
    \alpha \in A \iff \exists n,k \: R(n,\alpha\Rest{k}),
\end{equation*}
- (lightface) $\Pi^0_n$ if $\Co{A}$ is $\Sigma^0_n$,
- (lightface) $\Sigma^0_{n+1}$ if there exists a $\Pi^0_n$ set $P$ such that
\begin{equation*}
    \alpha \in A \iff \exists n \; (n,\alpha) \in P. 
\end{equation*}
```

The following result is at the heart of the effective theory. 

```{prf:proposition}
:label: prop-computable-codes 
Let $A \subseteq \Baire$. Then

> $A$ is (lightface) $\Sigma^0_n$ ($\Pi^0_n$) iff $A$ is (boldface) $\bSigma^0_n$ ($\bPi^0_n$) and has a computable $\bSigma^0_n$- ($\bPi^0_n$-) code.
```

```{prf:proof}
We proceed by induction on the Borel complexity. 

Suppose $A$ is $\Sigma^0_1$. Let $R$ be recursive such that $A = \{ \alpha \colon \exists n,k \: R(n,\alpha\Rest{k})\}$. If we let $W = \{\sigma \colon \exists n R(n,\sigma)\}$, then

$$ 
A = \bigcup_{\sigma \in W} \Cyl{\sigma},
$$

and hence is an open set. Furthermore,

$$ 
\gamma(n) = 
\begin{cases}
    2 & n = 0, \\
    1 & n \geq 1 \: \& \: R(n-1),\\
    0 & n \geq 1 \: \& \: \neg R(n-1), 
\end{cases}
$$

is a computable Borel code for $A$.

If $A$ is $\bSigma^0_1$ with a computable, $\bSigma^0_1$-code $\gamma$, then $\gamma$ is of the form $(2,\gamma')$, $\gamma'$ coding a representation of $A$ as a union of basic open cylinders. Then
\[ \alpha \in A \Iff \exists n \: [\gamma'(\alpha\Rest{n}) = 1]. \]
Hence we can set $R(\sigma) = \gamma'(\sigma)$.

\medskip If $A$ is $\Pi^0_n$, then $\Co{A}$ is $\Sigma^0_n$. By induction hypothesis, $\Co{A}$ has a computable $\bSigma^0_n$-code $\gamma$. Then $(3,\gamma)$ is a computable $\bPi^0_n$-code for $A$.

Conversely, if $\gamma = (3,\gamma')$ is a computable $\bPi^0_n$-code for a $\bPi^0_n$ set $A$, then $\gamma'$ is a computable $\bSigma^0_n$-code for the $\bSigma^0_n$ set $\Co{A}$. By induction hypothesis, $\Co{A}$ is $\Sigma^0_n$ and hence $A$ is $\Pi^0_n$.

\medskip Finally, assume that $A$ is $\Sigma^0_{n+1}$. Let $P$ be $\Pi^0_n$ such that
\[ \alpha \in A \Iff \exists n \; [(n,\alpha) \in P]. \]
By induction hypothesis, there exists $P$ is $\bPi^0_n$ with a computable $\bPi^0_n$-code $\gamma = (3,4, \dots)$. Let
\[ P_m = \{ \beta \colon (m,\beta) \in P \} = P \cap \Cyl{\Tup{m}}. \]
Then each $P_m$ is $\bPi^0_n$, since the Borel levels are closed under finite intersections, and we have
\[ A = \bigcup_m P_m. \]
Therefore, $A$ is $\bSigma^0_{n+1}$. Furthermore, each $P_m$ has a computable $\bPi^0_n$-code $\gamma_m$, which can be computed uniformly in $m$, and thus $\gamma^* = (4,(\gamma_m(n))_{m,n})$ is a computable, $\bSigma^0_{n+1}$-optimal code for $A$.

For the converse, let $A$ be $\bSigma^0_{n+1}$ with a computable $\bSigma^0_{n+1}$-code $\gamma = (4,\gamma')$. Then each of the columns of $\gamma'$ is a computable $\bPi^0_n$-code for a $\bPi^0_n$ set $P_m$. Let $P'_m = \{ (m,\alpha) \colon \alpha \in P_m \}$. $P'_m$ is $\bPi^0_n$, too. This can be seen as follows. $\Nat \times \Baire$ is homeomorphic to $\Baire$. $\{m\}\times P_m$ is $\Pi^0_n$ in $\Nat \times \Baire$, by replacing each set $S$ in the definition of $P_m$ by $\{m\}\times S$ (note that $\{m\}$ is clopen in $\Nat$). Borel complexities are preserved under homeomorphic images. (We will discuss the closure properties of Borel sets in detail later.) 

A similar argument shows that $P^*_m = \{(k,\alpha) \colon k\neq m \text{ or } (k=m \: \& \: \alpha\in P_m)\}$ is $\bPi^0_n$ for each $n$. Now let $P^* = \bigcup_m P^*_m$. Then $P^*$ is $\bPi^0_n$, and we can effectively and uniformly in $m$ compute an $\bPi^0_n$-code for it. By induction hypothesis, $P^*$ is $\Pi^0_n$, and we have
\[ \alpha \in A \Iff \exists m \; (m,\alpha) \in P^*, \]
as desired. 
```
