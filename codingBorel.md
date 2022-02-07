# Coding Borel Sets
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
\newcommand{\Sle}{\subset}
\newcommand{\Sleq}{\subseteq}
```

In this chapter, we take a further look at Borel subsets of $\Baire$. As is common in this setting, we call the elements of $\Baire$ **reals**. This is motivated by the fact that, via the continued fration expansion, $\Baire$ [is homeomorphic to the set of irrational real numbers](fact-paths-as-reals). Suppose $U \subseteq \Baire$ is open. Then there exists a set $W \subseteq \Nstr$ such that

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

## Some notation for reals, strings, and numbers

We fix a computable bijection $\pi: \Nat \to \Nstr$. In general, we will often use string and their images under $\pi$ interchangeably, that is, for example, if $A \subset \Nat$, we will write $\sigma \in A$ to denote $\pi(\sigma) \in A$. 
We will also freely identify infinite binary sequences with the set of natural numbers they represent as their characteristic function. 

Furthermore, let $\Tup{.,.}$ be the standard coding function for pairs,

$$ 
\Tup{x,y} = \frac{(x+y)(x+y+1)}{2}+y.
$$

Finally, let us define the following operation on elements of Baire (or Cantor) space: Given $\beta\in \Baire$, 
- let $\beta'$ be the real defined by $\beta'(n) = \beta(n+1)$. (*We cut the first entry.*)
- for $m \geq 0$, let $\beta_m$ be the *$m$-th column* of $\beta$, $\beta_m(n) = \beta(\Tup{m,n})$.


## Borel codes


Borel codes are defined inductively. 

```{prf:definition}
:label: def-Borel-codes
Let $\gamma \in \Baire$.

- Suppose $F \subseteq \Baire$ is closed, and $\gamma \in \Baire$ is such that $\gamma(0) = 2$ and $\gamma'$ codes the tree $T_F$. More precisely, $\gamma'(n) \in \{0,1\}$ for all $n$ and $T_F = \{\pi(n) \colon \gamma'(n) = 1 \}$.  In this case we say that $\gamma$ **is a Borel code for the closed set $F (= [T_F])$**.

- If $\gamma$ is such that $\gamma(0)=3$ and $\gamma'$ is a Borel code for $A \subseteq \Baire$, we say $\gamma$ **is a Borel code for $\Co{A}$**.

- If $\gamma$ is such that $\gamma(0)=4$ and for each $m$, $\gamma'_m$ is a Borel code of a set $A_m$, we say $\gamma$ **is a Borel code for $\bigcup_n A_n$**.
```

The first position in each code indicates the kind of set it codes -- an open set, a complement, or a union. 

We also define the **set of Borel codes**

$$
\Op{Bc} = \{\gamma \in \Baire \colon \gamma \text{ is a Borel code}\}. 
$$

The following is a straightforward induction.

```{prf:proposition}
:label: prop-Borel-codes

Every $\bPi^0_n$ ($\bSigma^0_n$) set has a $\bPi^0_n$ ($bSigma^0_n) Borel code.
```

The proposition actually holds for *all* Borel sets, which can be proved by **transfinite induction**. However, we have not introduced Borel sets of transfinite order yet, so we state the existence of codes only for $\pPi^0_n$ ($\pSigma^0_n$) sets. In the next chapter, we will study the *full* Borel hierarchy, and then it should be clear that the above proposition extends to all Borel sets. 


Note that the definition of Borel code actually assigns codes to **representations of sets**. A Borel set can have (and has) multiple codes, just as it has multiple representations. We can, for example, represent an open set by different sets $W$ of initial segments. 

Moreover, every $\bSigma^0_1$ set is also $\bSigma^0_2$, and thus a set has codes which reflect the ``more complicated'' definition of the $\bSigma^0_1$ set as a union of closed sets. It is useful to keep this distinction between a Borel set and its Borel representation in mind.


## The tree structure of Borel codes

Each Borel code induces a tree structure that reflects how the corresponding Borel set is built up from closed sets.
The terminal nodes are given by codes for closed sets (the ones starting with "$2$"), since they are the ``building blocks'' of the Borel sets and hence are not extend/split further. A "$3$-code" represents a node  with just one immediate successor, while a "$4$-code" corresponds to a node with infinitely many immediate successors.

The tree of a Borel code defined this way **is always well-founded** (i.e. has no infinite path), since a Borel code is defined via a well-founded recursion. The rank of the tree is a countable ordinal. 

How hard is it to decide whether a given real is a Borel code? We will see later that this question is quite difficult. More precisely, we will see that the **set $\Op{Bc}$ of all Borel codes is not Borel**. Deciding whether a tree on $\Nat$ is well-founded will play a fundamental role in this regard.

The tree structure of a code also lets us assign levels to a Borel code similar to the levels of the Borel hierarchy:

- Trees with a single node $(2)$ correspond to **$\bPi^0_1$ codes**. 
- If $T$ is a  a $\bPi^0_n$ ($\bSigma^0_n$) code, then the tree with new top node $(3)$ represents a $\bSigma^0_n$ ($\bPi^0_n$) code. 
- And if $T_n$ is a sequence of $\bPi^0_n$ codes, then the tree with new top node $(4)$ and each $T_n$ directly below it corresponds to a **$\bSigma^0_{n+1}$ code**.

## Computing with Borel codes

Suppose $\gamma$ is a **computable** code for an $F_\sigma$ set $B$. We may assume $\gamma$ is of the form $(4,\gamma')$, with each column $\gamma'_m$ being of the form $(2,\alpha_m)$, coding a closed set $F_m$.

With this, we can express membership in $B$ as follows:

\begin{align*}
    \beta \in B \quad & \Leftrightarrow \quad \exists m \: [\text{$\beta$ is in the set coded by $\gamma'_m$}] \\
        & \Leftrightarrow \quad \exists m \forall n \: [\beta\Rest{n} \text{ is in the tree coded by } \gamma'_m]. \\
        & \Leftrightarrow \quad \exists m \forall n \: [\alpha_m(\beta\Rest{n}) = 1 ].
\end{align*}

Note that, since we assume $\gamma$ to be computable, the **inner predicate** $R(m,\sigma)$ given by

$$
R(m,\sigma) :\iff \alpha_m(\sigma) = 1 
$$

is **decidable**, that is, it can be decided by a Turing machine.

Hence any $\bSigma^0_2$ set $B$ with a computable code can be represented in the following form:

>There exists a decidable predicate $R(m,\sigma)$ such that
\begin{equation*}
    \beta \in B \quad \Leftrightarrow \quad \exists m \: \forall n \; \neg R(m, \beta\Rest{n}). 
\end{equation*}

Conversely, if $R(m,\sigma)$ is a decidable predicate, let

$$
F_m = \{ \beta \colon \forall n \: R(m,\beta) \}.
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

In this analysis, there seems to be nothing specific about the $F_\sigma$ used in the example. Indeed, it can be extended to Borel sets of finite order, which we will do next. 

We will next introduce the 
**lightface** Borel hierarchy and show that it corresponds to Borel sets of finite order with recursive codes. Using **relativization**, we then obtain a complete characterization of Borel sets of finite order: *They are precisely those sets definable by arithmetical formulas, relative to a real parameter.*


## The effective Borel hierarchy

```{margin}
You may notice some sloppy notation in the third item here, since as written the set $P$ should technically be a subset of $\Nat\times \Baire$. We will put this on more solid footing in the next chapter. For now, you can think of $\Nat \times \Baire$ as the same as $\Baire$ -- just "merge" the pair into one real.
```
```{prf:definition} The Lightface Hierarchy
:label: def-effective-Borel
A set $A \subseteq \Baire$ is 
- (lightface) $\Pi^0_1$ if there exists a computable predicate $R(\sigma)$ such that
\begin{equation*}
    \alpha \in A \iff \forall k \: R(\alpha\Rest{k}),
\end{equation*}
- (lightface) $\Sigma^0_n$ if $\Co{A}$ is $\Pi^0_n$,
- (lightface) $\Sigma^0_{n+1}$ if there exists a $\Pi^0_n$ set $P$ such that
\begin{equation*}
    \alpha \in A \iff \exists n \; (n,\alpha) \in P. 
\end{equation*}
```

The following result is at the heart of the effective theory. 

```{prf:proposition}
:label: prop-computable-codes 
Let $A \subseteq \Baire$. Then

> $A$ is (lightface) $\Pi^0_n$ ($\Sigma^0_n$) iff $A$ is (boldface) $\bPi^0_n$ ($\bSigma^0_n$) and has a computable $\bPi^0_n$ ($\bSigma^0_n$) code.
```

````{prf:proof}
We proceed by induction on the Borel complexity. 

Suppose $A$ is $\Pi^0_1$. Let $R$ be computable such that $A = \{ \alpha \colon \ \: \forall k R(\alpha\Rest{k})\}$. As observed above, if we let $T = \{\sigma \colon \forall \tau \Sleq \sigma R(\tau)\}$, then $T$ is a tree with $[T] = A$. Moreover, since $R$ is computable, so is $T$, and $(1,T)$ is a computable $\Pi^0_1$ code for $A$. (Recall that we identify sets of strings with subsets of $\Nat$, which in turn we identify with the characteristic sequence.)

Conversely, if $(1,T)$ is a computable $\bPi^0_1$ code for a $\bPi^0_1$ set $A$, then 

$$
R(\sigma) :\iff \sigma \in T
$$

is computable and $\alpha \in A$ if and only if $\forall n \: R(\alpha\Rest{n})$.


Now assume 


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
````
