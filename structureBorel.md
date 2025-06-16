# The Structure of Borel Sets

In this chapter, we further investigate the structure of Borel sets. We will use the results of the previous lecture to derive various closure properties and other structural results. As an application, we see that the Borel hierarchy is indeed proper.


## Notation 

Before we go on, we have to address some notational issues. So far we have used notation quite liberally, especially when it came to product sets. We will continue to do so, but we want to put this on a firmer footing.

Using coding, we can identify any product space $\Nat^m \times (\Baire)^n$ with $\Nat^\Nat$. One way to do this is to fix, for each $n \geq 1$, an effective homeomorphism $\theta_n: (\Baire)^n \to \Baire$ and map

$$
	(k_1, \dots, k_m, \alpha_1, \dots, \alpha_n) \mapsto (k_1,\dots, k_m, \theta_n(\alpha_1, \dots, \alpha_n)).
$$

Here $(k_1,\dots, k_m, \theta_n(\alpha_1, \dots, \alpha_n))$ is just a suggestive way of writing the concatenation

$$
	\Tup{k_1} \Conc \cdots \Conc \Tup{k_m} \Conc \theta_n(\alpha_1, \dots, \alpha_n).
$$

We have already used this notation in the previous lecture. In the following, we will continue to switch freely between product sets and their coded counterparts, as subsets of $\Baire$.

Another notation identifies sets and relations. We will identify sets $A \subseteq \Nat^m \times (\Baire)^n$ with the relation they induce and write $A(k_1, \dots, k_m, \alpha_1, \dots, \alpha_n)$ instead of $(k_1, \dots, k_m, \alpha_1, \dots, \alpha_n) \in A$. Conversely, we will identify relations with the set they induce.



## Closure properties

We can use the lightface hierarchy to derive several closure properties of $\bSigma^0_n$ ($\bPi^0_n$).

If $P \subseteq \Nat \times \Baire$, we define the **projection of $P$ along $\Nat$**, $\exists^\Nat P$, as

$$
	\exists^\Nat P = \{ \alpha \colon \exists n \: P(n,\alpha)\}.
$$

We already encountered this operation in the definition of the effective Borel hierarchy ({prf:ref}`def-effective-Borel`). The dual operation is 

$$
	\forall^\Nat P = \{ \alpha \colon \forall n \: P(n,\alpha)\}.
$$

```{prf:proposition}
For each $n \geq 1$, $\bSigma^0_n$ is closed under $\exists^\Nat$, and $\bPi^0_n$ is closed under $\forall^\Nat$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

We prove the result for $\Sigma^0_n$ (lightface). The boldface case follows by relativization, and the proof for $\bPi^0_n$ is dual.

Let $R$ be a computable relation such that 
$$
    A(z,\alpha) \iff \exists x_1 \: \dots \: \Qu x_n \; R(x_1, \dots, x_{n-1}, z, \alpha\Rest{x_n}).
$$
Then 
$$
    \exists^\Nat A(\alpha) \iff \exists x_0 \exists x_1 \: \dots \: \Qu x_n \; R(x_1, \dots, x_{n-1}, x_0,\alpha\Rest{x_n}).
$$
We can combine two existential number quantifiers into one by using the pairing function $\Tup{.,.}$, or rather, its inverses, which we will denote by $(.)_0$ and $(.)_1$. 
Then 
$$
    \exists^\Nat A(\alpha) \iff \exists z_1  \: \dots \: \Qu z_n \; R((z_1)_1, \dots, z_{n-1}, (z_1)_0, \alpha\Rest{z_n}).
$$
The inner predicate is still computable, since the inverses of the pairing function are computable.
```

One can use similar applications of coding and quantifier manipulation to prove a number of other closure properties. Often they also easily follow from the topological definitions, but it is good to have several techniques at hand.

```{prf:proposition}
:label: prop-Borel-closure-finite

For all $n \geq 1$,
-  $\bSigma^0_n$ is closed under countable unions and finite intersections.
-  $\bPi^0_n$ is closed under finite unions and countable intersections.
-  $\bDelta^0_n$ is closed under finite unions, finite intersections, and complements.		
```
	
```{prf:proof}
:class: dropdown
:nonumber: true

One can prove this by induction along the hierarchy. To obtain the closure under finite unions and intersections, one can use the following logical equivalences.
\begin{align*}
    \exists x \, P(x) \, \wedge \,  \exists y \, R(y) &\iff \exists x  \exists y \, (P(x) \, \wedge \,  R(y)) \\
    \forall x \, P(x) \, \vee \,  \forall y \, R(y) &\iff  \forall x  \forall y \, (P(x) \, \vee \,  R(y))
\end{align*}
The result then follows using the pairing functions and by noting that computable relations are closed under $\wedge$ and $\vee$.
```


Given $P \subseteq \Nat \times \Baire$, the **bounded projection** along $\Nat$
is defined as

$$
	\exists^\leq P = \{ (n,\alpha) \colon \exists m \leq n \: P(m,\alpha)\}.
$$

and the dual is

$$
	\forall^\leq P = \{ (n,\alpha) \colon \forall m \leq n \: P(m,\alpha)\}.
$$

```{prf:proposition}
:label: prop-Borel-closure-bounded-projection

For all $n \geq 1$, $\bSigma^0_n$, $\bPi^0_n$, and $\bDelta^0_n$ are closed under $\exists^\leq$ and $\forall^\leq$.		
```

```{prf:proof}
:class: dropdown
:nonumber: true

In this case we use the computable coding function $\pi: \Nat \to \Nstr$. 
We have the following equivalence, which immediately implies the closure properties for $\bSigma^0_n$ and $\bPi^0_n$, respectively, and hence also for $\bDelta^0_n$.

\begin{align*}
    \forall m \le n \, \exists k \; P(m,k) &\iff \exists k  \, \forall m \le n \:  P(m,\pi(k)_m)\\
    \exists m \le n  \, \forall k \; P(m,k) &\iff \forall k  \, \exists m \le n \;   P(m,\pi(k)_m)
\end{align*}
Here we use $\pi(k)_m$ to denote the $m$-th entry of $\pi(k)$.
```

Finally, the levels of the Borel hierarchy are closed under continuous preimages.

```{prf:proposition}
:label: prop-Borel_closure-preimages

For all $n \geq 1$, for any $A \subseteq \Baire$, and for any continuous $f: \Baire \to \Baire$, if $A$ is $\bSigma^0_n$ $(\bPi^0_n$, $\bDelta^0_n)$ then $f^{-1}(A)$ is $\bSigma^0_n$ $(\bPi^0_n$, $\bDelta^0_n)$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

This follows easily by induction on $n$, since open and closed sets are closed under continuous preimages.

However, we can also argue via definability, since by {prf:ref}`prop-product-continuous` in the Section  @Polish one can represent a continuous function through a monotone mapping ${}\psi$ from finite strings to finite strings.  We have
$$
    f^{-1}(A) = \{ \alpha \colon A(f(\alpha)) \}.
$$
Let $R$ be computable such that
$$
    A(\alpha) \iff \exists x_1 \: \dots \: \Qu x_n \; R(x_1, \dots, x_{n-1}, \alpha\Rest{x_n}).
$$
Substitute $\psi(\alpha\Rest{x_n})$ for ${}\alpha\Rest{x_n}$. The resulting formula defines $f^{-1}(A)$, and is equivalent to a $\Sigma^0_n$-formula relative to (a real coding) the mapping $\psi$.
```



## Universal sets

Let ${}\Gamma$ be a family of subsets defined in various topological spaces. Of course we have in mind the classes $\bSigma^0_n$ or $\bPi^0_n$, but the concept of a **universal set** can be defined quite generally. Given a space $X$, we denote by $\Gamma(X)$ the collection of all subsets of $X$ that are in $\Gamma$. In this section, as we mostly focus on $\Baire$, we often drop the reference to $\Baire$ and simply write $\Gamma$ to denote $\Gamma(\Baire)$.

```{prf:definition}
:label: def-universal

Let $Y$ be a set. A set $U \subseteq X \times Y$ is **$Y$-universal for ${}\Gamma(X)$** if $U \in \Gamma(X\times Y)$, and for every set $A$ in ${}\Gamma(X)$ there exists a $y \in Y$ such that

$$
    A = \{ x \colon (x,y) \in U \}.
$$ 
```

A universal set for ${}\Gamma$ can be thought of as a **parametrization** of ${}\Gamma$, the second component providing a **code** or **parameter** for each set in ${}\Gamma$.

A well-known example of a universal set is the **generalized halting problem**,

$$
	K_0 = \{ (x,e) \colon \text{ the $e$-th Turing machine halts on input $x$} \}.
$$

In the sense of the above definition, $K_0$ is $\Nat$-universal for the family of recursively enumerable sets.

```{prf:proposition}
:label: prop-Borel-universal
For any $n \geq 1$, there exists a set $U \subseteq \Baire \times \Baire$ that is $\Baire$-universal for $\bSigma^0_n(\Baire)$ (or $\bPi^0_n(\Baire)$, respectively).
```

```{prf:proof} Sketch
:class: dropdown
:nonumber: true

Proceed by induction. 
To anchor the induction, observe that 
$$
U = \{ (\alpha, \gamma) \colon \alpha \text{ is in the open set coded by $(1, \gamma)$}\}
$$
is $\Baire$-unversial for $\BS{1}(\Baire)$.
For the inductive steps, make use of how the the Borel codes are built up inductively from codes for lower levels and apply the [fundamental theorem](#thm-fundamental) of effective descriptive set theory.
```

The result can be generalized to hold for arbitrary Polish spaces $X$, i.e. for any $n \geq 1$, there exists a set $U \subseteq \Baire \times X$ that is $\Baire$-universal for $\bSigma^0_n(X)$ ($\bPi^0_n(X)$). To achieve this, one has to define Borel codes for $X$. This can be done by fixing a countable basis $(V_n)$ of the topology of $X$ and assigning a sequence $\gamma \in \Baire$ the open set
$$
	U_\gamma = \bigcup_{n \in \Nat} V_{\gamma(n)}.
$$

The definition of codes for higher levels is then similar to [the definition of Borel codes for finite levels](#def-Borel-codes).

As in the case of the halting problem, we can use the existence of universal sets to show that the levels of the Borel hierarchy are proper. The crucial point is that we can use universal sets to **diagonalize**. 

```{prf:theorem} 
:label: thm-Borel-proper

For any $n \geq 1$, $\bSigma^0_n \neq \bPi^0_n$. 
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $U$ be an $\Baire$-universal set for $\bSigma^0_n$. Put

$$
    D = \{ \alpha \colon (\alpha, \alpha) \in U \}.
$$

Since $U$ is $\bSigma^0_n$, $D$ is $\bSigma^0_n$, too. Then $\Co{D}$ is $\bPi^0_n$, but cannot be $\bSigma^0_n$, for then there would exist ${}\beta$ such that 

$$
    \Co{D} = \{ \alpha \colon (\alpha, \beta) \in U \},
$$

and thus

$$
    \beta \in D \iff (\beta, \beta) \in U \iff \beta \in \Co{D}, 
$$

a contradiction.
```
The diagonal set $D$ can obviously be defined for any universal set $U$, and hence the same proof yields a $\bPi^0_n$ set that is not $\bSigma^0_n$. 

```{prf:corollary} 
:label: cor-hier-proper

For any $n \geq 1$,
\begin{gather*}
    \bDelta^0_n \subsetneq \bSigma^0_n \subsetneq \bDelta^0_{n+1} \\
    \bDelta^0_n \subsetneq \bPi^0_n \subsetneq \bDelta^0_{n+1}.
\end{gather*}
```

```{prf:proof}
:class: dropdown
:nonumber: true

Since $\BS{n} \nsubseteq \BP{n}$ and $\BP{n} \nsubseteq \BS{n}$, $\bDelta^0_n \subsetneq \BS{n},\BP{n}$. On the other hand if $\BS{n} = \bDelta^0_{n+1}$, then $\BS{n}$ would be closed under complements, and hence $\BS{n} = \BP{n}$, contradicting {prf:ref}`thm-Borel-proper`.
```


## Borel sets of transfinite order

We saw that the **Borel sets of finite order**

$$
	\operatorname{Borel}_\omega = \bigcup_{n < \omega} \BS{n}
$$

form a proper hierarchy. This fact also implies that $\Op{Borel}_\omega$ does not exhaust all Borel sets.

```{prf:proposition}
:label: prop-nonfinite-Borel

There exists a Borel set $B$ that is not $\BS{n}$ for any $n \in \Nat$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

For every $n \in \Nat$, pick a set $B_n$ in $\BP{n} \setminus \BS{n}$. Put

$$
    B = \bigcup_{n \in \Nat} \{(n,\alpha) \colon \alpha \in B_n \}.
$$

Each of the sets in the union is Borel and hence $B$ is Borel. If $B$ were of finite order, it would be $\BS{k}$ for some $k \geq 1$. Since each $\BS{n}$ is closed under finite intersections, it follows that for all $m \geq 1$, 

$$
    B \cap \Cyl{\Tup{m}} 
$$

is $\BS{k}$. But $B \cap \Cyl{\Tup{m}}$ is homeomorphic to $B_m$, hence $B_m$ in $\BS{k}$ for all $m \geq 1$, contradiction.
```

We can extend the Borel hierarchy to arbitrary ordinals.

```{prf:definition}
:label: def-transfinite-Borel

Let $X$ be a topological space. As before, let $\BS{1}(X)$ be the set of all open subsets of $X$, $\BP{1}$ be the set of all closed subsets of $X$, and $\bDelta^0_1(X)$ be the set of all clopen subsets of $X$. Given an ordinal ${}\xi > 1$, we define
\begin{align*}
    & \bSigma^0_\xi(X) = \{ \bigcup_k A_k \colon A_k \in \bPi^0_{\zeta_k}(X),\; \zeta_k < \xi \}, \\
    & \bPi^0_\xi(X) = \{ \Co{A} \colon A \in \bSigma^0_\xi(X) \} = \Co{\bSigma^0_\xi(X)}, \\
    & \bDelta^0_\xi(X) = \bSigma^0_\xi(X) \cap \bPi^0_\xi(X). \\
\end{align*}
```

It actually suffices to consider ordinals up to $\omega_1$, the first uncountable ordinal.

```{prf:proposition}
:label: prop-Borel-omega1

For every Borel set $B$ there exists $\xi < \omega_1$ such that $B \in \BS{\xi}$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

If $B$ is open, this is clear. It is also clear if $B$ is the complement of a Borel for which the statement has been verified.

Assume finally that 

$$
    B = \bigcup_n B_n, \; \text{ where each $B_n$ is Borel},
$$

and assume the statement holds for each $B_n$. For each $n$, let $\xi_n$ be a countable ordinal such that 

$$
    B_n \in \BP{\xi_n}.
$$

Then 

$$
    B \in \BS{\xi}, \; \text{ where $\xi = \sup \{\xi_n +1 \colon n \in \Nat\}$}.
$$

Since each $\xi_n$ is countable, ${}\xi$ is countable.
```

Borel sets of infinite order have the **same closure properties as their counterparts of finite order**. The proofs, however have to proceed by induction using the topological properties of $\BS{\xi}$ and $\BP{\xi}$, since the characterization via definability in arithmetic is no longer available -- the arithmetical hierarchy reaches only to ${}\omega$.

Similarly, the Hierarchy Theorem ({prf:ref}`thm-Borel-proper`) extends to the transfinite levels. As the finite levels, this follows from the existence of universal sets for each level, which we now prove for the full hierarchy.

```{prf:proposition} 
:label: prop-universal-general
For each $\xi < \omega_1$, there exists a $\Baire$-universal set for $\BS{\xi}$ $(\BP{\xi})$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

If $U$ is $\Baire$-universal for $\bSigma^0_\xi$, then 

$$
    \neg U = \{ (\alpha,\gamma) \colon (\alpha,\gamma) \not\in U \}
$$

is $\Baire$-universal for $\bPi^0_\xi$, since for any $\bPi^0_\xi$ set $A$, $B = \neg A$ is $\bSigma^0_\xi$ and hence there exists a ${}\gamma$ such that

$$
    B = \{\beta \colon (\beta,\gamma) \in U \}
$$

and hence

$$
    A = \{ \alpha \colon (\alpha,\gamma) \not\in U \}. 
$$

It remains to show that each $\BS{\xi}$ has an $\Baire$-universal set. By induction hypothesis, for every $\eta < \xi$ exists a $\Baire$-universal set $U_\eta$ for $\BP{\eta}$. Since ${}\xi$ is countable, we can pick a monotone  sequence of ordinals $(\xi_n)$ such that $\xi = \sup \{\xi_n + 1 \colon n < \omega \}$. Define

$$
    U_\xi =  \{ (\alpha, \gamma) \colon \exists n (\alpha, (\gamma)_n) \in U_{\xi_n} \},
$$

where $(\gamma)_n$ denotes the $n$th column of ${}\gamma$.

It is straightforward to check that $U_\xi$ is $\Baire$-universal for $\BS{\xi}$. (Note that any set $A$ in $\BS{\xi}$ can be represented as $\bigcup_n A_n$ with $A_n \in \BP{\xi_n}$, since $(\xi_n+1)$ is cofinal in ${}\xi$.)
```

The construction of the universal $\BS{\xi}$ set bears some resemblance to the construction of a $\bSigma^0_{n+1}$ code. It is indeed possible to formally define Borel codes for *all* Borel sets.

```{prf:definition}
:label: def-Borel-codes-transfinite
Let $\gamma \in \Baire$.

- Suppose $\gamma \in \Baire$ is such that $\gamma(0) = 1$ and $\gamma' \in \Baire$. ${}\gamma$ is a Borel code for the open set 
\begin{equation*}
    U = \bigcup_{\gamma'(\sigma) = 0} \Cyl{\sigma}
\end{equation*}

- If ${}\gamma$ is such that $\gamma(0)=2$ and $\gamma'$ is a Borel code for $A \subseteq \Baire$, we say ${}\gamma$ is a Borel code for $\Co{A}$.

- If ${}\gamma$ is such that $\gamma(0)=3$ and for each $m$, $\gamma'_m$ is a Borel code of a set $A_m$, we say ${}\gamma$ is a Borel code for $\bigcup_n A_n$.
```

Any Borel code induces a well-founded tree (given by the coding nodes $1$, $2$,and $3$). We can also consider Borel sets with computable codes. But there is no more straightforward connection with effective definability. It is possible to do this, but it requires a careful development of what it means to take effective unions along countable ordinals. We will return to it later.

Looking further ahead, one can show that **the set of all Borel codes is not Borel** (exercise -- use a diagonalization argument as in the proof of {prf:ref}`thm-Borel-proper`). At the heart of this lies the fact that we cannot, in a Borel way, describe whether an arbitrary tree over $\Nat$ is well-founded or not. This will soon be a central topic when we turn our investigation to analytic and co-analytic sets. 



<!-- This general proof of existence of universal sets does not use Borel codes, since those were defined only for Borel sets of finite order. The proof of {prf:ref}`prop-universal-general` provides an idea how we could extend the definition of a code to transfinite orders: Take unions of codes along a cofinal sequence. However, we would like to this in an effective way, and it is not clear how to do this for infinite ordinals in general. 

We will later return to this question, when we introduce computable ordinals}.
 -->
