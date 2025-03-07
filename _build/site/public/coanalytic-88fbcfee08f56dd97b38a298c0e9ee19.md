# Co-Analytic sets

We will see that, in many ways, $\PP{1}$ sets form the frontier between classical descriptive set theory and metamathematics. This chapter can be seen as the start of our transition to metamathematics. We will detail the distinguished role well-founded relations play in the analysis of $\PP{1}$ sets.


## Normal forms

Analytic sets are projections of closed sets. Closed sets are in $\Baire\times \Baire$ are infinite paths through **trees on $\Nat \times \Nat$**, i.e. two-dimensional trees.

```{prf:definition}
:label: def-two-dim-tree
	
A set $T \subseteq \Nstr \times \Nstr$  is a **two-dimensional tree** if
- **(i)** $(\sigma,\tau) \in T$ implies $|\sigma|=|\tau|$ and
- **(ii)** $(\sigma,\tau) \in T$ implies $(\sigma\Rest{n},\tau\Rest{n}) \in T$ for all $n \leq |\sigma|$.

An **infinite branch** of $T$ is a pair $(\alpha,\beta) \in \Baire\times \Baire$ so that
\begin{equation*}
    \forall n\in \Nat \; (\alpha\Rest{n},\beta\Rest{n}) \in T.
\end{equation*}
```

As in the one-dimensional case, we use $[T]$ to denote the set of all infinite paths through $T$. It follows that $A \subseteq \Baire$ is analytic if and only if there exists a two-dimensional tree $T$ on $\Nat \times \Nat$ such that
\begin{align*}
	\alpha \in A & \iff  \exists \beta \: (\alpha,\beta) \in [T]\\
	             & \iff  \exists \beta \, \forall n \: (\alpha\Rest{n},\beta\Rest{n}) \in T.
\end{align*}

Another way to write this is to put, for given $T$ and $\alpha \in \Baire$,

$$
	T(\alpha) = \{ \tau \colon (\alpha\Rest{|\tau|}, \tau) \in T \}.
$$

Then we have, with $T$ witnessing that $A$ is analytic,

$$
	\alpha \in A \iff T(\alpha) \text{ has an infinite path } \iff T(\alpha) \text{ is not well-founded}.
$$

We obtain the following normal form for co-analytic sets.

```{prf:proposition} Normal form for co-analytic sets  
:label: prop-norm-form-coanalytic
A set $A \subseteq \Baire$ is $\PP{1}$ if and only if there exists a two-dimensional tree $T$ such that

$$
    \alpha \in A \iff T(\alpha) \text{ is well-founded}.
$$
```

If $A$ is (lightface) $\Pi^1_1$, then there exists a computable such $T$, and the mapping $\alpha \mapsto T(\alpha)$ is computable, as a mapping between reals and trees (which can be coded by reals). This relativizes, i.e. for a $\Pi^1_1(\gamma)$ set, the mapping $\alpha \mapsto T(\alpha)$ is computable in ${}\gamma$. Since computable mappings are continuous, we obtain that the in the above proposition, the mapping $\alpha \mapsto T(\alpha)$ is continuous.



## $\mathbf{\Pi}^1_1$-complete sets

How does one show that a specific set is *not* Borel? A related question is: Given a definition of a set in second order arithmetic, how can we tell that there is not an easier definition (in the sense that it uses less quantifier changes, no function quantifiers etc.)? The notion of **completeness** for classes in Polish spaces provides a general method to answer such questions.

```{prf:definition}
:label: def-Wadge

Let $X,Y$ be Polish spaces. We say a set $A \subseteq X$ is **Wadge reducible** to $B \subseteq Y$, written $A \leq_{\W} B$, if there exists a continuous function $f: X \to Y$ such that

$$
	x \in A \iff f(x) \in B.
$$ 
```

The important fact about Wadge reducibility is that it preserves classes closed under continuous preimages.

```{prf:proposition}
:label: prop-Wadge-preimages

Let ${}\Gamma$ be a family of subsets in Polish spaces (such as the classes of the Borel or projective hierarchy). If ${}\Gamma$ is closed under continuous preimages, then $A \leq_{\W} B$ and $B \in \Gamma$ implies $A \in \Gamma$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

If $A \leq_{\W} B$ via $f$, then $A = f^{-1}(B)$.
```

```{prf:definition}
:label: def-completeness

A set $A \subseteq X$ is **${}\Gamma$-complete** if $A \in \Gamma$ and for all $B \in \Gamma$, $B \leq_{\W} A$. 
```

${}\Gamma$-complete sets can be seen as the most complicated members of ${}\Gamma$. In particular, for the $\bSigma/\bPi$ classes complete sets cannot be members of the dual class. For instance, a $\PP{1}$-complete set cannot be $\PS{1}$, since this would mean it is Borel, and hence every $\PP{1}$ set would be Borel, which we have seen is not true.


If $A \subseteq \Baire \times \Baire$ is $\Baire$-universal for some class ${}\Gamma$ in the Borel or projective hierarchy, then the set

$$
	\{ \alpha \oplus \beta \colon (\alpha,\beta) \in A \}
$$

is ${}\Gamma$-complete, where $\oplus$ here denotes the pairing function for reals

$$
	\alpha\oplus\beta(n) = \begin{cases}
	 	\alpha(k) & n = 2k, \\
		\beta(k) & n = 2k+1.
	\end{cases}
$$

Since $\oplus$ is continuous, and $B \in \Gamma$ if and only if $B = A_{\gamma}$ for some $\gamma\in \Baire$, we have in that case that $B \leq_{\W} A$ via the mapping

$$
	f(\beta) = \gamma\oplus\beta.
$$

It follows that complete sets exist for all levels of the Borel and projective hierarchy. However, the universal sets they are based on are rather abstract objects. Complete sets are most useful when we can show that a *specific property* implies completeness. We will encounter next an important example for the class of co-analytic sets.

(sec-well-founded)=
## Well-founded relations and well-orderings
 
Given a real in $\beta \in \Baire$, we can associate with $\beta$ a binary relation $E_\beta$ on $\Nat$:

$$
E_\beta(m,n) :\iff \beta(\Tup{m,n}) = 0.
$$

A binary relation $E$ on a set $X$ is **well-founded** if every non-empty $Y \subseteq X$ has an $E$-minimal element $y_0$, that is, there is no $z \in Y$ with $E(z,y)$.

Let

$$
	\WF = \{\beta \in \Baire \colon \text{$E_\beta$ is well-founded} \}.
$$

Using $\DC$, having a minimal element is equivalent to the non-existence of an infinite descending sequence. So we can rewrite: 

$$
	 \beta \in \WF \iff \forall \gamma \in \Baire \: \exists n \; [ \neg \gamma(n+1) E_\beta \gamma(n) ],
$$

and hence $\WF$ is $\Pi^1_1$.

A closely related set is

$$
	\WOrd = \{\beta \in \Baire \colon \text{$E_\beta$ is a well-ordering} \}.
$$

Then 

$$
	\beta \in \WOrd \iff \beta \in \WF  \text{ and $E_\beta$ is a linear ordering}.
$$

Coding a linear order is easily seen to be $\Pi^0_1$, hence $\WOrd$ is $\Pi^1_1$, too.


```{prf:theorem} 
:label: thm-WF-Wadge-complete

The sets $\WF$ and $\WOrd$ are $\PP{1}$-complete.
```

```{prf:proof}
:class: dropdown
:nonumber: true

We have seen in the chapter on {ref}`chap-trees` that a tree has an infinite path  if and only if the inverse prefix ordering is ill-founded. Trees can be coded as reals, and hence {prf:ref}`prop-norm-form-coanalytic` yields immediately that $\WF$ is $\PP{1}$-complete.

For $\WOrd$ we use the Kleene-Brouwer ordering and refer to {prf:ref}`prop-KB-wellorder`.
```

The theorem lets us gain further insights in the structure of co-analytic sets. If $\alpha \in \Baire$ codes a well-ordering on $\Nat$, let
\begin{equation*}
	\Norm{\alpha} = \text{ order type of well-ordering coded by $\alpha$}.
\end{equation*}

It is clear that $\Norm{\alpha} < \omega_1$. For a fixed ordinal $\xi < \omega_1$, we let
\begin{equation*}
	\WOrd_\xi = \{ \alpha \in \WOrd \colon \Norm{\alpha} \leq \xi \}.
\end{equation*}

```{prf:lemma}
:label: lem-bounded-rank-Borel

For any $\xi < \omega_1$, the set $\WOrd_\xi$ is Borel.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $\alpha \in \Baire$. We say $m \in \Nat$ is in the **domain** of $E_\alpha$, $m \in \Op{dom}(E_\alpha)$, if
\begin{equation*}
	\exists n \: [ m E_\alpha n \; \vee \; n E_\alpha m].
\end{equation*}

It is clear from the definition of $E_\alpha$ that $\Op{dom}(E_\alpha)$ is Borel. For $\xi < \omega_1$, let 
\begin{equation*}
	B_\xi = \{ (\alpha,n) \colon E_\alpha \Rest{\{m \colon m E_\alpha n\}} \text{ is a well-ordering of order type $\leq \xi$} \}
\end{equation*}

We show by transfinite induction that every $B_\xi$ is Borel. Suppose $B_\zeta$ is Borel for all $\zeta < \xi$. Then, since $\xi$ is countable, $\bigcup_{\zeta < \xi} B_\zeta$ is Borel, too. But
\begin{equation*}
	(\alpha,n) \in B_\xi \iff \forall m \: [m E_\alpha n \: \Rightarrow \: (\alpha,m) \in \bigcup_{\zeta < \xi} B_\zeta],
\end{equation*}
and from this it follows that $B_\xi$ is Borel. Finally, note that
\begin{equation*}
	\alpha \in \WOrd_\xi \iff \forall n \; [n \in \Op{dom}(E_\alpha) \: \Rightarrow \: (\alpha,n) \in B_\xi],
\end{equation*}
which implies that $\WOrd_\xi$ is Borel.
```


```{prf:corollary} 
:label: cor-coanal-union-Borel

Every $\PP{1}$ set is a union of $\aleph_1$ many Borel sets.
```

```{prf:proof}
:class: dropdown
:nonumber: true
	
Since $\WOrd$ is $\PP{1}$-complete, every co-analytic set $A$ is the preimage of $\WOrd$ for some continuous function $f$. We have
\begin{equation*}
	\WOrd = \bigcup_{\xi < \omega_1} \WOrd_\xi,
\end{equation*}
and hence
\begin{equation*}
	A = \bigcup_{\xi < \omega_1}  f^{-1}(\WOrd_\xi).
\end{equation*}
Since continuous preimages of Borel sets are Borel, the result follows.
```

If we work instead with the set
\begin{align*}
	C_\xi = & \{ \alpha \colon \alpha \in \WOrd_\xi \text{ or } \\
			& \exists n\in \Op{dom}(E_\alpha) 
			& [E_\alpha \Rest{ \{m : m E_\alpha n\} } \text{ is a well-ordering of order type $\xi$}] \},	
\end{align*}
then we get that $\WOrd = \bigcap_{\xi < \omega_1} C_\xi$, and hence

```{prf:corollary} 
:label: cor-aleph-union-intersect

Every $\PP{1}$ set can be obtained as a union or intersection of $\aleph_1$-many Borel sets. Consequently, the same holds for every $\PS{1}$ set.
```

The previous results allow us to solve the cardinality problem of co-analytic sets at least partially.

```{prf:corollary}
:label: cor-coanalytic-cardinality

Every $\PP{1}$ set is either countable, of cardinality $\aleph_1$, or of cardinality $2^{\aleph_0}$.
```


We conclude the chapter with another application of  {prf:ref}`lem-bounded-rank-Borel` – a useful tool for analyzing $\bSigma^1_1$ sets:

```{prf:theorem} $\bSigma^1_1$-bounding
:label: thm-sigma11-bounding

For every analytic $A \subseteq \WOrd$ there exists an ordinal $\nu < \omega_1$ such that

$$
	\forall x \in A \;\; \Norm{x} < \nu.
$$
```

```{prf:proof}
:class: dropdown
:nonumber: true

If such a $\nu$ did not exist, then

$$
	\alpha \in \WOrd \iff \exists \nu \: [\alpha \in A \; \wedge \; \WOrd_\nu].
$$

The right-hand side is $\bSigma^1_1$, and hence $\WOrd$ would be $\bSigma^1_1$, contradiction.
```

An analogous statement holds for $\WF$, with respect to the rank function $\rho$ of a well-founded relation.



<!-- ## Uniformization

Two important structural properties of pointclasses are **separation** and **uniformization**.

We have seen an instance of separation in  -->