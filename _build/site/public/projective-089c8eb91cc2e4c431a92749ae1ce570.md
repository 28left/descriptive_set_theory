# The Projective Hierarchy

We saw in the previous chapters that analytic sets are projections of closed sets and hence can be written as

$$
	x \in A \iff \exists \alpha \in \Baire \: F(\alpha,x),
$$

where $F \subseteq \Baire \times X$ is closed. It follows that co-analytic sets can be written in the form

\begin{equation*}
	x \in A \iff \forall \alpha \in \Baire \: U(\alpha,x),	
\end{equation*}

for some open $U \subseteq \Baire \times X$.

Using quantifier manipulations that allow to switch number and function quantifiers,

\begin{align*}
	\forall m  \, \exists \alpha \; P(m,\alpha)  & \iff   \exists \beta  \; \forall m \:  P(m,(\beta)_m)\\
	\exists m   \, \forall \alpha \; P(m,\alpha) &\iff \forall \beta  \; \exists m  \;   P(m,(\beta)_m),
\end{align*}

we obtain that *both* the analytic sets and the co-analytic sets are closed under countable unions and intersections.

We have seen ({prf:ref}`prop-prop-analytic`) that the analytic sets are closed under continuous images. Taking continuous images of co-analytic sets, however, leads out of the co-analytic sets.

Using continuous images (or rather, the special case of **projections**), we define the **projective hierarchy**. Recall our notation $\exists^\Nat$ for projection along $\Nat$, with $\forall^\Nat$ its dual. We denote by $\exists^{\Baire}$ and $\forall^{\Baire}$ projection along $\Baire$ and its dual, respectively.


\begin{align*}
 \PS{1}(X) &= \exists^{\Baire} \, \BP{1}(X) \\
 \PP{n}(X) &= \Co{\PS{n}}(X)  \\
 \PS{n+1}(X) &= \exists^{\Baire} \PP{n}(X) \\
 \bDelta^1_n(X) &= \PS{n}(X) \cap \PP{n}(X) \\
\end{align*}
 
Hence a set $P\subseteq X$ is
\begin{align*}
\PS{1}  \quad \text{ iff } \quad & P(x) \Leftrightarrow \exists \alpha \; F(\alpha,x)  \qquad & \text{ for a closed set  } F \subseteq \Baire \times X, \\
\PP{1} \quad \text{ iff } \quad &  P(x) \Leftrightarrow \forall \alpha \; G(\alpha,x)  \qquad & \text{ for an open set  } G \subseteq \Baire \times X, \\
\PS{2} \quad \text{ iff } \quad &  P(x) \Leftrightarrow \exists \alpha \forall \beta \; G(\alpha,\beta,x)  \qquad & \text{ for an open set  } G \subseteq \Baire \times \Baire \times X, \\
\PP{2}  \quad \text{ iff } \quad &  P(x) \Leftrightarrow \forall \alpha \exists \beta \; F(\alpha,\beta, x)  \qquad & \text{ for a closed set  } F \subseteq \Baire \times \Baire \times X, \\
& \vdots
\end{align*}

These characterizations clearly indicate a relation between being projective and being definable in second order arithmetic using function quantifiers. 


## The effective projective hierarchy

We have seen that the Borel sets of finite order correspond to the sets definable (from parameters) by formulas using only number quantifiers (**arithmetical formulas**). A similar relation holds between projective sets and sets definable by formulas using both number and function quantifiers. In fact, the way we defined the projective hierarchy makes this easy to see.

Historically, however, the topological approach and the definability approach happened separately, the former devised by the Russian school of Souslin, Lusin, and others, while the effective approach was pursued by Kleene. Kleene named the sets in his effective hierarchy *analytical* sets, which to this day is a source of much confusion.

```{prf:definition} Kleene
:label: def-analytical-hierarchy

- A set $A \subseteq \Baire$ is (lightface) $\Sigma^1_1$ if there exists a computable relation $R(\sigma, \tau)$ such that 

$$
	\alpha \in A \iff \exists \beta \forall n \: R(\alpha\Rest{n},\beta\Rest{n})
$$

- $A \subseteq \Baire$ is (lightface) $\Pi^1_n$ if $\Co{A}$ is $\Sigma^1_n$.

- $A \subseteq \Baire$ is (lightface) $\Sigma^1_{n+1}$ if it is $\exists^{\Baire} \Pi^1_{n+1}$, that is, if it a projection of a $\Pi^1_{n+1}$ relation along $\Baire$.

- A set that is $\Sigma^1_n$ and $\Pi^1_n$ at the same time is called $\Delta^1_n$.
```

As before, we can relativize this hierarchy with respect to a parameter $\gamma \in \Baire$, by requiring $R$ to be computable only relative to ${}\gamma$. This gives rise to classes $\Sigma^1_n(\gamma)$, $\Pi^1_n(\gamma)$, and $\Delta^1_n(\gamma)$. Then the {prf:ref}`Fundamental Theorem <thm-fundamental>` can be extended to projective sets as follows:

```{prf:theorem}
:label: thm-projective-definable

A set $A \subseteq \Baire$ is $\bSigma^1_n$ $(\bPi^1_n)$ if and only if it is $\Sigma^1_n(\gamma)$ $(\Pi^1_n(\gamma))$ relative to some $\gamma \in \Baire$.
```

$$
	\PS{n} = \bigcup_{\gamma \in \Baire} \Sigma^1_n(\gamma) \qquad \PP{n} = \bigcup_{\gamma \in \Baire} \Pi^1_n(\gamma)
$$



## Examples of projective sets

Here are a few examples of projective sets that occur naturally in mathematics.

**Analytic sets:**
- $\{K \subseteq X \colon K \text{ compact and uncountable} \} $ is a $\PS{1}$ subset of the space $K(X)$ of compact subsets of $X$.

- $\{f \in \mathcal{C}[0,1]\colon f \text{ continuously differentiable on } [0,1]\}$ is a $\PS{1}$ subset of $\mathcal{C}[0,1]$.

**Co-analytic sets:**	
- $\{f \in \mathcal{C}[0,1]\colon f \text{ differentiable on } [0,1]\}$ is a $\PP{1}$ subset of $\mathcal{C}[0,1]$.

- $\{f \in \mathcal{C}[0,1]\colon f \text{ nowhere differentiable on } [0,1]\}$ is a $\PP{1}$ subset of $\mathcal{C}[0,1]$.

- $\Op{WF} = \{\alpha \in \Cant \colon \alpha \text{ codes a well-founded tree on } \Nat \}$ is a $\PP{1}$ subset of the space $\Op{Tr}$ of trees, which can be seen as a closed subspace of $2^{\Nstr}$, and hence is Polish. As we will see, the set $\Op{WF}$ is a prototypical $\PP{1}$ set.
	
**Higher levels:**
- $\{f \in \mathcal{C}[0,1]\colon f \text{ satisfies the Mean Value Theorem } [0,1]\}$ is a $\PP{2}$ subset of $\mathcal{C}[0,1]$.

(Here $f$ satisfies the Mean Value Theorem if for all $a < b \in [0,1]$ there exists $c$ with $a < c < b$ such that  $f'(c)$ exists and $f(b) - f(a) = f'(c)(b-a)$.)



## Some structural properties of the projective hierarchy

The quantifier manipulations mentioned above yield the following closure properties.

```{prf:proposition}
:label: prop-closure-projective

- **(i)** The classes $\PS{n}$ are closed under continuous preimages, countable intersections and unions, and continuous images (in particular, $\exists^{\Baire}$).

- **(ii)** The classes $\PP{n}$ are closed under continuous preimages, countable intersections and unions, and co-projections $\forall^{\Baire}$.

- **(iii)** The classes $\bDelta^1_n$ are closed under continuous preimages, complements, countable intersections and unions. (In particular, they form a $\sigma$-algebra.)
```

To show that the hierarchy is proper, we need the existence of universal sets.


```{prf:proposition}
:label: prop-universal-projective

For every Polish space $X$, there is a $\Baire$-universal set for $\PS{n}$ and for $\PP{n}$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

By induction on $n$. We have seen ({prf:ref}`thm-Souslin-Borel-images`) that there exists a $\Baire$-universal set for $\PS{1}$. Now note that if $U \in \PS{n}(\Baire\times X)$ is $\Baire$-universal for $\PS{n}(X)$, then $\Co{U}$ is $\Baire$-universal for $\PP{n}(X)$, and if $U \subseteq \Baire \times \Baire \times X$ is $\Baire$-universal for $\PP{n}(\Baire \times X)$, then
\begin{equation*}
	V = \{(\alpha,z) \colon \exists \beta \: (\alpha,\beta,z) \in U \}
\end{equation*}
is $\Baire$-universal for $\PS{n+1}$.
```

```{prf:corollary}	
:label: cor-projective-proper 

For every $n \geq 1$, $\PS{n} \nsubseteq \PP{n}$ and $\PP{n} \nsubseteq \PS{n}$. Morover,
\begin{gather*}
	\PS{n} \subsetneq \bDelta^1_{n+1} \subsetneq \PS{n+1} \\
	\PP{n} \subsetneq \bDelta^1_{n+1} \subsetneq \PP{n+1} \\		
\end{gather*}
```

The proof is similar to the proofs of {prf:ref}`thm-Borel-proper` and {prf:ref}`cor-hier-proper`.


## Regularity properties of projective sets

We have seen ({prf:ref}`cor-analytic-measurable` and {prf:ref}`prop-Souslin-Baire`) that all analytic sets are Lebesgue measurable and have the Baire property. Since these properties are closed under complements, it follows that the same holds for co-analytic ($\PP{1}$) sets. Analytic sets also have the perfect-set property, but if you worked out the exercise, you will see that the proof does not carry over to complements of analytic sets. Can we find a different proof?

Similarly, it does not seem impossible to extend the regularity properties (LM) and (BP) to higher levels of the projective hierarchy. We will soon see that there are metamathematical limits that prevent us from doing so.

Without explicitly mentioning it, up to now we have been working in $\ZF$, Zermelo-Fraenkel set theory, plus a weak form of Choice ($\AC_\omega(\Baire)$). If we add the full Axiom of Choice ($\AC$), we saw that the regularity properties do not extend to all sets. Solovay's model of $\ZF+\DC$ shows that the use of a strong version of Choice is necessary for this. 

On the other hand, the proofs gave us no direct indication how 'complex' the non-regular sets we constructed are.
We will study a model of $\ZF$ in which exists a $\bDelta^1_2$ set which neither is Lebesgue measurable nor has the Baire property. This, together with the Solovay model, shows we cannot settle in $\ZF$ alone the question of whether the projective sets are measurable or have the Baire property. We would have to add additional axioms.

A key feature in the construction of a non-measurable $\bDelta^1_2$ set is the use of the well-ordering principle rather than the Axiom of Choice. 

```{prf:proposition} 
:label: prop-non-meas

Suppose $<_W \subseteq \Real\times\Real$ is a well-ordering of $\Real$ of order-type $\omega_1$, then the set

$$
A = \{(x,y) \colon x <_W y\}
$$

neither is Lebesgue measurable nor has the Baire property.
```

Lebesgue measure here refers to the product measure $\lambda \times \lambda$, which is the unique translation invariant measure defined on the Borel $\sigma$-algebra generated by the rectangles $I \times J$, where $I$ and $J$ are open intervals, and $(\lambda\times \lambda)(I \times J) = \lambda(I)\lambda(J)$.

```{prf:proof}
:class: dropdown
:nonumber: true

Since $<_W$ is of order type $\omega_1$, for every $y \in \Real$, the set $A_y = \{x \colon x <_W y \}$ is countable, and hence of Lebesgue measure zero. 

**Fubini's Theorem** implies that if $A \subseteq \Real^2$ is measurable, then 
\begin{equation*}
	(\lambda\times\lambda) (A) = \int \lambda(A_y) d\lambda(y) = 0.
\end{equation*}

So if $A$ is measurable, then $(\lambda\times\lambda) (A) = 0$. The complement of $A$ is $ \Co{A} = \{(x,y) \colon x \geq_W y \}$. As above, for any $x \in \Real$, $(\Co{A})_x = \{y \colon x \geq_W y \}$ is countable, and hence $\lambda(\Co{A})_x = 0$ for all $x$. 

Again, by Fubini's Theorem, $(\lambda\times\lambda) (\Co{A}) = 0$, and thus $(\lambda\times\lambda) (\Real)  = (\lambda\times\lambda) (A \cup \Co{A}) = (\lambda\times\lambda) (A) + (\lambda\times\lambda) (\Co{A}) = 0$, a contradiction.

We can apply a similar reasoning for Baire category, using the Lemma below. The sections $A_y$ and $\Co{A}_x$ are countable, and hence meager. 
```

The following lemma provides a Baire category analogue to Fubini's Theorem.

```{prf:lemma}
:label: lem-Fubini-category

Let $A \subseteq \Real^2$ have the property of Baire. Then $A$ is meager if and only if $A_x = \{y \colon (x,y) \in A\}$ is meager for all $x$ except a meager set.
```

For a proof see {cite}`Kechris:1995a`.	

Therefore, if the Continuum hypothesis ($\CH$) holds in a model and we can well-order $\Real$ (or $\Baire$, $\Cant$) within a certain complexity (as a subset of $\Real^2$), we can find a non-regular set of the same complexity. The question now becomes how (hard it is) to define a well-ordering of $\Real$, and of course if $\CH$ holds.

