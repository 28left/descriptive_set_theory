(cardinals)=
# Cardinals

## Cardinality
Cardinal numbers capture the notion of the **cardinality** of a set. We measure the cardinality of a set relative to other sets by saying sets $a,b$ have the **same cardinality** if there exists a bijection between them.

We use the following notation:
\begin{align*}
a \sim b \quad & : \Leftrightarrow \quad \text{ there exists a bijection } a \leftrightarrow b \\
a \preceq b \quad & : \Leftrightarrow \quad \text{ there exists an injection } a \hookrightarrow b \\
a \prec b \quad & : \Leftrightarrow \quad a \preceq b \; \wedge \; a \nsim b
\end{align*}

It is straightforward to show $\sim$ is an equivalence relation and that $\preceq$ is transitive. $\preceq$ is obviously also reflexive, but if we mod out by $\sim$, do we get a partial order? In other words, do we have antisymmetry in the form
```{aside}
Relations that are reflexive and transitive are called **preorders**.
```

$$
a \prec b \; \wedge \; b \preceq a \quad \overset{?}{\Rightarrow} \quad a \sim b.
$$
This follows pretty easily if we use the Axiom of Choice (in form of the well-ordering principle $\WO$), but it is one of the few fundamental results in the theory of cardinality one can prove without using Choice.


```{danger} Cantor-Schröder-Bernstein Theorem
:icon: false

Let $a$ and $b$ be sets. If there is an injection from $a$ to $b$ and an injection from $b$ to $a$, then there exists a bijection between $a$ and $b$.
```
```{note} Warmup
:icon: false
:class: dropdown

Find a bijection between $[0,1)$ and $[0,1]$.
```

````{hint}
:icon: false
:class: dropdown

"Proof by picture"
```{image} ./schroeder-bernstein.png
:alt: Proof of the Cantor-Schröder-Bernstein Theorem
:width: 800px
:align: center
```
````
The next result shows that this order is linear. To prove it, we have to use Choice.

```{danger} Theorem (Hartogs)
:icon: false
:label: thm-hartogs

For any sets $a,b$,
$$
a \preceq b \; \vee \; b \preceq a.
$$
```

```{prf:proof}
:nonumber: true
:class: dropdown

By the well-ordering principle $\WO$, there exist ordinals $\alpha, \beta$ such that $a \sim \alpha$ and $b \sim \beta$. Since any two ordinals are comparable by $<$, @pro-order-ordinals implies that $\alpha \subseteq \beta$ or $\beta \subseteq \alpha$, which easily yields the theorem.
```
Cantor's famous result shows that for every set there exists one with greater cardinality. In particular, the order $\preceq$ is infinite. Given a set $a$, we denote its **power set** by $\Pow(a)$, 
$$
\Pow(a) = \{ b \colon b \subseteq a \}.
$$

```{danger} Cantor's Theorem
:icon: false
:label: thm-cantor

For every set $a$,
$$
a \prec \Pow(a).
$$
```

```{prf:proof}
:nonumber: true
:class: dropdown

$x \mapsto \{x\}$ is an injection from $a$ to $\Pow(a)$, hence $a \preceq \Pow(a)$. 
Now assume $a \sim \Pow(a)$ via a bijection $f$. We use a diagonal argument (as for the case $a = \N$) to derive a contradiction. Let $d: = \{x \in a\colon x \notin f(x) \}$. As $f$ is onto, there exists $b \in a$ with $f(b) = d$.
But then
$$
b \in d \; \Leftrightarrow \; b \notin f(b) \; \Leftrightarrow \; b \notin d,
$$
contradiction.
```

## Cardinal numbers

As with ordinals, we would like to choose a system of representatives for the equivalence classes under $\sim$. @thm-hartogs suggests to use ordinals (which we can compare using the well-ordering of ordinals). We therefore assume the Axiom of Choice (so every set has a well-ordering). One issue that remains is that a set can have well-orderings of different lengths (as we saw in the case of the natural numbers $\Nat$). But since the ordinals are well-ordered, we can choose the *least* one of the same cardinality.

```{prf:definition}
:nonumber: true

The **cardinality** $|a|$ of a set $a$ is defined as
$$
|a| = \min \{ \alpha \in \Ord \colon \alpha \sim a \}.
$$
```

```{aside}
We have to be careful what we are taking a minimum over, since there could be a lot (i.e. "more than a set" many ordinals equinumeral to $a$.) We can avoid this by first using $\AC$ to find *one* ordinal $\beta \sim a$, and then taking the minimum ordinals $\leq \beta$. As we will see later, the latter will always be a set.
```

```{prf:lemma}
:nonumber: true

- $a \sim b \quad \iff \quad |a| = |b|$
- $a \preceq b \quad \iff \quad |a| \leq |b|$
- $a \prec b \quad \iff \quad |a| < |b|$
```

An ordinal ${}\kappa$ is a **cardinal** if it is the cardinality of some set. Equivalently, ${}\kappa$ is a cardinal if 
$$
\forall \beta < \kappa \; \beta \prec \kappa.
$$
We usually use Greek letters from the middle of the alphabet, $\kappa, \mu, \nu, \dots$ to denote cardinals.

Given a cardinal ${}\kappa$, we let $\kappa^+$ be the **cardinal successor** of ${}\kappa$, i.e. 
$$
\kappa^+ = \min \{ \nu \leq |\Pow(\kappa)| \colon  \kappa \prec \nu \}
$$
By @thm-cantor (and the Axiom of Choice), we have 
$$
  \kappa \prec \kappa^+ \preceq |\Pow(\kappa)|,
$$
and as ordinals,
$$
  \kappa < \kappa^+ \leq |\Pow(\kappa)|.
$$

All finite ordinals
$$
0, 1, 2, 3, \dots
$$

The **first infinite cardinal is ${}\omega$**, the cardinality of all countably infinite sets. 

We can use ordinals to enumerate all infinite cardinals. This the **aleph**-sequence.

\begin{align*}
  \aleph_0 &  \; := \; \omega\\
  \aleph_{\alpha+1}  & \; := \; \aleph^+_\alpha \\
  \aleph_\lambda  &\;  := \; \sup \{ \aleph_\beta \colon \beta < \alpha \}
\end{align*}

```{exercise}
:nonumber: true

Show that the supremum of a set of cardinals is a cardinal. (In particular, $\aleph_\lambda$ in the definition above is a cardinal.)
```

As in the case of ordinals, cardinals of the form $\aleph_{\alpha+1}$ are called **successor cardinals**, whereas alephs whose index is a limit ordinals are called **limit cardinals**.
```{exercise}
:nonumber: true

Show that every cardinal is an aleph, i.e. for every cardinal ${}\kappa$ there exists an ordinal $\alpha$ such that $\kappa = \aleph_\alpha$.
```
While every cardinal is an ordinal, not every ordinal is a cardinal. For example
$$
\aleph_0 = \omega = |\omega +1| = | \omega +2|= \ldots = |\omega+ \omega| = | \mathbb{Z}| =  |\mathbb{N} \times \mathbb{N}| = | \mathbb{Q}|.
$$

The next cardinal is
$$
  \aleph_1 = \aleph_0^+ = \omega_1 = \{\alpha \in \Ord\colon \alpha \text{ countable}\}.
$$
Between $\aleph_0$ and $\aleph_1$ are uncountably many ordinals, all of which are countable. The ordinal $\omega_1$ will play an important role when we close sets under countably infinite operations (like the Borel sets). 

We know the set of reals is uncountable, so at this time we are able to conclude
\begin{equation*}
|\mathbb{R}| = \ge \aleph_1, \quad
|\mathcal{P}(\mathbb{R})| \ge \aleph_2, \ldots
\end{equation*}


## Operations on cardinals

What can we say about the cardinality of unions, products, etc.?

```{exercise}
:nonumber: true

Show that $|\R \times \R| = |\R|$.
```

This is an instance of a more general result. We can define arithmetic operation on cardinals by looking at the cardinalities of the corresponding set theoretic operations.

\begin{align*}
\kappa + \lambda \quad & = \quad  |(\kappa  \times \{0\}) \cup (\lambda  \times \{1\})| & \qquad (\text{disjoint union}) \\
\kappa \cdot \lambda \quad & =  \quad  |\kappa  \times \lambda | & \qquad (\text{product})\\
\kappa^{\lambda} \quad & = \quad   |\{f \colon f: \lambda \to \kappa \}| & \qquad (\text{exponentiation})
\end{align*}

```{exercise}
:nonumber: true

Verify that for finite cardinalities, the operations defined above agree with the usual arithmetic operations on natural numbers.
```
It turns out for infinite cardinals, $+$ and $\cdot$ are trivial. This is mostly due to the fact that there is a nice (canonical) well-ordering of $\Ord\times\Ord$.


### The canonical well-ordering of ordinal pairs

We define a bijection $F: \Ord \times \Ord \leftrightarrow \Ord$. 
As a first step, we define the **lexicographic order** $<_{\lex}$ on $\Ord \times \Ord$:
\begin{equation*}
(\alpha, \beta) <_{\lex} (\gamma, \delta) \quad : \iff \quad \alpha < \gamma \, \vee \, ( \alpha = \gamma \, \wedge \beta < \delta).
\end{equation*}

This is a linear order in which every non-empty subset has a minimal element, but we have to be careful since in this order all pairs of the form $(0,\xi)$, $\xi \in \Ord$, precede $(1,0)$. And we saw that there is no set of the form $\{(0,\xi) \colon  \xi \in \Ord\}$. Gödel modified this order by *presorting* according to the maximum of the pair:
\begin{align}
(\alpha, \beta) <_g (\gamma, \delta) \; : \iff \; & \max(\alpha,\beta) <  \max(\gamma,\delta)  \\
  & \qquad \vee \; (\max(\alpha,\beta) =  \max(\gamma,\delta)  \: \wedge \: (\alpha, \beta) <_{\lex} (\gamma, \delta)).
\end{align}
This yields a linear order in which every element has only a *set* of predecessors. Moreover, the minimality condition is still satisfied: Let $A \subseteq \Ord \times \Ord$ be non-empty. We find the least element of $A$ by 
- first finding the least $\gamma_0 \in \{ \max(\alpha,\beta) \colon  (\alpha,\beta)\in A\}$,
- then finding the least $\alpha_0 \in \{\alpha \colon \exists \beta \;( (\alpha,\beta)\in A \wedge  \max(\alpha,\beta) = \gamma_0) \}$,
- and finally finding the least $\beta_0 \in \{\beta \colon (\alpha_0,\beta) \in A \wedge \max(\alpha_0,\beta) = \gamma_0 \}$.

It is straightforward to verify that $(\alpha_0, \beta_0)$ is the smallest element of $A$ with respect to $<_g$.

Enumerating pairs of ordinals along $<_g$ yields and order isomorphism $F: \Ord \times \Ord \to \Ord$, i.e.
$$  
 (\alpha, \beta) <_g (\gamma, \delta) \; \iff \;  F(\alpha, \beta) < F(\gamma, \delta).
$$


which is a consequence of the following theorem.

```{danger} Hessenberg's Theorem
:icon: false

Let $\kappa$ be an infinite cardinal. Then 
$$
  \kappa \cdot \kappa = \kappa.
$$
```

```{prf:proof}
:nonumber: true
:class: dropdown

that enumerate pairs of ordinals in the following way: 
> For any infinite cardinal $\kappa$, $F\Rest{\kappa\times \kappa}$ is a bijection from $\kappa \times \kappa$ to ${}\kappa$. 

```
