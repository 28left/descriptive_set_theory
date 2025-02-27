# Analytic Sets


```{prf:definition}
A subset $A$ of a Polish space $X$ is **analytic** if it is empty or there exists a continuous function $f:\Baire \to X$ such that $f(\Baire) = A$.
```

We will later see that the analytic sets correspond to the sets definable by means of $\Sigma^1_1$ formulas, that is formulas in the language of second order arithmetic that have **one existential function quantifier**.

Therefore, we will denote the analytic subsets of $X$ also by

$$
	\PS{1}(X).
$$ 

Here are some simple properties of analytic sets.

```{prf:proposition}
:label: prop-prop-analytic

- **(i)** Every Borel set is analytic.
- **(ii)** A continuous image of analytic set is analytic.
- **(iii)** Countable unions of analytic sets are analytic.
```

```{prf:proof}
:class: dropdown
:nonumber: true

(i): This follows directly from {prf:ref}`cor-Borel-image-closed` of the previous section.

(ii): The composition of continuous mappings is continuous.

(iii): Let $A_n$ be analytic and $f_n:\Baire \to X$ such that $f_n(\Baire) = A_n$. Define $f: \Baire \to X$ by

$$
    f(m,\alpha) = f_n(\alpha).
$$

Then $f$ is continuous and $f(\Baire) = \bigcup_n A_n$.
```

We can use our previous results about Borel sets to give various equivalent characterizations of analytic sets.

```{prf:proposition}
:label: characterization-analytic

For a subset $A$ of a Polish space $X$, the following are equivalent.
- **(i)** $A$ is analytic.
- **(ii)** $A$ is empty or there exists a Polish space $Y$ and a continuous $f:Y \to X$ such that $f(Y) = A$.
- **(iii)** $A$ is empty or there exists a Polish space $Y$, a Borel set $B \subseteq Y$ and a continuous $f:Y \to X$ such that $f(B) = A$. 
- **(iv)** $A$ is the **projection** of a closed set $F \subseteq \Baire \times X$ along $\Baire$.
- **(v)** $A$ is the projection of a $\BP{2}$ set $G \subseteq  \Cant \times   X  $ along $\Cant$.
- **(vi)** $A$ is the projection of a Borel set $B \subseteq X\times Y$ along $Y$, for some Polish space $Y$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

(i) $\Leftrightarrow$ (ii): Follows from the [Lusin-Souslin Theorem](thm-Polish-bijection-Baire) and {prf:ref}`prop-prop-analytic` (ii).

(ii) $\Leftrightarrow$ (iii): Follows from the [corollary to the Lusin-Souslin Theorem](cor-Borel-image-closed) and {prf:ref}`prop-prop-analytic` (ii).

(i) $\Rightarrow$ (iv):  Let $f:\Baire \to X$ be continuous, $f(\Baire) = A$. Then 

$$
    x \in A \iff \exists \alpha \; (\alpha,x) \in \Op{Graph}(f),
$$

hence $A$ is the projection of the closed set $\Op{Graph}(f)$ along $\Baire$.

(iv) $\Rightarrow$ (iii): Clear, since projections are continuous.

(iv) $\Rightarrow$ (v): $\Baire$ is homeomorphic to a $\BP{2}$ subset of $\Cant$. (Exercise!)

(v) $\Rightarrow$ (vi), (vi) $\Rightarrow$ (iii): Obvious.
```


## The Lusin Separation Theorem

In a course on computability theory one learns that there are **effectively inseparable** disjoint computably enumerable sets. i.e. disjoint c.e. sets $W,Z \subseteq \Nat$ for which no recursive set $A$ exists with $W \subseteq A$ and $A \cap Z = \emptyset$. 

In contrast to this, disjoint analytic sets can always be separated by a Borel set - they are **Borel separable**.

```{prf:theorem} Lusin
:label: thm-Lusin-separation

Let $A, B \subseteq X$ be disjoint analytic sets. Then there exists a Borel $C \subseteq X$ such that

$$
        A \subseteq C \quad \text{ and } \quad B \cap C = \emptyset,
$$
```

````{prf:proof}
:class: dropdown
:nonumber: true

Let $f:\Baire \to A$ and $g:\Baire \to B$ be continuous surjections.

We argue by contradiction. The key idea is: if $A$ and $B$ are Borel inseparable, then, for some $i,j \in \Nat$, $A_{\Tup{i}} = f(\Cyl{\Tup{i}})$ and $B_{\Tup{j}} = g(\Cyl{\Tup{j}})$ are Borel inseparable. 

This follows from the following observation:

```{card} $(\ast)$
If the sets  $R_{m,n}$ separate the sets  $P_m, \, Q_n$ (for each $m,n$), then $R = \bigcup_m \bigcap_n R_{m,n}$ separates the sets $P =  \bigcup_m P_m, \, Q =  \bigcup_n Q_n.$
```
So, by using $(\ast)$ repeatedly, we can construct sequences $\alpha, \beta \in \Baire$ such that for all $n$,
$A_{\alpha\Rest{n}}$ and $B_{\beta\Rest{n}}$ are Borel inseparable, where

$$
    A_{\sigma} = f(\Cyl{\sigma}) \quad \text{ and } \quad B_{\sigma} = g(\Cyl{\sigma}).
$$

Then we have $f(\alpha) \in A$ and $g(\beta) \in B$, and since $A$ and $B$ are disjoint, $f(\alpha) \neq g(\beta)$. Let $U,V$ be disjoint open sets such that $f(\alpha) \in U$, $g(\beta) \in V$. Since $f$ and $g$ are continuous, there exists $N$ such that $f(\Cyl{\alpha\Rest{N}}) \subseteq U$, $g(\Cyl{\beta\Rest{N}}) \subseteq V$, hence $U$ separates $A_{\alpha\Rest{N}}$ and $B_{\beta\Rest{N}}$, contradiction.
````

The Separation Theorem yields a nice characterization of the Borel sets.

```{prf:theorem} Souslin
:label: Borel-Delta11

If a set $A$ and its complement $\Co{A}$ are both analytic, then $A$ is Borel.
```

```{prf:proof}
:class: dropdown
:nonumber: true

In {prf:ref}`thm-Lusin-separation`, chose $A = A$ and $B = \Co{A}$.
```

It follows from {prf:ref}`thm-Souslin-Borel-images` and the {prf:ref}`Lusin separation theorem <thm-Lusin-separation>` that the analytic sets are not closed under complements. 

Sets whose complement is analytic are called **co-analytic**. Analogous to the levels of the Borel hierarchy, the co-analytic subsets of a Polish space $X$ are denoted by

$$
	\PP{1}(X).
$$

If we define, again analogy to the Borel hierarchy,

$$
	\bDelta^1_1(X) = \PS{(1)}(X) \cap \PP{1}(X),
$$

then Souslin's Theorem states that

$$
	\Op{Borel}(X) = \bDelta^1_1(X).
$$




## The Souslin operation

Souslin schemes give an alternative presentation of analytic sets which will be useful later.

```{prf:definition}
A **Souslin scheme** on a set $X$ is a family $P = (P_\sigma)_{\sigma\in \Nstr}$ of subsets of $X$ indexed by $\Nstr$.

The **Souslin operation** $\mathcal{A}$ for a Souslin scheme is given by 

$$
    \mathcal{A}P = \bigcup_{\alpha \in \Baire}  \bigcap_{n \in \Nat} P_{\alpha\Rest{n}}.
$$

This means
\begin{equation*} \tag{$**$}
    x \in \mathcal{A}P \iff \exists \alpha \in \Baire \; \forall n \in \Nat \; x \in P_{\alpha\Rest{n}}.
\end{equation*}
```

The analytic sets are precisely the sets that can be obtained by Souslin operations on closed sets. If a $\Gamma$ is a family of subsets of a set $X$, we let

$$
	\mathcal{A}\Gamma = \{\mathcal{A}P \colon \text{ $P = (P_\sigma)$ is a Souslin scheme with $P_\sigma \in \Gamma$ for all $\sigma$} \}.
$$

```{prf:theorem}
:label: analytic-Souslin-op

$$
	\PS{1}(X)\; = \; \mathcal{A}\,\BP{1}(X).
$$
```

```{prf:proof}
:class: dropdown
:nonumber: true

Suppose $f: \Baire \to X$ is continuous with $f(\Baire) = A$. Then 
\begin{equation*}
x \in A \iff \exists \alpha  \in \Baire \; \forall n \in \Nat \; x \in \Cl{f(\Cyl{\alpha\Rest{n}})}.
\end{equation*}

Hence if we let $P_\sigma = \Cl{f(\Cyl{\sigma})}$, then
\begin{equation*}
A =  \mathcal{A} \,P,
\end{equation*}
for the Souslin scheme $P = (P_\sigma)$.

To see that any set $A$ in $\mathcal{A}\,\BP{1}(X)$ is analytic, consider ($**$). If the $P_\sigma$ are closed, the condition

$$
    (\alpha,x) \in F \iff \forall n \in \Nat \; x \in P_{\alpha\Rest{n}}
$$

defines a closed subset of $\Baire \times X$ such that $A$ is the projection of $F$ along $\Baire$.
```

Note that the Souslin scheme $(P_\sigma)$ used in the previous proof has the additional property that

$$
	\sigma \Sleq \tau \quad \Rightarrow \quad P_\sigma \supseteq P_\tau.
$$

Such Souslin schemes are called **regular**. By replacing any Souslin scheme $P_\sigma$ with 

$$
	Q_\sigma = \bigcap_{\tau \Sleq \sigma} P_\tau,
$$

we obtain a regular Souslin scheme $Q = (Q_\sigma)$ with $\mathcal{A} \, Q = \mathcal{A}\, P$. Moreover, if the $P_\sigma$ are from a class $\Gamma$, and $\Gamma$ is closed under finite intersections, then the $Q_\sigma$ are also from $\Gamma$. In particular, **any analytic set can be obtained from a regular Souslin scheme of closed sets** via the Souslin operation. 
