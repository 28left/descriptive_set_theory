(ch_perfect)=
# Perfect Subsets of the Real Line

```{math}
\newcommand{\N}{\mathbb{N}}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\CH}{\mathsf{CH}}
\newcommand{\eps}{\varepsilon}
\newcommand{\Cant}{2^{\Nat}}
\newcommand{\Rest}[1]{\mid_{#1}}

\DeclareMathOperator{\diam}{diam}
```

Descriptive set theory nowadays is understood as the study of definable subsets of Polish Spaces. Many of its problems and techniques arose out of efforts to answer basic questions about the real numbers. A prominent example is the _Continuum Hypothesis_ ($\CH$):

```{admonition} Continuum Hypothesis (Cantor, 1890s)
:class: hint

If $A \subseteq \Real$ is uncountable, then there exists a bijection between $A$ and $\Real$. That is, is every uncountable subset of $\Real$ is of the same cardinality as $\Real$.
```

Early approaches to this problem tried to show that $\CH$ holds for a number of sets with an easy topological structure.

```{admonition} Exercise
:class: attention
Show that every open set in $\R$ satisfies $\CH$ (in the sense that it either countable or can be mapped bijectively to $\R$).
```

```{margin}
There are some divergences in terminology. Some authors call an accumulation point a *limit point*. We reserve the latter term for *any point that is the limit of a sequence of points*
from a given set. Hence every member of a set is a limit point of that set. In particular, isolated members of a set are limit points.
```

For closed sets, the situation is less clear. Given a set $A \subseteq \Real$, we call $x \in \Real$ an **accumulation point** of $A$ if

$$
\forall \epsilon > 0 \: \exists z \in A \: [z \neq x \: \& \: z \in U_\eps(x)],
$$

where $U_\eps(x)$ denotes the standard $\eps$-neighborhood of $x$ in $\Real$

```{prf:definition}
:label: def-perfect

A non-empty set $P \subseteq \Real$ is **perfect** if it is closed and every point of $P$ is an accumulation point.
```

In other words, a perfect set is a closed set that has no isolated points. We can also deduce that for a perfect set $P$, every neighborhood of a point $p \in P$ contains infinitely many points from $P$.

````{margin}
```{figure} ./images/Cantor_set.png
Cantor set
```
````

Obviously, $\Real$ itself is perfect, as is any closed interval in $\Real$. There are totally disconnected perfect sets, such as the **middle-third Cantor set** in $[0,1]$

```{prf:theorem} Cantor, 1884
:label: thm-card-perfect-sets

A perfect subset of $\Real$ has the same cardinality as $\Real$.
```

````{prf:proof}
Let $P \subseteq \Real$ be perfect. We construct an injection from the set $\Cant$ of all infinite binary sequences into $P$. An infinite binary sequence $\xi = \xi_0 \xi_1 \xi_2 \dots$ can be identified with a real number $\in [0,1]$ via the mapping

$$
\xi \mapsto \sum_{i \geq 0} \xi_i 2^{-i-1}.
$$

Note that this mapping is onto. It follows that the cardinality of $P$ is at least as large as the cardinality of $[0,1]$. The [Cantor-Schröder-Bernstein Theorem](https://en.wikipedia.org/wiki/Schröder–Bernstein_theorem) (for a proof see e.g. {cite}`jech2003a`)   implies that $|P| = |\R|$.

To construct the desired injection, choose $x \in P$ and let $\eps_0 = 1 = 2^0$. Since $P$ is perfect,  $P \cap U_{\eps_0}(x)$ is infinite. Let $x_0 \neq x_1$ be two points in $P \cap U_{\eps_0}(x)$, distinct from $x$. Let $\eps_1$ be such that $\eps_1 \leq 1/2$, $U_{\eps_1}(x_0), U_{\eps_1}(x_1) \subseteq U_{\eps_0}(x)$, and $\overline{U_{\eps_1}(x_0)} \cap \overline{U_{\eps_1}(x_1)} = \emptyset$, where $\overline{U}$ denotes the closure of $U$.

We can iterate this procedure recursively with smaller and smaller diameters, using the fact that $P$ is perfect. This gives rise to a so-called **Cantor scheme**, a family of open balls $(U_\sigma)$ satisfying certain *nesting conditions*. Here the index $\sigma$ is a finite binary sequence, also called a *string*. A Cantor scheme is defined by the following properties.

1. $\diam(U_\sigma) \leq 2^{-|\sigma|}$, where $|\sigma|$ denotes the length of $\sigma$.
2. If $\tau$ is a proper extension of $\sigma$, then $U_\tau \subset U_\sigma$.
3. If $\tau$ and $\sigma$ are *incompatible* (i.e. neither extends the other), then
    \begin{equation*}
        U_\tau \cap U_\sigma = \emptyset.
    \end{equation*}
4. The center of each $U_\sigma$, call it $x_\sigma$, is in $P$.

```{figure} ./images/Cantor_Scheme.png
:height: 400px
:name: Cantor Scheme

Nested structure of a Cantor scheme
```

Let $\xi$ be an infinite binary sequence. Given $n \geq 0$, we denote by $\xi\Rest{n}$ the string formed by the first $n$ bits of $\xi$, i.e.

$$
\xi\Rest{n} = \xi_0 \xi_1 \dots \xi_{n-1}.
$$

The finite initial segments give rise to a sequence $x_{\xi\Rest{n}}$ of centers. By properties (1.) and (2.), this is a Cauchy sequence. By (4.), the sequence lies in $P$. Since $P$ is closed, the limit $x_\xi$ is in $P$. By (3.), the mapping $\xi \mapsto x_\xi$ is well-defined and injective.
````

```{prf:theorem} Cantor-Bendixson
:label: cantor-bendixson
Every uncountable closed subset of $\Real$ contains a perfect subset.
```

```{prf:proof}
Let $C \subseteq \Real$ be uncountable and closed. We say $z \in \Real$ is a *condensation point* of $C$ if

$$
    \forall \eps > 0 \:[ U_\eps(z) \cap C \text{ uncountable}].
$$

Let $D$ be the set of all condensation points of $C$. Note that $D \subseteq C$, since every condensation point is clearly an accumulation point and $C$ is closed.

Furthermore, we claim that $D$ is perfect. Clearly $D$ is closed. Suppose $z \in D$ and $\eps > 0$. Then $U_\eps(z) \cap C$ is uncountable. We would like to conclude that $U_\eps(z) \cap D$ is uncountable, too, since this would mean in particular that $U_\eps(z) \cap D$ is infinite. The conclusion holds if $C \setminus D$ is countable.

To show that $C\setminus D$ is countable, assume that $y \in C \setminus D$. Then, for some $\delta > 0$,  $U_\delta(y) \cap C$ is countable. We can find and interval $I(y) \subseteq U_\delta(y)$ that contains $y$ and has rational endpoints. There are at most countably many intervals with rational endpoints and hence for each $y \in C \setminus D$ there are at most countably many choices for $I(y)$. Thus, we have

$$
    C\setminus D \subseteq \bigcup_{y \in C \setminus D} I_y \cap C.
$$

The right hand side is a countable union of countable sets, hence countable.
```

We will later encounter an alternative (more constructive) proof that gives additional information about the complexity of the closed set $C$. For now we conclude with the fact we were aiming to prove in this lecture.

```{prf:corollary}
Every closed subset of $\Real$ is either countable or of the cardinality of the continuum.
```

The results of this lecture give us a blueprint on how to verify the Continuum Hypothesis for a given family $\mathcal{F}$ of sets (of reals):

> Show that every set in $\mathcal{F}$ is either countable or has a perfect subset.

Over the next few lectures we will see for which families we can verify this **perfect set property**.
