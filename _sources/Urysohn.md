# Excursion: The Urysohn Space

```{math}
\newcommand{\N}{\mathbb{N}}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\eps}{\varepsilon}
\newcommand{\Cant}{2^{\Nat}}
\newcommand{\Baire}{\Nat^{\Nat}}
\newcommand{\Ury}{\mathbb{U}}
\newcommand{\Cl}[1]{\overline{#1}}

\DeclareMathOperator{\diam}{diam}
\DeclareMathOperator{\Lip}{Lip}
```

Recall that a mapping $f: X \to Y$ between two metric spaces $(X,d_X)$ and $(Y,d_Y)$ is an **isometry** if

$$
d_Y(f(x),f(y)) = d_X(x,y) \quad \text{ for all $x,y \in X$},
$$

that is, an isometry is a mapping that preserves distances. The function $f$ is also called an *isometric embedding* of $X$ into $Y$. $X$ and $Y$ are *isometric* if there exists a bijective isometry between them.

## Universal spaces

```{prf:theorem}
There exists a Polish metric space $\Ury$ such that every Polish metric space isometrically embeds into $\Ury$.
```

A concrete example of such a space is $\mathcal{C}[0,1]$.

```{admonition} Exercise
:class: tip

Show that the set $\mathcal{C}[0,1]$ of all continuous, real-valued functions on $[0,1]$ with the metric

$$
	d(f,g) = \sup\{|f(x) - g(x)| \colon x \in [0,1] \}
$$

contains an isomorphic copy of any Polish metric space. 
```

But this example is not quite what we have in mind here. There exists another space with a stronger, more "intrinsic" universality property. This space was first constructed by Pavel Urysohn in 1927 {cite}`Urysohn:1927a`.

The construction features an **amalgamation principle** that has surfaced in other areas like model theory or graph theory. 


## Extensions of finite isometries and Urysohn universality

Suppose $X$ is a Polish metric space. Let $D = \{x_1, x_2, \dots\}$ be a countable, dense subset. We first observe that, to isometrically embed $X$ into another Polish space, it is sufficient to embed $D$.

```{prf:lemma}
If $Y$ is Polish, then any isometric embedding $e$ of $D$ into $Y$ extends to an isometric embedding $e^*$ of $X$ into $Y$.
```

```{prf:proof}
Given $z \in X$, let $(x_{i_n})$ be a sequence in $D$ converging to $z$. Since $(x_{i_n})$ converges, it is Cauchy. 

$e$ is an isometry, and thus $y_n := e(x_{i_n})$ is Cauchy, and since $Y$ is Polish, $(y_n)$ converges to some $y \in Y$. Put $e^*(z) = y$. 

To see that this mapping is well-defined, let $(x_{j_n})$ be another sequence with $x_{j_n} \to z$. Then $d(x_{i_n}, x_{j_n}) \to 0$, and hence $d(e(x_{i_n}),e(x_{j_n}) = d(y_n, e(x_{j_n}))\to 0$, implying $e(x_{j_n}) \to y$. 

Furthermore, suppose $w = \lim x_{k_n}$ is another point in $X$. Then (since a metric is a continuous mapping from $Y\times Y \to \Real$)

$$
	d(e^*(z), e^*(w)) = \lim d( e(x_{i_n}),  e(x_{k_n})) = \lim d(  x_{i_n}, x_{k_n}) = d(z,w).
$$

Thus $e^*$ is an isometry.
```

In order to embed $D$, we can now exploit the inductive structure of $\Nat$ and reduce the task to extending finite isometries.

Suppose we have constructed an isometry $e$ between $F_N = \{x_1, \dots, x_N \} \subset D$ and a space $Y$. We would like to extend the isometry to include $x_{N+1}$. For this we have to find an element $y \in Y$ such that for all $i \leq N$

$$
	d_Y(y, e(x_i)) = d_X(x_{N+1}, x_i).
$$

This extension property gives rise to the following definition.

```{prf:definition}
A Polish metric space $(Y,d_Y)$ is **Urysohn universal** if for every finite subspace $F \subset Y$ and any extension $F^* = F \cup \{x^*\}$ with metric a $d^*$ such that 

$$
	d^*|_{F\times F} = d_Y|_{F\times F},
$$

there exists a point $u \in Y$ such that 

$$
	d_{Y}(u,x) = d^*(x^*,x) \quad \text{ for all $x \in F$}.
$$
```

As outlined above, the extension property of Urysohn universal spaces implies the desired isometric embedding property.

```{prf:proposition}
:label: prop-Urysohn-embedding

Let $U$ be a Urysohn universal Polish metric space. For any Polish metric space $(X,d)$ there exists an isometric embedding from $X$ into $U$.
```

But the extension property also implies a strong intrinsic extension property for the Urysohn space itself.

```{prf:proposition}	
:label: prop-Urysohn-extension

Let $U$ be a Urysohn universal Polish metric space. Every isometry between finite subsets of $\Ury$ extends to an isometry of $U$ onto itself.
```

The proof applies the [Back-and-forth method](https://en.wikipedia.org/wiki/Back-and-forth_method) that you may know from the rationals: every order-isomorphism between finite subsets of $\Q$ extends to an automorphism of $(\Q,<)$.

This property (which can be formulated for structures in general) is also known as **homogeneity**. It plays an important role, for example, in 
model theory {cite}`Macpherson:2011a` and in the topological dynamics of automorphism groups of countable structures {cite}`Kechris-Pestov-Todorcevic:2005a`.

```{admonition} Exercise
:class: tip

Show that any two Urysohn universal spaces are isometric.
``` 

We will prove the existence of this unique Polish space, which we denote by $\Ury$, in the following sections. 






## Constructing the Urysohn space -- a first approximation

We first give a construction of a space that has the extension property, but is not Polish. After that we will take additional steps to turn it into a Polish space. 

The crucial idea is to observe that if $X$ is a metric space and $x \in X$, then the mapping $f_{x}: X \to \Real^{\geq 0}$ given by

$$
	f_{x}(y) = d_X(x,y)
$$ 

is $1$-Lipschitz. Recall that a function $g$ between metric spaces $X$ and $Y$  is **$L$-Lipschitz**, $L > 0$ if for every $x,y \in X$,

$$
	d(g(x),g(y)) \leq L \, d(x,y).
$$

Let $\Lip_1(X)$ be the set of $1$-Lipschitz mappings from $X$ to $\Real$. We endow $\Lip_1(X)$ with the supremum metric

$$
	d(f,g) = \sup \{|f(x) - g(x)| \colon x \in X \}.
$$

If $\diam(X) \leq \mathrm{d}$ and $f,g$ are $1$-Lipschitz, then $d(f,g)$ is indeed finite.
However, we will [later](ury-finishing-construction)  need that the resulting space is also bounded. Let  $\Lip^{\mathrm{d}}_1(X)$ be the space of all $1$-Lipschitz functions from $X$ to $[0,\mathrm{d}]$.

Clearly, $\diam(\Lip^{\mathrm{d}}_1(X)) \leq \mathrm{d}$.


With this metric, the mapping $x \mapsto f_{x}(y) = d(x,y) $ becomes an isometry: We have

$$
	d(f_{x}, f_{z}) = \sup\{ | d(x,y) - d(z,y)| \colon y \in X \}.
$$

By the reverse triangle inequality, this is always $\leq d(x,z)$. On the other hand, setting $y=z$ yields $d(f_x,f_z) \geq d(x,z)$. This embedding of $X$ into $\Lip^{\mathrm{d}}_1(X)$ is called the **Kuratowski embedding**.

We use this fact as follows: If $X^* = X \sqcup \{x^*\}$ and $d^*$ is an extension of $d_X$, then $f_{x^*}$ is an element of $\Lip^{\mathrm{d}}_1(X)$, and as above, for any $x \in X$

$$
	d(f_{x^*}, f_x) = d^*(x^*,x).
$$
 
Hence $\Lip^{\mathrm{d}}_1(X)$ has an extension property of the kind we are looking for. 

> *Iterative construction*: Let $X_0$ be any non-empty Polish space with finite diameter $\mathrm{d} > 0$. Given $X_n$, let $\mathrm{d}(n) = \diam(X_n)$ and set $X_{n+1} = \Lip^{2\mathrm{d}(n)}_1(X_n)$. Finally, put $X_\infty = \bigcup_n X_n$. Note that $X_\infty$ inherits a well-defined metric $d$ from the $X_n$, which embed isometrically into it.

We wan to verify that $X_\infty$ has the extension property needed to be Urysohn universal. Let $F$ be a finite subset of $X_\infty$. There exists $N$ such that $F \subset X_N$. Suppose $F^* = F \sqcup \{x^*\}$ and $d^*$ is an extension of $d$ to $F^*$. Let $\mathrm{d}^* = \diam(F^*)$. Note that $\diam(X_n) = 2^n \mathrm{d}$. Choose $M$ so that $M \geq N$ and $\diam(X_M) \geq \mathrm{d}^*$. The next lemma ensures that we can find $f \in X_{M+1}$ such that $f(x) = d^*(x^*,x)$ for all $x \in F$. 


```{prf:lemma} McShane-Whitney
Let $X$ be a metric space with $\diam(X) \leq \mathrm d$, $A \subseteq X$, and $f \in \Lip^{\mathrm{d}}_1(A)$, then $f$ can be extended to a $1$-Lipschitz function $f^*$ on all of $X$ such that

$$
	f^*|_A = f \quad \text{ and } \quad f^* \in \Lip^{2\mathrm{d}}_1(X).
$$
```

```{prf:proof}
For each $a \in A$ define $f_a: X \to \Real$ as

$$
	f_a(x) = f(a) + d(a,x).
$$

Then $f_a$ is $1$-Lipschitz, by the reverse triangle inequality. Let

$$
	f^*(x) = \inf \{f_a(x) \colon a \in A\}. 
$$

Then $f^*(a) = f(a)$ for all $a \in A$. Let $x,y \in X$ and $\eps > 0$. Wlog assume $f^*(y) \geq f^*(x)$. Pick $a \in A$ so that $f_a(x) \leq f^*(x)   + \eps$. Then 
\begin{align*}
	|f^*(x) - f^*(y)| = f^*(y) - f^*(x) & \leq f^*(y) - f_a(x) + \eps \\
		& \leq f_a(y) - f_a(x) + \eps \leq d(x,y) + \eps.
\end{align*}
Since $\eps > 0$ was arbitrary, we have $|f^*(x) - f^*(y)| \leq d(x,y)$. 

Finally, we have $f(a) \leq f_a(x) \leq f(a) + \mathrm{d}$ and thus $0 \leq f^*(x) \leq f_a(x) \leq 2\mathrm{d}$.
```

(ury-finishing-construction)=
## Finishing the construction

The set $X_\infty$ we constructed has two deficiencies with respect to our goal of constructing a Urysohn universal space: $X_\infty$ is not necessarily separable, and $X_\infty$ is not necessarily complete.

To make $X_\infty$ separable, we observe that if $X$ is compact, then the set $\Lip^{\mathrm{d}}_1(X)$ is closed in $\mathcal{C}(X)$ (the set of all real-valued continuous functions on $X$), bounded, and equicontinuous. By the **Arzelà-Ascoli Theorem**, $\Lip^{\mathrm{d}}_1(X)$ is compact. 
Every compact metric space is separable: For every $\eps > 0$, there exists a finite covering of the space with sets of $\diam < \eps$. Letting $\eps$ traverse all positive rationals and picking a point from each set in an $\eps$-covering yields a countable dense subset. Hence if we start with $X_0$ compact, each $X_n$ will be compact, too. A countable union of separable spaces is separable, thus $X_\infty$ is separable.

To obtain a complete space, we can pass from $X_\infty$ to its *completion* $\Cl{X_\infty}$. First note that if a metric space $X$ is separable, so is its completion $\Cl{X}$. However, we also have to ensure that $\Cl{X_\infty}$ retains the universality property of $X_\infty$.

```{prf:lemma}
If a complete metric space $(Y,d)$ admits a dense Urysohn universal subspace $\mathcal{U}$, then $Y$ is Urysohn universal.
```

```{prf:proof}
We follow {cite}`Gromov:1999a`. Let $F = \{x_1, \dots, x_n\} \subset Y$ and assume $F^* = F \sqcup \{x^*\}$ is an extension with metric $d^*$.

We first note that $Y$ is **approximately universal**. This means that for any $\eps > 0$, there exists a point $y^* \in Y$ such that 
\begin{equation*} \tag{$*$}
	|d(y*,x) - d^*(x^*,x)| < \eps \quad \text{ for all $x \in F$}.
\end{equation*}
This can be seen as follows. Since $\mathcal{U}$ is dense in $Y$, we can find a finite set $F_\eps = \{z_1, \dots, z_n\} \subset \mathcal{U}$ such that 

$$
	d(x_i, z_i) < \eps \quad \text{ for $1 \leq i \leq n$}.
$$

To keep the proof technically simple, wlog we assume $\eps$ is much smaller than the individual distances between the $x_i$. Consider the extension $F^*_\eps = F_\eps \sqcup \{x^*\}$ with metric

$$
	e^*(x^*, z_i) = d^*(x^*,x_i) + d(x_i,z_i).
$$

Since $\mathcal{U}$ has the finite extension property, we can find $y^* \in \mathcal{U}$ such that

$$
	d(y^*,z_i) = e^*(x^*,z_i) 
$$

Hence 
\begin{align*}
	|d(y^*,x_i) - d^*(x^*,x_i)| & = | e^*(x^*,z_i) - d^*(x^*,x_i)|  \\
	 	& = | d^*(x^*,x_i) + d(x_i,z_i) - d^*(x^*,x_i) | <  \eps.
\end{align*}

We use this approximate universality to construct a Cauchy sequence $(y_k)$ in $Y$ of 'approximate' extension points that satisfy $(*)$ for smaller and smaller $\eps$. 

Let $0 < \delta = \max \{d^*(x^*,x_i) \colon 1 \leq i \leq n \}$. 
The formal requirements for the sequence $(y_i)$ are as follows.

1. $|d(y_k,x_i) - d^*(x^*,x_i)| \leq 2^{-k} \delta$.
2. $d(y_{k+1},y_k) \leq 2^{-k}\delta$.

The sequence necessarily converges in $Y$ and the limit point must be a true extension point, due to (1.)

Suppose we have already constructed $y_1, \dots, y_k$ satisfying (1.), (2.). Add an (abstract) point $y^*_{k+1}$ to $F_k = F \cup \{y_1, \dots, y_k\}$. Let $F^*_{k+1} = F_k \sqcup \{y^*_{k+1}\}$. 

We want to use approximate universality on $F^*_{k+1}$. To this end we have to define a metric $e^*$ on $F^*_{k+1}$ that has the following properties

\begin{align*}
	(i) 	\qquad	& e^*|_{F_k} = d|_{F_k} \\
	(ii)  	\qquad & e^*(y^*_{k+1},x_i) = d^*(x^*,x_i) \quad (1 \leq i \leq n) \\
	(iii)	\qquad 	& e^*(y^*_{k+1}, y_k) = 2^{-k-1}\delta 
\end{align*}

Indeed such a metric exists: The condition $(i)$ already defines a metric on the set $F_k$. The conditions $(i)$-$(iii)$ also define a metric on $F \cup \{y_k,y^*_{k+1}\}$ -- the only thing to check for this is the triangle inequality for $y_k, y^*_{k+1}$:

$$
	|e^*(x_i,y_k) - e^*(y^*_{k+1},x_i)| = |d(x_i,y_k) - d^*(x^*,x_i) | \leq 2^{-k}\delta = e^*(y_k, y^*_{k+1}),
$$

by (1.). These metrics agree on the set

$$
	F_k \cap (F \cup \{y_k,y^*_{k+1}\}) = F \cup \{y_k\}.
$$

Therefore, we can "merge" them to a metric on all of $F^*_{k+1}$ by letting

$$
	e^*(y^*_{k+1}, y_j) = \inf \{e^*(y^*_{k+1}, z) + e^*(z,y_j) \colon z \in \{y_1, \dots, y_{k-1}\} \}.	
$$

Now choose $\eps < 2^{-k-1}\delta$ and apply approximate universality to $F^*_{k+1}$. This yields a point $y_{k+1} \in Y$ such that

$$
	|d(y_{k+1}, z)  - e^*(y^*_{k+1}, z) | < 2^{-k-1}\delta
$$

for all $z \in F_k$. By definition of $e^*$, we have

$$
	|d(y_{k+1}, x_i)  - d^*(y^*_{k+1}, z) | < 2^{-k-1}\delta 
$$

for $1 \leq i \leq n$, and $(iii)$ yields

$$
	d(y_{k+1}, y_k) < e^*(y^*_{k+1},y_k) + \eps \leq 2^{-k-1}\delta + 2^{-k-1}\delta = 2^{-k}\delta
$$

as required. 
```