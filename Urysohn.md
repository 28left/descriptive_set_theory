# Excursion: The Urysohn Space

```{math}
\newcommand{\N}{\mathbb{N}}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\CH}{\mathsf{CH}}
\newcommand{\eps}{\varepsilon}
\newcommand{\Cant}{2^{\Nat}}
\newcommand{\Baire}{\Nat^{\Nat}}
\newcommand{\Rest}[1]{\mid_{#1}}
\newcommand{\Ci}{\mathbb{T}}
\newcommand{\Str}[1][2]{{#1}^{<\Nat}}
\newcommand{\Sle}{\subset}
\newcommand{\Sleq}{\subseteq}
\newcommand{\Cyl}[1]{N_{#1}}
\newcommand{\Ury}{\mathbb{U}}

\DeclareMathOperator{\diam}{diam}
```

Recall that a mapping $f: X \to Y$ between two metric spaces $(X,d_X)$ and $(Y,d_Y)$ is an **isometry** if

$$
d_Y(f(x),f(y)) = d_X(x,y) \quad \text{ for all $x,y \in X$},
$$

that is, an isometry is a mapping that preserves distances. The function $f$ is also called an *isometric embedding* of $X$ into $Y$. $X$ and $Y$ are *isometric* if there exists a bijective isometry between them.

It is a remarkable fact that there exists a "universal" Polish space -- a complete, separable metric space that contains an isometric copy of any other Polish metric space.

```{prf:theorem}
There exists a Polish metric space $\Ury$ such that every Polish metric space isometrically embeds into $\Ury$.
```

A concrete example of such a space is $\mathcal{C}[0,1]$.


the set of all continuous real-valued functions on $[0,1]$ with the $\sup$-metric (see exercises). But this space is not quite what we have in mind. There exists another space with a stronger, more ``intrinsic'' universality property, \defemph{Urysohn space}.
It was constructed by \citet{urysohn:espace_1927}.

The construction features an \emph{amalgamation principle} that has surfaced in other areas like model theory or graph theory. It has recently attracted increased attention, which has also led to renewed interest in the Urysohn space.

  


\subsection*{Extensions of finite isometries and Urysohn universality}

We first sketch the basic idea for constructing the Urysohn space. Suppose $X$ is a Polish metric space. Let $D = \{x_1, x_2, \dots\}$ be a countable, dense subset. We first observe that it is sufficient to isometrically embed $D$ into $\Ury$.

\begin{lem}
	If $Y$ is Polish, then any isometric embedding $e$ of $D$ into $Y$ extends to an isometric embedding $e^*$ of $X$ into $Y$.
\end{lem}

\begin{proof}
	Given $z \in X$, let $(x_{i_n})$ be a sequence in $D$ converging to $z$. Since $(x_{i_n})$ converges, it is Cauchy. $e$ is an isometry, and thus $y_n := e(x_{i_n})$ is Cauchy, and since $Y$ is Polish, $(y_n)$ converges to some $y \in Y$. Put $e^*(z) = y$. To see that this mapping is well-defined, let $(x_{j_n})$ be another sequence with $x_{j_n} \to z$. Then $d(x_{i_n}, x_{j_n}) \to 0$, and hence $d(e(x_{i_n}),e(x_{j_n}) = d(y_n, e(x_{j_n}))\to 0$, implying $e(x_{j_n}) \to y$. Furthermore, suppose $w = \lim x_{k_n}$ is another point in $X$. Then (since a metric is a continuous mapping from $Y\times Y \to \Real$)
	\[
		d(e*(z), e^*(w)) = \lim d( e(x_{i_n}),  e(x_{k_n})) = \lim d(  x_{i_n}, x_{k_n}) = d(z,w).
	\]
	Thus $e^*$ is an isometry.
\end{proof}

In order to embed $D$, we can now exploit the \emph{inductive structure} of $\Nat$ and reduce the task to \emph{extending finite isometries}.

Suppose we have constructed an isometry $e$ between $F_N = \{x_1, \dots, x_N \} \subset D$ and $\Ury$. We would like to extend the isometry to include $x_{N+1}$. For this we have to find an element $y \in \Ury$ such that for all $i \leq N$
\[
	d_\Ury(y, e(x_i)) = d_X(x_{N+1}, x_i).
\]

This extension property gives rise to the following definition.

\begin{defn}
	A Polish space $(\Ury,d_\Ury)$ is \defemph{Urysohn universal} if for every finite subspace $F \subset \Ury$ and any extension $F^* = F \sqcup \{x^*\}$ with metric $d^*$ such that 
	\[
		d^*|_{X\times X} = d_\Ury,
	\]
	there exists a point $u \in \Ury$ such that 
	\[
		d_{\Ury}(u,x) = d^*(x^*,x) \quad \text{ for all $x \in F$}.
	\]
\end{defn}

One can show that any two Urysohn universal spaces are isometric. We will show here that this unique (up to isometry) space actually exists, the \defemph{Urysohn space} $\Ury$. 

The extension property also implies a strong intrinsic extension property for the Urysohn space itself.

\begin{prop}
	Let $\mathcal{U}$ be a separable and complete metric space that contains an isometric image of every separable metric space. Then $\mathcal{U}$ is Urysohn universal if and only if every isometry between finite subsets of $\mathcal{U}$ extends to an isometry of $\mathcal{U}$ onto itself.
\end{prop}



\subsection*{Constructing the Urysohn space -- a first approximation}

We first give a construction of a space that has the extension property, but is not Polish. After that we will take additional steps to turn it into a Polish space. 

% We also restrict ourselves to spaces $X$ whose diameter is bounded by $\mathrm{d} < \infty$ (i.e.\ $d(x,y) \leq \mathrm{d}$ for all $x,y \in X$), where the extension property only has to hold if $d^*(x^*,x) < \mathrm{d}$ for all $x \in F$. Call such space \emph{$U_{\mathrm{d}}$-universal}. 

% A $U_{\mathrm{d}}$-universal space can be constructed by a countable extension process. 

The crucial idea is to observe that if $X$ is a metric space and $x \in X$, then the mapping $f_{x}: X \to \Real^{\geq 0}$ given by
\[
	f_{x}(y) = d_X(x,y)
\] 
is \emph{$1$-Lipschitz}. Recall that a function $g$ between metric spaces $X$ and $Y$  is \defemph{$L$-Lipschitz}, $L > 0$ if for every $x,y \in X$,
\[
	d(g(x),g(y)) \leq L \, d(x,y).
\]
Let $\Lip_1(X)$ be the set of $1$-Lipschitz mappings from $X$ to $\Real$. We endow $\Lip_1(X)$ with the \emph{supremum} metric
\[
	d(f,g) = \sup \{|f(x) - g(x)| \colon x \in X \}.
\]
If $\diam(X) \leq \mathrm{d}$ and $f,g$ are $1$-Lipschitz, then $d(f,g)$ is indeed finite.
However, we will need that the resulting space is also bounded. Let  $\Lip^{\mathrm{d}}_1(X)$ be the space of all $1$-Lipschitz functions from $X$ to $[0,\mathrm{d}]$.
% If $\diam(X) \leq \mathrm{d}$ and $f,g$ are $1$-Lipschitz, then, for a fixed $x_0 \in X$
% \begin{align*}
% 	|f(x) - g(x)|  & \leq |f(x) - f(x_0) | + |f(x_0) - g(x_0)| + |g(x_0) - g(x)| \\
% 		& \leq 2L d_X(x,x_0) + |f(x_0) - g(x_0)| \leq 2L\mathrm{d} + |f(x_0) - g(x_0)|.
% \end{align*}
% The inequality holds for all $x$, hence $d(f,g)$ is finite. 
Clearly, $\diam(\Lip^{\mathrm{d}}_1(X)) \leq \mathrm{d}$.


With this metric, the mapping $x \mapsto f_{x}(y) = d(x,y) $ becomes an isometry: We have
\[
	d(f_{x}, f_{z}) = \sup\{ | d(x,y) - d(z,y)| \colon y \in X \}.
\] 
By the reverse triangle inequality, this is always $\leq d(x,z)$. On the other hand, setting $z = x$ yields $d(f_x,f_z) \geq d(x,z)$. This embedding of $X$ into $\Lip^{\mathrm{d}}_1(X)$ is called the \defemph{Kuratowski embedding}.

We use this fact as follows: If $X^* = X \sqcup \{x^*\}$ and $d^*$ is an extension of $d_X$, then $f_{x^*}$ is an element of $\Lip^{\mathrm{d}}_1(X)$, and as above, for any $x \in X$
\[
	d(f_{x^*}, f_x) = d^*(x^*,x).
\] 
Hence $\Lip^{\mathrm{d}}_1(X)$ has an extension property of the kind we are looking for. 

\emph{Iterative construction}: Let $X_0$ be any non-empty Polish space with finite diameter $\mathrm{d} > 0$. Given $X_n$, let $\mathrm{d}(n) = \diam(X_n)$ and set $X_{n+1} = \Lip^{2\mathrm{d}(n)}_1(X_n)$. Finally, put $X_\infty = \bigcup_n X_n$. Note that $X_\infty$ inherits a well-defined metric $d$ from the $X_n$, which embed isometrically into it.

We claim that $X_\infty$ has the extension property needed to be Urysohn universal. Let $F$ be a finite subset of $X_\infty$. There exists $N$ such that $F \subset X_N$. Suppose $F^* = F \sqcup \{x^*\}$ and $d^*$ is an extension of $d$ to $F^*$. Let $\mathrm{d}^* = \diam(F^*)$. Note that $\diam(X_n) = 2^n \mathrm{d}$. Choose $M$ so that $M \geq N$ and $\diam(X_M) \geq \mathrm{d}^*$. The next lemma ensures that we can find $f \in X_{M+1}$ such that $f(x) = d^*(x^*,x)$ for all $x \in F$. 


\begin{lem}[McShane-Whitney]
	Let $X$ be a metric space with $\diam(X) \leq \mathrm d$, $A \subseteq X$, and $f \in \Lip^{\mathrm{d}}_1(A)$, then $f$ can be extended to an $1$-Lipschitz function $f^*$ on all of $X$ such that
	\[
		f^*|_A = f \quad \text{ and } \quad f^* \in \Lip^{2\mathrm{d}}_1(X).
	\]
\end{lem}

\begin{proof}
	For each $a \in A$ define $f_a: X \to \Real$ as
	\[
		f_a(x) = f(a) + d(a,x).
	\]
 	Then $f_a$ is $1$-Lipschitz, by the reverse triangle inequality. Let
	\[
		f^*(x) = \inf \{f_a(x) \colon a \in A\}. 
	\]
	Then $f^*(a) = f(a)$ for all $a \in A$. Let $x,y \in X$ and $\eps > 0$. Wlog assume $f^*(y) \geq f^*(x)$. Pick $a \in A$ so that $f_a(x) \leq f^*(x)   + \eps$. Then 
	\begin{align*}
		|f^*(x) - f^*(y)| = f^*(y) - f^*(x) & \leq f^*(y) - f_a(x) + \eps \\
			& \leq f_a(y) - f_a(x) + \eps \leq Ld(x,y) + \eps.
	\end{align*}
	Since $\eps > 0$ was arbitrary, we have $|f^*(x) - f^*(y)| \leq L d(x,y)$. 
	
	Finally, we have $f(a) \leq f_a(x) \leq f(a) + \mathrm{d}$ and thus $0 \leq f^*(x) \leq f_a(x) \leq 2\mathrm{d}$.
\end{proof}



\subsection*{Mending the construction}

The set $X_\infty$ we constructed has two deficiencies with respect to our goal of constructing a Urysohn universal space: $X_\infty$ is not necessarily separable, and $X_\infty$ is not necessarily complete.

To make $X_\infty$ separable, we observe that if $X$ is compact, then the set $\Lip^{\mathrm{d}}_1(X)$ is closed in $\mathcal{C}(X)$ (the set of all real-valued continuous functions on $X$), bounded, and \emph{equicontinuous}. By the \emph{Arzelà-Ascoli Theorem}, $\Lip^{\mathrm{d}}_1(X)$ is compact. Every compact metric space is separable: For every $\eps > 0$, there exists a finite covering of the space with sets of $\diam < \eps$. Letting $\eps$ traverse all positive rationals and picking a point from each set in an $\eps$-covering yields a countable dense subset. Hence if we start with $X_0$ compact, each $X_n$ will be compact, too. A countable union of separable spaces is separable, thus $X_\infty$ is separable.

To obtain a complete space, we can pass from $X_\infty$ to its \emph{completion} $\Cl{X_\infty}$. First note that if a metric space $X$ is separable, so is its completion $\Cl{X}$. However, we also have to ensure that $\Cl{X_\infty}$ retains the universality property of $X_\infty$.

\begin{lem}
	If a complete metric space $(Y,d)$ admits a dense Urysohn universal subspace $\mathcal{U}$, then $Y$ is Urysohn universal.
\end{lem}

\begin{proof}
	We follow \citet{gromov:metric}. Let $F = \{x_1, \dots, x_n\} \subset Y$ and assume $F^* = F \sqcup \{x^*\}$ is an extension with metric $d^*$.

	We first note that $Y$ is \emph{aproximately universal}. This means that for any $\eps > 0$, there exists a point $y^* \in Y$ such that 
	\begin{equation} \tag{$*$}
		|d(y*,x) - d^*(x^*,x)| < \eps \quad \text{ for all $x \in F$}.
	\end{equation}
 	This can be seen as follows. Since $\mathcal{U}$ is dense in $Y$, we can find a finite set $F_\eps = \{z_1, \dots, z_n\} \subset \mathcal{U}$ such that 
\[
	d(x_i, z_i) < \eps \quad \text{ for $1 \leq i \leq n$}.
\]
To keep the proof technically simple, wlog we assume $\eps$ is much smaller than the individual distances between the $x_i$. Consider the extension $F^*_\eps = F_\eps \sqcup \{x^*\}$ with metric
\[
	e^*(x^*, z_i) = d^*(x^*,x_i) + d(x_i,z_i).
\] 
Since $\mathcal{U}$ has the finite extension property, we can find $y^* \in \mathcal{U}$ such that
\[
	d(y^*,z_i) = e^*(x^*,z_i) 
\]
Hence 
\begin{align*}
	|d(y^*,x_i) - d^*(x^*,x_i)| & = | e^*(x^*,z_i) - d^*(x^*,x_i)|  \\
	 	& = | d^*(x^*,x_i) + d(x_i,z_i) - d^*(x^*,x_i) | <  \eps.
\end{align*}

We use this approximate universality to construct a Cauchy sequence $(y_k)$ in $Y$ of `approximate' extension points that satisfy $(*)$ for smaller and smaller $\eps$. 

Let $0 < \delta = \max \{d^*(x^*,x_i) \colon 1 \leq i \leq n \}$. 
The formal requirements for the sequence $(y_i)$ are as follows.
\begin{enumerate}[(i)]

\item $|d(y_k,x_i) - d^*(x^*,x_i)| \leq 2^{-k} \delta$.

\item $d(x_{k+1},x_k) \leq 2^{-k}\delta$.

\end{enumerate}
The sequence necessarily converges in $Y$ and the limit point must be a true extension point, due to (i).

Suppose we have already constructed $y_1, \dots, y_k$ satisfying (i), (ii). Add an (abstract) point $y^*_{k+1}$ to $F_k = F \cup \{y_1, \dots, y_k\}$. Let $F^*_{k+1} = F_k \sqcup \{y^*_{k+1}\}$. 

We want to use approximate universality on $F^*_{k+1}$. To this end we have to define a metric $e^*$ on $F^*_{k+1}$ that has the following properties
\begin{align}
	\tag{$+$} 		& e^*|_{F_k} = d|_{F_k} \\
	\tag{$++$}  	& e^*(y^*_{k+1},x_i) = d^*(x^*,x_i) \quad (1 \leq i \leq n) \\
	\tag{$+++$}		& e^*(y^*_{k+1}, y_k) = 2^{-k-1}\delta 
\end{align}
Indeed such a metric exists: The condition $(+)$ already defines a metric on the set $F_k$. $(+)$-$(+++)$ also define a metric on $F \cup \{y_k,y^*_{k+1}\}$. The only thing left to check for this is the triangle inequality for $y_k, y^*_{k+1}$.
\[
	|e^*(x_i,y_k) - e^*(y^*_{k+1},x_i)| = |d(x_i,y_k) - d^*(x^*,x_i) | \leq 2^{-k}\delta = e^*(y_k, y^*_{k+1}),
\]  
by (i). These metrics agree on the set
\[
	F_k \cap (F \cup \{y_k,y^*_{k+1}\}) = F \cup \{y_k\}.
\]
Therefore, we can ``merge'' them to a metric on all of $F^*_{k+1}$ by letting
\[
	e^*(y^*_{k+1}, y_j) = \inf \{e^*(y^*_{k+1}, z) + e^*(z,y_j) \colon z \in \{y_1, \dots, y_{k-1}\} \}.	
\]

Now choose $\eps < 2^{-k-1}\delta$ and apply approximate universality to $F^*_{k+1}$. This yields a point $y_{k+1} \in Y$ such that
\[
	|d(y_{k+1}, z)  - e^*(y^*_{k+1}, z) | < 2^{-k-1}\delta
\] 
for all $z \in F_k$. By definition of $e^*$, we have
\[
	|d(y_{k+1}, x_i)  - d^*(y^*_{k+1}, z) | < 2^{-k-1}\delta 
\]
for $1 \leq i \leq n$, and $(+++)$ yields
\[
	d(y_{k+1}, y_k) < e^*(y^*_{k+1},y_k) + \eps \leq 2^{-k-1}\delta + 2^{-k-1}\delta = 2^{-k}\delta
\]
as required. 
\end{proof}
