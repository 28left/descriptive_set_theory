# Large Cardinals
```{math}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\Integer}{\mathbb{Z}}
\newcommand{\Rat}{\mathbb{Q}}
\newcommand{\Baire}{\Nat^{\Nat}}
\newcommand{\Cyl}[1]{N_{#1}}
\newcommand{\Cant}{2^{\Nat}}
\newcommand{\Nstr}{\Nat^{<\Nat}}
\newcommand{\Tup}[1]{\langle #1 \rangle}
\newcommand{\Co}[1]{\neg \,#1}
\newcommand{\Op}[1]{\operatorname{#1}}
\newcommand{\Rest}[1]{|_{#1}}
\newcommand{\CH}{\mathsf{CH}}
\newcommand{\AC}{\mathsf{AC}}
\newcommand{\ZF}{\mathsf{ZF}}
\newcommand{\ZFC}{\mathsf{ZFC}}
\newcommand{\Norm}[1]{\parallel \! #1 \!\parallel}
\newcommand{\V}{\mathbf{V}}
\newcommand{\Ord}{\mathbf{Ord}}
\DeclareMathOperator{\W}{W}
\DeclareMathOperator{\WF}{WF}
\DeclareMathOperator{\WOrd}{WOrd}
```

## Inaccessible cardinals

The cardinality of $V_\alpha$ grows rather fast relative to $\alpha$. For example, 

$$
    |V_{\omega+\alpha}| = \beth_\alpha
$$    
where the **beth function** $\beth_\alpha$ is defined as
\begin{gather*}
    \beth_0 = \aleph_0 \\
    \beth_{\alpha+1} = 2^{\beth_\alpha} \\
    \beth_{\lambda} = \sup \{ \beth_\alpha \colon \alpha < \lambda\} \quad \text{ $\lambda$ limit}
\end{gather*}

This presents difficulties for the axiom of *Replacement* to hold in a $V_\alpha$, since we could define a function on a set of sufficiently high cardinality that maps to sets in $V_\alpha$ whose ranks are cofinal in $\alpha$ (and the image would not be an element of $V_\alpha$).

The existence of **inaccessible cardinals** ensures that the von-Neumann hierarchy is "long enough" for $\alpha$ to eventually "catch up" with the cardinality of $V_\alpha$.

Recall the enumeration of all cardinals by means of the **$\aleph$-sequence**:

\begin{equation*}
\aleph_0 = \omega, \quad \aleph_{\alpha+1} = \aleph_\alpha^+, \quad  \aleph_\lambda = \sup \{ \aleph_\xi \colon \xi<\lambda\} \; \text{ for limit } \lambda.
\end{equation*}

Here $\kappa^+$ is the least cardinal $> \kappa$. Some cardinals are limits of short sequences of cardinals -- for example, 
\begin{equation*}
    \aleph_\omega = \lim_n \aleph_n
\end{equation*}
is uncountable, but a limit of a countable sequence of smaller cardinals. Generally, cardinals who are a limit of a sequence of cardinals of length smaller than their cardinality are called **singular**. Non-singular cardinals are called **regular**:
\begin{equation*}
\Op{reg}(\kappa): \iff \forall \alpha < \kappa \;  \forall f \;( f: \alpha \to \kappa \;  \to \; \sup_{\xi < \alpha} f(\xi) < \kappa).
\end{equation*}

In other words, a regular cardinal $\kappa$ cannot be reached  by less then $\kappa$-many steps.  The first example of a regular cardinal is $\aleph_0$. 

```{admonition} Exercise
:class: tip

Show that all **successor cardinals**, i.e. cardinals of the form $\aleph_{\alpha+1}$ are regular. (Use the Axiom of Choice.)
```

On the other hand,
\begin{equation*}
\aleph_\omega,  \aleph_{\omega+\omega}, \aleph_{\aleph_{\omega}}, \aleph_{\aleph_{\aleph_\omega}}, \ldots
\end{equation*}
are singular and this suggests the question: 

> Are there regular cardinals of the form $\aleph_\lambda$ with $\lambda$ limit?

This is captured by the notion of **inaccessibility**.

```{prf:definition} Hausdorff 1908, Tarski, Zermelo 1930
:label: def-inaccessible

An uncountable cardinal $\kappa > \omega$ is 

- **weakly inaccessible** if 
\begin{align*}
    \Op{reg}(\kappa) \; &  \wedge \;  \exists \lambda (\Op{lim}(\lambda) \;  \wedge\;  \kappa = \aleph_\lambda)\\
                        (& \Leftrightarrow \Op{reg}(\kappa) \;  \wedge \;  \forall \alpha < \kappa \; \, \alpha^+ < \kappa)
\end{align*}

- **(strongly) inaccessible** if 
\begin{equation*}
    \Op{reg}(\kappa) \;  \wedge \;  \forall \alpha < \kappa \;\; 2^{\alpha} < \kappa
\end{equation*}
```

Under the **Generalized Continuum Hypothesis**,

> ($\mathsf{GCH}) \quad \forall \alpha \;\;  2^{\aleph_\alpha} = \aleph_{\alpha}^+$

weakly and strongly inaccessible cardinals coincide.

If $\kappa > \omega$ is inaccessible, then $\kappa = \aleph_\kappa$. Moreover, we have

```{prf:proposition}
:label: prop-cardinality-Vkappa

If $\kappa$ is strongly inaccessible, $|V_\kappa| = \kappa$. 
```

```{prf:proof}
It suffices to show that $|V_\alpha| < \kappa$ for all $\alpha < \kappa$. This follows by a straightforward induction, using the fact that $\kappa$ is strongly inaccessible. 
```

This in turn implies we can bound the cardinality of elements of $V_\kappa$.

```{prf:proposition}
:label: prop-inaccessible-cardinality

Suppose $\kappa$ is strongly inaccessible and $x\subset V_\kappa$. Then

$$
    x \in V_\kappa \; \Leftrightarrow \; |x| < \kappa.
$$
```

```{prf:proof}
($\Rightarrow$) $x \in V_\kappa$ implies $|x| < |V_\kappa|$. Apply {prf:ref}`prop-cardinality-Vkappa`.

($\Leftarrow$) Since $x \subseteq V_\kappa$, each $y \in x$ has rank $< \kappa$. Since $|x| < \kappa$, by regularity of $\kappa$, 

$$
    \Op{rank}(x) = \sup\{\Op{rank}(y)+1 \colon y \in x\} < \kappa
$$

 which implies $x \in V_\kappa$.
```

We have already seen that for limit $\alpha > \omega$, $V_\alpha$ is a model of all $\ZFC$ axioms except *Replacement*.

```{prf:theorem}
:label: thm-inaccessible-ZFC

If $\kappa$ is strongly inaccessible, then $V_\kappa \models \ZFC$.
```

```{prf:proof}
We verify that $V_\kappa$ satisfies the axiom of *Replacement*.
Suppose $x \in V_\kappa$ and $f:x \to V_\kappa$ is a function. Then $f[x] \subseteq V_\kappa$, and by {prf:ref}`prop-inaccessible-cardinality`, $|f[x]| \leq |x| < \kappa$. Applying the other direction of {prf:ref}`prop-inaccessible-cardinality` to $f[x]$, we obtain $f[x] \in V_\kappa$, as desired.
```

Suppose an inaccessible cardinal exists, and let $\kappa$ be the least inaccessible.  
It is not hard to verify that 

$$
V_\kappa \models \ZFC + \text{''there does not exist an inaccessible cardinal''}.
$$

(You verify that being a inaccessible cardinal is absolute for $V_\kappa$.) Therefore, the existence of an inaccessible cardinal is not provable from $\ZFC$. This fact also follows from Gödel's second incompleteness theorem.



## Measurability

We have seen that (assuming the Axiom of Choice) there subsets of $\Real$ that are not Lebesgue measurable. Inspecting the proof, we see that we only use the following properties of Lebesgue measure:

- $\sigma$-additivity,
- translation invariance ($\lambda(A) = \lambda(A+r)$),
- $\lambda(A) > 0$ for some $A$.

For spaces without an additive structures, instead of translation invariance, we can consider a **non-triviality condition**:

$$
m(\{x\})=0 \quad \text{ for all $x$}
$$

The **generalized measure problem** asks whether there exists a set $M$ together with a measure function
\begin{gather*}
m: \mathcal{P}(M) \to [0,\infty),
\end{gather*}
so that the following conditions are met:

- (**M1**) $\quad$ $m(M) =1$ 
- (**M2**) $\quad$ $\forall x \in M \; m(\{x\})=0$ 
- (**M3**) $\quad$ if $(A_i)_{i < \omega}$ is a countable sequence of disjoint sets $\subseteq M$, then 
\begin{equation*}
m\left(\bigcup_{i<\omega} A_i\right ) =  \sum_{i<\omega} m(A_i)
\end{equation*}

The structure of the set $M$ does not play any role here, so we can replace it by a cardinal $\kappa$ outright. One can also consider strengthening $\sigma$-additivity to **$\kappa$-additivity**:

> If $\gamma < \kappa$ and  $(A_\xi)_{\xi< \lambda}$ is a sequence of disjoint subsets of $\kappa$, then
\begin{equation*}
m(\bigcup_{\xi<\gamma} A_\xi) =  \sum_{\xi<\gamma} m(A_\xi).
\end{equation*}

A transfinite sum $\sum_{\xi<\gamma}$ is given as the supremum of all sums over finite subsequences:

$$
\sum_{\xi<\gamma} m(A_\xi) = \sup \left \{ \sum_{\xi \in F} m(A_\xi) \colon F \subseteq \gamma \text{ finite}\right \}.
$$

Hence, $\omega_1$-additive is the same as $\sigma$-additive.

```{prf:theorem} Banach
:label: thm-kappa-additivity

If $\kappa$ is the least cardinal for which a measure satisfying (M1)-(M3) exists, then any such measure on $\kappa$ is already $\kappa$-additive.
```

```{prf:proof}
Suppose $m$ is a measure on $\kappa$ that is not $\kappa$-additive. 
Then, for some $\gamma < \kappa$, there exists a sequence $(A_\xi)_{ \xi< \gamma}$ of disjoint subsets of $\kappa$ so that 

$$
m(\bigcup_{\xi<\gamma} A_\xi) \ne  \sum_{\xi<\gamma} m(A_\xi).
$$ 

Since a measure is always $\sigma$-additive, $\gamma > \omega$ has to hold, and there can be at most countably many $A_\xi$ with $m(A_\xi)>0$.

We can drop those $A_\xi$, and by the $\sigma$-additivity of $m$ for the remaining $\xi$ it has to hold that $m(A_\xi)=0$ while $m \left(\bigcup_{\xi<\gamma} A_\xi \right) = r >0$.

By putting 
\begin{equation*}
\overline{m}(X) = \frac{m(\bigcup_{\xi \in X} A_\xi)}{r}
\end{equation*}
we obtain a measure on $\gamma < \kappa$, contradicting the minimality of $\kappa$.
```


### Measurable cardinals

If $m$ is a measure on $\kappa$, the **associated ideal** 

$$
\mathcal{I}_m = \{x\subseteq \kappa \colon m(x) = 0 \}
$$ 

is a $\sigma$-ideal, or, complementing the notion of $\omega_1$-additivity, a **$\omega_1$-complete ideal**. 

```{admonition} Exercise
:class: tip

Show that $\mathcal{I}_m$ is not principal.
```

The corresponding filter 

$$
\mathcal{F}_m = \{x\subseteq \kappa \colon m(x) = 1\}
$$ 

is then $\omega_1$-complete, too. 

A measure $m$ is **two-valued** if it only assumes the values $0$ and $1$. In this case the corresponding filter $\mathcal{F}_m$ is an **ultrafilter** (and $\mathcal{I}_m$ is a **prime ideal**).

Conversely, if $U$ is $\omega_1$-complete, non-principal ultrafilter on $\kappa$, we can define a two-valued measure $m: \mathcal{P}(\kappa) \to \{0,1\}$ on $\kappa$ by letting

$$
m(x) = 
  \begin{cases}
   1  & \text{if } x \in U, \\
   0   & \text{otherwise}.
\end{cases}
$$

```{prf:definition}
:label: def-measurable-cardinal
Let $\kappa$ be an uncountable cardinal. 

- $\kappa$ is **real-valued measurable** if there exists a $\kappa$-additive measure on $\kappa$.

- $\kappa$ is **measurable** if there exists a $\kappa$-additive, two-valued measure on $\kappa$, or, equivalently, if there exists a $\kappa$-complete, non-principal ultrafilter on $\kappa$.
```

In the following, we will see that measurability implies inaccessibility. 

```{prf:lemma} 
:label: lem-cardinality-kappa-ultrafilter

If $U$ is a $\kappa$-complete, non-principal ultrafilter on $\kappa$, then every $X \in U$ has cardinality $\kappa$.
```

```{prf:proof}
Since $U$ is non-principal, no *singleton* set $\{x\}$ can be in $U$ (for this would imply $\kappa\setminus \{x\} \notin U$ and therefore no subset of it would be in $U$ either, contradicting the non-principality of $U$).

If $X \in U$ and $|X| < \kappa$, then $X$ is the union of $< \kappa$ many singletons. Since $\neg U$ is a $\kappa$-complete prime ideal, this implies $X \in \neg U$, contradiction.
```

```{prf:proposition}
:label: prop-measurable-regular

If $\kappa$ is measurable, then it is regular.
```

```{prf:proof}
If $\kappa$ were singular, it would be the union of $<\kappa$-many sets of cardinality $<\kappa$. Applying {prf:ref}`lem-cardinality-kappa-ultrafilter` leads to a contradiction.
```

```{prf:theorem}
:label: thm-measurable-inaccessible

A measurable cardinal is (strongly) inaccessible. 
```

```{prf:proof}
By {prf:ref}`prop-measurable-regular`, any measurable cardinal is regular. Assume for a contradiction there exists $\gamma < \kappa$ with $2^\gamma > \kappa$. As $2^\gamma > \kappa$, there exists a set $S$ of functions $f: \gamma \to \{0,1\}$ with $|S| = \kappa$. Let $U$ be a $\kappa$-complete, non-principal ultrafilter on $S$. 

For $\alpha < \gamma, i \in \{0,1\}$, let

$$
    X_{\alpha,i} = \{ f \in S \colon f(\alpha) = i\}
$$

and let $g(\alpha) = i$ if and only if $X_{\alpha,i} \in U$. Since $U$ is an ultrafilter, $g$ is well-defined on $\gamma$. 

Since $\gamma < \kappa$ and $U$ is $\kappa$-complete, 

$$
    X = \bigcap_{\alpha < \gamma} X_{\alpha, g(\alpha)} 
$$ 

is in $U$. But $|X| \leq 1$, since the only function possibly in $X$ is $g$. This contradicts {prf:ref}`lem-cardinality-kappa-ultrafilter`.
```

```{admonition} Exercise
:class: tip

Show that every real-valued measurable cardinal is weakly inaccessible.
```


```{prf:proposition}
:label: prop-measurable-vs-real-valued

If $\kappa$ is real-valued measurable, then $\kappa$ is measurable or $\kappa \le 2^{\aleph_0}$.
```

Thus, if $\kappa$ is real-valued measurable but not measurable, then the continuum $2^{\aleph_0}$ has to be very large.



## Partition properties

Another concept of largeness is related to the existence of large **homogeneous sets** for partitions. 

For given set $S$ and $n \in \Nat$, let
\begin{equation*}
	[S]^n := \{ X \subseteq S \colon \: |X| = n \} 
\end{equation*}
be the set of all $n$-element subsets of $S$. For cardinals $\kappa, \lambda$, we define 
\begin{equation*}
	\kappa \to (\lambda)^n_k 
\end{equation*}
to mean that any partition $F: [S]^n \to \{1, \dots, k\}$ mit $|S| = \kappa$ has an **$F$-homogeneous subset**  of cardinality $\lambda$, that is, a set $H$, $|H| = \lambda$, such that
\begin{equation*}
	F|_{[H]^n} \equiv \text{ constant}. 
\end{equation*}

**Ramsey's theorem** (1929/39) says that for any $n,k \in \Nat$, 
\begin{equation*}
	\aleph_0 \to (\aleph_0)^n_k. 
\end{equation*}

Do there exist uncountable cardinals with similar properties?

A cardinal $\kappa$ is **weakly compact** if it is uncountable and $\kappa \to (\kappa)^2_2$ holds. 

```{admonition} Exercise
:class: tip

Show that for any cardinal $\kappa$, $2^\kappa \nrightarrow (\kappa^+)^2_2$, and use this to infer that any weakly compact cardinal is inaccessible.

(Thus the existence of weakly compact cardinals cannot be established in $\ZFC$.)
```

Measurable cardinals have even stronger homogeneity properties. Let $[S]^{<\omega}$ be the set of all finite subsets of $S$. If $F: [S]^{<\omega} \to I$ is a partition, then $H \subseteq S$ is **$F$-homogenenous** if
\begin{equation*}
	F|_{[H]^n} \equiv \text{ constant} 
\end{equation*}
for all $n \in \Nat$.

```{prf:theorem} Rowbottom
:label: thm-measurable-Ramsey

Let $\kappa$ be a measurable cardinal and let $F: [\kappa]^{<\omega} \to \lambda$ a partition of $[\kappa]^{<\omega}$ into $\lambda < \kappa$ pieces. Then there exists an $F$-homogeneous set $H \subseteq \kappa$ with $|H| = \kappa$.
```

In general, any cardinal that satisfies the statement of the theorem is called **Ramsey**.

To prove {prf:ref}`thm-measurable-Ramsey`, we introduce **normal ultrafilters**.

```{prf:definition}
:label: def-normal-filter

Given a sequence of sets $(A_\xi)_{\xi < \gamma}$, the **diagonal intersection** is given as

$$
    \Delta_{\xi < \gamma} A_\xi = \{ \alpha < \gamma \colon  \alpha \in \bigcap_{\xi < \alpha} A_\xi \}.
$$

A filter $F$ on a cardinal $\kappa$ is **normal** if for any $\kappa$-sequence $(A_\xi)_{\xi < \kappa}$, $A_\xi \in F$, the diagonal intersection $\Delta_{\xi < \kappa} A_\xi$ is in $F$.
```

Let us assume as a convention that a filter on a cardinal $\kappa$ always contains the end-segments $\{\xi \colon \alpha \leq \xi < \kappa\}$.

```{admonition} Exercise
:class: tip

Show that a normal filter on $\kappa$ is $\kappa$-complete. 
```

```{admonition} Exercise
:class: tip

Show that if there is a normal filter over $\kappa$, then $\kappa$ is uncountable and regular.
```

```{admonition} Exercise
:class: tip

Show that if $\kappa$ is measurable, then there is a normal ultrafilter on $\kappa$.
```

```{prf:proof} 
(Proof of {prf:ref}`thm-measurable-Ramsey`) 

Let $U$ be a normal filter over $\kappa$.
We show that for every $n$, for any $g: [\kappa]^n \to \gamma$ with $\gamma < \kappa$, there is a set $H_n \in U$ such that $g_n \Rest{[H_n]^n} \equiv \text{const}$. The intersection of the $H_n$ is again in $U$ and satisfies the statement of the the theorem.

We proceed by induction. The case $n=1$ follows from the $\kappa$-completeness of $U$. Now assume $g:[\kappa]^{n+1} \to \gamma$, with $\gamma < \kappa$.

For each $S \in [\kappa]^n$, define $g_s : \kappa \to \gamma$ by 

$$
    g_S(\alpha) = \begin{cases}
        g(S \cup \{\alpha\}) & \text{ if } \max S < \alpha \\
        0 & \text{otherwise}
    \end{cases}
$$

By $\kappa$-completeness of $U$, $g_S$ is constant on a set $Y_S \in U$, say

$$
    g_S\Rest{Y_S} \equiv \delta_S < \gamma.
$$

We now define a function $h: [\kappa]^n \to \gamma$ 
by letting

$$
    h(S) = \delta_S.
$$

By induction hypothesis, $h$ is constant on a set $Z \subseteq \kappa$
in $U$ (and hence of size $\kappa$), say $h\Rest{[Z]^n} \equiv \delta < \kappa$.

For each $\alpha < \kappa$, let

$$
    Y_\alpha = \bigcap \{Y_S \colon \max S \leq \alpha\}
$$

By $\kappa$-completeness, $Y_\alpha \in U$, and by normality

$$
    H = Z \cap \Delta_{\alpha < \kappa} Y_\alpha \in U
$$

By {prf:ref}`lem-cardinality-kappa-ultrafilter`, $H$ has cardinality $\kappa$.

We claim that $g$ is constant on $[H]^{n+1}$: Let $T \in [H]^{n+1}$. Write $T$ as $S \cup \{\alpha\}$ with $\max S < \alpha$. Then 

\begin{align*}
    \alpha \in H & \Rightarrow  & \alpha \in \Delta_{\gamma < \kappa} Y_\gamma \\
                 & \Rightarrow  & \alpha \in \bigcap_{\beta < \alpha} Y_\beta \\
                 & \Rightarrow  & \alpha \in Y_{\max S} \\
                 & \Rightarrow  & \alpha \in Y_S \\
                 & \Rightarrow  & g_S(\alpha) = \delta_S
\end{align*}

On the other hand, $S \subseteq H$ implies $S \subseteq Z$ and hence by definition of $Z$, $h(S) = \delta_S = \delta$, so $g(T) = g_S(\alpha) = \delta_S = \delta$.
```