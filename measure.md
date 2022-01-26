# Measure and Baire Category
```{math}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\Pow}{\mathcal{P}}
\newcommand{\Co}[1]{\neg \,#1}
\newcommand{\Op}[1]{\operatorname{#1}}

```

At the end of the previous section, we saw that Borel sets are well-behaved in the sense that they possess the **perfect subset property**. Two other important regularity properties are **measurability** and the **Baire property**, which we will introduce in this section.


## Filters and Ideals

The most common measure of size is, of course, cardinality. In the presence of uncountable sets (like in a perfect Polish space), the usual division is between countable and uncountable sets. The smallness of the countable sets is reflected, in particular, by two properties: A subset of a countable set is countable, and countable unions of countable set are countable. These characteristics are shared with other notions of smallness, two of which we will encounter in this lecture.

```{prf:definition}
:label: def-ideal
A non-empty family $\mathcal{I} \subseteq \Pow(X)$ of subsets of a given set $X$ is an **ideal** if 
\begin{align*}
(\Op{I1}) & \qquad A \in \mathcal{I} \text{ and } B \subseteq A \text{ implies } B \in \mathcal{I},\\
(\Op{I2}) & \qquad A, B \in \mathcal{I}  \text{ implies } A \cup B \in\mathcal{I}.
\end{align*}
```

If we have closure even under *countable unions*, we speak of a **$\sigma$-ideal**. For example, while the countable sets in $\Real$ form a $\sigma$-ideal, the finite subsets only form an ideal. 

Another example of ideals are the so-called **principal ideals**. These are ideals of the form

$$
	\langle Z \rangle = \{ A \colon A \subseteq Z\}
$$

for a fixed $Z \subseteq X$.


The **dual notion** to an ideal is that of a **filter**. It reflects that the sets in a filter share some **largeness property**.

```{prf:definition}
:label: def-filter
A non-empty family $\mathcal{F} \subseteq \Pow(X)$ of subsets of a given set $X$ is a **filter** if 
\begin{align*}
(\Op{F1}) & \qquad A \in \mathcal{F} \text{ and } B \supseteq A \text{ implies } B \in \mathcal{F},\\
(\Op{F2}) & \qquad A, B \in \mathcal{F}  \text{ implies } A \cap B \in\mathcal{F}.
\end{align*}
```

Again, closure under countable intersections yields **$\sigma$-filters**. 

If $\mathcal{I}$ is a ($\sigma$-) ideal, then $\mathcal{F} = \{\Co{A} \colon A \in \mathcal{I}\}$ is a ($\sigma$-) filter. Hence the co-finite subsets of $\Real$ form a filter, and the co-countable subsets form a $\sigma$-filter.

Note that the complement of a ($\sigma$-) ideal (in $\Pow(X)$) is not necessarily a ($\sigma$-) filter. This is true, however, for a special class of ideals/filters.

```{prf:definition}
:label: def-ultrafilter
A non-empty family $\mathcal{I} \subseteq \Pow(X)$ is a **prime ideal** if it is an ideal for which

$$
    \text{for every $A \in X$, either $A\in \mathcal{I}$ or $\Co{A} \in \mathcal{I}$}.
$$

An **ultrafilter** is a filter whose complement in $\Pow(X)$ is a prime ideal.
```

In light of the small-/largeness motivation, prime ideals and ultrafilters provide a *complete* separation of $X$: Each set is either small or large.


## Measures

Coarsely speaking, a measure assigns a size to a set in a way that reflects our basic geometric intuition about sizes: The size of the union of disjoint objects is the sum of their sizes. The question whether this can be done in a consistent way for *all* subsets of a given space is of fundamental importance and has motivated many questions in set theory.

The formally, a measure $\mu$ on $X$ is a $[0,\infty]$-valued function defined on subsets of $X$ that satisfies

\begin{align*}
    (\Op{M1}) & \qquad \mu(\emptyset) = 0 \\
    (\Op{M2}) & \qquad \mu(\bigcup_n A_n) = \sum_n \mu(A_n), \\
              & \qquad \qquad \text{whenever the $A_n$ are pairwise disjoint.}
\end{align*}

The question is, of course, which subsets of $X$ can be assigned a measure. The condition (M2) suggests that this family is closed under countable unions. Furthermore, if $A \subseteq X$, then the equation $\mu(X) = \mu(A) + \mu(\Co{A})$ suggests that $\Co{A}$ should be measurable, too. In other words, the sets who are assigned a measure form a $\sigma$-algebra.

```{prf:definition}
:label: def-measure

A **measurable space** is a pair $(X, \mathcal{S})$, where $X$ is a set and $\mathcal{S}$ is a $\sigma$-algebra on $X$. A **measure** on a measurable space $(X, \mathcal{S})$ is a function $\mu: \mathcal{S} \to [0,\infty]$ that satisfies (M1) and (M2) for any pairwise disjoint family $\{A_n\}$ in $\mathcal{S}$. If $\mu$ is a measure on $(X, \mathcal{S})$, then the triple $(X,\mathcal{S}, \mu)$ is called a **measure space**.
```

If we want the measure $\mu$ to reflect also some other basic intuition about geometric sizes, this often puts restrictions on the $\sigma$-algebra of measurable sets. For example, in $\Real$ the measure of an interval should be its *length*. We will see later that, if we assume the Axiom of Choice, it is impossible to assign every subset of $\Real$ a measure, so that (M1) and (M2) are satisfied, and the measure of an interval is its length. 

To have some control over what the $\sigma$-algebra of measurable sets should be, one can construct a measure more carefully, start with a measure on basic objects such as intervals or balls, and then extend it to larger classes of sets by approximation.

An essential component in this extension process is the concept of an \emph{outer measure}.

```{prf:definition}
:label: def-outer-measure

An **outer measure** on a set $X$ is a function $\mu^*: \Pow(X) \to [0,\infty]$ such that 
\begin{align*}
    (\Op{O1}) & \qquad  \mu^*(\emptyset) = 0,\\
    (\Op{O2}) & \qquad  A \subseteq B \text{ implies } \mu^*(A) \leq \mu^*(B), \\
    (\Op{O3}) & \qquad  \mu^*(\bigcup_n A_n) \leq \sum_n \mu^*(A_n), \\
         & \qquad  \qquad \text{for any countable family  $\{A_n\}$ in $X$}.
\end{align*}
```

An outer measure hence weakens the conditions of **additivity** (M2) to **subadditivity** (O3). This makes it possible to have non-trivial outer measures that are defined on *all* subsets of $X$.

The usefulness of outer measures lies in the fact that they can always be restricted to subset of $\Pow(X)$ on which they behave as measures.

```{prf:definition}
:label: def-measurable

Let $\mu^*$ be an outer measure on $X$. A set $A \subseteq X$ is **$\mu^*$-measurable** if

$$
\mu^*(B) = \mu^*(B \cap A) + \mu^*(B \setminus A) \quad \text{ for all $B \subseteq X$}.
$$ 
```

The definition singles out those sets that split all other sets correctly, with regard to measure.

```{prf:proposition}
:label: prop-measurable-sets

The class of $\mu^*$-measurable sets forms a $\sigma$-algebra $\mathcal{M}$, and the restriction of $\mu^*$ to $\mathcal{M}$ is a measure.
```

For a proof see for instance {cite}`Halmos:1950a`.

The size of the $\sigma$-algebra of measurable sets depends, of course, on the outer measure $\mu^*$. If $\mu^*$ is behaving rather pathetically, we cannot expect $\mathcal{M}$ to contain many sets.


## Lebesgue measure

A standard way to obtain `nice' outer measures is to start with a well-behaved function defined on a certain class of sets, and then approximate. The paradigm for this approach is the construction of **Lebesgue measure** on $\Real$. 

```{prf:definition}
:label: def-Lebesgue
The **Lebesgue outer measure** $\lambda^*$ of a set $A \subseteq \Real$ is defined as

$$
\lambda^*(A) = \inf \left \{ \sum_n |b_n - a_n| \colon A \subseteq \bigcup_n (a_n,b_n) \right \}. 
$$
```

```{admonition} Exercise
:class: tip
Show that $\lambda^*$ indeed defines an outer measure.
```

We call the $\lambda^*$-measurable sets **Lebesgue measurable**. One can verify that every open interval is Lebesgue measurable. It follows from Proposition \ref{prop-measurable-sets} that every Borel set is Lebesgue measurable. 

The construction of Lebesgue measure can be generalized and extended to other metric spaces, for example through the concept of **Hausdorff measures**. 

All these measures are **Borel measures**, in the sense that the Borel measures are measurable. However, there measurable sets that are not Borel sets. The reason for this lies in the presence of **nullsets**, which are measure theoretically "easy" (since they do not contribute any measure at all), but can be topologically quite complicated.


## Nullsets

Let $\mu^*$ be an outer measure on $X$. If $\mu^*(A) = 0$, then $A$ is called a **$\mu^*$-nullset**.

```{prf:proposition} 
:label:prop-nullsets-measurable
Any $\mu^*$-nullset is $\mu^*$-measurable.
```

```{prf:proof}
Suppose $\mu^*(A)=0$. Let $B \subseteq X$. Then, since $\mu^*$ is subadditive and monotone,
\[
    \mu^*(B) \leq \mu^*(B \cap A) + \mu^*(B \cap \Co{A}) = \mu^*(B \cap \Co{A}) \leq \mu^*(B),
\]
and therefore $\mu^*(B) = \mu^*(B \cap A) + \mu^*(B \cap \Co{A})$.
```

The next result confirms the intuition that nullsets are a notion of smallness.

```{prf:proposition} 
:label:prop-null-sigmaideal

The $\mu^*$-nullsets form a $\sigma$-ideal.
```

```{prf:proof}
(I1) follows directly from monotonicity (O2). Countable additivity follows immediately from subadditivity (O3).
```

In case of Lebesgue measure, we can use Proposition {prf:ref}`prop-nullsets-measurable` to further describe the Lebesgue measurable subsets of $\Real$.

```{prf:proposition}
A set $A \subseteq \Real$ is Lebesgue measurable if and only if it is the difference of a $\bPi^0_2$ set and a Lebesgue nullset.
```

```{prf:proof}
We first assume $\lambda^*(A) < \infty$.  Let $G_n \subseteq \Real$ be an open set such that $G_n \supseteq A$ and  $\lambda^*(G_n) \leq \lambda^*(A) + 1/n$. The existence of such a $G_n$ follows from the definition of $\lambda^*$, and the fact that every open set is the disjoint union of open intervals.  Then $G = \bigcap_n G_n$ is $\bPi^0_2$, $A \subseteq G$, and for all $n$,

$$
    \lambda^*(A) \leq \lambda^*(G) \leq \lambda^*(A) + 1/n  
$$

hence $\lambda^*(A) = \lambda^*(G)$. Hence for $N = G \setminus A$, since $A$ is measurable,

$$
    \lambda^*(N) = \lambda^*(G) - \lambda^*(A)  = 0 \quad \text{ and } \quad A = G \setminus N.
$$

If $\lambda^*(A) = \infty$, we set $A_m = A \cap [m,m+1)$ for $m \in \Integer$. By monotonicity, each $\lambda^*(A_m)$ is finite. For each $m \in \Integer$, $n \in \Nat$, pick $G^{(m)}_n$ open such that $\lambda^*(G^{(m)}_n) \leq \lambda^*(A) + 1/2^{n+2|m|+1}$. Then, with

$$
    \bigcap_{n \in \Nat} \bigcup_{m \in \Integer} G^{(m)}_n,
$$

$N = G\setminus A$ is the desired set.

For the other direction, note that the measurable sets form a $\sigma$-algebra which contains both the Borel sets and the nullsets. Hence any set that is the difference of a Borel set and a nullset is measurable, too.
```

```{admonition} Exercise
:class: tip

Show that each Lebesgue measurable set can be written as a disjoint union of a $\bSigma^0_2$ set and a nullset. 
```

Hence if a set is measurable, it differs from a (rather simple) Borel set only by a nullset. 
 
We also obtain the following characterization of the $\sigma$-algebra of Lebesgue measurable sets.

\begin{prop}
	The $\sigma$-algebra of Lebesgue measurable sets in $\Real$ is the smallest $\sigma$-algebra containing the open sets and the nullsets.
\end{prop}

As mentioned before, there are Lebesgue measurable sets that are not Borel sets. We will eventually encounter such sets. The question which sets exactly are Lebesgue measurable was one of the major questions that drove the development of descriptive set theory, just like the question which uncountable sets have perfect subsets.
 




