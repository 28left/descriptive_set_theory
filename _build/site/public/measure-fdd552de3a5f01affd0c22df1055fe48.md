# Measure and Baire Category
```{math}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\Integer}{\mathbb{Z}}
\newcommand{\Rat}{\mathbb{Q}}
\newcommand{\Baire}{\Nat^{\Nat}}
\newcommand{\Pow}{\mathcal{P}}
\newcommand{\Co}[1]{\neg \,#1}
\newcommand{\Op}[1]{\operatorname{#1}}
\newcommand{\bPi}{\pmb{\Pi}}
\newcommand{\bSigma}{\pmb{\Sigma}}
\newcommand{\Cl}[1]{\overline{#1}}
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

> for every $A \in X$, either $A\in \mathcal{I}$ or $\Co{A} \in \mathcal{I}$ (but not both).

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

An essential component in this extension process is the concept of an **outer measure**.

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

This definition is justified rather by its consequences than by its intuitive appeal. Regarding the latter, suffice it to say here that outer measures may be rather far from being even *finitely* additive. The definition singles out those sets that split all other sets correctly, with regard to measure.

```{prf:proposition}
:label: prop-measurable-sets

The class of $\mu^*$-measurable sets forms a $\sigma$-algebra $\mathcal{M}$, and the restriction of $\mu^*$ to $\mathcal{M}$ is a measure.
```

A proof can be found in any standard book on measure theory, for instance {cite}`Halmos:1950a` or {cite}`RoydenFitzpatrick_1988n`.

The size of the $\sigma$-algebra of measurable sets depends, of course, on the outer measure $\mu^*$. If $\mu^*$ is behaving rather pathetically, we cannot expect $\mathcal{M}$ to contain many sets.


## Lebesgue measure

A standard way to obtain "nice" outer measures is to start with a well-behaved function defined on a certain class of sets, and then approximate. The paradigm for this approach is the construction of **Lebesgue measure** on $\Real$. 

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

We call the $\lambda^*$-measurable sets **Lebesgue measurable**. 

The following two facts are also standard {cite}`RoydenFitzpatrick_1988n`.

```{prf:proposition}
:label: prop-outer-meas-interval

If $I \subseteq \Real$ is an interval, then $\lambda^*(I)$ is equal to the length of $I$ (possibly infinite).
```

```{prf:proposition}
:label: prop-interval-measurable

Any interval $I \subseteq \Real$ is Lebesgue measurable.
```

```{prf:corollary}
:label: cor-Borel-measurable

Any Borel set in $\Real$ is Lebesgue measurable
```

```{prf:proof}
:nonumber: true

This follows from {prf:ref}`prop-measurable-sets`, {prf:ref}`prop-interval-measurable` and the fact that any open set in $\Real$ is a countable union of intervals.
```

The construction of Lebesgue measure can be generalized and extended to other metric spaces, for example through the concept of **Hausdorff measures**. 

All these measures are **Borel measures**, in the sense that the Borel sets are measurable. However, there are measurable sets that are not Borel sets. The reason for this lies in the presence of **nullsets**, which are measure theoretically "easy" (since they do not contribute any measure at all), but can be topologically quite complicated.


## Nullsets

Let $\mu^*$ be an outer measure on $X$. If $\mu^*(A) = 0$, then $A$ is called a **$\mu^*$-nullset**.

```{prf:proposition} 
:label: prop-nullsets-measurable

Any $\mu^*$-nullset is $\mu^*$-measurable.
```

```{prf:proof}
:nonumber: true

Suppose $\mu^*(A)=0$. Let $B \subseteq X$. Then, since $\mu^*$ is subadditive and monotone,

$$
    \mu^*(B) \leq \mu^*(B \cap A) + \mu^*(B \cap \Co{A}) = \mu^*(B \cap \Co{A}) \leq \mu^*(B),
$$

and therefore $\mu^*(B) = \mu^*(B \cap A) + \mu^*(B \cap \Co{A})$.
```

The next result confirms the intuition that nullsets are a notion of smallness.

```{prf:proposition} 
:label: prop-null-sigmaideal

The $\mu^*$-nullsets form a $\sigma$-ideal.
```

```{prf:proof}
:nonumber: true

(I1) follows directly from monotonicity (O2). Countable additivity follows immediately from subadditivity (O3).
```

In case of Lebesgue measure, we can use Proposition {prf:ref}`prop-nullsets-measurable` to further describe the Lebesgue measurable subsets of $\Real$.

```{prf:proposition}
:label: measurable-diff-Borel

A set $A \subseteq \Real$ is Lebesgue measurable if and only if it is the difference of a $\bPi^0_2$ set and a Lebesgue nullset.
```

```{prf:proof}
:nonumber: true

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

```{prf:proposition}
:label: prop-measurable-sigma-algebra

The $\sigma$-algebra of Lebesgue measurable sets in $\Real$ is the smallest $\sigma$-algebra containing the open sets and the nullsets.
```

As mentioned before, there are Lebesgue measurable sets that are not Borel sets. We will eventually encounter such sets. The question which sets exactly are Lebesgue measurable was one of the major questions that drove the development of descriptive set theory, just like the question which uncountable sets have perfect subsets.
 


## Baire category

The basic paradigm for smallness here is of topological nature. A set is small if it does not look anything like an open set, not even under closure. In the following, let $X$ be a Polish space.

```{prf:definition}
:label: def-nowhere-dense

A set $A \subseteq X$ is **nowhere dense** if its complement contains an open, dense set.
```

Being nowhere dense means for any open set $U \subseteq X$ we can find a non-empty open subset $V \subseteq U$ such that $V \subseteq \Co{A}$. In other words, a nowhere dense set is "full of holes".

Examples of nowhere dense sets are all finite, or more generally, all discrete subsets of a perfect Polish space, i.e. sets all whose points are isolated. There are non-discrete nowhere dense sets, such as $\{0\} \cup \{1/n \colon n \in \Nat \}$ in $\Real$, even uncountable ones, such as the middle-third Cantor set.

The nowhere dense sets form an ideal, but not a $\sigma$-ideal: Every singleton set is nowhere dense, but there are countable sets that are not, such as the rationals $\Rat$ in $\Real$.

To obtain a $\sigma$-ideal, we close the nowhere dense sets under countable unions.

```{prf:definition}
:label: def-meager

A set $A \subseteq X$ is **meager** or of **first category** if it is the countable union of nowhere dense sets. Non-meager sets are also called sets of **second category**. Complements of meager sets are called **comeager** or **residual**.
```

The meager subsets of $X$ form a $\sigma$-ideal. Examples of meager sets are all countable sets, but there are uncountable ones (Cantor set).

The concept of Baire category is often used in existence proofs: To show that a set with a certain property exists, one shows that the set of points *not having the property* is meager. A famous example is Banach's proof of the existence of continuous, nowhere differentiable functions. For this to work, of course, we have to ensure that the complements of meager sets are non-empty.

```{prf:theorem} Baire Category Theorem
:label: thm-Baire-category

For any Polish space $X$, the following statements hold.
- **(a)** For every meager set $M \subseteq X$, the complement $\Co{M}$ is dense in $X$.
- **(b)** No non-empty open set is meager.
- **(c)** If $\{D_n\}$ is a countable family of open, dense sets, then  $\bigcap_{n} D_n$ is dense.
```

```{prf:proof}
:nonumber: true

(a) Assume  $M = \bigcup_n N_n$, where each $N_n$ is nowhere dense. Then $\Co{M} = \bigcap D_n$, where each $D_n$ contains a dense, open set. Let $U \subseteq X$ be open. 

We construct a point $x \in U \cap \Co{M}$ by induction. We can find an open ball $B_1$ of radius $<1$ such that $\Cl{B_1} \subseteq U \cap D_1$, since $D_1$ contains a dense open set. In the next step, we use the same property of $D_2$ to find an open ball $B_2$ of radius $<1/2$ whose closure is completely contained in $B_1 \cap D_2$. 
Continuing inductively, we obtain a  nested sequence of balls $B_n$ of radius $<1/n$ such that $\Cl{B_n} \subseteq B_{n-1} \cap D_n$. 

Let $x_n$ be the center of $B_n$. Then $(x_n)$ is a Cauchy sequence, so $x = \lim_n x_n$ exists in $X$. Since for any $n$, all but finitely many $x_i$ are in $B_n$, we have $x \in \Cl{B_n}$ for all $n$. Therefore, by construction

$$
    x \in \bigcap_n \Cl{B_n} = \bigcap_n B_n \subseteq U \cap \bigcap_n D_n \subseteq U.
$$

(b) follows immediately from (a), the proof of (c) is exactly the same as that for (a). In fact, the three statements are equivalent. 
```

Any topological space that satisfies the three equivalent conditions (a)-(c) is called a **Baire space** (not to be confused with *the* Baire space $\Baire$ -- the latter is, of course, a Baire space, too).

As an application, we determine the exact location of $\Rat$ in the Borel hierarchy of $\Real$.

```{prf:corollary}
:label: cor-rationals-not-pi2

$\Rat$ is not a $\bPi^0_2$ set, hence a true $\bSigma^0_2$ set.
```

```{prf:proof}
:nonumber: true

Note that $\Real$ cannot be meager, by (b). Since $\Rat$ is meager, $\Real \setminus \Rat$ cannot be meager either. 
If $\Rat$ were a $\bPi^0_2$ set, it would be the intersection of open, dense sets and hence its complement $\Real \setminus \Rat$ would be meager.
```


## The Baire property

We have seen that the measurable sets are precisely the ones that differ from a $\bPi^0_2$ set by a nullset.
We can introduce a similar concept for Baire category.

```{prf:definition}
:label: def-BP

A set $B \subseteq X$ has the **Baire property** if there exists an open set $G$ and a meager set $M$ such that 

$$
    B \bigtriangleup G = M,
$$

where $\bigtriangleup$ denotes the *symmetric difference* between two sets: $A \bigtriangleup B = (A\setminus B) \cup (B \setminus A)$.
```

```{admonition} Exercise
:class: tip

Show that $\bigtriangleup$ is commutative, associative, and satisfies the distributive law

$$
A \cap (B \bigtriangleup C) = (A \cap B) \bigtriangleup (A \cap C).
$$
```

In the above definition, we can replace open sets by closed sets.

```{prf:lemma}
:label: lem-BP-closed

A set $B$ has the Baire property if and only if it can be represented in the form $B = F \bigtriangleup M$,  where $F$ is closed and $M$ is meager.
```

```{prf:proof}
:nonumber: true

Suppose $B = G \bigtriangleup M$, $G$ open and $M$ meager.

Then $N = \Cl{G} \setminus G$ is nowhere dense and closed. Furthermore, $Q = M \bigtriangleup N$ is meager (it is the union of two meager sets). We easily verify that $G = \Cl{G} \bigtriangleup N$, and therefore

$$
B = G \bigtriangleup M = (\Cl{G} \bigtriangleup N) \bigtriangleup M = \Cl{G} \bigtriangleup (N \bigtriangleup M) = \Cl{G} \bigtriangleup Q,
$$ 
as desired.

The converse direction is similar, using the interior instead of the closure.
```

```{prf:proposition}
:label: prop-BP-sigma-algebra

The sets having the Baire property form a $\sigma$-algebra.
```

```{prf:proof}
:nonumber: true

To show closure under complement, note that $\Co{(A \bigtriangleup B)} = \Co{A} \bigtriangleup B$. Therefore,
if $B = G \bigtriangleup M$ with $G$ open and $M$ meager, we have $\Co{B} = \Co{G} \bigtriangleup M$, and we can use {prf:ref}`lem-BP-closed`.

Now assume $B = \bigcup B_i$, and for each $i$ there exist open $G_i$ and meager $M_i$ such that $B_i = G_i \bigtriangleup M_i$.

Let $G = \bigcup G_i$ and $M = \bigcup M_i$. Then $G$ is open and $M$ is meager (since the meager sets for a $\sigma$-ideal). 

We easily check that

$$
G \setminus M  \subseteq B \subseteq G \cup M.
$$

This implies $B \bigtriangleup G \subseteq M$ and hence $B \bigtriangleup G$ is meager. 

Since

$$
B = G \bigtriangleup (B \bigtriangleup G),
$$

we conclude that $B$ has the Baire property. 
```


```{prf:corollary}
:label: cor-BP-algebra-small

The $\sigma$-algebra of sets having the Baire property is the smallest $\sigma$-algebra containing all open and all meager sets.
```

(exercise-BP-gdelta-plus)=
```{admonition} Exercise
:class: tip

Show that $B$ has the Baire property if and only if it can be represented as a $G_\delta$ set plus a meager set.
```


As in the case of measure, there exist non-Borel sets with the Baire property, and using the Axiom of Choice one can show that there exists set that do not have the Baire property.
 

We conclude this lecture with a note on the relationship between measure and category. From the results so far it seems that they behave quite similarly. This might lead to the conjecture that maybe they more or less coincide. This is not so, in fact, they are quite orthogonal to each other, as the next result shows.

```{prf:proposition}
The real numbers can be partitioned into two subsets, one a Lebesgue nullset and the other one meager.
```

```{prf:proof}
:nonumber: true

Let $(G_n)$  be a sequence of open sets witnessing that $\Rat$ is a nullset, i.e. each $G_n$ is a union of disjoint open intervals that covers $\Rat$ and whose total length does not exceed $2^{-n}$. Then $G = \bigcap_n G_n$ is a nullset, but at the same time it is an intersection of open dense sets, thus comeager, hence its complement is meager.
``` 



