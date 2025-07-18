# Counterexamples through Choice

In the previous lectures, a number of **regularity principles** for sets of real numbers emerged:
- **(PS)** &nbsp;&nbsp;&nbsp; the **perfect subset property**,
- **(LM)** &nbsp;&nbsp;&nbsp; **Lebesgue measurability**,
- **(BP)**  &nbsp;&nbsp;&nbsp; the **Baire property**.

We have seen that the Borel sets in $\Real$ have all these properties. In this lecture we will show how to construct counterexamples for each of these principles. The proofs make essential use of the Axiom of Choice.

One of the most famous applications of $\AC$ is Vitali's construction of a non-Lebesgue measurable set.

```{prf:theorem} $\AC$
:label: thm-Vitali-nonmeasurable

There exists a set $A \subseteq \Real$ that is not Lebesgue measurable.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Put
\begin{equation*}
    x \sim y \; \text{ if and only if }\;  x-y \in \Rat.
\end{equation*}
It is straightforward to check that this is an equivalence relation on $\Real$.
Using a choice function on the equivalence classes of $\sim$ intersected with the unit interval $[0,1]$, we pick from each equivalence class a representative from $[0,1]$, and collect them in a set $S$.

If we let, for $r \in \Rat$,
\begin{equation*}
    S_r = \{s+r \colon s \in S \},
\end{equation*}
then 

$$S_r \cap S_t \quad \text{ for $r \neq t$}.$$
    
Suppose $S$ is measurable. Then so is each $S_r$, and $\lambda(S_r) = \lambda(S)$.

If $\lambda(S) = 0$, then $\lambda(\Real) = 0$, which is impossible.
On the other hand, if $\lambda(S) > 0$, then, by countable additivity,
\begin{equation*}
    2 = \lambda([0,2]) \geq \lambda\left(\bigcup_{r\in \Rat\cap[0,1]} S_r\right) = \sum_{r\in \Rat\cap[0,1]} \lambda(S) = \infty,
\end{equation*} 
contradiction.
```

Next, we use the Well-ordering Principle ($\WO$) to construct a set $B\subseteq \Real$ such neither $B$ nor $\Real\setminus B$ contains a perfect subset. Such sets are called **Bernstein sets**.

```{prf:theorem} $\AC$ 
:label: thm-Bernstein

There exists a Bernstein set.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $\mathcal{P}$ be the set of perfect subsets of $\Real$. We can well-order this set, say
\begin{equation*}
    \mathcal{P} = \{P_\xi \colon \xi < 2^{\aleph_0} \}.
\end{equation*}
Note that there are $2^{\aleph_0}$-many open subsets of $\R$ (as every open set is a countable union of open intervals with rational endpoints) and therefore $2^{\aleph_0}$-many closed subsets of $\R$. Since every perfect set is closed, there are at most $2^{\aleph_0}$-many perfect subsets of $\Real$, and it is not hard to see that there are exactly $2^{\aleph_0}$-many. Hence we can choose a well-ordering of $\mathcal{P}$ of length $2^{\aleph_0}$.

Furthermore, we assume each $P_\xi$ is well-ordered.

Pick $a_0 \neq b_0$ from $P_0$. Assume for $\xi < 2^{\aleph_0}$ we have chosen  $\{a_\beta\colon \beta < \xi \}$ and $\{b_\beta\colon \beta < \xi \}$ so that
\begin{equation*}
   \forall \beta < \xi \; \; a_\beta, b_\beta \in P_\beta \quad \text{ and } \quad \text{all $a_\beta, b_\gamma$ pairwise distinct},
\end{equation*}
we can choose $a_\xi, b_\xi \in P_\xi$ to be the first two elements of $P_\xi \setminus \bigcup_{\gamma < \xi} \{a_\gamma, b_\gamma\}$. This is possible since a perfect subset of $\Real$ has cardinality $2^{\aleph_0}$, and $\xi< 2^{\aleph_0}$.

Put
\begin{equation*}
        A = \{a_\xi \colon \xi < 2^{\aleph_0} \} \qquad B = \{b_\xi \colon \xi < 2^{\aleph_0} \}.
\end{equation*}
Neither $A$ nor $B$ has a perfect subset by construction, and since $A \subseteq \Real\setminus B$, $B$ is a Bernstein set.
```

```{prf:proposition}
:label: prop-Bernstein-BP

A Bernstein set does not have the Baire property. 
```

```{prf:proof}
:class: dropdown
:nonumber: true

Assume for a contradiction a Bernstein set $B$ has the Baire property. By [an exercise](#exercise-BP-gdelta-plus) in the previous chapter, we can write $B = M \cup G$, where $M$ is meager and $G$ is $G_\delta$.

At least one of $B$, $\Real\setminus B$ is not meager. Wlog assume $B$ is not meager. (If not, obtain the representation "meager $\cup$ $G_\delta$" above for $\Real\setminus B$ and proceed analogously.) Then $G \subseteq B$ must be non-meager, too, and hence is an uncountable $G_\delta$ set. By {prf:ref}`thm-subsets-Polish`, $G$ is Polish and hence must contain a perfect subset, contradiction.
```

```{admonition} Exercise
:class: tip

Show that a Bernstein set is not Lebesgue measurable.
```

As mentioned before, the existence of arbitrary choice functions appears to be a rather strong assumption.  However, the weaker versions of $\AC$ introduced in the section [](#AC) do not suffice to construct counterexamples as above. {cite:t}`Solovay:1970a` constructed (though under a large cardinal assumption) a model of $\ZF+\DC$ in which every set of real numbers is Lebesgue measurable, has the Baire property, and has the perfect subset property.
