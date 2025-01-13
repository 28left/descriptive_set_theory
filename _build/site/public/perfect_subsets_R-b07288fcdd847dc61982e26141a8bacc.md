# Introduction: Perfect Subsets of the Real Line


:::{admonition} Continuum Hypothesis (Cantor, 1890s)
:class: hint
:icon: false

If $A \subseteq \Real$ is uncountable, then there exists a bijection between $A$ and $\Real$. That is, is every uncountable subset of $\Real$ is of the same cardinality as $\Real$.
:::

Possible approach: show that $\CH$ holds for a number of sets with an easy topological structure.

```{admonition} Exercise
:class: attention
Show that every open set in $\R$ satisfies $\CH$ (in the sense that it either countable or can be mapped bijectively to $\R$).
```


Closed sets? 

Given a set $A \subseteq \Real$, we call $x \in \Real$ an **limit point** of $A$ if

$$
\forall \epsilon > 0 \: \exists z \in A \: [z \neq x \: \& \: z \in U_\eps(x)],
$$

where $U_\eps(x)$ denotes the standard $\eps$-neighborhood of $x$ in $\Real$

A non-empty set $P \subseteq \Real$ is **perfect** if it is closed and every point of $P$ is an limit point.


In other words, a perfect set is a closed set that has no isolated points. 

For a perfect set $P$, every neighborhood of a point $p \in P$ contains infinitely many points from $P$.

Obviously, $\Real$ itself is perfect, as is any closed interval in $\Real$. There are totally disconnected perfect sets, such as the **middle-third Cantor set** in $[0,1]$

:::{figure} ./images/Cantor_set.png
:::



:::{prf:theorem} Cantor, 1884
:label: thm-card-perfect-sets

A perfect subset of $\Real$ has the same cardinality as $\Real$.
:::


:::{prf:theorem} Cantor-Bendixson
:label: cantor-bendixson
Every uncountable closed subset of $\Real$ contains a perfect subset.
:::

```{prf:corollary}
Every closed subset of $\Real$ is either countable or of the cardinality of the continuum.
```

:::{prf:definition}
A family $\mathcal{F}$ of sets (of reals) has the **perfect set property** if every set in $\mathcal{F}$ is either countable or has a perfect subset.
:::


:::{caution} Question
Which families of sets have the perfect set property?
:::
