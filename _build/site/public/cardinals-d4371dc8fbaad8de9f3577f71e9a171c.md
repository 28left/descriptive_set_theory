(cardinals)=
# Cardinals

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

The next result shows that this order is linear. To prove it, we have to use Choice.

```{danger} Theorem (Hartogs)
:icon: false
:label: thm-hartog

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

As with ordinals, we would like to choose a system of representatives for the equivalence classes under $\sim$. @thm-hartog suggests to use ordinals (which we can compare using the well-ordering of ordinals). We therefore assume the Axiom of Choice (so every set has a well-ordering). One issue that remains is that a set can have well-orderings of different lengths (as we saw in the case of the natural numbers $\Nat$). But since the ordinals are well-ordered, we can choose the *least* one of the same cardinality.

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

