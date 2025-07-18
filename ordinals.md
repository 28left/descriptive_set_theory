# Ordinals

It will be important for us to extend the usual counting process beyond the natural numbers. To give an example, let us return for a moment to perfect subsets of the reals. To show that every uncountable closed subset of $\mathbb{R}$ contains a perfect subset, we considered the *condensation points* of the set. There is another, more constructive way, to arrive at a perfect subset. When Cantor studied convergence of Fourier series, he introduced the **derivative** of a set: 
$$
A' = \{ x \in A \colon x \text{ is a limit point of } A\}
$$
We can iterate the derivative and consider $A^\prime, A^{\prime\prime}, A^{\prime\prime\prime}, \dots$. This yields a descending sequence of sets
$$
A^\prime \supseteq  A^{\prime\prime} \supseteq A^{\prime\prime\prime} \supseteq \dots \supseteq A^{(n)} \supseteq \dots
$$

```{hint} Exercise 
:nonumber: true

Find a set $A$ such that for all $n$, $A^{(n)} \supsetneq A^{(n+1)}$.
```
As the sequence is nested, we can take a “limit”:
$$
A^{\infty} = \bigcap_n A^{(n)}
$$
But the process does not necessarily stop here. $A^\infty$ may have isolated points again, so that $A^\infty \supsetneq (A^\infty)^\prime$. 

```{hint} Exercise
:nonumber: true

Find a set $A$ such that $A^\infty \supsetneq (A^\infty)^\prime \neq 0$.
```
Let us introduce ${\omega}$ as a new number to be used in place of $\infty$ above. We can continue the counting process:
$$
1,2,3, \dots, \omega, \omega+1, \omega+2, \dots, \omega + \omega, \omega + \omega +1, \dots, \omega + \omega + \omega, \dots, \omega\cdot \omega, \dots
$$

We can then define, for example,
$A^{\omega+1} := (A^{\omega})'$. As intuitively clear from above, the new transfinite numbers come with a natural ordering, so we can put, for example, $A^{\omega+\omega} := \bigcap_{\alpha < \omega+\omega} A^{\alpha}$.

To obtain a perfect subset, one can show that the above process of taking derivatives, eventually reaches a *fixed point*: some stage $\alpha$ for which $(A^{\alpha})' = A^\alpha$. If $A$ is uncountable, $A^\alpha$ will be a perfect subset, since one can show that at each derivative step we remove an at most countable set and it will take at most countably many steps to reach the fixed point. But what does "countably many steps" exactly mean if we have to count past $\omega$? The formal notions of *ordinal* and *cardinal numbers* will answer this question.  

<!-- --- 

Another way to count into the transfinite is to reorder the natural numbers and first enumerate all powers of two, followed by all powers of three and so on:
\begin{gather*}
	1, 2, 4, 8, \ldots 3, 9, 27, \ldots 5, 25, 125, \ldots
\end{gather*}
This still leaves an infinite reservoir of numbers like $0, 6, 10, \dots$. 

A number of questions arises: 
- Can this process be continued indefinitely?
- Is there a *unifying* principle behind the various ways to count into the transfinite?
- Can we define operations like $+$ and $\cdot$ on these infinite numbers independent of the way we represent these numbers, and without leading to contradictions? -->

The fundamental concept on which the ordinal numbers are based if that of a **well-order**.



## Orders and well-orders

```{prf:definition}
:nonumber: true

A (**reflexive** or **non-strict**) **partial order** on a set $A$ is a binary relation $\leq$ on $A$ such that for all $a,b,c \in A$,
-  $a\leq a$ &emsp; (reflexive)
-  $a \leq b \; \wedge \; b \leq a \quad \Rightarrow \quad a = b$ &emsp; (anti-symmetric)
 
-  $a \leq b \; \wedge \; b \leq c \quad \Rightarrow \quad a \leq c$ &emsp; (transitive).

A **linear** (or **total**) **order** additionally satisfies for all $a,b \in A$,
-  $a \leq b \; \vee \; b \leq a$  &emsp; (connected).
```

With any reflexive partial order $\leq$ we can associate an *irreflexive* or *strict* partial order by letting
$$a < b \quad :\iff \quad a \leq b \; \wedge \; a \neq b.$$
Likewise, we can obtain a reflexive order from a strict one by defining
$$a \leq b \quad :\iff \quad a < b \; \vee \; a = b.$$
We will use $\leq$ or similar symbols to indicate the order is reflexive, while $<$, $\prec$, etc. are reserved for strict orders. 

```{prf:example}
:nonumber: true

- The usual orders on $\mathbb{Z}$, $\mathbb{Q}$, and $\mathbb{R}$ are linear orders.
- The relation
$$
f \leq g \quad : \iff \quad \forall x \in \mathbb{R} \;\; f(x) \leq g(x)
$$
is a partial order on real valued functions on $\mathbb{R}$ but not a linear order.
- The subset relation $\subseteq$ is a partial order on the power set of any set $A$, but it is a linear order only when $A = \emptyset$ or $A$ is a singleton set. 
```

We can enumerate the natural numbers one after another, but for the other standard ordered number domains this is not possible: We cannot find a place to begin counting (as in the case of $\mathbb{Z}$) or there is no "next bigger" element (as in the case of $\mathbb{Q}$ or $\mathbb{R}$). 


To enumerate these domains in the form $\{a_0, a_1,\ldots, a_n, a_{n+1}, \ldots \}$ we have to reorder them in a way that
- we can start with a smallest element,

and once we have arrived at an element $a$, 
- we know with which element we continue the enumeration (i.e. there is an *immediate successor* to $a$),
- we can continue the enumeration even if we have already enumerated infinitely many elements before $a$ (but elements of the domain still remain). 

These requirements can be combined into a single property: every non-empty subset (i.e. the elements not enumerated yet) has a least element (to be enumerated next).

```{prf:definition}
:nonumber: true

A (strict) linear order $(A,<)$ is a **well-order** if 
$$
\forall Z \; (\emptyset \ne Z \subseteq A \; \Rightarrow \; \exists x \in Z \; \forall y \in Z \;  x \leq y)
$$
```

Orders themselves can be compared using *embeddings*.

```{prf:definition}
:nonumber: true

An **embedding** of a partial order $(A,<_A)$ into another partial order $(B,<_B)$ is a mapping $f:A \to B$ such that for all $x,y \in A$
$$
x <_A y \quad \iff \quad f(x) <_B f(y).
$$

Two orders are **isomorphic** if there exists a bijective embedding of one into the other.
```

Of course every order is isomorphic to itself (*automorphic*) via the identity. But many orders allow automorphisms other than the identity (e.g. $\mathbb{Z}$ or $\mathbb{R}$ with $z \mapsto z+1$). As we will see, well-orders are very rigid in this regard.

We start with a simple observation.

```{prf:proposition}
:label: pro-wo-embedding-increases
Let $(A,<)$ be a well-order and assume $f:A \to A$ is a self-embedding. Then for all $x \in A$, $x \leq f(x)$.
```
```{prf:proof}
:class: dropdown
:nonumber: true

If the set $\{x \in A \colon f(x) < x\}$ is non-empty, it has a minimal element $z$. But since $f$ is increasing, this would imply $f(f(z)) < f(z)$, contradicting the minimality of $z$. 
```

We immediately obtain

```{prf:corollary}
:nonumber: true

The only automorphism of a well-order is the identity.
```

An **initial segment** of an order $(A,<)$ is given by all elements that are smaller than a given element $b$. We denote this initial segment by $A\mid_b$. 

```{prf:corollary}
:nonumber: true

No well-order is isomorphic to an initial segment of itself.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Suppose $f: A \to A\mid_b$ is an isomorphism. Then $\operatorname{ran}(f) = A\mid_b$ and $f(x) < b$ for all $x \in A$. In particular, $f(b) < b$, contradicting @pro-wo-embedding-increases.
```

## Ordinal numbers

*Cantor* defined ordinal numbers (or ordinals) as **isomorphism classes of well-orders**. Later, *von Neumann* suggested a system of representatives particularly suitable for set theoretic considerations. The idea is to define the order $<$ through the $\in$-relation on a set. For example, 
$$
\{ \emptyset, \{\emptyset\}, \{\emptyset, \{\emptyset\}\}\}
$$ 
represents a $3$-element well-order. 

We will impose some conditions on the sets we allow as ordinals. Given a set $A$, we use $\in_A$ to denote the $\in$-relation *on* $A$:
$$
\in_A = \{ (x,y) \colon x,y \in A \; \wedge \; x \in y \}
$$

```{prf:definition}
:nonumber: true
:label: def-transitive
A set $A$ is **transitive** if 
\begin{equation*} \tag{trans}
    \forall x \in A \; \; x \subseteq A
\end{equation*}
```
```{prf:remark}
:nonumber: true
A set being transitive is not equivalent to $\in$ being transitive on the set. (Counterexample?)
```

In other words, transitive sets cannot "hide" elements in subsets.

```{prf:definition}
:nonumber: true
:label: def-ordinal

A set $A$ is an **ordinal** if it is transitive and well-ordered by $\in_A$
```
It is customary to use *lower case Greek letters* $\alpha, \beta, \gamma, \dots$ to denote ordinals.

If we exclude certain pathological sets from the beginning, we can further simplify this definition.

```{prf:definition}
:nonumber: true
:label: set-well-founded

A set $A$ is **well-founded** if every non-empty subset has a $\in$-minimal element:

$$\forall B \subseteq A \; (B \ne \emptyset \; \Rightarrow \; \exists y \in B \;  \forall z \in B \; \; z \not \in y)$$
```

Sets which contain themselves ($A \in A$) are not well-founded$-$ $\{A\}$ would be a subset without a $\in$-minimal element. Similarly, well-founded sets cannot have cycles like $a \in b \in c \in a$. 

```{prf:proposition}
:label: pro-ordinal-linear-order

Assume every set is well-founded. A set $A$ is an **ordinal** if and only if it is transitive and linearly ordered by $\in_A$.
```

```{hint} Exercise 
:class: tip
:nonumber: true

Prove [](#pro-ordinal-linear-order). 
```


If we write out the formulas in full, we see the characterization given in @pro-ordinal-linear-order is much simpler than the original one. Most notably, in @pro-ordinal-linear-order we only use only **bounded quantifiers** (of the form $\forall y \in a$), whereas in the original form we have to quantify over arbitrary subsets of $a$. This is an important difference whose impact will become clear later on.


```{prf:proposition}
:label: pro-ordinal-elements-are-ordinals
Any element of an ordinal is an ordinal.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let ${\alpha}$ be an ordinal, and assume $b \in \alpha$. Any subset of a linear order is again a linear order under the induced order relation. It remains to show that $(b, \in_b)$ is transitive (as a set). Let $x \in c \in b$. We claim $x \in b$. Since ${\alpha}$ is transitive, $b \subseteq \alpha$ and hence $c \in \alpha$. By transitivity of ${\alpha}$ again, $x \in \alpha$. Thus $x,b \in \alpha$, and since $\in_\alpha$ linearly orders ${\alpha}$, we must have
$$
x \in b \; \vee \; x = b \; \vee \; b \in x.
$$
If $x = b$, we get $b \in c \in b$, contradicting well-foundedness. Similar for $b \in x$. Therefore, $x \in b$.
```

## The well-ordering of ordinals

@pro-ordinal-elements-are-ordinals suggests we can order ordinals by letting
$$
\alpha < \beta \; :\iff \; \alpha \in \beta.
$$
By @pro-ordinal-elements-are-ordinals, an ordinal then contains precisely the ordinals smaller than it:
$$
\alpha = \{ \beta : \beta < \alpha \}.
$$

$\in$ defines a partial order on all ordinals:
As all sets are well-founded, irreflexivity holds, and since ordinals are transitive sets, $<$ is a transitive relation.

```{prf:proposition}
:label: pro-order-ordinals

For any ordinals $\alpha, \beta$,
$$
\alpha < \beta \; \iff \; \alpha \subset \beta.
$$
```

```{hint} Hint
:class: dropdown
For $\Leftarrow$, show that 
$$
\Op{trans}(a) \; \wedge \; a \subset \beta \quad \Rightarrow \quad \Op{Ord}(a) \; \wedge \; a \in \beta.
$$
To show $a \in \beta$, consider the $\in$-minimal element of $\beta\setminus a$.
```


```{prf:proof}
:nonumber: true
:class: dropdown

The $\Rightarrow$ direction follows directly from the transitivity of ordinals.
For $\Leftarrow$, we show something more general, namely that any transitive proper subset of an ordinal is itself an ordinal and is an element of the superset ordinal:
$$
\Op{trans}(a) \; \wedge \; a \subset \beta \quad \Rightarrow \quad \Op{Ord}(a) \; \wedge \; a \in \beta.
$$
If $a \subset \beta$, $a$ is linearly ordered by $\in$ (as a subset of ${}\beta$). Further, if $a$ is transitive, $a$ is an ordinal. 

It remains to show $a \in \beta$. Since $a$ is a proper subset of ${}\beta$, by well-foundedness there exists a $\in$-minimal element of $\gamma \in \beta \setminus a$. We claim $a = \gamma$. By $\in$-minimality of ${}\gamma$, every element of ${}\gamma$ cannot be in $\beta\setminus a$ and therefore has to be in $a$. Hence $\gamma \subseteq a$. On the other hand, if $x \in a$, then, by assumption $x \in \beta$, and since $\in$ linearly orders ${}\beta$, 
$$
x \in \gamma \; \vee \; x = \gamma \; \vee \; \gamma \in x.
$$
The latter two are impossible due to $\gamma \notin a$. Hence $x \in \gamma$ and therefore $a \subseteq \gamma$, yielding $a =\gamma$.
```

```{danger} Theorem (well-ordering of ordinals)
:icon: false

The ordinal numbers are well-ordered by $<$.
```

```{hint} Hint
:class: dropdown

Most properties follow directly from well-foundedness and the fact that ordinals are transitive as sets. 

To show that ordinals are linearly ordered by $<$, look at the intersection of two ordinals and try to apply @pro-order-ordinals.
```


```{prf:proof}
:nonumber: true
:class: dropdown

We first show $<$ is a linear order. Irreflexivity follows from well-foundedness of $\in$. Transitivity of $<$ follow from the transitivity of ordinals as sets. To show
$$
\alpha < \beta \; \vee \; \alpha = \beta \; \vee \; \beta < \alpha,
$$
observe that the intersection of two ordinals is an ordinal, the *minimum* of the two ordinals. Let $\gamma = \alpha \cap \beta$. Then $\gamma \subseteq \alpha$, so by @pro-order-ordinals, $\gamma \in \alpha$ or $\gamma = \alpha$ and similarly $\gamma \in \beta$ or $\gamma = \beta$. But in the case $\gamma \in \alpha, \gamma \in \beta$ we would have $\gamma \in \alpha \cap \beta = \gamma$, contradicting well-foundedness.

Finally, if $A$ is a non-empty set of ordinals, the well-ordering condition on $<$ spells out as
$$
\exists \alpha \in A \; \forall \beta \in A \; \; \beta \notin \alpha.
$$
But this holds since we assume all sets are well-founded.
```

(ordinals-basic)=
## Basic properties of ordinals
Using the results obtained so far, we can now deduce some basic facts about the structure of ordinals:

- $0 = \emptyset$ is the *smallest ordinal*.

- Every ordinal ${\alpha}$ has an **immediate successor** under the ordering $<$: 
$$\alpha' =  \alpha+1 = \alpha \cup \{\alpha\}.$$
Clearly $\alpha < \alpha+1$. If $\alpha < \beta$, then by @pro-order-ordinals, $\alpha \subset \beta$ and $\alpha \in \beta$. Hence $\alpha+1 \subseteq \beta$ and therefore $\alpha+1 \leq \beta$.

- The *finite ordinals* are exactly the **natural numbers** ("set theoretic version"):

$$0 = \emptyset, \quad 1 = 0 + 1 = \emptyset \cup \{\emptyset\} = \{\emptyset\}, \quad 2 = 1+1 = \{\emptyset, \{\emptyset\} \}, \dots
$$   

- The set of all natural numbers is transitive and well-ordered by $\in$ and thus itself an ordinal, the first infinite ordinal ${\omega}$:
$$
    \omega = \{\emptyset, \{\emptyset\}, \{\emptyset, \{\emptyset\}\}, \dots \}
$$

- ${\omega}$ is also the first instance of a *limit ordinal*: A **successor ordinal** is any ordinal of the form $\alpha+1$. Any ordinal ${\lambda}$ that is not a successor is called a **limit ordinal**. Being limit is equivalent to the following property:
$$
\lambda \neq 0 \: \wedge \: \forall \alpha < \lambda \; (\alpha+1 < \lambda).
$$
This shows immediately that ${\omega}$ is limit. 

- More generally, if $A$ is a set of ordinals, $\sup A = \bigcup_{\alpha \in A} \alpha$ is an ordinal and is the least upper bound for $A$.

- The first limit ordinal ${\omega}$ is followed by a number of successor ordinals as well as their limits as limit ordinals:
\begin{gather*}
\omega, \omega+1, \omega+2, \ldots \omega+\omega, \omega+\omega+1, \omega + \omega+2, \ldots \omega+\omega+ \omega, \qquad \quad \\ \omega + \omega+ \omega+1, \omega + \omega+ \omega+2, \ldots  \omega \cdot \omega,  \omega \cdot \omega +1,\ldots, \omega^{\omega} \ldots \omega^{\omega^{\omega}} \ldots
\end{gather*}
All of the ordinals listed here are still countable (as sets). The supremum of the set of all countable ordinals is denoted by $\omega_1$, the **first uncountable ordinal**. After $\omega_1$, we have again successors, limits, and so on. 


## Metamathematical issues

Is there a *set* $\Ord$ of *all* ordinals? If so, it would be well-ordered by $\in$ and also transitive (since, by @pro-ordinal-elements-are-ordinals, every element of an ordinal is an ordinal) and therefore an ordinal. Hence we would have $\Ord \in \Ord$. But no ordinal can be an element of itself. This holds even if we do not assume every set is well-founded, since ordinals are by definition *strictly* ordered by $\in$. 

This is known as the **Anomaly of Burali-Forti**. It tells us that somehow the collection of all ordinals is *too big* to form a set. It also warns us that if we handle the intuitive concept of a set too carelessly, it might lead to contradictions and inconsistencies. 

Later on we will develop an axiomatic approach to sets which aims to exclude antinomies like this. In this framework, we will be able to formally show that $\Ord$ is not a set. It forms what we will call a **proper class**.


## Representing well-orders as ordinals

We introduced ordinals with the goal to have a specific representation for any well-order. 

```{danger} Representation theorem for well-orders
:icon: false

Any well-ordered set $(A,<)$ is order-isomorphic to a unique ordinal ${\alpha}$. The isomorphism is unique.
```

The ordinal ${\alpha}$ is called the **order type** of $(A,<)$.
We will delay the proof of this theorem for a while, until we learn how to extend *induction* and *recursion* into the transfinite. This will, in particular, give us the following generalization of the usual induction principle for the natural numbers.

```{note} Transfinite Induction
:icon: false

Let $P$ be a property of ordinals. If 
- $P$ holds for the empty set, and
- whenever $P$ holds for ${}\alpha$, it also holds for $\alpha+1$, and
- for every limit ordinal ${\lambda}$, if $P$ holds for all $\beta < \lambda$, it also holds for ${\lambda}$,

then $P$ holds for all ordinals.
```

Of course, informally one would prove this as follows: If $P$ does not hold for some ordinal, since the ordinals are well-ordered, there has to be a least ordinal ${}\alpha$ for which $P$ does not hold. But then each of the three cases ($0$, successor, or limit ordinal) would lead to a contradiction based on the assumption.

However, we have seen that there is no set of all ordinals, so we have to tread a little carefully here. We will take this up again once we have developed an axiomatic foundation for sets.
