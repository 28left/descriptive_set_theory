(AC)=
# The Axiom of Choice

Can every set be well-ordered? This property is equivalent to the **Axiom of Choice** and therefore has a somewhat controversial ontological status among mathematicians.

Let $X$ be a set of non-empty sets. A **choice function** for $X$ is a function $f$ that assigns every set $Y \in X$ an element $y \in Y$.  


```{note} Axiom of Choice ($\AC$)
:icon: false

Every set $X$ of non-empty sets has a choice function.
```
The Axiom of Choice allows for enumerating a (non-empty) set $A$ by using  a choice function for all non-empty subsets of $A$. If the set of elements of $A$ not yet enumerated is non-empty, the choice function applied to this set will give us the next element to be enumerated (thereby well-ordering $A$). On the other hand, if $A$ is well-ordered, we can obtain a choice function by mapping a non-empty subset of $A$ to its least element under the well-ordering. 

It follows that the Axiom of Choice is equivalent to Zermelo's Well-Ordering Principle:

```{note} Well-Ordering Principle ($\WO$)
:icon: false

Every set can be well-ordered
```

Besides $\WO$, $\AC$ has applications in pretty much any branch of mathematics, with many equivalent principles (such as *Zorn's Lemma*, that every vector space has a basis, and Tychonoff's theorem), but also some strange consequences (such as the [Banach–Tarski paradox](wiki:Banach–Tarski_paradox)).


The foundational issue with the Axiom of Choice lies primarily in the fact that it postulates the existence of a function without giving any hint at how such a function might be defined. For some sets (e.g., the rationals) we can explicitly describe a well-ordering (by identifying $\Q$ with a subset of $\Z\times \Nat$ and then well-ordering that). But $\AC$ also guarantees a well-order of the reals, and if you try to 'write down' such a well-order, you will quickly run into difficulties.
```{prf:remark} Further reading
:nonumber: true 

For more on the history and the controversy surrounding the Axiom of Choice, see *G.H. Moore: Zermelo's Axiom of Choice, Springer. 1982*.
```

We will need the Axiom of Choice in many places. In the next section, we will use it to develop the theory of cardinal numbers. Some axioms that are considered in descriptive set theory (such as the **Axiom of Determinacy**, $\AD$) contradict $\AC$. It is therefore important to keep track of where exactly we use the Axiom of Choice.

For some applications, it suffices to use weaker forms of $\AC$.

```{note} Axiom of Countable Choice ($\AC_\omega$)
:icon: false

$$ 
\forall n \in \N \; A_n \ne \emptyset \quad \Rightarrow \quad  \exists f \; \forall n \in \omega \;  f(n) \in A_n
$$
```

```{note} Axiom of Dependent Choice ($\DC$)
:icon: false

If $R$ is a binary relation on a set $A$, $a_0 \in A$, and $\forall x \in A \exists y \in A \; xRy$, then 
$$
\exists f : \N  \longrightarrow A  \text{ with }  \; f(0) = a_0  \; \wedge  \;\forall n \in \N  \; f(n) R f(n+1).
$$
```

```{prf:proposition}
:nonumber: true

$\AC$ implies $\DC$ and $\DC$ implies $\AC_\omega$.
```

Both implications are strict, in a way we will make precise later.

The axiom $\AC_{\omega}$ is sufficient to prove, for example, the following:
- Every infinite set contains a countably infinite subset.
- A countable union of countable sets is countable.

$\DC$ and $\AC_\omega$ therefore play an important role in the foundations of analysis and measure theory.

