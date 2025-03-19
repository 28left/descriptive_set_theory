# Recursion and the Von-Neumann Hierarchy

## Transfinite induction

While the class $\Ord$ of all ordinals is not a set, it is still transitive and well-ordered by $\in$. Regarding the associated order $\leq$, every *set* of ordinals $a$ has a **supremum** $\bigcup a = \bigcup_{\xi \in a} \xi$ and (if $a \ne \emptyset$) an **infimum** 
$\bigcap a = \bigcap_{\xi \in a} \xi$, which is the *smallest element* of $a$. Such a smallest element exists actually for every (non-empty) *class* $A$ (since if $\xi \in A$, we only need to find the infimum of the *set* of ordinals $\le \xi$.) 
This allows us to prove properties about *all* ordinals by **induction**.

```{prf:proposition} Induction for ordinals, I
:label: prop-induction-ord-i

For every property ${}\varphi$, 
\begin{equation*}
    \forall \alpha \; [ \forall \xi < \alpha \; \varphi(\xi) \to \varphi(\alpha)] \to \forall \alpha \, \varphi(\alpha).
\end{equation*}
```

We have repeatedly used induction already for ordinals $< \omega_1$, the first uncountable ordinal.

To prove this principle simply observe that if $\forall \alpha \, \varphi(\alpha)$ failed there would have to be a *smallest*  ${}\alpha$ with  $\neg \varphi(\alpha)$, contradicting the induction hypothesis.

Since every ordinal is either $0$, a successor, or a limit ordinal, we have the following variant of induction.

```{prf:proposition} Induction for ordinals, II
:label: prop-induction-ord-ii

For every property ${}\varphi$, if

- **(i)** $\varphi(0)$, 
- **(ii)** $\forall \alpha (\varphi(\alpha) \to \varphi(\alpha+1))$, and
- **(iii)** $(\forall \xi < \lambda \; \varphi(\xi)) \to \varphi(\lambda)\quad $ for all limit $\lambda$,

then $\forall \alpha \;  \varphi(\alpha)$.
```

(i) and (ii) coincide with the usual induction scheme for natural numbers. To cover *all* ordinals we need to add (iii).


## Ordinal recursion

The induction principle can be used to define functions by **recursion**. For example, **addition** on the natural numbers is given by

\begin{align*}
    x+0 \quad & =  x\\
    x+ (y+1) & =  (x + y)+1. 
\end{align*}

In the case of ordinals, we have to consider the limit case, too.

```{prf:theorem} Recursion on ordinals
:label: thm-ordinal-recursion

If $G :\Ord \times \V \longrightarrow  \V$ is a function, then there exists a unique function $F: \Ord \longrightarrow \V$  such that for all $\alpha \in \Ord$,

$$
F(\alpha) = G(\alpha, F\Rest{\alpha})
$$
```

```{prf:proof}
:class: dropdown
:nonumber: true

The uniqueness of the function $F$ follows by induction. 

To show the existence of $F$, we define the following:

- Call $h$ *tame* if 
\begin{equation*}
\exists \alpha \, (h: \alpha \to \V  \wedge \forall \xi \in \alpha \; h(\xi) = G(\xi, h \Rest{\alpha}))
\end{equation*}

- Say $h$ is *compatible* with $g$ if 
\begin{equation*} 
    \forall x \in \Op{Dom}(h) \cap \Op{Dom}(g) \; h(x) = g(x)
\end{equation*}
 
It follows by induction that any two tame functions are compatible.

This lets us define the desired $F$ as

$$
F := \bigcup \{h \colon h\, \text{ tame}\}
$$

Then $F$ is a function (otherwise there would be two incompatible tame functions), its domain is transitive, and satisfies the recursion condition (since it is the union of tame functions). 

It remains to show that $F$ is defined on all of $\Ord$. 
If $D = \Op{Dom}(F) \neq \Ord$, then we would have $D = \alpha$ for some ordinal ${}\alpha$. In particular $B$ is a set therefore $F = f$ is a set, for some tame $f$. This $f$ could be extended to a tame $h = f \cup \{(\alpha,G(\alpha,f \Rest{\alpha}))\}$, contradiction.
```

Note that we defined $F$ **explicitly** as a *union* of all partial solutions to the recursion equation.


As with induction, we have the following variant of the recursion principle.

```{prf:proposition} Recursion on ordinals, variant
:label: prop-ordinal-recursion-ii

If $G, H: \Ord \times \V \longrightarrow  \V$ are functions and $a$ is a set, then there exists a unique function $F: \Ord \longrightarrow \V$  such that 
\begin{align*} 
    F(0) \quad & =  a\\ 
    F(\alpha+1) & =  G(\alpha,F(\alpha)) \\    
    F(\lambda) \quad & =  H(\lambda, \{F(\xi) \colon \xi<\lambda \}) \quad \text{for } \Op{Lim}(\lambda).
\end{align*}
```

We can establish a similar principle for a well-ordering $<$ on a class $A$. In case of a proper class, though, we have to require that for every $a \in A$,  the class of all **predecessors** of $a$
\begin{equation*}
S(a,<): = \{x \in A\colon x < a \},
\end{equation*}
is a set (if $A$ is a set, this follows automatically by *Separation*). If this is the case, the recursion principle yields a function $F: A \to \V$ such that
\begin{equation*}
    F(a) = G(a,F\Rest{S(a,<)}).
\end{equation*}


## Recursion for well-founded relations
More generally, we can define induction and recursion on **well-founded** relations. We already encountered those in a [previous chapter](sec-well-founded). 

```{prf:definition}
:label: def-well-founded

A relation $R$ on a class $A$ is **well-founded** if it satisfies the **minimality condition**
\begin{equation*}
    (\Op{Min}_R) \qquad  \emptyset \neq b \subset A \to \exists x \in b \; \forall y \in b \, (  \neg y R x)
\end{equation*}
and the **set condition**
\begin{equation*} 
    \forall x \in A \; S(a,R):= \{x \colon x R a\} \text{ is a set}
\end{equation*}
```

If $A$ is a set, the minimality condition is again automatically satisfied by *Separation*.

The set condition allows for taking the **$R$-transitive closure** of a set $a \in A$: the smallest superset $\Op{TC}_R(a)$ of $a$ that is *$R$-transitive*: 

$$ \forall x \in \Op{TC}_R(a)\; S(x,R) \subseteq  \Op{TC}_R(a)$$

This is done by recursion over the natural numbers. The following is an important example.

```{prf:example} Transitive closure of a set
:label: exa-trans-closure

By the axiom of *Foundation*, $\in$ is a well-founded relation on $\V$. (The set condition is satisfied since $S(a,\in)=a$.)

We can form the **transitive closure**, the smallest transitive superset, of a set $a$ as

\begin{align*}
    \Op{TC}(a):&= a \cup \bigcup a \cup \bigcup \bigcup a \ldots 
 = \bigcup_{n< \omega} U^n(a), \quad \text{ where} \\ 
 &U^0(a) = a, U^{n+1}(a) = \bigcup U^n(a).
\end{align*}

This is an example of definition by recursion along $\Nat$.
```

We can use the existence of $\Op{TC}_R$ as a set to strengthen the minimality condition to *subclasses*, similar to the case of the well-ordering of $\Ord$:

```{prf:lemma}
:label: lem-min-wf

For every non-empty class $B \subseteq A$, there exists $x \in B$ such that

$$
    \forall y \in B \;  \neg y R x
$$
```

To prove this lemma, simply pick any $x \in B$, take its transitive $R$-closure, and intersect it with $B$:

$$
    C = \Op{TC}_R(x) \cap B.
$$

$C$ is a set, and by the minimality condition $(\Op{Min}_R)$ has an $R$-minimal element $a$. $a$ has to be minimal for $B$, too, since otherwise there exists $b \in B$ with $b R a$. Since $a \in \Op{TC}_R(x)$, $b \in \Op{TC}_R(x)$, and therefore $b \in C$, contradicting the minimality of $a$.

The lemma implies a corresponding **induction principle for well-founded relations**:

\begin{equation*}
    (\Op{Ind}_R) \qquad  \forall x \in A [ \forall y ( yRx \, \to \varphi(y)) \to \varphi(x)] \to \forall x \in A \, \varphi(x)).
\end{equation*}

This in turn yields the following.

```{prf:theorem} Recursion principle for well-founded relations
:label: thm-wf-recursion

Let $R$ be a well-founded relation on a class $A$. The for every function $G : A \times \V \longrightarrow  \V$ exists a unique function $F: A \to \V$ such that

\begin{equation*}
    F(a) = G(a,F \Rest{\{x \mid xRa\}})  \text{ for all } a \in A.
\end{equation*}
```





## The Von Neumann hierarchy

Is there a way to systematically build the $\V$, the universe of all sets, "from below"?

We start with the empty set:

$$
V_0 = \emptyset
$$

Given $V_\alpha$, the *Power Set* axiom requires the set of all subsets to exist, so we set

$$ 
V_{\alpha+1} = \mathcal{P}(V_{\alpha}).
$$

Finally, at limit stages we simply collect all sets we have obtained so far:

$$
V_ \lambda =  \bigcup_{\xi < \lambda} V_\xi \quad \text{for limit } \lambda
$$

What we really are doing here is to construct a function $V: \Ord \to \V$ by ordinal recursion. Think $V_\alpha = V(\alpha)$.

Remarkably, if we assume the axiom of *Foundation*, we reach *all* sets this way.

```{prf:theorem}
:label: thm-von-Neumann

For every set $x$ there exists an ordinal ${}\alpha$ with $x \in V_\alpha$, that is,

$$
    \V = \bigcup_{\alpha \in \Ord} V_\alpha
$$
```
```{margin}
Recall that the notation $\bigcup_{\alpha \in \Ord} \dots$ is really just a shortcut for the class obtained as $\{ x \colon \exists \alpha \in \Ord \dots\}$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $C$ be the class of all sets not in any $V_\alpha$. Since $\in$ is well-founded, if $C$ is non-empty, it has a $\in$-minimal element $x$. This implies that for all $z \in x$, $z \in \bigcup_{\alpha \in \Ord} V_\alpha$. Define a function $h$ by mapping each $z\in x$ to the *least* ${}\alpha$ so that $z \in V_\alpha$. Since $x$ is a set, $h[x]$ is a set of ordinals, by *Replacement*. This set or ordinals has a supremum, say ${}\gamma$. Then $x \subseteq V_\gamma$ and therefore, 

$$
x \in \mathcal{P}(V_\gamma) = V_{\gamma+1}.
$$

Hence $C$ must be empty, and the theorem follows.
```

We can now split the question of "how large" $\V$ is into two sub-questions:
- How "**long**" is $\V$, that is, how many ordinals are there? Axioms for **large cardinals** attempt to extend this "length" as far as possible.
- How "**wide**" is $\V$, that is, how large is the power set of a set? A rather "slim" universe is given by the **constructible sets**, which we will encounter soon.
