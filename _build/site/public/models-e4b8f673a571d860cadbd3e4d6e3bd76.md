# Models of Set Theory

You may have noticed that, when introducing the axioms of $\ZFC$, we never *really* answered the question "*What is a set?*" Instead, we developed a formal theory of axioms for a binary relation that somehow describe "*how sets work*", that is, how we can obtain sets from given ones using well-known operations like power set and union.

We have then seen how we can develop a lot of standard mathematical *objects* (like $\Nat$, $\Real$) and *techniques* (like induction and definition by recursion) **inside** this formal system. In fact, most of mathematics can be developed formally inside this system. Almost all proofs you find in any standard math book are proofs that can be formalized in $\ZFC$. It is very tedious to do this for us humans, but there is little doubt it can be done, and in fact, looking at the recent work on **proof assistants** (like Coq or Lean), many parts of mathematics have been formalized (albeit not directly in $\ZFC$).

This expressiveness gives $\ZFC$ its foundational importance, but it is also the cause for much confusion for someone who first studies set theory.

From a pedagogical point of view, in what follows it is helpful to assume a "**Platonist**" perspective of mathematics, and set theory in particular, namely that *sets and the relations between exist independently (and outside) of the $\ZFC$ axioms*. The set of real numbers exists, and our development of $\Real$ inside $\ZFC$ is just a formal way to describe them. From this perspective, the axioms of $\ZF$ ($\AC$ is a little different) are just obvious truths about sets, just like the **Peano axioms** are obvious truths about natural numbers.

Among other things, this perspective allows us to treat $\ZF$ just like any other mathematical theory, like *group theory* or the theory of *algebraically closed fields*.
In particular, we can think about **models of set theory** the way we would think about models of group theory, in the sense of model theory.

A **model** would simply be a set $M$ together with a binary relation $E$ on $S$ such that

$$
    (M,E) \models \ZF,
$$

that is, all axioms hold when interpreted in $(M,E)$. Note that we use "*set*" in this context not in the formal sense, but in the "meta"-sense (the Platonist world of sets).

Working in the meta-theory ("*that what is mathematically true*"), we know by Gödel's completeness theorem that

> if $\ZF$ is consistent, then it has a model.

This model should be seen as a **set-theoretic universe**: Its elements can be seen as sets, and the interpretation  $E$ of the $\in$-symbol will tell us how these sets are connected via the element-relation.

Note that $E$ does not have to be the *actual* element relation on a set (of sets), but just some binary relation so that the axioms are satisfied.

In the meta-world, there are, of course, sets other than $M$, but that does not matter here, since all we are interested in is giving *some* universe in which our axioms hold. (Timothy Chow has suggested that set theory should rather be called "*universe theory*. He is right in the sense that what axiomatic set theory does is to define such *universes of sets*, rather than what a set is.)

In the meta-theory, we can then follow the usual techniques to show provability or non-provability results.

If we want to prove that $\CH$ is consistent with $\ZF$ (assuming $\ZF$ is consistent), we need to find a model in which both hold.

One difficulty in working with models of set theory is that they can look very different depending on whether you look at a model "**from the inside**" or "**from the outside**".

To illustrate this, assume $\ZF$ is consistent. Then, by the **[Löwenheim-Skolem theorem](https://en.wikipedia.org/wiki/L%C3%B6wenheim%E2%80%93Skolem_theorem)**, there exists a **countable model** for $\ZF$.
Yet it is a theorem of $\ZF$ that *there exists an uncountable set*. This is often referred to as **[Skolem's paradox](https://en.wikipedia.org/wiki/Skolem's_paradox)**, although it is not really an antinomy. 

If we break this down a bit, we see that the apparent paradox is really just a matter of perspective (*inside* or *outside*). Assume $(M,E)$ is a countable model of $\ZF$. Then there exists $x \in M$ such that there is no injection from $x$ to the natural numbers. Since $M$ is countable, $x$ can have at most countably many elements. So why is this *not* a contradiction? We should really read the statement above as

> there is no injection **in $M$** from $x$ to **$M$'s version** of the natural numbers.

In other words, even though $x$ is countable *from the outside*, $x$ appears uncountable *inside $M$* since a mapping witnessing its countability does not exist in $M$.

This is a first warning sign that models of $\ZF$ can behave in very unexpected ways. For another example, recall the axiom of *Foundation* asserts that the $\in$-relation is well-founded. But again, this means only "from the inside".

```{prf:proposition}
:label: prop-illfounded-ZF-model

If $\ZF$ is consistent, than there exists a model $(M,E)$ of $\ZF$ such that $(M,E)$ is ill-founded. 
```

```{prf:proof}
:class: dropdown
:nonumber: true

Introduce new constant symbols $c_n$ $(n \in \Nat)$ and add the formulas $\varphi_n \equiv c_{n+1} \in c_n$ to the axioms of $\ZF$. It is not hard to show, using the [compactness theorem](https://en.wikipedia.org/wiki/Compactness_theorem), that $\ZF + \bigcup_n \varphi_n$ has a model $(M^*, E^*)$, for which the set $\{c_n \colon n \in \Nat\}$ is ill-founded.
```

Since, as mentioned above, the model $(M^*,E^*)$ satisfies *Foundation*, the set $\{c_n \colon n \in \Nat\}$ is actually *not in* the model (and neither can be any other set with an infinite descending $\in$-chain).



## Mostowski collapse
If we restrict ourselves to models on which the $E$-relation is *actually* well-founded (i.e. from the outside), then interestingly these models look, in a way, "*natural*": They can be assumed to be the $\in$-relation on a set. Such models are also called **standard**.

Given a set theoretic structure $(M,E)$ (not necessarily a model of $\ZF$), for each $x \in M$ let
\begin{equation*}
	\Op{ext}_E(x) = \{ y \in X \colon y\, E \, x \}
\end{equation*}

If $E$ behaves "set-like", then it will respect the axiom of *Extensionality*, i.e. two sets are identical if and only if they have the same elements. Therefore we say that $E$ is **extensional** if
\begin{equation*}
	x,z \in X, \; x\neq z \quad \text{ implies } \quad \Op{ext}_E(x) \neq \Op{ext}_E(z).
\end{equation*}

Furthermore, as stated above, we want to exclude infinite descending $E$-chains. Recall we say that $E$ is **well-founded** if

>  every non-empty set $Y \subseteq X$ has an $E$-minimal element.

```{prf:theorem} Mostowski collapse
:label: thm-Mostowski-collapse

If $E$ is an extensional and well-founded relation on a set $X$, then there exists a transitive set $S$ and a bijection $\pi: X \to S$ such that
\begin{equation*}
    x \, E \, y \iff \pi(x) \in \pi(y) \quad \text{ for all $ x,y \in X$}.		
\end{equation*}
Moreover, $S$ and ${}\pi$ are unique.
```

```{prf:proof}
:class: dropdown
:nonumber: true

We construct ${}\pi$ and $S = \Op{im}(\pi)$ by recursion on $E$, which is possible since it is well-founded. 

For each $x \in X$, let
\begin{equation*}
    \pi(x) = \{\pi(y) \colon y \, E \, x \},
\end{equation*} 
and set $S = \Op{im}(\pi)$.

The injectivity of ${}\pi$ follows from the extensionality of ${}\pi$ by induction along $E$: 	
Suppose we have shown 
\begin{equation*}
\forall z \; (z E x \to \forall y  \in X (\pi(z) = \pi(y) \to z = y)).
\end{equation*}
and we have to show that it holds for $x$. Assume $\pi(x) = \pi(y)$ for some $y \in X$. Then
\begin{align*}
cEx &\Rightarrow& \pi(c) \in \pi(x) = \pi(y) &\\
&\Rightarrow& \pi(c) = \pi(z) & \qquad \text{ for some } zEy\\
&\Rightarrow& c=z & \qquad  (\text{by ind. hyp., since } cEx)\\
&\Rightarrow& cEy &.
\end{align*}
Similarly, we get $cEy \Rightarrow cEx$, hence $x=y$ as desired due to the extensionality of $E$. Finally we have
\begin{align*}
\pi(x) \in \pi(y) & \Rightarrow & \pi(x) = \pi(c) & \qquad \text{ for some } cEy \\
&\Rightarrow& x = c & \qquad \text{ (since ${}\pi$ is injective)}\\
&\Rightarrow& xEy &
\end{align*}
Thus ${}\pi$ is an isomorphism.

To see the uniqueness of ${}\pi$ and $S$, assume $\rho$, $T$ are such that the statement of the theorem is satisfied. Then $\pi \circ \rho^{-1}$ is an isomorphism between $(T, \in)$ and $(S,\in)$. Now apply the following lemma.
```

```{prf:lemma}    
:label: lem-Mostowski-unique
Suppose $X,Y$ are sets, and ${}\theta$ is an isomorphism between $(X,\in)$ and $(Y,\in)$. Then $X=Y$ and $\theta(x) = x$ for all $x \in X$.
```

```{prf:proof}
:class: dropdown
:nonumber: true
    
By induction on the well-founded relation $\in$. Assume that $\theta(z)=z$ for all $z \in x$ and let $y = \theta(x)$. 
    
We have $x \subseteq y$ because if $z \in x$, then $z = \theta(z) \in \theta(x) = y$.

We also have $y \subseteq x$: Let $t \in y$. Since $y \in Y$, there is $z \in X$ with $\theta(z) = t$. Since $\theta(z) \in y$ and $y = \theta(x)$, we have $z \in x$, and thus $t = \theta(z) = z \in x$. 

Hence $x = y$, and this also implies $\theta(x) = x$.
```

## Absoluteness and transitive models

Even if we consider well-founded standard models, interpreting set-theoretic statements in them can still lead to very different results, even for very simple formulas. 

:::{prf:example}
:nonumber: true

Consider $M = \{0, \{\{0\}\}\}$ and let $\varphi \equiv \{\{0\}\} \subseteq 0$. Clearly ${}\varphi$ is not true from the "outside". But what if we look at it from "inside" $M$? $x \subseteq y$ means $\forall z (z \in x \to z \in y)$. *Inside* $M$ this means every set $z$ *in* $M$ that is an element of $x$ is also an element of $y$. But in $M$, there is no element $z \in \{\{0\}\}$, $\{0\}$ is not an element of $M$. Therefore, 
$$
    (M, \in) \models \{\{0\}\} \subseteq 0.
$$
:::

In the example above, the set $M$ is not transitive, which allowed it to "hide" its elements. It turns out that if we require our model to be transitive, the truth of simple formulas cannot vary between the "inside" and the "outside" perspective. We call such properties **absolute**.

Given a formula ${}\varphi$ and some class $M$, we can **relativize** 
${}\varphi$ with respect to $M$ essentially by restricting all quantifiers in ${}\varphi$ to range over $M$, i.e.\ $\exists x$ becomes $\exists x \in M$ and $\forall x$ becomes $\forall x \in M$. Note that classes are defined by formulas, so the resulting formula, which we denote by $\varphi^M$, is still a formula of set theory. 

:::{prf:definition}
:nonumber: true

We say a formula $\varphi(x_0, \ldots, x_n)$ is **absolute** for a class $M$ if for all $a_0, \ldots, a_n \in M$
$$
	\varphi^M(a_0, \ldots, a_n) \text{ holds} \iff  \varphi(a_0, \ldots, a_n) \text{ holds}.
$$
:::

:::{prf:definition}
:nonumber: true

A formula ${}\varphi$ is $\Delta_0$ if it has no quantifiers or every quantifier of ${}\varphi$ is of the form $\exists x \in y$ or $\forall x \in y$ (i.e. every quantifier is *bounded*).
::: 


:::{prf:lemma}
If $M$ is transitive and ${}\varphi$ is $\Delta_0$, then ${}\varphi$ is absolute for $M$.
:::

:::{prf:proof} Sketch
:class: dropdown
:nonumber: true

Clearly $x=y$ and $x\in y$ are absolute for any $M$. It is also not hard to see that if ${}\varphi$ and ${}\psi$ are absolute for $M$, then so are $\neg \varphi$ and $\varphi \wedge \psi$. Hence all quantifier free formulas are absolute.

Finally, if ${}\varphi$ is absolute for $M$, so is $ \psi \equiv \exists x \in y \: \varphi$: 
If $\psi^M(y,\bar{z})$ holds for $y,\bar{z} \in M$, then we have $[\exists x (x \in y \: \wedge \: \varphi(x,y,\bar{z}))]^M$, i.e., $\exists x \in M(x \in y \: \wedge \: \varphi^M(x,y,\bar{z}))$. Since $\varphi^M(x,y,\bar{z})$ if and only if $\varphi(x,y,\bar{z})$, it follows that $\exists x\in y \varphi(x,y,\bar{z})$, i.e. ${}\psi$. 

Conversely, if for $y,\bar{z} \in M$, $\exists x\in y \varphi(x,y,\bar{z})$, then since $M$ is transitive, $x$ belongs to $M$, and since $\varphi(x,y,\bar{z})$ if and only $\varphi^M(x,y,\bar{z})$, we have $\exists x \in M \, (x \in y \: \wedge \: \varphi^M(x,y,\bar{z}) )$ and so $\psi^M(y,\bar{z})$.
:::

:::{prf:proposition}

The following expressions can be written as $\Delta_0$-formulas and hence are absolute for any transitive class $M$:
- $x = \emptyset$, $x=y$, $x \subseteq y$, $z = x \cap y$, $z = x \cup y$, $x = \bigcap y$, $x = \bigcup y$, $z = \{x,y\}$, $z =(x,y)$, $z= x \times y$
- $r$ is a relation, $f$ is a function, $x = \Op{dom}(f)$, $y = \Op{ran}(f)$
- $<$ is a linear order on $x$, $x$ is an ordinal, $x$ is a limit ordinal
::: 

