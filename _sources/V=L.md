# The Axiom of Constructibility
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
\newcommand{\VL}{\mathsf{V=L}}
\newcommand{\GN}[1]{\ulcorner #1 \urcorner}
\newcommand{\Const}[1]{\underline{#1}}
\newcommand{\V}{\mathbf{V}}
\newcommand{\Ord}{\mathbf{Ord}}
\DeclareMathOperator{\W}{W}
\DeclareMathOperator{\WF}{WF}
\DeclareMathOperator{\WOrd}{WOrd}
```


We can add to $\ZF$ the axiom that all sets are constructible, i.e.

> $(\VL) \qquad \forall x \exists y \: (y \text{ is an ordinal } \wedge \; x \in L_y).$

This axiom is usually denoted by $\VL$. We may be tempted to think that $L$ is then trivially a model of $\ZF + \VL$. But this is not at all clear, since this has to hold **relative to $L$**, i.e. $(\VL)^L$.

This means that
\begin{equation*}
	\forall x \in L \: \exists y \in L \: (y \text{ is an ordinal } \wedge \; (x \in L_y)^L).
\end{equation*} 

To verify this, we need to make sure that *inside* $L$, $L$ "means the same as" $L$. This is, of course, an absoluteness property, and we therefore revisit the complexity of the formulas defining the constructible universe.

We have seen that the map $a \mapsto \mathcal{P}_{\Op{Def}}(a)$ is $\Sigma_1$. This important implications for the map $\alpha \mapsto L_\alpha$.

```{prf:proposition}
:label: prop-map-Lalpha

The map $\alpha \mapsto L_\alpha$ is $\Delta_1$.
```

```{prf:proof}
We first show that the mapping is $\Sigma_1$. The mapping is obtained by ordinal recursion over the function $a \mapsto \mathcal{P}_{\Op{Def}}(a)$. 

In general, if a function $G: \V \to \V$ is $\Sigma_1$ and $F: \Ord \to \V$ is obtained by recursion from $G$, i.e. $F(\alpha) = G(F\Rest{\alpha})$, then $F$ is also $\Sigma_1$. This is because

\begin{multline*}
    y= F(\alpha) \; \leftrightarrow \; \alpha \in \Ord \: \wedge \: \exists f \: ( f \text{ function } \wedge \Op{dom}(f) = \alpha \\
        \wedge \forall \beta < \alpha (f(\beta) = G(f \Rest{\beta}) \wedge y = G(f)).
\end{multline*}

Applying some of the various prefix transformations for $\Sigma_1$-formulas, and using that being an ordinal, being an function, being the domain of a function, etc., are all $\Delta_0$ properties, the above formula can be shown to be $\Sigma_1$, too.

In our case, $G$ is a function that applies either $\mathcal{P}_{\Op{Def}}$ or $\bigcup$ (both at most $\Delta_1$), depending on whether the input is a function defined on a successor ordinal or a limit ordinal (or applies the identity if neither is the case). Fortunately, this case distinction is also $\Delta_0$, and hence we obtain that $G: \alpha \mapsto L_\alpha$ is $\Sigma_1$.

Finally, as in {prf:ref}`thm-definability-Pdef`, observe that if $G$ is a $\Sigma_1$ function with a $\Delta_1$ domain ($\Ord$), then $G$ is actually $\Delta_1$, since we have 

$$
	G(x) \neq y \; \Leftrightarrow \; \exists z (G(x)=z \: \wedge \: y \neq z)
$$

so the complement of the graph of $G$ is $\Sigma_1$-definable, too.
```

```{prf:corollary}
:label: cor-complexity-L

- (**1**) $\quad$   The relations $x = L_\alpha$ and $x \in L_\alpha$ are $\Delta_1$.
- (**2**) $\quad$   The predicate $x \in L$ is $\Sigma_1$.
- (**3**) $\quad$   The axiom $\VL$ is $\Pi_2$.
```

We can relativize the definition of $L$ to other classes $M$. If $M$ is is an inner model, then the development of $L$ can be done *relative to $M$*. Since $M$ is a $\ZF$-model, it has to contain all the sets $L_\alpha^M$ (as we developed definability and proved facts about it *inside* $\ZF$). As $M$ is transitive, the mapping $G: \alpha \to L_\alpha$ is absolute for $M$ and we obtain, for all $\alpha$, 

$$
L_\alpha^M = L_\alpha.
$$

```{prf:theorem}
:label: thm-L-absolute

- (**1**) $\quad$   If $M$ is any transitive proper class model of $\ZF$, then $L = L^M \subseteq  M$.
- (**2**) $\quad$   $L$ is a model of $\ZF + \VL$.
```

```{prf:proof}
(1) follows immediately from the fact that for such $M$, $L_\alpha^M = L_\alpha$.

(2) We have

\begin{align*}
    (\VL)^L & \leftrightarrow \: \forall x\in L \exists y \in L \: (y \text{ is an ordinal } \wedge \; x \in L_y)^L & \\
        & \leftrightarrow \: \forall x\in L \exists \alpha \: (x \in L_\alpha)^L  & \qquad \text{($\Ord \subset L$ and absolute)}\\
        & \leftrightarrow \: \forall x\in L \exists \alpha \: (x \in L_\alpha)    & \qquad \text{(by (1))} 
\end{align*}

The last statement is true since $L = \bigcup_{\alpha} L_\alpha$.
```


## Constructibility and the Axiom of Choice 

Every well-ordering on a transitive set $X$ can be extended to a well-ordering of $\mathcal{P}_{\Op{Def}}(X)$. 

Note that every element of $\mathcal{P}_{\Op{Def}}(X)$ is determined by a pair $(\psi, \vec{a})$, where $\psi$ is a set-theoretic formula, and $\vec{a} = (a_1, \dots, a_n) \in X^{<\omega}$ is a finite sequence of parameters.

For each $z \in \mathcal{P}_{\Op{Def}}(X)$ there may exist more than one such pair (i.e.\ $z$ can have more than one definition), but by well-ordering the pairs $(\psi, \vec{a})$, we can assign each $z \in \mathcal{P}_{\Op{Def}}(X)$ its **least** definition, and subsequently order $\mathcal{P}_{\Op{Def}}(X)$ by comparing least definitions. Elements already in $X$ will form an initial segment. 

Such an order on the pairs $(\psi, \vec{a})$ can be obtained in a **definable way**: First use the order on $X$ to order $X^{<\omega}$ length-lexicographically, order the formulas through their Gödel numbers, and finally put 

$$
	(\psi,\vec{a}) < (\varphi, \vec{b}) \quad \text{ iff } \quad \psi < \varphi \text { or } (\psi < \varphi \text { and } \vec{a} < \vec{b}).
$$

Based on this, we can order all levels of $L$ so that the following hold:

- (**1**) $\quad$   $<_L \Rest{V_\omega}$ is a standard well-ordering of $V_\omega$   (as for example given by a canonical isomorphism $(V_\omega, \in) \leftrightarrow (\Nat, E)$, see {cite}`Ackermann:1937a`)
- (**2**) $\quad$   $<_L\Rest{L_{\alpha+1}}$ is the order on $\mathcal{P}_{\Op{Def}}(L_\alpha)$ induced by $<_L|L_\alpha$.
- (**3**) $\quad$   $<_L\Rest{L_\lambda} = \bigcup_{\alpha < \lambda} <_L \Rest{L_\alpha}$ for a limit ordinal $\lambda > \omega$.

It is straightforward to verify that this is indeed a well-ordering on $L$. Moreover, the relation $<_L$ is $\Delta_1$. (To verify this, we have to spell out all the details of the above definition. This is a little involved, so we skip this here and refer to {cite}`jech2003a`.)

```{prf:theorem}
:label: thm-L-AC

$\VL$ implies $\AC$
```

Since $L$ is a model of $\ZF+\VL$, we obtain

```{prf:corollary}
:label: cor-Con(AC)

If $\ZF$ is consistent, then $\ZF+\AC (= \ZFC)$ is consistent, too.
```


## Condensation and the Continuum Hypothesis

We now show that $\VL$ implies the Continuum Hypothesis. The proof works by showing that under $\VL$, every subset of a cardinal $\kappa$ will be constructed by stage $\kappa^+$. This is made possible by a "**condensation**" argument: If any subset $x$ of $\kappa$ is in $L$, then it must show up at some stage $L_\lambda$. $\kappa$ and $x$ generate an elementary substructure $M$ of $L_\lambda$ or cardinality $\kappa$. If we could show that this **$M$ itself must be an $L_\beta$**, we can use the fact that the cardinality of the $L_\alpha$ behaves "tamely" along the ordinals, as evidenced by the following.

```{prf:proposition}
:label: prop-card-Lalpha

For all $\alpha \geq \omega$, $|L_{\alpha}| = |\alpha|$.
```	

```{prf:proof}
We know that $\alpha \subseteq L_\alpha$. Hence $|\alpha| \leq |L_\alpha|$. To show $|\alpha| \geq |L_\alpha|$, we work by induction on $\alpha$.

If $\alpha = \beta +1$, then by {prf:ref}`prop-basics-L`(4), $|L_\alpha| = |L_\beta| = |\beta| \leq |\alpha|$. 

If $\alpha$ is limit, then $L_\alpha$ is a union of $|\alpha|$ many sets of cardinality $\leq |\alpha|$ (by inductive hypothesis), hence of cardinality $\leq |\alpha|$.
```

But why would an elementary substructure of an $L_\lambda$ have to be itself an $L_\beta$? This is where the absoluteness of the construction of $L$ strikes yet again!

```{prf:lemma} Condensation lemma
:label: lem-condensation

There is a finite set $T$ of axioms of $\ZF - \text{Power Set}$ so that if $M$ is a transitive set with $M\models T + \VL$, then $M = L_\lambda$ for some limit ordinal $\lambda$.
```

```{margin}
If we choose our finite axiom set more carefully, it is actually possible to show something stronger -- namely that there exists a $\Pi_2$-formula $\sigma$ such that for transitive $M$, $M \models \sigma$ **if and only if** $M = L_\lambda$ for some limit $\lambda$, see for example {cite}`Devlin:1984a` (and {cite}`Mathias_2006m` for necessary additions to Devlin's axiom system $BS$).
```

```{prf:proof}
Let the axioms of $T$ be *Pairing*, *Union*, *Set Existence*, together with all (instances of) axioms of $\ZF$ used to prove that all the theorems leading up to the fact that for all $\alpha$, $L_\alpha$  exists and that $\alpha \mapsto L_\alpha$ is $\Delta_1$ (and hence absolute). (We have proved only finitely meany theorems so far so we only needed finitely many axioms!)

Suppose for a transitive set $M$, $M\models T + \VL$. Let $\lambda$ be the least ordinal not in $M$. 
We must have that $\Ord^M = \lambda$, by absoluteness of
ordinal.  Moreover, $\lambda$ must be a limit ordinal since for each $\alpha \in M$, $\alpha \cup \{\alpha\}$ is in $M$ since $M$ satisfies *Pairing* and *Union*.

We have that 

$$
    M\models \forall x \exists \alpha\in \Ord (x \in L_\alpha),
$$ 

thus 

$$
    \forall x \in M  \exists \alpha < \lambda (x \in L^M_\alpha).
$$ 

By absoluteness of $\alpha \mapsto L_\alpha$, we have $L^M_\alpha = L_\alpha$ and therefore 

$$
    M \subseteq \bigcup_{\alpha \in M} L_\alpha =  \bigcup_{\alpha < \lambda} L_\alpha = L_\lambda.
$$

On the other hand, for each $\alpha < \lambda$, $L_\alpha^M$ exists in $M$ (since $T$ is strong enough to prove this), and by absoluteness 

$$
  L_\lambda =  \subseteq \bigcup_{\alpha < \lambda} L_\alpha =  \bigcup_{\alpha \in M} L^M_\alpha \subseteq M.
$$
```

We now put condensation to use as described above.


```{prf:lemma} 
:label: lemma-L-GCH

Suppose $V=L$. If $\kappa$ is a cardinal and $x \subseteq \kappa$, then $x \in L_{\kappa^+}$.
```

```{prf:proof} 
Since we assume $\VL$, there exists limit $\lambda > \kappa$ such that $x \in L_\lambda$ and such that $L_\lambda \models T + \VL$, where $T$ is as in the **condensation lemma**. Such a $\lambda$ exists by the **reflection theorem** ({prf:ref}`thm-reflection`).  Let $X = \kappa \cup \{x\}$. By choice of $\lambda$, $X \subseteq L_\lambda$. 

    By the [Löwenheim-Skolem Theorem](https://en.wikipedia.org/wiki/L%C3%B6wenheim%E2%80%93Skolem_theorem), there exists an **elementary substructure** $N \preceq L_\lambda$ such that

    \begin{equation*} \tag{$*$}
        X \subseteq N \subseteq L_\lambda \quad \text{ and } \quad |N| = |X|.
    \end{equation*}

$N$ is not necessarily transitive, but since it is well-founded we can take its **Mostowski collapse** ({prf:ref}`thm-Mostowski-collapse`) and obtain a **transitive** set $M$
together with an **isomorphism** $\pi: (N,\in) \to (M,\in)$. 

Since $\kappa$ is contained in both $M$ and $N$, and is already transitive, it is straightforward to show via induction that $\pi(\alpha) = \alpha$ for all $\alpha \in \kappa$. Since $x \subseteq \kappa$, this also yields $\pi(x) = x$. This implies in turn that $x \in M$.

As $(M,\in)$ is isomorphic to $(N,\in)$ and $N \preceq L_\lambda$, $M$ satisfies the same sentences as $(L_\lambda, \in)$. In particular, $M \models T + \VL$. By the **condensation lemma**, $M = L_\beta$ for some $\beta$. 

This implies, by {prf:ref}`prop-card-Lalpha`,

$$  
    |\beta| = |L_\beta| = |M| = |N| = |X| = \kappa < \kappa^+ \leq \lambda.
$$

Since $x \in L_\beta$ and $\beta < \kappa^+$, it follows that $x \in L_{\kappa^+}$, as desired.
```

 
```{prf:theorem} Gödel
:label: thm-L-GCH

If $\VL$, then for all cardinals $\kappa$, $2^\kappa = \kappa^+$.
```

```{prf:proof}
If $\VL$, then by {prf:ref}`lemma-L-GCH`, $\mathcal{P}(\kappa) \subseteq L_{\kappa^+}$. With {prf:ref}`prop-card-Lalpha`, we obtain

$$
    2^\kappa = |\mathcal{P}(\kappa)| \leq |L_{\kappa^+}| = \kappa^+.
$$
```

```{prf:corollary} 
:label: cor-Con(ZFC+GCH)

If $\ZF$ is consistent, so is $\ZF + \AC + \mathsf{GCH}$.
```

