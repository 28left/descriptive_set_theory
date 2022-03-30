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

In our case, $G$ is a function that applies either $\mathcal{P}_{\Op{Def}}$ or $\bigcup$ (both at most $\Delta_1$), depending on whether the input is a function defined on a successor ordinal or a limit ordinal (or applies the identity if neither is the case). Fortunately, this case distinction is also $\Delta_0$, and hence we obtain that $G: $\alpha \mapsto L_\alpha$ is $\Sigma_1$.

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

- (**1**) $\quad$   If $M$ is any transitive proper class model of $\ZF$, then $L = L^M \s M$.
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

For each $z \in \mathcal{P}_{\Op{Def}}(X)$ there may exist more than one such pair (i.e.\ $z$ can have more than one definition), but by well-ordering the pairs $(\psi, \vec{a})$, we can assign each $z \in \mathcal{P}_{\Op{Def}}(X)$ its \emph{least} definition, and subsequently order $\mathcal{P}_{\Op{Def}}(X)$ by comparing least definitions. Elements already in $X$ will form an initial segment. 

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



