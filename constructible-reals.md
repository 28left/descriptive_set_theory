# Constructible Reals
```{math}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\Baire}{\Nat^{\Nat}}
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
\newcommand{\bPi}{\pmb{\Pi}}
\newcommand{\bSigma}{\pmb{\Sigma}}
\DeclareMathOperator{\W}{W}
\DeclareMathOperator{\WF}{WF}
\DeclareMathOperator{\WOrd}{WOrd}
\newcommand{\Norm}[1]{\parallel \! #1 \!\parallel}
```

In this lecture we transfer the results about $L$ to the projective hierarchy. The main idea is to relate sets of reals that are defined by set theoretic formulas to sets defined in second order arithmetic.



## The set of constructible reals

What is the complexity of the set $\Baire \cap L$? In particular, is it in the projective hierarchy?
The set of all constructible reals is defined by a $\Sigma_1$ formula over set theory:

$$
   \varphi(x_0)	\; \equiv \; \exists y \; [y \text{ is an ordinal }  \; \wedge \; x_0 \in L_y \; \wedge \; x_0 \text{ is a set of natural numbers }  ].
$$

We would like to replace this formula by an "equivalent" one in the language of second order arithmetic. In particular, we would like to replace the quantifier $\exists y$ by a quantifier over the reals.

The key for doing this is {prf:ref}`lemma-L-GCH`: every constructible real shows up at a countable stage of $L$. Hence if $\alpha \in L \cap \Baire$, there exists a countable $\xi$ such that $x \in L_\xi$. Since $|\xi| = |L_\xi|$, $L_\xi$ is countable, too. Hence we can hope to replace $L_\xi$ by something like "*there exists a real that codes a model that looks like $L_\xi$*". 

The **condensation lemma** ({prf:ref}`lem-condensation`) allows us to do this. 
Let $\varphi_{\VL}$ be the conjunction of the axioms in $T$ and the axiom $\VL$. 

Recall that any real $\alpha \in \Baire$ codes a set theoretic structure
\begin{equation*}
	(\omega, E_\alpha) \qquad \text{ where } E_\alpha = \{ \Tup{m,n} \colon \alpha(\Tup{m,n}) =  0 \}.
\end{equation*}

Unfortunately, the condensation lemma only holds for **transitive sets** (and $(\omega, E_\alpha)$ may look very different from a transitive set model), so simply requiring $(\omega,E_\beta) \models \varphi_{\VL}$ is not enough. But we know from {prf:ref}`thm-Mostowski-collapse` (**Mostowski collapse**) that if $E_\beta$ is well-founded and extensional, we can map it isomorphically to a transitive set $S$ on which we interpret $E_\beta$ as $\in$. By the condensation lemma, this $S$ must then be an $L_\xi$.

So, for reals, we can formulate membership in $L$ now as follows:

\begin{multline*} \tag{$*$}
	\alpha \in L \cap \Baire \iff \exists \beta \exists m \: [E_\beta \text{ is  extensional and well-founded} \\ \: \wedge \: (\omega,E_\beta) \models \varphi_{\VL} \: \wedge \: \pi_\beta(m) = \alpha ],
\end{multline*}
where $\pi_\beta$ is the Isomorphism of the Mostowski collapse of $E_\beta$.



It remains to show that the notions occurring inside the square brackets are definable in second order arithmetic.

```{prf:proposition}
:label: prop-satisfaction-arithmetic

- (**a**) $\quad$  For any $n \in \Nat$, the following set is $\Sigma^0_n$:
\begin{equation*}
    \{(m,\sigma,\gamma) \in \Nat\times \Nstr\times \Baire \colon m = \GN{\varphi} \: \wedge \: \varphi \text{ is $\Sigma_n$} \: \wedge \: (\omega,E_\gamma) \models \varphi[\sigma] \}
\end{equation*}

- (**b**) $\quad$  If $\alpha \in \Baire$ and $E_\alpha$ is well-founded and extensional, then the following set is arithmetic in $\alpha$:
\begin{equation*}
	\{ (m,\gamma) \in \Nat\times \Baire \colon \pi_\alpha(m) = \gamma\}
\end{equation*}
```

```{prf:proof}
:class: dropdown
:nonumber: true

(a) can be established similar to showing that $\Op{Sat}$-predicate of {prf:ref}`thm-sat-predicate` is $\Delta_1$-definable. One does this first for $\Sigma_1$ formulas and then uses induction. Using Gödelization, one carefully defines all syntactical notions using arithmetic formulas. Then, one uses the recursive definition of truth to establish the definability of the satisfaction relation. 

Since we work with relations over $\Nat$ now instead of arbitrary sets, it is not that easy anymore to keep quantifiers bounded. But since we are only interested in the complexity of $\models$ for $\Sigma_n$-formulas, this helps us bound the overall complexity at $\Sigma^0_n$

(c) By analyzing the recursive definition and using the definition of $\Nat$ in $\ZF$, one first shows that the set

$$
    \{ (m,p) \in \Nat\times \Nat  \colon \pi_\alpha(m) = p \}
$$
 
is arithmetic in $\alpha$. 

Let $\psi(v_0, v_1, v_2)$ be the formula $\Tup{v_0, v_1} \in v_2$. Then 

\begin{multline*}
    \pi_\alpha(m) = \gamma \iff \\ 
    \forall p, q \: \left (\gamma(p) = q \: \leftrightarrow \: \exists i,j \: (\pi_\alpha(i) = p \wedge \pi_\alpha(j)=q \wedge (\omega,E_\alpha) \models \psi[i,j,m]) \right )
\end{multline*}

Now apply the previous observation and (a).
```

Finally, note that

$$
	\text{$E_\beta$ is extensional} \iff \forall m,n \: [\forall k (k E_\beta m \; \leftrightarrow \; k E_\beta n) \; \to \; m=n ].
$$

Hence this is arithmetical. And we have already seen that coding a well-founded relation over $\Nat$ is $\Pi^1_1$.


Now we know the complexity of all parts of ($*$) and can put everything together.

```{prf:theorem}	
:label: thm-L-reals

The set $L \cap \Baire$ is $\Sigma^1_2$.
```

In a similar way we can show that the relation $\alpha <_L \beta$ over $(L\cap\Baire)^2$ is $\Sigma^1_2$ (using that $<_L$ is $\Delta_1$-definable). 

```{admonition} Exercise	
:class: tip

Recall that given $\alpha \in \Baire, n \in \Nat$, $(\alpha)_n$ denotes the $n$-th column of $\alpha$.

Show that the following relation $R$ over $(L\cap\Baire)^2$ is $\Sigma^1_2$.

$$
(\alpha, \beta) \in R :\iff \{(\alpha)_n\colon n \in \Nat \} = \{\gamma \colon \gamma <_L \beta \}
$$

In other words, $\alpha$ codes the (countable) $<_L$-initial segment restricted to $\Baire$.
```

If $\VL$, then the set is actually $\Delta^1_2$, since then 

$$
	\alpha <_L \beta \iff \alpha \neq \beta \: \wedge \: \neg(\beta <_L \alpha).
$$

Finally, since $\VL$ implies $\CH$, we can use {prf:ref}`prop-non-meas` to show the existence of non-measurable sets under $\VL$.

```{prf:corollary}	
:label: cor-L-reals

If $\VL$, then there exists a $\Delta^1_2$ set that is not Lebesgue-measurable and does not have the Baire property.
```


## An uncountable $\Pi^1_1$ set without a perfect subset

We now show that under the assumption $\VL$, the **perfect set property** fails at level $\Pi^1_1$.

We start with constructing an example at the $\Sigma^1_2$ level.

[Recall](sec-well-founded) that if $\alpha \in \Baire$ codes a well-ordering on $\Nat$, then
\begin{equation*}
	\Norm{\alpha} = \text{ order type of well-ordering coded by $\alpha$}.
\end{equation*}



```{prf:proposition}
:label: prop-sigma12-perfect

If $\VL$, there exists an uncountable $\Sigma^1_2$ set in $\Baire$ without a perfect subset.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $A \subseteq \Baire$ be given by
\begin{equation*}
    x \in A \iff x \in \WOrd \, \wedge \, \forall y <_L x \,  ( \parallel y \parallel \ne \parallel x \parallel).
\end{equation*}

In other words, $A$ collects the $<_L$-least code for every ordinal $< \omega_1$.

Clearly $A$ is uncountable, since it has a representative for every countable ordinal and hence of cardinality $\omega_1$.

Moreover, $A$ is $\Sigma^1_2$: Let $R$ be the $\Sigma^1_2$-relation of the exercise above. Then
\begin{equation*}
x \in A \iff x \in \WOrd \, \wedge \, \exists z \;(R(z,x) \, \wedge \; \forall n \,  ( \Norm {(z)_n} \neq \Norm{x}).
\end{equation*}

The relation $\Norm{(z)_n} \neq  \Norm{x}$ $\Pi^1_1$, hence $A$ is $\Sigma^1_2$.

Finally, we see that **$A$ does not have an uncountable $\bSigma^1_1$ subset** (hence, since all perfect sets are closed, no perfect subset): By $\bSigma^1_1$-boundedness ({prf:ref}`thm-sigma11-bounding`), for any $\bSigma^1_1$ subset $X \subseteq A$ the set $\{ \Norm{x} \colon x \in X\}$ bounded by an ordinal $\gamma < \omega_1$, hence countable.
```

It is possible to get this example down to $\Pi^1_1$ using the powerful technique of **uniformization**. 

```{prf:definition}
:label: def-uniformization

Suppose $A \subseteq \Baire \times \Baire$. We say $A^* \subseteq A$ **uniformizes** $A$ if 

$$
\forall x  \; [ \exists y \; A(x,y) \to  \exists ! y \; A^*(x,y)]
$$

A pointclass $\Gamma$ has the **uniformization property** if 
\begin{equation*}
A \subseteq \Baire  \times \Baire \, \wedge \, A \in \Gamma \quad \Rightarrow \quad \exists A^* \in  \Gamma \; (A^*  \text{ uniformizes } A).
\end{equation*}
```

```{prf:theorem} Kondo
:label: thm-Kondo

$\bPi^1_1$ has the uniformization property.
```

```{prf:theorem} 
:label: thm-prefect-set-L

If $\VL$, then there exists an uncountable $\bPi^1_1$ set without a perfect subset.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $A$ be the $\Sigma^1_2$ set from the proof of {prf:ref}`prop-sigma12-perfect`. $A \subseteq \Baire$ is the projection of a $\Pi^1_1$ set $B \subseteq \Baire \times \Baire$. If we apply uniformization to $B$, we obtain a uniformizing set $B^*$ whose projection is still $A$. 

$B^*$ is uncountable, but does not contain a perfect subset: If $P \subset B^*$ were such a subset, then $P$ would be (the graph of) a function and uncountable, and the projection $\exists^{\Baire} \; P$ would be an uncountable  $\bSigma^1_1$ subset of $A$, contradiction.
```
