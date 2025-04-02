# The Constructible Universe


A set $X$ is **(first-order) definable** in a set $Y$ (from parameters) if there exists a first-order formula $\varphi(x_0, x_1, \dots, x_n)$ in the language of set theory (i.e. only using the binary relation symbol $\in$) such that for some $a_1, \dots, a_n \in Y$,

$$
	X = \{ y \in Y \colon (Y,\in) \models \varphi[y, a_1, \dots, a_n] \}.
$$ 

The constructible universe is built as a cumulative hierarchy of sets along the ordinals. In each successor step, instead of adding all subsets of the current set, only the **definable** ones are added. Formally, $L$ is defined as follows. Given a set $Y$, let 

$$
	\mathcal{P}_{\Op{Def}}(Y) = \{X \subseteq Y \colon X \text{ is definable in $Y$ from parameters}\},
$$

where the underlying language is the language of set theory. Now put
\begin{align*}
	L_0 & = \emptyset \\
	L_{\alpha+1} & = \mathcal{P}_{\Op{Def}}(L_\alpha)  \\
	L_{\lambda} & = \bigcup_{\alpha < \lambda} L_\alpha \quad  \text{($\lambda$ limit ordinal)} \\
\end{align*}
Finally, let

$$
	L = \bigcup_{\alpha \in\Ord} L_\alpha.
$$



## Basic properties of $L$

The first Proposition tells us that the $L_\xi$ are set-theoretically nice structures and linearly ordered by the $\subseteq$-relation.

```{prf:proposition}
:label: prop-basics-L

For each ordinal ${}\xi$:

- **(1)** $L_\xi$ is transitive.
- **(2)** For $\alpha < \xi$, $L_\alpha \subseteq L_\xi$.
- **(3)** For $\alpha < \xi$, $L_\alpha \in L_\xi$.	
- **(4)** If $\xi \geq \omega$, then $|L_{\xi+1}| = |L_\xi|$. 
```

```{prf:proof}
:class: dropdown
:nonumber: true

We show the first two statements statements simultaneously by induction. 

They are clear for $\xi = 0$ and ${}\xi$ limit, so assume $\xi = \alpha +1$.  

Suppose $x \in L_\alpha$. Consider the formula $\varphi(x_0) \equiv x_0 \in x$ (here $x$ is a parameter). ${}\varphi$ defines the set

$$
    x' = \{a \in L_\alpha \colon L_\alpha \models \varphi[a] \} = \{ a \in L_\alpha \colon a \in x \}.  
$$

By induction hypothesis, $L_\alpha$ is transitive, and hence $a \in x$ implies $a \in L_\alpha$, and hence $x' = x$, so $x \in L_{\alpha+1}$. This yields $L_\alpha \subseteq L_\xi$. Now if $x \in L_\xi$, then $x \subseteq L_\alpha$, and hence $x \subseteq L_\xi$. Thus $L_\xi$ is transitive.

For the third statement, note that the formula $\varphi(x_0) \equiv x_0 = x_0$ defines $L_\alpha$ in $L_\alpha$, and hence $L_\alpha \in L_{\alpha + 1}$.

For (4), notice that there are only countably many formulas.
```

Next, we show that $L$ contains all ordinals and that ${}\xi$ "shows up" exactly after ${}\xi$ steps.

```{prf:proposition}
For any ${}\xi$, 

- **(1)** $\xi \subseteq L_\xi$,
- **(2)** $L_\xi \cap \Ord = \xi$.
```

```{prf:proof}
:class: dropdown

Clearly, $(1)$ follows from $(2)$. 

To show $(2)$, one again proceeds by induction. Again, the statement is clear for ${}0$ and limit ordinals, so assume $\xi = \alpha +1$ and $L_\alpha \cap \Ord = \alpha$. 

We need to show $L_{\alpha + 1} \cap \Ord = \alpha + 1 = \alpha \cup \{\alpha\}$. Since $L_\alpha \subseteq L_{\alpha + 1}$, we have $\alpha \subseteq L_{\alpha+1} \cap \Ord$. On the other hand, since $L_{\alpha+1} \subseteq \mathcal{P}(L_\alpha)$, we have $L_{\alpha+1} \cap \Ord \subseteq \alpha + 1$. It thus remains to show that $\alpha \in L_{\alpha+1}$. 

We observed before that the statement

>	$\varphi_{\Ord}(x)$: *$x$ is transitive and linearly ordered by $\in$*

can be formalized by a $\Delta_0$ formula, which are absolute for transitive classes.

Thus,
\begin{equation*}
	\alpha = \{ a \in L_\alpha \colon L_\alpha \models \varphi_{\Ord}[a] \},
\end{equation*} 
and hence we can conclude $\alpha \in L_{\alpha+1}$. 
```




## Defining definability

We want to study $L$ as a model of $\ZF$. In order to do that, we need a better understanding of $\mathcal{P}_{\Op{Def}}$. Our definition, so far, is "from the outside" (i.e. in the meta-theory). This will make it hard to understand how formulas behave relative to $L$, in particular, whether we can apply any of the absoluteness results we obtained. We will therefore have to develop (or at least, convince ourselves how we can develop) definability  **inside** $\ZF$. We can then combine this with some powerful results about **cumulative hierarchies** (such as $V$ and $L$) to prove that $L$ is a model not only of $\ZF$, but also of $\CH$ and $\AC$. 

### Coding set theoretic formulas

We follow the standard procedure of **Gödelization** and assign every set theoretic formula ${}\varphi$ a **Gödel number** $\GN{\varphi}$.

We fix the set of variables as $\{v_n: n \in \omega\}$ and put

$$
\GN{v_n} = (1,n).
$$

It will be helpful to extend the language by adding, for each set $x$, a formal constant, which we will denote by $\Const{x}$. We code this constant by

$$
\GN{\Const{x}} = (2,x)
$$

This allows us, for a given structure $(a,\in)$, to express statements about the elements of $a$ by formulas using the corresponding constants $\Const{x}$ for $x \in a$. If $\Const{x} \in a$ is interpreted in $(a,\in)$ by itself, we call this the **canonical interpretation**.

The Gödelization of formulas now follows the usual, recursion pattern:

\begin{align*}
\GN{x=y} & = (3, (\GN{x}, \GN{y})) \\
\GN{x\in y} & = (4, (\GN{x}, \GN{y})) \\
\GN{\neg \varphi} & = (5, \GN{\varphi}) \\
\GN{\varphi \vee \psi} & = (6, (\GN{\varphi}, \GN{\psi})) \\
\GN{\exists v_n \varphi} & = (7, (n, \GN{\varphi})) \\
\end{align*}

### Definability of syntactic notions

We can now express various syntactic statements about formulas, such as "$v$ is a variable", as a set theoretic formula via the corresponding codes:

$$
\Op{Vbl}(a) \; :\Leftrightarrow \; \exists y \in a \exists x \in y \: (a = (1,x) \wedge x \in \omega)
$$

where of course we substitute a suitable $\Delta_0$ formula for "$x \in \omega$".

```{prf:proposition}
:label: prop-defble-formula

The following relations are $\Delta_1$-definable over $\ZF$. 

> $\Op{Fml}^n(e): \quad$ $e$ is the code of a formula ${}\varphi$ whose free variables are among $v_0, \dots, v_{n-1}$;   
> $\Op{Fml}^n_a(e): \quad$ $e$ is the code of a formula ${}\varphi$ whose free variables are among $v_0, \dots, v_{n-1}$, and whose constants are of the form $\Const{a_i}$ with $a_i \in a$
```

### Definability of the satisfaction relation

Let $a$ be a set. If we replace a formula ${}\varphi$ by its code $\GN{\varphi}$, we have to express the fact that $\varphi^a$ holds now as a statement about validity in the structure $(a,\in)$, using the code. That is, we have to **formalize** the notion of truth. This can be done using the recursive definition of truth. 
This way we obtain a $\Delta_1$-definable predicate $\Op{Sat}(a,e)$ expressing 

> $\Op{Sat}(a,e): \quad$ $e$ is the code of a formula $\varphi(\Const{a_0}, \dots, \Const{a_n})$ that does not contain any free variables, and ${}\varphi$ is true in $(a,\in)$ under the canonical interpretation.

In place of  $\Op{Sat}(a,e)$, we will also write $(a,\in) \models e$. For any single formula, this formalization of truth then agrees with the validity of the corresponding relativization:

```{prf:theorem}
:label: thm-sat-predicate

Let $\varphi(v_0, \dots, v_{n-1})$ be a set theoretic formula, and assume $a_0, \dots, a_{n-1} \in a$. Then it is provable in ZF that

$$
	\varphi^a(a_0, \dots, a_{n-1}) \; \leftrightarrow \; \Op{Sat}(a,\GN{\varphi(\Const{a_0}, \dots, \Const{a_{n-1}})}).
$$
```

(Keep in mind, however, that the general satisfaction relation, over all formulas, is not formalizable in $\ZF$.)

The Theorem is proved via induction over the structure of ${}\varphi$. For atomic ${}\varphi$, both sides express the same fact, since we use the canonical interpretation of constants. The definition of relativization ensures that for the inductive cases, both sides behave identically wit respect to the corresponding subformulas.

### Definability of definability 

We can now formalize the notion of definability we used informally above in the definition of $L$:

> $\mathcal{P}_{\Op{Def}}(a) = \{ x \subseteq a \colon \exists e \: (\Op{Fml}^1_a(e) \: \wedge \: x = \{z \in a\colon (a,\in) \models e(z)\})\}$

Here, $e(z)$ is defined so that for a formula $\varphi(v_0)$ with code $e$,

> $e(z)$ is the code of the formula we obtain when we substitute $\Const{z}$ for $v_0$ in ${}\varphi$: 
\begin{equation*}
	\GN{\varphi(v_0)}(z) = \GN{\varphi(\Const{z})}
\end{equation*}

With little effort, one can read off the complexity of the mapping $a \mapsto \mathcal{P}_{\Op{Def}}(a)$.

```{prf:theorem}
:label: thm-definability-Pdef

The relation $b = \mathcal{P}_{\Op{Def}}(a)$ is $\Delta_1$-definable.
```

```{prf:proof}
:class: dropdown
:nonumber: true

(*Sketch*) Taking into account the complexity of the various sub-formulas, we see that the mapping $a \mapsto \mathcal{P}_{\Op{Def}}(a)$ is $\Sigma_1$-definable.

The graph of a $\Sigma_1$-definable function $f$ (with domain $\V$) is $\Delta_1$, since the complement is given as

$$
	f(x) \neq y \; \Leftrightarrow \; \exists z (f(x)=z \: \wedge \: y \neq z).
$$

Thus,  $b = \mathcal{P}_{\Op{Def}}(a)$ is $\Delta_1$.
```

This *complexity bound is of central importance* to the applications of $L$, and we will return to it soon ({prf:ref}`prop-map-Lalpha`).


## Cumulative hierarchies

Many facts about $L$ hold more generally for **cumulative hierarchies**.

```{prf:definition}
:label: def-cumulative

A sequence $(M_\alpha)_{\alpha \in \Ord}$ of sets is a **cumulative hierarchy** if

- (**H1**) $\quad$ each $M_\alpha$ is transitive,
- (**H2**) $\quad$ $\alpha < \beta$ implies $M_\alpha \subseteq M_\beta$,
- (**H3**) $\quad$ For limit $\lambda$, 
\begin{equation*}
	M_\lambda = \bigcup_{\alpha < \lambda} M_\alpha
\end{equation*}
```

The von-Neumann universe $V$ ($M_\alpha = V_\alpha$) and Gödel's $L$ ($M_\alpha = L_\alpha$) are the most important examples of cumulative hierarchies.

```{prf:definition}
:label: def-normal-function

A function $F: \Ord \to \Ord$ is **normal** if

\begin{gather*}
\alpha < \beta \; \Rightarrow \; F(\alpha) < F(\beta) \qquad \text{(strictly increasing)} \\
\lambda \text{ limit } \Rightarrow F(\lambda) = \bigcup_{\alpha < \lambda} F(\alpha) \qquad \text{(continuous)}
\end{gather*}
```

The images of normal functions are called **clubs** (short for **closed, unbounded**).

```{admonition} Exercise
:class: tip

Show that a normal function has arbitrarily large fixed points, that is,

$$
\forall \alpha \exists \beta \; (\beta > \alpha \: \wedge \: \beta = F(\beta))
$$
```

```{prf:theorem} Reflection for cumulative hierarchies
:label: thm-reflection

Let $(M_\alpha)_{\alpha \in \Ord}$ be a cumulative hierarchy and let $M = \bigcup_\alpha M_\alpha$.

For every set theoretic formula $\varphi(v_0, \dots, v_{n-1})$ there exists a normal function $F$ such that 

$$
	F(\alpha) = \alpha \; \; \rightarrow \;\;  \forall a_0, \dots, a_{n-1} \in M_\alpha \: (\varphi^{M_\alpha}(\vec{a}) \leftrightarrow \varphi^{M}(\vec{a}))
$$
```

```{prf:proof}
:class: dropdown
:nonumber: true

Proceed by induction on the formula structure. We focus on the case $\varphi \equiv \exists y \psi$. The other cases are straightforward due to the definition of relativization.

By induction hypothesis, there exists a normal function $G$ such that

$$
G(\alpha) = \alpha \; \; \rightarrow \;\;  \forall \vec{a},b \in M_\alpha \: (\psi^{M_\alpha}(\vec{a},b) \leftrightarrow \psi^{M}(\vec{a},b))
$$

We define a function $H$ by

$$
H(\alpha) = \text{ least } \beta > \alpha \text{ with } \forall \vec{a} \in M_\alpha \: ( \exists b \in M \: \psi^M(\vec{a},b) \; \rightarrow \; \exists b \in M_\beta \: \psi^M(\vec{a},b))
$$

We use $H$ to define, via transfinite recursion, another normal function $F$:
\begin{align*}
	F(0) & = 0 \\
	F(\alpha+1) & = H(F(\alpha)) \\
	F(\lambda) & = \bigcup_{\alpha < \lambda} F(\alpha) \quad \text{ for $\lambda$ limit}
\end{align*}

The composition $F^* = F\circ G$ is again normal, and its fixed points are simultaneously fixed points of $F$ and $G$. It is now straightforward to check  that $F^*$ has the desired property.
```

```{prf:corollary} Scott-Scarpellini Theorem
:label: cor-Scott-Scarpellini

If $(M_\alpha)_{\alpha \in \Ord}$ is a cumulative hierarchy, $M = \bigcup_\alpha M_\alpha$, and $\varphi(\vec{x})$ is a set-theoretic formula, then

$$
\forall \alpha \exists \beta > \alpha \; \forall a_0, \dots, a_{n-1} \in M_\beta \: (\varphi^{M_\beta}(\vec{a}) \leftrightarrow \varphi^{M}(\vec{a}))
$$
```

By taking conjunctions, it is possible to generalize the reflection theorem to **finite sets of formulas**. Again, it is not possible (unless $\ZF$ is inconsistent) to extend this to arbitrary sets of formulas (or we could produce, in $\ZF$, a *set model* of $\ZF$, contradicting the *second incompleteness theorem*).

```{prf:corollary}
:label: cor-ZF-axiomatizable

$\ZF$ is not finitely axiomatizable.
```



## Inner models

```{prf:definition}
:label: def-inner-model

A class $M$ is an **inner model of $\ZF$** if 

- $M$ is transitive,
- $M$ contains all ordinals,
- $\sigma^M$ holds for all axioms $\sigma$ of $\ZF$.
```

```{prf:theorem} Characterization of inner models
:label: thm-inner-models

A class $M$ is an inner model of $\ZF$ if and only if there exists a sequence $(M_\alpha)_{\alpha \in \Ord}$ such that for all $\alpha, \beta, \lambda \in \Ord$,

- (**I1**) $\quad$ $M = \bigcup_{\alpha \in \Ord} M_\alpha$ is a cumulative hierarchy,
- (**I2**) $\quad$ $\mathcal{P}_{\Op{Def}}(M_\alpha) \subseteq M_{\alpha+1} \subseteq \mathcal{P}(M_\alpha)$
```

```{prf:proof}
:class: dropdown
:nonumber: true

($\Rightarrow$) Suppose $M$ is an inner model of $\ZF$. Let 

$$
M_\alpha = V_\alpha^M = V_\alpha \cap M.
$$

This defines a cumulative hierarchy, so (I1) is satisfied.
For (I2), first note that $(\text{Power Set})^M$ if and only if $\forall x \in M (\mathcal{P}(x) \cap M \in M)$. Now we can use the absoluteness of $\mathcal{P}_{\Op{Def}}$ ({prf:ref}`thm-definability-Pdef`) and the fact that $M$ satisfies the axiom of *Separation* to conclude $\mathcal{P}_{\Op{Def}}(M_\alpha) \subseteq M_{\alpha+1}$.

($\Leftarrow$) 
*Extensionality* and *Foundation* hold in all transitive classes. *Set Existence* is satisfied in any cumulative hierarchy (since $\emptyset \in M$).

*Union*: By absoluteness, $(\text{Union})^M$ if and only if $\forall x \in M \; \bigcup x \in M$. The latter holds in $M$ by (I2) and the fact that $y = \bigcup x$ is definable.

*Pairing*: Similar to *Union*.

*Separation*: Suppose $a, b_1, \dots, b_n \in M$ and $\varphi(v_0, v_1, \dots, v_n)$ is a formula. We have to argue that the set 
\begin{equation*}
	z = \{ x \in a \colon \varphi^M(x, b_1, \dots, b_n) \}
\end{equation*}
is in $M$. By the reflection theorem for cumulative hierarchies, there exists $\alpha$ such that $a, b_1, \dots, b_n \in M_\alpha$ and for all $x \in M_\alpha$,
\begin{equation*}
	\varphi^M(x, b_1, \dots, b_n) \; \leftrightarrow \; \varphi^{M_\alpha}(x, b_1, \dots, b_n).
\end{equation*}
This implies $z \in \mathcal{P}_{\Op{Def}}(M_\alpha)$ and hence by (I2), $z \in M_{\alpha+1}$. By (I1), $z \in M$.

*Power Set*: Suppose $a \in M$, say $a \in M_\alpha$. The set $z = \mathcal{P}(a)\cap M$ has a $\Delta_0$-definition over $M_\alpha$: the formula "$x \subseteq a$". Therefore, by (I2), $z \in M_{\alpha+1}$ and hence $z \in M$. $z$ is the power set of $a$ relative to $M$ since, by absoluteness of $\subseteq$,
\begin{equation*}
	(z = \mathcal{P}(a))^M \: \iff \: \forall x \in M (x \in z \iff x \subseteq a) \: \iff \: z = \mathcal{P}(a) \cap M
\end{equation*}

*Replacement*: Assume a function $F$ on $M$ is defined by a formula $\varphi(x,y,\vec{a})$ ($\vec{a} \in M$ being parameters), that is
\begin{equation*}
	\forall x,y \in M \; (\varphi^M(x,y,\vec{a}) \wedge \varphi^M(x,z,\vec{a}) \; \to \; y=z )
\end{equation*}
Let $b $ be a set. By reflection, there exists an $\alpha$ such that $\vec{a}, b \in M_\alpha$ and the following two formulas hold:
\begin{gather*}
	\forall x,y, z \in M_\alpha \: (\varphi^M(x,y,\vec{a})) \leftrightarrow \: \varphi^{M_\alpha}(x,y,\vec{a})) \\
	\forall x \in M_\alpha \: (\exists y\in M \varphi^M(x,y,\vec{a}) \: \leftrightarrow \: \exists y \in M_\alpha \varphi^{M_\alpha}(x,y,\vec{a}))
\end{gather*}
Since $b \subseteq M_{\alpha}$ (transitivity), this implies
\begin{equation*}
	\forall x \in b \: (\exists y\in M \varphi^M(x,y,\vec{a}) \: \leftrightarrow \: \exists y \in M_\alpha \varphi^M(x,y,\vec{a}))
\end{equation*}
and therefore
\begin{equation*}
	\{ y : \exists x \in b \, \varphi^{M}(x,y,\vec{a}) \} = \{ y : \exists x \in b \, \varphi^{M_\alpha}(x,y,\vec{a}) \}
\end{equation*}
The left side defines the image of $F$ in $M$, which, by the right side, is in $\mathcal{P}_{\Op{Def}}(M_\alpha)$, and thus, by (I2), in $M_{\alpha+1}$.

*Infinity*: "$x = \omega$" is $\Delta_0$, and since by (I2), $L_\omega \subseteq M_\omega$, we have that $\omega \in M_{\omega+1}$ and that this witnesses the axiom of *Infinity*.
```

We see that $V$ and $L$ lie at the extreme ends of the spectrum of inner models.

```{prf:corollary}
:label: cor-L-inner-model

$L$ is an inner model of $\ZF$.
```




