# The Constructible Universe
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
\newcommand{\GN}[1]{\ulcorner #1 \urcorner}
\newcommand{\Const}[1]{\underline{#1}}
\newcommand{\V}{\mathbf{V}}
\newcommand{\Ord}{\mathbf{Ord}}
\DeclareMathOperator{\W}{W}
\DeclareMathOperator{\WF}{WF}
\DeclareMathOperator{\WOrd}{WOrd}

```


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
	L_{\xi+1} & = \mathcal{P}_{\Op{Def}}(L_\xi)  \\
	L_{\xi} & = \bigcup_{\alpha < \xi} L_\xi \quad  \text{($\xi$ limit ordinal)} \\
\end{align*}
Finally, let

$$
	L = \bigcup_{\xi \in\Ord} L_\xi.
$$



## Basic properties of $L$

The first Proposition tells us that the $L_\xi$ are set-theoretically nice structures and linearly ordered by the $\subseteq$-relation.

```{prf:proposition}
:label: prop-basics-L

For each ordinal $\xi$:

- **(1)** $L_\xi$ is transitive.
- **(2)** For $\alpha < \xi$, $L_\alpha \subseteq L_\xi$.
- **(3)** For $\alpha < \xi$, $L_\alpha \in L_\xi$.	
- **(4)** If $\xi \geq \omega$, then $|L_{\xi+1}| = |L_\xi|$. 
```

```{prf:proof}
We show the first two statements statements simultaneously by induction. 

They are clear for $\xi = 0$ and $\xi$ limit, so assume $\xi = \alpha +1$.  

Suppose $x \in L_\alpha$. Consider the formula $\varphi(x_0) \equiv x_0 \in x$ (here $x$ is a parameter). $\varphi$ defines the set

$$
    x' = \{a \in L_\alpha \colon L_\alpha \models \varphi[a] \} = \{ a \in L_\alpha \colon a \in x \}.  
$$

By induction hypothesis, $L_\alpha$ is transitive, and hence $a \in x$ implies $a \in L_\alpha$, and hence $x' = x$, so $x \in L_{\alpha+1}$. This yields $L_\alpha \subseteq L_\xi$. Now if $x \in L_\xi$, then $x \subseteq L_\alpha$, and hence $x \subseteq L_\xi$. Thus $L_\xi$ is transitive.

For the third statement, note that the formula $\varphi(x_0) \equiv x_0 = x_0$ defines $L_\alpha$ in $L_\alpha$, and hence $L_\alpha \in L_{\alpha + 1}$.

For (4), notice that there are only countably many formulas.
```

Next, we show that $L$ contains all ordinals and that $\xi$ "shows up" exactly after $\xi$ steps.

```{prf:proposition}
For any $\xi$, 

- **(1)** $\xi \subseteq L_\xi$,
- **(2)** $L_\xi \cap \Ord = \xi$.
```

```{prf:proof}
Clearly, $(1)$ follows from $(2)$. 

To show $(2)$, one again proceeds by induction. Again, the statement is clear for $0$ and limit ordinals, so assume $\xi = \alpha +1$ and $L_\alpha \cap \Ord = \alpha$. 

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

We follow the standard procedure of **Gödelization** and assign every set theoretic formula $\varphi$ a **Gödel number** $\GN{\varphi}$.

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
\Op{Vbl}(a) \; :\Leftrightarrow \; \exists y \in a \exists x \in y \: (a = (1,x) \wedge x = \in \omega)
$$

where of course we substitute a suitable $\Delta_0$ formula for "$x \in \omega$".

```{prf:proposition}
:label: prop-defble-formula

The following relations are $\Delta_1$-definable over $\ZF$. 

> $\Op{Fml}^n(e): \quad$ $e$ is the code of a formula $\varphi$ whose free variables are among $v_0, \dots, v_{n-1}$;   
> $\Op{Fml}^n_a(e): \quad$ $e$ is the code of a formula $\varphi$ whose free variables are among $v_0, \dots, v_{n-1}$, and whose constants are of the form $\Const{a_i}$ with $a_i \in a$
```

### Definability of the satisfaction relation

Let $a$ be a set. If we replace a formula $\varphi$ by its code $\GN{\varphi}$, we have to express the fact that $\varphi^a$ holds now as a statement about validity in the structure $(a,\in)$, using the code. That is, we have to **formalize** the notion of truth. This can be done using the recursive definition of truth. 
This way we obtain a $\Delta_1$-definable predicate $\Op{Sat}(a,e)$ expressing 

> $\Op{Sat}(a,e): \quad$ $e$ is the code of a formula $\varphi(\Const{a_0}, \dots, \Const{a_n})$ that does not contain any free variables, and $\varphi$ is true in $(a,\in)$ under the canonical interpretation.

In place of  $\Op{Sat}(a,e)$, we will also write $(a,\in) \models e$. For any single formula, this formalization of truth then agrees with the validity of the corresponding relativization:

```{prf:theorem}
Let $\varphi(v_0, \dots, v_{n-1})$ be a set theoretic formula, and assume $a_0, \dots, a_{n-1} \in a$. Then it is provable in ZF that

$$
	\varphi^a(a_0, \dots, a_{n-1}) \; \leftrightarrow \; \Op{Sat}(a,\GN{\varphi(\Const{a_0}, \dots, \Const{a_{n-1}})}).
$$
```

(Keep in mind, however, that the general satisfaction relation, over all formulas, is not formalizable in $\ZF$.)

The Theorem is proved via induction over the structure of $\varphi$. For atomic $\varphi$, both sides express the same fact, since we use the canonical interpretation of constants. The definition of relativization ensures that for the inductive cases, both sides behave identically wit respect to the corresponding subformulas.

### Definability of definability 

We can now formalize the notion of definability we used informally above in the definition of $L$:

> $\mathcal{P}_{\Op{Def}}(a) = \{ x \subseteq a \colon \exists e \: (\Op{Fml}^1_a \: \wedge \: x = \{z \in a\colon (a,e) \models e(z)\})\}$

Here, $e(z)$ is defined so that for a formula $\varphi(v_0)$ with code $e$,

> $e(z)$ is the code of the formula we obtain when we substitute $\Const{z}$ for $v_0$ in $\varphi$: 
\begin{equation*}
	\GN{\varphi(v_0)}(z) = \GN{\varphi(\Const{z})}
\end{equation*}

```{prf:theorem}
:label: thm-definability-Pdef

The mapping $a \mapsto \mathcal{P}_{\Op{Def}}(a)$ is $\Sigma_1$-definable. The relation $b = \mathcal{P}_{\Op{Def}}(a)$ is $\Delta_1$-definable.
```

```{prf:proof}
(*Sketch*) One first verifies that the mapping

$$
	a \mapsto \Op{Fml}^1_a := \{ e \colon \Op{Fml}^1_a(e)\}
$$

is $\Sigma_1$-definable. Then compose this with the surjection

$$
	\Op{Fml}^1_a \mapsto \mathcal{P}_{\Op{Def}}(a),
$$

which, by the above definition of $\mathcal{P}_{\Op{Def}}(a)$, is $\Sigma_1$, too. 

The relation $b = \mathcal{P}_{\Op{Def}}(a)$ is then $\Delta_1$ by the usual argument for functions:

$$
	f(x) \neq y \; \Leftrightarrow \; \exists z (f(x)=z \: \wedge \: y \neq z)
$$
```

