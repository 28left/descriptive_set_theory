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
\newcommand{\Norm}[1]{\parallel \! #1 \!\parallel}
\newcommand{\V}{\mathbf{V}}
\newcommand{\Ord}{\mathbf{Ord}}
\DeclareMathOperator{\W}{W}
\DeclareMathOperator{\WF}{WF}
\DeclareMathOperator{\WOrd}{WOrd}
```


A set $X$ is **(first-order) definable** in a set $Y$ (from parameters) if there exists a first-order formula $\varphi(x_0, x_1, \dots, x_n)$ in the language of set theory (i.e.\ only using the binary relation symbol $\in$) such that for some $a_1, \dots, a_n \in Y$,

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