This code generates the folding table for any element of a (reduced and irreducible) affine Weyl group. The concept of folding tables was introduced by Guilhot and Parkinson (Guilhot J, Parkinson J. A proof of Lusztig's conjectures for affine type $\tilde{G}_2$ with arbitrary parameters. Proceedings of the London Mathematical Society. 2019;118(5):1188-244.). This code generalises the definition to apply to all affine Coxeter types.

# Background

Let $V$ be the underlying vector space of the root system $\Phi$ of which our Coxeter group, $W$ is defined. The set of alcoves $\mathbb{A}$ is the set of the open connected components of $V\setminus (\bigcup_{\alpha,k}H_{\alpha,k})$ where $H_{\alpha,k} = \\{x\in V\mid \langle x,\alpha-k\delta\rangle = 0\\} = \\{x\in V\mid \langle x,\alpha\rangle = k\\}$ is the hyperplane corresponding to $\alpha\in \Phi$ and $k\in \mathbb{Z}$. We define the periodic orientation of each hyperplane $H_{\alpha,k}$ as follows:

$$H_{\alpha,k}^+ = \\{x\in V \mid \langle x,\alpha \rangle \geq k\\}\quad\text{ and }\quad H_{\alpha,k}^-=\\{x\in V \mid \langle x,\alpha \rangle\leq k\\}.$$

For two adjuacent alcoves $A,A'\in \mathbb{A}$, we write $A {^-}| ^+ A'$ if $A$ is on the negative side and $A'$ is of the positive side of the hyperplane containing their shared panel. Denote $A_0 =\\{x\in V \mid 0\leq \langle x,\alpha \rangle \leq 1 \text{ for all } \alpha \in \Phi^+\\}$ to be the fundamental alcove. 

Let $J\subseteq I = \\{1,2,3,\dots, n\\}$ be a subset of the indices of the finite generators of $W$ and let

$$\mathcal{A}_J = \\{x\in V \mid  0\leq \langle x, \alpha \rangle \leq 1 \text{ for all } \alpha \in \Phi_J^+\\}.$$

be the fundamental $J$-alcove where $\Phi_J\subseteq \Phi$ is the root system of the parabolic subgroup $W_J$ generated by $\\{s_j \mid j\in J\\}$. Denote the elements of $W$ within the fundamental $J$-alcove by $\mathbb{W}^J$, that is $\mathbb{W}^J = \\{w\in W \mid wA_0\subseteq \mathcal{A}_J\\}$.

Let $\overrightarrow{w} = s_{i_1}s_{i_2}\cdots s_{i_\ell}$ be an expression for $w\in W$ and $i_1,\dots i_\ell\in I\cup\{0\}$. A $J$*-folded alcove path* of type $\vec{w}$ starting at $v_0\in \mathbb{W}^J$ is the sequence $p = (v_0,v_1,\dots,v_\ell)$ where $v_1,\dots, v_\ell\in \mathbb{W}^J$ and we have the following conditions: for $1\leq k\leq \ell$
1. $v_k\in \\{v_{k-1},v_{k-1}s_{i_k}\\}$
2. if $v_{k-1} = v_k$ then either 
    1. $v_{k-1}s_{i_k}A_0\subseteq \mathcal{A}_J$ and $v_{k-1}A_0{^+}|^-v_{k-1}s_{i_k}A_0$, or 
    
    2. $v_{k-1}s_{i_k}A_0\nsubseteq \mathcal{A}_J$

Path $p$ has length $\ell$ and we define $\mathrm{end}(p) = v_\ell\sigma$ and $\mathrm{start}(p) = v_0$. Let $f(p)$ be the number of folds of $p$. We call a $J$-folded alcove path $p$ 'straight' if $f(p) = 0$. For $v\in \mathbb{W}^J$ and $w\in \widetilde{W}$, denote
$$\mathcal{P}_J(\overrightarrow{w},v) = \\{\text{all $J$-folded alcove paths of type $\vec{w}$ starting at $v$}\\}.$$

# Folding Tables

We can read such $J$-folded alcove paths off of folding tables. We define folding tables as follows. Let ${^J}W$ be the set of minimal length coset representatives of the cosets $W_J\setminus W_0$ where $W_0$ is the Coxeter group generated by the finite reflections of $W$ and let $u_1,\dots, u_r$ be the elements of ${^J}W$ ordered so that $\ell(u_i)\leq \ell(u_{i+1})$ (so $r = |{^J}W|$). Let $\vec{x}$ be a reduced expression of $x\in W$ and denote $p^i$ to be the straight path in $\mathcal{P}_J(\vec{x},u_i)$. If the $k$-th step of $p^i$ is a negative crossing, let $p_k^i$ denote the path in $\mathcal{P}_J(\vec{x},u_j)$ formed from $p^i$ by folding at step $k$. 
    
For each $1\leq i\leq r$ and $1\leq k\leq \ell(x)$ define $\mathsf{ft}_{i,k}(\vec{x})\in \\{-,*,1,2,3,\dots, r\\}$ as follows: 

1. If $p^i$ has a positive crossing at the $k$-th step, then $\mathsf{ft}_{i,k} = -$,
2. If $p^i$ has a bounce at the $k$-th step, then $\mathrm{ft}_{i,k} = *$, and 
3. If $p^i$ has a negative crossing at the $k$-th step, then $\mathsf{ft}_{i,k} = j$, where $u_{j} = \theta^J(p')$ and $p'$ is the straight path in $\mathcal{P}_J(\mathrm{rev}(\vec{x}),\theta^J(p_k^i))$

The $J$*-folding table of type $\vec{x}$* is then the $r\times \ell(x)$ array where the $(i,k)$-th entry is $\mathsf{ft}_{i,k}$. 

