# Note 3: Completions for Examples, Cardinal Arithmetic, König's Theorem, Club Filter, Fodor's Lemma, and GCH Formulas

This document provides rigorous mathematical proofs and constructive Coq derivations completing the unfinished example scripts ([examples/example_1.v](file:///botworkspace/zfc/examples/example_1.v) and [examples/example_2.v](file:///botworkspace/zfc/examples/example_2.v)) as well as the statement-only propositions and postulated parameters in [Cardinal.v](file:///botworkspace/zfc/Cardinal.v), [cardinal_exponentiation.v](file:///botworkspace/zfc/cardinal_exponentiation.v), [club_and_stationary.v](file:///botworkspace/zfc/club_and_stationary.v), and [gch_and_singular_cardinals.v](file:///botworkspace/zfc/gch_and_singular_cardinals.v).

---

## 1. Constructive Coq Completions of `examples/example_1.v` and `examples/example_2.v`

In [examples/example_1.v](file:///botworkspace/zfc/examples/example_1.v) and [examples/example_2.v](file:///botworkspace/zfc/examples/example_2.v), the informal theorems use surface set notation and end with `Admitted.`. In the Aczel-Werner `Ens` universe of [Sets.v](file:///botworkspace/zfc/Sets.v) and [Axioms.v](file:///botworkspace/zfc/Axioms.v), both theorems are proved constructively without axioms:

### 1.1 Example 1: Inhabitation of `{0, 1, 2}`
Represent $\{0, 1, 2\}$ as `Paire (Nat 0) (Paire (Nat 1) (Nat 2))`. By `IN_Paire_left`, `Nat 0` is an element:
```coq
Require Import Sets Axioms Omega.

Definition set_0_1_2 : Ens := Paire (Nat 0) (Paire (Nat 1) (Nat 2)).

Theorem example_1_completed : EXType Ens (fun x => IN x set_0_1_2).
Proof.
  exists (Nat 0).
  unfold set_0_1_2.
  apply IN_Paire_left.
Qed.
```

### 1.2 Example 2: Existence of Binary Union $C = A \cup B$
Given $A, B : \mathrm{Ens}$, the binary union is $C = \mathrm{Union}(\mathrm{Paire}\,A\,B)$. By `IN_Union`, `IN_Paire_left`, `IN_Paire_right`, `Union_IN`, and `Paire_IN`:
```coq
Require Import Sets Axioms.

Theorem example_2_completed :
  forall A B : Ens,
  EXType Ens (fun C => forall x : Ens, IN x C <-> (IN x A \/ IN x B)).
Proof.
  intros A B.
  exists (Union (Paire A B)).
  intros x. split.
  - intros Hin.
    destruct (Union_IN (Paire A B) x Hin) as [Y [HY HxY]].
    destruct (Paire_IN A B Y HY) as [HeqA | HeqB].
    + left. apply IN_sound_right with Y; [exact HeqA | exact HxY].
    + right. apply IN_sound_right with Y; [exact HeqB | exact HxY].
  - intros [HxA | HxB].
    + apply IN_Union with A; [apply IN_Paire_left | exact HxA].
    + apply IN_Union with B; [apply IN_Paire_right | exact HxB].
Qed.
```

---

## 2. Algebraic Laws of Cardinal Arithmetic and Hessenberg Absorption ([Cardinal.v](file:///botworkspace/zfc/Cardinal.v) and [cardinal_exponentiation.v](file:///botworkspace/zfc/cardinal_exponentiation.v))

### 2.1 Explicit Bijections for Sum, Product, and Exponentiation Laws
Let $\kappa + \lambda = (\kappa \times \{0\}) \cup (\lambda \times \{1\})$, $\kappa \cdot \lambda = \kappa \times \lambda$, and $\kappa^\lambda = \{F \subseteq \lambda \times \kappa : \mathrm{is\_function\_graph}(\lambda, \kappa, F)\}$:

1. **Commutativity of Sum (`card_sum_comm_statement`)**:
   $$\Phi(\langle x, 0 \rangle) = \langle x, 1 \rangle, \qquad \Phi(\langle y, 1 \rangle) = \langle y, 0 \rangle$$
   is an involution between $\kappa + \lambda$ and $\lambda + \kappa$.
2. **Commutativity of Product (`card_prod_comm_statement`)**:
   $$\Psi(\langle x, y \rangle) = \langle y, x \rangle$$
   is a bijection between $\kappa \times \lambda$ and $\lambda \times \kappa$ by `Couple_inj_left` and `Couple_inj_right`.
3. **Associativity of Sum and Product (`card_sum_assoc_statement`, `card_prod_assoc_statement`)**:
   $$\alpha_{\times}(\langle \langle x, y \rangle, z \rangle) = \langle x, \langle y, z \rangle \rangle$$
   is a bijection $(\kappa \times \lambda) \times \mu \cong \kappa \times (\lambda \times \mu)$.
4. **Distributivity (`card_prod_distrib_statement`)**:
   $$\delta(\langle x, \langle y, i \rangle \rangle) = \langle \langle x, y \rangle, i \rangle \quad (i \in \{0, 1\})$$
   is a bijection $\kappa \times (\lambda + \mu) \cong (\kappa \times \lambda) + (\kappa \times \mu)$.
5. **Exponentiation Laws (`card_exp_one_statement`, `card_exp_sum_statement`, `card_prod_exp_statement`, `card_exp_exp_statement`)**:
   - $\kappa^1 \cong \kappa$: $F \mapsto F(\emptyset)$, with inverse $a \mapsto \{\langle \emptyset, a \rangle\}$.
   - $\kappa^{\lambda + \mu} \cong \kappa^\lambda \times \kappa^\mu$: $F \mapsto \langle \lambda b \in \lambda.\, F(\langle b, 0 \rangle),\, \lambda c \in \mu.\, F(\langle c, 1 \rangle) \rangle$.
   - $(\kappa \cdot \lambda)^\mu \cong \kappa^\mu \times \lambda^\mu$: $F \mapsto \langle \pi_1 \circ F,\, \pi_2 \circ F \rangle$.
   - $(\kappa^\lambda)^\mu \cong \kappa^{\lambda \cdot \mu}$ (Currying): $F \mapsto (\langle b, c \rangle \mapsto F(c)(b))$.

### 2.2 Derivation of `Hessenberg_implies_Absorption`
**Theorem**: Assume Hessenberg's Theorem ($\forall \kappa \ge \aleph_0,\, \kappa \cdot \kappa \approx \kappa$) and Cantor-Bernstein ($\mathrm{injects}\,X\,Y \land \mathrm{injects}\,Y\,X \implies \mathrm{equipotent}\,X\,Y$). For any infinite cardinals $\kappa, \lambda$ with $1 \le \lambda \le \kappa$:
$$\kappa + \lambda \approx \kappa \quad \text{and} \quad \kappa \cdot \lambda \approx \kappa.$$
*Proof*:
1. **Product Absorption**: Since $\lambda \neq \emptyset$, choose $y_0 \in \lambda$. By `card_prod_inj_left`, $\kappa \hookrightarrow \kappa \times \lambda$ via $x \mapsto \langle x, y_0 \rangle$. Conversely, since $\lambda \hookrightarrow \kappa$, we have $\kappa \times \lambda \hookrightarrow \kappa \times \kappa \approx \kappa$ by Hessenberg's Theorem. By Cantor-Bernstein, $\kappa \cdot \lambda \approx \kappa$.
2. **Sum Absorption**: By `card_sum_inj_left`, $\kappa \hookrightarrow \kappa + \lambda$. Conversely, since $\lambda \hookrightarrow \kappa$, we have $\kappa + \lambda \hookrightarrow \kappa + \kappa = \kappa \times 2 \hookrightarrow \kappa \times \aleph_0 \hookrightarrow \kappa \times \kappa \approx \kappa$. By Cantor-Bernstein, $\kappa + \lambda \approx \kappa$.

---

## 3. König's Theorem and Cofinality of the Continuum ([cardinal_exponentiation.v](file:///botworkspace/zfc/cardinal_exponentiation.v))

### 3.1 Proof of König's Theorem (`Konig_Theorem_statement`)
**Theorem (König)**: Let $I$ be an indexing set and let $\langle \kappa_i : i \in I \rangle$, $\langle \lambda_i : i \in I \rangle$ be families of cardinals such that $\kappa_i < \lambda_i$ for every $i \in I$. Then
$$\sum_{i \in I} \kappa_i < \prod_{i \in I} \lambda_i.$$
*Proof*:
1. **Forward Injection ($\le$)**: For each $i \in I$, since $\kappa_i < \lambda_i$, choose an injection $e_i : \kappa_i \hookrightarrow \lambda_i$ and a witness $d_i \in \lambda_i \setminus e_i[\kappa_i]$. Define $\Phi : \sum_{i \in I} \kappa_i \to \prod_{i \in I} \lambda_i$ by sending $\langle i, x \rangle$ ($x \in \kappa_i$) to the function $f_{\langle i, x \rangle}$ where
   $$f_{\langle i, x \rangle}(j) = \begin{cases} e_i(x) & \text{if } j = i, \\ d_j & \text{if } j \neq i. \end{cases}$$
   If $f_{\langle i, x \rangle} = f_{\langle i', x' \rangle}$, then $i$ is the unique coordinate $j$ where the function value lies in $e_j[\kappa_j]$ rather than equaling $d_j$, so $i = i'$ and $e_i(x) = e_i(x') \implies x = x'$.
2. **No Surjection ($<$)**: Suppose $F : \sum_{i \in I} \kappa_i \to \prod_{i \in I} \lambda_i$ is any map. For each $i \in I$, the slice $S_i = \{F(\langle i, x \rangle)(i) : x \in \kappa_i\} \subseteq \lambda_i$ has cardinality $\le \kappa_i < \lambda_i$, so $S_i \neq \lambda_i$. Choose $d(i) \in \lambda_i \setminus S_i$. Then $d \in \prod_{i \in I} \lambda_i$, and by `Konig_diagonal_contradiction`, for every $\langle j, y \rangle \in \sum_{i \in I} \kappa_i$ we have $F(\langle j, y \rangle)(j) \neq d(j)$, so $F(\langle j, y \rangle) \neq d$. Thus $F$ is not surjective.

### 3.2 Proof of `Konig_implies_cf_power` ($\kappa < \mathrm{cf}(2^\kappa)$)
**Corollary**: For every infinite cardinal $\kappa$, $\kappa < \mathrm{cf}(2^\kappa)$. In particular, $\mathrm{cf}(2^{\aleph_0}) > \aleph_0$, so $2^{\aleph_0} \neq \aleph_\omega$.
*Proof*: Suppose $\beta = \mathrm{cf}(2^\kappa) \le \kappa$. Then $2^\kappa$ can be written as the union of $\beta$-many sets $\bigcup_{i < \beta} A_i$ where $|A_i| = \kappa_i < 2^\kappa$. Setting $\lambda_i = 2^\kappa$ for all $i < \beta$, König's Theorem yields:
$$2^\kappa = \left|\bigcup_{i < \beta} A_i\right| \le \sum_{i < \beta} \kappa_i < \prod_{i < \beta} 2^\kappa = (2^\kappa)^\beta \le (2^\kappa)^\kappa = 2^{\kappa \cdot \kappa} = 2^\kappa,$$
a contradiction ($2^\kappa < 2^\kappa$). Therefore, $\kappa < \mathrm{cf}(2^\kappa)$.

---

## 4. Proofs of Club Filter Closure, Diagonal Intersection, and Fodor's Lemma ([club_and_stationary.v](file:///botworkspace/zfc/club_and_stationary.v))

Let $\kappa > \aleph_0$ be an uncountable regular cardinal.

### 4.1 Proof of `club_filter_intersection_unbounded`
**Proposition**: If $C_1, C_2 \subseteq \kappa$ are club subsets of $\kappa$, then $C_1 \cap C_2$ is unbounded in $\kappa$.
*Proof*: Let $\alpha_0 < \kappa$ be arbitrary. Since $C_1$ and $C_2$ are unbounded in $\kappa$, construct by $\omega$-recursion an interleaving sequence:
$$\alpha_0 < \beta_0 < \alpha_1 < \beta_1 < \dots < \alpha_n < \beta_n < \alpha_{n+1} < \dots$$
where $\beta_n \in C_1$ with $\alpha_n < \beta_n$, and $\alpha_{n+1} \in C_2$ with $\beta_n < \alpha_{n+1}$. Since $\mathrm{cf}(\kappa) = \kappa > \omega$, the supremum
$$\delta = \sup_{n < \omega} \beta_n = \sup_{n < \omega} \alpha_n < \kappa$$
is a limit ordinal below $\kappa$. Because $\delta$ is a limit point of $C_1$ ($\{\beta_n : n < \omega\} \subseteq C_1 \cap \delta$ is cofinal in $\delta$) and $C_1$ is closed, $\delta \in C_1$. Similarly, $\{\alpha_{n+1} : n < \omega\} \subseteq C_2 \cap \delta$ is cofinal in $\delta$ and $C_2$ is closed, so $\delta \in C_2$. Thus $\delta \in C_1 \cap C_2$ and $\alpha_0 < \delta$.

### 4.2 Proof of `diagonal_intersection_closed` and `diagonal_intersection_unbounded`
Let $\langle C_\alpha : \alpha < \kappa \rangle$ be a sequence of club subsets of $\kappa$, and let
$$\Delta_{\alpha < \kappa} C_\alpha = \{\xi < \kappa : \forall \alpha < \xi,\, \xi \in C_\alpha\}.$$
1. **Closed (`diagonal_intersection_closed`)**: Let $\delta < \kappa$ be a limit point of $D = \Delta_{\alpha < \kappa} C_\alpha$, and fix $\alpha < \delta$. Since $D \cap \delta$ is unbounded in $\delta$, the tail $\{\xi \in D \cap \delta : \alpha < \xi\}$ is also unbounded in $\delta$. For every $\xi \in D \cap \delta$ with $\alpha < \xi$, the definition of $D$ guarantees $\xi \in C_\alpha$. Hence $\delta$ is a limit point of $C_\alpha$. Since $C_\alpha$ is closed, $\delta \in C_\alpha$. As $\alpha < \delta$ was arbitrary, $\delta \in D$.
2. **Unbounded (`diagonal_intersection_unbounded`)**: By replacing $C_\alpha$ with $\bigcap_{\eta \le \alpha} C_\eta$ (which is club since $\kappa$ is regular and $|\alpha + 1| < \kappa$), we may assume $C_0 \supseteq C_1 \supseteq \dots \supseteq C_\alpha \supseteq \dots$. Given $\gamma_0 < \kappa$, choose $\gamma_{n+1} \in C_{\gamma_n}$ with $\gamma_{n+1} > \gamma_n$ for each $n < \omega$. Let $\delta = \sup_{n < \omega} \gamma_n < \kappa$. For any $\alpha < \delta$, there exists $n_0 < \omega$ such that $\alpha < \gamma_{n_0}$. For all $n \ge n_0$, $\gamma_{n+1} \in C_{\gamma_n} \subseteq C_{\gamma_{n_0}} \subseteq C_\alpha$. Thus $\delta = \sup_{n \ge n_0} \gamma_{n+1} \in C_\alpha$ because $C_\alpha$ is closed. Hence $\delta \in \Delta_{\alpha < \kappa} C_\alpha$ and $\gamma_0 < \delta$.

### 4.3 Proof of Fodor's Pressing Down Lemma (`Fodors_Lemma_statement`)
**Theorem (Fodor, 1956)**: Let $S \subseteq \kappa$ be stationary in an uncountable regular cardinal $\kappa$, and let $f : S \to \kappa$ be regressive ($\forall \alpha \in S \setminus \{0\},\, f(\alpha) < \alpha$). Then there exists $\gamma < \kappa$ such that $f^{-1}(\{\gamma\}) = \{\alpha \in S : f(\alpha) = \gamma\}$ is stationary in $\kappa$.
*Proof*: Suppose towards a contradiction that for every $\gamma < \kappa$, the fiber $S_\gamma = f^{-1}(\{\gamma\})$ is non-stationary. Then for each $\gamma < \kappa$, there exists a club subset $C_\gamma \subseteq \kappa$ disjoint from $S_\gamma$ ($S_\gamma \cap C_\gamma = \emptyset$). By `diagonal_intersection_is_club`, the diagonal intersection
$$C = \Delta_{\gamma < \kappa} C_\gamma = \{\alpha < \kappa : \forall \gamma < \alpha,\, \alpha \in C_\gamma\}$$
is a club subset of $\kappa$, and $C \setminus \{0\}$ is also club in $\kappa$. Since $S$ is stationary, there exists $\alpha \in S \cap (C \setminus \{0\})$. Because $\alpha \in S \setminus \{0\}$ and $f$ is regressive, $\gamma = f(\alpha) < \alpha$. Since $\alpha \in \Delta_{\eta < \kappa} C_\eta$ and $\gamma < \alpha$, we have $\alpha \in C_\gamma$. But $\alpha \in S$ and $f(\alpha) = \gamma$ mean $\alpha \in S_\gamma$, contradicting $S_\gamma \cap C_\gamma = \emptyset$.

---

## 5. Proofs of Hausdorff's and Bernstein's Cardinal Exponentiation Formulas ([gch_and_singular_cardinals.v](file:///botworkspace/zfc/gch_and_singular_cardinals.v))

### 5.1 Hausdorff's Formula (`Hausdorff_formula_statement`, 1904)
**Theorem (Hausdorff)**: For all ordinals $\alpha, \beta$,
$$\aleph_{\alpha+1}^{\aleph_\beta} = \aleph_\alpha^{\aleph_\beta} \cdot \aleph_{\alpha+1}.$$
*Proof*:
- ($\ge$): Since $\aleph_\alpha \le \aleph_{\alpha+1}$, we have $\aleph_\alpha^{\aleph_\beta} \le \aleph_{\alpha+1}^{\aleph_\beta}$; also $\aleph_{\alpha+1} = \aleph_{\alpha+1}^1 \le \aleph_{\alpha+1}^{\aleph_\beta}$. By Hessenberg absorption, $\aleph_\alpha^{\aleph_\beta} \cdot \aleph_{\alpha+1} \le \aleph_{\alpha+1}^{\aleph_\beta}$.
- ($\le$): Since $\aleph_{\alpha+1}$ is a regular cardinal, depends on two cases:
  1. If $\aleph_{\alpha+1} \le \aleph_\beta$, then $\aleph_{\alpha+1}^{\aleph_\beta} = 2^{\aleph_\beta} = \aleph_\alpha^{\aleph_\beta} = \aleph_\alpha^{\aleph_\beta} \cdot \aleph_{\alpha+1}$.
  2. If $\aleph_\beta < \aleph_{\alpha+1}$, then since $\mathrm{cf}(\aleph_{\alpha+1}) = \aleph_{\alpha+1} > \aleph_\beta$, every function $f : \aleph_\beta \to \aleph_{\alpha+1}$ has bounded range in $\aleph_{\alpha+1}$, i.e., $f \in \xi^{\aleph_\beta}$ for some ordinal $\xi < \aleph_{\alpha+1}$. Therefore,
     $$\aleph_{\alpha+1}^{\aleph_\beta} = \left|\bigcup_{\xi < \aleph_{\alpha+1}} \xi^{\aleph_\beta}\right| \le \sum_{\xi < \aleph_{\alpha+1}} |\xi|^{\aleph_\beta} \le \sum_{\xi < \aleph_{\alpha+1}} \aleph_\alpha^{\aleph_\beta} = \aleph_\alpha^{\aleph_\beta} \cdot \aleph_{\alpha+1}.$$

### 5.2 Bernstein's Formula (`Bernstein_formula_statement`)
**Corollary (Bernstein)**: For every finite $n < \omega$ and every ordinal $\beta$,
$$\aleph_n^{\aleph_\beta} = 2^{\aleph_\beta} \cdot \aleph_n.$$
*Proof*: By mathematical induction on $n < \omega$:
- **Base Case ($n = 0$)**: Since $2 \le \aleph_0 \le 2^{\aleph_0} \le 2^{\aleph_\beta}$, we have $2^{\aleph_\beta} \le \aleph_0^{\aleph_\beta} \le (2^{\aleph_0})^{\aleph_\beta} = 2^{\aleph_0 \cdot \aleph_\beta} = 2^{\aleph_\beta} = 2^{\aleph_\beta} \cdot \aleph_0$.
- **Inductive Step ($n \mapsto n+1$)**: By Hausdorff's Formula and the induction hypothesis,
  $$\aleph_{n+1}^{\aleph_\beta} = \aleph_n^{\aleph_\beta} \cdot \aleph_{n+1} = (2^{\aleph_\beta} \cdot \aleph_n) \cdot \aleph_{n+1} = 2^{\aleph_\beta} \cdot (\aleph_n \cdot \aleph_{n+1}) = 2^{\aleph_\beta} \cdot \aleph_{n+1}.$$
