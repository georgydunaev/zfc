# Cross-System Set Theory Bridge: Coq `zfc`, Isabelle/ZF, and `MKTD1-theory` / `MKTD2-theory`

<!--
  Provenance Header:
  Source files: /botworkspace/zfc/CrossSystemSetTheoryBridge.v, /botworkspace/article_isabelle_in_zfc/ScopedDeductionAndChoice.thy, /hostramdisk/set_theory_prover/program/types/typetheory.ML
  Generator: Cross-System Set Theory Bridge Specialist
-->

## 1. Architectural Overview Across the Three Formalizations

This document and the accompanying Coq module [CrossSystemSetTheoryBridge.v](file:///botworkspace/zfc/CrossSystemSetTheoryBridge.v) establish a formal correspondence connecting the three set-theoretic foundations developed in this workspace:

| Feature / Construct | Coq Aczel-Werner Trees ([zfc](file:///botworkspace/zfc/Sets.v)) | Isabelle/ZF ([article_isabelle_in_zfc](file:///botworkspace/article_isabelle_in_zfc/recursion.thy)) | Obelisk Morse-Kelley / NBG (`MKTD1-theory` and `MKTD2-theory`) |
| :--- | :--- | :--- | :--- |
| **Primary Carrier** | Inductive type `Ens := sup (A : Type) (f : A -> Ens)` | Object sort `i` over `FOL` (`typedecl i`) | Default class sort `Class` (`Class_Expre` in SML AST; modeled over `Ens` as `ClassPred := Ens -> Prop`) |
| **Equality Relation** | Recursive bisimulation `EQ : Ens -> Ens -> Prop` | Object equality `= : [i, i] => o` with `axext` | Extensional class equality $A = B \iff \forall x \in V.\, (x \in A \leftrightarrow x \in B)$ (`class_eq`) |
| **Sethood ($x \in V$)** | Every `E : Ens` is a small set by construction | Every `x :: i` is a set | Small classes $x \in V$ (`isSetClass C`), distinguished from proper classes such as $V$ (`UniversalClass`) |
| **Comprehension** | Bounded separation `Comp (E : Ens) (P : Ens -> Prop) : Ens` | Bounded separation `Collect(A, P)` (`{x in A . P(x)}`) | Unrestricted class comprehension `{x | phi(x)}` (`ClassComp`), with `Separation_preserves_isSetClass` |
| **Ordered Pair** | `Couple E E' := Paire (Sing E) (Paire Vide (Sing E'))` | Kuratowski pair `\langle a, b \rangle = {{a}, {a, b}}` (`KuratowskiPair`) | **Dunaev Tagged Ordered Pair** $[A, B]_D = (\{0\} \times A) \cup (\{1\} \times B)$ (`DunaevTaggedClassPair`) |

---

## 2. Formalized Theorems in `CrossSystemSetTheoryBridge.v`

All theorems in [CrossSystemSetTheoryBridge.v](file:///botworkspace/zfc/CrossSystemSetTheoryBridge.v) are verified by `coqc` (`coqc -Q /botworkspace/zfc "" /tmp/CrossSystemSetTheoryBridge.v -o /tmp/CrossSystemSetTheoryBridge.vo`) with zero `Admitted` statements and without mutating any pre-compiled `.vo` files in `/botworkspace/zfc`.

### Part 1: Full and Faithful Embedding of `Ens` Sets into `MKTD1-theory` / `MKTD2-theory` Classes

In [CrossSystemSetTheoryBridge.v](file:///botworkspace/zfc/CrossSystemSetTheoryBridge.v#L19-L95):
- **`set_to_class (E : Ens) : ClassPred := fun x => IN x E`** embeds every Aczel-Werner tree `E : Ens` into the carrier of extensional classes (`set_to_class_extensional`).
- **`set_to_class_sub_iff` and `set_to_class_eq_iff`**: Prove that class inclusion `class_sub` and extensional class equality `class_eq` on embedded sets coincide with `INC E1 E2` and `EQ E1 E2`:
  $$\mathrm{class\_eq}(\mathrm{set\_to\_class}(E_1), \mathrm{set\_to\_class}(E_2)) \Longleftrightarrow \mathrm{EQ}(E_1, E_2).$$
- **`UniversalClass` and `isSetClass`**: Define the proper universal class $V$ (`UniversalClass`) and the sethood predicate `isSetClass C`, proving `every_Ens_isSetClass` and `Separation_preserves_isSetClass` (intersecting any extensional class $C$ with a set $E$ yields a set represented by `Comp E C`).

### Part 2: Isabelle/ZF Kuratowski Pairs and Double-Union Domain Bounds

In [CrossSystemSetTheoryBridge.v](file:///botworkspace/zfc/CrossSystemSetTheoryBridge.v#L98-L163):
- **`KuratowskiPair (A B : Ens) : Ens := Paire (Sing A) (Paire A B)`** models the Isabelle/ZF Kuratowski ordered pair $\langle A, B \rangle = \{\{A\}, \{A, B\}\}$ used in [recursion.thy](file:///botworkspace/article_isabelle_in_zfc/recursion.thy) and [additional.thy](file:///botworkspace/article_isabelle_in_zfc/additional.thy).
- **`sinup_bridge`, `Kuratowski_fst_in_Union`, and `Kuratowski_snd_in_Union`**: Prove $\{A\} \in \langle A, B \rangle_{\mathrm{Kur}}$ and $A, B \in \bigcup \langle A, B \rangle_{\mathrm{Kur}}$.
- **`Isabelle_ZF_domain_in_Union_Union`**: Formalizes `lemma2` ($\mathrm{domain}(f) \subseteq \bigcup\bigcup f$) from [additional.thy](file:///botworkspace/article_isabelle_in_zfc/additional.thy#L560-L585):
  $$\mathrm{IN}(\mathrm{KuratowskiPair}(x, y), f) \Longrightarrow \mathrm{IN}(x, \mathrm{Union}(\mathrm{Union}(f))).$$

### Part 3: Dunaev Tagged Ordered Pairs for Arbitrary Classes vs. Small Sets

In `MKTD1-theory` and `MKTD2-theory`, Kuratowski pairing cannot be applied to proper classes $A \notin V$ because a proper class cannot belong to a singleton $\{A\}$. Instead, `MKTD1-theory` and `MKTD2-theory` use **Dunaev Tagged Ordered Pairs**:
$$[A, B]_D = (\{\mathrm{Tag}_0\} \times A) \cup (\{\mathrm{Tag}_1\} \times B), \qquad \mathrm{Tag}_0 = \emptyset, \quad \mathrm{Tag}_1 = \{\emptyset\}.$$

In [CrossSystemSetTheoryBridge.v](file:///botworkspace/zfc/CrossSystemSetTheoryBridge.v#L166-L328), we formalize `DunaevTaggedClassPair (A B : ClassPred) : ClassPred` and prove:
1. **`DunaevTaggedClassPair_extensional`**: For any classes $A, B$, $[A, B]_D$ is an extensional class.
2. **`DunaevTaggedClassPair_inj_left` and `DunaevTaggedClassPair_inj_right`**: Unconditional first- and second-projection injectivity for **all** extensional classes $A, A', B, B'$ (including proper classes such as `UniversalClass` $V$):
   $$\mathrm{class\_eq}([A, B]_D, [A', B']_D) \Longrightarrow \mathrm{class\_eq}(A, A') \;\wedge\; \mathrm{class\_eq}(B, B').$$
3. **`DunaevEnsPair_matches_ClassPair` and `DunaevTaggedClassPair_preserves_isSetClass`**: When both $A = \mathrm{set\_to\_class}(E_1)$ and $B = \mathrm{set\_to\_class}(E_2)$ are small sets (`Ens`), their Dunaev tagged class pair coincides with the `Ens` set `DunaevEnsPair E1 E2 := Union (Paire (Prod (Sing Tag0) E1) (Prod (Sing Tag1) E2))` and therefore satisfies `isSetClass`.
