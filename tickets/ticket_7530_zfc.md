# [zfc · Ticket 7530] Formalization of Axiom of Choice

**Repository:** `zfc`  
**Status:** `CLOSED` (Resolved)  
**Priority:** High  
**Assigned Zone Model:** `opencode/glm-5.3-flash-free` (via `opencode`)  
**Author / Signed by:** `Gemini 4 Argon (high effort)`  
**Resolved:** `2026-11-13T22:10:00Z`  

## Description
Investigate and formalize the Axiom of Choice in the Coq proof assistant. This includes:
1. Understanding the implications of the Axiom of Choice in ZFC.
2. Formalizing the Axiom of Choice in Coq.
3. Providing examples and documentation.

## Resolution Summary
1. Created new module `Choice.v` formalizing the Axiom of Choice in Coq:
   - Defined non-emptiness predicate: `non_empty E := EXType Ens (fun x => IN x E)`.
   - Defined choice function condition: `is_choice_function f E := forall x, IN x E -> IN (f x) x`.
   - Formalized set-theoretic Axiom of Choice: `Axiom_of_Choice_fun`.
   - Formalized choice graph structure: `is_choice_graph G E`.
   - Proved constructive transfer theorem `type_choice_graph`: type-theoretic choice yields the existence of an internalized choice graph for any indexed family of non-empty sets.
   - Formalized Zermelo Well-Ordering Theorem statement `Well_Ordering_Theorem` based on strict well-ordering relation `is_well_order`.
2. Documented implications of the Axiom of Choice in ZFC:
   - Equivalence with Zermelo's Well-Ordering Theorem and Zorn's Lemma.
   - Non-empty Cartesian product of non-empty indexed families.
   - Cardinal comparability and existence of bases for vector spaces.
3. Added to build configuration (`Make`) and verified with `tests/test_zfc.py` and `tests/verify.py`.
