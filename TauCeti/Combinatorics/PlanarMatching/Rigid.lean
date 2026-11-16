/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.Combinatorics.PlanarMatching.Monoidal
import all TauCeti.Combinatorics.PlanarMatching.Associativity
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Tensor

/-!
# The rigid structure on the Temperley–Lieb diagram category

Every object `X = of n` of the Temperley–Lieb diagram category `TauCeti.TLDiagCat` is canonically
self-dual: the coevaluation `TauCeti.TLDiagCat.coeval n : 𝟙_ TLDiagCat ⟶ of n ⊗ of n` and
evaluation `TauCeti.TLDiagCat.eval n : of n ⊗ of n ⟶ 𝟙_ TLDiagCat` are given by the fully nested
matching `PlanarMatching.nested n` with no closed circles. At `n = 0`, both are definitionally
`𝟙 (of 0)`, so the self-duality on the tensor unit is definitionally equal to Mathlib's
`CategoryTheory.exactPairingUnit` (and likewise `HasRightDual (𝟙_ TLDiagCat)` and
`HasLeftDual (𝟙_ TLDiagCat)` agree definitionally with `hasRightDualUnit` and `hasLeftDualUnit`).
At `n = 1`, `coeval 1` and `eval 1` are the generating `cup` and `cap`.

The zigzag identities are checked directly for `n = 1` and propagated to all `n` by induction
using Mathlib's `ExactPairing.tensor` and `exactPairingCongrLeft`: the nested coevaluation and
evaluation on `n + 1` strands agree with the tensor product of the pairings on `1` and `n`
strands. Composing `coeval n` with `eval n` produces `n` closed circles
(`TauCeti.TLDiagCat.coeval_comp_eval`).

Through this self-duality, the categorical Frobenius reciprocity equivalences
`tensorRightHomEquiv` and `tensorLeftHomEquiv` at the generating object `of 1` coincide with the
combinatorial corner-dragging equivalences `TauCeti.TLDiagram.dragRight` and
`TauCeti.TLDiagram.dragLeft`. Consequently, both the right and left adjoint mates of any morphism
`f : X ⟶ Y` act on the underlying diagram by rotating it `180°` (horizontal followed by vertical
reflection, `TLDiagram.reflect Y.as X.as (TLDiagram.verticalReflect X.as Y.as f.diagram)`), so
`ᘁf = fᘁ` and `(fᘁ)ᘁ = f`.

## Main definitions

* `TauCeti.TLDiagCat.coeval`, `TauCeti.TLDiagCat.eval`: nested coevaluation and evaluation
  morphisms for `of n`.
* `TauCeti.TLDiagCat.selfExactPairing`: the self-duality `ExactPairing X X` on every object `X`.
* `TauCeti.TLDiagCat.instExactPairingOfOne`: the ambient `ExactPairing (of 1) (of 1)` given by
  `cup` and `cap`.
* `TauCeti.TLDiagCat.instHasRightDual`, `TauCeti.TLDiagCat.instHasLeftDual`,
  `TauCeti.TLDiagCat.instRightRigidCategory`, `TauCeti.TLDiagCat.instLeftRigidCategory`,
  `TauCeti.TLDiagCat.instRigidCategory`: the rigid monoidal category structure on `TLDiagCat`.

## Main results

* `TauCeti.TLDiagCat.coeval_succ`, `TauCeti.TLDiagCat.eval_succ`,
  `TauCeti.TLDiagCat.eval_succ_outer`: recursive decompositions of the nested coevaluation and
  evaluation in terms of `cup` and `cap`.
* `TauCeti.TLDiagCat.coeval_comp_eval`: closing `n` nested strands produces `n` closed circles.
* `TauCeti.TLDiagCat.diagram_tensorRightHomEquiv`,
  `TauCeti.TLDiagCat.diagram_tensorLeftHomEquiv`: Frobenius reciprocity at `of 1` agrees with
  combinatorial corner-dragging.
* `TauCeti.TLDiagCat.diagram_rightAdjointMate`, `TauCeti.TLDiagCat.diagram_leftAdjointMate`,
  `TauCeti.TLDiagCat.leftAdjointMate_eq_rightAdjointMate`,
  `TauCeti.TLDiagCat.rightAdjointMate_rightAdjointMate`: both adjoint mates rotate a diagram by
  `180°`, agree with each other, and are involutive.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory ExactPairing Equiv

namespace TauCeti

namespace TLDiagCat

/-! ### Nested coevaluation and evaluation -/

@[expose] section DualData

/-- The nested **coevaluation** `𝟙_ TLDiagCat ⟶ of n ⊗ of n`: the fully nested matching on `2n`
top boundary points with no closed circles. At `n = 0` this is definitionally `𝟙 (of 0)`, matching
`CategoryTheory.exactPairingUnit`. -/
def coeval : (n : ℕ) → (𝟙_ TLDiagCat ⟶ of n ⊗ of n)
  | 0 => 𝟙 (of 0)
  | n + 1 =>
      Hom.mk ⟨PlanarMatching.cast (Nat.zero_add _).symm (PlanarMatching.nested (n + 1)), 0⟩

/-- The nested **evaluation** `of n ⊗ of n ⟶ 𝟙_ TLDiagCat`: the fully nested matching on `2n`
bottom boundary points with no closed circles. At `n = 0` this is definitionally `𝟙 (of 0)`,
matching `CategoryTheory.exactPairingUnit`. -/
def eval : (n : ℕ) → (of n ⊗ of n ⟶ 𝟙_ TLDiagCat)
  | 0 => 𝟙 (of 0)
  | n + 1 => Hom.mk ⟨PlanarMatching.nested (n + 1), 0⟩

end DualData

@[simp]
theorem coeval_zero : coeval 0 = 𝟙 (of 0) :=
  (rfl)

@[simp]
theorem eval_zero : eval 0 = 𝟙 (of 0) :=
  (rfl)

theorem matching_coeval (n : ℕ) :
    (coeval n).diagram.matching =
      PlanarMatching.cast (Nat.zero_add _).symm (PlanarMatching.nested n) := by
  cases n with
  | zero => exact Subsingleton.elim (α := PlanarMatching 0) _ _
  | succ n => rfl

@[simp]
theorem circles_coeval (n : ℕ) : (coeval n).diagram.circles = 0 := by
  cases n <;> simp [coeval]

theorem matching_eval (n : ℕ) : (eval n).diagram.matching = PlanarMatching.nested n := by
  cases n with
  | zero => exact Subsingleton.elim (α := PlanarMatching 0) _ _
  | succ n => rfl

@[simp]
theorem circles_eval (n : ℕ) : (eval n).diagram.circles = 0 := by
  cases n <;> simp [eval]

/-- On two boundary points there is only one planar matching, namely `nested 1`. -/
private theorem eq_nested_one (x : PlanarMatching 2) : x = PlanarMatching.nested 1 := by
  apply PlanarMatching.ext
  intro a
  have hne : (x.1.val a : ℕ) ≠ (a : ℕ) := fun h => x.1.apply_ne a (Fin.ext h)
  have hlt : (x.1.val a : ℕ) < 2 := (x.1.val a).isLt
  have ha : (a : ℕ) < 2 := a.isLt
  have hnest : ((PlanarMatching.nested 1).1.val a : ℕ) = 1 - (a : ℕ) := by
    rw [← PlanarMatching.pv_coe, PlanarMatching.pv_nested 1 ha]
  exact Fin.ext (by omega)

@[simp]
theorem coeval_one : coeval 1 = cup := by
  apply hom_ext
  ext : 1
  · exact (eq_nested_one _).trans (eq_nested_one _).symm
  · simp

@[simp]
theorem eval_one : eval 1 = cap := by
  apply hom_ext
  ext : 1
  · exact (eq_nested_one _).trans (eq_nested_one _).symm
  · simp

/-! ### Recursive decompositions of `coeval` and `eval` -/

open PlanarMatching in
/-- Helper expressing the partner function of `(of 1 ◁ coeval n) ▷ of 1` as inserting `nested n`
at position `3` into `nested 2`. -/
private theorem pv_whiskerLeft_coeval_whiskerRight (n : ℕ) :
    pv ((of 1 ◁ coeval n) ▷ of 1).diagram.matching =
      insertFn 3 1 (n + n) (pv (nested 2)) (pv (nested n)) := by
  simp only [diagram_whiskerRight, diagram_whiskerLeft, TLDiagram.matching_tensor,
    TLDiagram.matching_id, matching_coeval, pv_cast_eq, pv_insert_eq, tensorObj_as, tensorUnit_as]
  funext q
  by_cases h0 : q = 0
  · subst h0
    simp [insertFn, shiftGap, pv_nested]
    omega
  by_cases h1 : q = 1
  · subst h1
    simp [insertFn, shiftGap, pv_nested]
  by_cases h2 : q = 2
  · subst h2
    simp [insertFn, shiftGap, pv_nested]
  by_cases h3 : q < 3 + (n + n)
  · rw [insertFn_of_le_of_lt _ _ (by omega) h3, insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega), pv_nested n (by omega),
      pv_nested n (by omega), shiftGap_of_le (by omega)]
    omega
  by_cases h4 : q = 3 + (n + n)
  · subst h4
    rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega)]
    rw [show 3 + (n + n) - (1 + 1) - (0 + (n + n)) = 1 by omega,
      show 3 + (n + n) - (n + n) = 3 by omega]
    simp [pv_nested, shiftGap]
  · rw [insertFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

open PlanarMatching in
/-- The nested coevaluation on `n + 1` strands is obtained by nesting `coeval n` inside `cup`. -/
theorem coeval_succ (n : ℕ) :
    coeval (n + 1) =
      coeval 1 ≫ (of 1 ◁ coeval n) ▷ of 1 ≫ eqToHom (by ext; simp; omega) := by
  apply hom_ext
  let x : PlanarMatching (5 + 1) :=
    PlanarMatching.cast (by simp) ((coeval 1).diagram.matching.append (nested 2))
  have hApp :
      pv ((coeval 1).diagram.matching.append ((of 1 ◁ coeval n) ▷ of 1).diagram.matching) =
        insertFn 5 1 (n + n) (pv x) (pv (nested n)) := by
    rw [pv_append_eq, pv_whiskerLeft_coeval_whiskerRight]
    simp only [tensorObj_as, tensorUnit_as]
    have h1 : 0 + (1 + 1) = 2 := rfl
    have h2 : 1 + 0 + 1 + (1 + (n + n) + 1) = 3 + (n + n) + 1 := by omega
    rw [h1, h2]
    have hR := appendFn_insertFn_right (k := 2) (a := 3) (b := 1) (l := n + n)
      (PlanarMatching.cast (by simp) (coeval 1).diagram.matching) (nested 2) (nested n)
    simpa only [x, pv_cast_eq, pv_append_eq, tensorObj_as, tensorUnit_as] using hR
  have hL := glueFn_insertFn_left (b := 1) (n := 0) (nested n) 2 5 x (by omega)
  have hbase : glueFn 0 2 (pv x) = pv (nested 1) := by
    have hcid := congrArg (fun d => pv d.matching) (TLDiagram.comp_id (coeval 1).diagram)
    rw [TLDiagram.matching_comp, TLDiagram.matching_id, pv_glueMiddle] at hcid
    have hcid' : glueFn 0 2 (pv x) = pv (coeval 1).diagram.matching := by
      dsimp only [x]
      rw [pv_cast_eq]
      exact hcid
    rw [hcid', matching_coeval, pv_cast_eq]
  have hbasec : glueCircles 0 2 (pv x) = 0 := by
    have hcid := congrArg TLDiagram.circles (TLDiagram.comp_id (coeval 1).diagram)
    simp only [TLDiagram.circles_comp, TLDiagram.circles_id, TLDiagram.matching_id, circles_coeval,
      zero_add, glueMiddleCircles_eq] at hcid
    dsimp only [x]
    rw [pv_cast_eq]
    exact hcid
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_coeval, pv_cast_eq, ← Category.assoc, matching_comp_eqToHom, pv_cast_eq,
      diagram_comp, TLDiagram.matching_comp, pv_glueMiddle]
    simp only [tensorObj_as, tensorUnit_as]
    rw [hApp, hL.1, hbase]
    have hins := congrArg pv (insert_nested 1 n)
    rw [pv_insert_eq, pv_cast_eq] at hins
    have hadd : 1 + n = n + 1 := Nat.add_comm 1 n
    have hsub : 5 - 2 * 2 = 1 := rfl
    rw [hsub, ← hadd]
    exact hins.symm
  · rw [circles_coeval, ← Category.assoc, circles_comp_eqToHom, diagram_comp,
      TLDiagram.circles_comp, glueMiddleCircles_eq]
    simp only [tensorObj_as, tensorUnit_as]
    rw [hApp, hL.2, hbasec, circles_coeval, diagram_whiskerRight, diagram_whiskerLeft,
      TLDiagram.circles_tensor, TLDiagram.circles_tensor, TLDiagram.circles_id, circles_coeval]

open PlanarMatching in
/-- Helper expressing the partner function of `of n ◁ (cap ▷ of n)` as inserting `nested 1`
at position `n` into `nested (2 * n)`. -/
private theorem pv_whiskerLeft_cap_whiskerRight (n : ℕ) :
    pv (of n ◁ (cap ▷ of n)).diagram.matching =
      insertFn n (3 * n) 2 (pv (nested (2 * n))) (pv (nested 1)) := by
  simp only [diagram_whiskerLeft, diagram_whiskerRight, TLDiagram.matching_tensor,
    TLDiagram.matching_id, diagram_cap, pv_cast_eq, pv_insert_eq, tensorObj_as]
  have hcap : pv TLDiagram.cap.matching = pv (nested 1) := by
    rw [eq_nested_one TLDiagram.cap.matching]
  rw [hcap]
  funext q
  by_cases h1 : q < n
  · rw [insertFn_of_lt _ _ h1, insertFn_of_lt _ _ h1, pv_nested n (by omega),
      pv_nested (2 * n) (by omega), shiftGap_of_le (by omega), shiftGap_of_le (by omega)]
    omega
  by_cases h2 : q < n + 2
  · rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega),
      insertFn_of_le_of_lt _ _ (by omega) h2, pv_nested 1 (by omega), shiftGap_of_lt (by omega)]
  by_cases h3 : q < n + 2 + (n + n)
  · rw [insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      pv_nested n (by omega), pv_nested (2 * n) (by omega), shiftGap_of_le (by omega)]
    omega
  by_cases h4 : q < n + 2 + 3 * n
  · rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) h4,
      pv_nested n (by omega), pv_nested (2 * n) (by omega),
      shiftGap_of_lt (by omega), shiftGap_of_lt (by omega)]
    omega
  · rw [insertFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

open PlanarMatching in
/-- The nested evaluation on `n + 1` strands is obtained by capping the inner two strands and
applying `eval n`. -/
theorem eval_succ (n : ℕ) :
    eval (n + 1) =
      eqToHom (by ext; simp; omega) ≫ of n ◁ (cap ▷ of n) ≫
        eqToHom (by ext; simp) ≫ eval n := by
  apply hom_ext
  let e2 : of n ⊗ (𝟙_ TLDiagCat ⊗ of n) ⟶ of n ⊗ of n := eqToHom (by ext; simp)
  let x : PlanarMatching (n + 5 * n) :=
    PlanarMatching.cast (by simp; omega) ((nested (2 * n)).append (eval n).diagram.matching)
  have hApp :
      pv ((of n ◁ (cap ▷ of n)).diagram.matching.append (e2 ≫ eval n).diagram.matching) =
        insertFn n (5 * n) 2 (pv x) (pv (nested 1)) := by
    rw [pv_append_eq, pv_whiskerLeft_cap_whiskerRight, matching_eqToHom_comp, pv_cast_eq]
    simp only [tensorObj_as, tensorUnit_as]
    have h1 : n + (2 + n) + (n + (0 + n)) = n + 2 + 3 * n := by omega
    have h2 : n + (0 + n) + 0 = n + n := by omega
    rw [h1, h2]
    have hL := appendFn_insertFn_left (a := n) (b := 3 * n) (l := 2) (k := n + n)
      (PlanarMatching.cast (by omega) (nested (2 * n))) (nested 1)
      (PlanarMatching.cast (by simp) (eval n).diagram.matching)
    have h3 : 3 * n + (n + n) = 5 * n := by omega
    have h4 : n + 3 * n = 2 * n + 2 * n := by omega
    have h5 : n + n + 0 = n + n := Nat.add_zero _
    simpa only [x, h3, h4, h5, pv_cast_eq, pv_append_eq, tensorObj_as, tensorUnit_as] using hL
  have hR := glueFn_insertFn_right (a := n) (n := 2 * n) (nested 1) (2 * n) (5 * n) x
    (by omega) (by omega)
  have hbase : glueFn (2 * n) (2 * n) (pv x) = pv (nested n) := by
    have hgm := congrArg pv (glueMiddle_nested_append
      (PlanarMatching.cast (by simp; omega) (eval n).diagram.matching : PlanarMatching (2 * n + 0)))
    rw [pv_glueMiddle, pv_cast_eq] at hgm
    have h2n : n + n + 0 = 2 * n + 0 := by omega
    have hgm' : glueFn (2 * n) (2 * n) (pv x) = pv (eval n).diagram.matching := by
      simpa only [x, h2n, pv_cast_eq, pv_append_eq, tensorObj_as, tensorUnit_as] using hgm
    rw [hgm', matching_eval]
  have hbasec : glueCircles (2 * n) (2 * n) (pv x) = 0 := by
    have hgc := glueMiddleCircles_nested_append
      (PlanarMatching.cast (by simp; omega) (eval n).diagram.matching : PlanarMatching (2 * n + 0))
    rw [glueMiddleCircles_eq] at hgc
    have h2n : n + n + 0 = 2 * n + 0 := by omega
    simpa only [x, h2n, pv_cast_eq, pv_append_eq, tensorObj_as, tensorUnit_as] using hgc
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_eval, matching_eqToHom_comp, pv_cast_eq, diagram_comp, TLDiagram.matching_comp,
      pv_glueMiddle]
    simp only [tensorObj_as]
    rw [show n + (2 + n) = 2 * n + 2 by omega, show n + (0 + n) = 2 * n by omega, hApp, hR.1,
      hbase, show 5 * n - 2 * (2 * n) = n by omega]
    have hins := congrArg pv (insert_nested n 1)
    rw [pv_insert_eq, pv_cast_eq] at hins
    exact hins.symm
  · rw [circles_eval, circles_eqToHom_comp, diagram_comp, TLDiagram.circles_comp,
      glueMiddleCircles_eq]
    simp only [tensorObj_as]
    rw [show n + (2 + n) = 2 * n + 2 by omega, show n + (0 + n) = 2 * n by omega, hApp, hR.2,
      hbasec, circles_eqToHom_comp, circles_eval, diagram_whiskerLeft, diagram_whiskerRight,
      TLDiagram.circles_tensor, TLDiagram.circles_tensor, TLDiagram.circles_id,
      diagram_cap, TLDiagram.circles_cap]

open PlanarMatching in
/-- Helper expressing the partner function of `of 1 ◁ (eval n ▷ of 1)` as inserting `nested n`
at position `1` into `nested 2`. -/
private theorem pv_whiskerLeft_eval_whiskerRight (n : ℕ) :
    pv (of 1 ◁ (eval n ▷ of 1)).diagram.matching =
      insertFn 1 3 (n + n) (pv (nested 2)) (pv (nested n)) := by
  simp only [diagram_whiskerLeft, diagram_whiskerRight, TLDiagram.matching_tensor,
    TLDiagram.matching_id, matching_eval, pv_cast_eq, pv_insert_eq, tensorObj_as, tensorUnit_as]
  funext q
  by_cases h0 : q = 0
  · subst h0
    simp [insertFn, shiftGap, pv_nested]
    omega
  by_cases h1 : q < 1 + (n + n)
  · rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega),
      insertFn_of_le_of_lt _ _ (by omega) h1, pv_nested n (by omega), shiftGap_of_lt (by omega)]
  by_cases h2 : q = 1 + (n + n)
  · subst h2
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega)]
    simp [pv_nested, shiftGap]
    omega
  by_cases h3 : q = 2 + (n + n)
  · subst h3
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega)]
    simp [pv_nested, shiftGap]
  by_cases h4 : q = 3 + (n + n)
  · subst h4
    rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega)]
    rw [show 3 + (n + n) - (n + n + 1 + (0 + 1)) = 1 by omega,
      show 3 + (n + n) - (n + n) = 3 by omega]
    simp [pv_nested, shiftGap]
  · rw [insertFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

open PlanarMatching in
/-- The nested evaluation on `n + 1` strands can also be factored by applying `eval n` on the
inner `2n` strands and then capping the outer two strands. -/
theorem eval_succ_outer (n : ℕ) :
    eval (n + 1) =
      eqToHom (by ext; simp; omega) ≫ of 1 ◁ (eval n ▷ of 1) ≫
        eqToHom (by ext; simp) ≫ cap := by
  apply hom_ext
  let e2 : of 1 ⊗ (𝟙_ TLDiagCat ⊗ of 1) ⟶ of 2 := eqToHom (by ext; simp)
  let x : PlanarMatching (1 + 5) :=
    PlanarMatching.cast (by omega) ((nested 2).append TLDiagram.cap.matching)
  have hApp :
      pv ((of 1 ◁ (eval n ▷ of 1)).diagram.matching.append (e2 ≫ cap).diagram.matching) =
        insertFn 1 5 (n + n) (pv x) (pv (nested n)) := by
    rw [pv_append_eq, pv_whiskerLeft_eval_whiskerRight, matching_eqToHom_comp, pv_cast_eq,
      diagram_cap]
    simp only [tensorObj_as, tensorUnit_as]
    have h1 : 1 + (n + n + 1) + (1 + (0 + 1)) = 1 + (n + n) + 3 := by omega
    rw [h1]
    have hL := appendFn_insertFn_left (a := 1) (b := 3) (l := n + n) (k := 2)
      (nested 2) (nested n) TLDiagram.cap.matching
    simpa only [x, pv_cast_eq, pv_append_eq] using hL
  have hR := glueFn_insertFn_right (a := 1) (n := 2) (nested n) 2 5 x (by omega) (by omega)
  have hbase : glueFn 2 2 (pv x) = pv (nested 1) := by
    have hgm := congrArg pv (glueMiddle_nested_append (n := 2) (p := 0) TLDiagram.cap.matching)
    rw [pv_glueMiddle] at hgm
    have hgm' : glueFn 2 2 (pv x) = pv TLDiagram.cap.matching := by
      simpa only [x, pv_cast_eq, pv_append_eq] using hgm
    rw [hgm', eq_nested_one TLDiagram.cap.matching]
  have hbasec : glueCircles 2 2 (pv x) = 0 := by
    have hgc := glueMiddleCircles_nested_append (n := 2) (p := 0) TLDiagram.cap.matching
    rw [glueMiddleCircles_eq] at hgc
    simpa only [x, pv_cast_eq, pv_append_eq] using hgc
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_eval, matching_eqToHom_comp, pv_cast_eq, diagram_comp, TLDiagram.matching_comp,
      pv_glueMiddle]
    simp only [tensorObj_as, tensorUnit_as]
    rw [show 1 + (n + n + 1) = 2 + (n + n) by omega, show 1 + (0 + 1) = 2 by omega, hApp, hR.1,
      hbase]
    have hins := congrArg pv (insert_nested 1 n)
    rw [pv_insert_eq, pv_cast_eq] at hins
    have hadd : 1 + n = n + 1 := Nat.add_comm 1 n
    have hsub : 5 - 2 * 2 = 1 := rfl
    rw [hsub, ← hadd]
    exact hins.symm
  · rw [circles_eval, circles_eqToHom_comp, diagram_comp, TLDiagram.circles_comp,
      glueMiddleCircles_eq]
    simp only [tensorObj_as, tensorUnit_as]
    rw [show 1 + (n + n + 1) = 2 + (n + n) by omega, show 1 + (0 + 1) = 2 by omega, hApp, hR.2,
      hbasec, circles_eqToHom_comp, diagram_cap, TLDiagram.circles_cap, diagram_whiskerLeft,
      diagram_whiskerRight, TLDiagram.circles_tensor, TLDiagram.circles_tensor,
      TLDiagram.circles_id, circles_eval]

/-! ### Self-duality and the rigid monoidal category structure -/

open PlanarMatching in
/-- The two zigzag identities at the generating object `of 1`. -/
private theorem zigzag_one_left :
    of 1 ◁ coeval 1 ≫ (α_ (of 1) (of 1) (of 1)).inv ≫ eval 1 ▷ of 1 =
      (ρ_ (of 1)).hom ≫ (λ_ (of 1)).inv := by
  apply hom_ext
  ext : 1
  · exact (eq_nested_one _).trans (eq_nested_one _).symm
  · have hrhs : ((ρ_ (of 1)).hom ≫ (λ_ (of 1)).inv).diagram.circles = 0 := by
      rw [rightUnitor_hom, leftUnitor_eq, eqToIso.inv]
      have hcomp : 𝟙 (of 1) ≫ eqToHom (congrArg of (Nat.zero_add 1)).symm =
          eqToHom (congrArg of (Nat.zero_add 1)).symm := Category.id_comp _
      rw [hcomp, circles_eqToHom]
    have hpv :
        pv ((of 1 ◁ cup).diagram.matching.append
            ((eqToHom (congrArg of (Nat.add_assoc 1 1 1)).symm ≫ cap ▷ of 1).diagram.matching)) =
          fun q => if q = 0 then 3 else if q = 1 then 2 else if q = 2 then 1 else
            if q = 3 then 0 else if q = 4 then 5 else if q = 5 then 4 else
            if q = 6 then 7 else if q = 7 then 6 else q := by
      rw [pv_append_eq, matching_eqToHom_comp, pv_cast_eq, diagram_whiskerLeft,
        diagram_whiskerRight, TLDiagram.matching_tensor, TLDiagram.matching_tensor,
        TLDiagram.matching_id, diagram_cup, diagram_cap, pv_cast_eq, pv_cast_eq,
        pv_insert_eq, pv_insert_eq, eq_nested_one TLDiagram.cup.matching,
        eq_nested_one TLDiagram.cap.matching]
      simp only [tensorObj_as]
      funext q
      match q with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [appendFn, insertFn, shiftGap, pv_nested]
      | q + 8 =>
        rw [appendFn_of_le _ _ (by omega)]
        simp
    rw [hrhs, coeval_one, eval_one, associator_eq, eqToIso.inv, diagram_comp,
      TLDiagram.circles_comp, glueMiddleCircles_eq]
    simp only [tensorObj_as, tensorUnit_as]
    rw [hpv, circles_eqToHom_comp, diagram_whiskerLeft, diagram_whiskerRight,
      TLDiagram.circles_tensor, TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cup,
      diagram_cap, TLDiagram.circles_cup, TLDiagram.circles_cap]
    decide

open PlanarMatching in
private theorem zigzag_one_right :
    coeval 1 ▷ of 1 ≫ (α_ (of 1) (of 1) (of 1)).hom ≫ of 1 ◁ eval 1 =
      (λ_ (of 1)).hom ≫ (ρ_ (of 1)).inv := by
  apply hom_ext
  ext : 1
  · exact (eq_nested_one _).trans (eq_nested_one _).symm
  · have hrhs : ((λ_ (of 1)).hom ≫ (ρ_ (of 1)).inv).diagram.circles = 0 := by
      rw [leftUnitor_eq, eqToIso.hom, rightUnitor_inv]
      have hcomp : eqToHom (congrArg of (Nat.zero_add 1)) ≫ 𝟙 (of 1) =
          eqToHom (congrArg of (Nat.zero_add 1)) := Category.comp_id _
      rw [hcomp, circles_eqToHom]
    have hpv :
        pv ((cup ▷ of 1).diagram.matching.append
            ((eqToHom (congrArg of (Nat.add_assoc 1 1 1)) ≫ of 1 ◁ cap).diagram.matching)) =
          fun q => if q = 0 then 1 else if q = 1 then 0 else if q = 2 then 3 else
            if q = 3 then 2 else if q = 4 then 7 else if q = 5 then 6 else
            if q = 6 then 5 else if q = 7 then 4 else q := by
      rw [pv_append_eq, matching_eqToHom_comp, pv_cast_eq, diagram_whiskerRight,
        diagram_whiskerLeft, TLDiagram.matching_tensor, TLDiagram.matching_tensor,
        TLDiagram.matching_id, diagram_cup, diagram_cap, pv_cast_eq, pv_cast_eq,
        pv_insert_eq, pv_insert_eq, eq_nested_one TLDiagram.cup.matching,
        eq_nested_one TLDiagram.cap.matching]
      simp only [tensorObj_as]
      funext q
      match q with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [appendFn, insertFn, shiftGap, pv_nested]
      | q + 8 =>
        rw [appendFn_of_le _ _ (by omega)]
        simp
    rw [hrhs, coeval_one, eval_one, associator_eq, eqToIso.hom, diagram_comp,
      TLDiagram.circles_comp, glueMiddleCircles_eq]
    simp only [tensorObj_as, tensorUnit_as]
    rw [hpv, circles_eqToHom_comp, diagram_whiskerRight, diagram_whiskerLeft,
      TLDiagram.circles_tensor, TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cup,
      diagram_cap, TLDiagram.circles_cup, TLDiagram.circles_cap]
    decide

/-- Both zigzag identities hold for `coeval n` and `eval n` at every `n : ℕ`, proved by induction
using `ExactPairing.tensor` and `exactPairingCongrLeft`. -/
private theorem zigzags_of (n : ℕ) :
    (of n ◁ coeval n ≫ (α_ (of n) (of n) (of n)).inv ≫ eval n ▷ of n =
      (ρ_ (of n)).hom ≫ (λ_ (of n)).inv) ∧
    (coeval n ▷ of n ≫ (α_ (of n) (of n) (of n)).hom ≫ of n ◁ eval n =
      (λ_ (of n)).hom ≫ (ρ_ (of n)).inv) := by
  induction n with
  | zero =>
    exact ⟨exactPairingUnit.coevaluation_evaluation', exactPairingUnit.evaluation_coevaluation'⟩
  | succ n ih =>
    let p1 : ExactPairing (of 1) (of 1) :=
      { coevaluation' := coeval 1
        evaluation' := eval 1
        coevaluation_evaluation' := zigzag_one_left
        evaluation_coevaluation' := zigzag_one_right }
    let pn : ExactPairing (of n) (of n) :=
      { coevaluation' := coeval n
        evaluation' := eval n
        coevaluation_evaluation' := ih.1
        evaluation_coevaluation' := ih.2 }
    let pt : ExactPairing (of 1 ⊗ of n) (of n ⊗ of 1) := @ExactPairing.tensor _ _ _ _ _ _ _ p1 pn
    let ι : of (n + 1) ≅ of 1 ⊗ of n := eqToIso (congrArg of (Nat.add_comm n 1))
    let p : ExactPairing (of (n + 1)) (of (n + 1)) := @exactPairingCongrLeft _ _ _ _ _ _ pt ι
    have hcoev : p.coevaluation' = coeval (n + 1) := by
      -- Expand `ExactPairing.tensor_coevaluation` in an arbitrary monoidal category because
      -- `of 1 ⊗ 𝟙_ TLDiagCat` is definitionally `of 1`, which confuses `monoidal` directly.
      have htensor :
          ∀ {C : Type} [Category.{0} C] [MonoidalCategory C] {X₁ X₂ Y₁ Y₂ : C}
            [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂],
            η_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) =
              η_ X₁ Y₁ ≫ (ρ_ X₁).inv ▷ Y₁ ≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ ≫
                (α_ X₁ X₂ Y₂).inv ▷ Y₁ ≫ (α_ (X₁ ⊗ X₂) Y₂ Y₁).hom := by
        intro C _ _ X₁ X₂ Y₁ Y₂ _ _
        rw [ExactPairing.tensor_coevaluation]
        monoidal
      have h1 :
          p.coevaluation' =
            (coeval 1 ≫ (ρ_ (of 1)).inv ▷ of 1 ≫ (of 1 ◁ coeval n) ▷ of 1 ≫
              (α_ (of 1) (of n) (of n)).inv ▷ of 1 ≫
              (α_ (of 1 ⊗ of n) (of n) (of 1)).hom) ≫ ι.inv ▷ (of n ⊗ of 1) :=
        congrArg (· ≫ ι.inv ▷ (of n ⊗ of 1)) (@htensor _ _ _ _ _ _ _ p1 pn)
      rw [h1, rightUnitor_inv, id_whiskerRight, Category.id_comp, coeval_succ n]
      simp only [ι, associator_eq, eqToIso.hom, eqToIso.inv, eqToHom_whiskerRight, eqToHom_trans,
        Category.assoc]
    have hev : p.evaluation' = eval (n + 1) := by
      have htensor :
          ∀ {C : Type} [Category.{0} C] [MonoidalCategory C] {X₁ X₂ Y₁ Y₂ : C}
            [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂],
            ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) =
              (α_ Y₂ Y₁ (X₁ ⊗ X₂)).hom ≫ Y₂ ◁ (α_ Y₁ X₁ X₂).inv ≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ≫
                Y₂ ◁ (λ_ X₂).hom ≫ ε_ X₂ Y₂ := by
        intro C _ _ X₁ X₂ Y₁ Y₂ _ _
        rw [ExactPairing.tensor_evaluation]
        monoidal
      have h1 :
          p.evaluation' =
            (of n ⊗ of 1) ◁ ι.hom ≫ ((α_ (of n) (of 1) (of 1 ⊗ of n)).hom ≫
              of n ◁ (α_ (of 1) (of 1) (of n)).inv ≫ of n ◁ (eval 1 ▷ of n) ≫
              of n ◁ (λ_ (of n)).hom ≫ eval n) :=
        congrArg ((of n ⊗ of 1) ◁ ι.hom ≫ ·) (@htensor _ _ _ _ _ _ _ p1 pn)
      rw [h1, eval_one, eval_succ]
      simp only [ι, associator_eq, leftUnitor_eq, eqToIso.hom, eqToIso.inv,
        whiskerLeft_eqToHom, eqToHom_trans_assoc]
    exact ⟨by simpa only [hcoev, hev] using p.coevaluation_evaluation',
      by simpa only [hcoev, hev] using p.evaluation_coevaluation'⟩

/-- Left zigzag identity for the nested coevaluation and evaluation on `n` strands. -/
theorem coeval_zigzag_left (n : ℕ) :
    of n ◁ coeval n ≫ (α_ (of n) (of n) (of n)).inv ≫ eval n ▷ of n =
      (ρ_ (of n)).hom ≫ (λ_ (of n)).inv :=
  (zigzags_of n).1

/-- Right zigzag identity for the nested coevaluation and evaluation on `n` strands. -/
theorem coeval_zigzag_right (n : ℕ) :
    coeval n ▷ of n ≫ (α_ (of n) (of n) (of n)).hom ≫ of n ◁ eval n =
      (λ_ (of n)).hom ≫ (ρ_ (of n)).inv :=
  (zigzags_of n).2

@[expose] section RigidInstances

/-- Every object `X = of n` of `TLDiagCat` is canonically self-dual via the nested coevaluation
and evaluation. Not registered as a blanket instance for all `X` to avoid diamonds with
`ExactPairing.tensor`; see `instExactPairingOfOne` for the generating object `of 1` and
`instHasRightDual` / `instHasLeftDual` for the rigid structure. -/
@[instance_reducible]
def selfExactPairing (X : TLDiagCat) : ExactPairing X X where
  coevaluation' := coeval X.as
  evaluation' := eval X.as
  coevaluation_evaluation' := coeval_zigzag_left X.as
  evaluation_coevaluation' := coeval_zigzag_right X.as

/-- The generating object `of 1` carries the canonical self-duality given by `cup` and `cap`. -/
instance instExactPairingOfOne : ExactPairing (of 1) (of 1) :=
  selfExactPairing (of 1)

instance instHasRightDual (X : TLDiagCat) : HasRightDual X where
  rightDual := X
  exact := selfExactPairing X

instance instHasLeftDual (X : TLDiagCat) : HasLeftDual X where
  leftDual := X
  exact := selfExactPairing X

instance instRightRigidCategory : RightRigidCategory TLDiagCat where

instance instLeftRigidCategory : LeftRigidCategory TLDiagCat where

instance instRigidCategory : RigidCategory TLDiagCat where

end RigidInstances

-- Verify zero diamonds with Mathlib's unit duality instances and the ambient pairing on `of 1`.
example : selfExactPairing (𝟙_ TLDiagCat) = exactPairingUnit := rfl
example : instHasRightDual (𝟙_ TLDiagCat) = hasRightDualUnit := rfl
example : instHasLeftDual (𝟙_ TLDiagCat) = hasLeftDualUnit := rfl
example : instExactPairingOfOne = HasRightDual.exact (X := of 1) := rfl
example : instExactPairingOfOne = HasLeftDual.exact (Y := of 1) := rfl

@[simp]
theorem rightDual_eq (X : TLDiagCat) : (Xᘁ : TLDiagCat) = X :=
  (rfl)

@[simp]
theorem leftDual_eq (X : TLDiagCat) : (ᘁX : TLDiagCat) = X :=
  (rfl)

@[simp]
theorem coevaluation_rightDual (X : TLDiagCat) : η_ X Xᘁ = coeval X.as :=
  (rfl)

@[simp]
theorem evaluation_rightDual (X : TLDiagCat) : ε_ X Xᘁ = eval X.as :=
  (rfl)

@[simp]
theorem coevaluation_leftDual (X : TLDiagCat) : η_ (ᘁX) X = coeval X.as :=
  (rfl)

@[simp]
theorem evaluation_leftDual (X : TLDiagCat) : ε_ (ᘁX) X = eval X.as :=
  (rfl)

@[simp]
theorem coevaluation_of_one : η_ (of 1) (of 1) = cup :=
  coeval_one

@[simp]
theorem evaluation_of_one : ε_ (of 1) (of 1) = cap :=
  eval_one

/-- Closing `n` nested strands produces `n` closed circles. -/
theorem coeval_comp_eval (n : ℕ) : coeval n ≫ eval n = ((End.of circle) ^ n).asHom := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact Category.id_comp (𝟙 (of 0))
  | succ n ih =>
    let s : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat := ((End.of circle) ^ n).asHom
    have hmid :
        eqToHom (by ext; simp; omega :
            (of 1 ⊗ (of n ⊗ of n)) ⊗ of 1 = of (n + 1) ⊗ of (n + 1)) ≫
          eqToHom (by ext; simp; omega :
            of (n + 1) ⊗ of (n + 1) = of 1 ⊗ ((of n ⊗ of n) ⊗ of 1)) =
          (α_ (of 1) (of n ⊗ of n) (of 1)).hom := by
      simp [associator_eq]
      rfl
    have hbot :
        eqToHom (by ext; simp : of 1 ⊗ (𝟙_ TLDiagCat ⊗ of 1) = of 2) =
          of 1 ◁ (λ_ (of 1)).hom := by
      rw [leftUnitor_eq, eqToIso.hom, whiskerLeft_eqToHom]
    calc
      coeval (n + 1) ≫ eval (n + 1)
          = coeval 1 ≫ (of 1 ◁ coeval n) ▷ of 1 ≫
              (α_ (of 1) (of n ⊗ of n) (of 1)).hom ≫ of 1 ◁ (eval n ▷ of 1) ≫
              of 1 ◁ (λ_ (of 1)).hom ≫ eval 1 := by
            rw [coeval_succ n, eval_succ_outer]
            simp only [Category.assoc]
            rw [← Category.assoc (eqToHom _) (eqToHom _), hmid, hbot, eval_one]
      _ = coeval 1 ≫ (α_ (of 1) (𝟙_ TLDiagCat) (of 1)).hom ≫
            of 1 ◁ ((coeval n ≫ eval n) ▷ of 1 ≫ (λ_ (of 1)).hom) ≫ eval 1 := by
            rw [← Category.assoc ((of 1 ◁ coeval n) ▷ of 1),
              associator_naturality_middle (of 1) (coeval n) (of 1)]
            simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp,
              MonoidalCategory.comp_whiskerRight]
      _ = coeval 1 ≫ (α_ (of 1) (𝟙_ TLDiagCat) (of 1)).hom ≫
            of 1 ◁ ((λ_ (of 1)).hom ≫ (λ_ (of 1)).inv ≫ s ▷ of 1 ≫ (λ_ (of 1)).hom) ≫ eval 1 := by
            rw [ih]
            simp only [s, Iso.hom_inv_id_assoc]
      _ = coeval 1 ≫ (α_ (of 1) (𝟙_ TLDiagCat) (of 1)).hom ≫
            of 1 ◁ ((λ_ (of 1)).hom ≫ (ρ_ (of 1)).inv ≫ of 1 ◁ s ≫ (ρ_ (of 1)).hom) ≫ eval 1 := by
            rw [← (circlesCommuteAt_iff s (of 1)).mp (circlesCommuteAt s (of 1))]
      _ = coeval 1 ≫ (of 1 ⊗ of 1) ◁ s ≫ eval 1 := by
            have h1 : (α_ (of 1) (𝟙_ TLDiagCat) (of 1)).hom ≫ of 1 ◁ (λ_ (of 1)).hom =
                𝟙 (of 1 ⊗ of 1) := by
              rw [associator_eq, leftUnitor_eq, eqToIso.hom, eqToIso.hom, whiskerLeft_eqToHom,
                eqToHom_trans]
              rfl
            have h2 : of 1 ◁ (of 1 ◁ s) = (of 1 ⊗ of 1) ◁ s := by
              have ha := associator_naturality_right (of 1) (of 1) s
              have ha1 : (α_ (of 1) (of 1) (𝟙_ TLDiagCat)).hom = 𝟙 (of 1 ⊗ of 1) := by
                rw [associator_eq, eqToIso.hom]
                rfl
              have hc : (of 1 ⊗ of 1) ◁ s ≫ 𝟙 (of 1 ⊗ of 1) = (of 1 ⊗ of 1) ◁ s :=
                Category.comp_id ((of 1 ⊗ of 1) ◁ s)
              have hid : 𝟙 (of 1 ⊗ of 1) ≫ of 1 ◁ (of 1 ◁ s) = of 1 ◁ (of 1 ◁ s) :=
                Category.id_comp (of 1 ◁ (of 1 ◁ s))
              rw [ha1, hid, hc] at ha
              exact ha.symm
            have h3 : (ρ_ (of 1)).inv ≫ of 1 ◁ s ≫ (ρ_ (of 1)).hom = of 1 ◁ s := by
              rw [rightUnitor_inv, rightUnitor_hom, Category.id_comp]
              exact Category.comp_id (of 1 ◁ s)
            have hid2 : 𝟙 (of 1 ⊗ of 1) ≫ (of 1 ⊗ of 1) ◁ s = (of 1 ⊗ of 1) ◁ s :=
              Category.id_comp ((of 1 ⊗ of 1) ◁ s)
            rw [h3, MonoidalCategory.whiskerLeft_comp, h2]
            simp only [Category.assoc]
            rw [← Category.assoc (α_ _ _ _).hom, h1, ← Category.assoc (𝟙 (of 1 ⊗ of 1)), hid2]
      _ = (coeval 1 ≫ eval 1) ≫ s := by
            rw [whiskerLeft_scalar_comp (Y := of 1 ⊗ of 1) s (eval 1), ← Category.assoc]
      _ = ((End.of circle) ^ (n + 1)).asHom := by
            rw [coeval_one, eval_one, cup_comp_cap, pow_succ', End.mul_asHom]
            exact scalar_comm circle s

/-! ### Corner-dragging and Frobenius reciprocity -/

open PlanarMatching in
/-- Dragging the top-right corner down via `tensorRightHomEquiv` at `of 1` agrees with
`(TLDiagram.dragRight n m).symm`. -/
theorem diagram_tensorRightHomEquiv_symm (n m : ℕ) (g : of n ⟶ of m ⊗ of 1) :
    ((tensorRightHomEquiv (of n) (of 1) (of 1) (of m)).symm g).diagram =
      (TLDiagram.dragRight n m).symm g.diagram := by
  have hdef :
      (tensorRightHomEquiv (of n) (of 1) (of 1) (of m)).symm g =
        g ▷ of 1 ≫ eqToHom (congrArg of (Nat.add_assoc m 1 1)) ≫ of m ◁ cap := by
    dsimp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
    rw [evaluation_of_one, associator_eq, eqToIso.hom, rightUnitor_hom]
    have hcomp : of m ◁ cap ≫ 𝟙 (of m) = of m ◁ cap := Category.comp_id (of m ◁ cap)
    rw [hcomp]
  have hmcap :
      (of m ◁ cap).diagram.matching = PlanarMatching.cast (by simp; omega) (nested (m + 1)) := by
    rw [diagram_whiskerLeft, TLDiagram.matching_tensor, TLDiagram.matching_id, diagram_cap,
      eq_nested_one TLDiagram.cap.matching, insert_nested, PlanarMatching.cast_cast]
  have hsplit := glueFn_add (n + 1) 1 (m + 1)
    (pv ((g ▷ of 1).diagram.matching.append
      (eqToHom (congrArg of (Nat.add_assoc m 1 1)) ≫ of m ◁ cap).diagram.matching))
  have hadd : 1 + (m + 1) = m + 1 + 1 := by omega
  rw [hadd] at hsplit
  have hinner_m :
      glueFn (n + 1 + 1) (m + 1)
          (pv ((g ▷ of 1).diagram.matching.append
            (eqToHom (congrArg of (Nat.add_assoc m 1 1)) ≫ of m ◁ cap).diagram.matching)) =
        pv (g ▷ of 1).diagram.matching := by
    let w : PlanarMatching ((n + 1 + 1) + (m + 1)) :=
      PlanarMatching.cast (by simp; omega) (g ▷ of 1).diagram.matching
    have hgm := congrArg pv (glueMiddle_append_nested w)
    rw [pv_glueMiddle] at hgm
    have ha1 : n + 1 + (m + 1 + 1) = n + 1 + 1 + (m + 1) := by omega
    have ha2 : m + 1 + 1 + (m + 0) = m + 1 + (m + 1) := by omega
    simpa only [w, ha1, ha2, matching_eqToHom_comp, hmcap, pv_append_eq, pv_cast_eq,
      tensorObj_as] using hgm
  have hinner_c :
      glueCircles (n + 1 + 1) (m + 1)
          (pv ((g ▷ of 1).diagram.matching.append
            (eqToHom (congrArg of (Nat.add_assoc m 1 1)) ≫ of m ◁ cap).diagram.matching)) = 0 := by
    let w : PlanarMatching ((n + 1 + 1) + (m + 1)) :=
      PlanarMatching.cast (by simp; omega) (g ▷ of 1).diagram.matching
    have hgc := glueMiddleCircles_append_nested w
    rw [glueMiddleCircles_eq] at hgc
    have ha1 : n + 1 + (m + 1 + 1) = n + 1 + 1 + (m + 1) := by omega
    have ha2 : m + 1 + 1 + (m + 0) = m + 1 + (m + 1) := by omega
    simpa only [w, ha1, ha2, matching_eqToHom_comp, hmcap, pv_append_eq, pv_cast_eq,
      tensorObj_as] using hgc
  have hphi : pv (g ▷ of 1).diagram.matching =
      insertFn n (m + 1) 2 (pv g.diagram.matching) (pv (nested 1)) := by
    rw [diagram_whiskerRight, TLDiagram.matching_tensor, TLDiagram.matching_id, pv_cast_eq,
      pv_insert_eq]
    simp only [tensorObj_as]
  have hc1 :
      circleInd (n + 1) (insertFn n (m + 1) 2 (pv g.diagram.matching) (pv (nested 1))) = 0 := by
    rw [circleInd, insertFn_of_le_of_lt _ _ (by omega) (by omega), pv_nested 1 (by omega)]
    simp only [show n + (1 + 1 - 1 - (n + 1 - n)) ≠ n + 1 + 1 by omega, ↓reduceIte]
  have hstep :
      contractFn (n + 1) (insertFn n (m + 1) 2 (pv g.diagram.matching) (pv (nested 1))) =
        pv g.diagram.matching := by
    funext q
    rw [contractFn, erasePair_apply]
    have hφ1 : insertFn n (m + 1) 2 (pv g.diagram.matching) (pv (nested 1)) (n + 1) = n := by
      rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), pv_nested 1 (by omega)]; omega
    have hφ2 : insertFn n (m + 1) 2 (pv g.diagram.matching) (pv (nested 1)) (n + 2) =
        shiftGap n 2 (pv g.diagram.matching n) := by
      rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega), show n + 2 - 2 = n by omega]
    have : pv g.diagram.matching n ≠ n := pv_ne g.diagram.matching (by simp)
    have : pv g.diagram.matching n < n + (m + 1) := by
      simpa using pv_lt g.diagram.matching (by simp)
    by_cases h1 : q < n
    · have : pv g.diagram.matching q < n + (m + 1) := by
        simpa using pv_lt g.diagram.matching (by simp; omega)
      rw [skipN_of_lt (by omega), splice_of_ne _ (by omega) (by omega),
        insertFn_of_lt _ _ h1]
      by_cases hqn : pv g.diagram.matching q = n
      · rw [hqn, shiftGap_of_le (by omega), rejoin_of_eq_right _ rfl, hφ1, unskipN_of_lt (by omega)]
      · rw [rejoin_of_ne]
        · simp only [shiftGap, unskipN]; split_ifs <;> omega
        · simp only [shiftGap]; split_ifs <;> omega
        · simp only [shiftGap]; split_ifs <;> omega
    by_cases h2 : q = n
    · subst q
      rw [skipN_of_lt (by omega), splice_of_ne _ (by omega) (by omega),
        insertFn_of_le_of_lt _ _ le_rfl (by omega), pv_nested 1 (by omega),
        show n + (1 + 1 - 1 - (n - n)) = n + 1 by omega, rejoin_of_eq_left _ rfl, hφ2]
      simp only [shiftGap, unskipN]; split_ifs <;> omega
    by_cases h3 : q < n + (m + 1)
    · have : pv g.diagram.matching q < n + (m + 1) := by
        simpa using pv_lt g.diagram.matching (by simp; omega)
      rw [skipN_of_le (by omega), splice_of_ne _ (by omega) (by omega),
        insertFn_of_le_of_lt_add _ _ (by omega) (by omega), show q + 2 - 2 = q by omega]
      by_cases hqn : pv g.diagram.matching q = n
      · rw [hqn, shiftGap_of_le (by omega), rejoin_of_eq_right _ rfl, hφ1, unskipN_of_lt (by omega)]
      · rw [rejoin_of_ne]
        · simp only [shiftGap, unskipN]; split_ifs <;> omega
        · simp only [shiftGap]; split_ifs <;> omega
        · simp only [shiftGap]; split_ifs <;> omega
    · rw [skipN_of_le (by omega), splice_of_ne _ (by omega) (by omega),
        insertFn_of_le _ _ (by omega), rejoin_of_ne _ (by omega) (by omega),
        unskipN_of_le (by omega), pv_of_le g.diagram.matching (by simp; omega)]
      omega
  rw [hdef]
  ext : 1
  · apply eq_of_pv_eq
    rw [diagram_comp, TLDiagram.matching_comp, pv_glueMiddle]
    simp only [tensorObj_as]
    rw [hsplit.1, hinner_m, hphi, glueFn, glueFn, hstep, TLDiagram.matching_dragRight_symm,
      pv_cast_eq]
  · rw [diagram_comp, TLDiagram.circles_comp, glueMiddleCircles_eq]
    simp only [tensorObj_as]
    rw [hsplit.2, hinner_m, hinner_c, hphi, glueCircles, glueCircles, hc1, diagram_whiskerRight,
      TLDiagram.circles_tensor, TLDiagram.circles_id, circles_eqToHom_comp, diagram_whiskerLeft,
      TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cap, TLDiagram.circles_cap,
      TLDiagram.circles_dragRight_symm]
    omega

/-- Dragging the bottom-right corner up via `tensorRightHomEquiv` at `of 1` agrees with
`TLDiagram.dragRight n m`. -/
theorem diagram_tensorRightHomEquiv (n m : ℕ) (f : of n ⊗ of 1 ⟶ of m) :
    (tensorRightHomEquiv (of n) (of 1) (of 1) (of m) f).diagram =
      TLDiagram.dragRight n m f.diagram := by
  have h := diagram_tensorRightHomEquiv_symm n m (tensorRightHomEquiv (of n) (of 1) (of 1) (of m) f)
  rw [Equiv.symm_apply_apply] at h
  exact (Equiv.symm_apply_eq (TLDiagram.dragRight n m)).mp h.symm

open PlanarMatching in
/-- Partner-function characterization of a single counterclockwise rotation
`PlanarMatching.rotate`. -/
private theorem pv_rotate_eq {K : ℕ} (x : PlanarMatching K) (q : ℕ) :
    pv (PlanarMatching.rotate K x) q =
      if q < K then
        if q = 0 then pv x (K - 1) + 1
        else if pv x (q - 1) = K - 1 then 0 else pv x (q - 1) + 1
      else q := by
  by_cases hq : q < K
  · simp only [hq, ↓reduceIte]
    have hK : 0 < K := by omega
    let i : Fin K := ⟨(q + K - 1) % K, Nat.mod_lt _ hK⟩
    have hrot : ((PlanarMatching.rotate K x).1.val (finRotate K i) : ℕ) =
        ((finRotate K (x.1.val i)) : ℕ) :=
      congrArg Fin.val (PlanarMatching.rotate_apply_val_apply x i)
    have hfin1 : ((finRotate K i) : ℕ) = q := by
      have h1 : ((finRotate K i) : ℕ) = ((finRotate K ^ 1) i : ℕ) := by simp
      rw [h1, Fin.coe_finRotate_pow]
      dsimp only [i]
      by_cases h0 : q = 0
      · subst h0
        simp only [zero_add]
        rw [Nat.mod_eq_of_lt (show K - 1 < K by omega), show K - 1 + 1 = K by omega, Nat.mod_self]
      · have hmod : (q + K - 1) % K = q - 1 := by
          have : q + K - 1 = (q - 1) + K := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod, show q - 1 + 1 = q by omega, Nat.mod_eq_of_lt hq]
    have hfin2 : ((finRotate K (x.1.val i)) : ℕ) = (pv x ((q + K - 1) % K) + 1) % K := by
      have h1 : ((finRotate K (x.1.val i)) : ℕ) = ((finRotate K ^ 1) (x.1.val i) : ℕ) := by simp
      rw [h1, Fin.coe_finRotate_pow, ← pv_coe]
    rw [← pv_coe, hfin1, hfin2] at hrot
    rw [hrot]
    by_cases h0 : q = 0
    · subst h0
      simp only [↓reduceIte, zero_add, Nat.mod_eq_of_lt (by omega : K - 1 < K)]
      have hne := pv_ne x (by omega : K - 1 < K)
      have hlt := pv_lt x (by omega : K - 1 < K)
      exact Nat.mod_eq_of_lt (by omega)
    · simp only [h0, ↓reduceIte]
      have hmod : (q + K - 1) % K = q - 1 := by
        have : q + K - 1 = (q - 1) + K := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have hlt := pv_lt x (by omega : q - 1 < K)
      by_cases heq : pv x (q - 1) = K - 1
      · simp [heq, show K - 1 + 1 = K by omega]
      · simp [heq, Nat.mod_eq_of_lt (by omega : pv x (q - 1) + 1 < K)]
  · simp [hq, pv_of_le (PlanarMatching.rotate K x) (Nat.le_of_not_lt hq)]

open PlanarMatching in
/-- Combined matching and circle calculation for
`(tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm`. -/
private theorem tensorLeftHomEquiv_symm_aux (n m : ℕ) (g : of n ⟶ of 1 ⊗ of m) :
    ((tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm g).diagram.matching =
        PlanarMatching.cast (by simp; omega)
          (PlanarMatching.rotate (n + (1 + m)) g.diagram.matching) ∧
      ((tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm g).diagram.circles =
        g.diagram.circles := by
  have hdef :
      (tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm g =
        (of 1 ◁ g ≫ (eqToHom (congrArg of (Nat.add_assoc 1 1 m).symm) ≫ cap ▷ of m)) ≫
          eqToHom (congrArg of (Nat.zero_add m)) := by
    dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
    rw [evaluation_of_one, associator_eq, leftUnitor_eq, eqToIso.inv, eqToIso.hom]
    simp only [Category.assoc]
  let K := n + (1 + m)
  let base : PlanarMatching (1 + n + (1 + (1 + m))) := (of 1 ◁ g).diagram.matching
  let mid : PlanarMatching (K + 2 + 2) := PlanarMatching.cast (by omega) (base.append (nested 1))
  have hcapm :
      (cap ▷ of m).diagram.matching =
        PlanarMatching.cast (by simp; omega) ((nested 1).append (nested m)) := by
    apply eq_of_pv_eq
    rw [diagram_whiskerRight, TLDiagram.matching_tensor, TLDiagram.matching_id, diagram_cap,
      eq_nested_one TLDiagram.cap.matching, pv_cast_eq, pv_cast_eq, pv_insert_eq, pv_append_eq]
    dsimp only
    funext q
    by_cases h1 : q < 2
    · have hlt := pv_lt (nested 1) (by omega : q < 1 + 1)
      rw [insertFn_of_lt _ _ h1, appendFn_of_lt _ _ h1, shiftGap_of_lt hlt]
    by_cases h2 : q < 2 + (m + m)
    · rw [insertFn_of_le_of_lt _ _ (by omega) h2, appendFn_of_le_of_lt _ _ (by omega) h2]
    · rw [insertFn_of_le _ _ (by omega), appendFn_of_le _ _ (by omega)]
  have hApp :
      pv (base.append
          (eqToHom (congrArg of (Nat.add_assoc 1 1 m).symm) ≫ cap ▷ of m).diagram.matching) =
        insertFn (K + 2 + 2) 0 (m + m) (pv mid) (pv (nested m)) := by
    rw [pv_append_eq, matching_eqToHom_comp, hcapm, pv_cast_eq, pv_cast_eq, pv_append_eq]
    simp only [tensorObj_as]
    funext q
    simp only [mid, pv_cast_eq, pv_append_eq]
    by_cases h1 : q < K + 2
    · have hlt := pv_lt base (show q < 1 + n + (1 + (1 + m)) by simp only [K] at h1; omega)
      rw [appendFn_of_lt _ _ (by omega), insertFn_of_lt _ _ (by omega),
        appendFn_of_lt _ _ (by omega), shiftGap_of_lt (by omega)]
    by_cases h2 : q < K + 2 + 2
    · have hlt := pv_lt (nested 1) (show q - (1 + n + (1 + (1 + m))) < 1 + 1 by omega)
      rw [appendFn_of_le_of_lt _ _ (by omega) (by omega),
        appendFn_of_lt _ _ (by omega), insertFn_of_lt _ _ h2,
        appendFn_of_le_of_lt _ _ (by simp only [K] at h1; omega) (by simp only [K] at h2; omega),
        shiftGap_of_lt (by omega)]
    by_cases h3 : q < K + 2 + 2 + (m + m)
    · rw [appendFn_of_le_of_lt _ _ (by omega) (by omega),
        appendFn_of_le_of_lt _ _ (by omega) (by omega),
        insertFn_of_le_of_lt _ _ (by omega) h3]
      have hsub : q - (1 + n + (1 + (1 + m))) - 2 = q - (K + 2 + 2) := by omega
      rw [hsub]; omega
    · rw [appendFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]
  have hsplit := glueFn_add (1 + n) m 2
    (pv (base.append
      (eqToHom (congrArg of (Nat.add_assoc 1 1 m).symm) ≫ cap ▷ of m).diagram.matching))
  have hL := glueFn_insertFn_left (b := 0) (n := 1 + n + m) (nested m) 2 (K + 2 + 2) mid (by omega)
  have hmid_pv : ∀ q, pv mid q =
      if q = 0 then K + 1
      else if q < K + 1 then 1 + pv g.diagram.matching (q - 1)
      else if q = K + 1 then 0
      else if q = K + 2 then K + 3
      else if q = K + 3 then K + 2
      else q := by
    intro q
    simp only [mid, base, diagram_whiskerLeft, TLDiagram.matching_tensor, TLDiagram.matching_id,
      pv_cast_eq, pv_append_eq, pv_insert_eq, tensorObj_as]
    by_cases h0 : q = 0
    · subst h0
      simp [appendFn, insertFn, shiftGap, pv_nested, K]; omega
    by_cases h1 : q < K + 1
    · rw [appendFn_of_lt _ _ (by omega), insertFn_of_le_of_lt _ _ (by omega) (by omega)]
      simp [h0, h1]
    by_cases h2 : q = K + 1
    · subst h2
      rw [appendFn_of_lt _ _ (by omega), insertFn_of_le_of_lt_add _ _ (by omega) (by omega)]
      simp [pv_nested, shiftGap, K]
    by_cases h3 : q = K + 2
    · subst h3
      rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), pv_nested 1 (by omega)]
      simp [K]; omega
    by_cases h4 : q = K + 3
    · subst h4
      rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), pv_nested 1 (by omega)]
      simp [K]; omega
    · rw [appendFn_of_le _ _ (by omega)]
      simp [h0, h1, h2, h3, h4]
  have hstep1 :
      contractFn (K + 1) (pv mid) = fun q =>
        if q = 0 then K + 1
        else if q < K + 1 then 1 + pv g.diagram.matching (q - 1)
        else if q = K + 1 then 0
        else q := by
    funext q
    rw [contractFn, erasePair_apply]
    have hm1 : pv mid (K + 1) = 0 := by rw [hmid_pv]; simp
    have hm2 : pv mid (K + 2) = K + 3 := by rw [hmid_pv]; simp
    by_cases h0 : q = 0
    · subst h0
      rw [skipN_of_lt (by omega), splice_of_ne _ (by omega) (by omega), hmid_pv]
      simp only [↓reduceIte]
      rw [rejoin_of_eq_left _ rfl, hm2, unskipN_of_le (by omega)]
      omega
    by_cases h1 : q < K + 1
    · have hlt : pv g.diagram.matching (q - 1) < K := by
        simpa [K] using pv_lt g.diagram.matching
          (by simp only [tensorObj_as]; dsimp only [K] at h1; omega)
      rw [skipN_of_lt (by omega), splice_of_ne _ (by omega) (by omega), hmid_pv]
      simp only [h0, h1, ↓reduceIte]
      rw [rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]
    by_cases h2 : q = K + 1
    · subst h2
      rw [skipN_of_le (by omega), splice_of_ne _ (by omega) (by omega), hmid_pv]
      simp only [show K + 1 + 2 ≠ 0 by omega, show ¬(K + 1 + 2 < K + 1) by omega,
        show K + 1 + 2 ≠ K + 1 by omega, show K + 1 + 2 ≠ K + 2 by omega,
        show K + 1 + 2 = K + 3 by omega, ↓reduceIte]
      rw [rejoin_of_eq_right _ rfl, hm1, unskipN_of_lt (by omega)]
      simp
    · rw [skipN_of_le (by omega), splice_of_ne _ (by omega) (by omega), hmid_pv]
      simp only [show q + 2 ≠ 0 by omega, show ¬(q + 2 < K + 1) by omega,
        show q + 2 ≠ K + 1 by omega, show q + 2 ≠ K + 2 by omega, show q + 2 ≠ K + 3 by omega,
        ↓reduceIte]
      rw [rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
      simp [h0, h1, h2]
  have hstep2 :
      contractFn K (contractFn (K + 1) (pv mid)) =
        pv (PlanarMatching.rotate K g.diagram.matching) := by
    funext q
    rw [contractFn, erasePair_apply, hstep1, pv_rotate_eq]
    have hK_lt : pv g.diagram.matching (K - 1) < K := by
      simpa [K] using pv_lt g.diagram.matching (by simp only [tensorObj_as]; omega)
    have hK_ne : pv g.diagram.matching (K - 1) ≠ K - 1 :=
      pv_ne g.diagram.matching (by simp only [tensorObj_as]; dsimp only [K]; omega)
    have hs1 : (if K = 0 then K + 1 else if K < K + 1 then 1 + pv g.diagram.matching (K - 1)
        else if K = K + 1 then 0 else K) = 1 + pv g.diagram.matching (K - 1) := by
      have : K ≠ 0 := by omega
      simp [this]
    have hs2 : (if K + 1 = 0 then K + 1 else if K + 1 < K + 1 then
        1 + pv g.diagram.matching (K + 1 - 1)
        else if K + 1 = K + 1 then 0 else K + 1) = 0 := by
      simp
    by_cases h0 : q = 0
    · subst h0
      have hKpos : 0 < K := by omega
      rw [skipN_of_lt hKpos, splice_of_ne _ (by omega) (by omega)]
      simp only [hKpos, ↓reduceIte]
      rw [rejoin_of_eq_right _ rfl, hs1, unskipN_of_lt (by omega)]
      omega
    by_cases h1 : q < K
    · have hlt : pv g.diagram.matching (q - 1) < K := by
        simpa [K] using pv_lt g.diagram.matching
          (by simp only [tensorObj_as]; dsimp only [K] at h1; omega)
      rw [skipN_of_lt h1, splice_of_ne _ (by omega) (by omega)]
      simp only [h0, h1, show q < K + 1 by omega, ↓reduceIte]
      by_cases heq : pv g.diagram.matching (q - 1) = K - 1
      · simp only [heq, ↓reduceIte]
        rw [show 1 + (K - 1) = K by omega, rejoin_of_eq_left _ rfl, hs2, unskipN_of_lt (by omega)]
      · simp only [heq, ↓reduceIte]
        rw [rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]
        omega
    · rw [skipN_of_le (by omega), splice_of_ne _ (by omega) (by omega)]
      simp only [h1, show q + 2 ≠ 0 by omega, show ¬(q + 2 < K + 1) by omega,
        show q + 2 ≠ K + 1 by omega, ↓reduceIte]
      rw [rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
      omega
  have hc1 : circleInd (K + 1) (pv mid) = 0 := by
    rw [circleInd, hmid_pv]
    simp
  have hc2 : circleInd K (contractFn (K + 1) (pv mid)) = 0 := by
    rw [circleInd, hstep1]
    have hKpos : K ≠ 0 := by omega
    have hlt : pv g.diagram.matching (K - 1) < K := by
      simpa [K] using pv_lt g.diagram.matching (by simp only [tensorObj_as]; omega)
    simp [hKpos, show 1 + pv g.diagram.matching (K - 1) ≠ K + 1 by omega]
  have hPhase1 :
      glueFn (1 + n + m) 2
          (pv (base.append
            (eqToHom (congrArg of (Nat.add_assoc 1 1 m).symm) ≫ cap ▷ of m).diagram.matching)) =
        pv ((PlanarMatching.cast (by omega) (PlanarMatching.rotate K g.diagram.matching) :
          PlanarMatching ((1 + n) + m)).append (nested m)) := by
    rw [hApp, hL.1]
    have hidx : 1 + n + m = K := by omega
    rw [show glueFn (1 + n + m) 2 (pv mid) = glueFn K 2 (pv mid) by rw [hidx],
      glueFn, glueFn, glueFn, show K + 0 = K from Nat.add_zero K, hstep2, pv_append_eq, pv_cast_eq]
    funext q
    by_cases h1 : q < K
    · have hlt := pv_lt (PlanarMatching.rotate K g.diagram.matching) h1
      rw [insertFn_of_lt _ _ (by omega), appendFn_of_lt _ _ (by omega), shiftGap_of_lt (by omega)]
    by_cases h2 : q < K + (m + m)
    · rw [insertFn_of_le_of_lt _ _ (by omega) (by omega),
        appendFn_of_le_of_lt _ _ (by omega) (by omega)]
      have heq1 : K + 2 + 2 - 2 * 2 = 1 + n + m := by omega
      rw [heq1]
    · rw [insertFn_of_le _ _ (by omega), appendFn_of_le _ _ (by omega)]
  have hPhase1c :
      glueCircles (1 + n + m) 2
          (pv (base.append
            (eqToHom (congrArg of (Nat.add_assoc 1 1 m).symm) ≫ cap ▷ of m).diagram.matching)) =
        0 := by
    rw [hApp, hL.2]
    have hidx : 1 + n + m = K := by omega
    rw [hidx, glueCircles, glueCircles, glueCircles, show K + 0 = K from Nat.add_zero K, hc1, hc2]
  have hPhase2 :
      glueFn (1 + n) m
          (pv ((PlanarMatching.cast (by omega) (PlanarMatching.rotate K g.diagram.matching) :
            PlanarMatching ((1 + n) + m)).append (nested m))) =
        pv (PlanarMatching.rotate K g.diagram.matching) := by
    have hgm := congrArg pv (glueMiddle_append_nested
      (PlanarMatching.cast (by omega) (PlanarMatching.rotate K g.diagram.matching) :
        PlanarMatching ((1 + n) + m)))
    rw [pv_glueMiddle, pv_cast_eq] at hgm
    exact hgm
  have hPhase2c :
      glueCircles (1 + n) m
          (pv ((PlanarMatching.cast (by omega) (PlanarMatching.rotate K g.diagram.matching) :
            PlanarMatching ((1 + n) + m)).append (nested m))) = 0 := by
    have hgc := glueMiddleCircles_append_nested
      (PlanarMatching.cast (by omega) (PlanarMatching.rotate K g.diagram.matching) :
        PlanarMatching ((1 + n) + m))
    rw [glueMiddleCircles_eq] at hgc
    exact hgc
  have hm2 : m + 2 = 1 + (1 + m) := by omega
  rw [hm2] at hsplit
  rw [hdef]
  constructor
  · apply eq_of_pv_eq
    rw [matching_comp_eqToHom, pv_cast_eq, diagram_comp, TLDiagram.matching_comp, pv_glueMiddle]
    simp only [tensorObj_as]
    rw [hsplit.1, hPhase1, hPhase2, pv_cast_eq]
  · rw [circles_comp_eqToHom, diagram_comp, TLDiagram.circles_comp, glueMiddleCircles_eq]
    simp only [tensorObj_as]
    rw [hsplit.2, hPhase1, hPhase1c, hPhase2c,
      diagram_whiskerLeft, TLDiagram.circles_tensor, TLDiagram.circles_id, circles_eqToHom_comp,
      diagram_whiskerRight, TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cap,
      TLDiagram.circles_cap]
    omega

/-- Dragging the top-left corner down via `tensorLeftHomEquiv` at `of 1` rotates the matching
one step counterclockwise. -/
theorem matching_tensorLeftHomEquiv_symm (n m : ℕ) (g : of n ⟶ of 1 ⊗ of m) :
    ((tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm g).diagram.matching =
      PlanarMatching.cast (by simp; omega)
        (PlanarMatching.rotate (n + (1 + m)) g.diagram.matching) :=
  (tensorLeftHomEquiv_symm_aux n m g).1

/-- Dragging the top-left corner down via `tensorLeftHomEquiv` at `of 1` preserves circles. -/
theorem circles_tensorLeftHomEquiv_symm (n m : ℕ) (g : of n ⟶ of 1 ⊗ of m) :
    ((tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm g).diagram.circles =
      g.diagram.circles :=
  (tensorLeftHomEquiv_symm_aux n m g).2

/-- Dragging the top-left corner down via `tensorLeftHomEquiv` at `of 1` agrees with
`(TLDiagram.dragLeft n m).symm`. -/
theorem diagram_tensorLeftHomEquiv_symm (n m : ℕ) (g : of n ⟶ of (m + 1)) :
    (eqToHom (congrArg of (Nat.add_comm n 1)) ≫
      (tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm
        (g ≫ eqToHom (congrArg of (Nat.add_comm m 1)))).diagram =
      (TLDiagram.dragLeft n m).symm g.diagram := by
  ext : 1
  · rw [matching_eqToHom_comp, matching_tensorLeftHomEquiv_symm, matching_comp_eqToHom,
      PlanarMatching.cast_cast, PlanarMatching.cast_rotate, PlanarMatching.cast_cast,
      TLDiagram.matching_dragLeft_symm]
  · rw [circles_eqToHom_comp, circles_tensorLeftHomEquiv_symm, circles_comp_eqToHom,
      TLDiagram.circles_dragLeft_symm]

/-- Dragging the bottom-left corner up via `tensorLeftHomEquiv` at `of 1` agrees with
`TLDiagram.dragLeft n m`. -/
theorem diagram_tensorLeftHomEquiv (n m : ℕ) (f : of (n + 1) ⟶ of m) :
    (tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)
        (eqToHom (congrArg of (Nat.add_comm 1 n)) ≫ f) ≫
      eqToHom (congrArg of (Nat.add_comm 1 m))).diagram =
      TLDiagram.dragLeft n m f.diagram := by
  set g := tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)
      (eqToHom (congrArg of (Nat.add_comm 1 n)) ≫ f) ≫
    eqToHom (congrArg of (Nat.add_comm 1 m))
  have hg := diagram_tensorLeftHomEquiv_symm n m g
  have hcancel :
      eqToHom (congrArg of (Nat.add_comm n 1)) ≫
        (tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm
          (g ≫ eqToHom (congrArg of (Nat.add_comm m 1))) = f := by
    simp only [g, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Equiv.symm_apply_apply, eqToHom_trans_assoc, Category.id_comp]
  rw [hcancel] at hg
  exact (Equiv.symm_apply_eq (TLDiagram.dragLeft n m)).mp hg.symm

/-! ### Adjoint mates as 180° diagram rotation -/

/-- Evaluating `g : of a ⟶ of k` against `eval k` on the right preserves both the underlying
matching (up to `a + k = a + k + 0`) and the circle count. -/
private theorem diagram_whiskerRight_comp_eval :
    ∀ (k : ℕ) {a : ℕ} (g : of a ⟶ of k),
      (g ▷ of k ≫ eval k).diagram.matching =
          PlanarMatching.cast (by simp) g.diagram.matching ∧
        (g ▷ of k ≫ eval k).diagram.circles = g.diagram.circles
  | 0, a, g => by
    have hcomp : g ▷ of 0 ≫ eval 0 = g := by
      have : g ▷ of 0 ≫ 𝟙 (of 0) = g ▷ of 0 := Category.comp_id (g ▷ of 0)
      rw [eval_zero, this]
      exact hom_ext (TLDiagram.tensor_id_zero g.diagram)
    rw [hcomp]
    exact ⟨by simp, rfl⟩
  | k + 1, a, g => by
    let g' : of (a + 1) ⟶ of k := (tensorRightHomEquiv (of a) (of 1) (of 1) (of k)).symm g
    have hfact :
        g ▷ of (k + 1) ≫ eval (k + 1) =
          eqToHom (by ext; simp; omega) ≫ g' ▷ of k ≫ eval k := by
      have h1 :
          g' ▷ of k =
            (g ▷ of 1) ▷ of k ≫ (α_ (of k) (of 1) (of 1)).hom ▷ of k ≫
              (of k ◁ cap) ▷ of k ≫ (ρ_ (of k)).hom ▷ of k := by
        dsimp only [g', tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
        rw [evaluation_of_one, comp_whiskerRight, comp_whiskerRight, comp_whiskerRight]
      rw [eval_succ, h1]
      have hco :
          eqToHom (by ext; simp; omega :
              of a ⊗ of (k + 1) = (of a ⊗ of 1) ⊗ of k) ≫
            (g ▷ of 1) ▷ of k ≫ (α_ (of k) (of 1) (of 1)).hom ▷ of k ≫
            (of k ◁ cap) ▷ of k ≫ (ρ_ (of k)).hom ▷ of k =
            g ▷ of (k + 1) ≫
              eqToHom (by ext; simp; omega :
                of (k + 1) ⊗ of (k + 1) = of k ⊗ ((of 1 ⊗ of 1) ⊗ of k)) ≫
              of k ◁ (cap ▷ of k) ≫
              eqToHom (by ext; simp :
                of k ⊗ (𝟙_ TLDiagCat ⊗ of k) = of k ⊗ of k) := by
        let ι : of (k + 1) ≅ of 1 ⊗ of k := eqToIso (congrArg of (Nat.add_comm k 1))
        calc
          eqToHom (by ext; simp; omega : of a ⊗ of (k + 1) = (of a ⊗ of 1) ⊗ of k) ≫
              (g ▷ of 1) ▷ of k ≫ (α_ (of k) (of 1) (of 1)).hom ▷ of k ≫
              (of k ◁ cap) ▷ of k ≫ (ρ_ (of k)).hom ▷ of k
              = of a ◁ ι.hom ≫ ((α_ (of a) (of 1) (of k)).inv ≫ (g ▷ of 1) ▷ of k) ≫
                  (α_ (of k) (of 1) (of 1)).hom ▷ of k ≫
                  (of k ◁ cap) ▷ of k ≫ (ρ_ (of k)).hom ▷ of k := by
                have hL :
                    eqToHom (by ext; simp; omega : of a ⊗ of (k + 1) = (of a ⊗ of 1) ⊗ of k) =
                      of a ◁ ι.hom ≫ (α_ (of a) (of 1) (of k)).inv := by
                  simp [ι, associator_eq, whiskerLeft_eqToHom]
                rw [hL]
                simp only [Category.assoc]
          _ = (of a ◁ ι.hom ≫ g ▷ (of 1 ⊗ of k)) ≫
                (α_ (of (k + 1)) (of 1) (of k)).inv ≫ (α_ (of k) (of 1) (of 1)).hom ▷ of k ≫
                (of k ◁ cap) ▷ of k ≫ (ρ_ (of k)).hom ▷ of k := by
                rw [← associator_inv_naturality_left g (of 1) (of k)]
                simp only [Category.assoc]
          _ = g ▷ of (k + 1) ≫
                (of (k + 1) ◁ ι.hom ≫ (α_ (of (k + 1)) (of 1) (of k)).inv ≫
                  (α_ (of k) (of 1) (of 1)).hom ▷ of k) ≫
                (of k ◁ cap) ▷ of k ≫ (ρ_ (of k)).hom ▷ of k := by
                rw [whisker_exchange g ι.hom]
                simp only [Category.assoc]
          _ = g ▷ of (k + 1) ≫
                eqToHom (by ext; simp; omega :
                  of (k + 1) ⊗ of (k + 1) = of k ⊗ ((of 1 ⊗ of 1) ⊗ of k)) ≫
                ((α_ (of k) (of 2) (of k)).inv ≫ (of k ◁ cap) ▷ of k) ≫
                (ρ_ (of k)).hom ▷ of k := by
                have hM :
                    of (k + 1) ◁ ι.hom ≫ (α_ (of (k + 1)) (of 1) (of k)).inv ≫
                      (α_ (of k) (of 1) (of 1)).hom ▷ of k =
                    eqToHom (by ext; simp; omega :
                        of (k + 1) ⊗ of (k + 1) = of k ⊗ ((of 1 ⊗ of 1) ⊗ of k)) ≫
                      (α_ (of k) (of 2) (of k)).inv := by
                  rw [associator_eq (of k) (of 1) (of 1), associator_eq (of (k + 1)) (of 1) (of k),
                    associator_eq (of k) (of 2) (of k)]
                  simp only [ι, eqToIso.hom, eqToIso.inv, whiskerLeft_eqToHom, eqToHom_whiskerRight,
                    eqToHom_trans]
                rw [hM]
                simp only [Category.assoc]
          _ = g ▷ of (k + 1) ≫
                eqToHom (by ext; simp; omega :
                  of (k + 1) ⊗ of (k + 1) = of k ⊗ ((of 1 ⊗ of 1) ⊗ of k)) ≫
                of k ◁ (cap ▷ of k) ≫
                eqToHom (by ext; simp :
                  of k ⊗ (𝟙_ TLDiagCat ⊗ of k) = of k ⊗ of k) := by
                rw [← associator_inv_naturality_middle (of k) cap (of k)]
                have hR : (α_ (of k) (of 0) (of k)).inv ≫ (ρ_ (of k)).hom ▷ of k =
                    eqToHom (by ext; simp : of k ⊗ (𝟙_ TLDiagCat ⊗ of k) = of k ⊗ of k) := by
                  rw [associator_eq, eqToIso.inv, rightUnitor_hom]
                  have hid : 𝟙 (of k) ▷ of k = 𝟙 (of k ⊗ of k) := id_whiskerRight (of k) (of k)
                  rw [hid]
                  exact Category.comp_id (eqToHom _)
                simp only [Category.assoc, hR]
      simpa only [Category.assoc] using (congrArg (· ≫ eval k) hco).symm
    obtain ⟨ihm, ihc⟩ := diagram_whiskerRight_comp_eval k g'
    have hg' := diagram_tensorRightHomEquiv_symm a k g
    rw [hfact]
    constructor
    · rw [matching_eqToHom_comp, ihm, PlanarMatching.cast_cast]
      have hm' : g'.diagram.matching = ((TLDiagram.dragRight a k).symm g.diagram).matching :=
        congrArg TLDiagram.matching hg'
      rw [hm', TLDiagram.matching_dragRight_symm, PlanarMatching.cast_cast]
    · rw [circles_eqToHom_comp, ihc]
      have hc' : g'.diagram.circles = ((TLDiagram.dragRight a k).symm g.diagram).circles :=
        congrArg TLDiagram.circles hg'
      rw [hc', TLDiagram.circles_dragRight_symm]

/-- Evaluating `f : of a ⟶ of k` against `eval k` on the left rotates the matching `k` steps
counterclockwise and preserves the circle count. -/
private theorem diagram_whiskerLeft_comp_eval :
    ∀ (k : ℕ) {a : ℕ} (f : of a ⟶ of k),
      (of k ◁ f ≫ eval k).diagram.matching =
          PlanarMatching.cast (by simp; omega)
            ((PlanarMatching.rotate (a + k) ^ k) f.diagram.matching) ∧
        (of k ◁ f ≫ eval k).diagram.circles = f.diagram.circles
  | 0, a, f => by
    have hcomp : of 0 ◁ f ≫ eval 0 = (λ_ (of a)).hom ≫ f := by
      have hid : of 0 ◁ f ≫ 𝟙 (of 0) = of 0 ◁ f := Category.comp_id (of 0 ◁ f)
      rw [eval_zero, hid]
      have hln := leftUnitor_naturality f
      have hlam0 : (λ_ (of 0)).hom = 𝟙 (of 0) := by
        simp [leftUnitor_eq]
      rw [hlam0] at hln
      exact hid.symm.trans hln
    rw [hcomp, leftUnitor_eq, eqToIso.hom]
    constructor
    · rw [matching_eqToHom_comp, pow_zero, Perm.one_apply]
    · rw [circles_eqToHom_comp]
  | k + 1, a, f => by
    let ι : of (k + 1) ≅ of 1 ⊗ of k := eqToIso (congrArg of (Nat.add_comm k 1))
    let f₁ : of a ⟶ of 1 ⊗ of k := f ≫ ι.hom
    let f' : of 1 ⊗ of a ⟶ of k := (tensorLeftHomEquiv (of a) (of 1) (of 1) (of k)).symm f₁
    have hfact :
        of (k + 1) ◁ f ≫ eval (k + 1) =
          eqToHom (by ext; simp; omega) ≫ of k ◁ f' ≫ eval k := by
      have h1 :
          of k ◁ f' =
            of k ◁ (of 1 ◁ f₁) ≫ of k ◁ (α_ (of 1) (of 1) (of k)).inv ≫
              of k ◁ (cap ▷ of k) ≫ of k ◁ (λ_ (of k)).hom := by
        dsimp only [f', tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
        rw [evaluation_of_one]
        simp only [MonoidalCategory.whiskerLeft_comp]
      rw [eval_succ, h1]
      have hco :
          eqToHom (by ext; simp; omega :
              of (k + 1) ⊗ of a = of k ⊗ (of 1 ⊗ of a)) ≫
            of k ◁ (of 1 ◁ f₁) ≫ of k ◁ (α_ (of 1) (of 1) (of k)).inv ≫
            of k ◁ (cap ▷ of k) ≫ of k ◁ (λ_ (of k)).hom =
            of (k + 1) ◁ f ≫
              eqToHom (by ext; simp; omega :
                of (k + 1) ⊗ of (k + 1) = of k ⊗ ((of 1 ⊗ of 1) ⊗ of k)) ≫
              of k ◁ (cap ▷ of k) ≫
              eqToHom (by ext; simp :
                of k ⊗ (𝟙_ TLDiagCat ⊗ of k) = of k ⊗ of k) := by
        calc
          eqToHom (by ext; simp; omega : of (k + 1) ⊗ of a = of k ⊗ (of 1 ⊗ of a)) ≫
              of k ◁ (of 1 ◁ f₁) ≫ of k ◁ (α_ (of 1) (of 1) (of k)).inv ≫
              of k ◁ (cap ▷ of k) ≫ of k ◁ (λ_ (of k)).hom
              = ((α_ (of k) (of 1) (of a)).hom ≫ of k ◁ (of 1 ◁ f₁)) ≫
                  of k ◁ (α_ (of 1) (of 1) (of k)).inv ≫
                  of k ◁ (cap ▷ of k) ≫ of k ◁ (λ_ (of k)).hom := by
                have hL :
                    eqToHom (by ext; simp; omega : of (k + 1) ⊗ of a = of k ⊗ (of 1 ⊗ of a)) =
                      (α_ (of k) (of 1) (of a)).hom := by
                  simp [associator_eq]
                rw [hL]
                simp only [Category.assoc]
          _ = of (k + 1) ◁ f ≫
                (of (k + 1) ◁ ι.hom ≫ (α_ (of k) (of 1) (of 1 ⊗ of k)).hom ≫
                  of k ◁ (α_ (of 1) (of 1) (of k)).inv) ≫
                of k ◁ (cap ▷ of k) ≫ of k ◁ (λ_ (of k)).hom := by
                rw [← associator_naturality_right (of k) (of 1) f₁]
                dsimp only [f₁]
                rw [MonoidalCategory.whiskerLeft_comp]
                simp only [Category.assoc]
                rfl
          _ = of (k + 1) ◁ f ≫
                eqToHom (by ext; simp; omega :
                  of (k + 1) ⊗ of (k + 1) = of k ⊗ ((of 1 ⊗ of 1) ⊗ of k)) ≫
                of k ◁ (cap ▷ of k) ≫
                eqToHom (by ext; simp :
                  of k ⊗ (𝟙_ TLDiagCat ⊗ of k) = of k ⊗ of k) := by
                have hR1 :
                    of (k + 1) ◁ ι.hom ≫ (α_ (of k) (of 1) (of 1 ⊗ of k)).hom ≫
                      of k ◁ (α_ (of 1) (of 1) (of k)).inv =
                    eqToHom (by ext; simp; omega :
                        of (k + 1) ⊗ of (k + 1) = of k ⊗ ((of 1 ⊗ of 1) ⊗ of k)) := by
                  simp only [ι, associator_eq, eqToIso.hom, eqToIso.inv, whiskerLeft_eqToHom,
                    eqToHom_trans]
                have hR2 :
                    of k ◁ (λ_ (of k)).hom =
                      eqToHom (by ext; simp : of k ⊗ (𝟙_ TLDiagCat ⊗ of k) = of k ⊗ of k) := by
                  rw [leftUnitor_eq, eqToIso.hom, whiskerLeft_eqToHom]
                rw [hR1, hR2]
      simpa only [Category.assoc] using (congrArg (· ≫ eval k) hco).symm
    obtain ⟨ihm, ihc⟩ := diagram_whiskerLeft_comp_eval k f'
    rw [hfact]
    constructor
    · have hf1 : f₁.diagram.matching = PlanarMatching.cast (by simp; omega) f.diagram.matching :=
        matching_comp_eqToHom f (congrArg of (Nat.add_comm k 1))
      rw [matching_eqToHom_comp, ihm, PlanarMatching.cast_cast, matching_tensorLeftHomEquiv_symm,
        hf1, ← PlanarMatching.cast_rotate, PlanarMatching.cast_cast,
        ← PlanarMatching.cast_rotate_pow, PlanarMatching.cast_cast, ← Perm.mul_apply, ← pow_succ]
    · rw [circles_eqToHom_comp, ihc, circles_tensorLeftHomEquiv_symm]
      exact circles_comp_eqToHom f (congrArg of (Nat.add_comm k 1))

/-- The right adjoint mate `fᘁ : Y ⟶ X` of a morphism `f : X ⟶ Y` rotates the underlying diagram
by `180°` (horizontal reflection composed with vertical reflection). -/
theorem diagram_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) :
    (fᘁ).diagram = TLDiagram.reflect Y.as X.as (TLDiagram.verticalReflect X.as Y.as f.diagram) := by
  have hev : (fᘁ ▷ X ≫ eval X.as).diagram = (Y ◁ f ≫ eval Y.as).diagram :=
    congrArg Hom.diagram (rightAdjointMate_comp_evaluation f)
  obtain ⟨hLm, hLc⟩ := diagram_whiskerRight_comp_eval X.as (fᘁ)
  obtain ⟨hRm, hRc⟩ := diagram_whiskerLeft_comp_eval Y.as f
  ext : 1
  · have hm := congrArg TLDiagram.matching hev
    rw [hLm, hRm] at hm
    rw [TLDiagram.matching_reflect, TLDiagram.matching_verticalReflect,
      ← PlanarMatching.cast_reflect, PlanarMatching.reflect_reflect,
      ← PlanarMatching.cast_rotate_pow]
    have hm' := congrArg (PlanarMatching.cast (by omega : Y.as + X.as + 0 = Y.as + X.as)) hm
    simpa only [PlanarMatching.cast_cast, PlanarMatching.cast_refl, Equiv.refl_apply] using hm'
  · have hc := congrArg TLDiagram.circles hev
    rw [hLc, hRc] at hc
    simpa [TLDiagram.circles_reflect, TLDiagram.circles_verticalReflect] using hc

/-- The left adjoint mate `ᘁf : Y ⟶ X` of a morphism `f : X ⟶ Y` also rotates the underlying
diagram by `180°`. -/
theorem diagram_leftAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) :
    (ᘁf).diagram = TLDiagram.reflect Y.as X.as (TLDiagram.verticalReflect X.as Y.as f.diagram) := by
  have hev : (X ◁ (ᘁf) ≫ eval X.as).diagram = (f ▷ Y ≫ eval Y.as).diagram :=
    congrArg Hom.diagram (leftAdjointMate_comp_evaluation f)
  obtain ⟨hLm, hLc⟩ := diagram_whiskerLeft_comp_eval X.as (ᘁf)
  obtain ⟨hRm, hRc⟩ := diagram_whiskerRight_comp_eval Y.as f
  ext : 1
  · have hm := congrArg TLDiagram.matching hev
    rw [hLm, hRm] at hm
    rw [TLDiagram.matching_reflect, TLDiagram.matching_verticalReflect,
      ← PlanarMatching.cast_reflect, PlanarMatching.reflect_reflect]
    have hm' :
        (PlanarMatching.rotate (Y.as + X.as) ^ X.as) (ᘁf).diagram.matching =
          PlanarMatching.cast (by omega) f.diagram.matching := by
      have h0 := congrArg (PlanarMatching.cast (by omega : X.as + Y.as + 0 = Y.as + X.as)) hm
      simp only [PlanarMatching.cast_cast, PlanarMatching.cast_refl, Equiv.refl_apply] at h0
      exact h0
    have hrot := congrArg (PlanarMatching.rotate (Y.as + X.as) ^ Y.as) hm'
    rw [← Perm.mul_apply, ← pow_add, PlanarMatching.rotate_pow_self, Perm.one_apply] at hrot
    exact hrot
  · have hc := congrArg TLDiagram.circles hev
    rw [hLc, hRc] at hc
    simpa [TLDiagram.circles_reflect, TLDiagram.circles_verticalReflect] using hc

/-- The left and right adjoint mates coincide on every morphism of `TLDiagCat`. -/
theorem leftAdjointMate_eq_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) : (ᘁf) = fᘁ :=
  hom_ext ((diagram_leftAdjointMate f).trans (diagram_rightAdjointMate f).symm)

/-- Taking the right adjoint mate twice is the identity on every morphism of `TLDiagCat`. -/
@[simp]
theorem rightAdjointMate_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) : (fᘁ)ᘁ = f := by
  apply hom_ext
  rw [diagram_rightAdjointMate, diagram_rightAdjointMate]
  dsimp only [HasRightDual.rightDual]
  rw [← TLDiagram.reflect_verticalReflect, TLDiagram.reflect_reflect,
    TLDiagram.verticalReflect_verticalReflect]

end TLDiagCat

end TauCeti
