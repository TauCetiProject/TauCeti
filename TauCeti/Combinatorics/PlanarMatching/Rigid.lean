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
theorem coeval_zero : coeval 0 = 𝟙 (of 0) := (rfl)

@[simp]
theorem eval_zero : eval 0 = 𝟙 (of 0) := (rfl)

theorem matching_coeval (n : ℕ) :
    (coeval n).diagram.matching =
      PlanarMatching.cast (Nat.zero_add _).symm (PlanarMatching.nested n) := by
  cases n with
  | zero => exact Subsingleton.elim (α := PlanarMatching 0) _ _
  | succ _ => rfl

@[simp]
theorem circles_coeval (n : ℕ) : (coeval n).diagram.circles = 0 := by cases n <;> simp [coeval]

theorem matching_eval (n : ℕ) : (eval n).diagram.matching = PlanarMatching.nested n := by
  cases n with
  | zero => exact Subsingleton.elim (α := PlanarMatching 0) _ _
  | succ _ => rfl

@[simp]
theorem circles_eval (n : ℕ) : (eval n).diagram.circles = 0 := by cases n <;> simp [eval]

/-- On two boundary points there is only one planar matching, namely `nested 1`. -/
private theorem eq_nested_one (x : PlanarMatching 2) : x = PlanarMatching.nested 1 := by
  refine PlanarMatching.ext fun a => Fin.ext ?_
  have hne : (x.1.val a : ℕ) ≠ (a : ℕ) := fun h => x.1.apply_ne a (Fin.ext h)
  have hnest : ((PlanarMatching.nested 1).1.val a : ℕ) = 1 - (a : ℕ) := by
    rw [← PlanarMatching.pv_coe, PlanarMatching.pv_nested 1 a.isLt]
  omega

@[simp]
theorem coeval_one : coeval 1 = cup :=
  hom_ext (TLDiagram.ext ((eq_nested_one _).trans (eq_nested_one _).symm)
    (by rw [circles_coeval, diagram_cup, TLDiagram.circles_cup]))

@[simp]
theorem eval_one : eval 1 = cap :=
  hom_ext (TLDiagram.ext ((eq_nested_one _).trans (eq_nested_one _).symm)
    (by rw [circles_eval, diagram_cap, TLDiagram.circles_cap]))

open PlanarMatching in
private theorem glueFn_append_nested {a b : ℕ} (x : PlanarMatching (a + b)) :
    glueFn a b (pv (x.append (nested b))) = pv x ∧
      glueCircles a b (pv (x.append (nested b))) = 0 :=
  ⟨by rw [← pv_glueMiddle, glueMiddle_append_nested],
   by rw [← glueMiddleCircles_eq, glueMiddleCircles_append_nested]⟩

open PlanarMatching in
private theorem glueFn_nested_append {a b : ℕ} (x : PlanarMatching (a + b)) :
    glueFn a a (pv ((nested a).append x)) = pv x ∧
      glueCircles a a (pv ((nested a).append x)) = 0 :=
  ⟨by rw [← pv_glueMiddle, glueMiddle_nested_append],
   by rw [← glueMiddleCircles_eq, glueMiddleCircles_nested_append]⟩

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
  by_cases h1 : q < 3
  · interval_cases q <;> simp [insertFn, shiftGap, pv_nested]; omega
  by_cases h2 : q < 3 + (n + n)
  · rw [insertFn_of_le_of_lt _ _ (by omega) h2, insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega), pv_nested n (by omega),
      pv_nested n (by omega), shiftGap_of_le (by omega)]; omega
  by_cases h3 : q = 3 + (n + n)
  · subst h3
    rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      show 3 + (n + n) - (1 + 1) - (0 + (n + n)) = 1 by omega,
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
    simp only [tensorObj_as, tensorUnit_as, show 1 + 0 + 1 + (1 + (n + n) + 1) = 3 + (n + n) + 1 by
      omega]
    simpa only [x, pv_cast_eq, pv_append_eq, tensorObj_as, tensorUnit_as] using
      appendFn_insertFn_right (k := 2) (a := 3) (b := 1) (l := n + n)
        (PlanarMatching.cast (by simp) (coeval 1).diagram.matching) (nested 2) (nested n)
  have hL := glueFn_insertFn_left (b := 1) (n := 0) (nested n) 2 5 x (by omega)
  have hx : pv x = pv ((coeval 1).diagram.matching.append (nested 2)) := pv_cast_eq _ _
  have hbase : glueFn 0 2 (pv x) = pv (nested 1) := by
    rw [hx, (glueFn_append_nested (a := 0) (b := 2) (coeval 1).diagram.matching).1,
      matching_coeval, pv_cast_eq]
  have hbasec : glueCircles 0 2 (pv x) = 0 := by
    rw [hx, (glueFn_append_nested (a := 0) (b := 2) (coeval 1).diagram.matching).2]
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_coeval, pv_cast_eq, ← Category.assoc, matching_comp_eqToHom, pv_cast_eq,
      diagram_comp, TLDiagram.matching_comp, pv_glueMiddle]
    simp only [tensorObj_as, tensorUnit_as]
    rw [hApp, hL.1, hbase, show 5 - 2 * 2 = 1 from rfl, ← Nat.add_comm 1 n]
    simpa only [pv_insert_eq, pv_cast_eq] using (congrArg pv (insert_nested 1 n)).symm
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
    TLDiagram.matching_id, diagram_cap, eq_nested_one TLDiagram.cap.matching, pv_cast_eq,
    pv_insert_eq, tensorObj_as]
  funext q
  by_cases h1 : q < n
  · rw [insertFn_of_lt _ _ h1, insertFn_of_lt _ _ h1, pv_nested n (by omega),
      pv_nested (2 * n) (by omega), shiftGap_of_le (by omega), shiftGap_of_le (by omega)]; omega
  by_cases h2 : q < n + 2
  · rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega),
      insertFn_of_le_of_lt _ _ (by omega) h2, pv_nested 1 (by omega), shiftGap_of_lt (by omega)]
  by_cases h3 : q < n + 2 + (n + n)
  · rw [insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      pv_nested n (by omega), pv_nested (2 * n) (by omega), shiftGap_of_le (by omega)]; omega
  by_cases h4 : q < n + 2 + 3 * n
  · rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) h4, pv_nested n (by omega),
      pv_nested (2 * n) (by omega), shiftGap_of_lt (by omega), shiftGap_of_lt (by omega)]; omega
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
    simp only [tensorObj_as, tensorUnit_as,
      show n + (2 + n) + (n + (0 + n)) = n + 2 + 3 * n by omega,
      show n + (0 + n) + 0 = n + n by omega]
    simpa only [x, show 3 * n + (n + n) = 5 * n by omega, show n + 3 * n = 2 * n + 2 * n by omega,
      Nat.add_zero, pv_cast_eq, pv_append_eq, tensorObj_as, tensorUnit_as] using
      appendFn_insertFn_left (a := n) (b := 3 * n) (l := 2) (k := n + n)
        (PlanarMatching.cast (by omega) (nested (2 * n))) (nested 1)
        (PlanarMatching.cast (by simp) (eval n).diagram.matching)
  have hR := glueFn_insertFn_right (a := n) (n := 2 * n) (nested 1) (2 * n) (5 * n) x
    (by omega) (by omega)
  let w : PlanarMatching (2 * n + 0) :=
    PlanarMatching.cast (by simp; omega) (eval n).diagram.matching
  have hx : pv x = pv ((nested (2 * n)).append w) := by
    simp only [x, w, show n + n + 0 = 2 * n + 0 by omega, pv_cast_eq, pv_append_eq,
      tensorObj_as, tensorUnit_as]
  have hbase : glueFn (2 * n) (2 * n) (pv x) = pv (nested n) := by
    rw [hx, (glueFn_nested_append w).1, pv_cast_eq, matching_eval]
  have hbasec : glueCircles (2 * n) (2 * n) (pv x) = 0 := by
    rw [hx, (glueFn_nested_append w).2]
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_eval, matching_eqToHom_comp, pv_cast_eq, diagram_comp, TLDiagram.matching_comp,
      pv_glueMiddle]
    simp only [tensorObj_as]
    rw [show n + (2 + n) = 2 * n + 2 by omega, show n + (0 + n) = 2 * n by omega, hApp, hR.1,
      hbase, show 5 * n - 2 * (2 * n) = n by omega]
    simpa only [pv_insert_eq, pv_cast_eq] using (congrArg pv (insert_nested n 1)).symm
  · rw [circles_eval, circles_eqToHom_comp, diagram_comp, TLDiagram.circles_comp,
      glueMiddleCircles_eq]
    simp only [tensorObj_as]
    rw [show n + (2 + n) = 2 * n + 2 by omega, show n + (0 + n) = 2 * n by omega, hApp, hR.2,
      hbasec, circles_eqToHom_comp, circles_eval, diagram_whiskerLeft, diagram_whiskerRight,
      TLDiagram.circles_tensor, TLDiagram.circles_tensor, TLDiagram.circles_id,
      diagram_cap, TLDiagram.circles_cap]

/-- The nested evaluation on `n + 1` strands can also be factored by applying `eval n` on the
inner `2n` strands and then capping the outer two strands. -/
theorem eval_succ_outer (n : ℕ) :
    eval (n + 1) =
      eqToHom (by ext; simp; omega) ≫ of 1 ◁ (eval n ▷ of 1) ≫
        eqToHom (by ext; simp) ≫ cap := by
  induction n with
  | zero =>
    rw [eval_one, show eval 0 = eqToHom (rfl : of 0 ⊗ of 0 = 𝟙_ TLDiagCat) from rfl,
      eqToHom_whiskerRight, whiskerLeft_eqToHom, eqToHom_trans_assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  | succ n ih =>
    have ih' : of 1 ◁ (eval n ▷ of 1) ≫ eqToHom (by ext; simp) ≫ cap =
        eqToHom (by ext; simp; omega) ≫ eval (n + 1) := by
      have h := congrArg (eqToHom (by ext; simp; omega :
        of 1 ⊗ ((of n ⊗ of n) ⊗ of 1) = of (n + 1) ⊗ of (n + 1)) ≫ ·) ih
      simpa only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using h.symm
    have hstep : ∀ {A B C D E F : TLDiagCat} {f : A ⟶ B} {g : C ⟶ D} {k : E ⟶ F}
        {h₁ : B = D} {h₂ : A = C} {h₃ : D = F} {h₄ : C = E},
        f ≫ eqToHom h₁ = eqToHom h₂ ≫ g → g ≫ eqToHom h₃ = eqToHom h₄ ≫ k →
          f ≫ eqToHom (h₁.trans h₃) = eqToHom (h₂.trans h₄) ≫ k := by
      rintro _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl h1 h2
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h1 h2 ⊢
      exact h1.trans h2
    have h1 := congrArg (of 1 ◁ ·) (associator_naturality_middle (of n) (cap ▷ of n) (of 1))
    have h2 := congrArg (fun u => of 1 ◁ (of n ◁ u)) (associator_naturality_left cap (of n) (of 1))
    have h3 := associator_inv_naturality_right (of 1) (of n) (cap ▷ of (n + 1))
    have h4 : ∀ {X Y : TLDiagCat} (h : X = Y), X ◁ (cap ▷ of (n + 1)) ≫ eqToHom (by rw [h]) =
        eqToHom (by rw [h]) ≫ Y ◁ (cap ▷ of (n + 1)) := by rintro _ _ rfl; simp
    simp only [MonoidalCategory.whiskerLeft_comp, associator_eq, eqToIso.hom, eqToIso.inv,
      whiskerLeft_eqToHom] at h1 h2 h3
    have hnat' := congrArg (· ≫ eqToHom (by ext; simp :
        of (n + 1) ⊗ (𝟙_ TLDiagCat ⊗ of (n + 1)) = of (n + 1) ⊗ of (n + 1)) ≫ eval (n + 1))
      (hstep (hstep (hstep h1 h2) h3) (h4 (congrArg of (Nat.add_comm 1 n))))
    simp only [Category.assoc, eqToHom_trans_assoc] at hnat'
    conv_rhs => rw [eval_succ n]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, eqToHom_whiskerRight,
      whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc]
    rw [ih', eqToHom_trans_assoc, hnat', eqToHom_trans_assoc, ← eval_succ (n + 1)]

/-! ### Self-duality and the rigid monoidal category structure -/

open PlanarMatching in
/-- The two zigzag identities at the generating object `of 1`. -/
private theorem zigzag_one_left :
    of 1 ◁ coeval 1 ≫ (α_ (of 1) (of 1) (of 1)).inv ≫ eval 1 ▷ of 1 =
      (ρ_ (of 1)).hom ≫ (λ_ (of 1)).inv := by
  apply hom_ext; ext : 1
  · exact (eq_nested_one _).trans (eq_nested_one _).symm
  · have hpv :
        pv ((of 1 ◁ cup).diagram.matching.append
            ((eqToHom (congrArg of (Nat.add_assoc 1 1 1)).symm ≫ cap ▷ of 1).diagram.matching)) =
          fun q => match q with
            | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => q := by
      simp only [pv_append_eq, matching_eqToHom_comp, pv_cast_eq, diagram_whiskerLeft,
        diagram_whiskerRight, TLDiagram.matching_tensor, TLDiagram.matching_id, diagram_cup,
        diagram_cap, pv_insert_eq, eq_nested_one TLDiagram.cup.matching,
        eq_nested_one TLDiagram.cap.matching, tensorObj_as]
      funext q; match q with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [appendFn, insertFn, shiftGap, pv_nested]
      | q + 8 => rw [appendFn_of_le _ _ (by omega)]; rfl
    rw [rightUnitor_hom, leftUnitor_eq, eqToIso.inv,
      show 𝟙 (of 1) ≫ eqToHom (congrArg of (Nat.zero_add 1)).symm = eqToHom _ from
        Category.id_comp _,
      circles_eqToHom, coeval_one, eval_one, associator_eq, eqToIso.inv, diagram_comp,
      TLDiagram.circles_comp, glueMiddleCircles_eq, hpv]
    simp only [tensorObj_as, tensorUnit_as, circles_eqToHom_comp, diagram_whiskerLeft,
      diagram_whiskerRight, TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cup,
      diagram_cap, TLDiagram.circles_cup, TLDiagram.circles_cap]
    decide

open PlanarMatching in
private theorem zigzag_one_right :
    coeval 1 ▷ of 1 ≫ (α_ (of 1) (of 1) (of 1)).hom ≫ of 1 ◁ eval 1 =
      (λ_ (of 1)).hom ≫ (ρ_ (of 1)).inv := by
  apply hom_ext; ext : 1
  · exact (eq_nested_one _).trans (eq_nested_one _).symm
  · have hpv :
        pv ((cup ▷ of 1).diagram.matching.append
            ((eqToHom (congrArg of (Nat.add_assoc 1 1 1)) ≫ of 1 ◁ cap).diagram.matching)) =
          fun q => match q with
            | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 7 | 5 => 6 | 6 => 5 | 7 => 4 | _ => q := by
      simp only [pv_append_eq, matching_eqToHom_comp, pv_cast_eq, diagram_whiskerRight,
        diagram_whiskerLeft, TLDiagram.matching_tensor, TLDiagram.matching_id, diagram_cup,
        diagram_cap, pv_insert_eq, eq_nested_one TLDiagram.cup.matching,
        eq_nested_one TLDiagram.cap.matching, tensorObj_as]
      funext q; match q with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [appendFn, insertFn, shiftGap, pv_nested]
      | q + 8 => rw [appendFn_of_le _ _ (by omega)]; rfl
    rw [leftUnitor_eq, eqToIso.hom, rightUnitor_inv,
      show eqToHom (congrArg of (Nat.zero_add 1)) ≫ 𝟙 (of 1) = eqToHom _ from Category.comp_id _,
      circles_eqToHom, coeval_one, eval_one, associator_eq, eqToIso.hom, diagram_comp,
      TLDiagram.circles_comp, glueMiddleCircles_eq, hpv]
    simp only [tensorObj_as, tensorUnit_as, circles_eqToHom_comp, diagram_whiskerRight,
      diagram_whiskerLeft, TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cup,
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
    let p1 : ExactPairing (of 1) (of 1) := ⟨coeval 1, eval 1, zigzag_one_left, zigzag_one_right⟩
    let pn : ExactPairing (of n) (of n) := ⟨coeval n, eval n, ih.1, ih.2⟩
    let pt : ExactPairing (of 1 ⊗ of n) (of n ⊗ of 1) := @ExactPairing.tensor _ _ _ _ _ _ _ p1 pn
    let ι : of (n + 1) ≅ of 1 ⊗ of n := eqToIso (congrArg of (Nat.add_comm n 1))
    let p : ExactPairing (of (n + 1)) (of (n + 1)) := @exactPairingCongrLeft _ _ _ _ _ _ pt ι
    have hcoev : p.coevaluation' = coeval (n + 1) := by
      have h1 : pt.coevaluation' = coeval 1 ≫ (ρ_ (of 1)).inv ▷ of 1 ≫ (of 1 ◁ coeval n) ▷ of 1 ≫
          (α_ (of 1) (of n) (of n)).inv ▷ of 1 ≫ (α_ (of 1 ⊗ of n) (of n) (of 1)).hom := by
        rw [show pt.coevaluation' = @ExactPairing.coevaluation _ _ _ _ _ pt from rfl,
          @ExactPairing.tensor_coevaluation _ _ _ _ _ _ _ p1 pn]
        dsimp only [ExactPairing.coevaluation, p1, pn]; monoidal
      change pt.coevaluation' ≫ ι.inv ▷ (of n ⊗ of 1) = coeval (n + 1)
      rw [h1, rightUnitor_inv, id_whiskerRight, Category.id_comp, coeval_succ n]
      simp only [ι, associator_eq, eqToIso.hom, eqToIso.inv, eqToHom_whiskerRight, eqToHom_trans,
        Category.assoc]
    have hev : p.evaluation' = eval (n + 1) := by
      have h1 : pt.evaluation' = (α_ (of n) (of 1) (of 1 ⊗ of n)).hom ≫
          of n ◁ (α_ (of 1) (of 1) (of n)).inv ≫ of n ◁ (eval 1 ▷ of n) ≫
          of n ◁ (λ_ (of n)).hom ≫ eval n := by
        rw [show pt.evaluation' = @ExactPairing.evaluation _ _ _ _ _ pt from rfl,
          @ExactPairing.tensor_evaluation _ _ _ _ _ _ _ p1 pn]
        dsimp only [ExactPairing.evaluation, p1, pn]; monoidal
      change (of n ⊗ of 1) ◁ ι.hom ≫ pt.evaluation' = eval (n + 1)
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
theorem rightDual_eq (X : TLDiagCat) : (Xᘁ : TLDiagCat) = X := (rfl)

@[simp]
theorem leftDual_eq (X : TLDiagCat) : (ᘁX : TLDiagCat) = X := (rfl)

@[simp]
theorem coevaluation_rightDual (X : TLDiagCat) : η_ X Xᘁ = coeval X.as := (rfl)

@[simp]
theorem evaluation_rightDual (X : TLDiagCat) : ε_ X Xᘁ = eval X.as := (rfl)

@[simp]
theorem coevaluation_leftDual (X : TLDiagCat) : η_ (ᘁX) X = coeval X.as := (rfl)

@[simp]
theorem evaluation_leftDual (X : TLDiagCat) : ε_ (ᘁX) X = eval X.as := (rfl)

@[simp]
theorem coevaluation_of_one : η_ (of 1) (of 1) = cup := coeval_one

@[simp]
theorem evaluation_of_one : ε_ (of 1) (of 1) = cap := eval_one

/-- Closing `n` nested strands produces `n` closed circles. -/
theorem coeval_comp_eval (n : ℕ) : coeval n ≫ eval n = ((End.of circle) ^ n).asHom := by
  induction n with
  | zero => rw [pow_zero]; exact Category.id_comp (𝟙 (of 0))
  | succ n ih =>
    let s : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat := ((End.of circle) ^ n).asHom
    have h1 : (α_ (of 1) (𝟙_ TLDiagCat) (of 1)).hom ≫ of 1 ◁ (λ_ (of 1)).hom = 𝟙 (of 1 ⊗ of 1) := by
      rw [associator_eq, leftUnitor_eq, eqToIso.hom, eqToIso.hom, whiskerLeft_eqToHom,
        eqToHom_trans]; rfl
    have h2 : of 1 ◁ (of 1 ◁ s) = (of 1 ⊗ of 1) ◁ s := by
      have ha := associator_naturality_right (of 1) (of 1) s
      rw [associator_eq, eqToIso.hom, eqToHom_refl] at ha
      exact (Category.id_comp _).symm.trans (ha.symm.trans (Category.comp_id _))
    rw [coeval_succ n, eval_succ_outer]
    simp only [Category.assoc]
    rw [← Category.assoc (eqToHom _) (eqToHom _),
      show eqToHom (by ext; simp; omega) ≫ eqToHom (by ext; simp; omega) =
        (α_ (of 1) (of n ⊗ of n) (of 1)).hom by simp [associator_eq]; rfl,
      show eqToHom (by ext; simp : of 1 ⊗ (𝟙_ TLDiagCat ⊗ of 1) = of 2) =
        of 1 ◁ (λ_ (of 1)).hom by rw [leftUnitor_eq, eqToIso.hom, whiskerLeft_eqToHom],
      ← Category.assoc ((of 1 ◁ coeval n) ▷ of 1),
      associator_naturality_middle (of 1) (coeval n) (of 1), Category.assoc,
      ← Category.assoc (of 1 ◁ (coeval n ▷ of 1)), ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.comp_whiskerRight, ih, ← eval_one,
      ← Category.assoc (of 1 ◁ (s ▷ of 1)), ← MonoidalCategory.whiskerLeft_comp,
      show s ▷ of 1 ≫ (λ_ (of 1)).hom = (λ_ (of 1)).hom ≫ (λ_ (of 1)).inv ≫ s ▷ of 1 ≫
        (λ_ (of 1)).hom by simp,
      ← (circlesCommuteAt_iff s (of 1)).mp (circlesCommuteAt s (of 1)),
      show (ρ_ (of 1)).inv ≫ of 1 ◁ s ≫ (ρ_ (of 1)).hom = of 1 ◁ s by
        rw [rightUnitor_inv, rightUnitor_hom, Category.id_comp]; exact Category.comp_id _,
      MonoidalCategory.whiskerLeft_comp, h2, Category.assoc, ← Category.assoc (α_ _ _ _).hom, h1,
      show 𝟙 (of 1 ⊗ of 1) ≫ (of 1 ⊗ of 1) ◁ s ≫ eval 1 = _ from Category.id_comp _,
      whiskerLeft_scalar_comp (Y := of 1 ⊗ of 1) s (eval 1), ← Category.assoc,
      coeval_one, eval_one, cup_comp_cap, pow_succ', End.mul_asHom]
    exact scalar_comm circle s

/-! ### Corner-dragging and Frobenius reciprocity -/

open PlanarMatching in
/-- Dragging the top-right corner down via `tensorRightHomEquiv` at `of 1` agrees with
`(TLDiagram.dragRight n m).symm`. -/
theorem diagram_tensorRightHomEquiv_symm (n m : ℕ) (g : of n ⟶ of m ⊗ of 1) :
    ((tensorRightHomEquiv (of n) (of 1) (of 1) (of m)).symm g).diagram =
      (TLDiagram.dragRight n m).symm g.diagram := by
  have hdef : (tensorRightHomEquiv (of n) (of 1) (of 1) (of m)).symm g =
      g ▷ of 1 ≫ eqToHom (congrArg of (Nat.add_assoc m 1 1)) ≫ of m ◁ cap := by
    dsimp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
    rw [evaluation_of_one, associator_eq, eqToIso.hom, rightUnitor_hom,
      show of m ◁ cap ≫ 𝟙 (of m) = of m ◁ cap from Category.comp_id _]
  let rhs := (eqToHom (congrArg of (Nat.add_assoc m 1 1)) ≫ of m ◁ cap).diagram.matching
  have hsplit := glueFn_add (n + 1) 1 (m + 1) (pv ((g ▷ of 1).diagram.matching.append rhs))
  rw [show 1 + (m + 1) = m + 1 + 1 by omega] at hsplit
  let w : PlanarMatching ((n + 1 + 1) + (m + 1)) :=
    PlanarMatching.cast (by simp; omega) (g ▷ of 1).diagram.matching
  obtain ⟨hinner_m, hinner_c⟩ := glueFn_append_nested w
  have hw : pv (w.append (nested (m + 1))) = pv ((g ▷ of 1).diagram.matching.append rhs) := by
    have hmcap : (of m ◁ cap).diagram.matching =
        PlanarMatching.cast (by simp; omega) (nested (m + 1)) := by
      rw [diagram_whiskerLeft, TLDiagram.matching_tensor, TLDiagram.matching_id, diagram_cap,
        eq_nested_one TLDiagram.cap.matching, insert_nested, PlanarMatching.cast_cast]
    simp only [w, rhs, matching_eqToHom_comp, hmcap, pv_append_eq, pv_cast_eq, tensorObj_as,
      show n + 1 + 1 + (m + 1) = n + 1 + (m + 1 + 1) by omega,
      show m + 1 + (m + 1) = m + 1 + 1 + (m + 0) by omega]
  rw [hw, pv_cast_eq] at hinner_m; rw [hw] at hinner_c
  let φ := insertFn n (m + 1) 2 (pv g.diagram.matching) (pv (nested 1))
  have hphi : pv (g ▷ of 1).diagram.matching = φ := by
    rw [diagram_whiskerRight, TLDiagram.matching_tensor, TLDiagram.matching_id, pv_cast_eq,
      pv_insert_eq]; simp only [φ, tensorObj_as]
  have hφ1 : φ (n + 1) = n := by
    rw [show φ (n + 1) = _ from insertFn_of_le_of_lt _ _ (by omega) (by omega),
      pv_nested 1 (by omega)]; omega
  have hφ2 : φ (n + 2) = shiftGap n 2 (pv g.diagram.matching n) := by
    rw [show φ (n + 2) = _ from insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      show n + 2 - 2 = n by omega]
  have hc1 : circleInd (n + 1) φ = 0 := by rw [circleInd, hφ1]; simp [show n ≠ n + 1 + 1 by omega]
  have hstep : contractFn (n + 1) φ = pv g.diagram.matching := by
    have : pv g.diagram.matching n ≠ n := pv_ne g.diagram.matching (by simp)
    have hrejoin : ∀ v, unskipN (n + 1) (rejoin φ (n + 1) (shiftGap n 2 v)) = v := fun v => by
      by_cases hvn : v = n
      · rw [hvn, shiftGap_of_le le_rfl, rejoin_of_eq_right _ rfl, hφ1, unskipN_of_lt (by omega)]
      · rw [rejoin_of_ne _ (by simp only [shiftGap]; split_ifs <;> omega)
          (by simp only [shiftGap]; split_ifs <;> omega)]
        simp only [shiftGap, unskipN]; split_ifs <;> omega
    funext q; rw [contractFn_apply]
    by_cases h1 : q < n
    · rw [skipN_of_lt (by omega), show φ q = _ from insertFn_of_lt _ _ h1]; exact hrejoin _
    by_cases h2 : q = n
    · subst q
      rw [skipN_of_lt (by omega), show φ n = _ from insertFn_of_le_of_lt _ _ le_rfl (by omega),
        pv_nested 1 (by omega), show n + (1 + 1 - 1 - (n - n)) = n + 1 by omega,
        rejoin_of_eq_left _ rfl, hφ2]
      simp only [shiftGap, unskipN]; split_ifs <;> omega
    by_cases h3 : q < n + (m + 1)
    · rw [skipN_of_le (by omega),
        show φ (q + 2) = _ from insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
        show q + 2 - 2 = q by omega]; exact hrejoin _
    · rw [skipN_of_le (by omega), show φ (q + 2) = _ from insertFn_of_le _ _ (by omega),
        rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega),
        pv_of_le g.diagram.matching (by simp; omega)]; omega
  rw [hdef]; ext : 1
  · apply eq_of_pv_eq
    rw [diagram_comp, TLDiagram.matching_comp, pv_glueMiddle]; simp only [tensorObj_as]
    rw [hsplit.1, hinner_m, hphi, glueFn, glueFn, hstep, TLDiagram.matching_dragRight_symm,
      pv_cast_eq]
  · rw [diagram_comp, TLDiagram.circles_comp, glueMiddleCircles_eq]; simp only [tensorObj_as]
    rw [hsplit.2, hinner_m, hinner_c, hphi, glueCircles, glueCircles, hc1, diagram_whiskerRight,
      TLDiagram.circles_tensor, TLDiagram.circles_id, circles_eqToHom_comp, diagram_whiskerLeft,
      TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cap, TLDiagram.circles_cap,
      TLDiagram.circles_dragRight_symm]; omega

/-- Dragging the bottom-right corner up via `tensorRightHomEquiv` at `of 1` agrees with
`TLDiagram.dragRight n m`. -/
theorem diagram_tensorRightHomEquiv (n m : ℕ) (f : of n ⊗ of 1 ⟶ of m) :
    (tensorRightHomEquiv (of n) (of 1) (of 1) (of m) f).diagram =
      TLDiagram.dragRight n m f.diagram := by
  have h := diagram_tensorRightHomEquiv_symm n m (tensorRightHomEquiv (of n) (of 1) (of 1) (of m) f)
  rw [Equiv.symm_apply_apply] at h; exact (Equiv.symm_apply_eq (TLDiagram.dragRight n m)).mp h.symm

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
  · have hrot1 : ∀ j : Fin K, ((finRotate K j : Fin K) : ℕ) = (j + 1) % K := fun j => by
      rw [show finRotate K j = (finRotate K ^ 1) j by simp, Fin.coe_finRotate_pow]
    let i : Fin K := ⟨if q = 0 then K - 1 else q - 1, by split_ifs <;> omega⟩
    have hrot := congrArg Fin.val (PlanarMatching.rotate_apply_val_apply x i)
    rw [← pv_coe, hrot1, hrot1, ← pv_coe] at hrot
    have hi : ((i : ℕ) + 1) % K = q := by
      dsimp only [i]; split_ifs with h0
      · rw [show K - 1 + 1 = K by omega, Nat.mod_self, h0]
      · rw [show q - 1 + 1 = q by omega, Nat.mod_eq_of_lt hq]
    rw [hi] at hrot; rw [hrot]; simp only [hq, ↓reduceIte, i]
    split_ifs with h0 heq
    · have := pv_ne x (by omega : K - 1 < K); have := pv_lt x (by omega : K - 1 < K)
      exact Nat.mod_eq_of_lt (by omega)
    · rw [heq, show K - 1 + 1 = K by omega, Nat.mod_self]
    · have := pv_lt x (by omega : q - 1 < K); exact Nat.mod_eq_of_lt (by omega)
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
  have hdef : (tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm g =
      (of 1 ◁ g ≫ (eqToHom (congrArg of (Nat.add_assoc 1 1 m).symm) ≫ cap ▷ of m)) ≫
        eqToHom (congrArg of (Nat.zero_add m)) := by
    dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
    rw [evaluation_of_one, associator_eq, leftUnitor_eq, eqToIso.inv, eqToIso.hom]
    simp only [Category.assoc]
  let K := n + (1 + m)
  let base : PlanarMatching (1 + n + (1 + (1 + m))) := (of 1 ◁ g).diagram.matching
  let rhs := (eqToHom (congrArg of (Nat.add_assoc 1 1 m).symm) ≫ cap ▷ of m).diagram.matching
  let mid : PlanarMatching (K + 2 + 2) := PlanarMatching.cast (by omega) (base.append (nested 1))
  have hglt : ∀ r < K, pv g.diagram.matching r < K := fun r hr => by
    simpa [K] using pv_lt g.diagram.matching (by simpa [K] using hr)
  have hApp : pv (base.append rhs) = appendFn (K + 2 + 2) (m + m) (pv mid) (pv (nested m)) := by
    have hcapm : (cap ▷ of m).diagram.matching =
        PlanarMatching.cast (by simp; omega) ((nested 1).append (nested m)) := by
      apply eq_of_pv_eq
      rw [diagram_whiskerRight, TLDiagram.matching_tensor, TLDiagram.matching_id, diagram_cap,
        eq_nested_one TLDiagram.cap.matching, pv_cast_eq, pv_cast_eq, pv_insert_eq, pv_append_eq]
      exact insertFn_zero_right (nested 1) _
    rw [pv_append_eq, show pv rhs = pv (cap ▷ of m).diagram.matching by
        simp [rhs, matching_eqToHom_comp, pv_cast_eq], hcapm, pv_cast_eq, pv_append_eq]
    simp only [mid, pv_cast_eq, pv_append_eq, tensorObj_as,
      show 1 + n + (1 + (1 + m)) = K + 2 by omega,
      show 1 + (1 + m) + (0 + m) = 2 + (m + m) by omega]
    exact (appendFn_assoc (K + 2) 2 (m + m) _ _ _).symm
  have hsplit := glueFn_add (1 + n) m 2 (pv (base.append rhs))
  rw [show m + 2 = 1 + (1 + m) by omega] at hsplit
  have hL := glueFn_appendFn_left (n := 1 + n + m) (nested m) 2 (K + 2 + 2) mid (by omega)
  have hmid_pv : ∀ q, pv mid q =
      if q = 0 then K + 1 else if q < K + 1 then 1 + pv g.diagram.matching (q - 1)
      else if q = K + 1 then 0 else if q = K + 2 then K + 3
      else if q = K + 3 then K + 2 else q := fun q => by
    simp only [mid, base, diagram_whiskerLeft, TLDiagram.matching_tensor, TLDiagram.matching_id,
      pv_cast_eq, pv_append_eq, pv_insert_eq, tensorObj_as]
    by_cases h0 : q = 0
    · subst h0; simp [appendFn, insertFn, shiftGap, pv_nested, K]; omega
    by_cases h1 : q < K + 1
    · rw [appendFn_of_lt _ _ (by omega), insertFn_of_le_of_lt _ _ (by omega) (by omega)]
      simp [h0, h1]
    by_cases h2 : q = K + 1
    · subst h2; rw [appendFn_of_lt _ _ (by omega),
        insertFn_of_le_of_lt_add _ _ (by omega) (by omega)]; simp [pv_nested, shiftGap, K]
    by_cases h3 : q < K + 4
    · rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), pv_nested 1 (by omega)]
      split_ifs <;> omega
    · rw [appendFn_of_le _ _ (by omega)]; split_ifs <;> omega
  let f₁ : ℕ → ℕ := fun q =>
    if q = 0 then K + 1 else if q < K + 1 then 1 + pv g.diagram.matching (q - 1)
    else if q = K + 1 then 0 else q
  have hstep1 : contractFn (K + 1) (pv mid) = f₁ := by
    have hm1 : pv mid (K + 1) = 0 := by rw [hmid_pv]; simp
    have hm2 : pv mid (K + 2) = K + 3 := by rw [hmid_pv]; simp
    funext q; rw [contractFn_apply]; dsimp only [f₁]
    by_cases h0 : q = 0
    · subst h0; rw [skipN_of_lt (by omega), hmid_pv]
      simp only [↓reduceIte]; rw [rejoin_of_eq_left _ rfl, hm2, unskipN_of_le (by omega)]; omega
    by_cases h1 : q < K + 1
    · have := hglt (q - 1) (by omega)
      rw [skipN_of_lt (by omega), hmid_pv]; simp only [h0, h1, ↓reduceIte]
      rw [rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]
    by_cases h2 : q = K + 1
    · subst h2
      have hq : pv mid (K + 1 + 2) = K + 2 := by rw [show K + 1 + 2 = K + 3 by omega, hmid_pv]; simp
      rw [skipN_of_le (by omega), hq, rejoin_of_eq_right _ rfl, hm1, unskipN_of_lt (by omega)]; simp
    · have hq : pv mid (q + 2) = q + 2 := by rw [hmid_pv]; repeat rw [ite_eq_right (by omega)]
      rw [skipN_of_le (by omega), hq, rejoin_of_ne _ (by omega) (by omega),
        unskipN_of_le (by omega)]; simp [h0, h1, h2]
  have hK_lt : pv g.diagram.matching (K - 1) < K := hglt (K - 1) (by omega)
  have hs1 : f₁ K = 1 + pv g.diagram.matching (K - 1) := by dsimp [f₁]; split_ifs <;> omega
  have hstep2 : contractFn K f₁ = pv (PlanarMatching.rotate K g.diagram.matching) := by
    have hK_ne : pv g.diagram.matching (K - 1) ≠ K - 1 :=
      pv_ne g.diagram.matching (by simp only [tensorObj_as]; dsimp only [K]; omega)
    have hs2 : f₁ (K + 1) = 0 := by dsimp [f₁]; split_ifs <;> omega
    funext q; rw [contractFn_apply, pv_rotate_eq]
    by_cases h0 : q = 0
    · subst h0; rw [skipN_of_lt (by omega), show f₁ 0 = K + 1 by simp [f₁],
        rejoin_of_eq_right _ rfl, hs1, unskipN_of_lt (by omega)]; split_ifs <;> omega
    by_cases h1 : q < K
    · have := hglt (q - 1) (by omega)
      rw [skipN_of_lt h1, show f₁ q = 1 + pv g.diagram.matching (q - 1) by
        dsimp [f₁]; split_ifs <;> omega]; simp only [h0, h1, ↓reduceIte]
      by_cases heq : pv g.diagram.matching (q - 1) = K - 1
      · simp only [heq, ↓reduceIte]
        rw [show 1 + (K - 1) = K by omega, rejoin_of_eq_left _ rfl, hs2, unskipN_of_lt (by omega)]
      · simp only [heq, ↓reduceIte]
        rw [rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]; omega
    · rw [skipN_of_le (by omega), show f₁ (q + 2) = q + 2 by dsimp [f₁]; split_ifs <;> omega,
        rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]; simp [h1]
  have hmid_glue :
      glueFn (1 + n + m) 2 (pv mid) = pv (PlanarMatching.rotate K g.diagram.matching) ∧
        glueCircles (1 + n + m) 2 (pv mid) = 0 := by
    have hc1 : circleInd (K + 1) (pv mid) = 0 := by rw [circleInd, hmid_pv]; simp
    have hc2 : circleInd K f₁ = 0 := by
      rw [circleInd, hs1]; simp [show 1 + pv g.diagram.matching (K - 1) ≠ K + 1 by omega]
    rw [show 1 + n + m = K by omega]
    exact ⟨by rw [glueFn, glueFn, glueFn, Nat.add_zero, hstep1, hstep2],
      by rw [glueCircles, glueCircles, glueCircles, Nat.add_zero, hc1, hstep1, hc2]⟩
  let rot : PlanarMatching ((1 + n) + m) :=
    PlanarMatching.cast (by omega) (PlanarMatching.rotate K g.diagram.matching)
  have hPhase1 : glueFn (1 + n + m) 2 (pv (base.append rhs)) = pv (rot.append (nested m)) := by
    rw [hApp, ← hL.1, hmid_glue.1, pv_append_eq, pv_cast_eq,
      show K + 2 + 2 - 2 * 2 = 1 + n + m by omega]
  obtain ⟨hPhase2, hPhase2c⟩ := glueFn_append_nested rot
  rw [hdef]; constructor
  · apply eq_of_pv_eq
    rw [matching_comp_eqToHom, pv_cast_eq, diagram_comp, TLDiagram.matching_comp, pv_glueMiddle]
    simp only [tensorObj_as]; rw [hsplit.1, hPhase1, hPhase2, pv_cast_eq]
  · rw [circles_comp_eqToHom, diagram_comp, TLDiagram.circles_comp, glueMiddleCircles_eq]
    simp only [tensorObj_as]
    rw [hsplit.2, hPhase1, hApp, hL.2, hmid_glue.2, hPhase2c, diagram_whiskerLeft,
      TLDiagram.circles_tensor, TLDiagram.circles_id, circles_eqToHom_comp, diagram_whiskerRight,
      TLDiagram.circles_tensor, TLDiagram.circles_id, diagram_cap, TLDiagram.circles_cap]; omega

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
      (eqToHom (congrArg of (Nat.add_comm 1 n)) ≫ f) ≫ eqToHom (congrArg of (Nat.add_comm 1 m))
  have hg := diagram_tensorLeftHomEquiv_symm n m g
  rw [show eqToHom (congrArg of (Nat.add_comm n 1)) ≫
      (tensorLeftHomEquiv (of n) (of 1) (of 1) (of m)).symm
        (g ≫ eqToHom (congrArg of (Nat.add_comm m 1))) = f by
    simp only [g, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Equiv.symm_apply_apply, eqToHom_trans_assoc, Category.id_comp]] at hg
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
      rw [eval_zero, show g ▷ of 0 ≫ 𝟙 (of 0) = g ▷ of 0 from Category.comp_id _]
      exact hom_ext (TLDiagram.tensor_id_zero g.diagram)
    rw [hcomp]; exact ⟨by simp, rfl⟩
  | k + 1, a, g => by
    let g' : of (a + 1) ⟶ of k := (tensorRightHomEquiv (of a) (of 1) (of 1) (of k)).symm g
    have hfact :
        g ▷ of (k + 1) ≫ eval (k + 1) =
          eqToHom (by ext; simp; omega) ≫ g' ▷ of k ≫ eval k := by
      let ι : of (k + 1) ≅ of 1 ⊗ of k := eqToIso (congrArg of (Nat.add_comm k 1))
      rw [eval_succ]; dsimp only [g', tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
      rw [evaluation_of_one, comp_whiskerRight, comp_whiskerRight, comp_whiskerRight]
      suffices hco :
          eqToHom (by ext; simp; omega : of a ⊗ of (k + 1) = (of a ⊗ of 1) ⊗ of k) ≫
              (g ▷ of 1) ▷ of k ≫ (α_ (of k) (of 1) (of 1)).hom ▷ of k ≫
              (of k ◁ cap) ▷ of k ≫ (ρ_ (of k)).hom ▷ of k =
            g ▷ of (k + 1) ≫ eqToHom (by ext; simp; omega) ≫ of k ◁ (cap ▷ of k) ≫
              eqToHom (by ext; simp) by
        simpa only [Category.assoc] using (congrArg (· ≫ eval k) hco).symm
      rw [show eqToHom (by ext; simp; omega : of a ⊗ of (k + 1) = (of a ⊗ of 1) ⊗ of k) =
            of a ◁ ι.hom ≫ (α_ (of a) (of 1) (of k)).inv by
            simp [ι, associator_eq, whiskerLeft_eqToHom],
        Category.assoc, ← Category.assoc (α_ _ _ _).inv, ← associator_inv_naturality_left g,
        ← Category.assoc (of a ◁ ι.hom), ← Category.assoc (of a ◁ ι.hom), whisker_exchange g ι.hom,
        Category.assoc, Category.assoc, ← Category.assoc (of (k + 1) ◁ ι.hom),
        ← Category.assoc (of (k + 1) ◁ ι.hom ≫ _), Category.assoc (of (k + 1) ◁ ι.hom),
        show of (k + 1) ◁ ι.hom ≫ (α_ (of (k + 1)) (of 1) (of k)).inv ≫
            (α_ (of k) (of 1) (of 1)).hom ▷ of k =
            eqToHom (by ext; simp; omega) ≫ (α_ (of k) (of 2) (of k)).inv by
          rw [associator_eq (of k) (of 1) (of 1), associator_eq (of (k + 1)) (of 1) (of k),
            associator_eq (of k) (of 2) (of k)]
          simp only [ι, eqToIso.hom, eqToIso.inv, whiskerLeft_eqToHom, eqToHom_whiskerRight,
            eqToHom_trans],
        Category.assoc, ← Category.assoc (α_ (of k) (of 2) (of k)).inv,
        ← associator_inv_naturality_middle (of k) cap (of k), Category.assoc]
      congr 3
      rw [associator_eq, eqToIso.inv, show (ρ_ (of k)).hom = eqToHom (by ext; simp) from rfl,
        eqToHom_whiskerRight, eqToHom_trans]
    obtain ⟨ihm, ihc⟩ := diagram_whiskerRight_comp_eval k g'
    have hg' := diagram_tensorRightHomEquiv_symm a k g
    rw [hfact]
    exact ⟨by rw [matching_eqToHom_comp, ihm, congrArg TLDiagram.matching hg',
        TLDiagram.matching_dragRight_symm, PlanarMatching.cast_cast, PlanarMatching.cast_cast],
      by rw [circles_eqToHom_comp, ihc, congrArg TLDiagram.circles hg',
        TLDiagram.circles_dragRight_symm]⟩

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
      have hln := leftUnitor_naturality f
      rwa [show (λ_ (of 0)).hom = 𝟙 (of 0) by simp [leftUnitor_eq], ← eval_zero] at hln
    rw [hcomp, leftUnitor_eq, eqToIso.hom]
    exact ⟨by rw [matching_eqToHom_comp, pow_zero, Perm.one_apply], circles_eqToHom_comp _ _⟩
  | k + 1, a, f => by
    let ι : of (k + 1) ≅ of 1 ⊗ of k := eqToIso (congrArg of (Nat.add_comm k 1))
    let f₁ : of a ⟶ of 1 ⊗ of k := f ≫ ι.hom
    let f' : of 1 ⊗ of a ⟶ of k := (tensorLeftHomEquiv (of a) (of 1) (of 1) (of k)).symm f₁
    have hfact :
        of (k + 1) ◁ f ≫ eval (k + 1) =
          eqToHom (by ext; simp; omega) ≫ of k ◁ f' ≫ eval k := by
      rw [eval_succ]; dsimp only [f', tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
      rw [evaluation_of_one]; simp only [MonoidalCategory.whiskerLeft_comp]
      suffices hco :
          eqToHom (by ext; simp; omega : of (k + 1) ⊗ of a = of k ⊗ (of 1 ⊗ of a)) ≫
              of k ◁ (of 1 ◁ f₁) ≫ of k ◁ (α_ (of 1) (of 1) (of k)).inv ≫
              of k ◁ (cap ▷ of k) ≫ of k ◁ (λ_ (of k)).hom =
            of (k + 1) ◁ f ≫ eqToHom (by ext; simp; omega) ≫ of k ◁ (cap ▷ of k) ≫
              eqToHom (by ext; simp) by
        simpa only [Category.assoc] using (congrArg (· ≫ eval k) hco).symm
      rw [show eqToHom (by ext; simp; omega : of (k + 1) ⊗ of a = of k ⊗ (of 1 ⊗ of a)) =
            (α_ (of k) (of 1) (of a)).hom by simp [associator_eq],
        ← Category.assoc (α_ _ _ _).hom, ← associator_naturality_right (of k) (of 1) f₁]
      change (of (k + 1) ◁ (f ≫ ι.hom) ≫ (α_ (of k) (of 1) (of 1 ⊗ of k)).hom) ≫ _ = _
      rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, Category.assoc,
        ← Category.assoc (of (k + 1) ◁ ι.hom), ← Category.assoc (of (k + 1) ◁ ι.hom ≫ _),
        Category.assoc (of (k + 1) ◁ ι.hom),
        show of (k + 1) ◁ ι.hom ≫ (α_ (of k) (of 1) (of 1 ⊗ of k)).hom ≫
            of k ◁ (α_ (of 1) (of 1) (of k)).inv = eqToHom (by ext; simp; omega) by
          simp only [ι, associator_eq, eqToIso.hom, eqToIso.inv, whiskerLeft_eqToHom,
            eqToHom_trans],
        show of k ◁ (λ_ (of k)).hom = eqToHom (by ext; simp) by
          rw [leftUnitor_eq, eqToIso.hom, whiskerLeft_eqToHom]]
    obtain ⟨ihm, ihc⟩ := diagram_whiskerLeft_comp_eval k f'
    rw [hfact]
    refine ⟨?_, ?_⟩
    · rw [matching_eqToHom_comp, ihm, matching_tensorLeftHomEquiv_symm]; dsimp only [f₁, ι]
      rw [eqToIso.hom, matching_comp_eqToHom, ← PlanarMatching.cast_rotate,
        ← PlanarMatching.cast_rotate_pow, ← PlanarMatching.cast_rotate_pow,
        PlanarMatching.cast_cast, PlanarMatching.cast_cast, PlanarMatching.cast_cast,
        ← Perm.mul_apply, ← pow_succ]
    · rw [circles_eqToHom_comp, ihc, circles_tensorLeftHomEquiv_symm]; dsimp only [f₁, ι]
      rw [eqToIso.hom, circles_comp_eqToHom]

/-- The right adjoint mate `fᘁ : Y ⟶ X` of a morphism `f : X ⟶ Y` rotates the underlying diagram
by `180°` (horizontal reflection composed with vertical reflection). -/
theorem diagram_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) :
    (fᘁ).diagram = TLDiagram.reflect Y.as X.as (TLDiagram.verticalReflect X.as Y.as f.diagram) := by
  have hev : (fᘁ ▷ X ≫ eval X.as).diagram = (Y ◁ f ≫ eval Y.as).diagram :=
    congrArg Hom.diagram (rightAdjointMate_comp_evaluation f)
  obtain ⟨hLm, hLc⟩ := diagram_whiskerRight_comp_eval X.as (fᘁ)
  obtain ⟨hRm, hRc⟩ := diagram_whiskerLeft_comp_eval Y.as f
  ext : 1
  · apply PlanarMatching.eq_of_pv_eq
    have hm := congrArg (PlanarMatching.pv ∘ TLDiagram.matching) hev
    simp only [Function.comp_apply, hLm, hRm, PlanarMatching.pv_cast_eq] at hm
    rw [TLDiagram.matching_reflect, TLDiagram.matching_verticalReflect,
      ← PlanarMatching.cast_reflect, PlanarMatching.reflect_reflect,
      ← PlanarMatching.cast_rotate_pow, PlanarMatching.pv_cast_eq, hm]
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
  · have hm := congrArg (PlanarMatching.pv ∘ TLDiagram.matching) hev
    simp only [Function.comp_apply, hLm, hRm, PlanarMatching.pv_cast_eq] at hm
    have hm' :
        (PlanarMatching.rotate (Y.as + X.as) ^ X.as) (ᘁf).diagram.matching =
          PlanarMatching.cast (Nat.add_comm X.as Y.as) f.diagram.matching :=
      PlanarMatching.eq_of_pv_eq (by rw [PlanarMatching.pv_cast_eq]; exact hm)
    have hrot := congrArg (PlanarMatching.rotate (Y.as + X.as) ^ Y.as) hm'
    rw [TLDiagram.matching_reflect, TLDiagram.matching_verticalReflect,
      ← PlanarMatching.cast_reflect, PlanarMatching.reflect_reflect]
    rwa [← Perm.mul_apply, ← pow_add, PlanarMatching.rotate_pow_self, Perm.one_apply] at hrot
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
