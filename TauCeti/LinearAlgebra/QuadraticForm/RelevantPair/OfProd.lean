/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Stabilizer

/-!
# Canonical product model and dimension witnesses for relevant pairs

This file constructs the canonical framed orthogonal relevant pair `ofProd` embedding `(W, Q_W)` as
the first summand of `Q_W ⊥ (H^j ⊥ ⟨c⟩)`, identifies its stabilizer embedding with the
first-factor inclusion into `SO(Q_W ⊥ (H^j ⊥ ⟨c⟩))`, and records non-vacuous dimension
witnesses.

## Main definitions

* `TauCeti.FramedOrthogonalRelevantPair.ofProd`: the canonical framed relevant pair on the
  orthogonal sum `Q_W ⊥ (H^j ⊥ ⟨c⟩)`.

## Main results

* `TauCeti.FramedOrthogonalRelevantPair.ofProd_stabilizerHom_apply`: `stabilizerHom` on `ofProd`
  is the product inclusion `(g, 1)`.
-/

public section

open Module QuadraticMap QuadraticForm TauCeti.QuadraticMap

namespace TauCeti

/-! ### Canonical product model and witnesses -/

namespace FramedOrthogonalRelevantPair

section OfProd

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W : Type*} [AddCommGroup W] [Module K W]
  (Q_W : QuadraticForm K W) (hW : Q_W.Nondegenerate) (j : ℕ) (c : Kˣ)

/-- The canonical framed orthogonal relevant pair embedding `(W, Q_W)` as the first summand of
`Q_W ⊥ (H^j ⊥ ⟨c⟩)`. -/
noncomputable def ofProd :
    FramedOrthogonalRelevantPair Q_W
      (Q_W.prod ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq))) j :=
  let Q₂ : QuadraticForm K ((Fin j → Fin 2 → K) × K) :=
    (hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq)
  let e : ((Q_W.prod Q₂).restrict
      (LinearMap.BilinForm.orthogonal (Q_W.prod Q₂).polarBilin
        (LinearMap.range (QuadraticMap.Isometry.inl Q_W Q₂).toLinearMap))).IsometryEquiv Q₂ :=
    QuadraticMap.orthogonalRangeInlEquiv Q_W Q₂ (nondegenerate_polar_iff.mpr hW)
  { embed := QuadraticMap.Isometry.inl Q_W Q₂
    nondegenerate_domain := hW
    lineCoeff := c
    complementEquiv := e }

/-- Evaluating `ofProd.embed` at `w` places `w` in the first summand `(w, (0, 0))`. -/
@[simp]
theorem ofProd_embed_apply (w : W) : (ofProd Q_W hW j c).embed w = (w, (0, 0)) :=
  (rfl)

/-- The distinguished line coefficient of `ofProd` is `c`. -/
@[simp]
theorem ofProd_lineCoeff : (ofProd Q_W hW j c).lineCoeff = c :=
  (rfl)

/-- The inverse framing of `ofProd` places a complement vector `y` in the second summand
`(0, y)`. -/
@[simp]
theorem ofProd_complementEquiv_symm_apply (y : (Fin j → Fin 2 → K) × K) :
    ((ofProd Q_W hW j c).complementEquiv.symm y : W × (Fin j → Fin 2 → K) × K) = (0, y) := by
  dsimp only [ofProd]
  exact QuadraticMap.coe_orthogonalRangeInlEquiv_symm_apply Q_W _ (nondegenerate_polar_iff.mpr hW) y

/-- The distinguished line vector of `ofProd` is `(0, (0, 1))`. -/
@[simp]
theorem ofProd_lineVector : (ofProd Q_W hW j c).lineVector = (0, (0, 1)) := by
  simp [lineVector_eq]

/-- The stabilizer embedding of `ofProd` at `g` is the product special orthogonal automorphism
`(g, 1)`. -/
@[simp]
theorem ofProd_stabilizerHom_apply [FiniteDimensional K W] (g : specialOrthogonalGroup Q_W) :
    (ofProd Q_W hW j c).stabilizerHom g =
      specialOrthogonalGroupProd Q_W ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq))
        (g, 1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rcases x with ⟨w, y⟩
  have hy : (0, y) ∈ (ofProd Q_W hW j c).orthogonal := by
    rw [OrthogonalRelevantPair.mem_orthogonal_iff]
    intro w'
    simp [QuadraticMap.polar]
  have hsplit : (w, y) = (ofProd Q_W hW j c).embed w + (0, y) := by simp
  rw [hsplit, map_add, map_add]
  dsimp only [FramedOrthogonalRelevantPair.stabilizerHom]
  rw [← (ofProd Q_W hW j c).toOrthogonalRelevantPair_embed,
    (ofProd Q_W hW j c).toOrthogonalRelevantPair.stabilizerHom_apply_embed,
    (ofProd Q_W hW j c).toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g hy]
  simp

end OfProd

/-! ### Non-vacuous dimension witnesses -/

-- Witness for a zero-dimensional smaller space `W = Fin 0 → K` and `j = 0`: trivial stabilizer
-- `SO(Q_W)` and ambient dimension `1`.
example (K : Type*) [Field K] [Invertible (2 : K)] (c : Kˣ) :
    Module.finrank K ((Fin 0 → K) × ((Fin 0 → Fin 2 → K) × K)) = 1 ∧
      Subsingleton (specialOrthogonalGroup (0 : QuadraticForm K (Fin 0 → K))) ∧
      Odd (Module.finrank K ((Fin 0 → K) × ((Fin 0 → Fin 2 → K) × K)) -
        Module.finrank K (Fin 0 → K)) := by
  refine ⟨by simp [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self], ?_, ?_⟩
  · refine ⟨fun g₁ g₂ ↦ Subtype.ext (LinearEquiv.ext fun x ↦ Subsingleton.elim _ _)⟩
  · exact (ofProd (0 : QuadraticForm K (Fin 0 → K))
      (by rw [nondegenerate_iff_radical_eq_bot]; exact Submodule.eq_bot_of_subsingleton)
      0 c).toOrthogonalRelevantPair.odd_codimension

-- Positive-dimension witness with `dim W = 2`, `j = 1`, and ambient dimension `d = 5`.
example (K : Type*) [Field K] [Invertible (2 : K)] (c : Kˣ) :
    let F := ofProd (hyperbolicPlane K) nondegenerate_hyperbolicPlane 1 c
    Module.finrank K ((Fin 2 → K) × ((Fin 1 → Fin 2 → K) × K)) = 5 ∧
      ((hyperbolicPlane K).prod ((hyperbolicSum K 1).prod ((c : K) • QuadraticMap.sq)))
        F.lineVector ≠ 0 ∧
      Odd (Module.finrank K ((Fin 2 → K) × ((Fin 1 → Fin 2 → K) × K)) -
        Module.finrank K (Fin 2 → K)) := by
  let F := ofProd (hyperbolicPlane K) nondegenerate_hyperbolicPlane 1 c
  refine ⟨by simp [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self],
    F.apply_lineVector_ne_zero, F.toOrthogonalRelevantPair.odd_codimension⟩

end FramedOrthogonalRelevantPair

end TauCeti
