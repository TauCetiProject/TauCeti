/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Contraction

/-!
# Bidual evaluation twisted by a line

For a finite-dimensional vector space `A` and a one-dimensional vector space `D`,
`lineTwistedBidualEquiv` is the canonical identification `(A* ⊗ D)* ⊗ D ≃ A`.
It combines Mathlib's `TensorProduct.dualDistribEquiv` and `Module.evalEquiv` with
`contractLeftEquivOfFinrankEqOne`. In particular it involves no choice of a generator of `D`.
This is the fibrewise identification needed to recover differential forms from
density-twisted dual tests.

The evaluation equation says that pairing the image of `ψ ⊗ d` with `a*` gives
`ψ (a* ⊗ d)`. The inverse can be computed with any pair `δ, d` satisfying `δ d = 1`;
its independence of this pair and compatibility with changes of both vector-space
coordinates follow from the same evaluation equation. These are algebraic statements;
no smooth bundle or test-space topology is constructed here.
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable {K A D : Type*} [Field K] [AddCommGroup A] [Module K A]
  [FiniteDimensional K A] [AddCommGroup D] [Module K D]

/-- Canonical bidual evaluation with a one-dimensional twist, obtained by cancelling
`D* ⊗ D` and evaluating the remaining bidual. -/
def lineTwistedBidualEquiv (hD : finrank K D = 1) :
    (Dual K (Dual K A ⊗[K] D)) ⊗[K] D ≃ₗ[K] A :=
  haveI : FiniteDimensional K D := Module.finite_of_finrank_eq_succ hD
  (TensorProduct.congr (TensorProduct.dualDistribEquiv K (Dual K A) D).symm
      (LinearEquiv.refl K D)) ≪≫ₗ
    TensorProduct.assoc K (Dual K (Dual K A)) (Dual K D) D ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl K (Dual K (Dual K A)))
      (contractLeftEquivOfFinrankEqOne hD) ≪≫ₗ
    TensorProduct.rid K (Dual K (Dual K A)) ≪≫ₗ (Module.evalEquiv K A).symm

/-- On decomposable dual tensors, the line factors contract by evaluation. -/
@[simp]
theorem lineTwistedBidualEquiv_dualDistrib_tmul (hD : finrank K D = 1)
    (Φ : Dual K (Dual K A)) (δ : Dual K D) (d : D) :
    lineTwistedBidualEquiv (A := A) hD
      (TensorProduct.dualDistrib K (Dual K A) D (Φ ⊗ₜ δ) ⊗ₜ d) =
      δ d • (Module.evalEquiv K A).symm Φ := by
  have : FiniteDimensional K D := Module.finite_of_finrank_eq_succ hD
  simp [lineTwistedBidualEquiv, ← TensorProduct.toLinearMap_dualDistribEquiv]

/-- The coordinate-free evaluation formula characterizing the identification. -/
@[simp]
theorem apply_lineTwistedBidualEquiv_tmul (hD : finrank K D = 1)
    (ψ : Dual K (Dual K A ⊗[K] D)) (d : D) (a' : Dual K A) :
    a' (lineTwistedBidualEquiv hD (ψ ⊗ₜ d)) = ψ (a' ⊗ₜ d) := by
  have : FiniteDimensional K D := Module.finite_of_finrank_eq_succ hD
  obtain ⟨t, rfl⟩ := (TensorProduct.dualDistribEquiv K (Dual K A) D).surjective ψ
  induction t using TensorProduct.inductionOn with
  | tmul Φ δ =>
    simp only [← LinearEquiv.coe_toLinearMap, TensorProduct.toLinearMap_dualDistribEquiv]
    simp [TensorProduct.dualDistrib_apply, mul_comm]
  | add x y hx hy => simp_all [add_tmul]

/-- A normalized line generator gives an explicit inverse, without choosing one globally. -/
theorem lineTwistedBidualEquiv_symm_apply (hD : finrank K D = 1)
    (δ : Dual K D) (d : D) (hδd : δ d = 1) (a : A) :
    (lineTwistedBidualEquiv (A := A) hD).symm a =
      TensorProduct.dualDistrib K (Dual K A) D
        (Dual.eval K A a ⊗ₜ δ) ⊗ₜ d := by
  apply (lineTwistedBidualEquiv (K := K) (A := A) hD).injective
  simp [hδd, ← Module.evalEquiv_apply]

section Naturality

variable {B L : Type*} [AddCommGroup B] [Module K B] [FiniteDimensional K B]
  [AddCommGroup L] [Module K L]

/-- Bidual evaluation with a line twist is natural in the vector space and invariant under
changes of line coordinates. In particular, it commutes with changes of both frames. -/
theorem lineTwistedBidualEquiv_natural (hD : finrank K D = 1) (hL : finrank K L = 1)
    (f : A →ₗ[K] B) (g : D ≃ₗ[K] L) (t : Dual K (Dual K A ⊗[K] D) ⊗[K] D) :
    lineTwistedBidualEquiv hL
      (TensorProduct.map
        (TensorProduct.map f.dualMap g.symm.toLinearMap).dualMap g.toLinearMap t) =
      f (lineTwistedBidualEquiv hD t) := by
  induction t using TensorProduct.inductionOn with
  | tmul ψ d =>
    apply Module.eval_apply_injective K
    ext b'
    simp
    simpa only [LinearMap.dualMap_apply] using
      (apply_lineTwistedBidualEquiv_tmul hD ψ d (f.dualMap b')).symm
  | add x y hx hy => simp_all

/-- The inverse identification obeys the same coordinate-change equation. -/
theorem lineTwistedBidualEquiv_symm_natural (hD : finrank K D = 1) (hL : finrank K L = 1)
    (f : A →ₗ[K] B) (g : D ≃ₗ[K] L) (a : A) :
    (lineTwistedBidualEquiv hL).symm (f a) =
      TensorProduct.map
        (TensorProduct.map f.dualMap g.symm.toLinearMap).dualMap g.toLinearMap
        ((lineTwistedBidualEquiv hD).symm a) := by
  apply (lineTwistedBidualEquiv hL).injective
  rw [lineTwistedBidualEquiv_natural hD hL]
  simp

end Naturality

end TauCeti
