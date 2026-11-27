/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import TauCeti.Data.Finsupp.Pointwise
public import TauCeti.RingTheory.Idempotented.Center

/-!
# Checks for bimodule endomorphisms acting on nondegenerate modules

* A coefficient scalar `a ∈ A` is a bimodule endomorphism `x ↦ a • x` of `H`, and acts on a
  nondegenerate module by `a`.
* Multiplication by a noncentral element is not a bimodule endomorphism: left multiplication by
  `E₀₁` on `M₂(ℚ)` does not commute with left multiplication by `E₁₀`.
* For `H = ⊕_{n ∈ ℕ} ℚ`, which has no identity element, the identity bimodule endomorphism (the
  all-one multiplier) acts as the identity of the centre.
-/

public section

open CategoryTheory TauCeti TauCeti.NondegMod

/-- A coefficient scalar acts on a nondegenerate module through the centre by scalar
multiplication. -/
example (A H : Type) [CommRing A] [NonUnitalRing H] [Module A H] [IsScalarTower A H H]
    [SMulCommClass A H H] [IsIdempotented H] (a : A) (M : NondegMod.{0} A H) (m : M.obj) :
    ((centroidToCatCenter.{0} A H (a • 1)).app M).hom.hom m =
      (Unitization.inl a : Unitization A H) • m := by
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 ((nondegenerateModuleProperty_iff _).1 M.property) m
  rw [centroidToCatCenter_app_apply _ M he, CentroidHom.smul_apply, CentroidHom.one_apply,
    inl_smul_eq_inr_smul he]

/-- Left multiplication by the noncentral `E₀₁` on `M₂(ℚ)` is not a bimodule endomorphism. -/
example : ¬∃ φ : CentroidHom (Matrix (Fin 2) (Fin 2) ℚ),
    ∀ x, φ x = Matrix.single 0 1 1 * x := by
  rintro ⟨φ, hφ⟩
  have h := map_mul_left φ (Matrix.single 1 0 1) 1
  rw [hφ, hφ, mul_one, mul_one] at h
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.single_apply] at this

/-- On nondegenerate modules over `⊕_n ℚ`, the identity bimodule endomorphism acts as `1`. -/
example (M : NondegMod.{0} ℚ (ℕ →₀ ℚ)) :
    (centroidToCatCenter.{0} ℚ (ℕ →₀ ℚ) 1).app M = 𝟙 M := by
  rw [map_one, CatCenter.app_one]
