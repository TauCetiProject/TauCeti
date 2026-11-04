/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Fibrewise linear automorphisms of a trivial bundle

A continuous family `A : B → (V →L[𝕜] V)ˣ` of invertible continuous linear maps of a normed space
`V` defines the homeomorphism `(x, v) ↦ (x, A x v)` of `B × V` (`TauCeti.prodUnitsHomeomorph`),
whose inverse applies `(A x)⁻¹` fibrewise. It changes the framing of the trivial bundle `B × V` by
`A`.
-/

public section

namespace TauCeti

variable {𝕜 V B : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace B]

/-- The homeomorphism `(x, v) ↦ (x, A x v)` of `B × V` defined by a continuous family `A` of
invertible continuous linear maps of `V`; it changes the framing of a trivial bundle by `A`. -/
noncomputable def prodUnitsHomeomorph (A : B → (V →L[𝕜] V)ˣ) (hA : Continuous A) :
    B × V ≃ₜ B × V where
  toFun p := (p.1, (A p.1 : V →L[𝕜] V) p.2)
  invFun p := (p.1, (↑(A p.1)⁻¹ : V →L[𝕜] V) p.2)
  left_inv p := by simp [← mul_apply_eq_comp]
  right_inv p := by simp [← mul_apply_eq_comp]
  continuous_toFun := continuous_fst.prodMk
    ((Units.continuous_val.comp (hA.comp continuous_fst)).clm_apply continuous_snd)
  continuous_invFun := continuous_fst.prodMk
    ((Units.continuous_coe_inv.comp (hA.comp continuous_fst)).clm_apply continuous_snd)

@[simp]
theorem prodUnitsHomeomorph_apply (A : B → (V →L[𝕜] V)ˣ) (hA : Continuous A) (p : B × V) :
    prodUnitsHomeomorph A hA p = (p.1, (A p.1 : V →L[𝕜] V) p.2) :=
  (rfl)

@[simp]
theorem prodUnitsHomeomorph_symm_apply (A : B → (V →L[𝕜] V)ˣ) (hA : Continuous A) (p : B × V) :
    (prodUnitsHomeomorph A hA).symm p = (p.1, (↑(A p.1)⁻¹ : V →L[𝕜] V) p.2) :=
  (rfl)

end TauCeti
