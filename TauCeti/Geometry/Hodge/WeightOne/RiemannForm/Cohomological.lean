/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Dual.Polarization
public import TauCeti.Geometry.Hodge.WeightOne.Cohomological
public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm.Homological

/-!
# The polarization of the cohomological Hodge structure by a Riemann form

For a complex torus `V_ℝ / Λ` with complex structure `J`, the cohomological Hodge structure
`TauCeti.AlmostComplexStructure.RiemannForm.cohomological` of weight one on `H¹ = Hom(Λ, ℤ)` is
the dual of the homological structure on `Λ = H₁`. The structure itself carries no form. A Riemann
form `E` for `J` gives the polarization `Q = -E` of the homological structure
(`IsRiemannForm.homologicalPolarization`). If a positive integer `a` kills the cokernel of
`E♭ : Λ → Hom(Λ, ℤ)`, the integral form `a Q^∨` on `H¹` (`LinearMap.BilinForm.scaledDualForm`)
polarizes the cohomological structure (`IsRiemannForm.isPolarization_cohomological`). When `E` is
principal one may take `a = 1`, and the dual form `Q^∨` itself polarizes the cohomological
structure (`IsRiemannForm.isPolarization_cohomological_one`).

The construction follows the Stanford VIGRE notes, *Complex theory of abelian varieties*,
Definitions 1.13–1.14 and Lemma 1.16.

## Main declarations

* `TauCeti.AlmostComplexStructure.IsRiemannForm.isPolarization_cohomological`: `a (-E)^∨`
  polarizes the cohomological structure, for `a > 0` killing the cokernel of `E♭`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.isPolarization_cohomological_one`: for a principal
  `E`, `(-E)^∨` polarizes it.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.cohomologicalPolarization`: the bundled
  polarization, with `cohomologicalPolarization_Qint` and `cohomologicalPolarization_Q`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

namespace IsRiemannForm

variable {J : AlmostComplexStructure (Hodge.Realification V)} {E : LinearMap.BilinForm ℤ V}
variable [Module.Free ℤ V] [Module.Finite ℤ V]

/-- **The scaled dual form polarizes the cohomological structure.** If `E` is a Riemann form for
`J` and the positive integer `a` kills the cokernel of `E♭ : Λ → Hom(Λ, ℤ)`, then `a Q^∨` with
`Q = -E` polarizes the weight-one structure on `H¹ = Hom(Λ, ℤ)`. -/
theorem isPolarization_cohomological (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ) {a : ℤ}
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range E) (ha0 : 0 < a) :
    Hodge.IsPolarization (Hodge.isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J hℂ)
      ((-E).scaledDualForm h.injective_neg a (E.smul_mem_range_neg a ha)) :=
  RiemannForm.cohomological_def J hℂ ▸
    (h.isPolarization_homological hℂ).scaledDualForm (E.smul_mem_range_neg a ha) ha0

/-- **The dual of a principal Riemann form polarizes the cohomological structure.** If `E` is a
principal Riemann form for `J`, the integral dual form `Q^∨` of `Q = -E` polarizes the weight-one
structure on `H¹ = Hom(Λ, ℤ)`. -/
theorem isPolarization_cohomological_one (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ)
    [E.IsPerfPair] :
    Hodge.IsPolarization (Hodge.isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J hℂ)
      ((-E).scaledDualForm h.injective_neg 1 E.one_smul_mem_range_neg_of_isPerfPair) :=
  h.isPolarization_cohomological hℂ E.one_smul_mem_range_of_isPerfPair one_pos

/-- The polarization `a Q^∨`, `Q = -E`, of the cohomological structure defined by a Riemann form
`E`, for a positive integer `a` killing the cokernel of `E♭` (`isPolarization_cohomological`). -/
noncomputable def cohomologicalPolarization (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ)
    {a : ℤ} (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range E) (ha0 : 0 < a) :
    Hodge.Polarization (Hodge.isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J hℂ) where
  Qint := (-E).scaledDualForm h.injective_neg a (E.smul_mem_range_neg a ha)
  isPolarization := h.isPolarization_cohomological hℂ ha ha0

/-- The integral form of the cohomological polarization of `E` is `a (-E)^∨`. -/
@[simp]
theorem cohomologicalPolarization_Qint (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ) {a : ℤ}
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range E) (ha0 : 0 < a) :
    (h.cohomologicalPolarization hℂ ha ha0).Qint =
      (-E).scaledDualForm h.injective_neg a (E.smul_mem_range_neg a ha) :=
  (rfl)

/-- The complex form of the cohomological polarization of `E` is the complexification of
`a (-E)^∨`. -/
@[simp]
theorem cohomologicalPolarization_Q (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ) {a : ℤ}
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range E) (ha0 : 0 < a) :
    (h.cohomologicalPolarization hℂ ha ha0).Q =
      IsBaseChange.bilinForm (Hodge.isBaseChange_dualLatticeMap hℂ)
        ((-E).scaledDualForm h.injective_neg a (E.smul_mem_range_neg a ha)) := by
  rw [Hodge.Polarization.Q_def, cohomologicalPolarization_Qint]

end IsRiemannForm

end TauCeti.AlmostComplexStructure
