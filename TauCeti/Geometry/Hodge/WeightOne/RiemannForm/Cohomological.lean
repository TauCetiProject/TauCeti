/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Dual.Polarization
public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm.Homological

/-!
# The cohomological Hodge structure of a complex torus and its polarization

For a complex torus `V_ℝ / Λ` with complex structure `J`, the lattice `Λ = H₁` carries the
homological Hodge structure `TauCeti.AlmostComplexStructure.RiemannForm.homological` of weight
`-1`, with Weil operator `C = -J`. Its dual, carried by `H¹ = Hom(Λ, ℤ)`, is the **cohomological**
Hodge structure of weight one (`TauCeti.AlmostComplexStructure.RiemannForm.cohomological`). Its
filtration step `F¹` is the annihilator of the `-i`-eigenspace of `J`, that is the complex-linear
functionals on `(V_ℝ, J)`, and its Weil operator is the transpose of `J`.

The structure itself carries no form. A Riemann form `E` for `J` gives the polarization `Q = -E`
of the homological structure (`IsRiemannForm.homologicalPolarization`). If a positive integer `a`
kills the cokernel of `E♭ : Λ → Hom(Λ, ℤ)`, the integral form `a Q^∨` on `H¹`
(`LinearMap.BilinForm.scaledDualForm`) polarizes the cohomological structure
(`IsRiemannForm.isPolarization_cohomological`). When `E` is principal one may take `a = 1`, and the
dual form `Q^∨` itself is a principal polarization
(`IsRiemannForm.isPolarization_cohomological_one`).

The construction follows the Stanford VIGRE notes, *Complex theory of abelian varieties*,
Definitions 1.13–1.14 and Lemma 1.16.

## Main declarations

* `TauCeti.AlmostComplexStructure.RiemannForm.cohomological`: the weight-one structure on
  `Hom(Λ, ℤ)`, the dual of the homological structure.
* `TauCeti.AlmostComplexStructure.RiemannForm.cohomological_F`: its Hodge filtration.
* `TauCeti.AlmostComplexStructure.RiemannForm.cohomological_weilOperator`: its Weil operator is
  the transpose of `J`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.isPolarization_cohomological`: `a (-E)^∨`
  polarizes it, for `a > 0` killing the cokernel of `E♭`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.isPolarization_cohomological_one`: for a principal
  `E`, `(-E)^∨` polarizes it.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

namespace RiemannForm

variable (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)
variable [Module.Free ℤ V] [Module.Finite ℤ V]

/-- The **cohomological Hodge structure** of a lattice with a complex structure `J` on its
realification: the weight-one structure on `H¹ = Hom(Λ, ℤ)` dual to the homological structure on
`Λ = H₁`. Its step `F¹` is the annihilator of the `-i`-eigenspace of `J` (`cohomological_F`) and
its Weil operator is the transpose of `J` (`cohomological_weilOperator`). -/
noncomputable def cohomological :
    Hodge.HodgeStructure (Hodge.isBaseChange_dualLatticeMap hℂ) 1 :=
  (homological J hℂ).dual

/-- The cohomological structure is the dual of the homological structure. -/
theorem cohomological_def : cohomological J hℂ = (homological J hℂ).dual :=
  (rfl)

/-- The Hodge filtration of the cohomological structure is top in degrees at most zero, the
annihilator of the `-i`-eigenspace of `J` in degree one, and bottom above. -/
@[simp]
theorem cohomological_F (p : ℤ) :
    (cohomological J hℂ).F p = if p ≤ 0 then ⊤ else if p = 1 then
      (Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I)).dualAnnihilator
      else ⊥ := by
  rw [cohomological_def, Hodge.HodgeStructure.dual_F, Hodge.HodgeStructureOn.dual_F,
    homological_F]
  split_ifs <;> first
    | (exfalso; omega)
    | rfl
    | simp

/-- The step `F¹` of the cohomological structure is the annihilator of the `-i`-eigenspace
of `J`: the functionals that are complex linear for `J`. -/
theorem cohomological_F_one :
    (cohomological J hℂ).F 1 =
      (Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I)).dualAnnihilator := by
  simp

/-- **The Weil operator of the cohomological structure is the transpose of `J`.** It is the
transpose of the inverse of the homological Weil operator `C = -J`, and `(-J)⁻¹ = J`. -/
@[simp]
theorem cohomological_weilOperator :
    (cohomological J hℂ).weilOperator = (J.latticeComplexification hℂ).dualMap := by
  rw [cohomological_def, Hodge.HodgeStructure.dual_weilOperator]
  congr 1
  ext x
  simp

end RiemannForm

namespace IsRiemannForm

variable {J : AlmostComplexStructure (Hodge.Realification V)} {E : LinearMap.BilinForm ℤ V}

/-- The map `x ↦ -E(x, ·)` is injective for a Riemann form `E`, on a flat integral module. -/
theorem injective_neg [Module.Flat ℤ V] (h : J.IsRiemannForm E) : Function.Injective (-E) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_neg]
  exact LinearMap.separatingLeft_iff_ker_eq_bot.mp h.nondegenerate.1

/-- For a principal Riemann form `E`, `1` kills the cokernel of `(-E)♭`. -/
theorem one_smul_mem_range_neg [E.IsPerfPair] (η : Module.Dual ℤ V) :
    (1 : ℤ) • η ∈ LinearMap.range (-E) := by
  simpa [LinearMap.range_neg] using E.one_smul_mem_range_of_isPerfPair η

variable [Module.Free ℤ V] [Module.Finite ℤ V]

/-- **The scaled dual form polarizes the cohomological structure.** If `E` is a Riemann form for
`J` and the positive integer `a` kills the cokernel of `E♭ : Λ → Hom(Λ, ℤ)`, then `a Q^∨` with
`Q = -E` polarizes the weight-one structure on `H¹ = Hom(Λ, ℤ)`. -/
theorem isPolarization_cohomological (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ) {a : ℤ}
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range E) (ha0 : 0 < a) :
    Hodge.IsPolarization (Hodge.isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J hℂ)
      ((-E).scaledDualForm h.injective_neg a (by simpa [LinearMap.range_neg] using ha)) :=
  (h.isPolarization_homological hℂ).scaledDualForm _ ha0

/-- **The dual of a principal Riemann form polarizes the cohomological structure.** If `E` is a
principal Riemann form for `J`, the integral dual form `Q^∨` of `Q = -E` polarizes the weight-one
structure on `H¹ = Hom(Λ, ℤ)`. -/
theorem isPolarization_cohomological_one (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ)
    [E.IsPerfPair] :
    Hodge.IsPolarization (Hodge.isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J hℂ)
      ((-E).scaledDualForm h.injective_neg 1 one_smul_mem_range_neg) :=
  h.isPolarization_cohomological hℂ (fun η ↦ E.one_smul_mem_range_of_isPerfPair η) one_pos

/-- The polarization `a Q^∨`, `Q = -E`, of the cohomological structure defined by a Riemann form
`E`, for a positive integer `a` killing the cokernel of `E♭` (`isPolarization_cohomological`). -/
noncomputable def cohomologicalPolarization (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ)
    {a : ℤ} (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range E) (ha0 : 0 < a) :
    Hodge.Polarization (Hodge.isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J hℂ) where
  Qint := (-E).scaledDualForm h.injective_neg a (by simpa [LinearMap.range_neg] using ha)
  isPolarization := h.isPolarization_cohomological hℂ ha ha0

/-- The integral form of the cohomological polarization of `E` is `a (-E)^∨`. -/
@[simp]
theorem cohomologicalPolarization_Qint (h : J.IsRiemannForm E) (hℂ : IsBaseChange ℂ ιℂ) {a : ℤ}
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range E) (ha0 : 0 < a) :
    (h.cohomologicalPolarization hℂ ha ha0).Qint =
      (-E).scaledDualForm h.injective_neg a (by simpa [LinearMap.range_neg] using ha) :=
  (rfl)

end IsRiemannForm

end TauCeti.AlmostComplexStructure
