/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Dual.Basic
public import TauCeti.Geometry.Hodge.WeightOne.Homological

/-!
# The cohomological Hodge structure of a lattice with a complex structure

For a complex torus `V_ℝ / Λ` with complex structure `J`, the lattice `Λ = H₁` carries the
homological Hodge structure `TauCeti.AlmostComplexStructure.RiemannForm.homological` of weight
`-1`, with Weil operator `C = -J`. Its dual, carried by `H¹ = Hom(Λ, ℤ)`, is the **cohomological**
Hodge structure of weight one (`TauCeti.AlmostComplexStructure.RiemannForm.cohomological`). Its
filtration step `F¹` is the annihilator of the `-i`-eigenspace of `J`, that is the complex-linear
functionals on `(V_ℝ, J)`, and its Weil operator is the transpose of `J`.

The construction follows the Stanford VIGRE notes, *Complex theory of abelian varieties*,
Definitions 1.13–1.14.

## Main declarations

* `TauCeti.AlmostComplexStructure.RiemannForm.cohomological`: the weight-one structure on
  `Hom(Λ, ℤ)`, the dual of the homological structure.
* `TauCeti.AlmostComplexStructure.RiemannForm.cohomological_F`: its Hodge filtration.
* `TauCeti.AlmostComplexStructure.RiemannForm.cohomological_piece_one`,
  `TauCeti.AlmostComplexStructure.RiemannForm.cohomological_piece_zero`: `H^{1,0}` and `H^{0,1}`
  are the annihilators of the `-i`- and `+i`-eigenspaces of `J`.
* `TauCeti.AlmostComplexStructure.RiemannForm.cohomological_weilOperator`: its Weil operator is
  the transpose of `J`.
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

/-- The component `H^{1,0}` of the cohomological structure is the annihilator of the
`-i`-eigenspace of `J`: the functionals that are complex linear for `J`. -/
@[simp]
theorem cohomological_piece_one :
    (cohomological J hℂ).piece 1 =
      (Module.End.eigenspace (J.latticeComplexification hℂ) (-Complex.I)).dualAnnihilator := by
  rw [cohomological_def, Hodge.HodgeStructure.dual_piece, Hodge.HodgeStructureOn.dual_piece,
    Hodge.HodgeStructureOn.conjF_def]
  simp

/-- The component `H^{0,1}` of the cohomological structure is the annihilator of the
`+i`-eigenspace of `J`: the functionals that are conjugate linear for `J`. -/
@[simp]
theorem cohomological_piece_zero :
    (cohomological J hℂ).piece 0 =
      (Module.End.eigenspace (J.latticeComplexification hℂ) Complex.I).dualAnnihilator := by
  have hconj : (homological J hℂ).conjF 0 =
      Module.End.eigenspace (J.latticeComplexification hℂ) Complex.I := by
    rw [← homological_piece_neg_one, Hodge.HodgeStructureOn.piece_def, homological_F]
    simp
  rw [cohomological_def, Hodge.HodgeStructure.dual_piece, Hodge.HodgeStructureOn.dual_piece]
  simp [hconj]

/-- Every Hodge component of the cohomological structure other than `H^{1,0}` and `H^{0,1}`
vanishes. -/
theorem cohomological_piece_eq_bot {p : ℤ} (hp : p ≠ 0) (hp' : p ≠ 1) :
    (cohomological J hℂ).piece p = ⊥ := by
  by_cases hneg : p < 0
  · exact (cohomological J hℂ).piece_eq_bot_of_F_eq_top (a := 0) (by simp) hneg
  · exact (cohomological J hℂ).piece_eq_bot_of_F_eq_bot (b := 2) (by simp) (by omega)

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

end TauCeti.AlmostComplexStructure
