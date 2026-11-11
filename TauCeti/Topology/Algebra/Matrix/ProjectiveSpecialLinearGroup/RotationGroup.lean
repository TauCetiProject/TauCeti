/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.SpecialLinear
public import TauCeti.RepresentationTheory.SU2.Adjoint
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# `PSU(2) ≅ SO(3)`, and `PSL(2, ℂ)` is homotopy equivalent to `SO(3)`

The double cover `SU(2) → SO(3)` (`TauCeti.SU2.toSO3`) and the map `SU(2) → PSL(2, ℂ)`
(`Matrix.specialUnitaryGroup.toPSL`) have the same kernel `{1, -1}`. So the projective special
unitary group `PSU(2)`, the image of `SU(2)` in `PSL(2, ℂ)`, is isomorphic as a topological group to
the rotation group `SO(3)` (`TauCeti.SU2.psuEquivSO3`): both are `SU(2) ⧸ {±1}`, by the
compact-to-Hausdorff identifications `Matrix.specialUnitaryGroup.quotientKerToPSLContinuousMulEquiv`
and `TauCeti.SU2.quotientKerToSO3`.

Combined with the polar deformation retraction of `PSL(2, ℂ)` onto `PSU(2)`
(`Matrix.ProjectiveSpecialLinearGroup.polarHomotopyEquiv`), this shows that the group `PSL(2, ℂ)`
of Möbius transformations of the Riemann sphere is homotopy equivalent to `SO(3)`
(`TauCeti.pslHomotopyEquivSO3`). The equivalence sends the class of `g ∈ SL(2, ℂ)` to the rotation
`toSO3 k` of the polar unitary factor `k` of `g`.

## Main definitions

* `TauCeti.SU2.psuEquivSO3`: the isomorphism of topological groups `PSU(2) ≃ₜ* SO(3)`.
* `TauCeti.pslHomotopyEquivSO3`: the homotopy equivalence `PSL(2, ℂ) ≃ₕ SO(3)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Sections 1.3 and 2.5.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapter 2.
-/

public section

noncomputable section

open Matrix Matrix.specialUnitaryGroup
open scoped ContinuousMap

namespace TauCeti

namespace SU2

/-- The maps `SU(2) → PSL(2, ℂ)` and `SU(2) → SO(3)` have the same kernel `{1, -1}`. -/
theorem ker_toPSL_eq_ker_toSO3 :
    (toPSL : SU2 →* ProjectiveSpecialLinearGroup (Fin 2) ℂ).ker = toSO3.ker := by
  ext g
  rw [mem_ker_toPSL_iff, MonoidHom.mem_ker, toSO3_eq_one_iff]

/-- **`PSU(2) ≅ SO(3)`**: the projective special unitary group, the image of `SU(2)` in
`PSL(2, ℂ)`, is isomorphic as a topological group to the rotation group `SO(3)`, through the
double cover `SU(2) → SO(3)`. -/
def psuEquivSO3 : (toPSL : SU2 →* ProjectiveSpecialLinearGroup (Fin 2) ℂ).range ≃ₜ*
    specialOrthogonalGroup (Fin 3) ℝ :=
  quotientKerToPSLContinuousMulEquiv.symm.trans <|
    ((ContinuousMulEquiv.refl SU2).quotientCongr _ _ (by
        rw [ker_toPSL_eq_ker_toSO3]
        exact Subgroup.map_id _)).trans
    quotientKerToSO3

/-- The isomorphism `PSU(2) ≃ₜ* SO(3)` sends the class of `g ∈ SU(2)` to the rotation
`toSO3 g`. -/
@[simp]
theorem psuEquivSO3_rangeRestrict (g : SU2) :
    psuEquivSO3 (toPSL.rangeRestrict g) = toSO3 g := by
  have h : quotientKerToPSLContinuousMulEquiv (g : SU2 ⧸ _) = toPSL.rangeRestrict g :=
    Subtype.ext (coe_quotientKerToPSLContinuousMulEquiv_mk g)
  simp [psuEquivSO3, ← h, quotientKerToSO3_mk]

end SU2

/-- **`PSL(2, ℂ)` is homotopy equivalent to `SO(3)`**: the group of Möbius transformations of the
Riemann sphere deformation retracts onto its rotation subgroup `PSU(2) ≅ SO(3)`. -/
def pslHomotopyEquivSO3 :
    ProjectiveSpecialLinearGroup (Fin 2) ℂ ≃ₕ specialOrthogonalGroup (Fin 3) ℝ :=
  (ProjectiveSpecialLinearGroup.polarHomotopyEquiv (Fin 2) ℂ).symm.trans
    SU2.psuEquivSO3.toHomeomorph.toHomotopyEquiv

/-- The homotopy equivalence `PSL(2, ℂ) ≃ₕ SO(3)` sends the class of `g ∈ SL(2, ℂ)` to the rotation
of the polar unitary factor of `g`. -/
@[simp]
theorem pslHomotopyEquivSO3_mk (g : SpecialLinearGroup (Fin 2) ℂ) :
    pslHomotopyEquivSO3 (g : ProjectiveSpecialLinearGroup (Fin 2) ℂ) =
      SU2.toSO3 (SpecialLinearGroup.polarRetraction (Fin 2) ℂ g) := by
  simp [pslHomotopyEquivSO3]

/-- The homotopy inverse of `PSL(2, ℂ) ≃ₕ SO(3)` is the inverse of `PSU(2) ≃ₜ* SO(3)` followed by
the inclusion `PSU(2) → PSL(2, ℂ)`. -/
@[simp]
theorem pslHomotopyEquivSO3_symm_apply (R : specialOrthogonalGroup (Fin 3) ℝ) :
    pslHomotopyEquivSO3.symm R =
      (SU2.psuEquivSO3.symm R : ProjectiveSpecialLinearGroup (Fin 2) ℂ) := by
  simp [pslHomotopyEquivSO3, ← Homeomorph.symm_toHomotopyEquiv,
    ContinuousMulEquiv.toHomeomorph_eq_coe]

/-- The homotopy inverse of `PSL(2, ℂ) ≃ₕ SO(3)` sends the rotation `toSO3 k` of `k ∈ SU(2)` to the
class of `k`. -/
theorem pslHomotopyEquivSO3_symm_toSO3 (k : SU2) :
    pslHomotopyEquivSO3.symm (SU2.toSO3 k) = toPSL k := by
  rw [pslHomotopyEquivSO3_symm_apply, ← SU2.psuEquivSO3_rangeRestrict,
    ContinuousMulEquiv.symm_apply_apply, MonoidHom.coe_rangeRestrict]

end TauCeti
