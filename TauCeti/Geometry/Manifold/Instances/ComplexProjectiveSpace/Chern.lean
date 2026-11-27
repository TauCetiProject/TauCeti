/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Clutching
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Symplectic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Generator

/-!
# The first Chern number of complex projective space

A fiberwise nondegenerate two-form `σ` on a manifold has a first Chern number
`c₁ : π₂(M, x) → ℤ` (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom`), the clutching number of
the tangent bundle made complex by any almost complex structure tamed by `σ`. This file evaluates it
for the Fubini–Study form `ω_FS` of complex projective space `CPⁿ`.

Since `ω_FS` is compatible with the standard complex structure of `CPⁿ`, multiplication by `i` on
its tangent spaces (`TauCeti.ComplexProjectiveSpace.compatible_fubiniStudyForm`), its first Chern
number is the clutching number homomorphism of the holomorphic tangent bundle of `CPⁿ`
(`TauCeti.ComplexProjectiveSpace.firstChernHom_fubiniStudyForm_eq_clutchingNumberHom_tangentSpace`).
On the class of the coordinate line `TauCeti.ComplexProjectiveSpace.lineSquare n` of `CPⁿ⁺¹` that
clutching number is `n + 2`
(`TauCeti.ComplexProjectiveSpace.clutchingNumberHom_tangentSpace_lineSquare`), so the first Chern
number of `ω_FS` on a line of `CPᵐ` is `m + 1`
(`TauCeti.ComplexProjectiveSpace.firstChernHom_fubiniStudyForm_apply_mk_lineSquare`). This is the
Chern number of the line class with which the grading of capped Hamiltonian Floer theory on
`(CPᵐ, ω_FS)` changes under recapping, and which gives the quantum variable of the line class its
degree `2 (m + 1)`. For `m = 1` it is the value `2` of
`OnePoint.firstChernHom_fubiniStudyForm_apply_mk_riemannSphereSquare` on the Riemann sphere.

## Main results

* `TauCeti.ComplexProjectiveSpace.firstChernHom_fubiniStudyForm_eq_clutchingNumberHom_tangentSpace`:
  the first Chern number of the Fubini–Study form is the clutching number homomorphism of the
  holomorphic tangent bundle.
* `TauCeti.ComplexProjectiveSpace.firstChernHom_fubiniStudyForm_apply_mk_lineSquare`: it takes the
  value `n + 2` on the class of a line of `CPⁿ⁺¹`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the first Chern class of the tangent bundle of complex projective space).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number by clutching).
-/

public section

open scoped Manifold

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-- **The first Chern number of the Fubini–Study form** of `CPⁿ` at any base point is the clutching
number homomorphism of the holomorphic tangent bundle of `CPⁿ`, since the Fubini–Study form tames
the standard complex structure. -/
theorem firstChernHom_fubiniStudyForm_eq_clutchingNumberHom_tangentSpace
    (x : ComplexProjectiveSpace n) :
    (isSymplectic_fubiniStudyForm (n := n)).isNondegenerate.firstChernHom x =
      clutchingNumberHom (Fin n → ℂ) (TangentSpace 𝓘(ℂ, Fin n → ℂ)) x :=
  isSymplectic_fubiniStudyForm.isNondegenerate.firstChernHom_eq_clutchingNumberHom_tangentSpace
    compatible_fubiniStudyForm.tames x

/-- **The first Chern number of `CPᵐ` on a line is `m + 1`.** The first Chern number of the
Fubini–Study form of `CPⁿ⁺¹` takes the value `n + 2` on the class of the coordinate line
`lineSquare n`. -/
theorem firstChernHom_fubiniStudyForm_apply_mk_lineSquare :
    (isSymplectic_fubiniStudyForm (n := n + 1)).isNondegenerate.firstChernHom (affineParam 1 0)
      (Additive.ofMul (Quotient.mk _ (lineSquare n))) = n + 2 := by
  rw [firstChernHom_fubiniStudyForm_eq_clutchingNumberHom_tangentSpace,
    clutchingNumberHom_tangentSpace_lineSquare]

/-- **The generator of `π₂(CPⁿ⁺¹)` has first Chern number `n + 2`** for the Fubini–Study form:
it is the class of the coordinate line
(`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_symm_ofAdd_one`). -/
@[simp]
theorem firstChernHom_fubiniStudyForm_apply_pi2MulEquivInt_symm_ofAdd_one :
    (isSymplectic_fubiniStudyForm (n := n + 1)).isNondegenerate.firstChernHom
      (mk (n + 1) (affineUnitVector 1 0))
      (Additive.ofMul ((pi2MulEquivInt (affineUnitVector 1 0) n.add_one_ne_zero).symm
        (Multiplicative.ofAdd 1))) = n + 2 := by
  rw [pi2MulEquivInt_symm_ofAdd_one]
  exact (apply_lineClass n fun y a ↦ isSymplectic_fubiniStudyForm.isNondegenerate.firstChernHom y
    (Additive.ofMul a)).trans firstChernHom_fubiniStudyForm_apply_mk_lineSquare

end TauCeti.ComplexProjectiveSpace
