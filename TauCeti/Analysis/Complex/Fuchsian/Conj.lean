/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Descent
public import TauCeti.GroupTheory.GroupAction.ConjAct
public import TauCeti.Topology.Algebra.ConstMulAction
public import TauCeti.Topology.Homeomorph.Quotient

/-!
# Coarse quotients of conjugate Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)`, `g ∈ PSL(2, ℝ)`, and let `Γ' = g Γ g⁻¹`, written
`ConjAct.toConjAct g • Γ = Γ'`. The biholomorphism `z ↦ g • z` of the upper half-plane carries
`Γ`-orbits onto `Γ'`-orbits, so it descends to a homeomorphism
`Subgroup.quotientConjHomeomorph` of the coarse quotients `Γ \ ℍ ≃ₜ Γ' \ ℍ`, sending the orbit of
`z` to the orbit of `g • z`. For properly discontinuous (equivalently, discrete) groups it is
holomorphic, including at elliptic orbits, by holomorphic descent through the orbit projection
(`Subgroup.mdifferentiableAt_of_eventually_mdifferentiableAt_comp_quotientMk`). Its inverse is the
same construction for `g⁻¹` (`Subgroup.quotientConjHomeomorph_symm`), so it is holomorphic in both
directions. The construction is functorial: `g = 1` gives the identity
(`Subgroup.quotientConjHomeomorph_one`), and conjugating by `g` and then by `g'` is conjugating by
`g' * g` (`Subgroup.quotientConjHomeomorph_trans`).

The conjugate is passed as a subgroup `Γ'` together with the equation
`ConjAct.toConjAct g • Γ = Γ'`, so that the inverse is again of this form and an element of the
normalizer of `Γ` acts on `Γ \ ℍ` itself.

## Main declarations

* `Subgroup.quotientConjHomeomorph`: the homeomorphism `Γ \ ℍ ≃ₜ Γ' \ ℍ`, with
  `Subgroup.quotientConjHomeomorph_mk`, `Subgroup.quotientConjHomeomorph_symm`,
  `Subgroup.quotientConjHomeomorph_one` and `Subgroup.quotientConjHomeomorph_trans`.
* `Subgroup.mdifferentiable_quotientConjHomeomorph`: it is holomorphic.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.2.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups Pointwise

namespace Subgroup

variable {Γ Γ' : Subgroup PSL(2, ℝ)} {g : PSL(2, ℝ)}

/-- **The coarse quotients of conjugate groups are homeomorphic.** If `Γ' = g Γ g⁻¹`, the
translation `z ↦ g • z` of the upper half-plane descends to a homeomorphism `Γ \ ℍ ≃ₜ Γ' \ ℍ`
sending the orbit of `z` to the orbit of `g • z`. -/
def quotientConjHomeomorph (h : ConjAct.toConjAct g • Γ = Γ') :
    orbitRel.Quotient Γ ℍ ≃ₜ orbitRel.Quotient Γ' ℍ :=
  Homeomorph.Quotient.congr (Homeomorph.smul g) fun z w ↦
    (TauCeti.MulAction.orbitRel_smul_smul_iff_of_conjAct_smul_eq h z w).symm

@[simp]
theorem quotientConjHomeomorph_mk (h : ConjAct.toConjAct g • Γ = Γ') (z : ℍ) :
    quotientConjHomeomorph h (Quotient.mk _ z) = Quotient.mk _ (g • z) :=
  (rfl)

/-- The inverse of the homeomorphism of coarse quotients induced by `g` is the one induced by
`g⁻¹`. -/
@[simp]
theorem quotientConjHomeomorph_symm (h : ConjAct.toConjAct g • Γ = Γ') :
    (quotientConjHomeomorph h).symm =
      quotientConjHomeomorph (by rw [← h, map_inv, inv_smul_smul] :
        ConjAct.toConjAct g⁻¹ • Γ' = Γ) :=
  Homeomorph.ext fun p ↦ Quotient.inductionOn p fun _ ↦ (rfl)

/-- Conjugation by `1` induces the identity of the coarse quotient. -/
@[simp]
theorem quotientConjHomeomorph_one (h : ConjAct.toConjAct (1 : PSL(2, ℝ)) • Γ = Γ) :
    quotientConjHomeomorph h = Homeomorph.refl _ :=
  Homeomorph.ext fun p ↦ Quotient.inductionOn p fun z ↦ by
    rw [quotientConjHomeomorph_mk, one_smul, Homeomorph.refl_apply, id]

/-- Conjugating by `g` and then by `g'` induces the same homeomorphism of coarse quotients as
conjugating by `g' * g`. -/
@[simp]
theorem quotientConjHomeomorph_trans {Γ'' : Subgroup PSL(2, ℝ)} {g' : PSL(2, ℝ)}
    (h : ConjAct.toConjAct g • Γ = Γ') (h' : ConjAct.toConjAct g' • Γ' = Γ'') :
    (quotientConjHomeomorph h).trans (quotientConjHomeomorph h') =
      quotientConjHomeomorph (by rw [map_mul, mul_smul, h, h'] :
        ConjAct.toConjAct (g' * g) • Γ = Γ'') :=
  Homeomorph.ext fun p ↦ Quotient.inductionOn p fun z ↦ by
    rw [Homeomorph.trans_apply, quotientConjHomeomorph_mk, quotientConjHomeomorph_mk,
      quotientConjHomeomorph_mk, mul_smul]

/-- **The homeomorphism of coarse quotients induced by conjugation is holomorphic**, also at the
elliptic orbits: its pullback to the upper half-plane is the orbit projection of `Γ'` composed with
the biholomorphism `z ↦ g • z`. Proper discontinuity of `Γ'` follows from that of `Γ`. -/
theorem mdifferentiable_quotientConjHomeomorph [ProperlyDiscontinuousSMul Γ ℍ]
    (h : ConjAct.toConjAct g • Γ = Γ') :
    letI := TauCeti.properlyDiscontinuousSMul_of_conjAct_smul_eq (X := ℍ) h
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (quotientConjHomeomorph h) := fun p ↦ by
  have := TauCeti.properlyDiscontinuousSMul_of_conjAct_smul_eq (X := ℍ) h
  induction p using Quotient.inductionOn' with | h z => ?_
  refine mdifferentiableAt_of_eventually_mdifferentiableAt_comp_quotientMk
    (.of_forall fun w ↦ ?_)
  have hcomp : quotientConjHomeomorph h ∘ Quotient.mk _ = Quotient.mk (orbitRel Γ' ℍ) ∘ (g • ·) :=
    funext (quotientConjHomeomorph_mk h)
  rw [hcomp]
  exact (mdifferentiable_quotientMk Γ' _).comp w
    ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) (M := ℍ) g).mdifferentiable (by simp) w)

end Subgroup
