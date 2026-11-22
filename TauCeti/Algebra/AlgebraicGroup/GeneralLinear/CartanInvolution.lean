/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CartanInvolution
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.InverseTranspose
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Topology
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The Cartan involution of the real general linear group

Inverse transpose `θ(g) = (g⁻¹)ᵀ` is a Cartan involution of `GLₙ` over `ℝ`. A complex point `g`
satisfies `g = θ(conj g)` exactly when `g⁻¹ = (conj g)ᵀ`, that is when `g` is unitary, so the
twisted real form of `θ` is the compact unitary group `U(n)`. Its real fixed points are the
orthogonal group `O(n)`
(`TauCeti.GeneralLinear.toConv_comp_inverseTransposeCoordinateIso_eq_self_iff`), the maximal
compact subgroup of `GLₙ(ℝ)` that the symmetric space `GLₙ(ℝ)/O(n)` is built from.

The identity is not a Cartan involution of `GLₙ` for `n ≠ 0`: its twisted real form is `GLₙ`
itself, and `GLₙ(ℝ)` is not compact.

## Main results

* `TauCeti.GeneralLinear.mem_twistedRealPoints_inverseTransposeCoordinateIso_iff`: the twisted
  real points of inverse transpose are the unitary matrices.
* `TauCeti.GeneralLinear.isCartanInvolution_inverseTransposeCoordinateIso`: inverse transpose is a
  Cartan involution of `GLₙ` over `ℝ`.
* `TauCeti.GeneralLinear.not_isCartanInvolution_refl`: the identity of `GLₙ` over `ℝ` is not a
  Cartan involution when `n ≠ 0`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, notes, version of 16 September 2017, §1,
  Example 1.17(b), p. 15.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

variable {n : ℕ}

/-- **The twisted real points of inverse transpose are the unitary matrices.** A complex point of
`GLₙ` satisfies `g = θ(conj g)` for inverse transpose `θ` exactly when its matrix is unitary. -/
theorem mem_twistedRealPoints_inverseTransposeCoordinateIso_iff
    (p : coordinateHopfAlgebra ℝ n →ₐ[ℝ] ℂ) :
    p ∈ twistedRealPoints (inverseTransposeCoordinateIso ℝ n) ↔
      pointsMulEquiv n (toConv p) ∈ unitarySubgroup (GL (Fin n) ℂ) := by
  have hθ := pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso ℂ (toConv p)
  have hconj := pointToGeneralLinear_toConv_comp n (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (toConv p)
  rw [ofConv_toConv] at hθ hconj
  have hconj' : Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (pointsMulEquiv n (toConv p)) =
      pointsMulEquiv n (toConv ((Complex.conjAe : ℂ →ₐ[ℝ] ℂ).comp p)) := by
    rw [pointsMulEquiv_apply, pointsMulEquiv_apply]
    exact hconj.symm
  rw [mem_twistedRealPoints_iff_comp_eq, mem_unitarySubgroup_GL_iff_inverseTranspose_eq, ← hθ,
    hconj', (pointsMulEquiv n).injective.eq_iff, toConv_injective.eq_iff]

/-- **Inverse transpose is a Cartan involution of `GLₙ` over `ℝ`**: its twisted real form is the
compact unitary group `U(n)`. -/
theorem isCartanInvolution_inverseTransposeCoordinateIso :
    IsCartanInvolution (inverseTransposeCoordinateIso ℝ n) where
  hom_comp_self := inverseTransposeCoordinateIso_hom_comp_self
  isCompact := by
    have hcont : Continuous fun g : GL (Fin n) ℂ ↦
        (((pointsMulEquiv (R := ℝ) (A := ℂ) n).symm g).ofConv :
          coordinateHopfAlgebra ℝ n → ℂ) :=
      continuous_pi fun h ↦ (PointTopology.continuous_eval_ofConv h).comp <|
        (pointsContinuousMulEquiv (k := ℝ) (R := ℂ) n).symm.continuous.congr
          (pointsContinuousMulEquiv_symm_apply n)
    convert Matrix.GeneralLinearGroup.isCompact_unitarySubgroup.image hcont using 1
    ext f
    simp only [Set.mem_image, mem_twistedRealPoints_inverseTransposeCoordinateIso_iff]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, hp, by simp⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨((pointsMulEquiv n).symm g).ofConv, by simpa using hg, rfl⟩

/-- **The identity is not a Cartan involution of `GLₙ` over `ℝ` when `n ≠ 0`**: its twisted real
form is `GLₙ` itself, and `GLₙ(ℝ)` is not compact, since the scalar matrices `t • 1` have
unbounded entries. -/
theorem not_isCartanInvolution_refl (hn : n ≠ 0) :
    ¬ IsCartanInvolution (Iso.refl (coordinateHopfAlgebra ℝ n)) := by
  rw [isCartanInvolution_refl_iff]
  intro hcompact
  have i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let x := coordinateHopfAlgebraAlgEquiv ℝ n (coordinateRingMap ℝ n (MvPolynomial.X (i, i)))
  obtain ⟨b, hb⟩ := hcompact.bddAbove_image (f := fun f : coordinateHopfAlgebra ℝ n → ℝ ↦ f x)
    (continuous_apply x).continuousOn
  obtain ⟨m, hm⟩ := exists_nat_gt b
  let t : ℝˣ := Units.mk0 ((m : ℝ) + 1) (by positivity)
  have hle := hb ⟨_, ⟨(generalLinearToPoint (R := ℝ) n (diagGL fun _ ↦ t)).ofConv, rfl⟩, rfl⟩
  simp only [x, generalLinearToPoint_apply, diagGL_apply, ↓reduceIte, t, Units.val_mk0] at hle
  linarith

end TauCeti.GeneralLinear
