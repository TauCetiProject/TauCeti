/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC

/-!
# The half-spin representations of `Spin(4)` and `Spinᶜ(4)`

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and let `W` be
a complex vector space with a real algebra map
`ρ : CliffordAlgebra Q → End_ℂ W`. The chirality element `Γ` (`CliffordAlgebra.chirality`)
commutes with every even Clifford element, so the even subalgebra, and with it the Spin group
`spinGroup Q`, acts on each eigenspace `W^ε` of `Γ`; for `ε = ±1` these are the half-spinors
`W^±`, and `ε = 1` is `CliffordAlgebra.positiveHalfSpinors o ρ`. Twisting by a unit complex
scalar gives the action `(s, z) ↦ z ρ(s)` of `Spin(4) × U(1)`. As `(-1, -1)` acts trivially, it
descends to the half-spin representations `ρ^±([s, z]) = z ρ^±(s)` of
`Spinᶜ(4) = (Spin(4) × U(1)) / {±(1, 1)}` (`CliffordAlgebra.spinCGroup`), the structure group of
the spinor bundles of a `Spinᶜ` four-manifold.

When `W^ε` has complex dimension two, `ρ(x* x) = det(ρ x)` on `W^ε` for every even `x`
(`CliffordAlgebra.evenHalfSpinAction_reverseEven_mul_self`), so every Spin element acts with
determinant one, and `[s, z]` acts with determinant `z²`, the determinant character of
`Spinᶜ(4)` (`CliffordAlgebra.spinCGroup.det`): the determinant line of `W^±` is the square of the
twisting circle. If `W` is moreover a Hermitian Clifford module, the generators
acting skew-adjointly, both representations are unitary.

Clifford multiplication `c(v) : W^ε → W^{-ε}` (`CliffordAlgebra.halfSpinCliffordMul`) is
equivariant: `ρ^{-ε}(s) c(v) = c(s v) ρ^ε(s)`, where `s v` is the rotation action of `s` on `V`
(`CliffordAlgebra.spinVectorAction`). The circle factor of `[s, z]` scales both sides alike and
does not act on vectors, so `Spinᶜ(4)` acts on vectors through its rotation
`CliffordAlgebra.spinCGroup.toSpecialOrthogonal`. This is the equivariance that lets Clifford
multiplication by cotangent vectors be defined on the associated spinor bundles `W^±` of a `Spinᶜ`
structure.

## Main definitions

* `CliffordAlgebra.halfSpinRep o ρ ε`: the representation of `spinGroup Q` on the
  `ε`-eigenspace of `Γ`, restricting `CliffordAlgebra.evenHalfSpinAction o ρ ε`.
* `CliffordAlgebra.spinCHalfSpinRep o ρ ε`: the representation `(s, z) ↦ z ρ(s)` of
  `spinGroup Q × Circle` on that eigenspace.
* `CliffordAlgebra.spinCGroupHalfSpinRep o ρ ε hQ₀`: its descent `[s, z] ↦ z ρ(s)` to the
  quotient `CliffordAlgebra.spinCGroup Q hQ₀ = Spinᶜ(4)`.

## Main results

* `CliffordAlgebra.det_halfSpinRep`: Spin elements act on a two-dimensional `W^ε` with
  determinant one.
* `CliffordAlgebra.inner_halfSpinRep_apply_halfSpinRep_apply`: on a Hermitian Clifford module the
  Spin action is unitary.
* `CliffordAlgebra.spinCHalfSpinRep_negOne_neg_one`: `(-1, -1)` acts trivially, so the twisted
  action descends to `Spinᶜ(4)`.
* `CliffordAlgebra.halfSpinRep_comp_halfSpinCliffordMul`,
  `CliffordAlgebra.spinCHalfSpinRep_comp_halfSpinCliffordMul`: Clifford multiplication
  `W^ε → W^{-ε}` intertwines the half-spin representations of `Spin(4)` and of `Spinᶜ(4)`, with
  `Spin(4)` acting on vectors by rotation.
* `CliffordAlgebra.det_spinCHalfSpinRep`: `(s, z)` acts with determinant `z²`, and
  `CliffordAlgebra.inner_spinCHalfSpinRep_apply_spinCHalfSpinRep_apply`: the twisted action is
  unitary.
* `CliffordAlgebra.spinCGroupHalfSpinRep_comp_halfSpinCliffordMul`,
  `CliffordAlgebra.det_spinCGroupHalfSpinRep` and
  `CliffordAlgebra.inner_spinCGroupHalfSpinRep_apply_spinCGroupHalfSpinRep_apply`: the descended
  representations of `Spinᶜ(4)` are Clifford equivariant over its rotation, have determinant the
  determinant character, and are unitary.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))

section Module

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (ε : ℂ)

/-- **The half-spin representation of the Spin group** on the `ε`-eigenspace of `Γ`, the
restriction of the Clifford action along `spinGroup Q ⊆ even Q`. -/
def halfSpinRep : Representation ℂ (spinGroup Q) (eigenspace (ρ (chirality Q o)) ε) :=
  (evenHalfSpinAction o ρ ε).toMonoidHom.comp (spinGroupToEven Q)

/-- `halfSpinRep` is `evenHalfSpinAction` at the Spin element, viewed as an even element. -/
theorem halfSpinRep_apply (s : spinGroup Q) :
    halfSpinRep o ρ ε s = evenHalfSpinAction o ρ ε (spinGroupToEven Q s) :=
  (rfl)

/-- `halfSpinRep` is the restriction of the Clifford action. -/
@[simp]
theorem coe_halfSpinRep_apply (s : spinGroup Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinRep o ρ ε s ψ : W) = ρ s ψ := by
  simp [halfSpinRep]

/-- **The half-spin representation of `Spinᶜ(4)`**, before passing to the quotient by
`{±(1, 1)}`: `(s, z)` acts on the `ε`-eigenspace of `Γ` by `z ρ(s)`. It is trivial on
`(-1, -1)` (`CliffordAlgebra.spinCHalfSpinRep_negOne_neg_one`), and descends to
`CliffordAlgebra.spinCGroupHalfSpinRep`. -/
def spinCHalfSpinRep :
    Representation ℂ (spinGroup Q × Circle) (eigenspace (ρ (chirality Q o)) ε) where
  toFun p := (p.2 : ℂ) • halfSpinRep o ρ ε p.1
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Circle.coe_mul, mul_smul_comm, smul_mul_assoc,
      smul_smul, mul_comm]

/-- `(s, z)` acts by `z ρ(s)`. -/
@[simp]
theorem spinCHalfSpinRep_apply (s : spinGroup Q) (z : Circle) :
    spinCHalfSpinRep o ρ ε (s, z) = (z : ℂ) • halfSpinRep o ρ ε s :=
  (rfl)

/-- **The twisted action descends to `Spinᶜ(4)`**: the central element `(-1, -1)` of
`spinGroup Q × Circle` acts trivially. -/
theorem spinCHalfSpinRep_negOne_neg_one (hQ₀ : Q ≠ 0) :
    spinCHalfSpinRep o ρ ε (spinGroup.negOne Q hQ₀, -1) = 1 := by
  ext ψ
  simp

/-- **Clifford equivariance of the half-spin representations**: Clifford multiplication
`W^ε → W^{-ε}` intertwines the half-spin representations when `Spin(4)` acts on vectors by its
rotation action, `ρ^{-ε}(s) c(v) = c(s v) ρ^ε(s)`. -/
theorem halfSpinRep_comp_halfSpinCliffordMul (s : spinGroup Q) (v : V) :
    halfSpinRep o ρ (-ε) s ∘ₗ halfSpinCliffordMul o ρ ε v =
      halfSpinCliffordMul o ρ ε (spinVectorAction Q s v) ∘ₗ halfSpinRep o ρ ε s := by
  ext ψ
  simp only [LinearMap.comp_apply, coe_halfSpinRep_apply, coe_halfSpinCliffordMul_apply_apply,
    ← Module.End.mul_apply, ← map_mul, ι_spinVectorAction_apply_mul]

/-- **Clifford equivariance of the `Spinᶜ(4)` half-spin representations**: `(s, z)` acts on
vectors through the rotation action of `s` alone, and Clifford multiplication `W^ε → W^{-ε}`
intertwines the twisted half-spin representations, `ρ^{-ε}(s, z) c(v) = c(s v) ρ^ε(s, z)`. -/
theorem spinCHalfSpinRep_comp_halfSpinCliffordMul (p : spinGroup Q × Circle) (v : V) :
    spinCHalfSpinRep o ρ (-ε) p ∘ₗ halfSpinCliffordMul o ρ ε v =
      halfSpinCliffordMul o ρ ε (spinVectorAction Q p.1 v) ∘ₗ spinCHalfSpinRep o ρ ε p := by
  obtain ⟨s, z⟩ := p
  rw [spinCHalfSpinRep_apply, spinCHalfSpinRep_apply, LinearMap.smul_comp, LinearMap.comp_smul,
    halfSpinRep_comp_halfSpinCliffordMul]

variable (hQ₀ : Q ≠ 0)

/-- **The half-spin representation of `Spinᶜ(4)`** on the `ε`-eigenspace of `Γ`:
`[s, z]` acts by `z ρ(s)`. It is the descent of `CliffordAlgebra.spinCHalfSpinRep` to the quotient
`CliffordAlgebra.spinCGroup Q hQ₀` of `spinGroup Q × Circle` by `{1, (-1, -1)}`. -/
def spinCGroupHalfSpinRep :
    Representation ℂ (spinCGroup Q hQ₀) (eigenspace (ρ (chirality Q o)) ε) :=
  spinCGroup.lift Q hQ₀ (spinCHalfSpinRep o ρ ε) (spinCHalfSpinRep_negOne_neg_one o ρ ε hQ₀)

/-- `[s, z]` acts by `z ρ(s)`. -/
@[simp]
theorem spinCGroupHalfSpinRep_mk (p : spinGroup Q × Circle) :
    spinCGroupHalfSpinRep o ρ ε hQ₀ (spinCGroup.mk Q hQ₀ p) = spinCHalfSpinRep o ρ ε p :=
  spinCGroup.lift_mk ..

/-- On `Spin(4) ⊆ Spinᶜ(4)` the representation restricts to the half-spin representation of the
Spin group. -/
@[simp]
theorem spinCGroupHalfSpinRep_ofSpin (s : spinGroup Q) :
    spinCGroupHalfSpinRep o ρ ε hQ₀ (spinCGroup.ofSpin Q hQ₀ s) = halfSpinRep o ρ ε s := by
  simp [spinCGroup.ofSpin_apply]

/-- The circle `U(1) ⊆ Spinᶜ(4)` acts by scalars. -/
@[simp]
theorem spinCGroupHalfSpinRep_ofCircle (z : Circle) :
    spinCGroupHalfSpinRep o ρ ε hQ₀ (spinCGroup.ofCircle Q hQ₀ z) = (z : ℂ) • 1 := by
  simp [spinCGroup.ofCircle_apply]

/-- **Clifford equivariance of the half-spin representations of `Spinᶜ(4)`**: Clifford
multiplication `W^ε → W^{-ε}` intertwines them when `Spinᶜ(4)` acts on vectors through its rotation
`[s, z] ↦ π(s)`, `ρ^{-ε}(x) c(v) = c(π(x) v) ρ^ε(x)`. -/
theorem spinCGroupHalfSpinRep_comp_halfSpinCliffordMul (x : spinCGroup Q hQ₀) (v : V) :
    spinCGroupHalfSpinRep o ρ (-ε) hQ₀ x ∘ₗ halfSpinCliffordMul o ρ ε v =
      halfSpinCliffordMul o ρ ε ((spinCGroup.toSpecialOrthogonal Q hQ₀ x : V ≃ₗ[ℝ] V) v) ∘ₗ
        spinCGroupHalfSpinRep o ρ ε hQ₀ x := by
  obtain ⟨p, rfl⟩ := spinCGroup.mk_surjective Q hQ₀ x
  rw [spinCGroupHalfSpinRep_mk, spinCGroupHalfSpinRep_mk,
    spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply,
    spinCHalfSpinRep_comp_halfSpinCliffordMul]

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **Spin elements act with determinant one** on an eigenspace of `Γ` of complex dimension
two: the half-spin representations of `Spin(4)` take values in the special linear group. -/
@[simp]
theorem det_halfSpinRep (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : spinGroup Q) : LinearMap.det (halfSpinRep o ρ ε s) = 1 := by
  have : Nontrivial (eigenspace (ρ (chirality Q o)) ε) :=
    Module.nontrivial_of_finrank_eq_succ h₂
  -- `s* s = 1` for `s ∈ Spin`, so `1 = det (ρ s) • 1` on `W^ε`.
  have h := evenHalfSpinAction_reverseEven_mul_self o ρ ε hQ h₂ (spinGroupToEven Q s)
  rw [reverseEven_spinGroupToEven_mul_self, map_one, ← halfSpinRep_apply] at h
  exact (smul_left_injective ℂ (one_ne_zero (α := Module.End ℂ (eigenspace _ ε)))
    ((one_smul ℂ _).trans h)).symm

/-- **The twisted action has determinant `z²`**: `(s, z)` acts on an eigenspace of `Γ` of
complex dimension two with determinant `z²`. So the determinant line of `W^±` is the square of the
twisting circle. -/
theorem det_spinCHalfSpinRep (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : spinGroup Q) (z : Circle) :
    LinearMap.det (spinCHalfSpinRep o ρ ε (s, z)) = (z : ℂ) ^ 2 := by
  rw [spinCHalfSpinRep_apply, LinearMap.det_smul, h₂, det_halfSpinRep o ρ ε hQ h₂, mul_one]

/-- **The determinant of the half-spin representations of `Spinᶜ(4)` is the determinant
character**: on an eigenspace of `Γ` of complex dimension two, `x` acts with determinant
`det x`, which is `z²` at `x = [s, z]`. -/
theorem det_spinCGroupHalfSpinRep (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (x : spinCGroup Q hQ₀) :
    LinearMap.det (spinCGroupHalfSpinRep o ρ ε hQ₀ x) = (spinCGroup.det Q hQ₀ x : ℂ) := by
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective Q hQ₀ x
  rw [spinCGroupHalfSpinRep_mk, det_spinCHalfSpinRep o ρ ε hQ h₂, spinCGroup.det_mk,
    Circle.coe_pow]

end Module

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} (ε : ℂ)

/-- **The half-spin representations are unitary** on a Hermitian Clifford module, whose
generators act skew-adjointly: `⟪ρ(s) ψ, ρ(s) χ⟫ = ⟪ψ, χ⟫`. -/
theorem inner_halfSpinRep_apply_halfSpinRep_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (s : spinGroup Q)
    (ψ χ : eigenspace (ρ (chirality Q o)) ε) :
    ⟪halfSpinRep o ρ ε s ψ, halfSpinRep o ρ ε s χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_halfSpinRep_apply, coe_halfSpinRep_apply,
    ← LinearMap.adjoint_inner_right, adjoint_map_eq_map_star hρ, ← Module.End.mul_apply,
    ← map_mul, spinGroup.star_mul_self_of_mem s.2, map_one, Module.End.one_apply]

/-- **The twisted half-spin representations are unitary** on a Hermitian Clifford module. -/
theorem inner_spinCHalfSpinRep_apply_spinCHalfSpinRep_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (p : spinGroup Q × Circle)
    (ψ χ : eigenspace (ρ (chirality Q o)) ε) :
    ⟪spinCHalfSpinRep o ρ ε p ψ, spinCHalfSpinRep o ρ ε p χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  obtain ⟨s, z⟩ := p
  rw [spinCHalfSpinRep_apply, LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, inner_halfSpinRep_apply_halfSpinRep_apply o ε hρ, ← mul_assoc,
    Complex.conj_mul', Circle.norm_coe, Complex.ofReal_one, one_pow, one_mul]

/-- **The half-spin representations of `Spinᶜ(4)` are unitary** on a Hermitian Clifford module. -/
theorem inner_spinCGroupHalfSpinRep_apply_spinCGroupHalfSpinRep_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (hQ₀ : Q ≠ 0)
    (x : spinCGroup Q hQ₀) (ψ χ : eigenspace (ρ (chirality Q o)) ε) :
    ⟪spinCGroupHalfSpinRep o ρ ε hQ₀ x ψ, spinCGroupHalfSpinRep o ρ ε hQ₀ x χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  obtain ⟨p, rfl⟩ := spinCGroup.mk_surjective Q hQ₀ x
  rw [spinCGroupHalfSpinRep_mk, inner_spinCHalfSpinRep_apply_spinCHalfSpinRep_apply o ε hρ]

end Hermitian

end CliffordAlgebra
