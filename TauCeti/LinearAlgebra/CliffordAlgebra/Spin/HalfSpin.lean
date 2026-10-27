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
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel

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
`Spinᶜ(4) = (Spin(4) × U(1)) / {±(1, 1)}`, the structure group of the spinor bundles of a `Spinᶜ`
four-manifold.

When `W^ε` has complex dimension two, `ρ(x* x) = det(ρ x)` on `W^ε` for every even `x`
(`CliffordAlgebra.map_star_mul_self_apply_of_mem_even`), so every Spin element acts with
determinant one, and `[s, z]` acts with determinant `z²`: the determinant line of `W^±` is the
square of the twisting circle. If `W` is moreover a Hermitian Clifford module, the generators
acting skew-adjointly, both representations are unitary.

## Main definitions

* `CliffordAlgebra.halfSpinRep o ρ ε`: the representation of `spinGroup Q` on the
  `ε`-eigenspace of `Γ`, restricting `CliffordAlgebra.evenHalfSpinAction o ρ ε`.
* `CliffordAlgebra.spinCHalfSpinRep o ρ ε`: the representation `(s, z) ↦ z ρ(s)` of
  `spinGroup Q × Circle` on that eigenspace.

## Main results

* `CliffordAlgebra.det_halfSpinRep`: Spin elements act on a two-dimensional `W^ε` with
  determinant one.
* `CliffordAlgebra.inner_halfSpinRep_apply_halfSpinRep_apply`: on a Hermitian Clifford module the
  Spin action is unitary.
* `CliffordAlgebra.spinCHalfSpinRep_negOne_neg_one`: `(-1, -1)` acts trivially, so the twisted
  action descends to `Spinᶜ(4)`.
* `CliffordAlgebra.det_spinCHalfSpinRep`: `(s, z)` acts with determinant `z²`, and
  `CliffordAlgebra.inner_spinCHalfSpinRep_apply_spinCHalfSpinRep_apply`: the twisted action is
  unitary.

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

/-- `halfSpinRep` is the restriction of the Clifford action. -/
@[simp]
theorem coe_halfSpinRep_apply (s : spinGroup Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinRep o ρ ε s ψ : W) = ρ s ψ := by
  simp [halfSpinRep]

/-- **The half-spin representation of `Spinᶜ(4)`**, before passing to the quotient by
`{±(1, 1)}`: `(s, z)` acts on the `ε`-eigenspace of `Γ` by `z ρ(s)`. It is trivial on
`(-1, -1)` (`CliffordAlgebra.spinCHalfSpinRep_negOne_neg_one`). -/
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

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **Spin elements act with determinant one** on an eigenspace of `Γ` of complex dimension
two: the half-spin representations of `Spin(4)` take values in the special linear group. -/
theorem det_halfSpinRep (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : spinGroup Q) : LinearMap.det (halfSpinRep o ρ ε s) = 1 := by
  have : Nontrivial (eigenspace (ρ (chirality Q o)) ε) :=
    Module.nontrivial_of_finrank_eq_succ h₂
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : eigenspace (ρ (chirality Q o)) ε)
  have hs : halfSpinRep o ρ ε s = evenHalfSpinAction o ρ ε ⟨s, spinGroup.mem_even s.2⟩ :=
    congrArg (evenHalfSpinAction o ρ ε) (Subtype.ext (coe_spinGroupToEven_apply Q s))
  have h := map_star_mul_self_apply_of_mem_even o ρ ε hQ h₂ (spinGroup.mem_even s.2) ψ
  rw [← hs] at h
  rw [spinGroup.star_mul_self_of_mem s.2, map_one, Module.End.one_apply, eq_comm,
    ← sub_eq_zero] at h
  have h' : (LinearMap.det (halfSpinRep o ρ ε s) - 1) • (ψ : W) = 0 := by
    rw [sub_smul, one_smul]
    exact h
  exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right (by simpa using hψ))

/-- **The twisted action has determinant `z²`**: `(s, z)` acts on an eigenspace of `Γ` of
complex dimension two with determinant `z²`. So the determinant line of `W^±` is the square of the
twisting circle. -/
theorem det_spinCHalfSpinRep (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : spinGroup Q) (z : Circle) :
    LinearMap.det (spinCHalfSpinRep o ρ ε (s, z)) = (z : ℂ) ^ 2 := by
  rw [spinCHalfSpinRep_apply, LinearMap.det_smul, h₂, det_halfSpinRep o ρ ε hQ h₂, mul_one]

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

end Hermitian

end CliffordAlgebra
