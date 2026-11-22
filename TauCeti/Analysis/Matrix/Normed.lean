/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UniformSpace.Matrix
import TauCeti.Topology.Instances.Matrix

/-!
# Topologies from matrix norms, and limits of products

This file exposes the topology underlying Mathlib's `L∞` operator norm on finite matrices. Since
matrix norms are scoped, consumers can select this topology locally without reconstructing the
instance projection chain.

Mathlib's `ContinuousStar` instance for matrices is stated for the entrywise topology. The `L∞`
operator topology agrees with it definitionally (`Matrix.linftyOpTopologicalSpace_eq`), but it is
not syntactically the same instance, so continuity of the conjugate transpose is transported along
that equality to the topology selected here.

The operator uniformity also agrees with the complete product uniformity when the entries are
complete. Its completeness instance is activated by `Matrix.Norms.Operator`, alongside the norm.
Similarly, the entrywise sup norm makes finite matrices over a proper space a proper space; this
instance is activated by `Matrix.Norms.Elementwise`, alongside the norm.

Over a seminormed ring, a family of matrices whose entries are bounded along a filter, multiplied
on either side by a family tending to `0`, tends to `0`. This is entrywise the corresponding
fact for the ring of entries, so it needs no matrix norm.

## Main declarations

* `Matrix.linftyOpTopologicalSpace`: the topology induced by the `L∞` operator norm.
* `Matrix.linftyOpTopologicalSpace_eq`: that topology is the entrywise topology on matrices.
* `Matrix.linftyOpContinuousStar`: conjugate transposition is continuous for that topology.
* `Matrix.linftyOpCompleteSpace`: completeness for the operator uniformity, scoped with the norm.
* `Matrix.ofContinuousLinearEquiv`: `Matrix.of` as a continuous linear equivalence from entry
  functions to matrices with the topology of the `L∞` operator norm.
* `Matrix.properSpace`: properness for the entrywise sup norm, scoped with the norm.
* `Matrix.isBoundedUnder_le_mul_tendsto_zero`, `Matrix.tendsto_zero_mul_isBoundedUnder_le`: an
  entrywise bounded family times a family tending to `0`, in either order, tends to `0`.
-/

public section

namespace Matrix

/-- The topology underlying the `L∞` operator norm on finite matrices. -/
protected noncomputable abbrev linftyOpTopologicalSpace
    (m n : Type*) [Fintype m] [Fintype n]
    (α : Type*) [SeminormedAddCommGroup α] : TopologicalSpace (Matrix m n α) :=
  (Matrix.linftyOpSeminormedAddCommGroup (m := m) (n := n) (α := α)).toPseudoMetricSpace
    |>.toUniformSpace |>.toTopologicalSpace

/-- The topology of the `L∞` operator norm is the entrywise topology on matrices.

This holds by `rfl` by design of Mathlib's `PiLp.pseudoMetricSpaceToPi`, which underlies
`Matrix.linftyOpSeminormedAddCommGroup`: it pulls back the `L^p` distance along `WithLp.toLp`
and then replaces the uniformity by the product uniformity, so the induced topology is the
product topology, which is Mathlib's topology on matrices. -/
theorem linftyOpTopologicalSpace_eq (m n : Type*) [Fintype m] [Fintype n]
    (α : Type*) [SeminormedAddCommGroup α] :
    Matrix.linftyOpTopologicalSpace m n α = (inferInstance : TopologicalSpace (Matrix m n α)) :=
  rfl

/-- Finite matrices over a complete normed additive group are complete for the
operator uniformity. -/
protected theorem linftyOpCompleteSpace {R p q : Type*} [NormedAddCommGroup R]
    [CompleteSpace R] [Fintype p] [Fintype q] :
    @CompleteSpace (Matrix p q R)
      (Matrix.linftyOpNormedAddCommGroup (m := p) (n := q) (α := R)).toUniformSpace :=
  inferInstanceAs (CompleteSpace (p → q → R))

namespace Norms.Operator
attribute [scoped instance] Matrix.linftyOpCompleteSpace
end Norms.Operator

/-- Finite matrices over a proper space are a proper space for the entrywise sup norm. -/
protected theorem properSpace {R p q : Type*} [SeminormedAddCommGroup R] [ProperSpace R]
    [Fintype p] [Fintype q] :
    @ProperSpace (Matrix p q R)
      (Matrix.seminormedAddCommGroup (m := p) (n := q) (α := R)).toPseudoMetricSpace :=
  inferInstanceAs (ProperSpace (p → q → R))

namespace Norms.Elementwise
attribute [scoped instance] Matrix.properSpace
end Norms.Elementwise

section

attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- Conjugate transposition is continuous for the topology of the `L∞` operator norm. -/
protected theorem linftyOpContinuousStar (n : Type*) [Fintype n]
    (α : Type*) [SeminormedAddCommGroup α] [Star α] [ContinuousStar α] :
    ContinuousStar (Matrix n n α) :=
  linftyOpTopologicalSpace_eq n n α ▸ inferInstance

end

section

attribute [local instance] Matrix.linftyOpTopologicalSpace

variable (R : Type*) {m n α : Type*} [Fintype m] [Fintype n] [Semiring R]
  [SeminormedAddCommGroup α] [Module R α]

/-- `Matrix.of` as a continuous linear equivalence from entry functions to matrices with the
topology of the `L∞` operator norm. That topology is the entrywise topology
(`Matrix.linftyOpTopologicalSpace_eq`), so both directions are continuous as the identity. -/
def ofContinuousLinearEquiv : (m → n → α) ≃L[R] Matrix m n α :=
  { ofLinearEquiv R with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

@[simp]
theorem coe_ofContinuousLinearEquiv :
    ⇑(ofContinuousLinearEquiv R : (m → n → α) ≃L[R] Matrix m n α) = of :=
  (rfl)

@[simp]
theorem coe_ofContinuousLinearEquiv_symm :
    ⇑(ofContinuousLinearEquiv R : (m → n → α) ≃L[R] Matrix m n α).symm = of.symm :=
  (rfl)

end

section

open Filter Topology

variable {ι l m n R : Type*} [Fintype m] [NonUnitalSeminormedRing R] {f : Filter ι}

/-- A family of matrices with entries bounded along `f`, times a family tending to `0`, tends
to `0`. -/
theorem isBoundedUnder_le_mul_tendsto_zero {F : ι → Matrix l m R} {H : ι → Matrix m n R}
    (hF : ∀ i k, IsBoundedUnder (· ≤ ·) f fun x ↦ ‖F x i k‖) (hH : Tendsto H f (𝓝 0)) :
    Tendsto (fun x ↦ F x * H x) f (𝓝 0) := by
  rw [tendsto_iff_tendsto_apply] at hH ⊢
  intro i j
  simpa only [Matrix.mul_apply, Matrix.zero_apply, Finset.sum_const_zero] using
    tendsto_finsetSum _ fun k _ ↦ Filter.isBoundedUnder_le_mul_tendsto_zero (hF i k) (hH k j)

/-- A family of matrices tending to `0`, times a family with entries bounded along `f`, tends
to `0`. -/
theorem tendsto_zero_mul_isBoundedUnder_le {H : ι → Matrix l m R} {F : ι → Matrix m n R}
    (hH : Tendsto H f (𝓝 0)) (hF : ∀ k j, IsBoundedUnder (· ≤ ·) f fun x ↦ ‖F x k j‖) :
    Tendsto (fun x ↦ H x * F x) f (𝓝 0) := by
  rw [tendsto_iff_tendsto_apply] at hH ⊢
  intro i j
  simpa only [Matrix.mul_apply, Matrix.zero_apply, Finset.sum_const_zero] using
    tendsto_finsetSum _ fun k _ ↦ (hH i k).zero_mul_isBoundedUnder_le (hF k j)

end

end Matrix
