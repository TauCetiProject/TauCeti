/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic

/-!
# Lattice coordinates on the dual space

Let `i : N →+ V` be an additive map from an abelian group of integral vectors into a real normed
space. A basis `b` of `N` gives *lattice coordinates* `x ↦ (⟨x, b k⟩)_k` on `V*`
(`TauCeti.Toric.latticeCoord i b`). A point of `V*` takes integer values on the lattice exactly
when its lattice coordinates are integers (`TauCeti.Toric.forall_apply_mem_range_intCast_iff`).
For an integral lattice the lattice coordinates are a linear isomorphism `V* ≃ ℝ^κ`
(`TauCeti.Toric.IsIntegralLattice.bijective_latticeCoord`), so they carry the dual lattice
`{x ∈ V* | ⟨x, n⟩ ∈ ℤ for every n ∈ N}` onto `ℤ^κ`. Two lattice bases give coordinates related
by the transpose of the integral change-of-basis matrix (`TauCeti.Toric.latticeCoord_eq_mulVec`).

## Main definitions

* `TauCeti.Toric.latticeCoord i b`: the coordinates `x ↦ (⟨x, b k⟩)_k` of `V*` in a lattice basis.

## Main results

* `TauCeti.Toric.apply_eq_sum_latticeCoord`: the value of a point of `V*` on a lattice vector, in
  lattice coordinates.
* `TauCeti.Toric.latticeCoord_eq_mulVec`: change of lattice basis.
* `TauCeti.Toric.forall_apply_mem_range_intCast_iff`: the dual lattice in lattice coordinates.
* `TauCeti.Toric.IsIntegralLattice.bijective_latticeCoord`: for an integral lattice, the lattice
  coordinates are bijective.
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable {κ κ' N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

variable (i) in
/-- The *lattice coordinates* `x ↦ (⟨x, b k⟩)_k` of a point `x` of `V*` in a basis `b` of the
lattice `N`. -/
def latticeCoord (b : Module.Basis κ ℤ N) : StrongDual ℝ V →L[ℝ] κ → ℝ :=
  ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.apply ℝ ℝ (i (b k))

@[simp]
theorem latticeCoord_apply (b : Module.Basis κ ℤ N) (x : StrongDual ℝ V) (k : κ) :
    latticeCoord i b x k = x (i (b k)) :=
  (rfl)

/-- The value of a point of `V*` on a lattice vector `n` is the combination of its lattice
coordinates with the coordinates of `n`. -/
theorem apply_eq_sum_latticeCoord [Fintype κ] (b : Module.Basis κ ℤ N) (x : StrongDual ℝ V)
    (n : N) : x (i n) = ∑ k, (b.repr n k : ℝ) * latticeCoord i b x k := by
  conv_lhs => rw [← b.sum_repr n]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, latticeCoord_apply]

/-- **Change of lattice basis.** The lattice coordinates in a basis `b'` are obtained from those in
`b` by the transpose of the integral change-of-basis matrix. -/
theorem latticeCoord_eq_mulVec [Fintype κ] (b : Module.Basis κ ℤ N) (b' : Module.Basis κ' ℤ N)
    (x : StrongDual ℝ V) :
    latticeCoord i b' x =
      ((b.toMatrix b').transpose.map ((↑) : ℤ → ℝ)).mulVec (latticeCoord i b x) := by
  funext k'
  rw [latticeCoord_apply, apply_eq_sum_latticeCoord b x (b' k')]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply,
    Module.Basis.toMatrix_apply]

/-- **The dual lattice in lattice coordinates.** A point of `V*` takes integer values on the
lattice exactly when its lattice coordinates are integers. -/
theorem forall_apply_mem_range_intCast_iff (b : Module.Basis κ ℤ N) (x : StrongDual ℝ V) :
    (∀ n, x (i n) ∈ range ((↑) : ℤ → ℝ)) ↔ ∀ k, latticeCoord i b x k ∈ range ((↑) : ℤ → ℝ) := by
  refine ⟨fun h k ↦ h (b k), fun h n ↦ ?_⟩
  induction b.mem_span n using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨k, rfl⟩ := hm
    exact h k
  | zero => exact ⟨0, by simp⟩
  | add m m' _ _ hm hm' =>
    obtain ⟨p, hp⟩ := hm
    obtain ⟨q, hq⟩ := hm'
    exact ⟨p + q, by simp [hp, hq]⟩
  | smul z m _ hm =>
    obtain ⟨p, hp⟩ := hm
    exact ⟨z * p, by simp [hp]⟩

/-- For an integral lattice, the lattice coordinates in any basis are a linear isomorphism
`V* ≃ ℝ^κ`: the images `i (b k)` of a lattice basis form a real basis of `V`. With
`forall_apply_mem_range_intCast_iff`, they carry the dual lattice onto `ℤ^κ`. -/
theorem IsIntegralLattice.bijective_latticeCoord (hi : IsIntegralLattice i)
    (b : Module.Basis κ ℤ N) : Function.Bijective (latticeCoord i b) := by
  have := hi.finite
  have := Module.Finite.finite_basis b
  let B := hi.isBaseChange.basis b
  have hB (k : κ) : B k = i (b k) := by simpa using hi.isBaseChange.basis_apply b k
  refine ⟨fun x y hxy ↦ ContinuousLinearMap.coe_injective (B.ext fun k ↦ ?_), fun y ↦ ?_⟩
  · simpa [hB] using congrFun hxy k
  · have := Module.Finite.of_basis B
    refine ⟨LinearMap.toContinuousLinearMap (B.constr ℝ y), funext fun k ↦ ?_⟩
    simp [← hB, Module.Basis.constr_basis]

end TauCeti.Toric
