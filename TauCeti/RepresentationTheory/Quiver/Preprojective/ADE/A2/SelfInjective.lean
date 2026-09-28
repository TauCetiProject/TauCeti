/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Truncation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.A2.Basic

/-!
# Self-injectivity of the preprojective algebra of `A₂`

The preprojective algebra of `A₂` is the radical-square-zero algebra of the doubled edge. It has
a basis consisting of the two vertex idempotents and the two oppositely oriented arrows. The
linear functional which is one on both arrows and zero on the vertices gives a Frobenius pairing

```text
(x, y) ↦ φ (x * y).
```

In the displayed basis its Gram matrix is a permutation matrix: each basis element has a unique
right-dual basis element. The pairing is therefore perfect over every commutative ring. Over a
field, the general Frobenius criterion proves that both regular modules are injective. Together
with finite-dimensionality from
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.A2.Basic`, this settles both parts of the
finite-ADE preprojective claim in type `A₂`.

## Main definitions

* `TauCeti.preprojectiveA2Basis`: the two vertices and two arrows as a basis.
* `TauCeti.preprojectiveA2FrobeniusFunctional`: the functional taking both arrows to one.
* `TauCeti.preprojectiveA2FrobeniusPairing`: multiplication followed by that functional.
* `TauCeti.preprojectiveA2RightDualIndex`: the right-dual permutation of the displayed basis.

## Main results

* `TauCeti.preprojectiveA2FrobeniusPairing_isPerfPair`: the Frobenius pairing is perfect.
* `TauCeti.moduleInjective_preprojectiveAlgebra_A2`: the `A₂` preprojective algebra is
  left self-injective.
* `TauCeti.moduleInjective_op_preprojectiveAlgebra_A2`: the `A₂` preprojective algebra is
  right self-injective.

## References

See W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1, for the preprojective presentation, and C. M. Ringel,
*The preprojective algebra of a quiver*, for the Frobenius property in finite Dynkin type.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

private abbrev v0 : Symmetrify preprojectiveA2Quiver :=
  Symmetrify.of.obj preprojectiveA2VertexZero

private abbrev v1 : Symmetrify preprojectiveA2Quiver :=
  Symmetrify.of.obj preprojectiveA2VertexOne

private def a2ShortPath : Fin 4 → ShortPath (Symmetrify preprojectiveA2Quiver) 2
  | 0 => ⟨⟨v0, v0, .nil⟩, by simp⟩
  | 1 => ⟨⟨v1, v1, .nil⟩, by simp⟩
  | 2 => ⟨⟨v0, v1, preprojectiveA2ForwardArrow.toPath⟩, by simp⟩
  | 3 => ⟨⟨v1, v0, preprojectiveA2ReverseArrow.toPath⟩, by simp⟩

private theorem a2ShortPath_injective : Function.Injective a2ShortPath := by
  intro i j h
  apply Fin.ext
  have hc := congrArg
    (fun x : ShortPath (Symmetrify preprojectiveA2Quiver) 2 =>
      2 * x.1.2.2.length + (preprojectiveA2DoubledVertexEquiv.symm x.1.1).val) h
  fin_cases i <;> fin_cases j <;>
    simp [a2ShortPath] at hc ⊢

private theorem a2ShortPath_surjective : Function.Surjective a2ShortPath := by
  rintro ⟨⟨i, j, p⟩, hp⟩
  -- Expose the path-length condition carried by the dependent `ShortPath` subtype.
  change p.length < 2 at hp
  have hlen : p.length = 0 ∨ p.length = 1 := by omega
  rcases hlen with hlen | hlen
  · obtain rfl := Path.eq_of_length_zero p hlen
    obtain rfl := Path.eq_nil_of_length_zero p hlen
    rcases preprojectiveA2DoubledVertex_cases i with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · obtain ⟨c, e, q, hq, rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p hlen
    obtain rfl := Path.eq_of_length_zero q hq
    obtain rfl := Path.eq_nil_of_length_zero q hq
    rcases preprojectiveA2DoubledArrow_cases e with
      ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
    · cases he
      exact ⟨2, rfl⟩
    · cases he
      exact ⟨3, rfl⟩

private noncomputable def a2ShortPathEquiv :
    Fin 4 ≃ ShortPath (Symmetrify preprojectiveA2Quiver) 2 :=
  Equiv.ofBijective a2ShortPath ⟨a2ShortPath_injective, a2ShortPath_surjective⟩

universe w

section CommRing

variable (k : Type w) [CommRing k]

/-- The basis of the `A₂` preprojective algebra consisting, in order, of the vertex at `0`, the
vertex at `1`, the arrow `0 → 1`, and its formal reverse `1 → 0`. -/
noncomputable def preprojectiveA2Basis :
    Module.Basis (Fin 4) k (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (((arrowIdealQuotientBasis k (Symmetrify preprojectiveA2Quiver) 2).reindex
    a2ShortPathEquiv.symm).map (preprojectiveAlgebraEquivA2 k).symm.toLinearEquiv)

private theorem preprojectiveA2Basis_apply (i : Fin 4) :
    preprojectiveA2Basis k i =
      preprojectiveMk k preprojectiveA2Quiver (ofPath (a2ShortPath i).1) := by
  rw [preprojectiveA2Basis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm]
  -- Expose the representative selected by the reindexed quotient basis before applying the
  -- presentation equivalence.
  change (preprojectiveAlgebraEquivA2 k).symm
      (arrowIdealQuotientBasis k (Symmetrify preprojectiveA2Quiver) 2 (a2ShortPathEquiv i)) = _
  apply (preprojectiveAlgebraEquivA2 k).injective
  rw [AlgEquiv.apply_symm_apply, arrowIdealQuotientBasis_apply,
    preprojectiveAlgebraEquivA2_preprojectiveMk]
  rfl

/-- The first basis vector is the trivial path at vertex zero. -/
@[simp]
theorem preprojectiveA2Basis_zero :
    preprojectiveA2Basis k 0 =
      preprojectiveMk k preprojectiveA2Quiver
        (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexZero,
          Symmetrify.of.obj preprojectiveA2VertexZero, .nil⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (0 : Fin 4)

/-- The second basis vector is the trivial path at vertex one. -/
@[simp]
theorem preprojectiveA2Basis_one :
    preprojectiveA2Basis k 1 =
      preprojectiveMk k preprojectiveA2Quiver
        (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexOne,
          Symmetrify.of.obj preprojectiveA2VertexOne, .nil⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (1 : Fin 4)

/-- The third basis vector is the forward arrow. -/
@[simp]
theorem preprojectiveA2Basis_two :
    preprojectiveA2Basis k 2 = preprojectiveMk k preprojectiveA2Quiver
      (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexZero,
        Symmetrify.of.obj preprojectiveA2VertexOne,
          preprojectiveA2ForwardArrow.toPath⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (2 : Fin 4)

/-- The fourth basis vector is the reverse arrow. -/
@[simp]
theorem preprojectiveA2Basis_three :
    preprojectiveA2Basis k 3 = preprojectiveMk k preprojectiveA2Quiver
      (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexOne,
        Symmetrify.of.obj preprojectiveA2VertexZero,
          preprojectiveA2ReverseArrow.toPath⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (3 : Fin 4)

/-- The Frobenius functional on the `A₂` preprojective algebra: it is zero on the two vertex
idempotents and one on each of the two arrows. -/
noncomputable def preprojectiveA2FrobeniusFunctional :
    preprojectiveAlgebra k preprojectiveA2Quiver →ₗ[k] k :=
  (preprojectiveA2Basis k).constr k ![0, 0, 1, 1]

@[simp]
theorem preprojectiveA2FrobeniusFunctional_basis (i : Fin 4) :
    preprojectiveA2FrobeniusFunctional k (preprojectiveA2Basis k i) = ![0, 0, 1, 1] i :=
  (preprojectiveA2Basis k).constr_basis k ![0, 0, 1, 1] i

private theorem preprojectiveMk_ofPath_eq_zero_of_two_le
    (p : Quiver.TotalPath (Symmetrify preprojectiveA2Quiver)) (hp : 2 ≤ p.2.2.length) :
    preprojectiveMk k preprojectiveA2Quiver (ofPath p) = 0 := by
  rw [preprojectiveMk_eq_zero_iff]
  -- The quotient kernel is a two-sided ideal, while the truncation theorem uses its underlying
  -- ordinary ideal.
  change ofPath p ∈ (preprojectiveIdeal k preprojectiveA2Quiver).asIdeal
  rw [preprojectiveIdeal_A2_eq_arrowIdeal_sq]
  exact Ideal.pow_le_pow_right hp (ofPath_mem_arrowIdeal_pow p)

/-- The partial multiplication operation on indices of `TauCeti.preprojectiveA2Basis`; `none`
means that the product is zero. -/
def preprojectiveA2BasisMul : Fin 4 → Fin 4 → Option (Fin 4)
  | 0, 0 => some 0
  | 0, 3 => some 3
  | 1, 1 => some 1
  | 1, 2 => some 2
  | 2, 0 => some 2
  | 3, 1 => some 3
  | _, _ => none

/-- The multiplication table of `TauCeti.preprojectiveA2Basis`. -/
theorem preprojectiveA2Basis_mul (i j : Fin 4) :
    preprojectiveA2Basis k i * preprojectiveA2Basis k j =
      (preprojectiveA2BasisMul i j).elim 0 (preprojectiveA2Basis k) := by
  fin_cases i <;> fin_cases j <;>
    simp only [preprojectiveA2BasisMul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Option.elim_some, Option.elim_none]
  all_goals simp only [preprojectiveA2Basis_apply, a2ShortPath]
  all_goals rw [← map_mul]
  · rw [ofPath_mul_ofPath_of_comp]
    simp
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one.symm, map_zero]
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one.symm, map_zero]
  · rw [ofPath_mul_ofPath_of_comp]
    rw [Path.comp_nil]
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one, map_zero]
  · rw [ofPath_mul_ofPath_of_comp]
    rfl
  · rw [ofPath_mul_ofPath_of_comp]
    simp
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one, map_zero]
  · rw [ofPath_mul_ofPath_of_comp]
    rfl
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one.symm, map_zero]
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one.symm, map_zero]
  · rw [ofPath_mul_ofPath_of_comp]
    apply preprojectiveMk_ofPath_eq_zero_of_two_le
    simp
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one, map_zero]
  · rw [ofPath_mul_ofPath_of_comp]
    rw [Path.nil_comp]
  · rw [ofPath_mul_ofPath_of_comp]
    apply preprojectiveMk_ofPath_eq_zero_of_two_le
    simp
  · rw [ofPath_mul_ofPath_of_not_composable
      preprojectiveA2DoubledVertexZero_ne_one, map_zero]

/-- Multiplication followed by `TauCeti.preprojectiveA2FrobeniusFunctional`, the Frobenius pairing
on the `A₂` preprojective algebra. -/
noncomputable def preprojectiveA2FrobeniusPairing :
    LinearMap.BilinForm k (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (LinearMap.mul k _).compr₂ (preprojectiveA2FrobeniusFunctional k)

@[simp]
theorem preprojectiveA2FrobeniusPairing_apply
    (x y : preprojectiveAlgebra k preprojectiveA2Quiver) :
    preprojectiveA2FrobeniusPairing k x y = preprojectiveA2FrobeniusFunctional k (x * y) := by
  rw [preprojectiveA2FrobeniusPairing, LinearMap.compr₂_apply, LinearMap.mul_apply']

/-- The permutation matching each element of `TauCeti.preprojectiveA2Basis` with its right dual
for the Frobenius pairing. -/
def preprojectiveA2RightDualIndex : Equiv.Perm (Fin 4) where
  toFun
    | 0 => 3
    | 1 => 2
    | 2 => 0
    | 3 => 1
  invFun
    | 0 => 2
    | 1 => 3
    | 2 => 1
    | 3 => 0
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- **The Gram matrix of the `A₂` Frobenius pairing is a permutation matrix.** -/
theorem preprojectiveA2FrobeniusPairing_basis (i j : Fin 4) :
    preprojectiveA2FrobeniusPairing k (preprojectiveA2Basis k i)
      (preprojectiveA2Basis k j) =
        if j = preprojectiveA2RightDualIndex i then 1 else 0 := by
  rw [preprojectiveA2FrobeniusPairing_apply, preprojectiveA2Basis_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [preprojectiveA2BasisMul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Option.elim_some, Option.elim_none]
  all_goals simp only [map_zero, preprojectiveA2FrobeniusFunctional_basis]
  all_goals simp [preprojectiveA2RightDualIndex]

/-- **The `A₂` Frobenius pairing is perfect.** Its Gram matrix is a permutation matrix, so no
scalar needs to be inverted and a commutative base ring suffices. -/
instance preprojectiveA2FrobeniusPairing_isPerfPair :
    (preprojectiveA2FrobeniusPairing k).IsPerfPair := by
  have key : preprojectiveA2FrobeniusPairing k =
      ((preprojectiveA2Basis k).equiv (preprojectiveA2Basis k).dualBasis
        preprojectiveA2RightDualIndex).toLinearMap := by
    refine (preprojectiveA2Basis k).ext fun i => (preprojectiveA2Basis k).ext fun j => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Module.Basis.dualBasis_apply_self,
      preprojectiveA2FrobeniusPairing_basis]
  have hbij : Function.Bijective ⇑(preprojectiveA2FrobeniusPairing k) := by
    rw [key]
    exact LinearEquiv.bijective _
  have keyFlip : LinearMap.flip (preprojectiveA2FrobeniusPairing k) =
      ((preprojectiveA2Basis k).equiv (preprojectiveA2Basis k).dualBasis
        preprojectiveA2RightDualIndex.symm).toLinearMap := by
    refine (preprojectiveA2Basis k).ext fun i => (preprojectiveA2Basis k).ext fun j => ?_
    rw [LinearMap.flip_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Module.Basis.dualBasis_apply_self, preprojectiveA2FrobeniusPairing_basis]
    fin_cases i <;> fin_cases j <;> simp [preprojectiveA2RightDualIndex]
  have hbijFlip : Function.Bijective ⇑(LinearMap.flip
      (preprojectiveA2FrobeniusPairing k)) := by
    rw [keyFlip]
    exact LinearEquiv.bijective _
  exact ⟨hbij, hbijFlip⟩

/-- **The displayed functional makes the `A₂` preprojective algebra Frobenius.** -/
theorem isFrobeniusFunctional_preprojectiveA2FrobeniusFunctional :
    (preprojectiveA2FrobeniusFunctional k).IsFrobeniusFunctional := by
  have h := (preprojectiveA2FrobeniusPairing_isPerfPair k).nondegenerate
  exact LinearMap.isFrobeniusFunctional_iff.mpr ⟨
    fun a ha => h.1 a fun b => by simpa using ha b,
    fun b hb => h.2 b fun a => by simpa using hb a⟩

end CommRing

section Field

variable (k : Type w) [Field k]

/-- **The preprojective algebra of `A₂` is left self-injective.** -/
theorem moduleInjective_preprojectiveAlgebra_A2 :
    Module.Injective (preprojectiveAlgebra k preprojectiveA2Quiver)
      (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (isFrobeniusFunctional_preprojectiveA2FrobeniusFunctional k).moduleInjective_self

/-- **The preprojective algebra of `A₂` is right self-injective.** -/
theorem moduleInjective_op_preprojectiveAlgebra_A2 :
    Module.Injective (preprojectiveAlgebra k preprojectiveA2Quiver)ᵐᵒᵖ
      (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (isFrobeniusFunctional_preprojectiveA2FrobeniusFunctional k).moduleInjective_op_self

end Field

end TauCeti
