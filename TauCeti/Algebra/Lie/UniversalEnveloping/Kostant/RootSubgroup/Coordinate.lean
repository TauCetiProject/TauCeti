/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix coordinates for Kostant root subgroups

Let `M` be a Kostant-stable integral lattice in a rational representation. A finite basis
`b : Basis η ℤ M` gives every scalar extension `A ⊗[ℤ] M` the base-changed basis
`b.baseChange A`. This file expresses the divided-power root subgroup action in that basis,
as an invertible matrix over `A` indexed by `η`.

The resulting matrices are natural in the commutative value ring. They are the finite-coordinate
input for the natural transformation whose representing morphism is the root subgroup
`𝔾ₐ → GLₙ`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix`: the matrix-valued root
  subgroup attached to a finite integral basis.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply`: its entries are the
  coordinates of the divided-power exponential on basis vectors.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix`: matrix coordinates commute
  with maps of value rings.
* `TauCeti.UniversalEnvelopingAlgebra.repr_kostantRootSubgroupPoints_baseChange`: the coordinates
  of a root-subgroup point on a base-changed basis vector.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_sum`: a nilpotent root
  operator exponentiates to the finite sum of its integral divided-power matrices.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*} [Fintype η] [DecidableEq η] (b : Module.Basis η ℤ M)

section Pointwise

variable {A : Type*} [CommRing A]

/-- The Kostant root subgroup in matrix coordinates: the monoid homomorphism sending an `A`-point
to the matrix of its action on `A ⊗[ℤ] M` in the base-changed basis `b.baseChange A`. -/
noncomputable def kostantRootSubgroupMatrix :
    WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) →*
      Matrix.GeneralLinearGroup η A :=
  (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
    (kostantRootSubgroupPoints e h ρ M hM i hnil)

/-- The public unfolding equation for the matrix-valued root subgroup, exposing across the module
boundary the divided-power action followed by the change to the coordinates of `b.baseChange A`. -/
theorem kostantRootSubgroupMatrix_def :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b =
      (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
        (kostantRootSubgroupPoints e h ρ M hM i hnil) := by
  rw [kostantRootSubgroupMatrix]

/-- An entry of the root-subgroup matrix is the corresponding coordinate of the exponential
action on a base-changed basis vector. -/
@[simp] theorem kostantRootSubgroupMatrix_apply
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) (r s : η) :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b f r s =
      (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val
          (b.baseChange A s)) r := by
  rw [kostantRootSubgroupMatrix, MonoidHom.comp_apply, Units.coe_map]
  exact LinearMap.toMatrixAlgEquiv_apply (b.baseChange A)
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).val r s

end Pointwise

omit [Fintype η] [DecidableEq η] in
/-- The coordinates of a root-subgroup point on a base-changed basis vector: the `r`-th
coordinate of `xᵢ(t) (1 ⊗ b s)` is the divided-power polynomial in `t` whose coefficients are the
`r`-th coordinates of the integral divided powers of `b s`. -/
theorem repr_kostantRootSubgroupPoints_baseChange {A : Type*} [CommRing A]
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) (r s : η) :
    (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val (b.baseChange A s)) r =
      ∑ k ∈ Finset.range
          (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
        b.repr (integralDividedPower
            (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
            (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
              e h ρ hM i k hv) (b s)) r •
          Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ k := by
  rw [Module.Basis.baseChange_apply, kostantRootSubgroupPoints_tmul, map_sum,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.Basis.baseChange_repr_tmul, mul_one]

/-- The zeroth divided power has the identity matrix in an integral lattice basis. -/
theorem integralDividedPower_zero_basis_eq_sum (s : η) :
    integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 0
        (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i 0 hv) (b s) =
      ∑ r, (1 : Matrix η η ℤ) r s • b r := by
  rw [integralDividedPower_zero]
  -- The rewrite leaves the identity endomorphism acting on the lattice subtype; exposing its
  -- underlying function is the definitional step needed before applying the basis expansion.
  change b s = ∑ r, (1 : Matrix η η ℤ) r s • b r
  convert (b.sum_repr (b s)).symm using 1
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrs : r = s
  · subst r
    simp
  · simp [hrs]

/-- **A nilpotent root-subgroup matrix is the finite divided-power sum.** If `X k` is the
integral matrix of the `k`th divided power for every `k < d`, and the nilpotency class is at most
`d`, then evaluation at `t` is `∑ k < d, t ^ k • X k`. -/
theorem kostantRootSubgroupMatrix_eq_sum {A : Type*} [CommRing A]
    (d : ℕ) (X : ℕ → Matrix η η ℤ)
    (hclass : nilpotencyClass
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ≤ d)
    (haction : ∀ k < d, ∀ s, integralDividedPower
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
      (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv)
      (b s) = ∑ r, X k r s • b r)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (kostantRootSubgroupMatrix e h ρ M hM i hnil b f).val =
      ∑ k ∈ Finset.range d,
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ k •
          (X k).map (Int.cast : ℤ → A) := by
  classical
  ext r s
  have hpad : ∑ k ∈ Finset.range
        (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
      b.repr (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
          (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv)
          (b s)) r • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ k =
      ∑ k ∈ Finset.range d,
        b.repr (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
            (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv)
            (b s)) r • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ k := by
    refine Finset.sum_subset (Finset.range_subset_range.2 hclass) fun k _ hk => ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [integralDividedPower_eq_zero_of_le _ _ _ _ (pow_nilpotencyClass hnil) hk]
    simp
  rw [kostantRootSubgroupMatrix_apply, repr_kostantRootSubgroupPoints_baseChange, hpad,
    Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Matrix.smul_apply, Matrix.map_apply, haction k (Finset.mem_range.1 hk) s,
    map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, map_zsmul, Module.Basis.repr_self,
    Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_ite_eq' Finset.univ r fun x => X k x s]
  simp [mul_comm]

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The matrix-valued Kostant root subgroup is natural in the value ring. -/
theorem map_kostantRootSubgroupMatrix (φ : A →+* B)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Matrix.GeneralLinearGroup.map φ
        (kostantRootSubgroupMatrix e h ρ M hM i hnil b f) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b
        (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom f) := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [Matrix.GeneralLinearGroup.map_apply,
    kostantRootSubgroupMatrix_apply, kostantRootSubgroupMatrix_apply]
  have hmatrix := Module.Basis.map_toMatrixAlgEquiv_baseChange b φ.toIntAlgHom
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).val
    (kostantRootSubgroupPoints e h ρ M hM i hnil
      (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom f)).val
    (map_kostantRootSubgroupPoints e h ρ M hM i hnil φ f)
  simpa only [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply,
    RingHom.toIntAlgHom_apply] using congrFun (congrFun hmatrix r) s

end Naturality

end TauCeti.UniversalEnvelopingAlgebra
