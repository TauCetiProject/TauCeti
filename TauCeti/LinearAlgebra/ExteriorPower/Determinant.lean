/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.LinearAlgebra.Determinant.Projective
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.Matrix.Compound
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Determinants of exterior-power actions

The **Sylvester–Franke theorem** computes the determinant of the action of a matrix on an exterior
power: for an `n × n` matrix `A` over a commutative ring and `0 < r`, the `r`-th compound matrix
`A.compound r`, the matrix of `⋀ʳ A` in the exterior-power basis, has determinant
`det A ^ (n - 1).choose (r - 1)`. For instance `⋀ⁿ A` has determinant `det A`, and on a free
module of rank four `⋀² A` has determinant `det A ^ 3`.

The exponent counts the `r`-element subsets containing a given index. Indeed, for a diagonal
matrix `diag(d)` the compound matrix is diagonal with entries `∏ i ∈ S, d i`, so its determinant
is `∏ S, ∏ i ∈ S, d i = (∏ i, d i) ^ (n - 1).choose (r - 1)`. Since the compound matrix is
multiplicative (the Cauchy–Binet formula `Matrix.compound_mul`), the general case over a field
follows from the factorisation of a matrix as a product of transvections and a diagonal matrix,
once one knows that transvections have compound matrices of determinant one. In characteristic
other than two this holds because `A ↦ det (A.compound r)` is multiplicative and a transvection
`t(c) = 1 + c • Eᵢⱼ` satisfies `t(2c) = t(c) ^ 2` while being conjugate to `t(2c)` by a diagonal
matrix. The identity over every commutative ring then follows from the case of the generic matrix
over the fraction field of `MvPolynomial (ι × ι) ℤ`, by specialisation.

The identity is transported to linear maps: on a free module of rank `n` the determinant
of `exteriorPower.map r f` is `det f ^ (n - 1).choose (r - 1)`, and the same holds for
`LinearMap.projectiveDet` on a finite projective module of constant rank `n`, by localising at
maximal ideals. Over a commutative ring, the determinant of the exterior-power action is therefore
a power of the original determinant, compatibly with base change.

## Main results

* `Matrix.det_compound`: the Sylvester–Franke theorem
  `det (A.compound r) = det A ^ (n - 1).choose (r - 1)` for `0 < r`.
* `LinearMap.det_exteriorPower_map`: the same for an endomorphism of a free module.
* `LinearMap.projectiveDet_exteriorPower_map`: the same for an endomorphism of a finite projective
  module of constant rank.

## References

* L. Tornheim, *The Sylvester–Franke theorem*, Amer. Math. Monthly 59 (1952), 389–391.
-/

public section

open Module

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- The determinant of the `r`-th compound matrix, as a multiplicative map of square matrices. -/
private noncomputable def detCompoundHom (R : Type*) [CommRing R] (r : ℕ) :
    Matrix ι ι R →* R where
  toFun A := (A.compound r).det
  map_one' := by simp
  map_mul' A B := by simp [compound_mul]

private theorem detCompoundHom_apply (r : ℕ) (A : Matrix ι ι R) :
    detCompoundHom R r A = (A.compound r).det :=
  rfl

/-- When `2` is a unit, transvections have compound matrices of determinant one: the
multiplicative map `A ↦ det (A.compound r)` takes the same value on `t(c)` and on its conjugate
`t(2c) = t(c) ^ 2` by a diagonal matrix, and this value is a unit. -/
private theorem det_compound_transvection (h2 : IsUnit (2 : R)) {i j : ι} (hij : i ≠ j) (c : R)
    (r : ℕ) : ((transvection i j c).compound r).det = 1 := by
  rw [← detCompoundHom_apply]
  set f := detCompoundHom (ι := ι) R r
  -- `t(2c) = t(c) ^ 2`, and `t(c)` is invertible with inverse `t(-c)`.
  have hsq : f (transvection i j (2 * c)) = f (transvection i j c) ^ 2 := by
    rw [sq, ← map_mul, transvection_mul_transvection_same _ _ hij, two_mul]
  have hinv : f (transvection i j c) * f (transvection i j (-c)) = 1 := by
    rw [← map_mul, transvection_mul_transvection_same _ _ hij, add_neg_cancel,
      transvection_zero, map_one]
  -- The diagonal matrix `D = 1 + Eᵢᵢ`, with entry `2` at `i`, conjugates `t(c)` to `t(2c)`.
  let D : Matrix ι ι R := 1 + single i i 1
  let a : R := ↑h2.unit⁻¹
  have hDD' : D * (1 + single i i (-a)) = 1 := by
    simp only [D, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, single_mul_single_same, one_mul]
    rw [add_assoc, ← single_add, ← single_add,
      show (1 + (-a + -a) : R) = 0 by rw [← h2.mul_val_inv]; ring, single_zero, add_zero]
  have hD : f D * f (1 + single i i (-a)) = 1 := by rw [← map_mul, hDD', map_one]
  have hconj : D * transvection i j c = transvection i j (2 * c) * D := by
    have h0 : single i j (2 * c) * single i i (1 : R) = 0 :=
      single_mul_single_of_ne _ _ _ _ hij.symm _
    rw [transvection, transvection]
    simp only [D, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h0, single_mul_single_same,
      one_mul, add_zero]
    rw [two_mul, single_add]
    abel
  have hcomm : f (transvection i j c) = f (transvection i j (2 * c)) := by
    have h := congrArg f hconj
    rw [map_mul, map_mul, mul_comm (f _) (f D)] at h
    exact (IsUnit.of_mul_eq_one _ hD).mul_left_cancel h
  have hu : IsUnit (f (transvection i j c)) := IsUnit.of_mul_eq_one _ hinv
  rw [hsq, sq] at hcomm
  exact hu.mul_left_cancel (hcomm.symm.trans (mul_one _).symm)

/-- The Sylvester–Franke theorem over a field of characteristic other than two, from the
factorisation of a matrix as transvections times a diagonal matrix. -/
private theorem det_compound_of_two_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (A : Matrix ι ι K) {r : ℕ} (hr : 0 < r) :
    (A.compound r).det = A.det ^ (Fintype.card ι - 1).choose (r - 1) := by
  obtain ⟨L, L', D, rfl⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  -- Products of transvections have determinant one and compound matrices of determinant one.
  have hcomp (L : List (TransvectionStruct ι K)) :
      detCompoundHom K r (L.map TransvectionStruct.toMatrix).prod = 1 := by
    rw [map_list_prod, List.map_map]
    exact List.prod_eq_one fun x hx ↦ by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
      exact det_compound_transvection (Ne.isUnit h2) t.hij t.c r
  have h := hcomp L
  have h' := hcomp L'
  rw [detCompoundHom_apply] at h h'
  rw [compound_mul, compound_mul, det_mul, det_mul, h, h', det_mul, det_mul,
    TransvectionStruct.det_toMatrix_prod, TransvectionStruct.det_toMatrix_prod,
    compound_diagonal, det_diagonal, det_diagonal, Set.powersetCard.prod_prod hr]
  simp only [one_mul, mul_one]

/-- **The Sylvester–Franke theorem**: for `0 < r`, the `r`-th compound matrix of a square matrix
`A` with `n` rows has determinant `det A ^ (n - 1).choose (r - 1)`. -/
theorem det_compound (A : Matrix ι ι R) {r : ℕ} (hr : 0 < r) :
    (A.compound r).det = A.det ^ (Fintype.card ι - 1).choose (r - 1) := by
  -- The identity for the generic matrix `X` over `P = ℤ[Xᵢⱼ]`, checked in its fraction field.
  let P := MvPolynomial (ι × ι) ℤ
  let X := mvPolynomialX ι ι ℤ
  have hX : (X.compound r).det = X.det ^ (Fintype.card ι - 1).choose (r - 1) := by
    have h2 : (2 : FractionRing P) ≠ 0 := by
      have h := (IsFractionRing.injective P (FractionRing P)).ne (two_ne_zero : (2 : P) ≠ 0)
      rwa [map_ofNat, map_zero] at h
    apply IsFractionRing.injective P (FractionRing P)
    rw [map_pow, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, ← compound_map]
    exact det_compound_of_two_ne_zero h2 _ hr
  -- Specialise the generic matrix to `A`.
  let ψ := MvPolynomial.eval₂Hom (Int.castRingHom R) fun p : ι × ι ↦ A p.1 p.2
  have hA : X.map ψ = A := mvPolynomialX_map_eval₂ _ A
  have h := congrArg ψ hX
  rwa [map_pow, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, ← compound_map, hA] at h

end Matrix

namespace LinearMap

open TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The Sylvester–Franke theorem** for linear maps: for `0 < r`, an endomorphism `f` of a free
module of rank `n` acts on its `r`-th exterior power with determinant
`det f ^ (n - 1).choose (r - 1)`. In infinite rank both determinants are `1`. -/
theorem det_exteriorPower_map [Module.Free R M] (f : M →ₗ[R] M) {r : ℕ} (hr : 0 < r) :
    LinearMap.det (exteriorPower.map r f) = LinearMap.det f ^ (finrank R M - 1).choose (r - 1) := by
  nontriviality R
  by_cases hM : Module.Finite R M
  · let b := Module.finBasis R M
    rw [← LinearMap.det_toMatrix (b.exteriorPower r), ← LinearMap.det_toMatrix b,
      Module.Basis.toMatrix_exteriorPower_map_eq_compound, Matrix.det_compound _ hr,
      Fintype.card_fin]
  · -- In infinite rank, the exterior power has an infinite basis, so neither module is finite.
    rw [det_eq_one_of_not_module_finite hM, one_pow]
    refine det_eq_one_of_not_module_finite (fun h ↦ ?_) _
    classical
    let b := Module.Free.chooseBasis R M
    let _ : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
    have : Infinite (Module.Free.ChooseBasisIndex R M) :=
      not_finite_iff_infinite.mp fun _ ↦ hM (Module.Finite.of_basis b)
    have : NeZero r := ⟨hr.ne'⟩
    have := Module.Finite.finite_basis (b.exteriorPower r)
    exact not_finite (Set.powersetCard (Module.Free.ChooseBasisIndex R M) r)

/-- **The Sylvester–Franke theorem** for finite projective modules: for `0 < r`, an endomorphism
`f` of a finite projective module of constant rank `d` acts on its `r`-th exterior power with
determinant `projectiveDet f ^ (d - 1).choose (r - 1)`. -/
theorem projectiveDet_exteriorPower_map [Module.Finite R M] [Module.Projective R M] {d : ℕ}
    (hd : ∀ p, rankAtStalk (R := R) M p = d) (f : Module.End R M) {r : ℕ} (hr : 0 < r) :
    projectiveDet (exteriorPower.map r f) = projectiveDet f ^ (d - 1).choose (r - 1) := by
  refine Module.eq_of_localization_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap R (Localization.AtPrime P)) _ _ fun P _ ↦ ?_
  let A := Localization.AtPrime P
  have : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  have hfin : finrank A (A ⊗[R] M) = d := by
    rw [← rankAtStalk_eq_finrank_tensorProduct (M := M) ⟨P, inferInstance⟩, hd]
  -- Over the local ring `A`, the base change of `⋀ʳ f` is conjugate to `⋀ʳ` of the base change
  -- of `f`, an endomorphism of a free module of rank `d`.
  let e := TauCeti.exteriorPower.equivBaseChange (R := R) (M := M) A r
  have hconj : (exteriorPower.map r f).baseChange A =
      (e : _ →ₗ[A] _) ∘ₗ exteriorPower.map r (f.baseChange A) ∘ₗ (e.symm : _ →ₗ[A] _) := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [e, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      TauCeti.exteriorPower.equivBaseChange_map]
  simp only [Algebra.linearMap_apply, map_pow, ← projectiveDet_baseChange]
  rw [hconj, projectiveDet_conj, projectiveDet_eq_det, projectiveDet_eq_det,
    det_exteriorPower_map _ hr, hfin]

end LinearMap
