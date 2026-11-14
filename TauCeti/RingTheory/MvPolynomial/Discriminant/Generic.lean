/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Prime
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Normalization
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# Weighted homogeneity and primality of generic discriminants

Let `R` be a commutative ring. A monic polynomial of degree `m` over `R` has `m` free lower
coefficients, represented universally by `Polynomial.freeMonic R m` over `MvPolynomial (Fin m) R`,
and `m - 1` lower coefficients after depressing the subleading term, represented universally by
`TauCeti.genericDepressed R m = X ^ m + a₂ X ^ (m - 2) + ⋯ + aₘ` over
`MvPolynomial (Fin (m - 1)) R`. This file establishes the weighted homogeneity and unique
factorization primality of their discriminants.

1. **Weighted homogeneity.** Scaling the roots of `Polynomial.freeMonic R m` by an indeterminate
   `T` multiplies the `k`-th coefficient by `T ^ (m - k)` and multiplies the discriminant by
   `T ^ (m * (m - 1))`. Consequently `(Polynomial.freeMonic R m).discr` is weighted homogeneous of
   weight `m * (m - 1)` when `X k` is given weight `m - k`
   (`Polynomial.isWeightedHomogeneous_discr_freeMonic`). Specializing the universal monic
   polynomial transfers this to any monic polynomial `f` over `MvPolynomial σ R` whose `k`-th
   coefficient is weighted homogeneous of weight `(f.natDegree - k) • u` in an arbitrary additive
   commutative monoid (`Polynomial.Monic.isWeightedHomogeneous_discr`). In particular,
   `TauCeti.depressedDiscr R m` has weight `m * (m - 1)` for `TauCeti.depressedWeight m`
   (`TauCeti.depressedDiscr_mem`).

2. **Primality of the generic monic discriminant.** Via Vieta's formulas and the fundamental
   theorem of symmetric polynomials, `MvPolynomial (Fin m) R` embeds `R`-algebraically onto the
   symmetric polynomials in `m` root variables, sending `(Polynomial.freeMonic R m).discr` to the
   square `δ ^ 2` of the Vandermonde product `δ = ∏_{i < j} (X i - X j)`. Over a unique
   factorization domain `R` with `2 ≤ m`, the linear factors `X i - X j` are pairwise
   non-associated primes permuted transitively on ordered pairs by `Equiv.Perm (Fin m)`. Any
   symmetric factor of `δ ^ 2` divisible by one root difference is therefore divisible by `δ`,
   whereas permuting two variables negates `δ` and rules out symmetric unit multiples of `δ`
   whenever `(2 : R) ≠ 0`. Conversely, when `(2 : R) = 0`, `δ` is symmetric and the generic
   discriminant is a square (`Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`). Hence
   `(Polynomial.freeMonic R m).discr` is prime if and only if `(2 : R) ≠ 0`
   (`Polynomial.prime_discr_freeMonic_iff`).

3. **Tschirnhaus equivalence and the generic depressed discriminant.** When `(m : R)` is a unit,
   translating the variable by the root barycenter identifies `MvPolynomial (Fin m) R` as an
   `R`-algebra with `Polynomial (MvPolynomial (Fin (m - 1)) R)` (`TauCeti.tschirnhausAlgEquiv`),
   carrying `(Polynomial.freeMonic R m).discr` to `Polynomial.C (TauCeti.depressedDiscr R m)` by
   translation invariance of the discriminant. Primality of `TauCeti.depressedDiscr R m` over any
   unique factorization domain in which `2 ≠ 0` and `m` is invertible
   (`TauCeti.prime_depressedDiscr_of_isUnit`), and in particular over any field of characteristic
   zero (`TauCeti.depressedDiscr_prime`), follows immediately.

4. **Low degrees and sharpness.** Explicit formulas are given in degrees `0` through `4`,
   including the Weierstrass cubic discriminant `4 X₀³ + 27 X₁²` of weight `12` for weights
   `(4, 6)`, together with counterexamples showing that `(2 : R) ≠ 0`, invertibility of `3` in
   degree `3`, and `IsUnit (m : R)` over `ℤ` in degree `2` are all necessary.

## Main definitions

* `TauCeti.genericDepressed R m`: the generic monic depressed polynomial
  `X ^ m + ∑ i : Fin (m - 1), C (MvPolynomial.X i) * X ^ (m - (i + 2))`.
* `TauCeti.depressedWeight m`: the weight assignment `i ↦ (i : ℤ) + 2` on `Fin (m - 1)`.
* `TauCeti.depressedDiscr R m`: the discriminant `(genericDepressed R m).discr`.
* `TauCeti.tschirnhausAlgEquiv`: for `IsUnit (m : R)`, the Tschirnhaus `R`-algebra equivalence
  `MvPolynomial (Fin m) R ≃ₐ[R] Polynomial (MvPolynomial (Fin (m - 1)) R)`.

## Main results

* `Polynomial.isWeightedHomogeneous_discr_freeMonic`,
  `Polynomial.Monic.isWeightedHomogeneous_discr`: weighted homogeneity of the universal and
  specialized monic discriminants.
* `Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`,
  `Polynomial.prime_discr_freeMonic`, `Polynomial.prime_discr_freeMonic_iff`: squareness when
  `2 = 0` and unique factorization primality of `(Polynomial.freeMonic R m).discr` when `2 ≤ m`.
* `TauCeti.depressedDiscr_mem`, `TauCeti.isWeightedHomogeneous_depressedDiscr`: weighted
  homogeneity of `depressedDiscr R m` of weight `m * (m - 1)`.
* `TauCeti.tschirnhausAlgEquiv_discr_freeMonic`, `TauCeti.prime_depressedDiscr_iff`:
  identification of generic monic and depressed discriminants when `m` is invertible.
* `TauCeti.prime_depressedDiscr_of_isUnit`, `TauCeti.prime_depressedDiscr`,
  `TauCeti.depressedDiscr_prime`: primality of `depressedDiscr`.
* `TauCeti.depressedDiscr_two`, `TauCeti.depressedDiscr_three`, `TauCeti.depressedDiscr_four`,
  `TauCeti.prime_weierstrassDiscr`: explicit low-degree discriminants and Weierstrass primality.

## References

* S. Lang, *Algebra*, Revised Third Edition, GTM 211, Springer (2002), Chapter IV, §8.
* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.B.
-/

public section

open Finset MvPolynomial Polynomial

/-! ### Weighted homogeneity of discriminants -/

namespace Polynomial

/-- The discriminant of `Polynomial.freeMonic R m` is weighted homogeneous of weight `m * (m - 1)`
when the variable `X i` (the coefficient in degree `i`) is given weight `m - i`. -/
theorem isWeightedHomogeneous_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    (freeMonic R m).discr.IsWeightedHomogeneous (fun i : Fin m ↦ m - (i : ℕ)) (m * (m - 1)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (freeMonic R m).discr 0]
    exact isWeightedHomogeneous_zero R _ _
  let w : Fin m → ℕ := fun i ↦ m - (i : ℕ)
  let g : Fin m → (MvPolynomial (Fin m) R)[X] :=
    fun i ↦ Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i
  let F : (MvPolynomial (Fin m) R)[X][X] := (freeMonic R m).map Polynomial.C
  have hFdeg : F.natDegree = m := by
    rw [((monic_freeMonic R m).natDegree_map Polynomial.C), natDegree_freeMonic]
  have hscale : (freeMonic R m).map (MvPolynomial.aeval g).toRingHom =
      F.scaleRoots Polynomial.X := by
    refine AddMonoidAlgebra.ext (DFunLike.ext _ _ fun k ↦ ?_)
    rw [Polynomial.coeff_map, coeff_scaleRoots, Polynomial.coeff_map, hFdeg, coeff_freeMonic]
    split_ifs with hk hkm
    · simp [g, w]
    · rw [hkm]
      simp
    · simp
  have hdiscr := congrArg Polynomial.discr hscale
  rw [(monic_freeMonic R m).discr_map, discr_scaleRoots, hFdeg,
    (monic_freeMonic R m).discr_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    mul_comm] at hdiscr
  have hcoeff := congrArg (fun p : (MvPolynomial (Fin m) R)[X] ↦ p.coeff (m * (m - 1))) hdiscr
  rw [MvPolynomial.coeff_aeval_C_X_mul_X_pow, coeff_C_mul_X_pow, ite_eq_left rfl] at hcoeff
  rw [← hcoeff]
  exact weightedHomogeneousComponent_mem w (freeMonic R m).discr (m * (m - 1))

/-- **Weighted homogeneity of the discriminant.** If `f` is a monic polynomial over
`MvPolynomial σ R` whose coefficient in degree `k < f.natDegree` is weighted homogeneous of weight
`(f.natDegree - k) • u` in an additive commutative monoid `M`, then `f.discr` is weighted
homogeneous of weight `(f.natDegree * (f.natDegree - 1)) • u`. -/
theorem Monic.isWeightedHomogeneous_discr {R σ M : Type*} [CommRing R] [AddCommMonoid M]
    (w : σ → M) (u : M) {f : (MvPolynomial σ R)[X]} (hf : f.Monic)
    (hc : ∀ k < f.natDegree, (f.coeff k).IsWeightedHomogeneous w ((f.natDegree - k) • u)) :
    f.discr.IsWeightedHomogeneous w ((f.natDegree * (f.natDegree - 1)) • u) := by
  let n := f.natDegree
  let φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial σ R :=
    MvPolynomial.aeval fun i : Fin n ↦ f.coeff i
  have hmap : (freeMonic R n).map φ.toRingHom = f := by
    refine AddMonoidAlgebra.ext (DFunLike.ext _ _ fun k ↦ ?_)
    rw [Polynomial.coeff_map, coeff_freeMonic]
    split_ifs with hk hkn
    · simp [φ]
    · rw [hkn, map_one]
      exact hf.leadingCoeff.symm
    · simp only [AlgHom.toRingHom_eq_coe, map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hdiscr : f.discr = φ (freeMonic R n).discr := by
    rw [← hmap, (monic_freeMonic R n).discr_map]
    rfl
  rw [hdiscr]
  have hfree := isWeightedHomogeneous_discr_freeMonic R n
  -- Transfer weighted homogeneity monomial by monomial along the universal evaluation `φ`.
  refine IsWeightedHomogeneous.induction_on
    (motive := fun p _ ↦ (φ p).IsWeightedHomogeneous w ((n * (n - 1)) • u))
    (by simp [isWeightedHomogeneous_zero])
    (fun p q _ _ ihp ihq ↦ by rw [map_add]; exact ihp.add ihq)
    (fun d r hr ↦ ?_) hfree
  dsimp only [φ]
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ r
  have hprod : (∏ i ∈ d.support, f.coeff i ^ d i).IsWeightedHomogeneous w
      (∑ i ∈ d.support, d i • ((n - (i : ℕ)) • u)) :=
    IsWeightedHomogeneous.prod d.support (fun i ↦ f.coeff i ^ d i)
      (fun i ↦ d i • ((n - (i : ℕ)) • u)) fun i _ ↦ (hc i i.2).pow (d i)
  have hsum : ∑ i ∈ d.support, d i • ((n - (i : ℕ)) • u) = (n * (n - 1)) • u := by
    simp_rw [← mul_smul, ← Finset.sum_smul]
    rw [← hr, Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul]
  rwa [hsum] at hprod

/-! ### Primality of the generic monic discriminant -/

section FreeMonicPrime

/-- The sign-twisting `R`-algebra involution `X j ↦ (-1) ^ (j + 1) * X j` on
`MvPolynomial (Fin m) R`. -/
private noncomputable def signTwistAlgEquiv (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun j : Fin m ↦
      (-1 : MvPolynomial (Fin m) R) ^ ((j : ℕ) + 1) * MvPolynomial.X j)
    (MvPolynomial.aeval fun j : Fin m ↦
      (-1 : MvPolynomial (Fin m) R) ^ ((j : ℕ) + 1) * MvPolynomial.X j)
    (by
      refine MvPolynomial.algHom_ext fun j ↦ ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X, map_mul, map_pow,
        map_neg, map_one]
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp)
    (by
      refine MvPolynomial.algHom_ext fun j ↦ ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X, map_mul, map_pow,
        map_neg, map_one]
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp)

/-- Vieta's `R`-algebra isomorphism from the universal coefficient ring `MvPolynomial (Fin m) R`
onto the symmetric polynomials in `m` root variables, sending `X i` (the degree-`i` coefficient)
to `(-1) ^ (m - i) * esymm (Fin m) R (m - i)`. -/
private noncomputable def vietaAlgEquiv (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R ≃ₐ[R] symmetricSubalgebra (Fin m) R :=
  (renameEquiv R Fin.revPerm).trans
    ((signTwistAlgEquiv R m).trans (esymmAlgEquiv (Fin m) R (Fintype.card_fin m)))

/-- The injective `R`-algebra homomorphism embedding `MvPolynomial (Fin m) R` into the root-variable
ring `MvPolynomial (Fin m) R` with image `symmetricSubalgebra (Fin m) R`. -/
private noncomputable def vietaAlgHom (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  (symmetricSubalgebra (Fin m) R).val.comp (vietaAlgEquiv R m).toAlgHom

private theorem vietaAlgHom_injective (R : Type*) [CommRing R] (m : ℕ) :
    Function.Injective (vietaAlgHom R m) :=
  Subtype.val_injective.comp (vietaAlgEquiv R m).injective

private theorem isSymmetric_vietaAlgHom {R : Type*} [CommRing R] {m : ℕ}
    (p : MvPolynomial (Fin m) R) : (vietaAlgHom R m p).IsSymmetric :=
  (vietaAlgEquiv R m p).2

private theorem vietaAlgHom_X {R : Type*} [CommRing R] {m : ℕ} (i : Fin m) :
    vietaAlgHom R m (MvPolynomial.X i) =
      (-1) ^ (m - (i : ℕ)) * esymm (Fin m) R (m - (i : ℕ)) := by
  have hrev : (i.rev : ℕ) + 1 = m - (i : ℕ) := by
    rw [Fin.val_rev]
    have := i.2
    omega
  simp only [vietaAlgHom, vietaAlgEquiv, signTwistAlgEquiv, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, Fin.revPerm_apply,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_X, esymmAlgEquiv_apply, esymmAlgHom, map_mul,
    map_pow, map_neg, map_one, hrev]
  rfl

/-- Mapping `Polynomial.freeMonic R m` along `vietaAlgHom` factors it into linear root factors
`∏ j, (X - C (MvPolynomial.X j))`. -/
private theorem map_freeMonic_vietaAlgHom (R : Type*) [CommRing R] (m : ℕ) :
    (freeMonic R m).map (vietaAlgHom R m).toRingHom =
      ∏ j : Fin m, (Polynomial.X - Polynomial.C (MvPolynomial.X j)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let P : (MvPolynomial (Fin m) R)[X] :=
    ∏ j : Fin m, (Polynomial.X - Polynomial.C (MvPolynomial.X j))
  have hmon : P.Monic := monic_prod_of_monic univ _ fun j _ ↦ monic_X_sub_C _
  have hdeg : P.natDegree = m := by
    simp [P, natDegree_finsetProd_X_sub_C_eq_card]
  have hlead : P.coeff m = 1 :=
    (congrArg P.coeff hdeg.symm).trans hmon.leadingCoeff
  refine AddMonoidAlgebra.ext (DFunLike.ext _ _ fun k ↦ ?_)
  rw [Polynomial.coeff_map, coeff_freeMonic]
  split_ifs with hk hkm
  · rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, vietaAlgHom_X]
    have hv := MvPolynomial.aeval_esymm_eq_coeff_prod_X_sub_C
      (R := R) (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R) (k := m - k)
      (by simp)
    rw [MvPolynomial.aeval_X_left, AlgHom.id_apply, Fintype.card_fin, Nat.sub_sub_self hk.le] at hv
    rw [hv, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [hkm, hlead, map_one]
  · simp only [AlgHom.toRingHom_eq_coe, map_zero]
    exact (coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by omega))).symm

/-- The Vandermonde product `∏_{i < j} (X i - X j)` in `MvPolynomial (Fin m) R`. -/
private noncomputable def vandermonde (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R :=
  ∏ i : Fin m, ∏ j ∈ Ioi i, (MvPolynomial.X i - MvPolynomial.X j)

private theorem vietaAlgHom_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    vietaAlgHom R m (freeMonic R m).discr = vandermonde R m ^ 2 := by
  have h := congrArg Polynomial.discr (map_freeMonic_vietaAlgHom R m)
  rw [(monic_freeMonic R m).discr_map, discr_prod_X_sub_C_eq_sq] at h
  exact h

private theorem rename_vandermonde {R : Type*} [CommRing R] {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    rename σ (vandermonde R m) = (Equiv.Perm.sign σ : ℤ) • vandermonde R m := by
  simp only [vandermonde, map_prod, map_sub, rename_X]
  have h := σ.prod_Ioi_comp_eq_sign_mul_prod
    (f := fun i j : Fin m ↦ (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) R))
    (fun i j ↦ by ring)
  rw [h, zsmul_eq_mul]

/-- When `(2 : R) = 0`, the discriminant of `Polynomial.freeMonic R m` is a square in
`MvPolynomial (Fin m) R`: the Vandermonde product is then invariant under every permutation of the
roots, hence descends to a polynomial in the coefficients whose square is the discriminant. -/
theorem isSquare_discr_freeMonic_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    (m : ℕ) : IsSquare (freeMonic R m).discr := by
  have h2' : (2 : MvPolynomial (Fin m) R) = 0 := by
    rw [← map_ofNat MvPolynomial.C 2, h2, map_zero]
  have hneg : (-1 : MvPolynomial (Fin m) R) = 1 := by
    calc (-1 : MvPolynomial (Fin m) R)
      _ = 1 - 2 := by ring
      _ = 1 := by rw [h2', sub_zero]
  have hsymm : (vandermonde R m).IsSymmetric := by
    intro σ
    rw [rename_vandermonde]
    rcases Int.units_eq_one_or σ.sign with hs | hs
    · simp [hs]
    · simp only [hs, Units.val_neg, Units.val_one, neg_smul, one_smul]
      rw [neg_eq_neg_one_mul, hneg, one_mul]
  let s : MvPolynomial (Fin m) R := (vietaAlgEquiv R m).symm ⟨vandermonde R m, hsymm⟩
  have hs : vietaAlgHom R m s = vandermonde R m := by
    simp [s, vietaAlgHom]
  refine ⟨s, (vietaAlgHom_injective R m) ?_⟩
  rw [vietaAlgHom_discr_freeMonic, map_mul, ← sq, hs]

private theorem coeff_single_X_sub_X_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ}
    {i j : Fin m} (hij : i ≠ j) (k : Fin m) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) R).coeff
      (Finsupp.single k 1) ≠ 0 ↔ k = i ∨ k = j := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_X]
  simp only [Finsupp.single_eq_single_iff, one_ne_zero, and_true, false_and, or_false]
  rcases eq_or_ne k i with rfl | hki
  · simp [hij, hij.symm]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [hki, hki.symm]
    · simp [hki, hki.symm, hkj, hkj.symm]

private theorem irreducible_X_sub_X {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    {i j : Fin m} (hij : i ≠ j) :
    Irreducible (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) R) := by
  have hle : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) R).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans ?_
    simp [totalDegree_X]
  have hge : 1 ≤ (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) R).totalDegree := by
    have hc : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) R).coeff
        (Finsupp.single i 1) ≠ 0 :=
      (coeff_single_X_sub_X_ne_zero hij i).mpr (Or.inl rfl)
    simpa using le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  refine irreducible_of_totalDegree_eq_one (le_antisymm hle hge) fun r hr ↦ ?_
  have hri := hr (Finsupp.single i 1)
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_X, ite_eq_left rfl,
    ite_eq_right (by simp [Finsupp.single_eq_single_iff, hij.symm]), sub_zero] at hri
  exact isUnit_of_dvd_one hri

private theorem eq_of_associated_X_sub_X {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    {i j i' j' : Fin m} (hij : i < j) (hij' : i' < j')
    (hass : Associated (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) R)
      (MvPolynomial.X i' - MvPolynomial.X j')) :
    i = i' ∧ j = j' := by
  obtain ⟨u, hu⟩ := hass
  obtain ⟨r, hr, huC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hiff : ∀ k : Fin m, (k = i ∨ k = j) ↔ (k = i' ∨ k = j') := fun k ↦ by
    rw [← coeff_single_X_sub_X_ne_zero (R := R) hij.ne,
      ← coeff_single_X_sub_X_ne_zero (R := R) hij'.ne, ← hu, huC, mul_comm,
      MvPolynomial.coeff_C_mul]
    simp [hr.ne_zero]
  have hi := (hiff i).mp (Or.inl rfl)
  have hj := (hiff j).mp (Or.inr rfl)
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

/-- Any two ordered pairs `(i₀, j₀)` and `(i, j)` in `Fin m` with `i₀ ≠ j₀` and `i ≠ j` are
related by a permutation of `Fin m`. -/
private theorem exists_perm_map_pair {m : ℕ} {i₀ j₀ i j : Fin m} (h₀ : i₀ ≠ j₀) (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin m), σ i₀ = i ∧ σ j₀ = j := by
  let τ₁ : Equiv.Perm (Fin m) := Equiv.swap i₀ i
  have hne : τ₁ j₀ ≠ i := fun heq ↦
    h₀ (τ₁.injective ((Equiv.swap_apply_left i₀ i).trans heq.symm))
  refine ⟨τ₁.trans (Equiv.swap (τ₁ j₀) j), ?_, by simp⟩
  simp [τ₁, Equiv.swap_apply_of_ne_of_ne hne.symm h]

/-- If a symmetric polynomial over a UFD is divisible by one root difference `X i₀ - X j₀`,
then it is divisible by the entire Vandermonde product `∏_{i < j} (X i - X j)`. -/
private theorem vandermonde_dvd_of_isSymmetric {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {m : ℕ}
    {p : MvPolynomial (Fin m) R} (hp : p.IsSymmetric) {i₀ j₀ : Fin m} (h₀ : i₀ < j₀)
    (hdvd₀ : MvPolynomial.X i₀ - MvPolynomial.X j₀ ∣ p) :
    vandermonde R m ∣ p := by
  let S : Finset (Σ _ : Fin m, Fin m) := univ.sigma fun i : Fin m ↦ Ioi i
  have hvand : vandermonde R m = ∏ x ∈ S, (MvPolynomial.X x.1 - MvPolynomial.X x.2) := by
    rw [vandermonde, Finset.prod_sigma']
  rw [hvand]
  refine Finset.prod_dvd_of_isRelPrime (fun x hx y hy hxy ↦ ?_) (fun x hx ↦ ?_)
  · have hx' : x.1 < x.2 := mem_Ioi.mp (mem_sigma.mp hx).2
    have hy' : y.1 < y.2 := mem_Ioi.mp (mem_sigma.mp hy).2
    dsimp only [Function.onFun]
    rw [(irreducible_X_sub_X hx'.ne).isRelPrime_iff_not_dvd]
    intro hdvd
    have hass := (irreducible_X_sub_X hx'.ne).associated_of_dvd (irreducible_X_sub_X hy'.ne) hdvd
    obtain ⟨h1, h2⟩ := eq_of_associated_X_sub_X hx' hy' hass
    exact hxy (Sigma.ext h1 (heq_of_eq h2))
  · have hx' : x.1 < x.2 := mem_Ioi.mp (mem_sigma.mp hx).2
    obtain ⟨σ, hσ1, hσ2⟩ := exists_perm_map_pair h₀.ne hx'.ne
    have hmap := _root_.map_dvd (rename (R := R) σ) hdvd₀
    simpa [hp σ, hσ1, hσ2] using hmap

private theorem vandermonde_ne_zero {R : Type*} [CommRing R] [IsDomain R] (m : ℕ) :
    vandermonde R m ≠ 0 := by
  rw [vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
  exact (irreducible_X_sub_X (mem_Ioi.mp hj).ne).ne_zero

/-- **Primality of the generic monic discriminant.** Over any unique factorization domain `R` in
which `2 ≠ 0`, the discriminant of `Polynomial.freeMonic R m` is prime in `MvPolynomial (Fin m) R`
for every `m ≥ 2`. -/
theorem prime_discr_freeMonic {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ < i₁ := Fin.mk_lt_mk.mpr (by omega)
  have hdvd_vand : MvPolynomial.X i₀ - MvPolynomial.X i₁ ∣ vandermonde R m := by
    rw [vandermonde]
    exact dvd_trans
      (Finset.dvd_prod_of_mem (fun j ↦ MvPolynomial.X i₀ - MvPolynomial.X j) (mem_Ioi.mpr h01))
      (Finset.dvd_prod_of_mem
        (fun i ↦ ∏ j ∈ Ioi i, (MvPolynomial.X i - MvPolynomial.X j)) (mem_univ i₀))
  refine ⟨fun hu ↦ ?_, fun f g hfg ↦ ?_⟩
  · have hu' : IsUnit (vandermonde R m ^ 2) := by
      rw [← vietaAlgHom_discr_freeMonic]
      exact hu.map (vietaAlgHom R m)
    have hv_unit : IsUnit (vandermonde R m) := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hu'
    exact (irreducible_X_sub_X h01.ne).not_isUnit (isUnit_of_dvd_unit hdvd_vand hv_unit)
  · have hprod : vietaAlgHom R m f * vietaAlgHom R m g = vandermonde R m ^ 2 := by
      rw [← map_mul, ← hfg, vietaAlgHom_discr_freeMonic]
    have hp01 : Prime (MvPolynomial.X i₀ - MvPolynomial.X i₁ : MvPolynomial (Fin m) R) :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_X_sub_X h01.ne)
    have hdvd_fg : MvPolynomial.X i₀ - MvPolynomial.X i₁ ∣
        vietaAlgHom R m f * vietaAlgHom R m g := by
      rw [hprod, sq]
      exact dvd_mul_of_dvd_left hdvd_vand _
    -- Symmetric case split on which factor of `δ ^ 2` is divisible by `X 0 - X 1`.
    suffices ∀ a b : MvPolynomial (Fin m) R,
        vietaAlgHom R m a * vietaAlgHom R m b = vandermonde R m ^ 2 →
        MvPolynomial.X i₀ - MvPolynomial.X i₁ ∣ vietaAlgHom R m a → IsUnit a ∨ IsUnit b by
      rcases hp01.dvd_or_dvd hdvd_fg with hfa | hgb
      · exact this f g hprod hfa
      · exact (this g f (by rwa [mul_comm]) hgb).symm
    intro a b hab ha
    by_cases hb : MvPolynomial.X i₀ - MvPolynomial.X i₁ ∣ vietaAlgHom R m b
    · -- If `X 0 - X 1` divides both symmetric factors, `δ` divides both, so `vietaAlgHom a` is a
      -- unit multiple of `δ`; swapping `0` and `1` then forces `2 = 0`.
      obtain ⟨q₁, hq₁⟩ := vandermonde_dvd_of_isSymmetric (isSymmetric_vietaAlgHom a) h01 ha
      obtain ⟨q₂, hq₂⟩ := vandermonde_dvd_of_isSymmetric (isSymmetric_vietaAlgHom b) h01 hb
      have hmul : vandermonde R m ^ 2 * (q₁ * q₂) = vandermonde R m ^ 2 * 1 := by
        calc vandermonde R m ^ 2 * (q₁ * q₂)
          _ = (vandermonde R m * q₁) * (vandermonde R m * q₂) := by ring
          _ = vietaAlgHom R m a * vietaAlgHom R m b := by rw [← hq₁, ← hq₂]
          _ = vandermonde R m ^ 2 * 1 := by rw [hab, mul_one]
      have hq12 : q₁ * q₂ = 1 :=
        mul_left_cancel₀ (pow_ne_zero 2 (vandermonde_ne_zero m)) hmul
      have hq₁_unit : IsUnit q₁ := IsUnit.of_mul_eq_one q₂ hq12
      obtain ⟨r, hr, hq₁C⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hq₁_unit
      have hswap := isSymmetric_vietaAlgHom a (Equiv.swap i₀ i₁)
      rw [hq₁, hq₁C, map_mul, rename_vandermonde, Equiv.Perm.sign_swap h01.ne, rename_C] at hswap
      have hzero : MvPolynomial.C (2 : R) * (vandermonde R m * MvPolynomial.C r) = 0 := by
        have hswap' : -(vandermonde R m * MvPolynomial.C r) =
            vandermonde R m * MvPolynomial.C r := by
          simpa using hswap
        calc MvPolynomial.C (2 : R) * (vandermonde R m * MvPolynomial.C r)
          _ = (1 + 1) * (vandermonde R m * MvPolynomial.C r) := by
              rw [← one_add_one_eq_two, map_add, map_one]
          _ = -(vandermonde R m * MvPolynomial.C r) +
                vandermonde R m * MvPolynomial.C r := by
              rw [add_mul, one_mul]
              nth_rw 1 [← hswap']
          _ = 0 := neg_add_cancel _
      have hne0 : vandermonde R m * MvPolynomial.C r ≠ 0 :=
        mul_ne_zero (vandermonde_ne_zero m) (by simpa using hr.ne_zero)
      exact absurd (MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hne0)) h2
    · -- Otherwise no root difference divides `vietaAlgHom b`, so `vietaAlgHom b` has no
      -- irreducible factors in `δ ^ 2` and must be a constant unit; injectivity gives `IsUnit b`.
      right
      have hb0 : vietaAlgHom R m b ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hab
        exact pow_ne_zero 2 (vandermonde_ne_zero m) hab.symm
      have hb_unit : IsUnit (vietaAlgHom R m b) := by
        by_contra hnb
        obtain ⟨p, hp_irr, hpb⟩ := WfDvdMonoid.exists_irreducible_factor hnb hb0
        have hp_prime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr
        have hp_vand : p ∣ vandermonde R m :=
          hp_prime.dvd_of_dvd_pow (dvd_trans hpb ⟨vietaAlgHom R m a, by rw [mul_comm, hab]⟩)
        rw [vandermonde] at hp_vand
        obtain ⟨i, -, hpi⟩ := hp_prime.exists_mem_finset_dvd hp_vand
        obtain ⟨j, hj, hpij⟩ := hp_prime.exists_mem_finset_dvd hpi
        have hij : i < j := mem_Ioi.mp hj
        have hass := hp_irr.associated_of_dvd (irreducible_X_sub_X hij.ne) hpij
        have hdvd_ij : MvPolynomial.X i - MvPolynomial.X j ∣ vietaAlgHom R m b :=
          hass.symm.dvd.trans hpb
        obtain ⟨σ, hσ1, hσ2⟩ := exists_perm_map_pair hij.ne h01.ne
        have hmap := _root_.map_dvd (rename (R := R) σ) hdvd_ij
        rw [isSymmetric_vietaAlgHom b σ] at hmap
        exact hb (by simpa [hσ1, hσ2] using hmap)
      obtain ⟨r, hr, hbC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hb_unit
      have hbeq : b = MvPolynomial.C r := by
        apply vietaAlgHom_injective R m
        rw [hbC, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rw [hbeq]
      exact hr.map MvPolynomial.C

/-- Over a unique factorization domain `R` and for `m ≥ 2`, the discriminant of
`Polynomial.freeMonic R m` is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_discr_freeMonic_iff {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr ↔ (2 : R) ≠ 0 :=
  ⟨fun hp h2 ↦ (isSquare_discr_freeMonic_of_two_eq_zero h2 m).not_prime hp,
    fun h2 ↦ prime_discr_freeMonic h2 hm⟩

end FreeMonicPrime

end Polynomial

/-! ### The generic depressed polynomial and its discriminant -/

namespace TauCeti

section GenericDepressed

/-- The **generic monic depressed polynomial** of degree `m` over `R`:
`X ^ m + a₂ X ^ (m - 2) + ⋯ + aₘ`, viewed in `(MvPolynomial (Fin (m - 1)) R)[X]` with `X i`
representing `a_{i + 2}`. For `m = 0` this is `1`, and for `m = 1` it is `X`. -/
noncomputable def genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (MvPolynomial (Fin (m - 1)) R)[X] :=
  Polynomial.X ^ m +
    ∑ i : Fin (m - 1), Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (m - ((i : ℕ) + 2))

/-- Explicit sum formula for `TauCeti.genericDepressed R m`. -/
theorem genericDepressed_def (R : Type*) [CommSemiring R] (m : ℕ) :
    genericDepressed R m =
      Polynomial.X ^ m +
        ∑ i : Fin (m - 1),
          Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (m - ((i : ℕ) + 2)) :=
  (rfl)

/-- The coefficients of `TauCeti.genericDepressed R m`: in degree `k < m - 1` the coefficient is
`X ⟨m - 2 - k, _⟩`, in degree `m - 1` (when `m ≥ 1`) it vanishes, in degree `m` it is `1`, and
above `m` it vanishes. -/
theorem coeff_genericDepressed (R : Type*) [CommSemiring R] (m k : ℕ) :
    (genericDepressed R m).coeff k =
      if hk : k < m - 1 then MvPolynomial.X ⟨m - 2 - k, by omega⟩
      else if k = m then 1 else 0 := by
  simp only [genericDepressed_def, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    finsetSum_coeff, Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k < m - 1
  · have hkm : k ≠ m := by omega
    rw [ite_eq_right hkm, zero_add, dite_eq_left hk]
    rw [Finset.sum_eq_single (⟨m - 2 - k, by omega⟩ : Fin (m - 1))]
    · dsimp only
      rw [ite_eq_left (by omega)]
    · intro j _ hj
      rw [ite_eq_right]
      intro hjk
      apply hj
      ext
      dsimp only
      have := j.2
      omega
    · intro h
      exact absurd (mem_univ _) h
  · rw [dite_eq_right hk, Finset.sum_eq_zero fun j _ ↦ ?_, add_zero]
    have := j.2
    exact ite_eq_right (by omega)

/-- Mapping the base ring commutes with forming `TauCeti.genericDepressed`. -/
@[simp]
theorem map_genericDepressed {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (m : ℕ) :
    (genericDepressed R m).map (MvPolynomial.map φ) = genericDepressed S m := by
  simp [genericDepressed_def, Polynomial.map_sum]

/-- `TauCeti.genericDepressed R m` is monic for every `m`. -/
@[simp]
theorem monic_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one m ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_left rfl]

/-- Over a nontrivial coefficient semiring, `TauCeti.genericDepressed R m` has degree `m`. -/
theorem degree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).degree = m := by
  refine degree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro k hk
    have hmk : m < k := WithBot.coe_lt_coe.mp hk
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_left rfl]
    exact one_ne_zero

/-- Over a nontrivial coefficient semiring, `TauCeti.genericDepressed R m` has `natDegree` `m`. -/
@[simp]
theorem natDegree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).natDegree = m :=
  natDegree_eq_of_degree_eq_some (degree_genericDepressed R m)

/-- The subleading coefficient of `TauCeti.genericDepressed R m` vanishes for every `m`. -/
@[simp]
theorem nextCoeff_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).nextCoeff = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  rcases m with _ | m
  · rw [nextCoeff, ite_eq_left (natDegree_genericDepressed R 0)]
  · have hpos : 0 < (genericDepressed R (m + 1)).natDegree := by
      rw [natDegree_genericDepressed]
      omega
    rw [nextCoeff_of_natDegree_pos hpos]
    have hdeg := natDegree_genericDepressed R (m + 1)
    have hsub : (genericDepressed R (m + 1)).natDegree - 1 = m := by omega
    rw [hsub, coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]

/-- For `m = 0`, `TauCeti.genericDepressed R 0` is the constant polynomial `1`. -/
@[simp]
theorem genericDepressed_zero (R : Type*) [CommSemiring R] :
    genericDepressed R 0 = 1 := by
  simp [genericDepressed_def]

/-- For `m = 1`, `TauCeti.genericDepressed R 1` is `X`. -/
@[simp]
theorem genericDepressed_one (R : Type*) [CommSemiring R] :
    genericDepressed R 1 = Polynomial.X := by
  simp [genericDepressed_def]

/-- For `m = 2`, `TauCeti.genericDepressed R 2` is `X ^ 2 + C (X 0)`. -/
theorem genericDepressed_two (R : Type*) [CommSemiring R] :
    genericDepressed R 2 = Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 0) := by
  simp [genericDepressed_def]

/-- For `m = 3`, `TauCeti.genericDepressed R 3` is `X ^ 3 + C (X 0) * X + C (X 1)`. -/
theorem genericDepressed_three (R : Type*) [CommSemiring R] :
    genericDepressed R 3 =
      Polynomial.X ^ 3 + Polynomial.C (MvPolynomial.X 0) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 1) := by
  rw [genericDepressed_def, Fin.sum_univ_two]
  simp [add_assoc]

/-- For `m = 4`, `TauCeti.genericDepressed R 4` is
`X ^ 4 + C (X 0) * X ^ 2 + C (X 1) * X + C (X 2)`. -/
theorem genericDepressed_four (R : Type*) [CommSemiring R] :
    genericDepressed R 4 =
      Polynomial.X ^ 4 + Polynomial.C (MvPolynomial.X 0) * Polynomial.X ^ 2 +
        Polynomial.C (MvPolynomial.X 1) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 2) := by
  rw [genericDepressed_def, Fin.sum_univ_three]
  simp [add_assoc]

end GenericDepressed

/-! ### Weights and weighted homogeneity of the generic depressed discriminant -/

section DepressedDiscr

/-- The weight assignment `i ↦ i + 2` on `Fin (m - 1)`, giving the coefficient `aₖ` of
`X ^ (m - k)` in `TauCeti.genericDepressed` weight `k`. -/
def depressedWeight (m : ℕ) : Fin (m - 1) → ℤ :=
  fun i ↦ (i : ℤ) + 2

/-- Explicit formula for `TauCeti.depressedWeight m`. -/
theorem depressedWeight_def (m : ℕ) :
    depressedWeight m = fun i : Fin (m - 1) ↦ (i : ℤ) + 2 :=
  (rfl)

/-- Evaluation of `TauCeti.depressedWeight m` at `i : Fin (m - 1)`. -/
@[simp]
theorem depressedWeight_apply (m : ℕ) (i : Fin (m - 1)) :
    depressedWeight m i = (i : ℤ) + 2 := by
  rw [depressedWeight_def]

/-- The discriminant of `TauCeti.genericDepressed R m`, as an element of
`MvPolynomial (Fin (m - 1)) R`. -/
noncomputable def depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin (m - 1)) R :=
  (genericDepressed R m).discr

/-- Unfolding lemma for `TauCeti.depressedDiscr R m` as `(genericDepressed R m).discr`. -/
theorem depressedDiscr_def (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m = (genericDepressed R m).discr :=
  (rfl)

/-- Mapping the base ring commutes with forming `TauCeti.depressedDiscr`. -/
@[simp]
theorem map_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (depressedDiscr R m) = depressedDiscr S m := by
  rw [depressedDiscr_def, ← (monic_genericDepressed R m).discr_map (MvPolynomial.map φ),
    map_genericDepressed, depressedDiscr_def]

/-- `TauCeti.depressedDiscr R m` is weighted homogeneous of natural-number weight `m * (m - 1)`
with respect to `i ↦ i + 2`. -/
theorem isWeightedHomogeneous_nat_depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    (depressedDiscr R m).IsWeightedHomogeneous (fun i : Fin (m - 1) ↦ (i : ℕ) + 2)
      (m * (m - 1)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (depressedDiscr R m) 0]
    exact isWeightedHomogeneous_zero R _ _
  have h := (monic_genericDepressed R m).isWeightedHomogeneous_discr
    (fun i : Fin (m - 1) ↦ (i : ℕ) + 2) 1 fun k hk ↦ ?_
  · simpa [depressedDiscr_def, natDegree_genericDepressed] using h
  · rw [natDegree_genericDepressed] at hk ⊢
    rw [coeff_genericDepressed, smul_eq_mul, mul_one]
    split_ifs with hk' hkm
    · convert isWeightedHomogeneous_X R (fun i : Fin (m - 1) ↦ (i : ℕ) + 2)
        ⟨m - 2 - k, by omega⟩ using 1
      dsimp only
      omega
    · omega
    · exact isWeightedHomogeneous_zero R _ _

/-- `TauCeti.depressedDiscr R m` is weighted homogeneous of integer weight `m * (m - 1)` for
`TauCeti.depressedWeight m`. -/
theorem isWeightedHomogeneous_depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    (depressedDiscr R m).IsWeightedHomogeneous (depressedWeight m) ((m : ℤ) * (m - 1)) := by
  intro d hd
  have hnat := isWeightedHomogeneous_nat_depressedDiscr R m hd
  have hw : Finsupp.weight (depressedWeight m) d =
      ((Finsupp.weight (fun i : Fin (m - 1) ↦ (i : ℕ) + 2) d : ℕ) : ℤ) := by
    simp [Finsupp.weight_apply, Finsupp.sum, depressedWeight_apply, Nat.cast_sum]
  rw [hw, hnat]
  rcases m with _ | m
  · simp
  · simp

/-- `TauCeti.depressedDiscr R m` belongs to the submodule of weighted homogeneous polynomials of
weight `m * (m - 1)` with respect to `TauCeti.depressedWeight m`. -/
theorem depressedDiscr_mem (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m ∈
      weightedHomogeneousSubmodule R (depressedWeight m) ((m : ℤ) * (m - 1)) :=
  isWeightedHomogeneous_depressedDiscr R m

end DepressedDiscr

/-! ### Tschirnhaus equivalence between generic monic and depressed discriminants -/

section Tschirnhaus

/-- For a polynomial `f` of `natDegree` `m ≥ 1`, the `(m - 1)`-st coefficient of `taylor r f` is
`f.coeff (m - 1) + m * f.coeff m * r`. -/
private theorem coeff_taylor_sub_one {S : Type*} [CommRing S] (f : S[X]) (r : S) {m : ℕ}
    (hdeg : f.natDegree = m) (hm : 1 ≤ m) :
    (taylor r f).coeff (m - 1) = f.coeff (m - 1) + (m : S) * f.coeff m * r := by
  have hlt : (hasseDeriv (m - 1) f).natDegree < 2 := by
    have hle := natDegree_hasseDeriv_le f (m - 1)
    omega
  rw [taylor_coeff, eval_eq_sum_range' hlt, Finset.sum_range_succ, Finset.sum_range_one,
    hasseDeriv_coeff, hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul,
    pow_zero, mul_one, pow_one]
  have hm_eq : m = 1 + (m - 1) := by omega
  have hchoose : m.choose (m - 1) = m :=
    (Nat.choose_symm_of_eq_add hm_eq).symm.trans (Nat.choose_one_right m)
  rw [← hm_eq, hchoose]

/-- The `R`-algebra map from the universal monic coefficient ring `MvPolynomial (Fin m) R` to
`(MvPolynomial (Fin (m - 1)) R)[X]`, classifying the shifted generic depressed polynomial
`((genericDepressed R m).map C).comp (X + C X)`. -/
private noncomputable def tschirnhausToDepressed (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R →ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] :=
  MvPolynomial.aeval fun k : Fin m ↦
    (((genericDepressed R m).map Polynomial.C).comp
      (Polynomial.X + Polynomial.C Polynomial.X)).coeff k

/-- Mapping `Polynomial.freeMonic R m` along `tschirnhausToDepressed` produces the generic
depressed polynomial translated by the indeterminate `Polynomial.X`. -/
private theorem map_freeMonic_tschirnhausToDepressed (R : Type*) [CommRing R] (m : ℕ) :
    (freeMonic R m).map (tschirnhausToDepressed R m).toRingHom =
      ((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let Q : (MvPolynomial (Fin (m - 1)) R)[X][X] :=
    ((genericDepressed R m).map Polynomial.C).comp (Polynomial.X + Polynomial.C Polynomial.X)
  have hQ_eq : Q = taylor Polynomial.X ((genericDepressed R m).map Polynomial.C) := by
    rw [taylor_apply]
  have hQmon : Q.Monic := by
    rw [hQ_eq]
    have hmon := (monic_genericDepressed R m).map
      (Polynomial.C : MvPolynomial (Fin (m - 1)) R →+* (MvPolynomial (Fin (m - 1)) R)[X])
    rw [Monic.def, leadingCoeff_taylor, hmon.leadingCoeff]
  have hQdeg : Q.natDegree = m := by
    rw [hQ_eq, natDegree_taylor, (monic_genericDepressed R m).natDegree_map,
      natDegree_genericDepressed]
  have hQlead : Q.coeff m = 1 :=
    (congrArg Q.coeff hQdeg.symm).trans hQmon.leadingCoeff
  refine AddMonoidAlgebra.ext (DFunLike.ext _ _ fun k ↦ ?_)
  rw [Polynomial.coeff_map, coeff_freeMonic]
  split_ifs with hk hkm
  · simp [tschirnhausToDepressed]
  · rw [hkm, hQlead, map_one]
  · simp only [AlgHom.toRingHom_eq_coe, map_zero]
    exact (coeff_eq_zero_of_natDegree_lt (hQdeg.trans_lt (by omega))).symm

/-- Auxiliary construction of `TauCeti.tschirnhausAlgEquiv` over a nontrivial base ring. -/
private noncomputable def tschirnhausAlgEquivOfNontrivial {R : Type*} [CommRing R] [Nontrivial R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] := by
  have hm1 : 1 ≤ m := by
    rcases m with _ | n
    · rw [Nat.cast_zero] at hmu
      exact absurd hmu not_isUnit_zero
    · omega
  let u : R := ↑hmu.unit⁻¹
  have hmu_cancel : (m : R) * u = 1 := by simp [u]
  let bary : MvPolynomial (Fin m) R := MvPolynomial.C u * MvPolynomial.X ⟨m - 1, by omega⟩
  let P₀ : (MvPolynomial (Fin m) R)[X] :=
    (freeMonic R m).comp (Polynomial.X - Polynomial.C bary)
  let baseAlgHom : MvPolynomial (Fin (m - 1)) R →ₐ[R] MvPolynomial (Fin m) R :=
    MvPolynomial.aeval fun i : Fin (m - 1) ↦ P₀.coeff (m - ((i : ℕ) + 2))
  let inv : (MvPolynomial (Fin (m - 1)) R)[X] →ₐ[R] MvPolynomial (Fin m) R :=
    Polynomial.aevalTower baseAlgHom bary
  let fwd : MvPolynomial (Fin m) R →ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] :=
    tschirnhausToDepressed R m
  -- First compute the subleading coefficient `m * X` of the forward-shifted depressed polynomial.
  have hfwd_bary : fwd bary = Polynomial.X := by
    let G : (MvPolynomial (Fin (m - 1)) R)[X][X] := (genericDepressed R m).map Polynomial.C
    have hGdeg : G.natDegree = m := by
      rw [(monic_genericDepressed R m).natDegree_map, natDegree_genericDepressed]
    have hGsub : G.coeff (m - 1) = 0 := by
      rw [Polynomial.coeff_map, coeff_genericDepressed, dite_eq_right (by omega),
        ite_eq_right (by omega), map_zero]
    have hGlead : G.coeff m = 1 := by
      rw [Polynomial.coeff_map, coeff_genericDepressed, dite_eq_right (by omega),
        ite_eq_left rfl, map_one]
    have htaylor_next : (taylor Polynomial.X G).coeff (m - 1) =
        (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
      rw [coeff_taylor_sub_one G Polynomial.X hGdeg hm1, hGsub, hGlead, zero_add, mul_one]
    have hX : fwd (MvPolynomial.X ⟨m - 1, by omega⟩) =
        (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
      simpa [fwd, tschirnhausToDepressed, G, ← taylor_apply] using htaylor_next
    have hum : u • (m : (MvPolynomial (Fin (m - 1)) R)[X]) = 1 := by
      rw [Algebra.smul_def, ← map_natCast (algebraMap R _), ← map_mul, mul_comm, hmu_cancel,
        map_one]
    calc fwd bary
      _ = u • fwd (MvPolynomial.X ⟨m - 1, by omega⟩) := by
          dsimp only [bary]
          rw [← MvPolynomial.smul_eq_C_mul, map_smul]
      _ = (u • (m : (MvPolynomial (Fin (m - 1)) R)[X])) * Polynomial.X := by
          rw [hX, smul_mul_assoc]
      _ = Polynomial.X := by
          rw [hum, one_mul]
  -- Next compute that `P₀` has vanishing subleading coefficient, so `P₀` is
  -- `(genericDepressed R m).map` along `baseAlgHom`.
  have hP₀_eq_taylor : P₀ = taylor (-bary) (freeMonic R m) := by
    simp [P₀, taylor_apply, sub_eq_add_neg]
  have hP₀_mon : P₀.Monic := by
    rw [hP₀_eq_taylor, Monic.def, leadingCoeff_taylor, (monic_freeMonic R m).leadingCoeff]
  have hP₀_deg : P₀.natDegree = m := by
    rw [hP₀_eq_taylor, natDegree_taylor, natDegree_freeMonic]
  have hP₀_lead : P₀.coeff m = 1 :=
    (congrArg P₀.coeff hP₀_deg.symm).trans hP₀_mon.leadingCoeff
  have hP₀_sublead : P₀.coeff (m - 1) = 0 := by
    have hflead : (freeMonic R m).coeff m = 1 := by
      rw [coeff_freeMonic, dite_eq_right (by omega), ite_eq_left rfl]
    rw [hP₀_eq_taylor, coeff_taylor_sub_one (freeMonic R m) (-bary) (natDegree_freeMonic R m) hm1,
      coeff_freeMonic, dite_eq_left (by omega), hflead, mul_one]
    calc MvPolynomial.X ⟨m - 1, by omega⟩ +
          (m : MvPolynomial (Fin m) R) * -(MvPolynomial.C u * MvPolynomial.X ⟨m - 1, by omega⟩)
      _ = (1 - MvPolynomial.C ((m : R) * u)) * MvPolynomial.X ⟨m - 1, by omega⟩ := by
          simp only [map_mul, map_natCast]
          ring
      _ = 0 := by simp [hmu_cancel]
  have hmap_dep : (genericDepressed R m).map baseAlgHom.toRingHom = P₀ := by
    refine AddMonoidAlgebra.ext (DFunLike.ext _ _ fun k ↦ ?_)
    rw [Polynomial.coeff_map, coeff_genericDepressed]
    split_ifs with hk hkm
    · have hk_eq : m - ((m - 2 - k) + 2) = k := by omega
      simp [baseAlgHom, hk_eq]
    · rw [hkm, hP₀_lead, map_one]
    · simp only [AlgHom.toRingHom_eq_coe, map_zero]
      rcases eq_or_ne k (m - 1) with rfl | hkne
      · exact hP₀_sublead.symm
      · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  refine AlgEquiv.ofAlgHom fwd inv ?_ ?_
  · -- Right inverse: `fwd ∘ inv = id` on `(MvPolynomial (Fin (m - 1)) R)[X]`.
    apply Polynomial.algHom_ext'
    · refine MvPolynomial.algHom_ext fun i ↦ ?_
      have hcomp : P₀.map fwd.toRingHom = (genericDepressed R m).map Polynomial.C := by
        dsimp only [P₀]
        rw [Polynomial.map_comp, map_freeMonic_tschirnhausToDepressed]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, hfwd_bary, comp_assoc]
        have hcancel : (Polynomial.X + Polynomial.C Polynomial.X :
              (MvPolynomial (Fin (m - 1)) R)[X][X]).comp
            (Polynomial.X - Polynomial.C Polynomial.X) = Polynomial.X := by
          simp
        rw [hcancel, comp_X]
      have hcoeff := congrArg (fun p : (MvPolynomial (Fin (m - 1)) R)[X][X] ↦
        p.coeff (m - ((i : ℕ) + 2))) hcomp
      rw [Polynomial.coeff_map, Polynomial.coeff_map, coeff_genericDepressed,
        dite_eq_left (by have := i.2; omega)] at hcoeff
      have hi_eq : (⟨m - 2 - (m - ((i : ℕ) + 2)), by have := i.2; omega⟩ : Fin (m - 1)) = i := by
        ext
        dsimp only
        have := i.2
        omega
      rw [hi_eq] at hcoeff
      simpa [inv, baseAlgHom, Polynomial.aevalTower_C] using hcoeff
    · simpa [inv] using hfwd_bary
  · -- Left inverse: `inv ∘ fwd = id` on `MvPolynomial (Fin m) R`.
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    have hcomp : ((freeMonic R m).map fwd.toRingHom).map inv.toRingHom = freeMonic R m := by
      rw [map_freeMonic_tschirnhausToDepressed, Polynomial.map_comp, Polynomial.map_map]
      have hbase : inv.toRingHom.comp Polynomial.C = baseAlgHom.toRingHom := by
        refine RingHom.ext fun x ↦ ?_
        simp [inv]
      have hX_inv : inv Polynomial.X = bary := by simp [inv]
      rw [hbase, hmap_dep]
      simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hX_inv, P₀, comp_assoc]
      have hcancel : (Polynomial.X - Polynomial.C bary).comp
          (Polynomial.X + Polynomial.C bary) = Polynomial.X := by
        simp
      rw [hcancel, comp_X]
    have hcoeff := congrArg (fun p : (MvPolynomial (Fin m) R)[X] ↦ p.coeff k) hcomp
    rw [Polynomial.map_map, Polynomial.coeff_map, coeff_freeMonic, dite_eq_left k.2] at hcoeff
    simpa [fwd] using hcoeff

private theorem tschirnhausAlgEquivOfNontrivial_apply {R : Type*} [CommRing R] [Nontrivial R]
    {m : ℕ} (hmu : IsUnit (m : R)) (x : MvPolynomial (Fin m) R) :
    tschirnhausAlgEquivOfNontrivial hmu x = tschirnhausToDepressed R m x :=
  rfl

/-- When `(m : R)` is invertible, centering `Polynomial.freeMonic R m` by `- m⁻¹ * X (m - 1)` and
recording the root barycenter `m⁻¹ * X (m - 1)` in `Polynomial.X` gives an `R`-algebra equivalence
`MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`. -/
noncomputable def tschirnhausAlgEquiv {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R)) :
    MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] := by
  classical
  exact if hR : Subsingleton R then
    { toFun := 0
      invFun := 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _
      map_mul' := fun _ _ ↦ Subsingleton.elim _ _
      map_add' := fun _ _ ↦ Subsingleton.elim _ _
      commutes' := fun _ ↦ Subsingleton.elim _ _ }
  else
    haveI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    tschirnhausAlgEquivOfNontrivial hmu

/-- Mapping `Polynomial.freeMonic R m` along `TauCeti.tschirnhausAlgEquiv` produces the generic
depressed polynomial translated by `Polynomial.X`. -/
theorem map_freeMonic_tschirnhausAlgEquiv {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (freeMonic R m).map (tschirnhausAlgEquiv hmu).toRingHom =
      ((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have halg : (tschirnhausAlgEquiv hmu).toAlgHom = tschirnhausToDepressed R m := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    rw [AlgEquiv.coe_toAlgHom, tschirnhausAlgEquiv,
      dite_eq_right (not_subsingleton_iff_nontrivial.mpr hR), tschirnhausAlgEquivOfNontrivial_apply]
  have hfun : (tschirnhausAlgEquiv hmu).toRingHom = (tschirnhausToDepressed R m).toRingHom :=
    congrArg AlgHom.toRingHom halg
  rw [hfun, map_freeMonic_tschirnhausToDepressed]

/-- `TauCeti.tschirnhausAlgEquiv` maps `X k` to the `k`-th coefficient of the shifted generic
depressed polynomial `((genericDepressed R m).map C).comp (X + C X)`. -/
theorem tschirnhausAlgEquiv_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (k : Fin m) :
    tschirnhausAlgEquiv hmu (MvPolynomial.X k) =
      (((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X)).coeff k := by
  have h := congrArg (fun p : (MvPolynomial (Fin (m - 1)) R)[X][X] ↦ p.coeff k)
    (map_freeMonic_tschirnhausAlgEquiv hmu)
  rw [Polynomial.coeff_map, coeff_freeMonic, dite_eq_left k.2] at h
  exact h

/-- **Tschirnhaus invariance of the universal discriminant.** When `(m : R)` is invertible,
`TauCeti.tschirnhausAlgEquiv` carries `(Polynomial.freeMonic R m).discr` to the constant
polynomial `Polynomial.C (depressedDiscr R m)`. -/
@[simp]
theorem tschirnhausAlgEquiv_discr_freeMonic {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    tschirnhausAlgEquiv hmu (freeMonic R m).discr = Polynomial.C (depressedDiscr R m) := by
  have h := congrArg Polynomial.discr (map_freeMonic_tschirnhausAlgEquiv hmu)
  rw [(monic_freeMonic R m).discr_map, discr_comp_X_add_C,
    (monic_genericDepressed R m).discr_map] at h
  exact h

/-- When `(m : R)` is a unit, `TauCeti.depressedDiscr R m` is prime in
`MvPolynomial (Fin (m - 1)) R` if and only if `(Polynomial.freeMonic R m).discr` is prime in
`MvPolynomial (Fin m) R`. -/
theorem prime_depressedDiscr_iff {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R)) :
    Prime (depressedDiscr R m) ↔ Prime (freeMonic R m).discr := by
  rw [← Polynomial.prime_C_iff, ← tschirnhausAlgEquiv_discr_freeMonic hmu,
    MulEquiv.prime_iff (tschirnhausAlgEquiv hmu)]

/-- Over a unique factorization domain `R` with `2 ≤ m` and `IsUnit (m : R)`, the generic
depressed discriminant is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_depressedDiscr_iff_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {m : ℕ} (hm : 2 ≤ m) (hmu : IsUnit (m : R)) :
    Prime (depressedDiscr R m) ↔ (2 : R) ≠ 0 :=
  (prime_depressedDiscr_iff hmu).trans (prime_discr_freeMonic_iff hm)

/-- **Primality of the generic depressed discriminant over a UFD.** If `R` is a unique
factorization domain in which `2 ≠ 0` and `(m : R)` is a unit, then `TauCeti.depressedDiscr R m`
is prime in `MvPolynomial (Fin (m - 1)) R` for every `m ≥ 2`. -/
theorem prime_depressedDiscr_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hmu : IsUnit (m : R)) : Prime (depressedDiscr R m) :=
  (prime_depressedDiscr_iff_of_isUnit hm hmu).mpr h2

/-- Over a field `K` of characteristic different from `2` in which `(m : K) ≠ 0`,
`TauCeti.depressedDiscr K m` is prime in `MvPolynomial (Fin (m - 1)) K` for every `m ≥ 2`. -/
theorem prime_depressedDiscr {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hm0 : (m : K) ≠ 0) : Prime (depressedDiscr K m) :=
  prime_depressedDiscr_of_isUnit h2 hm (IsUnit.mk0 _ hm0)

/-- Over a field `K` of characteristic zero, `TauCeti.depressedDiscr K m` is prime in
`MvPolynomial (Fin (m - 1)) K` for every `m ≥ 2`. -/
theorem depressedDiscr_prime (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  prime_depressedDiscr two_ne_zero hm (Nat.cast_ne_zero.mpr (by omega))

end Tschirnhaus

/-! ### Explicit low-degree formulas, Weierstrass discriminant, and sharpness -/

section LowDegree

/-- For `m = 0`, `TauCeti.depressedDiscr R 0` is `1`. -/
@[simp]
theorem depressedDiscr_zero (R : Type*) [CommRing R] :
    depressedDiscr R 0 = 1 := by
  rw [depressedDiscr_def, genericDepressed_zero]
  simpa only [Polynomial.C_1] using Polynomial.discr_C (1 : MvPolynomial (Fin 0) R)

/-- For `m = 1`, `TauCeti.depressedDiscr R 1` is `1`. -/
@[simp]
theorem depressedDiscr_one (R : Type*) [CommRing R] :
    depressedDiscr R 1 = 1 := by
  rw [depressedDiscr_def, genericDepressed_one]
  simpa using discr_X_pow_sub_C (0 : MvPolynomial (Fin 0) R) 1

/-- For `m = 2`, the discriminant of `X ^ 2 + a₂` is `-4 a₂`. -/
theorem depressedDiscr_two (R : Type*) [CommRing R] :
    depressedDiscr R 2 = -4 * MvPolynomial.X 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  rw [depressedDiscr_def, discr_of_degree_eq_two (degree_genericDepressed R 2)]
  have hc0 : (genericDepressed R 2).coeff 0 = MvPolynomial.X 0 := by
    rw [coeff_genericDepressed, dite_eq_left (by omega)]
    rfl
  have hc1 : (genericDepressed R 2).coeff 1 = 0 := by
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
  have hc2 : (genericDepressed R 2).coeff 2 = 1 := by
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_left rfl]
  rw [hc0, hc1, hc2]
  ring

/-- For `m = 3`, the discriminant of `X ^ 3 + a₂ X + a₃` is `-4 a₂ ^ 3 - 27 a₃ ^ 2`. -/
theorem depressedDiscr_three (R : Type*) [CommRing R] :
    depressedDiscr R 3 = -4 * MvPolynomial.X 0 ^ 3 - 27 * MvPolynomial.X 1 ^ 2 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  rw [depressedDiscr_def, discr_of_degree_eq_three (degree_genericDepressed R 3)]
  have hc0 : (genericDepressed R 3).coeff 0 = MvPolynomial.X 1 := by
    rw [coeff_genericDepressed, dite_eq_left (by omega)]
    rfl
  have hc1 : (genericDepressed R 3).coeff 1 = MvPolynomial.X 0 := by
    rw [coeff_genericDepressed, dite_eq_left (by omega)]
    rfl
  have hc2 : (genericDepressed R 3).coeff 2 = 0 := by
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
  have hc3 : (genericDepressed R 3).coeff 3 = 1 := by
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_left rfl]
  rw [hc0, hc1, hc2, hc3]
  ring

/-- For `m = 4`, the discriminant of `X ^ 4 + a₂ X ^ 2 + a₃ X + a₄`. -/
theorem depressedDiscr_four (R : Type*) [CommRing R] :
    depressedDiscr R 4 =
      256 * MvPolynomial.X 2 ^ 3 - 128 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 2 +
        144 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
        27 * MvPolynomial.X 1 ^ 4 + 16 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 2 -
        4 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 := by
  rw [depressedDiscr_def, genericDepressed_four, discr_depressedQuartic]

/-- In characteristic `2`, `depressedDiscr R 2` vanishes identically. -/
theorem depressedDiscr_two_of_charTwo (R : Type*) [CommRing R] [CharP R 2] :
    depressedDiscr R 2 = 0 := by
  rw [depressedDiscr_two]
  have h2R : (2 : R) = 0 := by simpa using CharP.cast_eq_zero R 2
  have h2 : (2 : MvPolynomial (Fin 1) R) = 0 := by
    rw [← map_ofNat MvPolynomial.C 2, h2R, map_zero]
  have h4 : (-4 : MvPolynomial (Fin 1) R) = 0 := by
    calc (-4 : MvPolynomial (Fin 1) R)
      _ = -2 * 2 := by ring
      _ = 0 := by rw [h2, mul_zero]
  rw [h4, zero_mul]

/-- In characteristic `2`, `depressedDiscr R 2` is not prime. -/
theorem not_prime_depressedDiscr_two_of_charTwo (R : Type*) [CommRing R] [CharP R 2] :
    ¬ Prime (depressedDiscr R 2) := by
  rw [depressedDiscr_two_of_charTwo]
  exact not_prime_zero

/-- In characteristic `3`, `depressedDiscr R 3` collapses to `-X 0 ^ 3`. -/
theorem depressedDiscr_three_of_charThree (R : Type*) [CommRing R] [CharP R 3] :
    depressedDiscr R 3 = -MvPolynomial.X 0 ^ 3 := by
  rw [depressedDiscr_three]
  have h3R : (3 : R) = 0 := by simpa using CharP.cast_eq_zero R 3
  have h3 : (3 : MvPolynomial (Fin 2) R) = 0 := by
    rw [← map_ofNat MvPolynomial.C 3, h3R, map_zero]
  have h4 : (-4 : MvPolynomial (Fin 2) R) = -1 := by
    calc (-4 : MvPolynomial (Fin 2) R)
      _ = -1 - 3 := by ring
      _ = -1 := by rw [h3, sub_zero]
  have h27 : (27 : MvPolynomial (Fin 2) R) = 0 := by
    calc (27 : MvPolynomial (Fin 2) R)
      _ = 9 * 3 := by ring
      _ = 0 := by rw [h3, mul_zero]
  rw [h4, h27]
  ring

/-- In characteristic `3`, `depressedDiscr R 3` is not prime over any nontrivial ring `R`. -/
theorem not_prime_depressedDiscr_three_of_charThree (R : Type*) [CommRing R] [Nontrivial R]
    [CharP R 3] : ¬ Prime (depressedDiscr R 3) := by
  rw [depressedDiscr_three_of_charThree]
  intro hp
  have hp' : Prime (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) R) := by
    simpa using hp.neg
  have hdvd : MvPolynomial.X 0 ^ 3 ∣ (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) *
      MvPolynomial.X 0 ^ 2 := by
    ring_nf
    exact dvd_rfl
  let ev : MvPolynomial (Fin 2) R →+* R[X] :=
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0]
  rcases hp'.dvd_or_dvd hdvd with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hev := congrArg ev hq
    simp only [ev, map_mul, map_pow, eval₂Hom_X', Matrix.cons_val_zero] at hev
    have hevq0 : ev q ≠ 0 := fun h0 ↦ by
      rw [h0, mul_zero] at hev
      exact X_ne_zero hev
    have hdeg3 : (Polynomial.X ^ 3 * ev q : R[X]).natDegree = 3 + (ev q).natDegree := by
      rw [(monic_X_pow 3).natDegree_mul' hevq0, natDegree_X_pow]
    rw [← hev, natDegree_X] at hdeg3
    omega
  · have hev := congrArg ev hq
    simp only [ev, map_mul, map_pow, eval₂Hom_X', Matrix.cons_val_zero] at hev
    have hevq0 : ev q ≠ 0 := fun h0 ↦ by
      rw [h0, mul_zero] at hev
      exact (monic_X_pow 2).ne_zero hev
    have hdeg3 : (Polynomial.X ^ 3 * ev q : R[X]).natDegree = 3 + (ev q).natDegree := by
      rw [(monic_X_pow 3).natDegree_mul' hevq0, natDegree_X_pow]
    rw [← hev, natDegree_X_pow] at hdeg3
    omega

/-- Over `ℤ`, `depressedDiscr ℤ 2 = -4 X₀` is not prime because `2` is not a unit in `ℤ`
(witnessing that `IsUnit (m : R)` cannot be weakened to `(m : R) ≠ 0` in
`TauCeti.prime_depressedDiscr_of_isUnit`). -/
theorem not_prime_depressedDiscr_int_two : ¬ Prime (depressedDiscr ℤ 2) := by
  rw [depressedDiscr_two]
  intro hp
  have hfac : (-4 : MvPolynomial (Fin 1) ℤ) * MvPolynomial.X 0 =
      (-2 : MvPolynomial (Fin 1) ℤ) * (2 * MvPolynomial.X 0) := by
    ring
  have hdvd : (-4 : MvPolynomial (Fin 1) ℤ) * MvPolynomial.X 0 ∣
      (-2 : MvPolynomial (Fin 1) ℤ) * (2 * MvPolynomial.X 0) := by
    rw [← hfac]
  rcases hp.dvd_or_dvd hdvd with ⟨q, hq⟩ | ⟨q, hq⟩
  · -- Specializing `X 0 ↦ 1` would yield `4 ∣ 2` in `ℤ`.
    have hev := congrArg (MvPolynomial.eval (fun _ ↦ (1 : ℤ))) hq
    simp only [map_mul, map_neg, map_ofNat, MvPolynomial.eval_X, mul_one] at hev
    omega
  · -- Specializing `X 0 ↦ 1` would yield `4 ∣ 2` in `ℤ`.
    have hev := congrArg (MvPolynomial.eval (fun _ ↦ (1 : ℤ))) hq
    simp only [map_mul, map_neg, map_ofNat, MvPolynomial.eval_X, mul_one] at hev
    omega

/-- The **Weierstrass cubic discriminant factor** `4 X₀³ + 27 X₁² = -depressedDiscr R 3` is
weighted homogeneous of weight `12` when `X₀` and `X₁` are given integer weights `4` and `6`. -/
theorem isWeightedHomogeneous_weierstrassDiscr (R : Type*) [CommRing R] :
    (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 :
      MvPolynomial (Fin 2) R).IsWeightedHomogeneous ![(4 : ℤ), 6] 12 := by
  have hneg : (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) =
      -depressedDiscr R 3 := by
    rw [depressedDiscr_three]
    ring
  rw [hneg, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.neg_mem _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (depressedDiscr R 3) 0]
    exact isWeightedHomogeneous_zero R _ _
  have h := (monic_genericDepressed R 3).isWeightedHomogeneous_discr ![(4 : ℤ), 6] 2 fun k hk ↦ ?_
  · rw [natDegree_genericDepressed] at h
    simpa [depressedDiscr_def] using h
  · rw [natDegree_genericDepressed] at hk ⊢
    interval_cases k
    · rw [coeff_genericDepressed, dite_eq_left (by omega)]
      exact isWeightedHomogeneous_X R ![(4 : ℤ), 6] 1
    · rw [coeff_genericDepressed, dite_eq_left (by omega)]
      exact isWeightedHomogeneous_X R ![(4 : ℤ), 6] 0
    · rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
      exact isWeightedHomogeneous_zero R _ _

/-- Over a unique factorization domain `R` in which `2 ≠ 0` and `(3 : R)` is a unit (in particular
over any field of characteristic neither `2` nor `3`), `4 X₀³ + 27 X₁²` is prime in
`MvPolynomial (Fin 2) R`. -/
theorem prime_weierstrassDiscr {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) (h3 : IsUnit (3 : R)) :
    Prime (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have hneg : (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) =
      -depressedDiscr R 3 := by
    rw [depressedDiscr_three]
    ring
  rw [hneg]
  exact Prime.neg (prime_depressedDiscr_of_isUnit h2 (by omega : 2 ≤ 3) (by simpa using h3))

end LowDegree

end TauCeti
