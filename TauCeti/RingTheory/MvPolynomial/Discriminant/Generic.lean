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
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.RingTheory.MvPolynomial.IrreducibleQuadratic
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Normalization
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# Weighted homogeneity and primality of the generic monic discriminant

Let `R` be a commutative ring. A monic polynomial of degree `m` over `R` has `m` free lower
coefficients, represented universally by `Polynomial.freeMonic R m` over `MvPolynomial (Fin m) R`.
Under uniform scaling `rᵢ ↦ t rᵢ` of the roots, the elementary symmetric coefficient `aₖ` of
`X ^ (m - k)` acquires weight `k`, and over any commutative ring `R` and degree `m` the universal
monic discriminant `(Polynomial.freeMonic R m).discr` is weighted homogeneous of weight
`m * (m - 1)`. Over a unique factorization domain `R` and for `2 ≤ m`,
`(Polynomial.freeMonic R m).discr` is prime if and only if `(2 : R) ≠ 0` (and is a square when
`(2 : R) = 0`), so under those hypotheses the repeated-root locus where the generic monic
discriminant vanishes is an irreducible weighted-homogeneous hypersurface of weight `m * (m - 1)`.

1. **Weighted homogeneity.** Scaling the roots of `Polynomial.freeMonic R m` by an indeterminate
   `T` multiplies the `k`-th coefficient by `T ^ (m - k)` and multiplies the discriminant by
   `T ^ (m * (m - 1))`. Consequently `(Polynomial.freeMonic R m).discr` is weighted homogeneous of
   weight `m * (m - 1)` when `X k` is given weight `m - k`
   (`Polynomial.isWeightedHomogeneous_discr_freeMonic`). Specializing the universal monic
   polynomial transfers this to any monic polynomial `f` over `MvPolynomial σ R` whose `k`-th
   coefficient (`k < f.natDegree`) is weighted homogeneous of weight `(f.natDegree - k) • u` in an
   arbitrary additive commutative monoid (`Polynomial.Monic.isWeightedHomogeneous_discr`).

2. **Primality of the generic monic discriminant.** Via Vieta's formulas and the fundamental
   theorem of symmetric polynomials, `MvPolynomial (Fin m) R` embeds `R`-algebraically onto the
   symmetric polynomials in `m` root variables, sending `(Polynomial.freeMonic R m).discr` to the
   square `δ ^ 2` of the Vandermonde product `δ = ∏_{i < j} (X i - X j)`. Over a unique
   factorization domain `R` with `2 ≤ m`, the linear factors `X i - X j` (`i < j`) are pairwise
   non-associated primes permuted transitively on ordered pairs of distinct indices by
   `Equiv.Perm (Fin m)`. Any symmetric factor of `δ ^ 2` divisible by one root difference is
   therefore divisible by `δ`, whereas permuting two variables negates `δ` and rules out symmetric
   unit multiples of `δ` whenever `(2 : R) ≠ 0`. Conversely, when `(2 : R) = 0`, `δ` is symmetric
   and the generic monic discriminant is a square
   (`Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`). Hence `(Polynomial.freeMonic R m).discr`
   is prime if and only if `(2 : R) ≠ 0` (`Polynomial.prime_discr_freeMonic_iff`).

## Main results

* `Polynomial.isWeightedHomogeneous_discr_freeMonic`,
  `Polynomial.Monic.isWeightedHomogeneous_discr`: weighted homogeneity of the universal and
  specialized monic discriminants.
* `Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`,
  `Polynomial.prime_discr_freeMonic`, `Polynomial.prime_discr_freeMonic_iff`: squareness when
  `2 = 0` and unique factorization primality of `(Polynomial.freeMonic R m).discr` when `2 ≤ m`.

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
  have hscale_mon : (F.scaleRoots Polynomial.X).Monic :=
    (monic_scaleRoots_iff _).mpr ((monic_freeMonic R m).map Polynomial.C)
  have hscale_deg : (F.scaleRoots Polynomial.X).natDegree = m := by
    rw [natDegree_scaleRoots, hFdeg]
  have hg_eq : g = fun i : Fin m ↦ (F.scaleRoots Polynomial.X).coeff i := by
    funext i
    simp [F, g, w, coeff_scaleRoots, hFdeg, coeff_freeMonic, i.isLt]
  have hscale : (freeMonic R m).map (MvPolynomial.aeval g).toRingHom =
      F.scaleRoots Polynomial.X := by
    rw [hg_eq]
    exact congrArg Subtype.val
      ((MvPolynomial.mapEquivMonic R _ m).apply_symm_apply (.mk _ hscale_mon hscale_deg))
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
  have hmap : (freeMonic R n).map φ.toRingHom = f :=
    congrArg Subtype.val ((MvPolynomial.mapEquivMonic R _ n).apply_symm_apply (.mk f hf rfl))
  have hdiscr : f.discr = φ (freeMonic R n).discr := by
    rw [← hmap, (monic_freeMonic R n).discr_map]
    rfl
  have hfree : (freeMonic R n).discr.IsWeightedHomogeneous
      (fun i : Fin n ↦ (n - (i : ℕ)) • u) ((n * (n - 1)) • u) := fun d hd ↦ by
    simpa only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, multiplesHom_apply, smul_eq_mul,
      mul_smul] using congrArg (multiplesHom M u) (isWeightedHomogeneous_discr_freeMonic R n hd)
  rw [hdiscr]
  exact hfree.aeval fun i ↦ hc i i.2

/-! ### Primality of the generic monic discriminant -/

section FreeMonicPrime

/-- The Vandermonde product `∏_{i < j} (X i - X j)` in `MvPolynomial (Fin m) R`. -/
private noncomputable def vandermonde (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R :=
  ∏ i : Fin m, ∏ j ∈ Ioi i, (MvPolynomial.X i - MvPolynomial.X j)

private theorem vietaAlgHom_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    vietaAlgHom R m (freeMonic R m).discr = vandermonde R m ^ 2 := by
  have h := congrArg Polynomial.discr (map_vietaAlgHom_freeMonic R m)
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
`MvPolynomial (Fin m) R`. -/
theorem isSquare_discr_freeMonic_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    (m : ℕ) : IsSquare (freeMonic R m).discr := by
  -- When `2 = 0`, `-1 = 1`, so the Vandermonde product is invariant under every permutation of
  -- the roots and descends along `vietaAlgEquiv` to a square root of the discriminant.
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
    simp [s, vietaAlgHom_apply]
  refine ⟨s, (vietaAlgHom_injective R m) ?_⟩
  rw [vietaAlgHom_discr_freeMonic, map_mul, ← sq, hs]

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
    obtain ⟨σ, hσ1, hσ2⟩ := MulAction.is_two_pretransitive_iff.mp
      (Equiv.Perm.isMultiplyPretransitive (Fin m) 2) h₀.ne hx'.ne
    simp only [Equiv.Perm.smul_def] at hσ1 hσ2
    have hmap := _root_.map_dvd (rename (R := R) σ) hdvd₀
    simpa [hp σ, hσ1, hσ2] using hmap

private theorem vandermonde_ne_zero {R : Type*} [CommRing R] [IsDomain R] (m : ℕ) :
    vandermonde R m ≠ 0 := by
  rw [vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
  exact (irreducible_X_sub_X (mem_Ioi.mp hj).ne).ne_zero

/-- Any symmetric divisor of `vandermonde R m ^ 2` over a UFD is either a unit or divisible by
`vandermonde R m`. -/
private theorem isUnit_or_vandermonde_dvd_of_isSymmetric_of_dvd_sq {R : Type*} [CommRing R]
    [IsDomain R] [UniqueFactorizationMonoid R] {m : ℕ} {p : MvPolynomial (Fin m) R}
    (hp : p.IsSymmetric) (hdvd : p ∣ vandermonde R m ^ 2) :
    IsUnit p ∨ vandermonde R m ∣ p := by
  by_cases hu : IsUnit p
  · exact Or.inl hu
  right
  have hp0 : p ≠ 0 := fun h0 ↦ pow_ne_zero 2 (vandermonde_ne_zero m) (zero_dvd_iff.mp (h0 ▸ hdvd))
  obtain ⟨q, hq_irr, hqp⟩ := WfDvdMonoid.exists_irreducible_factor hu hp0
  have hq_prime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irr
  have hq_vand : q ∣ vandermonde R m := hq_prime.dvd_of_dvd_pow (hqp.trans hdvd)
  rw [vandermonde] at hq_vand
  obtain ⟨i, -, hqi⟩ := hq_prime.exists_mem_finset_dvd hq_vand
  obtain ⟨j, hj, hqij⟩ := hq_prime.exists_mem_finset_dvd hqi
  have hij : i < j := mem_Ioi.mp hj
  have hass := hq_irr.associated_of_dvd (irreducible_X_sub_X hij.ne) hqij
  exact vandermonde_dvd_of_isSymmetric hp hij (hass.symm.dvd.trans hqp)

/-- When `(2 : R) ≠ 0`, `2 ≤ m`, and `r ≠ 0`, `vandermonde R m * C r` is negated by swapping the
first two variables and is therefore not symmetric. -/
private theorem not_isSymmetric_vandermonde_mul_C {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) {r : R} (hr : r ≠ 0) :
    ¬ (vandermonde R m * MvPolynomial.C r).IsSymmetric := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  intro hsymm
  have hswap := hsymm (Equiv.swap i₀ i₁)
  rw [map_mul, rename_vandermonde, Equiv.Perm.sign_swap h01, rename_C] at hswap
  have hswap' : -(vandermonde R m * MvPolynomial.C r) = vandermonde R m * MvPolynomial.C r := by
    simpa using hswap
  have hzero : MvPolynomial.C (2 : R) * (vandermonde R m * MvPolynomial.C r) = 0 := by
    calc MvPolynomial.C (2 : R) * (vandermonde R m * MvPolynomial.C r)
      _ = (1 + 1) * (vandermonde R m * MvPolynomial.C r) := by
          rw [← one_add_one_eq_two, map_add, map_one]
      _ = -(vandermonde R m * MvPolynomial.C r) + vandermonde R m * MvPolynomial.C r := by
          rw [add_mul, one_mul]
          nth_rw 1 [← hswap']
      _ = 0 := neg_add_cancel _
  have hne0 : vandermonde R m * MvPolynomial.C r ≠ 0 :=
    mul_ne_zero (vandermonde_ne_zero m) (by simpa using hr)
  exact h2 (MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hne0))

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
    rcases isUnit_or_vandermonde_dvd_of_isSymmetric_of_dvd_sq (isSymmetric_vietaAlgHom f)
      ⟨vietaAlgHom R m g, hprod.symm⟩ with hf | ⟨q₁, hq₁⟩
    · exact Or.inl (isUnit_of_isUnit_vietaAlgHom hf)
    rcases isUnit_or_vandermonde_dvd_of_isSymmetric_of_dvd_sq (isSymmetric_vietaAlgHom g)
      ⟨vietaAlgHom R m f, by rw [mul_comm, hprod]⟩ with hg | ⟨q₂, hq₂⟩
    · exact Or.inr (isUnit_of_isUnit_vietaAlgHom hg)
    have hmul : vandermonde R m ^ 2 * (q₁ * q₂) = vandermonde R m ^ 2 * 1 := by
      calc vandermonde R m ^ 2 * (q₁ * q₂)
        _ = (vandermonde R m * q₁) * (vandermonde R m * q₂) := by ring
        _ = vietaAlgHom R m f * vietaAlgHom R m g := by rw [← hq₁, ← hq₂]
        _ = vandermonde R m ^ 2 * 1 := by rw [hprod, mul_one]
    have hq₁_unit : IsUnit q₁ :=
      IsUnit.of_mul_eq_one q₂ (mul_left_cancel₀ (pow_ne_zero 2 (vandermonde_ne_zero m)) hmul)
    obtain ⟨r, hr, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hq₁_unit
    exact absurd (hq₁ ▸ isSymmetric_vietaAlgHom f)
      (not_isSymmetric_vandermonde_mul_C h2 hm hr.ne_zero)

/-- Over a unique factorization domain `R` and for `m ≥ 2`, the discriminant of
`Polynomial.freeMonic R m` is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_discr_freeMonic_iff {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr ↔ (2 : R) ≠ 0 :=
  ⟨fun hp h2 ↦ (isSquare_discr_freeMonic_of_two_eq_zero h2 m).not_prime hp,
    fun h2 ↦ prime_discr_freeMonic h2 hm⟩

end FreeMonicPrime

end Polynomial
