/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
-- Proof-only: supplies integral-closure constructions and integrality transitivity.
-- The statements only need the public imports above.
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.ComputeDegree

/-!
# Integrality and clearing denominators

Mathlib's `isIntegral_trans` transfers integrality down a scalar tower `R → A → B`. The variant
here drops the tower: the two candidate base rings are only required to map compatibly into the
ring where the element lives, which is what happens when both of them sit inside that ring
without either being an algebra over the other.

## Main results

* `IsIntegral.exists_isIntegral_algebraMap_pow_mul`: if each element of `A` times a power of `r`
  is integral over `P`, every element of an `A`-algebra integral over `A` becomes integral over
  `P` after multiplication by a power of `r`.
* `TauCeti.isIntegral_trans_common`: if every element of `P` becomes integral over `R` once
  mapped into `L`, then an element of `L` integral over `P` is integral over `R`.
* `TauCeti.dvd_of_isIntegral_div`: an element of a field extension of `A` that is a quotient of
  elements of `A` and is integral over `A` has its numerator divisible by its denominator, when
  `A` is integrally closed.
* `TauCeti.isIntegral_natCast_pow_mul_pow`: if `b x` is integral over `ℤ`, then so is
  `b ^ n x ^ j` for `j ≤ n`.
* `TauCeti.isIntegral_pow_card_mul_prod_sub`: an integral common denominator for a finite set
  clears the denominators of the product of differences from any one of its elements.
* `TauCeti.isIntegral_rat_of_isIntegral_natCast_mul`: if `b x` is integral over `ℤ` for some
  `b ≠ 0`, then `x` is integral over `ℚ`.
* `TauCeti.isIntegral_of_pow_add_pow_eq_mul_pow`: integrality from a monic power relation
  with integral coefficients.
* `Algebra.IsIntegral.of_finrank_pos`: an algebra of positive finite rank over a field is integral.
-/

public section

section

open Polynomial

variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B] [Algebra P A] [Algebra A B]
  [Algebra P B] [IsScalarTower P A B]

/-- Let `r ∈ A` be such that every element of `A` times a power of `r` is integral over `P`. Then
every element `c` of an `A`-algebra that is integral over `A` becomes integral over `P` after
multiplication by a power of `r`. -/
theorem IsIntegral.exists_isIntegral_algebraMap_pow_mul {c : B} (hc : IsIntegral A c) {r : A}
    (H : ∀ a : A, ∃ m, IsIntegral P (r ^ m * a)) :
    ∃ n, IsIntegral P (algebraMap A B r ^ n * c) := by
  -- If `f` is a monic equation of `c` over `A` and `rᴺ` clears its coefficients, then `rᴺ c` is
  -- a root of `f.scaleRoots rᴺ`, a monic polynomial with coefficients integral over `P`.
  obtain ⟨f, hfm, hfc⟩ := hc
  choose m hm using H
  have hr : IsIntegral P r := .of_pow (Nat.succ_pos _) (by simpa [pow_succ] using hm r)
  -- A common exponent `N` clearing all the coefficients of `f`.
  set N := ∑ i ∈ Finset.range (f.natDegree + 1), m (f.coeff i)
  have hcoeff (i : ℕ) : IsIntegral P (r ^ N * f.coeff i) := by
    rcases le_or_gt i f.natDegree with hi | hi
    · have : m (f.coeff i) ≤ N := Finset.single_le_sum (f := fun i ↦ m (f.coeff i))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      rw [← Nat.sub_add_cancel this, pow_add, mul_assoc]
      exact (hr.pow _).mul (hm _)
    · rw [f.coeff_eq_zero_of_natDegree_lt hi, mul_zero]
      exact isIntegral_zero
  -- The coefficients of `f.scaleRoots rᴺ` lie in the integral closure `S` of `P` in `A`.
  let S := integralClosure P A
  have hg (i : ℕ) : (f.scaleRoots (r ^ N)).coeff i ∈ S := by
    rw [coeff_scaleRoots, mem_integralClosure_iff]
    rcases lt_or_ge i f.natDegree with hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, f.natDegree - i = k + 1 := ⟨f.natDegree - i - 1, by omega⟩
      rw [hk, pow_succ, mul_comm, mul_assoc]
      exact ((hr.pow N).pow k).mul (hcoeff i)
    · rw [Nat.sub_eq_zero_of_le hi, pow_zero, mul_one]
      rcases hi.eq_or_lt with h | h
      · rw [← h, hfm.coeff_natDegree]
        exact isIntegral_one
      · rw [f.coeff_eq_zero_of_natDegree_lt h]
        exact isIntegral_zero
  obtain ⟨g, hgf, -, hgm⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := algebraMap S A) _).mpr fun i ↦ ⟨⟨_, hg i⟩, rfl⟩)
    ((monic_scaleRoots_iff _).mpr hfm)
  -- So `rᴺ c` is integral over `S`, which is integral over `P`.
  have : IsIntegral S (algebraMap A B r ^ N * c) := ⟨g, hgm, by
    rw [IsScalarTower.algebraMap_eq S A B, ← eval₂_map, hgf, ← map_pow, ← aeval_def]
    exact scaleRoots_aeval_eq_zero hfc⟩
  exact ⟨N, isIntegral_trans _ this⟩

end

namespace TauCeti

/-- Integrality transfers through compatible maps from two rings into a common ring. -/
theorem isIntegral_trans_common {R P L : Type*} [CommRing R] [CommRing P]
    [CommRing L] [Algebra R L] [Algebra P L]
    (hP : ∀ x : P, IsIntegral R (algebraMap P L x)) {x : L}
    (hx : IsIntegral P x) : IsIntegral R x := by
  let S := Algebra.adjoin R (Set.range (algebraMap P L))
  let integral : Algebra.IsIntegral R S := Algebra.IsIntegral.adjoin fun y hy ↦ by
    obtain ⟨z, rfl⟩ := hy
    exact hP z
  let pToS : P →+* S := RingHom.codRestrict (algebraMap P L) S fun z ↦
    Algebra.subset_adjoin ⟨z, rfl⟩
  let pAlgebra : Algebra P S := pToS.toAlgebra
  -- the tower equality holds pointwise: `pToS` restricts `algebraMap P L` to `S`, so composing
  -- with the inclusion `S.val` returns the original map. Stated by extensionality rather than by
  -- `rfl`, so it does not depend on how `codRestrict` and `toAlgebra` unfold.
  let scalarTower : IsScalarTower P S L := IsScalarTower.of_algebraMap_eq' <| by
    ext z
    simp [pAlgebra, RingHom.algebraMap_toAlgebra, pToS]
  exact isIntegral_trans (R := R) (A := S) x (hx.tower_top (A := S))

/-- An element of a field extension of `A` that is a quotient of elements of `A` and is integral
over `A` has its numerator divisible by its denominator, when `A` is integrally closed. -/
theorem dvd_of_isIntegral_div
    {A L : Type*} [CommRing A]
    [IsIntegrallyClosed A] [Field L] [Algebra A L] [FaithfulSMul A L] {a d : A} (hd : d ≠ 0)
    (h : IsIntegral A (algebraMap A L a / algebraMap A L d)) : d ∣ a := by
  have hinj : Function.Injective (algebraMap A L) := FaithfulSMul.algebraMap_injective A L
  have : IsDomain A := hinj.isDomain (algebraMap A L)
  let f : FractionRing A →ₐ[A] L := IsFractionRing.liftAlgHom (g := Algebra.ofId A L) hinj
  have hf : Function.Injective f := (f : FractionRing A →+* L).injective
  have hdF : algebraMap A (FractionRing A) d ≠ 0 := fun h' =>
    hd (IsFractionRing.injective A (FractionRing A) (by rw [h', map_zero]))
  have hw : f (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) d) =
      algebraMap A L a / algebraMap A L d := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes]
  obtain ⟨e, he⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algHom_iff f hf).mp (hw ▸ h))
  refine ⟨e, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, he, mul_div_cancel₀ _ hdF]

/-- If `b x` is integral over `ℤ`, then so is `b ^ n x ^ j` for `j ≤ n`. -/
theorem isIntegral_natCast_pow_mul_pow {A : Type*} [CommRing A] {x : A} {b : ℕ}
    (hbx : IsIntegral ℤ ((b : A) * x)) {j n : ℕ} (hj : j ≤ n) :
    IsIntegral ℤ ((b : A) ^ n * x ^ j) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [pow_add, mul_right_comm, ← mul_pow, mul_comm]
  exact ((isIntegral_natCast b).pow l).mul (hbx.pow j)

/-- If `l` and every `l x` for `x ∈ S` are integral over `R`, then
`l ^ S.card * ∏ x ∈ S.erase a, (a - x)` is integral over `R` for every `a ∈ S`. -/
theorem isIntegral_pow_card_mul_prod_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq A] {S : Finset A} {l a : A} (ha : a ∈ S) (hl : IsIntegral R l)
    (hS : ∀ x ∈ S, IsIntegral R (l * x)) :
    IsIntegral R (l ^ S.card * ∏ x ∈ S.erase a, (a - x)) := by
  rw [← Finset.card_erase_add_one ha, pow_succ', mul_assoc, Finset.pow_card_mul_prod]
  refine hl.mul (IsIntegral.prod _ fun x hx ↦ ?_)
  rw [mul_sub]
  exact (hS a ha).sub (hS x (Finset.mem_of_mem_erase hx))

/-- If `b x` is integral over `ℤ` for a nonzero natural number `b`, then `x` is integral over
`ℚ`. -/
theorem isIntegral_rat_of_isIntegral_natCast_mul {F : Type*} [Field F] [CharZero F] {x : F}
    {b : ℕ} (hb : b ≠ 0) (hbx : IsIntegral ℤ ((b : F) * x)) : IsIntegral ℚ x := by
  have h := (isIntegral_algebraMap (R := ℚ) (x := ((b : ℚ)⁻¹))).mul (hbx.tower_top (A := ℚ))
  rwa [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hb), one_mul] at h

/-- If `(g ^ n + c) ^ m = z * (g ^ n) ^ k` with `0 < n`, `k < m`, and both `c` and `z`
integral over `R`, then `g` is integral over `R`. The degree bound makes the relation monic
in `g ^ n` over the integral closure, and integrality descends from this positive power. -/
theorem isIntegral_of_pow_add_pow_eq_mul_pow {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {z c g : A} (hz : IsIntegral R z) (hc : IsIntegral R c)
    {n m k : ℕ} (hn : 0 < n) (hk : k < m)
    (hg : (g ^ n + c) ^ m = z * (g ^ n) ^ k) : IsIntegral R g := by
  let z' : integralClosure R A := ⟨z, hz⟩
  let c' : integralClosure R A := ⟨c, hc⟩
  have hpow : IsIntegral (integralClosure R A) (g ^ n) := by
    refine ⟨(Polynomial.X + Polynomial.C c') ^ m -
      Polynomial.C z' * Polynomial.X ^ k, ?_, ?_⟩
    · monicity!; simp [hk.le, hk.not_ge]
    · simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
        Subalgebra.algebraMap_apply] using sub_eq_zero.mpr hg
  exact isIntegral_trans g (hpow.of_pow hn)

end TauCeti

/-- **A positive finite rank forces integrality**: if `0 < finrank K L` for a field `K` and a ring
`L` over it, then `L` is finite over `K` (a module of infinite dimension has `finrank` zero), hence
integral. -/
theorem Algebra.IsIntegral.of_finrank_pos {K L : Type*} [Field K] [Ring L] [Algebra K L]
    (h : 0 < Module.finrank K L) : Algebra.IsIntegral K L :=
  haveI := Module.finite_of_finrank_pos h
  Algebra.IsIntegral.of_finite K L
