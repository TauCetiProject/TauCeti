/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
-- Proof-only: supplies integral-closure constructions and integrality transitivity.
-- The statements only need the public imports above.
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.ComputeDegree

/-!
# Integrality and clearing denominators

Integrality lemmas complementing Mathlib's `IsIntegral` API: clearing denominators of integral
elements by powers of a fixed element, module-finiteness from finitely many integral generators,
and a variant of Mathlib's `isIntegral_trans` without a scalar tower. Mathlib's lemma transfers
integrality down a tower `R → A → B`; the variant here only requires every element of the middle
ring `P` to become integral over `R` once mapped into the ring `L` where the element lives, which
is what happens when `R` and `P` both sit inside `L` without either being an algebra over the
other.

## Main results

* `IsIntegral.exists_isIntegral_algebraMap_pow_mul`: if each element of `A` times a power of `r`
  is integral over `P`, every element of an `A`-algebra integral over `A` becomes integral over
  `P` after multiplication by a power of `r`.
* `AlgHom.finite_of_adjoin_eq_top`: an `R`-algebra morphism `f : B →ₐ[R] A` is module-finite when
  `A` is generated as an `R`-algebra by a finite set of elements integral over `B` via `f`.
* `IsIntegral.natCast_pow_mul_pow`: if `b x` is integral over `R` for a natural number
  `b`, then so is `b ^ n x ^ j` for `j ≤ n`.
* `TauCeti.isIntegral_trans_common`: if every element of `P` becomes integral over `R` once
  mapped into `L`, then an element of `L` integral over `P` is integral over `R`.
* `TauCeti.dvd_of_isIntegral_div`: an element of a field extension of `A` that is a quotient of
  elements of `A` and is integral over `A` has its numerator divisible by its denominator, when
  `A` is integrally closed.
* `TauCeti.isIntegral_pow_card_mul_prod_sub`: an integral common denominator for a finite set
  clears the denominators of the product of differences from any one of its elements.
* `TauCeti.isIntegral_rat_of_isIntegral_natCast_mul`: if `b x` is integral over `ℤ` for some
  `b ≠ 0`, then `x` is integral over `ℚ`.
* `TauCeti.isIntegral_of_pow_add_pow_eq_mul_pow`: integrality from a monic power relation
  with integral coefficients.
* `Algebra.IsIntegral.of_finrank_pos`: a free algebra of positive finite rank over a commutative
  ring with the strong rank condition is integral.
-/

public section

section

open Polynomial

variable {P A B : Type*} [CommRing P] [CommRing A] [Ring B] [Algebra P A] [Algebra A B]
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

/-- If a finite set `s ⊆ A` generates `A` as an `R`-algebra and every element of `s` is integral
over `B` along `f : B →ₐ[R] A`, then `f` is module-finite. -/
theorem AlgHom.finite_of_adjoin_eq_top {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] (f : B →ₐ[R] A) {s : Set A} (hs : s.Finite)
    (hx : Algebra.adjoin R s = ⊤) (hint : ∀ a ∈ s, f.toRingHom.IsIntegralElem a) :
    f.Finite := by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have htop : Algebra.adjoin B s = ⊤ :=
    Subalgebra.restrictScalars_injective R (by simp [Algebra.Subalgebra.restrictScalars_adjoin, hx])
  refine Module.finite_def.mpr ?_
  rw [← Algebra.top_toSubmodule, ← htop]
  exact fg_adjoin_of_finite hs hint

/-- If `b x` is integral over `R` for a natural number `b`, then so is `b ^ n x ^ j` for
`j ≤ n`. -/
theorem IsIntegral.natCast_pow_mul_pow {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} {b : ℕ} (hbx : IsIntegral R ((b : A) * x)) {j n : ℕ} (hj : j ≤ n) :
    IsIntegral R ((b : A) ^ n * x ^ j) := by
  -- Write `b ^ n x ^ j` as the natural-number multiple `b ^ l • (b x) ^ j`, using that the cast
  -- of `b` commutes with `x`.
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [pow_add, mul_assoc, ← (Nat.cast_commute b x).mul_pow, ← Nat.cast_pow, ← nsmul_eq_mul]
  exact (hbx.pow j).smul _

namespace TauCeti

/-- If every element of `P` maps to an element of `L` integral over `R`, then every element of `L`
integral over `P` is integral over `R`. No algebra structure between `R` and `P` is needed. -/
theorem isIntegral_trans_common {R P L : Type*} [CommRing R] [CommRing P]
    [CommRing L] [Algebra R L] [Algebra P L]
    (hP : ∀ x : P, IsIntegral R (algebraMap P L x)) {x : L}
    (hx : IsIntegral P x) : IsIntegral R x := by
  -- Lift the monic equation of `x` over `P` to the integral closure of `R` in `L`, following the
  -- proof of Mathlib's `IsIntegral.of_aeval_monic_of_isIntegral_coeff`.
  obtain ⟨p, hpm, hpx⟩ := hx
  obtain ⟨q, hqp, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := algebraMap (integralClosure R L) L) (p := p.map (algebraMap P L))
    ((Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦
      ⟨⟨_, hP (p.coeff i)⟩, (Polynomial.coeff_map _ i).symm⟩) (hpm.map _)
  exact isIntegral_trans x ⟨q, hqm, by rw [← Polynomial.eval_map, hqp, Polynomial.eval_map, hpx]⟩

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
theorem isIntegral_rat_of_isIntegral_natCast_mul {A : Type*} [Ring A] [Algebra ℚ A] {x : A}
    {b : ℕ} (hb : b ≠ 0) (hbx : IsIntegral ℤ ((b : A) * x)) : IsIntegral ℚ x := by
  -- `b` becomes a unit over `ℚ`, with inverse `algebraMap ℚ A b⁻¹`.
  refine .of_mul_unit (y := (b : A)) (r := (b : ℚ)⁻¹) ?_ ?_
  · rw [← map_natCast (algebraMap ℚ A), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hb),
      map_one]
  · rw [← Nat.cast_comm]
    exact hbx.tower_top

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

/-- **A positive finite rank forces integrality**: if `0 < Module.finrank K L` for a commutative
ring `K` with the strong rank condition (for example a nontrivial commutative ring) and a free
`K`-algebra `L` (automatic over a field), then `L` is integral over `K`.

This is the composition of Mathlib's `Module.finite_of_finrank_pos` (positive rank gives a finite
module) and `Algebra.IsIntegral.of_finite` (finite algebras are integral). -/
theorem Algebra.IsIntegral.of_finrank_pos {K L : Type*} [CommRing K] [Ring L] [Algebra K L]
    [StrongRankCondition K] [Module.Free K L] (h : 0 < Module.finrank K L) :
    Algebra.IsIntegral K L :=
  haveI := Module.finite_of_finrank_pos h
  Algebra.IsIntegral.of_finite K L
