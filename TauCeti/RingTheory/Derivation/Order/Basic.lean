/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.Derivation.Order.Bound
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.Derivation.LocalLift
import TauCeti.RingTheory.MvPolynomial.Evaluation.Derivation
import TauCeti.RingTheory.RegularLocalRing.AssociatedGraded
import TauCeti.RingTheory.Smooth.Field

/-!
# Order of derivation ideals in characteristic zero

For an algebra `R` over a characteristic-zero field `k` with `Ω[R⁄k]` finitely generated and
projective over `R`, the derivation ideal `I.derivationIdeal k` lowers ideal order at every
regular prime `p` (meaning `IsRegularLocalRing (Localization.AtPrime p.asIdeal)`) by exactly one:
`(I.derivationIdeal k).orderAt p = I.orderAt p - 1` (truncated subtraction in `ℕ∞`, so finite
positive order drops by one while `0` and `⊤` remain fixed).

The proof uses formal smoothness of the residue field `κ(p)` over the characteristic-zero field `k`
to inject `𝔪_p ⧸ 𝔪_p²` into `κ(p) ⊗[R_p] Ω[R_p⁄k]`, lifts dual `κ(p)`-linear functionals to global
`k`-derivations of `R` up to a denominator outside `p` (`Derivation.exists_dual_derivation`), and
applies the associated-graded criterion
`TauCeti.IsRegularLocalRing.map_residue_eq_zero_iff_eval_mem_pow_succ` together with
`MvPolynomial.eq_C_constantCoeff_of_forall_pderiv_eq_zero` over `κ(p)`.

Iterating `n` times gives
`((n + 1 : ℕ) : ℕ∞) ≤ I.orderAt p ↔ (derivationIdeal k)^[n] I ≤ p.asIdeal` at every regular prime
`p`.

## Main results

Common hypotheses: `k` is a characteristic-zero field and `Ω[R⁄k]` is finitely generated and
projective over `R`.

* `Ideal.mem_maximalIdeal_pow_add_two_of_forall_derivation`: elementwise order-increase test in any
  regular local localization `A` of `R`.
* `Ideal.orderAt_derivationIdeal`: at a prime `p` with `R_p` regular local,
  `(I.derivationIdeal k).orderAt p = I.orderAt p - 1`.
* `Ideal.orderAt_derivationIdeal_iterate`: at a prime `p` with `R_p` regular local,
  `((derivationIdeal k)^[n] I).orderAt p = I.orderAt p - n`.
* `Ideal.natCast_add_one_le_orderAt_iff_iterate_derivationIdeal_le`: at a prime `p` with `R_p`
  regular local, `((n + 1 : ℕ) : ℕ∞) ≤ I.orderAt p ↔ (derivationIdeal k)^[n] I ≤ p.asIdeal`.

## References

* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing
  up the maximum strata of a local invariant*, Invent. Math. 128 (1997), §4.1–4.2 and
  Proposition 4.12.
-/

public section

open IsLocalRing MvPolynomial

namespace Ideal

section SmoothCharZero

/-- If a homogeneous form `F` of degree `n + 1` in a regular system of parameters `rs` of `A` has
every global derivation sending `F(rs)` into `𝔪 ^ (n + 1)`, then every partial derivative of
`F.map (residue A)` vanishes. -/
private theorem pderiv_map_residue_eq_zero {k R A : Type*} [Field k] [PerfectField k]
    [CommRing R] [CommRing A] [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    (S : Submonoid R) [IsLocalization S A] [IsRegularLocalRing A]
    {rs : List A} (hofList : ofList rs = maximalIdeal A)
    (hlen : rs.length = (maximalIdeal A).spanFinrank)
    {n : ℕ} {F : MvPolynomial (Fin rs.length) A} (hF : F.IsHomogeneous (n + 1))
    (hD : ∀ δ : Derivation k R R,
      (((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S) (F.eval fun j ↦ rs[j]) ∈
        maximalIdeal A ^ (n + 1)) (i : Fin rs.length) :
    pderiv i (F.map (residue A)) = 0 := by
  classical
  let t : Fin rs.length → A := fun j ↦ rs[j]
  have ht : span (Set.range t) = maximalIdeal A := by
    rw [← hofList, ofList_eq_span_range_getElem]
  have htmem (j : Fin rs.length) : t j ∈ maximalIdeal A := ht ▸ subset_span ⟨j, rfl⟩
  obtain ⟨s, δ, hDt⟩ := Derivation.exists_dual_derivation (k := k) S ht hlen.symm i
  let Dloc : Derivation k A A := ((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S
  have hcongr := Dloc.apply_eval_sub_pderiv_mul_mem_pow_succ htmem hF hDt
  have hmul_mem : (pderiv i F).eval t * algebraMap R A s ∈ maximalIdeal A ^ (n + 1) := by
    simpa [Dloc, t] using Ideal.sub_mem _ (hD δ) hcongr
  have hp_eval : (pderiv i F).eval t ∈ maximalIdeal A ^ (n + 1) :=
    (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units A s)).mp hmul_mem
  rw [pderiv_map]
  exact (TauCeti.IsRegularLocalRing.map_residue_eq_zero_iff_eval_mem_pow_succ hofList hlen.le
    hF.pderiv).mpr hp_eval

/-- In a regular local localization `A` of `R` with `Ω[R⁄k]` finite projective over a
characteristic-zero field `k`, if `y ∈ 𝔪 ^ (n + 1)` has `D_loc y ∈ 𝔪 ^ (n + 1)` for every global
`k`-derivation `δ : Derivation k R R`, then `y ∈ 𝔪 ^ (n + 2)`. -/
theorem mem_maximalIdeal_pow_add_two_of_forall_derivation {k R A : Type*} [Field k]
    [CharZero k] [CommRing R] [CommRing A] [Algebra k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    (S : Submonoid R) [IsLocalization S A] [IsRegularLocalRing A] {n : ℕ} {y : A}
    (hy : y ∈ maximalIdeal A ^ (n + 1))
    (hD : ∀ δ : Derivation k R R,
      (((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S) y ∈ maximalIdeal A ^ (n + 1)) :
    y ∈ maximalIdeal A ^ (n + 2) := by
  classical
  -- Choose a regular system of parameters `rs` of `A` and write `y = F(rs)` with `F` homogeneous.
  obtain ⟨U, hcard, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal A).fg_of_isNoetherianRing
  let rs : List A := U.toList
  have hofList : ofList rs = maximalIdeal A := by
    simpa [rs, ofList] using hU
  have hlen : rs.length = (maximalIdeal A).spanFinrank := by simp [rs, hcard]
  let t : Fin rs.length → A := fun i ↦ rs[i]
  have ht : span (Set.range t) = maximalIdeal A := by
    rw [← hofList, ofList_eq_span_range_getElem]
  obtain ⟨F, hF, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous t y).mp (ht.symm ▸ hy)
  -- Every partial derivative of `F.map (residue A)` vanishes, so it is a homogeneous constant `0`.
  have hpderiv_zero := pderiv_map_residue_eq_zero (k := k) S hofList hlen hF hD
  have hchar : CharZero (IsLocalRing.ResidueField A) :=
    charZero_of_injective_algebraMap (algebraMap k (IsLocalRing.ResidueField A)).injective
  have : HasUniqueDiv (IsLocalRing.ResidueField A) := IsAddTorsionFree.hasUniqueDiv
  have hFmap : F.map (residue A) = 0 := by
    rw [MvPolynomial.eq_C_constantCoeff_of_forall_pderiv_eq_zero hpderiv_zero,
      MvPolynomial.constantCoeff_eq, (hF.map (residue A)).coeff_eq_zero (by simp), map_zero]
  -- Passing back through the associated graded criterion puts `F(t)` in `𝔪 ^ (n + 2)`.
  simpa [t] using (TauCeti.IsRegularLocalRing.map_residue_eq_zero_iff_eval_mem_pow_succ
    hofList hlen.le hF).mp hFmap

variable (k : Type*) [Field k] [CharZero k] {R : Type*} [CommRing R] [Algebra k R]

/-- **Over a characteristic-zero field, the derivation ideal satisfies
`(I.derivationIdeal k).orderAt p = I.orderAt p - 1` at a regular prime** (truncated subtraction
in `ℕ∞`, so finite positive order drops by one while `0` and `⊤` remain fixed), assuming
`Ω[R⁄k]` is finitely generated and projective over `R` and `R_p` is regular local. -/
@[simp]
theorem orderAt_derivationIdeal [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    (I : Ideal R) (p : PrimeSpectrum R) [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] :
    (I.derivationIdeal k).orderAt p = I.orderAt p - 1 := by
  refine le_antisymm ?_
    (tsub_le_iff_right.mpr (orderAt_le_orderAt_derivationIdeal_add_one k I p))
  refine ENat.forall_natCast_le_iff_le.mp fun m hm ↦ ?_
  cases m with
  | zero => simp
  | succ n =>
    refine ENat.le_sub_of_add_le_right ENat.one_ne_top ?_
    have hle : ((n + 2 : ℕ) : ℕ∞) ≤ I.orderAt p := by
      rw [natCast_le_orderAt_iff] at hm ⊢
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [mem_comap]
      refine mem_maximalIdeal_pow_add_two_of_forall_derivation (k := k) p.asIdeal.primeCompl
        (hm (mem_map_of_mem _ (le_derivationIdeal k I hf))) fun δ ↦ ?_
      rw [Derivation.extendOfIsLocalization_algebraMap]
      exact hm (mem_map_of_mem _ (apply_mem_derivationIdeal k δ hf))
    exact_mod_cast hle

/-- Over a characteristic-zero field, at a regular prime of an algebra with finitely generated
projective differentials, `((derivationIdeal k)^[n] I).orderAt p = I.orderAt p - n`
(truncated subtraction in `ℕ∞`). -/
@[simp]
theorem orderAt_derivationIdeal_iterate [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    (I : Ideal R) (p : PrimeSpectrum R) [IsRegularLocalRing (Localization.AtPrime p.asIdeal)]
    (n : ℕ) :
    ((derivationIdeal k)^[n] I).orderAt p = I.orderAt p - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', orderAt_derivationIdeal, ih, tsub_tsub, Nat.cast_succ]

/-- Over a characteristic-zero field, at a regular prime of an algebra with finitely generated
projective differentials, an ideal has order at least `n + 1` precisely when its `n`-th iterated
derivation ideal lies in that prime. -/
theorem natCast_add_one_le_orderAt_iff_iterate_derivationIdeal_le [Module.Projective R Ω[R⁄k]]
    [Module.Finite R Ω[R⁄k]] (I : Ideal R) (p : PrimeSpectrum R)
    [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ I.orderAt p ↔ (derivationIdeal k)^[n] I ≤ p.asIdeal := by
  rw [← one_le_orderAt_iff, orderAt_derivationIdeal_iterate k]
  cases h : I.orderAt p with
  | top => simp
  | coe a =>
    rw [← ENat.natCast_sub]
    norm_cast
    omega

end SmoothCharZero

end Ideal
