/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.GaussValuation.RootCounting
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.NNRat.Floor
public import TauCeti.NumberTheory.Padics.PadicAlgCl.Valuation
import TauCeti.RingTheory.RootsOfUnity.ValuationAverage
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.RingTheory.Valuation.Polynomial
import TauCeti.RingTheory.Valuation.AddValuation
import TauCeti.Algebra.Order.BigOperators.WithTop

/-!
# Sparse root multiplicities at prime-power cyclotomic radii

The radii `1 / φ(p ^ h)` are eventually below every positive rational radius. Harmonic
averaging gives a bound on the level, independent of degree, at which an integral polynomial
has few roots of that valuation. This supplies degree-free estimates for evaluation at roots of
unity. The final theorem chooses one tuple of roots of bounded order that preserves finitely
many multivariable polynomial values up to any prescribed positive loss.

## Provenance

`Polynomial.exists_isPrimitiveRoot_padicAlgClRealValuation_eval_le_gaussValuation_add` and
`TauCeti.exists_rootsOfUnity_padicAlgClRealValuation_eval_le_add` adapt
`New.Selmer.exists_rootOfUnity_eval_le_gaussVal_add` and
`New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add` in
`src/New/Congruences/Selmer/RootsOfUnity.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The radius definitions, harmonic estimate, sparse-radius
selection, tied-root correction and coordinate induction follow the corresponding helpers
`rootRadius`, `radiusExponents`, `rootRadius_injOn`, `eventually_rootRadius_le`,
`exists_lt_mul_sum_radiusExponents`, `exists_card_rootsOfValuation_mul_le`,
`ellVal_eval_add_card_mul`, `freeCoordinate`, `eval_freeCoordinate`,
`exists_ellVal_eval_update_le_add` and `exists_ellVal_eval_piecewise_le_add` in that namespace.
The implementation uses the native multiplicative Gauss valuation and the untruncated
normalized real valuation on `PadicAlgCl`; these agree with the additive quantities on
integral inputs. The general root-counting and averaging results are in their own modules.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1 (Gauss valuations).
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Chapters 1–2.
-/

@[expose] public section

open scoped NNReal NNRat

noncomputable section

namespace TauCeti

open Finset Polynomial Filter
open scoped NNReal ENNReal NNRat

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (ℓ) in
/-- The number `ρ_h = 1 / φ(ℓ ^ h)`, where `φ` is Euler's totient. For prime `ℓ` and `h ≥ 1`, it is
the valuation `v(ζ - 1)`, normalised by `v ℓ = 1`, for `ζ` of order `ℓ ^ h`. -/
def primePowerRootRadius (h : ℕ) : ℚ≥0 := (Nat.totient (ℓ ^ h) : ℚ≥0)⁻¹

private lemma strictMono_totient_pow_succ : StrictMono fun k : ℕ ↦ Nat.totient (ℓ ^ (k + 1)) := by
  have hℓ : ℓ.Prime := Fact.out
  simp only [Nat.totient_prime_pow_succ hℓ]
  exact (pow_right_strictMono₀ hℓ.one_lt).mul_const (Nat.sub_pos_of_lt hℓ.one_lt)

/-- The radii `primePowerRootRadius ℓ h` with `h ≥ 1` are distinct. -/
lemma primePowerRootRadius_injOn : Set.InjOn (primePowerRootRadius ℓ) (Set.Ici 1) := by
  intro h hh h' hh' h_eq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hh
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hh'
  exact congrArg (· + 1)
    (strictMono_totient_pow_succ.injective (by simpa [primePowerRootRadius] using h_eq))

/-- For `ρ > 0`, all large `h` have `primePowerRootRadius ℓ h = 1 / φ(ℓ ^ h) ≤ ρ`. -/
lemma eventually_primePowerRootRadius_le {ρ : ℚ≥0} (hρ : 0 < ρ) :
    ∀ᶠ h : ℕ in atTop, primePowerRootRadius ℓ h ≤ ρ := by
  filter_upwards [eventually_ge_atTop (⌈ρ⁻¹⌉₊ + 1)] with h hh
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right hh)
  have h_totient : ⌈ρ⁻¹⌉₊ ≤ Nat.totient (ℓ ^ (k + 1)) :=
    (Nat.le_of_succ_le_succ hh).trans strictMono_totient_pow_succ.le_apply
  exact inv_le_of_inv_le₀ hρ ((Nat.le_ceil _).trans (Nat.cast_le.2 h_totient))

variable (ℓ) in
/-- The exponents `h` with `1 ≤ h ≤ h₀` and `ρ_h ≤ ρ`, where `ρ_h = primePowerRootRadius ℓ h`. -/
def primePowerRadiusExponents (ρ : ℚ≥0) (h₀ : ℕ) : Finset ℕ :=
  {h ∈ Icc 1 h₀ | primePowerRootRadius ℓ h ≤ ρ}

omit [Fact ℓ.Prime] in
/-- Membership in the admissible range of prime-power exponents. -/
@[simp]
lemma mem_primePowerRadiusExponents {ρ : ℚ≥0} {h h₀ : ℕ} :
    h ∈ primePowerRadiusExponents ℓ ρ h₀ ↔ 1 ≤ h ∧ h ≤ h₀ ∧ primePowerRootRadius ℓ h ≤ ρ := by
  rw [primePowerRadiusExponents, mem_filter, mem_Icc, and_assoc]

/-- Let `ρ > 0` and `δ > 0`. As the harmonic series diverges, there is an `h₀` such that `δ` times
the sum of `1 / (h + 1)` over `primePowerRadiusExponents ℓ ρ h₀` (the `h` with `1 ≤ h ≤ h₀` and
`primePowerRootRadius ℓ h = 1 / φ(ℓ ^ h) ≤ ρ`) exceeds `B`. -/
lemma exists_lt_mul_sum_primePowerRadiusExponents {ρ : ℚ≥0} {δ : ℝ≥0}
    (hρ : 0 < ρ) (B : ℝ≥0) (hδ : 0 < δ) :
    ∃ h₀ : ℕ, B < δ * ∑ h ∈ primePowerRadiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ h ≥ N, 1 ≤ h ∧ primePowerRootRadius ℓ h ≤ ρ :=
    eventually_atTop.1 ((eventually_ge_atTop 1).and (eventually_primePowerRootRadius_le hρ))
  have h_diverges : ∀ᶠ n : ℕ in atTop,
      (B : ℝ) / δ + ∑ h ∈ range N, 1 / ((h : ℝ) + 1) < ∑ h ∈ range n, 1 / ((h : ℝ) + 1) :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop _
  obtain ⟨h₀, h_large, hNh₀⟩ := (h_diverges.and (eventually_ge_atTop N)).exists
  have h_tail : B / δ < ∑ h ∈ Ico N h₀, ((h : ℝ≥0) + 1)⁻¹ := by
    rw [← sum_range_add_sum_Ico _ hNh₀, add_comm, add_lt_add_iff_left] at h_large
    simpa [← NNReal.coe_lt_coe] using h_large
  have h_subset : Ico N h₀ ⊆ primePowerRadiusExponents ℓ ρ h₀ := fun h hh ↦ by
    obtain ⟨hNh, hh₀⟩ := mem_Ico.1 hh
    exact mem_primePowerRadiusExponents.2 ⟨(hN h hNh).1, hh₀.le, (hN h hNh).2⟩
  exact ⟨h₀, (div_lt_iff₀' hδ).1 (h_tail.trans_le (sum_le_sum_of_subset h_subset))⟩


end TauCeti

namespace Polynomial

open Finset TauCeti
open scoped NNReal NNRat

variable {K : Type*} [CommRing K] [IsDomain K] {ℓ : ℕ} [Fact ℓ.Prime]
  {v : AddValuation K (WithTop ℝ)}

/-- Harmonic averaging finds an admissible prime-power radius with few roots. The bound on a
weighted coefficient is an additive Gauss bound expressed without a new valuation interface.
There is no degree bound and `δ` need not be less than one. -/
theorem exists_card_roots_valuation_mul_le (g : K[X])
    (hcoeff : ∀ i, 0 ≤ v (g.coeff i)) {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0}
    (h_harmonic : B < δ * ∑ h ∈ primePowerRadiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (hbound : ∃ d, v (g.coeff d) + d • ((ρ : ℝ) : WithTop ℝ) ≤ (B : ℝ)) :
    ∃ h ∈ primePowerRadiusExponents ℓ ρ h₀,
      ((g.roots.filter fun a ↦ v a = ((primePowerRootRadius ℓ h : ℝ) : WithTop ℝ)).card : ℝ) *
        (primePowerRootRadius ℓ h : ℝ) ≤ (δ : ℝ) / (h + 1) := by
  classical
  let E := primePowerRadiusExponents ℓ ρ h₀
  let r : ℕ → ℝ := fun h ↦ primePowerRootRadius ℓ h
  have hinj : ∀ h ∈ E, ∀ k ∈ E, r h = r k → h = k := by
    intro h hh k hk heq
    apply primePowerRootRadius_injOn (ℓ := ℓ) (mem_primePowerRadiusExponents.1 hh).1
      (mem_primePowerRadiusExponents.1 hk).1
    dsimp [r] at heq
    exact_mod_cast heq
  obtain ⟨d, hd⟩ := hbound
  have hcount : (∑ h ∈ E,
      ((g.roots.filter fun a ↦ v a = ((r h : ℝ) : WithTop ℝ)).card : ℝ) * r h : ℝ) ≤ B := by
    have H := (g.sum_card_roots_valuation_mul_le (v := v) hcoeff
      (NNRat.cast_nonneg ρ) (E.image r) (by
        intro t ht
        obtain ⟨h, hh, rfl⟩ := mem_image.1 ht
        exact NNRat.cast_le.2 (mem_primePowerRadiusExponents.1 hh).2.2)
      d).trans hd
    rw [sum_image hinj] at H
    exact_mod_cast H
  by_contra! hmany
  have H : (B : ℝ) < δ * ∑ h ∈ E, ((h : ℝ) + 1)⁻¹ := by
    simpa only [E, NNReal.coe_lt_coe, NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_inv,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using (NNReal.coe_lt_coe.2 h_harmonic)
  apply H.not_ge
  calc
    (δ : ℝ) * ∑ h ∈ E, ((h : ℝ) + 1)⁻¹
        = ∑ h ∈ E, (δ : ℝ) / (h + 1) := by rw [mul_sum]; simp only [div_eq_mul_inv]
    _ ≤ ∑ h ∈ E,
        ((g.roots.filter fun a ↦ v a = ((r h : ℝ) : WithTop ℝ)).card : ℝ) * r h :=
      sum_le_sum fun h hh ↦ (hmany h hh).le
    _ ≤ B := hcount

end Polynomial

namespace TauCeti

open Finset Polynomial TauCeti
open scoped NNReal NNRat

variable {p : ℕ} [Fact p.Prime]

-- Local names for the field and its fixed normalized valuation.
local notation "K" => PadicAlgCl p
local notation "V" => padicAlgClRealValuation p

private lemma eval_add_card_tied_roots (g : K[X]) {r : ℝ} {y : K}
    (hy : V y = (r : WithTop ℝ)) :
    V (g.eval y) + (g.roots.filter fun a ↦ V a = (r : WithTop ℝ)).card • (r : WithTop ℝ) =
      V g.leadingCoeff + (g.roots.map fun a ↦ min (r : WithTop ℝ) (V a)).sum +
        ((g.roots.filter fun a ↦ V a = (r : WithTop ℝ)).map fun a ↦ V (y - a)).sum := by
  classical
  let R := g.roots.filter fun a ↦ V a = (r : WithTop ℝ)
  let R' := g.roots.filter fun a ↦ ¬V a = (r : WithTop ℝ)
  have hsplit : g.roots = R + R' := (Multiset.filter_add_not _ _).symm
  have hother : ∀ a ∈ R', V (y - a) = min (r : WithTop ℝ) (V a) := by
    intro a ha
    rw [sub_eq_add_neg, (V).map_add_of_distinct_val (by
      rw [hy, (V).map_neg]
      exact Ne.symm (Multiset.mem_filter.1 ha).2), hy, (V).map_neg]
  have hsame : ∀ a ∈ R, min (r : WithTop ℝ) (V a) = r := by
    intro a ha
    rw [(Multiset.mem_filter.1 ha).2, min_self]
  have heval : V (g.eval y) =
      V g.leadingCoeff + (g.roots.map fun a ↦ V (y - a)).sum :=
    valuation_eval_eq_mul_prod_roots (V).toValuation g (IsAlgClosed.splits _) y
  have heval' : V (g.eval y) = V g.leadingCoeff +
      ((R.map fun a ↦ V (y - a)).sum + (R'.map fun a ↦ min (r : WithTop ℝ) (V a)).sum) := by
    conv_lhs => rw [heval, hsplit]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl hother]
  have hgauss : (g.roots.map fun a ↦ min (r : WithTop ℝ) (V a)).sum =
      R.card • (r : WithTop ℝ) + (R'.map fun a ↦ min (r : WithTop ℝ) (V a)).sum := by
    conv_lhs => rw [hsplit]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl hsame,
      Multiset.map_const', Multiset.sum_replicate]
  rw [heval', hgauss]
  ac_rfl

private lemma exists_isPrimitiveRoot_eval_le_gauss_add
    {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : B < δ * ∑ h ∈ primePowerRadiusExponents p ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (g : K[X]) (hcoeff : ∀ i, 0 ≤ V (g.coeff i))
    (hG : (g.gaussValuation (V).toValuation
      (.ofAdd (.toDual ((ρ : ℝ) : WithTop ℝ)))).toAdd.ofDual ≤ (B : ℝ)) :
    ∃ h ∈ primePowerRadiusExponents p ρ h₀, ∃ ζ : K, IsPrimitiveRoot ζ (p ^ h) ∧
      V (g.eval (ζ - 1)) ≤ (g.gaussValuation (V).toValuation
        (.ofAdd (.toDual ((primePowerRootRadius p h : ℝ) : WithTop ℝ)))).toAdd.ofDual +
          (δ : ℝ) := by
  classical
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  let r : Multiplicative (WithTop ℝ)ᵒᵈ := .ofAdd (.toDual ((ρ : ℝ) : WithTop ℝ))
  have hne : g.gaussValuation (V).toValuation r ≠ 0 := by
    intro hz
    have H := hG
    dsimp only [r] at hz
    rw [hz] at H
    exact (WithTop.not_top_le_coe _) H
  obtain ⟨d, _, hd⟩ := exists_eq_gaussValuation (V).toValuation r hne
  have hbound : ∃ d, V (g.coeff d) + d • ((ρ : ℝ) : WithTop ℝ) ≤ (B : ℝ) := by
    refine ⟨d, ?_⟩
    rw [← hd] at hG
    exact hG
  obtain ⟨h, hh, hfew⟩ := g.exists_card_roots_valuation_mul_le (v := V)
    hcoeff h_harmonic hbound
  let R := g.roots.filter fun a ↦ V a = ((primePowerRootRadius p h : ℝ) : WithTop ℝ)
  have hrpos : 0 < (primePowerRootRadius p h : ℝ) := by
    simp only [primePowerRootRadius, NNRat.cast_inv, NNRat.cast_natCast]
    exact inv_pos.2 (Nat.cast_pos.2 (Nat.totient_pos.2
      (pow_pos (Fact.out : p.Prime).pos _)))
  have hcost : (R.card : ℝ) * (Nat.totient (p ^ h) : ℝ)⁻¹ * (h + 1) ≤ (δ : ℝ) := by
    have H := (le_div_iff₀ (by positivity : (0 : ℝ) < h + 1)).1 hfew
    simpa only [R, primePowerRootRadius, NNRat.cast_inv, NNRat.cast_natCast] using H
  obtain ⟨ζ, hζ, hsum⟩ := (V).exists_isPrimitiveRoot_sum_sub_le (padicAlgClRealValuation_p p) h
    (by exact_mod_cast hδ) hcost
  have hy : V (ζ - 1) = ((primePowerRootRadius p h : ℝ) : WithTop ℝ) :=
    by
      simpa only [primePowerRootRadius, NNRat.cast_inv, NNRat.cast_natCast] using
        padicAlgClRealValuation_sub_one p (mem_primePowerRadiusExponents.1 hh).1 hζ
  refine ⟨h, hh, ζ, hζ, ?_⟩
  have htied := eval_add_card_tied_roots g hy
  have hgauss : (g.gaussValuation (V).toValuation
      (.ofAdd (.toDual ((primePowerRootRadius p h : ℝ) : WithTop ℝ)))).toAdd.ofDual =
        V g.leadingCoeff + (g.roots.map fun a ↦
          min ((primePowerRootRadius p h : ℝ) : WithTop ℝ) (V a)).sum :=
    gaussValuation_eq_mul_prod_roots (V).toValuation g (IsAlgClosed.splits _) _
  rw [hgauss]
  calc
    V (g.eval (ζ - 1)) ≤ V (g.eval (ζ - 1)) + R.card •
        ((primePowerRootRadius p h : ℝ) : WithTop ℝ) :=
      le_add_of_nonneg_right (nsmul_nonneg (by exact_mod_cast hrpos.le) _)
    _ = V g.leadingCoeff + (g.roots.map fun a ↦
          min ((primePowerRootRadius p h : ℝ) : WithTop ℝ) (V a)).sum +
          (R.map fun a ↦ V (ζ - 1 - a)).sum := htied
    _ ≤ V g.leadingCoeff + (g.roots.map fun a ↦
          min ((primePowerRootRadius p h : ℝ) : WithTop ℝ) (V a)).sum + (δ : ℝ) := by
      exact add_le_add le_rfl hsum

private lemma exists_integer_root_eval_le_gauss_add
    {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : B < δ * ∑ h ∈ primePowerRadiusExponents p ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (g : (V).toValuation.valuationSubring[X])
    (hG : ((g.map (V).toValuation.valuationSubring.subtype).gaussValuation (V).toValuation
      (.ofAdd (.toDual ((ρ : ℝ) : WithTop ℝ)))).toAdd.ofDual ≤ (B : ℝ)) :
    ∃ h ∈ primePowerRadiusExponents p ρ h₀, ∃ ζ : (V).toValuation.valuationSubring,
      ζ ^ p ^ h₀ = 1 ∧
      V ((ζ - 1 : (V).toValuation.valuationSubring) : K) =
        ((primePowerRootRadius p h : ℝ) : WithTop ℝ) ∧
      V (↑(g.eval (ζ - 1)) : K) ≤
        ((g.map (V).toValuation.valuationSubring.subtype).gaussValuation (V).toValuation
          (.ofAdd (.toDual ((primePowerRootRadius p h : ℝ) : WithTop ℝ)))).toAdd.ofDual +
            (δ : ℝ) := by
  let O := (V).toValuation.valuationSubring
  let e : O →+* K := O.subtype
  have hcoeff : ∀ k, 0 ≤ V ((g.map e).coeff k) := by
    intro k
    rw [coeff_map]
    exact (g.coeff k).property
  obtain ⟨h, hh, ξ, hξ, hbound⟩ :=
    exists_isPrimitiveRoot_eval_le_gauss_add hδ h_harmonic (g.map e) hcoeff hG
  obtain ⟨hone, hh₀, _⟩ := mem_primePowerRadiusExponents.1 hh
  have hy : V (ξ - 1) = ((primePowerRootRadius p h : ℝ) : WithTop ℝ) := by
    simpa only [primePowerRootRadius, NNRat.cast_inv, NNRat.cast_natCast] using
      padicAlgClRealValuation_sub_one p hone hξ
  let y : O := ⟨ξ - 1, by
    have H : 0 ≤ V (ξ - 1) := by rw [hy]; exact_mod_cast (primePowerRootRadius p h).coe_nonneg
    exact H⟩
  let ζ : O := 1 + y
  have hζ : (ζ : K) = ξ := by simp [ζ, y]
  have hζy : ζ - 1 = y := by simp [ζ]
  have hpow : ζ ^ p ^ h₀ = 1 := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, hζ]
    obtain ⟨k, hk⟩ := pow_dvd_pow p hh₀
    rw [hk, pow_mul, hξ.pow_eq_one, one_pow]
  refine ⟨h, hh, ζ, hpow, ?_, ?_⟩
  · rw [hζy]
    exact hy
  · have heval : (g.map e).eval (y : K) = (↑(g.eval y) : K) := eval_map_apply e y
    rw [hζy, ← heval]
    exact hbound

private lemma exists_root_eval_family_le_add {ι : Type*} [Fintype ι]
    {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : B < δ * ∑ h ∈ primePowerRadiusExponents p ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (g : ι → (V).toValuation.valuationSubring[X]) (x : ι → (V).toValuation.valuationSubring)
    (hx : ∀ i, ((ρ : ℝ) : WithTop ℝ) ≤ V (x i : K))
    (hP : ∑ i, V (↑((g i).eval (x i)) : K) ≤ (B : ℝ)) :
    ∃ ζ : (V).toValuation.valuationSubring,
      ζ ^ p ^ h₀ = 1 ∧ V ((ζ - 1 : (V).toValuation.valuationSubring) : K) ≤ (ρ : ℝ) ∧
      (∀ i, V (↑((g i).eval (ζ - 1)) : K) ≤ V (↑((g i).eval (x i)) : K) + (δ : ℝ)) ∧
      ∑ i, V (↑((g i).eval (ζ - 1)) : K) ≤ ∑ i, V (↑((g i).eval (x i)) : K) + (δ : ℝ) := by
  classical
  let O := (V).toValuation.valuationSubring
  let e : O →+* K := O.subtype
  let G (r : ℚ≥0) (P : O[X]) : WithTop ℝ :=
    ((P.map e).gaussValuation (V).toValuation
      (.ofAdd (.toDual ((r : ℝ) : WithTop ℝ)))).toAdd.ofDual
  have hprod (r : ℚ≥0) : G r (∏ i, g i) = ∑ i, G r (g i) := by
    dsimp only [G]
    rw [Polynomial.map_prod, Finset.prod_eq_multiset_prod, gaussValuation_multiset_prod]
    simp only [Finset.sum_eq_multiset_sum, Multiset.map_map, Function.comp_def]
    rfl
  have heval (r : ℚ≥0) (P : O[X]) (y : O)
      (hy : ((r : ℝ) : WithTop ℝ) ≤ V (y : K)) : G r P ≤ V (↑(P.eval y) : K) := by
    have H := valuation_eval_le_gaussValuation (V).toValuation
      (.ofAdd (.toDual ((r : ℝ) : WithTop ℝ))) (P.map e) hy
    have heval' : (P.map e).eval (y : K) = (↑(P.eval y) : K) := eval_map_apply e y
    rw [heval'] at H
    exact H
  have hG : G ρ (∏ i, g i) ≤ (B : ℝ) := by
    rw [hprod]
    exact (sum_le_sum fun i _ ↦ heval ρ (g i) (x i) (hx i)).trans hP
  obtain ⟨h, hh, ζ, hpow, hy, hbound⟩ :=
    exists_integer_root_eval_le_gauss_add hδ h_harmonic (∏ i, g i) hG
  have hrρ := (mem_primePowerRadiusExponents.1 hh).2.2
  have hold (i : ι) : G (primePowerRootRadius p h) (g i) ≤ V (↑((g i).eval (x i)) : K) :=
    heval _ _ _ ((show ((primePowerRootRadius p h : ℝ) : WithTop ℝ) ≤
      ((ρ : ℝ) : WithTop ℝ) by exact_mod_cast hrρ).trans (hx i))
  have hnew (i : ι) : G (primePowerRootRadius p h) (g i) ≤ V (↑((g i).eval (ζ - 1)) : K) :=
    heval _ _ _ hy.ge
  have hsum : ∑ i, V (↑((g i).eval (ζ - 1)) : K) ≤
      ∑ i, G (primePowerRootRadius p h) (g i) + (δ : ℝ) := by
    have heprod : (↑(∏ i, (g i).eval (ζ - 1)) : K) = ∏ i, (↑((g i).eval (ζ - 1)) : K) :=
      _root_.map_prod O.subtype (fun i ↦ (g i).eval (ζ - 1)) univ
    have H : V (↑((∏ i, g i).eval (ζ - 1)) : K) ≤
        G (primePowerRootRadius p h) (∏ i, g i) + (δ : ℝ) := hbound
    rw [eval_prod, heprod, AddValuation.map_prod, hprod] at H
    exact H
  have hcomp := sum_le_sum fun i (_ : i ∈ univ) ↦ hold i
  have hfinite : ∑ i, G (primePowerRootRadius p h) (g i) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hcomp.trans hP)
  refine ⟨ζ, hpow, hy.le.trans (by exact_mod_cast hrρ), fun i ↦ ?_, ?_⟩
  · exact (Finset.le_add_of_sum_le_sum_add univ (fun i _ ↦ hnew i) hfinite hsum i
      (mem_univ i)).trans (add_le_add (hold i) le_rfl)
  · exact hsum.trans (add_le_add hcomp le_rfl)

private lemma exists_root_eval_update_le_add {σ ι : Type*} [DecidableEq σ] [Fintype ι]
    {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : B < δ * ∑ h ∈ primePowerRadiusExponents p ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (P : ι → MvPolynomial σ (V).toValuation.valuationSubring)
    {x : ι → σ → (V).toValuation.valuationSubring} {j : σ}
    (hx : ∀ i, ((ρ : ℝ) : WithTop ℝ) ≤ V (x i j : K))
    (hP : ∑ i, V (↑(MvPolynomial.eval (x i) (P i)) : K) ≤ (B : ℝ)) :
    ∃ ζ : (V).toValuation.valuationSubring,
      ζ ^ p ^ h₀ = 1 ∧ V ((ζ - 1 : (V).toValuation.valuationSubring) : K) ≤ (ρ : ℝ) ∧
      (∀ i, V (↑(MvPolynomial.eval (Function.update (x i) j (ζ - 1)) (P i)) : K) ≤
        V (↑(MvPolynomial.eval (x i) (P i)) : K) + (δ : ℝ)) ∧
      ∑ i, V (↑(MvPolynomial.eval (Function.update (x i) j (ζ - 1)) (P i)) : K) ≤
        ∑ i, V (↑(MvPolynomial.eval (x i) (P i)) : K) + (δ : ℝ) := by
  let O := (V).toValuation.valuationSubring
  let g : ι → O[X] := fun i ↦
    MvPolynomial.aeval (Function.update (fun k ↦ C (x i k)) j X) (P i)
  have heval (i : ι) (y : O) :
      (g i).eval y = MvPolynomial.eval (Function.update (x i) j y) (P i) := by
    dsimp only [g]
    rw [← coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
    refine congrArg (MvPolynomial.eval · (P i)) (funext fun k ↦ ?_)
    by_cases hk : k = j <;> simp [hk]
  have hold (i : ι) : (g i).eval (x i j) = MvPolynomial.eval (x i) (P i) := by
    rw [heval, Function.update_eq_self]
  obtain ⟨ζ, hpow, hval, heach, hsum⟩ :=
    exists_root_eval_family_le_add hδ h_harmonic g (fun i ↦ x i j)
    hx (by simpa only [hold] using hP)
  exact ⟨ζ, hpow, hval, by simpa only [hold, heval, Function.update_eq_self] using heach,
    by simpa only [hold, heval, Function.update_eq_self] using hsum⟩

private lemma exists_root_eval_piecewise_le_add {σ ι : Type*}
    [DecidableEq σ] [Fintype σ] [Fintype ι]
    {ρ : ℚ≥0} {h₀ : ℕ} {β δ : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : β + 1 < δ * ∑ h ∈ primePowerRadiusExponents p ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (hσ : Fintype.card σ * δ ≤ 1)
    (P : ι → MvPolynomial σ (V).toValuation.valuationSubring)
    {x : ι → σ → (V).toValuation.valuationSubring}
    (hx : ∀ i j, ((ρ : ℝ) : WithTop ℝ) ≤ V (x i j : K))
    (hP : ∑ i, V (↑(MvPolynomial.eval (x i) (P i)) : K) ≤ (β : ℝ)) (t : Finset σ) :
    ∃ ζ : σ → (V).toValuation.valuationSubring,
      (∀ j ∈ t, ζ j ^ p ^ h₀ = 1) ∧
      (∀ j ∈ t, V ((ζ j - 1 : (V).toValuation.valuationSubring) : K) ≤ (ρ : ℝ)) ∧
      (∀ i, V (↑(MvPolynomial.eval (t.piecewise (fun j ↦ ζ j - 1) (x i)) (P i)) : K) ≤
        V (↑(MvPolynomial.eval (x i) (P i)) : K) + t.card • ((δ : ℝ) : WithTop ℝ)) ∧
      ∑ i, V (↑(MvPolynomial.eval (t.piecewise (fun j ↦ ζ j - 1) (x i)) (P i)) : K) ≤
        (β : ℝ) + t.card • ((δ : ℝ) : WithTop ℝ) := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp, by simp, by simpa using hP⟩
  | insert j t hj ih =>
    obtain ⟨ζ, hpow, hval, heach, hsum⟩ := ih
    let y := fun i ↦ t.piecewise (fun k ↦ ζ k - 1) (x i)
    have hloss : (t.card * δ : ℝ≥0) ≤ 1 :=
      (mul_le_mul_left (Nat.cast_le.2 (card_le_univ t)) δ).trans hσ
    have hloss' : t.card • ((δ : ℝ) : WithTop ℝ) ≤ 1 := by
      rw [← WithTop.coe_nsmul]
      norm_cast
      simpa only [nsmul_eq_mul] using hloss
    have hbelow : ∑ i, V (↑(MvPolynomial.eval (y i) (P i)) : K) ≤ ((β + 1 : ℝ≥0) : ℝ) := by
      simpa only [NNReal.coe_add, NNReal.coe_one, WithTop.coe_add, WithTop.coe_one] using
        hsum.trans (add_le_add (le_refl ((β : ℝ) : WithTop ℝ)) hloss')
    obtain ⟨ξ, hξpow, hξval, heachstep, hsumstep⟩ :=
      exists_root_eval_update_le_add hδ h_harmonic P
      (j := j) (fun i ↦ by simpa [y, hj] using hx i j) hbelow
    have hold : ∀ k ∈ t, Function.update ζ j ξ k = ζ k :=
      fun k hk ↦ Function.update_of_ne (ne_of_mem_of_not_mem hk hj) ξ ζ
    have hpoint (i : ι) :
        (insert j t).piecewise (fun k ↦ Function.update ζ j ξ k - 1) (x i) =
          Function.update (y i) j (ξ - 1) := by
      rw [piecewise_insert, Function.update_self,
        piecewise_congr t (fun k hk ↦ by rw [hold k hk]) fun _ _ ↦ rfl]
    have hcard : (insert j t).card • ((δ : ℝ) : WithTop ℝ) =
        t.card • ((δ : ℝ) : WithTop ℝ) + (δ : ℝ) := by
      simp [hj, add_nsmul]
    refine ⟨Function.update ζ j ξ, ?_, ?_, fun i ↦ ?_, ?_⟩
    · simp +contextual [hold, hξpow, hpow]
    · rw [forall_mem_insert, Function.update_self]
      exact ⟨hξval, fun k hk ↦ by simpa only [hold k hk] using hval k hk⟩
    · rw [hpoint, hcard, ← add_assoc]
      exact (heachstep i).trans (add_le_add (heach i) le_rfl)
    · simp only [hpoint, hcard, ← add_assoc]
      exact hsumstep.trans (add_le_add hsum le_rfl)

private lemma exists_roots_eval_le_add
    (s₀ : ℕ) {ρ : ℚ≥0} (hρ : 0 < ρ) (β : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ (σ ι : Type) [Fintype σ] [Fintype ι]
      (P : ι → MvPolynomial σ (V).toValuation.valuationSubring)
      (x : ι → σ → (V).toValuation.valuationSubring),
      Fintype.card σ ≤ s₀ →
      (∀ i j, ((ρ : ℝ) : WithTop ℝ) ≤ V (x i j : K)) →
      ∑ i, V (↑(MvPolynomial.eval (x i) (P i)) : K) ≤ (β : ℝ) →
      ∃ ζ : σ → (V).toValuation.valuationSubring,
        (∀ j, ζ j ^ p ^ h₀ = 1) ∧
        (∀ j, V ((ζ j - 1 : (V).toValuation.valuationSubring) : K) ≤ (ρ : ℝ)) ∧
        ∀ i, V (↑(MvPolynomial.eval (fun j ↦ ζ j - 1) (P i)) : K) ≤
          V (↑(MvPolynomial.eval (x i) (P i)) : K) + (ε : ℝ) := by
  classical
  let δ : ℝ≥0 := min ε 1 / (s₀ + 2)
  have hpos : (0 : ℝ≥0) < s₀ + 2 := by positivity
  have hδ : δ < 1 :=
    (div_lt_one hpos).2 ((min_le_right ε 1).trans_lt (one_lt_two.trans_le le_add_self))
  obtain ⟨h₀, hharmonic⟩ := exists_lt_mul_sum_primePowerRadiusExponents (ℓ := p) hρ
    (β + 1) (show 0 < δ by positivity)
  refine ⟨h₀, fun σ ι _ _ P x hσ hx hP ↦ ?_⟩
  have hloss : (Fintype.card σ * δ : ℝ≥0) ≤ min ε 1 := by
    calc
      (Fintype.card σ * δ : ℝ≥0) ≤ (s₀ + 2) * δ :=
        mul_le_mul_left (le_add_right (by exact_mod_cast hσ)) δ
      _ = min ε 1 := mul_div_cancel₀ (min ε 1) hpos.ne'
  obtain ⟨hlossε, hlossone⟩ := le_min_iff.1 hloss
  have hloss' : Fintype.card σ • ((δ : ℝ) : WithTop ℝ) ≤ (ε : ℝ) := by
    rw [← WithTop.coe_nsmul]
    norm_cast
    simpa only [nsmul_eq_mul] using hlossε
  obtain ⟨ζ, hpow, hval, heach, _⟩ :=
    exists_root_eval_piecewise_le_add hδ hharmonic hlossone P hx hP univ
  refine ⟨ζ, fun j ↦ hpow j (mem_univ j), fun j ↦ hval j (mem_univ j), fun i ↦ ?_⟩
  have H := heach i
  simp only [piecewise_univ, card_univ] at H
  exact H.trans (add_le_add le_rfl hloss')

end TauCeti

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- Given a bound on the number of variables, a positive rational input radius, a bound on the
sum of the input valuations, and a positive error, choose one bound on the orders of roots of
unity before the finite polynomial family is given. One tuple of roots of those bounded orders
loses at most the specified error against every given polynomial value. -/
theorem exists_rootsOfUnity_padicAlgClRealValuation_eval_le_add (s₀ : ℕ) {ρ : ℚ≥0}
    (hρ : 0 < ρ) (β : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) :
    let v := padicAlgClRealValuation p
    let O := v.toValuation.valuationSubring
    ∃ h₀ : ℕ, ∀ (σ ι : Type) [Fintype σ] [Fintype ι]
      (P : ι → MvPolynomial σ O) (x : ι → σ → O),
      Fintype.card σ ≤ s₀ →
      (∀ i j, ((ρ : ℝ) : WithTop ℝ) ≤ v (x i j : PadicAlgCl p)) →
      ∑ i, v (↑(MvPolynomial.eval (x i) (P i)) : PadicAlgCl p) ≤ (β : ℝ) →
      ∃ ζ : σ → O,
        (∀ j, ζ j ^ p ^ h₀ = 1) ∧
        (∀ j, v ((ζ j - 1 : O) : PadicAlgCl p) ≤ (ρ : ℝ)) ∧
        ∀ i, v (↑(MvPolynomial.eval (fun j ↦ ζ j - 1) (P i)) : PadicAlgCl p) ≤
          v (↑(MvPolynomial.eval (x i) (P i)) : PadicAlgCl p) + (ε : ℝ) := by
  exact exists_roots_eval_le_add s₀ hρ β hε

end TauCeti

namespace Polynomial

open TauCeti
variable {p : ℕ} [Fact p.Prime]

/-- The harmonic-sum estimate: an integral polynomial with bounded Gauss valuation has a
primitive root of unity at an admissible level where evaluation at the root minus one loses
at most `δ` against the Gauss valuation at that level. Both Gauss valuations use the native
multiplicative API, read additively by `toAdd.ofDual`. -/
theorem exists_isPrimitiveRoot_padicAlgClRealValuation_eval_le_gaussValuation_add
    (g : (PadicAlgCl p)[X]) {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : B < δ * ∑ h ∈ primePowerRadiusExponents p ρ h₀, ((h : ℝ≥0) + 1)⁻¹) :
    let v := padicAlgClRealValuation p
    (∀ i, 0 ≤ v (g.coeff i)) →
    (g.gaussValuation v.toValuation
      (.ofAdd (.toDual ((ρ : ℝ) : WithTop ℝ)))).toAdd.ofDual ≤ (B : ℝ) →
    ∃ h ∈ primePowerRadiusExponents p ρ h₀, ∃ ζ : PadicAlgCl p,
      IsPrimitiveRoot ζ (p ^ h) ∧ v (g.eval (ζ - 1)) ≤
        (g.gaussValuation v.toValuation
          (.ofAdd (.toDual ((primePowerRootRadius p h : ℝ) : WithTop ℝ)))).toAdd.ofDual +
          (δ : ℝ) := by
  exact TauCeti.exists_isPrimitiveRoot_eval_le_gauss_add hδ h_harmonic g

end Polynomial
