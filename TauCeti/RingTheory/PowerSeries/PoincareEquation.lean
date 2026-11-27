/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Integrality of solutions of the functional equation `Y(π X) = π G(Y)`

Let `O` be a local ring, `π` an element of its maximal ideal, and `O → R` an algebra in which `π`
is a nonzerodivisor; the main example is the valuation ring `O` of a nonarchimedean field `R`
such as `ℂ_p`, with `0 < |π| < 1`. For a power series `G = g₁ X + ⋯` over `O` with `g₁` a unit,
a solution `Y ∈ R⟦X⟧` of Poincaré's functional equation

  `Y(π X) = π G(Y)`, `Y(0) = 0`,

has all its coefficients in `O` as soon as its linear coefficient does
(`PowerSeries.exists_map_eq_of_rescale_eq_smul_subst`). Indeed the coefficient of `Xⁿ` in the
equation reads `πⁿ yₙ = π (g₁ yₙ + wₙ)`, where `wₙ` only involves `G` and `y₁, …, yₙ₋₁`; for
`n ≥ 2` the factor `πⁿ⁻¹ - g₁` is a unit of `O`, so `yₙ` is integral when the earlier
coefficients are.

If `G = X - X ^ q + π E` and `Y = H` is a solution over `O` with `H = X + ⋯`, then reducing the
equation modulo `π` gives `H - H ^ q ≡ X` (`PowerSeries.C_dvd_sub_pow_sub_X_of_rescale_eq`).
Over a ring `A` of prime characteristic `p` and for `q = p ^ k`, `k ≥ 1`, the series
`S = ∑_{j ≥ 0} X ^ (q ^ j)` is the only series without constant term with `S - S ^ q = X`
(`PowerSeries.sub_pow_eq_X_iff`): it is a solution since `S ^ q = S(X ^ q)` in characteristic
`p`, and the difference `D` of two solutions satisfies `D = D ^ q`, which forces `D = 0`. Applied
to `A = O ⧸ (π)` when `π ∣ p`, this determines `H` modulo `π`
(`PowerSeries.C_dvd_sub_mk_of_C_dvd_sub_pow_sub_X`).

This is the situation of formal complex multiplication. If a parameter `T = X + ⋯` satisfies
`T(π X) = g(T)` for an integral series `g = π X + b X ^ q + ⋯` containing only the degrees
`≡ 1 (mod q - 1)`, with `b` a unit, then `Y(X) = T(ϖ X) / ϖ` with `ϖ ^ (q - 1) = -π / b`
satisfies `Y(π X) = π G(Y)` with `G = X - X ^ q + π E` and `E` integral, so `Y` is integral and,
when `π ∣ p` and `q` is a power of `p`, reduces to `∑ X ^ (q ^ j)` modulo `π`.

## Main results

* `PowerSeries.exists_map_eq_of_rescale_eq_smul_subst`: a solution of `Y(π X) = π G(Y)` with
  integral linear coefficient is integral.
* `PowerSeries.C_dvd_sub_pow_sub_X_of_rescale_eq`: if `H(π X) = π (H - H ^ q + π E(H))` and
  `H = X + ⋯`, then `H - H ^ q ≡ X` modulo `π`.
* `PowerSeries.exists_map_eq_and_C_dvd_sub_pow_sub_X`: the two combined, for `Y` over `R`.
* `PowerSeries.sub_pow_eq_X_iff`: in characteristic `p`, `S - S ^ (p ^ k) = X` with `S(0) = 0`
  exactly when `S = ∑_j X ^ (p ^ (k j))`.
* `PowerSeries.C_dvd_sub_mk_of_C_dvd_sub_pow_sub_X`: if `π ∣ p`, `S(0) = 0` and
  `S - S ^ (p ^ k) ≡ X` modulo `π`, then `S ≡ ∑_j X ^ (p ^ (k j))` modulo `π`.

## References

* J. Lubin and J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81
  (1965), 380–387.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/CM/FormalGroup/IntegralParameter.lean` (declarations
  `New.mem_range_seriesToCp_of_rescale_eq`, `New.mem_range_seriesToCp_of_rescale_eq_X_sub_X_pow`,
  `New.C_dvd_sub_pow_sub_X_of_rescale_eq`, `New.exists_seriesToCp_eq_of_rescale_eq`,
  `New.dvd_coeff_sub_of_C_dvd_sub_pow_sub_X`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  results here correspond to these declarations, which are stated over `ℂ_p`; the proofs follow
  the outline of that formal proof.
-/

public section

open IsLocalRing

namespace PowerSeries

section Integrality

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]

/-- The induction step for `PowerSeries.exists_map_eq_of_rescale_eq_smul_subst`: if `Y` solves
`Y(π X) = π G(Y)` and its truncation below degree `n ≥ 2` is the image of a series `H` over `O`,
then the coefficient of degree `n` of `Y` lies in `O`. -/
private theorem coeff_mem_range_of_rescale_eq [IsLocalRing O] {π : O} (hπ : π ∈ maximalIdeal O)
    (hπR : IsLeftRegular (algebraMap O R π)) {G : O⟦X⟧} (hG : IsUnit (coeff 1 G)) {Y : R⟦X⟧}
    (hY : rescale (algebraMap O R π) Y = π • G.subst Y) {n : ℕ} (hn : 2 ≤ n) {H : O⟦X⟧}
    (hH₀ : constantCoeff H = 0) (hH : map (algebraMap O R) H = trunc n Y) :
    coeff n Y ∈ Set.range (algebraMap O R) := by
  set c := algebraMap O R
  -- `Y = H + Xⁿ r`, where `r(0) = yₙ`, so `G(Y) = G(H) + Xⁿ s` with `s(0) = g₁ yₙ`
  have hY' : map c H + X ^ n * mk (fun i ↦ coeff (i + n) Y) = Y := by
    rw [hH, add_comm]
    exact (eq_X_pow_mul_shift_add_trunc n Y).symm
  obtain ⟨s, hs, hs₀⟩ := exists_subst_add_X_pow_mul G (a := map c H)
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hH₀, map_zero]) (mk fun i ↦ coeff (i + n) Y) (by omega : n ≠ 0)
  rw [hY', subst_map_algebraMap (.of_constantCoeff_zero' hH₀)] at hs
  -- the coefficient of `Xⁿ` in the equation: `πⁿ yₙ = π (wₙ + g₁ yₙ)`
  have h := congrArg (coeff n) hY
  rw [coeff_rescale, coeff_smul, hs, map_add, coeff_map, coeff_X_pow_mul', Algebra.smul_def] at h
  simp only [le_refl, ite_true, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, hs₀,
    constantCoeff_mk, zero_add] at h
  -- so `(πⁿ⁻¹ - g₁) yₙ = wₙ`, and `πⁿ⁻¹ - g₁` is a unit of `O`
  have key : c (π ^ (n - 1) - coeff 1 G) * coeff n Y = c (coeff n (G.subst H)) := by
    have h' : c π * (c π ^ (n - 1) * coeff n Y) =
        c π * (c (coeff n (G.subst H)) + c (coeff 1 G) * coeff n Y) := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
      exact h
    rw [map_sub, map_pow, sub_mul, hπR h']
    ring
  have hv : IsUnit (π ^ (n - 1) - coeff 1 G) := by
    refine (isUnit_or_isUnit_of_isUnit_add (a := π ^ (n - 1) - coeff 1 G) (b := -π ^ (n - 1))
      ((show -coeff 1 G = π ^ (n - 1) - coeff 1 G + -π ^ (n - 1) by ring) ▸ hG.neg)).resolve_right
      fun hu ↦ ?_
    exact (mem_maximalIdeal _).mp (neg_mem (Ideal.pow_mem_of_mem _ hπ _ (by omega))) hu
  refine ⟨↑hv.unit⁻¹ * coeff n (G.subst H), ?_⟩
  rw [map_mul, ← key, ← mul_assoc, ← map_mul, hv.val_inv_mul, map_one, one_mul]

/-- **Integrality of solutions of `Y(π X) = π G(Y)`.** Let `O` be a local ring, `π` in its maximal
ideal with image in `R` a nonzerodivisor, and `G ∈ O⟦X⟧` with unit linear coefficient. If
`Y ∈ R⟦X⟧` has no constant term, satisfies `Y(π X) = π G(Y)`, and its linear coefficient lies in
`O`, then all its coefficients lie in `O`. -/
theorem exists_map_eq_of_rescale_eq_smul_subst [IsLocalRing O] {π : O}
    (hπ : π ∈ maximalIdeal O) (hπR : IsLeftRegular (algebraMap O R π)) {G : O⟦X⟧}
    (hG : IsUnit (coeff 1 G)) {Y : R⟦X⟧} (hY₀ : constantCoeff Y = 0)
    (hY₁ : coeff 1 Y ∈ Set.range (algebraMap O R))
    (hY : rescale (algebraMap O R π) Y = π • G.subst Y) :
    ∃ H : O⟦X⟧, map (algebraMap O R) H = Y := by
  suffices h : ∀ n, coeff n Y ∈ Set.range (algebraMap O R) by
    choose c hc using h
    exact ⟨mk c, ext fun n ↦ by simp [hc]⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n, ih with
  | 0, _ => exact ⟨0, by simp [hY₀]⟩
  | 1, _ => exact hY₁
  | n + 2, ih =>
    choose c hc using ih
    -- the truncation of `Y` below degree `n + 2`, lifted to `O`
    refine coeff_mem_range_of_rescale_eq hπ hπR hG hY (by omega)
      (H := mk fun i ↦ if h : 0 < i ∧ i < n + 2 then c i h.2 else 0) (by simp) (ext fun i ↦ ?_)
    rcases i with _ | i
    · simp [coeff_trunc, hY₀]
    · by_cases hi : i + 1 < n + 2 <;> simp [coeff_trunc, hi, hc]

/-- **The congruence `H - H ^ q ≡ X` modulo `π`.** If `H = X + ⋯` over `O` satisfies
`H(π X) = π G(H)` with `G = X - X ^ q + π E` and `π` is a nonzerodivisor, then `π` divides every
coefficient of `H - H ^ q - X`. -/
theorem C_dvd_sub_pow_sub_X_of_rescale_eq {π : O} (hπ : IsLeftRegular π) {q : ℕ} {E H : O⟦X⟧}
    (hH₀ : constantCoeff H = 0) (hH₁ : coeff 1 H = 1)
    (h : rescale π H = π • (X - X ^ q + π • E).subst H) : C π ∣ H - H ^ q - X := by
  have hH : HasSubst H := .of_constantCoeff_zero' hH₀
  -- `H(π X) = π X + π² W`, since `H = X + ⋯`
  set W : O⟦X⟧ := mk fun n ↦ if 2 ≤ n then π ^ (n - 2) * coeff n H else 0
  have hres : rescale π H = C π * X + C π * (C π * W) := by
    ext n
    rcases n with _ | _ | n
    · simp [hH₀, W]
    · simp [hH₁, W]
    · simp [W, coeff_rescale, pow_add]
      ring
  rw [hres, subst_add hH, subst_sub hH, subst_smul hH, subst_pow hH, subst_X hH, smul_eq_C_mul,
    smul_eq_C_mul] at h
  -- so `π (H - H ^ q - X) = π (π (W - E(H)))`, and `π` can be cancelled
  refine ⟨W - E.subst H, isSMulRegular_C_iff.mpr hπ.isSMulRegular ?_⟩
  simp only [smul_eq_mul]
  linear_combination -h

/-- **Integrality and the congruence `Y - Y ^ q ≡ X` modulo `π`.** Let `O ⊆ R` with `O` local, `π`
in its maximal ideal a nonzerodivisor in `R`, and `E ∈ O⟦X⟧`. If `Y = X + ⋯` over `R` satisfies
`Y(π X) = π G(Y)` with `G = X - X ^ q + π E`, then `Y` is the image of a series `H` over `O`, and
`π` divides every coefficient of `H - H ^ q - X`. -/
theorem exists_map_eq_and_C_dvd_sub_pow_sub_X [IsLocalRing O] [FaithfulSMul O R] {π : O}
    (hπ : π ∈ maximalIdeal O) (hπR : IsLeftRegular (algebraMap O R π)) {q : ℕ} {E : O⟦X⟧}
    {Y : R⟦X⟧} (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1)
    (hY : rescale (algebraMap O R π) Y = π • (X - X ^ q + π • E).subst Y) :
    ∃ H : O⟦X⟧, map (algebraMap O R) H = Y ∧ C π ∣ H - H ^ q - X := by
  set c := algebraMap O R
  have hinj : Function.Injective c := FaithfulSMul.algebraMap_injective O R
  -- comparing linear coefficients, `G = X - X ^ q + π E` has linear coefficient `1`
  have hG₁ : coeff 1 (X - X ^ q + π • E) = 1 := by
    have h := congrArg (coeff 1) hY
    rw [coeff_rescale, coeff_smul, coeff_one_subst hY₀, hY₁, pow_one, mul_one, mul_one,
      Algebra.smul_def] at h
    have h' : c π * c (coeff 1 (X - X ^ q + π • E)) = c π * c 1 := by rw [map_one, mul_one, ← h]
    exact hinj (hπR h')
  obtain ⟨H, rfl⟩ := exists_map_eq_of_rescale_eq_smul_subst hπ hπR (hG₁ ▸ isUnit_one) hY₀
    ⟨1, by rw [hY₁, map_one]⟩ hY
  have hH₀ : constantCoeff H = 0 := hinj <| by
    rw [map_zero, ← hY₀, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_zero_eq_constantCoeff_apply, coeff_map]
  have hH₁ : coeff 1 H = 1 := hinj (by rw [map_one, ← hY₁, coeff_map])
  have hπO : IsLeftRegular π := fun a b hab ↦ hinj (hπR (by simpa using congrArg c hab))
  refine ⟨H, rfl, C_dvd_sub_pow_sub_X_of_rescale_eq (E := E) hπO hH₀ hH₁ (map_injective _ hinj ?_)⟩
  -- the equation over `R` is the image of the equation over `O`
  rw [← rescale_map, hY, subst_map_algebraMap (.of_constantCoeff_zero' hH₀)]
  ext n
  rw [coeff_smul, coeff_map, coeff_map, coeff_smul, Algebra.smul_def, smul_eq_mul, map_mul]

end Integrality

section CharP

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime] [CharP A p]

/-- For `q ≥ 2`, a natural number is a power of `q` exactly when it is `1` or `q` times a power of
`q`. -/
private theorem mem_range_pow_iff {q : ℕ} (hq : 2 ≤ q) {n : ℕ} :
    n ∈ Set.range (q ^ ·) ↔ n = 1 ∨ q ∣ n ∧ n / q ∈ Set.range (q ^ ·) := by
  simp only [Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro ⟨_ | j, rfl⟩
    · exact .inl (pow_zero q)
    · refine .inr ⟨dvd_pow_self q j.succ_ne_zero, j, ?_⟩
      rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
  · rintro (rfl | ⟨⟨m, rfl⟩, j, hj⟩)
    · exact ⟨0, pow_zero q⟩
    · rw [Nat.mul_div_cancel_left _ (by omega)] at hj
      exact ⟨j + 1, by rw [pow_succ, hj, mul_comm]⟩

/-- In characteristic `p` and for `q = p ^ k ≥ 2`, the series `S = ∑_{j ≥ 0} X ^ (q ^ j)` satisfies
`S - S ^ q = X`: since its coefficients are `0` and `1`, `S ^ q = S(X ^ q) = S - X`. -/
private theorem mk_indicator_sub_pow_eq_X {k : ℕ} (hq : 2 ≤ p ^ k) :
    mk ((Set.range ((p ^ k) ^ ·)).indicator 1) -
      mk ((Set.range ((p ^ k) ^ ·)).indicator 1) ^ p ^ k = (X : A⟦X⟧) := by
  set s := Set.range ((p ^ k) ^ ·)
  set S₀ : A⟦X⟧ := mk (s.indicator 1)
  have hpow : S₀ ^ p ^ k = expand (p ^ k) (by omega) S₀ := by
    rw [← map_iterateFrobenius_expand p hp.out.ne_zero S₀ k]
    ext n
    rw [coeff_map, iterateFrobenius_def]
    have h01 (x : A) (hx : x = 0 ∨ x = 1) : x ^ p ^ k = x := by
      rcases hx with rfl | rfl
      · exact zero_pow (by omega)
      · exact one_pow _
    refine h01 _ ?_
    rw [coeff_expand]
    split_ifs
    · exact s.indicator_eq_zero_or_self 1 _
    · exact .inl rfl
  ext n
  rw [hpow, map_sub, coeff_expand, coeff_X, coeff_mk]
  by_cases hn : n = 1
  · subst hn
    rw [Set.indicator_of_mem (Set.mem_range.mpr ⟨0, pow_zero _⟩), ite_eq_right fun h ↦ by
      have := Nat.le_of_dvd one_pos h; omega, ite_eq_left rfl, sub_zero, Pi.one_apply]
  rw [ite_eq_right hn, sub_eq_zero]
  by_cases hmem : n ∈ s
  · obtain ⟨hd, hdiv⟩ := ((mem_range_pow_iff hq).mp hmem).resolve_left hn
    rw [Set.indicator_of_mem hmem, ite_eq_left hd, coeff_mk, Set.indicator_of_mem hdiv]
    rfl
  · rw [Set.indicator_of_notMem hmem]
    split_ifs with hd
    · rw [coeff_mk, Set.indicator_of_notMem fun h ↦ hmem ((mem_range_pow_iff hq).mpr
        (.inr ⟨hd, h⟩))]
    · rfl

/-- **The series `∑ X ^ (q ^ j)` in characteristic `p`.** Over a ring of prime characteristic `p`,
for `q = p ^ k` with `k ≥ 1`, the series `S = ∑_{j ≥ 0} X ^ (q ^ j)` is the only series without
constant term with `S - S ^ q = X`. -/
theorem sub_pow_eq_X_iff {k : ℕ} (hk : k ≠ 0) {S : A⟦X⟧} (hS₀ : constantCoeff S = 0) :
    S - S ^ p ^ k = X ↔ S = mk ((Set.range ((p ^ k) ^ ·)).indicator 1) := by
  have hq : 2 ≤ p ^ k := hp.out.two_le.trans (Nat.le_self_pow hk p)
  have hsol := mk_indicator_sub_pow_eq_X (A := A) hq
  set S₀ : A⟦X⟧ := mk ((Set.range ((p ^ k) ^ ·)).indicator 1)
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hsol⟩
  -- the difference `D` of two solutions satisfies `D = D ^ q = D ^ (q - 1) * D`
  have hS₀₀ : constantCoeff S₀ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, Set.indicator_of_notMem]
    rintro ⟨j, hj⟩
    exact pow_ne_zero j (by omega) hj
  have : CharP A⟦X⟧ p := charP_of_injective_ringHom C_injective p
  have hD : S - S₀ = (S - S₀) ^ (p ^ k - 1) * (S - S₀) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega), sub_pow_char_pow]
    linear_combination h - hsol
  refine sub_eq_zero.mp (eq_zero_of_self_eq_mul_self ?_ hD)
  rw [map_pow, map_sub, hS₀, hS₀₀, sub_zero, zero_pow (by omega)]

/-- **The congruence `S ≡ ∑ X ^ (q ^ j)` modulo `π`.** Let `π ∈ O` divide the prime `p`, and
`q = p ^ k`. If `S` has no constant term and `S - S ^ q ≡ X` modulo `π`, then
`S ≡ ∑_{j ≥ 0} X ^ (q ^ j)` modulo `π`. -/
theorem C_dvd_sub_mk_of_C_dvd_sub_pow_sub_X {O : Type*} [CommRing O] {π : O} (hπp : π ∣ (p : O))
    {k : ℕ} {S : O⟦X⟧} (hS₀ : constantCoeff S = 0) (hS : C π ∣ S - S ^ p ^ k - X) :
    C π ∣ S - mk ((Set.range ((p ^ k) ^ ·)).indicator 1) := by
  by_cases hπ : IsUnit π
  · exact (hπ.map C).dvd
  -- for `k = 0` the hypothesis would say that `π` divides the linear coefficient `-1` of `-X`
  have hk : k ≠ 0 := by
    rintro rfl
    have h := (C_dvd_iff_dvd_coeff _ _).mp hS 1
    rw [pow_zero, pow_one, sub_self, zero_sub, map_neg, coeff_one_X, dvd_neg] at h
    exact hπ (isUnit_of_dvd_one h)
  -- reduce modulo `π`, a ring of characteristic `p`
  set I := Ideal.span {π}
  have : Nontrivial (O ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have : CharP (O ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact hπp
  rw [C_dvd_iff_map_mk_eq_zero] at hS ⊢
  rw [map_sub, map_sub, map_pow, map_X, sub_eq_zero] at hS
  have hS₀' : constantCoeff (map (Ideal.Quotient.mk I) S) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hS₀,
      map_zero]
  rw [map_sub, (sub_pow_eq_X_iff hk hS₀').mp hS, sub_eq_zero]
  ext n
  rw [coeff_map, coeff_mk, coeff_mk]
  by_cases hn : n ∈ Set.range ((p ^ k) ^ ·)
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, Pi.one_apply, Pi.one_apply, map_one]
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, map_zero]

end CharP

end PowerSeries
