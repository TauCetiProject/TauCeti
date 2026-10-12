/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.DiscPoint

import TauCeti.RingTheory.Huber.Restricted.OneVariable

/-!
# Recognising the points `η_{a,r}` of the closed unit disc

Let `K` be an algebraically closed complete nontrivially normed nonarchimedean field and
`X = Spa (K⟨T⟩, K⟨T⟩°)` the closed unit disc. Wedhorn's Example 7.57 sorts the points of `X` into
five types. The points of types (2) and (3) are the Gauss points `η_{a,r}` of the discs
`D(a, r) = {y : ‖y - a‖ ≤ r}` (`TauCeti.ValuationSpectrum.discPoint`). This file characterises
them among all points of `X` by their values on linear polynomials: a point `x` is `η_{a,r}`
exactly when

* `x(T - a) ≤ x(T - b)` for every `b ∈ D(a, r)`, so `a` minimises `b ↦ x(T - b)` on the disc, and
* `x(T - a)` sits at `r` relative to the constants: `x(T - a) ≤ x(c)` exactly when `r ≤ ‖c‖`,
  and `x(c) ≤ x(T - a)` exactly when `‖c‖ ≤ r`.

The second condition says that `x(T - a)` has the same position in the value group of `x` as the
real number `r` among the norms of `K`. It fails for the rank-two points `η_{a,r⁺}` and `η_{a,r⁻}`
of type (5), whose values on `T - a` are infinitesimally above and below `r`. The first condition
fails for the point `η_{b,s}` with `s < r = ‖b - a‖`, whose value on `T - a` is again `r`.

The proof compares `x` with `η_{a,r}` on polynomials first. Over an algebraically closed field
every polynomial is a constant times a product of linear factors `T - b`. The two conditions give
`x(T - b) = x(T - a)` for `b ∈ D(a, r)` and `x(T - b) = x(b - a)` otherwise, so `x` takes the value
`x(c) x(T - a)^m` on a polynomial on which `η_{a,r}` takes the value `‖c‖ r^m`. Taking `m`-th roots
in `K`, the second condition compares these values as `η_{a,r}` does. Polynomials are dense in
`K⟨T⟩` (`TauCeti.Huber.denseRange_eval₂RingHom_weightedX`) and both points are continuous with
trivial support, so they agree everywhere (`Valuation.IsContinuous.isEquiv_of_dense`). Trivial
support of `x` holds because a point with nonzero support kills some `T - b`
(`TauCeti.ValuationSpectrum.exists_weightedX_sub_weightedC_mem_supp`).

## Main results

* `TauCeti.ValuationSpectrum.eq_discPoint_iff`: a point of the closed unit disc over an
  algebraically closed field is `η_{a,r}` if and only if it satisfies the two conditions above.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [NonarchimedeanRing K] {r : ℝ}

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

/-! ### Points satisfying the two conditions -/

/-- Under the two conditions, `x(T - b)` is `x(T - a)` on the disc `D(a, r)` and `x(b - a)` off
it. -/
private theorem valuation_weightedX_sub_weightedC {x : closedPolydisc 1 K} {a : K}
    (hmin : ∀ b : K, ‖b - a‖ ≤ r → x.1.toValuativeRel.vle (T - C a) (T - C b))
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) (b : K) :
    x.1.valuation (T - C b) =
      if ‖b - a‖ ≤ r then x.1.valuation (T - C a) else x.1.valuation (C (b - a)) := by
  have hsplit : T - C b = (T - C a) - C (b - a) := by
    rw [map_sub]
    ring
  split_ifs with hb
  · refine le_antisymm ?_ ((valuation_le_iff _ _ _).mpr (hmin b hb))
    rw [hsplit]
    exact (Valuation.map_sub _ _ _).trans
      (max_le le_rfl ((valuation_le_iff _ _ _).mpr ((hge _).mpr hb)))
  · rw [hsplit, Valuation.map_sub_eq_of_lt_right]
    exact lt_of_not_ge fun h ↦ hb ((hge _).mp ((valuation_le_iff _ _ _).mp h))

/-- Under the second condition, `x(T - a) ≠ 0`. -/
private theorem valuation_weightedX_sub_weightedC_ne_zero {x : closedPolydisc 1 K} {a : K}
    (hr₀ : 0 < r) (hle : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖) :
    x.1.valuation (T - C a) ≠ 0 := fun h ↦ by
  have := (hle 0).mp ((valuation_le_iff _ _ _).mp (h ▸ zero_le))
  rw [norm_zero] at this
  exact hr₀.not_ge this

variable [IsUltrametricDist K]

/-- A point of the closed unit disc compares constants by their norms. -/
private theorem valuation_weightedC_le_iff (x : closedPolydisc 1 K) (c d : K) :
    x.1.valuation (C c) ≤ x.1.valuation (C d) ↔ ‖c‖ ≤ ‖d‖ := by
  rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff]

/-- Under the second condition, `x(T - a)^k` compares with `x(e)` as `r^k` compares with `‖e‖`:
take a `k`-th root of `e` in `K`. -/
private theorem pow_le_valuation_weightedC_iff_and_valuation_weightedC_le_pow_iff [IsAlgClosed K]
    {x : closedPolydisc 1 K} {a : K} (hr₀ : 0 < r)
    (hle : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖)
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) (e : K) (k : ℕ) :
    (x.1.valuation (T - C a) ^ k ≤ x.1.valuation (C e) ↔ r ^ k ≤ ‖e‖) ∧
      (x.1.valuation (C e) ≤ x.1.valuation (T - C a) ^ k ↔ ‖e‖ ≤ r ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨by simpa using valuation_weightedC_le_iff x 1 e,
      by simpa using valuation_weightedC_le_iff x e 1⟩
  obtain ⟨e, rfl⟩ := IsAlgClosed.exists_pow_nat_eq e hk
  simp only [map_pow, norm_pow, pow_le_pow_iff_left₀ zero_le zero_le hk.ne',
    pow_le_pow_iff_left₀ hr₀.le (norm_nonneg _) hk.ne',
    pow_le_pow_iff_left₀ (norm_nonneg _) hr₀.le hk.ne', valuation_le_iff, hle, hge, and_self]

/-- Under the second condition, for `c ≠ 0` and `n ≤ m`, `x` compares `x(c) x(T - a)^m` and
`x(d) x(T - a)^n`, in both directions, as the reals `‖c‖ r^m` and `‖d‖ r^n` compare. -/
private theorem valuation_mul_pow_le_iff_of_le [IsAlgClosed K] {x : closedPolydisc 1 K} {a : K}
    (hr₀ : 0 < r) (hle : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖)
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) {c : K} (hc : c ≠ 0)
    (d : K) {m n : ℕ} (h : n ≤ m) :
    (x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ≤
        x.1.valuation (C d) * x.1.valuation (T - C a) ^ n ↔ ‖c‖ * r ^ m ≤ ‖d‖ * r ^ n) ∧
      (x.1.valuation (C d) * x.1.valuation (T - C a) ^ n ≤
        x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ↔ ‖d‖ * r ^ n ≤ ‖c‖ * r ^ m) := by
  set γ := x.1.valuation (T - C a)
  -- `m = n + k` and `d = e c`: cancel `x(c) x(T - a)^n` and `‖c‖ r^n`
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨e, rfl⟩ : ∃ e, d = e * c := ⟨d / c, (div_mul_cancel₀ d hc).symm⟩
  have hx : 0 < x.1.valuation (C c) * γ ^ n := by
    refine zero_lt_iff.mpr (mul_ne_zero (fun h0 ↦ hc ?_)
      (pow_ne_zero n (valuation_weightedX_sub_weightedC_ne_zero hr₀ hle)))
    simpa [h0] using valuation_weightedC_le_iff x c 0
  have h₁ : x.1.valuation (C c) * γ ^ (n + k) = x.1.valuation (C c) * γ ^ n * γ ^ k := by
    rw [pow_add, mul_assoc]
  have h₂ : x.1.valuation (C (e * c)) * γ ^ n = x.1.valuation (C c) * γ ^ n *
      x.1.valuation (C e) := by
    rw [map_mul, map_mul]
    ac_rfl
  have h₁' : ‖c‖ * r ^ (n + k) = ‖c‖ * r ^ n * r ^ k := by rw [pow_add, mul_assoc]
  have h₂' : ‖e * c‖ * r ^ n = ‖c‖ * r ^ n * ‖e‖ := by
    rw [norm_mul]
    ring
  simp only [h₁, h₂, h₁', h₂', mul_le_mul_iff_of_pos_left hx,
    mul_le_mul_iff_of_pos_left (mul_pos (norm_pos_iff.mpr hc) (pow_pos hr₀ n))]
  exact pow_le_valuation_weightedC_iff_and_valuation_weightedC_le_pow_iff hr₀ hle hge e k

/-- Under the second condition, `x` compares `x(c) x(T - a)^m` and `x(d) x(T - a)^n` as the reals
`‖c‖ r^m` and `‖d‖ r^n` compare. -/
private theorem valuation_mul_pow_le_iff [IsAlgClosed K] {x : closedPolydisc 1 K} {a : K}
    (hr₀ : 0 < r) (hle : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖)
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) (c d : K) (m n : ℕ) :
    x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ≤
        x.1.valuation (C d) * x.1.valuation (T - C a) ^ n ↔
      ‖c‖ * r ^ m ≤ ‖d‖ * r ^ n := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [map_zero, zero_mul, zero_le, norm_zero, true_iff]
    positivity
  rcases eq_or_ne d 0 with rfl | hd
  · simpa using (valuation_mul_pow_le_iff_of_le hr₀ hle hge hc 0 (Nat.zero_le m)).1
  rcases le_total n m with h | h
  · exact (valuation_mul_pow_le_iff_of_le hr₀ hle hge hc d h).1
  · exact (valuation_mul_pow_le_iff_of_le hr₀ hle hge hd c h).2

variable [CompleteSpace K]

/-- Under the two conditions, on every polynomial `x` takes a value `x(c) x(T - a)^m` where the
Gauss norm of radius `r` about `a` takes the value `‖c‖ r^m`. -/
private theorem exists_valuation_eval₂RingHom_eq [IsAlgClosed K] {x : closedPolydisc 1 K} {a : K}
    (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (hmin : ∀ b : K, ‖b - a‖ ≤ r → x.1.toValuativeRel.vle (T - C a) (T - C b))
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) (p : Polynomial K) :
    ∃ (c : K) (m : ℕ), x.1.valuation (Polynomial.eval₂RingHom C T p) =
        x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ∧
      ((closedDiscGaussValuation hr₀ hr₁).comap (taylorHom (fun _ ↦ a)
        (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha)) (Polynomial.eval₂RingHom C T p) : ℝ) =
        ‖c‖ * r ^ m := by
  set w := (closedDiscGaussValuation hr₀ hr₁).comap
    (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
  -- the claim for a product of linear factors, by induction on the multiset of roots
  have key (s : Multiset K) : ∃ (c : K) (m : ℕ),
      x.1.valuation ((s.map fun b ↦ T - C b).prod) =
        x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ∧
      (w ((s.map fun b ↦ T - C b).prod) : ℝ) = ‖c‖ * r ^ m := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, 0, by simp, by simp⟩
    | cons b s ih =>
      obtain ⟨c, m, h₁, h₂⟩ := ih
      have hw : (w (T - C b) : ℝ) = max r ‖b - a‖ :=
        coe_closedDiscGaussValuation_taylorHom_weightedX_sub_weightedC ha hr₀ hr₁ b
      have hv := valuation_weightedX_sub_weightedC hmin hge b
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, NNReal.coe_mul, h₁, h₂, hw, hv]
      by_cases hb : ‖b - a‖ ≤ r
      · refine ⟨c, m + 1, ?_, ?_⟩
        · simp only [hb, ↓reduceIte, pow_succ]
          ac_rfl
        · rw [max_eq_left hb, pow_succ]
          ring
      · refine ⟨(b - a) * c, m, ?_, ?_⟩
        · simp only [hb, ↓reduceIte, map_mul]
          ac_rfl
        · rw [max_eq_right (not_le.mp hb).le, norm_mul]
          ring
  obtain ⟨c, m, h₁, h₂⟩ := key p.roots
  have hp := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := p))
  have hP : Polynomial.eval₂RingHom C T p =
      C p.leadingCoeff * (p.roots.map fun b ↦ T - C b).prod := by
    conv_lhs => rw [← hp]
    rw [map_mul, map_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  refine ⟨p.leadingCoeff * c, m, ?_, ?_⟩
  · rw [hP, map_mul, h₁, map_mul, map_mul, mul_assoc]
  · rw [hP, map_mul, NNReal.coe_mul, h₂, norm_mul, mul_assoc]
    simp [w]

/-- Under the two conditions, `x` has trivial support: a point with nonzero support kills some
`T - b`, while `x(T - b)` is never zero. -/
private theorem valuation_eq_zero_iff_of_conditions [IsAlgClosed K] {x : closedPolydisc 1 K} {a : K}
    (hr₀ : 0 < r) (hmin : ∀ b : K, ‖b - a‖ ≤ r → x.1.toValuativeRel.vle (T - C a) (T - C b))
    (hle : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖)
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) (f : 𝒯) :
    x.1.valuation f = 0 ↔ f = 0 := by
  suffices hsupp : x.1.supp = ⊥ by
    rw [← Valuation.mem_supp_iff, ← supp_eq_valuation_supp, hsupp, Ideal.mem_bot]
  by_contra hne
  obtain ⟨b, -, hb⟩ := exists_weightedX_sub_weightedC_mem_supp x hne
  rw [supp_eq_valuation_supp, Valuation.mem_supp_iff, valuation_weightedX_sub_weightedC hmin hge]
    at hb
  split_ifs at hb with hba
  · exact valuation_weightedX_sub_weightedC_ne_zero hr₀ hle hb
  · have h0 := valuation_weightedC_le_iff x (b - a) 0
    rw [map_zero, map_zero, le_zero_iff, norm_zero] at h0
    exact hba ((h0.mp hb).trans hr₀.le)

/-! ### The characterisation -/

/-- **The points `η_{a,r}` among the points of the closed unit disc**, over an algebraically closed
complete nonarchimedean field: a point `x` is `η_{a,r}` if and only if `x(T - a) ≤ x(T - b)` for
every `b` with `‖b - a‖ ≤ r`, and `x(T - a)` compares with the constants as `r` compares with their
norms. These are the points of types (2) and (3) in Wedhorn's Example 7.57. -/
theorem eq_discPoint_iff [IsAlgClosed K] (x : closedPolydisc 1 K) {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    x = discPoint a ha hr₀ hr₁ ↔
      (∀ b : K, ‖b - a‖ ≤ r → x.1.toValuativeRel.vle (T - C a) (T - C b)) ∧
      (∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖) ∧
      (∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) := by
  have hG := coe_closedDiscGaussValuation_taylorHom_weightedX_sub_weightedC ha hr₀ hr₁
  constructor
  · rintro rfl
    refine ⟨fun b _ ↦ ?_, fun c ↦ ?_, fun c ↦ ?_⟩ <;>
      simp only [discPoint_vle_iff, ← NNReal.coe_le_coe, hG, taylorHom_weightedC,
        closedDiscGaussValuation_weightedC, coe_nnnorm, sub_self, norm_zero, max_eq_left hr₀.le]
    · exact le_max_left _ _
  rintro ⟨hmin, hle, hge⟩
  set η := discPoint a ha hr₀ hr₁
  have hcont (y : closedPolydisc 1 K) : y.1.valuation.IsContinuous :=
    (ValuationSpectrum.isContinuous_def _).mp ((mem_closedPolydisc_iff 1 K y.1).mp y.2).1
  -- `η` is the Gauss norm of radius `r` composed with the translation `T ↦ T + a`
  set w := (closedDiscGaussValuation hr₀ hr₁).comap
    (taylorHom (fun _ ↦ a) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))
  have hη (f g : 𝒯) : η.1.valuation f ≤ η.1.valuation g ↔ w f ≤ w g := by
    rw [valuation_le_iff, discPoint_vle_iff, Valuation.comap_apply, Valuation.comap_apply]
  have hη0 (f : 𝒯) : η.1.valuation f = 0 ↔ f = 0 := by
    simpa using (valuation_le_iff η.1 f 0).trans (discPoint_vle_zero_iff a ha hr₀ hr₁)
  -- `x` and `η` compare polynomials in the same way, and polynomials are dense
  have hequiv : x.1.valuation.IsEquiv η.1.valuation := by
    refine (hcont x).isEquiv_of_dense (hcont η)
      (fun f ↦ (valuation_eq_zero_iff_of_conditions hr₀ hmin hle hge f).trans (hη0 f).symm)
      (denseRange_eval₂RingHom_weightedX isWeightFamily_one_weight) ?_
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    obtain ⟨c, m, hp, hp'⟩ := exists_valuation_eval₂RingHom_eq ha hr₀ hr₁ hmin hge p
    obtain ⟨d, n, hq, hq'⟩ := exists_valuation_eval₂RingHom_eq ha hr₀ hr₁ hmin hge q
    rw [hη, ← NNReal.coe_le_coe, hp, hq, hp', hq', valuation_mul_pow_le_iff hr₀ hle hge]
  exact Subtype.ext (ext' fun f g ↦ by
    rw [← valuation_le_iff, ← valuation_le_iff]
    exact hequiv f g)

end TauCeti.ValuationSpectrum
