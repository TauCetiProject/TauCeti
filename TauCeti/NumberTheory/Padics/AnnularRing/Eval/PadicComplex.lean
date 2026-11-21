/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.NumberTheory.Padics.AnnularRing.Eval.Basic
import TauCeti.Analysis.Normed.Group.NullFamily
import TauCeti.NumberTheory.Padics.Complex.Valuation

/-!
# Joint injectivity of `ℂ_[p]`-evaluations on the open annulus

Over `ℂ_[p]`, whose value group is `p ^ ℚ`, the family of annulus evaluations
`TauCeti.AnnularRing.evalAt t` and `TauCeti.AnnularRing.localizedEvalAt t` at all `t : ℂ_[p]` with
`p⁻¹ < ‖t‖ < 1` is jointly injective on both `H = TauCeti.AnnularRing p` and `H[1/T]`.

## Main results

* `TauCeti.AnnularRing.eq_zero_of_forall_evalAt_padicComplex_eq_zero`,
  `TauCeti.AnnularRing.eq_of_forall_evalAt_padicComplex_eq`: joint injectivity on `H`.
* `TauCeti.AnnularRing.eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero`,
  `TauCeti.AnnularRing.eq_of_forall_localizedEvalAt_padicComplex_eq`: joint injectivity on `H[1/T]`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

namespace TauCeti.AnnularRing

variable {p : ℕ} [Fact p.Prime]

private theorem one_lt_p : (1 : ℝ) < p :=
  mod_cast (Fact.out : p.Prime).one_lt

private theorem p_pos : (0 : ℝ) < p :=
  zero_lt_one.trans one_lt_p

/-- On the sub-annulus `q ∈ [1/4, 3/4]` (where `r = p ^ (-q)`), every term `‖x.coeff m‖ * r ^ m`
is uniformly bounded by `(p ^ (-1/4)) ^ |m|`. -/
private theorem norm_coeff_mul_rpow_le_of_mem_Icc (x : AnnularRing p) {q : ℚ}
    (hq₁ : (1 / 4 : ℚ) ≤ q) (hq₂ : q ≤ 3 / 4) (m : ℤ) :
    ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m ≤ ((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ m.natAbs := by
  have hp0 : (0 : ℝ) ≤ p := (p_pos (p := p)).le
  have hq₁' : (1 / 4 : ℝ) ≤ (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₁
  have hq₂' : (q : ℝ) ≤ 3 / 4 := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₂
  rw [← Real.rpow_intCast, ← Real.rpow_mul hp0, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
  rcases le_or_gt 0 m with hm | hm
  · have habs : (m.natAbs : ℝ) = (m : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hm]
    have _ : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    calc ‖x.coeff m‖ * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ))
        ≤ 1 * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (Real.rpow_nonneg hp0 _)
      _ = (p : ℝ) ^ (-(q : ℝ) * (m : ℝ)) := one_mul _
      _ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ) * (m.natAbs : ℝ)) := by
          rw [habs]
          exact Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le (by nlinarith)
  · have habs : (m : ℝ) = -(m.natAbs : ℝ) := by
      have : m = -(m.natAbs : ℤ) := by omega
      exact_mod_cast this
    have hcoeff : ‖x.coeff m‖ ≤ (p : ℝ) ^ (m : ℝ) := by
      have := x.norm_coeff_le m
      rwa [min_eq_right hm.le, ← Real.rpow_intCast] at this
    calc ‖x.coeff m‖ * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ))
        ≤ (p : ℝ) ^ (m : ℝ) * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hp0 _)
      _ = (p : ℝ) ^ ((m : ℝ) + -(q : ℝ) * (m : ℝ)) := (Real.rpow_add (p_pos (p := p)) _ _).symm
      _ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ) * (m.natAbs : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le ?_
          rw [habs]
          nlinarith

/-- Uniform positive lower bound on `‖x.coeff m₀‖ * (p ^ (-q)) ^ m₀` over `q ∈ [1/4, 3/4]`. -/
private theorem min_rpow_le_rpow_zpow {q : ℚ} (hq₁ : (1 / 4 : ℚ) ≤ q) (hq₂ : q ≤ 3 / 4) (m : ℤ) :
    min (((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ m) (((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ m) ≤
      ((p : ℝ) ^ (-(q : ℝ))) ^ m := by
  have hp0 : (0 : ℝ) ≤ p := (p_pos (p := p)).le
  have h1p : (1 : ℝ) < p := one_lt_p (p := p)
  have hq₁' : (1 / 4 : ℝ) ≤ (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₁
  have hq₂' : (q : ℝ) ≤ 3 / 4 := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₂
  rcases le_or_gt 0 m with hm | hm
  · refine (min_le_left _ _).trans ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul hp0, ← Real.rpow_intCast, ← Real.rpow_mul hp0]
    have _ : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    exact Real.rpow_le_rpow_of_exponent_le h1p.le (by nlinarith)
  · refine (min_le_right _ _).trans ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul hp0, ← Real.rpow_intCast, ← Real.rpow_mul hp0]
    have _ : (m : ℝ) ≤ 0 := by exact_mod_cast hm.le
    exact Real.rpow_le_rpow_of_exponent_le h1p.le (by nlinarith)

/-- Two distinct degrees `m ≠ n` (with nonzero coefficient at `m`) can yield equal term norms
`‖x.coeff m‖ * (p ^ (-q)) ^ m = ‖x.coeff n‖ * (p ^ (-q)) ^ n` for at most one rational `q`. -/
private theorem subsingleton_eq_norm_coeff_mul_rpow (x : AnnularRing p) {m n : ℤ} (hmn : m ≠ n) :
    {q : ℚ | x.coeff m ≠ 0 ∧
      ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m =
        ‖x.coeff n‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ n}.Subsingleton := by
  rintro q₁ ⟨hm, h₁⟩ q₂ ⟨-, h₂⟩
  have hp : (0 : ℝ) < p := p_pos (p := p)
  have hm_pos : 0 < ‖x.coeff m‖ := norm_pos_iff.mpr hm
  have hrel (q : ℚ) (hq : ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m =
      ‖x.coeff n‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ n) :
      ‖x.coeff m‖ / ‖x.coeff n‖ = (p : ℝ) ^ ((q : ℝ) * ((m : ℝ) - (n : ℝ))) := by
    have hn_pos : 0 < ‖x.coeff n‖ := by
      by_contra h
      have hn0 : ‖x.coeff n‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      rw [hn0, zero_mul] at hq
      exact (mul_pos hm_pos (zpow_pos (Real.rpow_pos_of_pos hp _) m)).ne' hq
    rw [← Real.rpow_intCast, ← Real.rpow_mul hp.le, ← Real.rpow_intCast,
      ← Real.rpow_mul hp.le] at hq
    rw [div_eq_iff hn_pos.ne', ← mul_left_inj' (Real.rpow_pos_of_pos hp (-(q : ℝ) * (m : ℝ))).ne',
      hq, mul_assoc, mul_left_comm _ ‖x.coeff n‖, ← Real.rpow_add hp]
    congr 2
    ring
  have heq : (p : ℝ) ^ ((q₁ : ℝ) * ((m : ℝ) - (n : ℝ))) =
      (p : ℝ) ^ ((q₂ : ℝ) * ((m : ℝ) - (n : ℝ))) :=
    (hrel q₁ h₁).symm.trans (hrel q₂ h₂)
  have hexp := (Real.rpow_right_inj hp (one_lt_p (p := p)).ne').mp heq
  have hsub : ((m : ℝ) - (n : ℝ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  exact Rat.cast_injective (mul_right_cancel₀ hsub hexp)

/-- Given a finite set `S : Finset ℤ`, there exists `q ∈ [1/4, 3/4]` at which no two distinct
degrees `m ≠ n` in `S` (with `x.coeff m ≠ 0`) have equal term norms `‖x.coeff m‖ * p ^ (-q m)`. -/
private theorem exists_rat_Icc_distinct_term_norms (x : AnnularRing p) (S : Finset ℤ) :
    ∃ q : ℚ, (1 / 4 : ℚ) ≤ q ∧ q ≤ 3 / 4 ∧
      ∀ m ∈ S, ∀ n ∈ S, m ≠ n → x.coeff m ≠ 0 →
        ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m ≠
          ‖x.coeff n‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ n := by
  set P : Finset (ℤ × ℤ) := (S ×ˢ S).filter fun mn ↦ mn.1 ≠ mn.2
  set bad : Set ℚ := ⋃ mn ∈ P, {q : ℚ | x.coeff mn.1 ≠ 0 ∧
    ‖x.coeff mn.1‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ mn.1 =
      ‖x.coeff mn.2‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ mn.2}
  have hbad : bad.Finite :=
    P.finite_toSet.biUnion fun mn hmn ↦
      (subsingleton_eq_norm_coeff_mul_rpow x (Finset.mem_filter.mp hmn).2).finite
  obtain ⟨q, ⟨hq₁, hq₂⟩, hq_good⟩ := ((Set.Icc_infinite (by norm_num : (1 / 4 : ℚ) < 3 / 4)).sdiff
    hbad).nonempty
  refine ⟨q, hq₁, hq₂, fun m hm n hn hmn hxm heq ↦ hq_good ?_⟩
  exact Set.mem_iUnion₂.mpr ⟨(m, n),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hn⟩, hmn⟩, hxm, heq⟩

/-- **Joint injectivity on `H`**: an element of `AnnularRing p` that vanishes at every point
`t ∈ ℂ_[p]` of the open annulus `p⁻¹ < ‖t‖ < 1` is zero. -/
theorem eq_zero_of_forall_evalAt_padicComplex_eq_zero {x : AnnularRing p}
    (hx : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1), evalAt t ht₀ ht₁ x = 0) :
    x = 0 := by
  by_contra hne
  obtain ⟨m₀, hm₀⟩ : ∃ m : ℤ, x.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (AnnularRing.ext (funext h))
  have hp : (0 : ℝ) < p := p_pos (p := p)
  set δ : ℝ := ‖x.coeff m₀‖ *
    min (((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ m₀) (((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ m₀)
  have hδ : 0 < δ := mul_pos (norm_pos_iff.mpr hm₀)
    (lt_min (zpow_pos (Real.rpow_pos_of_pos hp _) _) (zpow_pos (Real.rpow_pos_of_pos hp _) _))
  set ρ : ℝ := (p : ℝ) ^ (-(1 / 4 : ℝ))
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hp _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (one_lt_p (p := p)) (by norm_num)
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt_of_lt_one hδ hρ1
  set M : ℕ := max M₀ m₀.natAbs
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) M
  have hm₀S : m₀ ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨q, hq₁, hq₂, hq_dist⟩ := exists_rat_Icc_distinct_term_norms x S
  obtain ⟨t, htnorm⟩ := PadicComplex.exists_norm_eq_rpow (p := p) (-q)
  rw [Rat.cast_neg] at htnorm
  have h1p : (1 : ℝ) < p := one_lt_p (p := p)
  have hq₁' : (1 / 4 : ℝ) ≤ (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₁
  have hq₂' : (q : ℝ) ≤ 3 / 4 := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₂
  have ht₀ : (p : ℝ)⁻¹ < ‖t‖ := by
    rw [htnorm, ← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt h1p (by linarith)
  have ht₁ : ‖t‖ < 1 := by
    rw [htnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg h1p (by linarith)
  let term (m : ℤ) : ℂ_[p] := padicIntAlgebraMap p ℂ_[p] (x.coeff m) * t ^ m
  have hterm_norm (m : ℤ) : ‖term m‖ = ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m := by
    simp [term, htnorm]
  obtain ⟨m₁, hm₁S, hm₁max⟩ := S.exists_max_image (fun m ↦ ‖term m‖) ⟨m₀, hm₀S⟩
  have hδ_le_m₁ : δ ≤ ‖term m₁‖ :=
    (mul_le_mul_of_nonneg_left (min_rpow_le_rpow_zpow hq₁ hq₂ m₀) (norm_nonneg _)).trans
      ((hterm_norm m₀).symm.le.trans (hm₁max m₀ hm₀S))
  have hm₁_ne : x.coeff m₁ ≠ 0 := fun h0 ↦ by
    have : ‖term m₁‖ = 0 := by simp [term, h0]
    linarith
  have hdom : ∀ m : ℤ, m ≠ m₁ → ‖term m‖ < ‖term m₁‖ := fun m hm ↦ by
    by_cases hmS : m ∈ S
    · refine lt_of_le_of_ne (hm₁max m hmS) fun heq ↦
        hq_dist m₁ hm₁S m hmS hm.symm hm₁_ne ?_
      simpa only [hterm_norm] using heq.symm
    · have hMlt : M₀ ≤ m.natAbs := by
        simp only [S, Finset.mem_Icc, not_and_or, not_le] at hmS
        omega
      calc ‖term m‖ = ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m := hterm_norm m
        _ ≤ ρ ^ m.natAbs := norm_coeff_mul_rpow_le_of_mem_Icc x hq₁ hq₂ m
        _ ≤ ρ ^ M₀ := pow_le_pow_of_le_one hρ0.le hρ1.le hMlt
        _ < δ := hM₀
        _ ≤ ‖term m₁‖ := hδ_le_m₁
  have heval_norm := (hasSum_evalAt t ht₀ ht₁ x).norm_eq_of_forall_norm_lt m₁ hdom
  rw [hx t ht₀ ht₁, norm_zero] at heval_norm
  linarith

/-- Two elements of `AnnularRing p` that agree at every point `t ∈ ℂ_[p]` of the open annulus
`p⁻¹ < ‖t‖ < 1` are equal. -/
theorem eq_of_forall_evalAt_padicComplex_eq {x y : AnnularRing p}
    (hxy : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      evalAt t ht₀ ht₁ x = evalAt t ht₀ ht₁ y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_evalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [map_sub, hxy t ht₀ ht₁, sub_self]

/-- **Joint injectivity on `H[1/T]`**: an element of `H[1/T]` that vanishes at every point
`t ∈ ℂ_[p]` of the open annulus `p⁻¹ < ‖t‖ < 1` is zero. -/
theorem eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x : A}
    (hx : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      localizedEvalAt t ht₀ ht₁ x = 0) : x = 0 := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have ha0 : a = 0 := eq_zero_of_forall_evalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [← localizedEvalAt_algebraMap (A := A), ← ha, map_mul, hx t ht₀ ht₁, zero_mul]
  rw [ha0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).pow k).mul_left_eq_zero.mp ha

/-- Two elements of `H[1/T]` that agree at every point `t ∈ ℂ_[p]` of the open annulus
`p⁻¹ < ‖t‖ < 1` are equal. -/
theorem eq_of_forall_localizedEvalAt_padicComplex_eq {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x y : A}
    (hxy : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      localizedEvalAt t ht₀ ht₁ x = localizedEvalAt t ht₀ ht₁ y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [map_sub, hxy t ht₀ ht₁, sub_self]

end TauCeti.AnnularRing
