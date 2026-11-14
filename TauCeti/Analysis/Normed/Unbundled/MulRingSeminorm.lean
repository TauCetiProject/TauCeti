/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SmoothingSeminorm

import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Order.Zorn

/-!
# Multiplicative ring seminorms below power-multiplicative seminorms

Every nonzero power-multiplicative ring seminorm `ρ` on a commutative ring `R` is the pointwise
maximum of the multiplicative ring seminorms `α : MulRingSeminorm R` bounded above by `ρ`
([BGR, §1.3.2, Theorem 2]). Given `x₀ : R` with `ρ x₀ ≠ 0`, `seminormFromConst` produces a
power-multiplicative seminorm `μ₁ ≤ ρ` agreeing with `ρ` at `x₀` for which `x₀` is multiplicative.
Zorn's lemma applied to descending chains of power-multiplicative seminorms below `μ₁` that keep
`x₀` multiplicative and preserve its value yields a minimal element; applying `seminormFromConst`
again at each element of nonzero seminorm shows that a minimal element is multiplicative on all of
`R`.

Combining this representation with `RingSeminorm.smoothing` expresses `smoothingFun μ x`, for any
ring seminorm `μ` on a commutative ring `R`, as the supremum of `α x` over all multiplicative ring
seminorms `α ≤ μ`, attained whenever `μ ≠ 0`. This is the unbundled core of Berkovich's spectral
formula on the Gel'fand spectrum of a normed commutative ring.

## Main definitions

* `MulRingSeminorm.toRingSeminorm`: view a multiplicative ring seminorm as a `RingSeminorm`.
* `MulRingSeminorm.comp`: composition of a multiplicative ring seminorm with a ring homomorphism.

## Main results

* `MulRingSeminorm.le_of_le_mul`, `MulRingSeminorm.le_smoothingFun_of_le_mul`: a multiplicative
  seminorm bounded by `C * μ` is bounded by `μ` and (over a commutative ring) by `smoothingFun μ`.
* `RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq`: for a nonzero power-multiplicative ring
  seminorm `ρ` on a commutative ring and any `x₀`, some `α : MulRingSeminorm R` satisfies
  `α ≤ ρ` and `α x₀ = ρ x₀`.
* `RingSeminorm.eq_sSup_mulRingSeminorm`: every power-multiplicative ring seminorm `ρ` on a
  commutative ring is the pointwise supremum of the multiplicative ring seminorms below `ρ`.
* `RingSeminorm.smoothing_eq_sSup_mulRingSeminorm`: `μ.smoothing x` is the supremum of `α x` over
  multiplicative ring seminorms `α ≤ μ`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2, Theorem 2.
* V. G. Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, Theorem 1.3.1.
-/

public section

open Filter Topology

namespace MulRingSeminorm

section NonAssocRing

variable {R S T : Type*} [NonAssocRing R] [NonAssocRing S] [NonAssocRing T]

/-- Forget multiplicativity and view a `MulRingSeminorm` as a `RingSeminorm`. -/
def toRingSeminorm (α : MulRingSeminorm R) : RingSeminorm R where
  __ := α.toAddGroupSeminorm
  mul_le' x y := (map_mul α x y).le

/-- A ring admitting a multiplicative ring seminorm is nontrivial, since `α 1 = 1 ≠ 0 = α 0`. -/
theorem nontrivial (α : MulRingSeminorm R) : Nontrivial R :=
  ⟨⟨1, 0, fun h ↦ one_ne_zero (by rw [← map_one α, h, map_zero])⟩⟩

/-- Composition of a multiplicative ring seminorm with a ring homomorphism `φ : R →+* S`, as a
multiplicative ring seminorm on `R`. -/
def comp (α : MulRingSeminorm S) (φ : R →+* S) : MulRingSeminorm R where
  __ := α.toAddGroupSeminorm.comp φ.toAddMonoidHom
  map_one' := by simp
  map_mul' x y := by simp

/-- Evaluating `α.comp φ` applies `α` after `φ`. -/
@[simp]
theorem comp_apply (α : MulRingSeminorm S) (φ : R →+* S) (x : R) :
    α.comp φ x = α (φ x) :=
  (rfl)

/-- The underlying function of `α.comp φ` is `α ∘ φ`. -/
@[simp]
theorem coe_comp (α : MulRingSeminorm S) (φ : R →+* S) :
    ⇑(α.comp φ) = α ∘ φ :=
  (rfl)

/-- Composing with the identity ring homomorphism is the identity. -/
@[simp]
theorem comp_id (α : MulRingSeminorm R) :
    α.comp (RingHom.id R) = α :=
  ext fun _ ↦ rfl

/-- Composition of multiplicative ring seminorms with ring homomorphisms is associative. -/
theorem comp_assoc (α : MulRingSeminorm T) (ψ : S →+* T) (φ : R →+* S) :
    α.comp (ψ.comp φ) = (α.comp ψ).comp φ :=
  ext fun _ ↦ rfl

/-- Adding an element of seminorm zero leaves a multiplicative ring seminorm unchanged. -/
theorem map_add_eq_left_of_map_eq_zero (α : MulRingSeminorm R) (x : R) {y : R} (hy : α y = 0) :
    α (x + y) = α x :=
  sub_eq_zero.1 <| abs_nonpos_iff.1 <|
    (abs_sub_map_le_sub α (x + y) x).trans_eq (by rw [add_sub_cancel_left, hy])

end NonAssocRing

section Ring

variable {R : Type*} [Ring R]

/-- The underlying function of `α.toRingSeminorm` is `α` itself. -/
@[simp]
theorem coe_toRingSeminorm (α : MulRingSeminorm R) :
    ⇑α.toRingSeminorm = α :=
  (rfl)

/-- Evaluating `α.toRingSeminorm` agrees with `α`. -/
@[simp]
theorem toRingSeminorm_apply (α : MulRingSeminorm R) (x : R) :
    α.toRingSeminorm x = α x :=
  (rfl)

/-- `α.toRingSeminorm` is nonzero because `α 1 = 1`. -/
theorem toRingSeminorm_ne_zero (α : MulRingSeminorm R) : α.toRingSeminorm ≠ 0 :=
  RingSeminorm.ne_zero_iff.2 ⟨1, by simp⟩

/-- Every multiplicative ring seminorm is power-multiplicative. -/
theorem isPowMul (α : MulRingSeminorm R) : IsPowMul α :=
  fun x n _ ↦ map_pow α x n

/-- Every multiplicative ring seminorm vanishes on nilpotent elements. -/
theorem eq_zero_of_isNilpotent (α : MulRingSeminorm R) {x : R} (hx : IsNilpotent x) : α x = 0 := by
  obtain ⟨n, hn⟩ := hx
  exact eq_zero_of_pow_eq_zero (by rw [← map_pow, hn, map_zero])

/-- **Multiplicativity absorbs constant factors.** If `α : MulRingSeminorm R` satisfies
`α x ≤ C * μ x` for a ring seminorm `μ` and every `x`, then in fact `α x ≤ μ x`. -/
theorem le_of_le_mul (α : MulRingSeminorm R) {μ : RingSeminorm R} {C : ℝ}
    (h : ∀ x, α x ≤ C * μ x) (x : R) : α x ≤ μ x := by
  set D := max C 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ) * μ x) atTop (𝓝 (μ x)) := by
    have hD1 : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using ((Real.continuousAt_const_rpow hD.ne').tendsto).comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using hD1.mul_const (μ x)
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  calc α x = (α x ^ n) ^ (1 / n : ℝ) := by
        rw [one_div, Real.pow_rpow_inv_natCast (apply_nonneg α x) hn0]
    _ = α (x ^ n) ^ (1 / n : ℝ) := by rw [map_pow]
    _ ≤ (D * μ (x ^ n)) ^ (1 / n : ℝ) := by
        gcongr
        exact (h _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg μ _))
    _ ≤ (D * μ x ^ n) ^ (1 / n : ℝ) := by
        gcongr
        exact map_pow_le_pow μ x hn0
    _ = D ^ (1 / n : ℝ) * (μ x ^ n) ^ (1 / n : ℝ) :=
        Real.mul_rpow hD.le (pow_nonneg (apply_nonneg μ x) n)
    _ = D ^ (1 / n : ℝ) * μ x := by
        rw [one_div, Real.pow_rpow_inv_natCast (apply_nonneg μ x) hn0]

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- Over a commutative ring, if `α : MulRingSeminorm R` satisfies `α x ≤ C * μ x` for every `x`,
then `α x ≤ smoothingFun μ x` for every `x`. -/
theorem le_smoothingFun_of_le_mul (α : MulRingSeminorm R) {μ : RingSeminorm R} {C : ℝ}
    (h : ∀ x, α x ≤ C * μ x) (x : R) : α x ≤ smoothingFun μ x := by
  set D := max C 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ) * smoothingSeminormSeq μ x n) atTop
      (𝓝 (smoothingFun μ x)) := by
    have hD1 : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using ((Real.continuousAt_const_rpow hD.ne').tendsto).comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using hD1.mul (μ.tendsto_smoothingFun x)
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  calc α x = (α x ^ n) ^ (1 / n : ℝ) := by
        rw [one_div, Real.pow_rpow_inv_natCast (apply_nonneg α x) hn0]
    _ = α (x ^ n) ^ (1 / n : ℝ) := by rw [map_pow]
    _ ≤ (D * μ (x ^ n)) ^ (1 / n : ℝ) := by
        gcongr
        exact (h _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg μ _))
    _ = D ^ (1 / n : ℝ) * smoothingSeminormSeq μ x n :=
        Real.mul_rpow hD.le (apply_nonneg μ _)

end CommRing

end MulRingSeminorm

namespace RingSeminorm

section CommRing

variable {R : Type*} [CommRing R]

/-- A nonzero power-multiplicative ring seminorm takes value `1` at `1`. -/
theorem map_one_eq_one_of_isPowMul {ρ : RingSeminorm R} (hpm : IsPowMul ρ) (hρ : ρ ≠ 0) :
    ρ 1 = 1 :=
  (ρ.seminorm_one_eq_one_iff_ne_zero hpm.map_one_le_one).2 hρ

/-- Auxiliary step of BGR Theorem 1.3.2/2 when `ρ x₀ ≠ 0`. -/
private theorem exists_mulRingSeminorm_le_of_apply_ne_zero {ρ : RingSeminorm R}
    (hpm : IsPowMul ρ) {x₀ : R} (hx₀ : ρ x₀ ≠ 0) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  let μ₁ : RingSeminorm R := seminormFromConst hx₀ hpm
  have hμ₁_pm : IsPowMul μ₁ := seminormFromConst_isPowMul hx₀ hpm
  have hμ₁_one : μ₁ 1 = 1 := seminormFromConst_one hx₀ hpm
  have hμ₁_le : ∀ x, μ₁ x ≤ ρ x := seminormFromConst_le_seminorm hx₀ hpm
  have hμ₁_x₀ : μ₁ x₀ = ρ x₀ := seminormFromConst_apply_c hx₀ hpm
  have hμ₁_mul : ∀ y, μ₁ (x₀ * y) = μ₁ x₀ * μ₁ y := seminormFromConst_const_mul hx₀ hpm
  have hx₀_pos : 0 < μ₁ x₀ :=
    lt_of_le_of_ne (apply_nonneg μ₁ x₀) (by rw [hμ₁_x₀]; exact hx₀.symm)
  let S : Set (R → ℝ) :=
    {f | f 0 = 0 ∧ (∀ a, 0 ≤ f a) ∧ (∀ a b, f (a + b) ≤ f a + f b) ∧
      (∀ a, f (-a) = f a) ∧ (∀ a b, f (a * b) ≤ f a * f b) ∧ IsPowMul f ∧
      f 1 = 1 ∧ f x₀ = μ₁ x₀ ∧ ∀ y, f (x₀ * y) = f x₀ * f y}
  have hμ₁_mem : (⇑μ₁ : R → ℝ) ∈ S :=
    ⟨map_zero μ₁, apply_nonneg μ₁, map_add_le_add μ₁, map_neg_eq_map μ₁, map_mul_le_mul μ₁,
      hμ₁_pm, hμ₁_one, rfl, hμ₁_mul⟩
  obtain ⟨m, hm_le, hm_min⟩ := zorn_ge_nonempty₀ S
    (fun c hcs hc y₀ hy₀ ↦ by
      have : Nonempty c := ⟨⟨y₀, hy₀⟩⟩
      let lb : R → ℝ := fun a ↦ ⨅ z : c, z.1 a
      have hbdd (a : R) : BddBelow (Set.range fun z : c ↦ z.1 a) :=
        ⟨0, by rintro _ ⟨z, rfl⟩; exact (hcs z.2).2.1 a⟩
      have hlb_le (z : c) (a : R) : lb a ≤ z.1 a := ciInf_le (hbdd a) z
      have hlb_nonneg (a : R) : 0 ≤ lb a := le_ciInf fun z ↦ (hcs z.2).2.1 a
      have hlb_zero : lb 0 = 0 := by
        simp only [lb, fun z : c ↦ (hcs z.2).1, ciInf_const]
      have hlb_neg (a : R) : lb (-a) = lb a := by
        simp only [lb, fun z : c ↦ (hcs z.2).2.2.2.1 a]
      have hlb_one : lb 1 = 1 := by
        simp only [lb, fun z : c ↦ (hcs z.2).2.2.2.2.2.2.1, ciInf_const]
      have hlb_x₀ : lb x₀ = μ₁ x₀ := by
        simp only [lb, fun z : c ↦ (hcs z.2).2.2.2.2.2.2.2.1, ciInf_const]
      have hlb_add (a b : R) : lb (a + b) ≤ lb a + lb b := by
        have hpair (z₁ z₂ : c) : lb (a + b) ≤ z₁.1 a + z₂.1 b := by
          rcases hc.total z₁.2 z₂.2 with h12 | h21
          · exact (hlb_le z₂ (a + b)).trans
              (((hcs z₂.2).2.2.1 a b).trans (add_le_add_left (h12 a) _))
          · exact (hlb_le z₁ (a + b)).trans
              (((hcs z₁.2).2.2.1 a b).trans (add_le_add_right (h21 b) _))
        have h1 (z₁ : c) : lb (a + b) - z₁.1 a ≤ lb b :=
          le_ciInf fun z₂ ↦ sub_le_iff_le_add'.2 (hpair z₁ z₂)
        have h2 : lb (a + b) - lb b ≤ lb a :=
          le_ciInf fun z₁ ↦ sub_le_iff_le_add.2 (sub_le_iff_le_add'.1 (h1 z₁))
        exact sub_le_iff_le_add.1 h2
      have hlb_mul (a b : R) : lb (a * b) ≤ lb a * lb b := by
        have hpair (z₁ z₂ : c) : lb (a * b) ≤ z₁.1 a * z₂.1 b := by
          rcases hc.total z₁.2 z₂.2 with h12 | h21
          · exact (hlb_le z₂ (a * b)).trans (((hcs z₂.2).2.2.2.2.1 a b).trans
              (mul_le_mul_of_nonneg_right (h12 a) ((hcs z₂.2).2.1 b)))
          · exact (hlb_le z₁ (a * b)).trans (((hcs z₁.2).2.2.2.2.1 a b).trans
              (mul_le_mul_of_nonneg_left (h21 b) ((hcs z₁.2).2.1 a)))
        have h1 (z₁ : c) : lb (a * b) ≤ z₁.1 a * lb b := by
          rcases (hcs z₁.2).2.1 a |>.eq_or_lt with hza | hza
          · simpa [← hza] using hpair z₁ z₁
          · rw [← div_le_iff₀' hza]
            exact le_ciInf fun z₂ ↦ (div_le_iff₀' hza).2 (hpair z₁ z₂)
        rcases (hlb_nonneg b).eq_or_lt with hlbb | hlbb
        · simpa [← hlbb] using h1 ⟨y₀, hy₀⟩
        · rw [← div_le_iff₀ hlbb]
          exact le_ciInf fun z₁ ↦ (div_le_iff₀ hlbb).2 (h1 z₁)
      have hlb_pm : IsPowMul lb := fun a k hk ↦ by
        refine le_antisymm ?_
          (le_ciInf fun z ↦ (pow_le_pow_left₀ (hlb_nonneg a) (hlb_le z a) k).trans_eq
            ((hcs z.2).2.2.2.2.2.1 a hk).symm)
        have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.1 hk
        have hroot : lb (a ^ k) ^ (1 / k : ℝ) ≤ lb a := by
          refine le_ciInf fun z ↦ ?_
          calc lb (a ^ k) ^ (1 / k : ℝ)
              ≤ z.1 (a ^ k) ^ (1 / k : ℝ) := by
                gcongr
                · exact hlb_nonneg _
                · exact hlb_le z (a ^ k)
            _ = (z.1 a ^ k) ^ (1 / k : ℝ) := by rw [(hcs z.2).2.2.2.2.2.1 a hk]
            _ = z.1 a := by rw [one_div, Real.pow_rpow_inv_natCast ((hcs z.2).2.1 a) hk0]
        calc lb (a ^ k) = (lb (a ^ k) ^ (1 / k : ℝ)) ^ k := by
              rw [one_div, ← Real.rpow_natCast, ← Real.rpow_mul (hlb_nonneg _),
                inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk0), Real.rpow_one]
          _ ≤ lb a ^ k := pow_le_pow_left₀ (Real.rpow_nonneg (hlb_nonneg _) _) hroot k
      have hlb_x₀_mul (y : R) : lb (x₀ * y) = lb x₀ * lb y := by
        rw [hlb_x₀]
        refine le_antisymm ?_ ?_
        · rw [← div_le_iff₀' hx₀_pos]
          refine le_ciInf fun z ↦ (div_le_iff₀' hx₀_pos).2 ?_
          have hz := (hcs z.2).2.2.2.2.2.2.2.2 y
          rw [(hcs z.2).2.2.2.2.2.2.2.1] at hz
          exact (hlb_le z (x₀ * y)).trans_eq hz
        · refine le_ciInf fun z ↦ ?_
          have hz := (hcs z.2).2.2.2.2.2.2.2.2 y
          rw [(hcs z.2).2.2.2.2.2.2.2.1] at hz
          rw [hz]
          exact mul_le_mul_of_nonneg_left (hlb_le z y) hx₀_pos.le
      exact ⟨lb, ⟨hlb_zero, hlb_nonneg, hlb_add, hlb_neg, hlb_mul, hlb_pm, hlb_one, hlb_x₀,
        hlb_x₀_mul⟩, fun z hz ↦ hlb_le ⟨z, hz⟩⟩)
    (⇑μ₁) hμ₁_mem
  rcases hm_min.prop with ⟨hm0, -, hm_add, hm_neg, hm_mul_le, hm_pm, hm1, hmx₀, hmx₀_mul⟩
  let ν : RingSeminorm R :=
    { toFun := m
      map_zero' := hm0
      add_le' := hm_add
      neg' := hm_neg
      mul_le' := hm_mul_le }
  have hν_pm : IsPowMul ν := hm_pm
  have hν_mul (c y : R) : ν (c * y) = ν c * ν y := by
    by_cases hc0 : ν c = 0
    · refine le_antisymm ?_ (by simp [hc0])
      exact (map_mul_le_mul ν c y).trans (by simp [hc0])
    · let g : RingSeminorm R := seminormFromConst hc0 hν_pm
      have hg_le : (⇑g : R → ℝ) ≤ m := seminormFromConst_le_seminorm hc0 hν_pm
      have hg_mem : (⇑g : R → ℝ) ∈ S :=
        ⟨map_zero g, apply_nonneg g, map_add_le_add g, map_neg_eq_map g, map_mul_le_mul g,
          seminormFromConst_isPowMul hc0 hν_pm,
          seminormFromConst_one hc0 hν_pm,
          (seminormFromConst_apply_of_isMul hc0 hν_pm hmx₀_mul).trans hmx₀,
          seminormFromConst_isMul_of_isMul hc0 hν_pm hmx₀_mul⟩
      have hgm : m = ⇑g := le_antisymm (hm_min.2 hg_mem hg_le) hg_le
      have hc_mul := seminormFromConst_const_mul hc0 hν_pm y
      change g (c * y) = g c * g y at hc_mul
      change m (c * y) = m c * m y
      simpa only [← hgm] using hc_mul
  refine ⟨{ toAddGroupSeminorm := ν.toAddGroupSeminorm
            map_one' := hm1
            map_mul' := hν_mul },
    fun x ↦ (hm_le x).trans (hμ₁_le x), hmx₀.trans hμ₁_x₀⟩

/-- **Bosch–Güntzer–Remmert Theorem 1.3.2/2.** For every nonzero power-multiplicative ring seminorm
`ρ` on a commutative ring `R` and every `x₀ : R`, there exists a multiplicative ring seminorm
`α : MulRingSeminorm R` with `α ≤ ρ` and `α x₀ = ρ x₀`. -/
theorem exists_mulRingSeminorm_le_and_apply_eq {ρ : RingSeminorm R} (hpm : IsPowMul ρ)
    (hρ : ρ ≠ 0) (x₀ : R) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  by_cases hx₀ : ρ x₀ = 0
  · have h1 : ρ 1 ≠ 0 := by rw [map_one_eq_one_of_isPowMul hpm hρ]; exact one_ne_zero
    obtain ⟨α, hα, -⟩ := exists_mulRingSeminorm_le_of_apply_ne_zero hpm h1
    exact ⟨α, hα, le_antisymm (hα x₀) (by rw [hx₀]; exact apply_nonneg α x₀)⟩
  · exact exists_mulRingSeminorm_le_of_apply_ne_zero hpm hx₀

/-- Every nonzero power-multiplicative ring seminorm on a commutative ring dominates at least one
multiplicative ring seminorm. -/
theorem exists_mulRingSeminorm_le {ρ : RingSeminorm R} (hpm : IsPowMul ρ) (hρ : ρ ≠ 0) :
    ∃ α : MulRingSeminorm R, ∀ x, α x ≤ ρ x := by
  obtain ⟨α, hα, -⟩ := exists_mulRingSeminorm_le_and_apply_eq hpm hρ 1
  exact ⟨α, hα⟩

/-- Every power-multiplicative ring seminorm `ρ` on a commutative ring is the pointwise supremum of
the multiplicative ring seminorms bounded above by `ρ` (including `ρ = 0`, where the set of such
multiplicative seminorms is empty and `sSup ∅ = 0`). -/
theorem eq_sSup_mulRingSeminorm {ρ : RingSeminorm R} (hpm : IsPowMul ρ) (x : R) :
    ρ x = sSup {r : ℝ | ∃ α : MulRingSeminorm R, (∀ y, α y ≤ ρ y) ∧ α x = r} := by
  by_cases hρ : ρ = 0
  · have hρ0 : ∀ y, ρ y = 0 := eq_zero_iff.1 hρ
    have hempty : {r : ℝ | ∃ α : MulRingSeminorm R, (∀ y, α y ≤ ρ y) ∧ α x = r} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro α hα _
      have h1 : (1 : ℝ) ≤ 0 := by simpa [hρ0 1] using hα 1
      linarith
    rw [hempty, Real.sSup_empty, hρ0 x]
  · symm
    refine IsGreatest.csSup_eq ⟨?_, ?_⟩
    · obtain ⟨α, hα, hαx⟩ := exists_mulRingSeminorm_le_and_apply_eq hpm hρ x
      exact ⟨α, hα, hαx⟩
    · rintro _ ⟨α, hα, rfl⟩
      exact hα x

/-- For any ring seminorm `μ` on a commutative ring, `μ.smoothing x` is the supremum of `α x` over
all multiplicative ring seminorms `α ≤ μ`. -/
theorem smoothing_eq_sSup_mulRingSeminorm (μ : RingSeminorm R) (x : R) :
    μ.smoothing x = sSup {r : ℝ | ∃ α : MulRingSeminorm R, (∀ y, α y ≤ μ y) ∧ α x = r} := by
  rw [eq_sSup_mulRingSeminorm μ.isPowMul_smoothing x]
  congr 1
  ext r
  refine exists_congr fun α ↦ and_congr_left fun _ ↦
    ⟨fun h y ↦ (h y).trans (μ.smoothing_le_self y), fun h y ↦ by
      rw [smoothing_apply]
      exact α.le_smoothingFun_of_le_mul (C := 1) (fun z ↦ by simpa only [one_mul] using h z) y⟩

end CommRing

end RingSeminorm
