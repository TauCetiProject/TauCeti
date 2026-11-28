/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.MulRingSeminorm
public import TauCeti.Analysis.Normed.Unbundled.SmoothingSeminorm

import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Order.Zorn
import TauCeti.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Multiplicative ring seminorms below a ring seminorm

Every nonzero power-multiplicative ring seminorm `ρ` on a commutative ring `R` is the pointwise
maximum of the multiplicative ring seminorms `α : MulRingSeminorm R` bounded above by `ρ`
([BGR, §1.3.2, Theorem 3]). Given `x₀ : R` with `ρ x₀ ≠ 0`, `seminormFromConst`
([BGR, Proposition 1.3.2/2]) produces a power-multiplicative seminorm `μ₁ ≤ ρ` agreeing with `ρ`
at `x₀` for which `x₀` is multiplicative. Zorn's lemma applied to descending chains of
power-multiplicative seminorms below `μ₁` that keep `x₀` multiplicative and preserve its value
yields a minimal element; applying `seminormFromConst` again at each element of nonzero seminorm
shows that a minimal element is multiplicative on all of `R`.

Combining this representation with `RingSeminorm.smoothing` expresses `smoothingFun μ x`, for any
ring seminorm `μ` on a commutative ring `R`, as the supremum of `α x` over all multiplicative ring
seminorms `α ≤ μ`, attained whenever `μ ≠ 0`. This is the unbundled core of Berkovich's spectral
formula on the Berkovich spectrum of a normed commutative ring.

## Main results

* `MulRingSeminorm.le_smoothingFun_of_le_mul`: a bound `α ≤ C * μ` forces `α ≤ smoothingFun μ`.
* `RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq`: Bosch–Güntzer–Remmert Theorem 1.3.2/3.
* `RingSeminorm.exists_mulRingSeminorm_le`: every nonzero power-multiplicative ring seminorm on a
  commutative ring dominates a multiplicative ring seminorm.
* `RingSeminorm.eq_sSup_mulRingSeminorm`: every power-multiplicative ring seminorm is the pointwise
  supremum of the multiplicative ring seminorms below it.
* `RingSeminorm.smoothing_eq_sSup_mulRingSeminorm`: `μ.smoothing x` is the supremum of `α x` over
  all multiplicative ring seminorms `α ≤ μ`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2, Proposition 2 and
  Theorem 3.
* V. G. Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, Theorem 1.3.1.
-/

public section

namespace MulRingSeminorm

section CommRing

variable {R : Type*} [CommRing R]

/-- Over a commutative ring, if `α : MulRingSeminorm R` satisfies `α x ≤ C * μ x` for every `x`,
then `α x ≤ smoothingFun μ x` for every `x`. -/
theorem le_smoothingFun_of_le_mul (α : MulRingSeminorm R) {μ : RingSeminorm R} {C : ℝ}
    (h : ∀ x, α x ≤ C * μ x) (x : R) : α x ≤ smoothingFun μ x := by
  have h1 : α.toRingSeminorm 1 ≤ 1 := by
    simpa only [coe_toRingSeminorm] using (map_one α).le
  have hpm : ∀ n ≥ 1, α.toRingSeminorm (x ^ n) = α.toRingSeminorm x ^ n := fun n _ ↦ by
    simp only [coe_toRingSeminorm, map_pow]
  have hle : ∀ y, α.toRingSeminorm ((RingHom.id R) y) ≤ C * μ y := by
    simpa only [RingHom.id_apply, coe_toRingSeminorm] using h
  calc α x = α.toRingSeminorm x := by simp only [coe_toRingSeminorm]
    _ = smoothingFun α.toRingSeminorm x := (smoothingFun_of_powMul α.toRingSeminorm h1 hpm).symm
    _ ≤ smoothingFun μ x := (RingHom.id R).smoothingFun_map_le_of_le_mul hle x

end CommRing

end MulRingSeminorm

namespace RingSeminorm

section CommRing

variable {R : Type*} [CommRing R]

/-- Predicate characterizing the Zorn poset in BGR Theorem 1.3.2/3: power-multiplicative ring
seminorm functions normalized at `1` that take value `r` at `x₀` and are multiplicative at `x₀`. -/
private structure PowMulSeminormAt (x₀ : R) (r : ℝ) (f : R → ℝ) : Prop where
  map_zero : f 0 = 0
  add_le : ∀ a b, f (a + b) ≤ f a + f b
  neg : ∀ a, f (-a) = f a
  mul_le : ∀ a b, f (a * b) ≤ f a * f b
  isPowMul : IsPowMul f
  map_one : f 1 = 1
  apply_x₀ : f x₀ = r
  const_mul : ∀ y, f (x₀ * y) = f x₀ * f y

/-- Bundle a function satisfying `PowMulSeminormAt` as a `RingSeminorm R`. -/
private def PowMulSeminormAt.toRingSeminorm {x₀ : R} {r : ℝ} {f : R → ℝ}
    (hf : PowMulSeminormAt x₀ r f) : RingSeminorm R where
  toFun := f
  map_zero' := hf.map_zero
  add_le' := hf.add_le
  neg' := hf.neg
  mul_le' := hf.mul_le

private theorem PowMulSeminormAt.toRingSeminorm_apply {x₀ : R} {r : ℝ} {f : R → ℝ}
    (hf : PowMulSeminormAt x₀ r f) (a : R) :
    hf.toRingSeminorm a = f a :=
  rfl

private theorem PowMulSeminormAt.of_ringSeminorm {x₀ : R} {r : ℝ} (ν : RingSeminorm R)
    (hpm : IsPowMul ν) (h1 : ν 1 = 1) (hx₀ : ν x₀ = r)
    (hmul : ∀ y, ν (x₀ * y) = ν x₀ * ν y) :
    PowMulSeminormAt x₀ r ν :=
  ⟨_root_.map_zero ν, map_add_le_add ν, map_neg_eq_map ν, map_mul_le_mul ν,
    hpm, h1, hx₀, hmul⟩

/-- The pointwise infimum of a nonempty descending chain in `{f | PowMulSeminormAt x₀ r f}` again
satisfies `PowMulSeminormAt x₀ r` and bounds the chain from below. -/
private theorem powMulSeminormAt_iInf_of_chain {x₀ : R} {r : ℝ}
    {c : Set (R → ℝ)} (hcs : c ⊆ {f | PowMulSeminormAt x₀ r f})
    (hc : IsChain (· ≥ ·) c) {y₀ : R → ℝ} (hy₀ : y₀ ∈ c) :
    ∃ lb ∈ {f | PowMulSeminormAt x₀ r f}, ∀ z ∈ c, lb ≤ z := by
  have : Nonempty c := ⟨⟨y₀, hy₀⟩⟩
  have hmem (z : c) : PowMulSeminormAt x₀ r z.val := hcs z.property
  let p : c → RingSeminorm R := fun z ↦ (hmem z).toRingSeminorm
  have hr : 0 ≤ r := (hmem ⟨y₀, hy₀⟩).apply_x₀ ▸ apply_nonneg (p ⟨y₀, hy₀⟩) x₀
  have hdir : Directed (· ≥ ·) (fun z : c ↦ (p z : R → ℝ)) := hc.directedOn.directed_val
  let lb : RingSeminorm R := iInfOfDirected p hdir
  have hlb_apply (a : R) : lb a = ⨅ z : c, z.val a := by
    simp only [lb, iInfOfDirected_apply, p, PowMulSeminormAt.toRingSeminorm_apply]
  have hlb_le (z : c) (a : R) : lb a ≤ z.val a := iInfOfDirected_le p hdir z a
  have hlb_pm : IsPowMul lb := isPowMul_iInfOfDirected p hdir (fun z ↦ (hmem z).isPowMul)
  have hlb_one : lb 1 = 1 := by
    simp only [hlb_apply, fun z : c ↦ (hmem z).map_one, ciInf_const]
  have hlb_x₀ : lb x₀ = r := by
    simp only [hlb_apply, fun z : c ↦ (hmem z).apply_x₀, ciInf_const]
  have hlb_x₀_mul (y : R) : lb (x₀ * y) = lb x₀ * lb y := by
    have hz_mul (z : c) : z.val (x₀ * y) = r * z.val y := by
      rw [(hmem z).const_mul y, (hmem z).apply_x₀]
    simp only [hlb_x₀, hlb_apply, hz_mul]
    exact (Real.mul_iInf_of_nonneg hr _).symm
  exact ⟨lb, PowMulSeminormAt.of_ringSeminorm lb hlb_pm hlb_one hlb_x₀ hlb_x₀_mul,
    fun z hz ↦ hlb_le ⟨z, hz⟩⟩

/-- Every minimal element of `{f | PowMulSeminormAt x₀ r f}` is multiplicative on all of `R`. -/
private theorem mul_of_minimal_powMulSeminormAt {x₀ : R} {r : ℝ} {m : R → ℝ}
    (hm_min : Minimal (· ∈ {f | PowMulSeminormAt x₀ r f}) m) (c y : R) :
    m (c * y) = m c * m y := by
  have hm : PowMulSeminormAt x₀ r m := hm_min.prop
  let ν : RingSeminorm R := hm.toRingSeminorm
  have hν_apply (a : R) : ν a = m a := hm.toRingSeminorm_apply a
  have hν_pm : IsPowMul ν := fun a k hk ↦ by
    simp only [hν_apply]
    exact hm.isPowMul a hk
  by_cases hc0 : ν c = 0
  · have hν_mul : ν (c * y) = ν c * ν y :=
      le_antisymm ((map_mul_le_mul ν c y).trans (by simp [hc0])) (by simp [hc0])
    simpa only [hν_apply] using hν_mul
  · let g : RingSeminorm R := seminormFromConst c ν
    have hg_le : (⇑g : R → ℝ) ≤ m := fun a ↦
      (seminormFromConst_le_seminorm c ν a).trans_eq (hν_apply a)
    have hν_x₀_mul (a : R) : ν (x₀ * a) = ν x₀ * ν a := by
      simp only [hν_apply]
      exact hm.const_mul a
    have hg_mem : PowMulSeminormAt x₀ r g :=
      PowMulSeminormAt.of_ringSeminorm g
        (seminormFromConst_isPowMul hν_pm)
        (seminormFromConst_one hc0 hν_pm)
        ((seminormFromConst_apply_of_isMul hc0 hν_pm hν_x₀_mul).trans
          ((hν_apply x₀).trans hm.apply_x₀))
        (seminormFromConst_isMul_of_isMul hc0 hν_pm hν_x₀_mul)
    have hgm : m = ⇑g := (hm_min.eq_of_le hg_mem hg_le).symm
    rw [hgm]
    exact seminormFromConst_const_mul hc0 hν_pm y

/-- Auxiliary step of BGR Theorem 1.3.2/3 when `ρ x₀ ≠ 0`. -/
private theorem exists_mulRingSeminorm_le_of_apply_ne_zero {ρ : RingSeminorm R}
    (hpm : IsPowMul ρ) {x₀ : R} (hx₀ : ρ x₀ ≠ 0) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  let μ₁ : RingSeminorm R := seminormFromConst x₀ ρ
  have hμ₁_le (x : R) : μ₁ x ≤ ρ x := seminormFromConst_le_seminorm x₀ ρ x
  have hμ₁_x₀ : μ₁ x₀ = ρ x₀ := seminormFromConst_apply_c hx₀ hpm
  have hμ₁_mem : PowMulSeminormAt x₀ (μ₁ x₀) μ₁ :=
    PowMulSeminormAt.of_ringSeminorm μ₁
      (seminormFromConst_isPowMul hpm)
      (seminormFromConst_one hx₀ hpm)
      rfl
      (seminormFromConst_const_mul hx₀ hpm)
  obtain ⟨m, hm_le, hm_min⟩ :=
    zorn_ge_nonempty₀ {f | PowMulSeminormAt x₀ (μ₁ x₀) f}
      (fun _ hcs hc _ hy₀ ↦ powMulSeminormAt_iInf_of_chain hcs hc hy₀)
      (⇑μ₁) hμ₁_mem
  have hm : PowMulSeminormAt x₀ (μ₁ x₀) m := hm_min.prop
  refine ⟨{ toAddGroupSeminorm := hm.toRingSeminorm.toAddGroupSeminorm
            map_one' := hm.map_one
            map_mul' := mul_of_minimal_powMulSeminormAt hm_min },
    fun x ↦ (hm_le x).trans (hμ₁_le x), hm.apply_x₀.trans hμ₁_x₀⟩

/-- **Bosch–Güntzer–Remmert Theorem 1.3.2/3.** For every nonzero power-multiplicative ring seminorm
`ρ` on a commutative ring `R` and every `x₀ : R`, there exists a multiplicative ring seminorm
`α : MulRingSeminorm R` with `α ≤ ρ` and `α x₀ = ρ x₀` (proved via Zorn's lemma and
`seminormFromConst`, [BGR, Proposition 1.3.2/2]). -/
theorem exists_mulRingSeminorm_le_and_apply_eq {ρ : RingSeminorm R} (hpm : IsPowMul ρ)
    (hρ : ρ ≠ 0) (x₀ : R) :
    ∃ α : MulRingSeminorm R, (∀ x, α x ≤ ρ x) ∧ α x₀ = ρ x₀ := by
  by_cases hx₀ : ρ x₀ = 0
  · have h1 : ρ 1 ≠ 0 := by
      rw [(ρ.seminorm_one_eq_one_iff_ne_zero hpm.map_one_le_one).2 hρ]
      exact one_ne_zero
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
