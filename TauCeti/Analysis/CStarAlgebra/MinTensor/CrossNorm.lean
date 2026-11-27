/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Algebra.Star.TensorProductLift
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.MaxTensor.Comparison
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# C*-norms on the algebraic tensor product of unital C*-algebras are cross norms

Let `A` and `B` be unital C*-algebras. A C*-norm on the algebraic tensor product `A ⊗[ℂ] B` is
presented as `x ↦ ‖Ψ x‖` for an injective star homomorphism `Ψ : A ⊗[ℂ] B → D` into a
C*-algebra `D`. Such a `Ψ` restricts to commuting star homomorphisms `a ↦ Ψ (a ⊗ 1)` and
`b ↦ Ψ (1 ⊗ b)` (its compositions with `Algebra.TensorProduct.includeLeftNonUnitalStarAlgHom`
and `Algebra.TensorProduct.includeRightNonUnitalStarAlgHom`), so `‖Ψ (a ⊗ 1)‖ ≤ ‖a‖`
(`NonUnitalStarAlgHom.norm_apply_tmul_one_le`), and `‖Ψ (a ⊗ b)‖ ≤ ‖a‖ ‖b‖` for every star
homomorphism `Ψ` (`NonUnitalStarAlgHom.norm_apply_tmul_le`, in
`TauCeti.Analysis.CStarAlgebra.MaxTensor.Comparison`). This file proves the reverse inequality for
injective `Ψ`: every C*-norm on `A ⊗[ℂ] B` is a cross norm, `‖Ψ (a ⊗ b)‖ = ‖a‖ ‖b‖`
(`TauCeti.norm_apply_tmul_of_injective`).

The proof reduces to positive `a`, `b` of norm one through the C*-identity. If
`c = ‖Ψ (a ⊗ b)‖ < 1`, choose `c < t ^ 2`, `t < s < 1`, a continuous `g` with `g = 0` on
`(-∞, t]`, `g = 1` on `[s, ∞)` and `g(x) ≤ x / t`, and a continuous `f` vanishing on `(-∞, s]`
with `f 1 = 1`, so that `f g = f`. Then `w₂ = Ψ (g(a) ⊗ g(b))` has norm at most `c / t ^ 2 < 1`,
while `w₁ = Ψ (f(a) ⊗ f(b))` satisfies `w₁ = w₁ w₂`, so `w₁ = 0`. Since `1` lies in the spectra
of `a` and `b`, `f(a)` and `f(b)` are nonzero, so `f(a) ⊗ f(b) ≠ 0`, contradicting injectivity.

## Main declarations

* `NonUnitalStarAlgHom.norm_apply_tmul_one_le`: `‖Ψ (a ⊗ 1)‖ ≤ ‖a‖`.
* `TauCeti.norm_apply_tmul_of_injective`: **every C*-norm is a cross norm**.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.5.1–II.9.5.2.
-/

public section

noncomputable section

open TensorProduct

universe u v w

namespace TauCeti

variable {A : Type u} {B : Type v} {D : Type w} [CStarAlgebra A] [CStarAlgebra B]
  [NonUnitalCStarAlgebra D]

/-- Every star homomorphism out of `A ⊗[ℂ] B` into a C*-algebra is bounded by `‖a‖` on
`a ⊗ 1`. -/
theorem _root_.NonUnitalStarAlgHom.norm_apply_tmul_one_le (Ψ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (a : A) :
    ‖Ψ (a ⊗ₜ 1)‖ ≤ ‖a‖ := by
  simpa using NonUnitalStarAlgHom.norm_apply_le
    (Ψ.comp Algebra.TensorProduct.includeLeftNonUnitalStarAlgHom) a

/-- The real functions of the proof of `TauCeti.one_le_norm_apply_tmul_of_injective`: with
`0 < t < s < 1`, `g` is `0` on `(-∞, t]` and `1` on `[s, ∞)`. -/
private def cutoff (t s x : ℝ) : ℝ :=
  max 0 (min 1 ((x - t) / (s - t)))

private theorem continuous_cutoff (t s : ℝ) : Continuous (cutoff t s) := by
  unfold cutoff
  fun_prop

private theorem cutoff_nonneg (t s x : ℝ) : 0 ≤ cutoff t s x :=
  le_max_left _ _

private theorem cutoff_le_one (t s x : ℝ) : cutoff t s x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem cutoff_eq_zero {t s x : ℝ} (hts : t < s) (hx : x ≤ t) : cutoff t s x = 0 := by
  refine max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg ?_ ?_))
  · linarith
  · linarith

private theorem cutoff_eq_one {t s x : ℝ} (hts : t < s) (hx : s ≤ x) : cutoff t s x = 1 := by
  have : 1 ≤ (x - t) / (s - t) := by
    rw [one_le_div (by linarith)]
    linarith
  rw [cutoff, min_eq_left this, max_eq_right zero_le_one]

/-- `x ↦ g(x) / x` made continuous: `g(x) / max x t`. -/
private def cutoffDiv (t s x : ℝ) : ℝ :=
  cutoff t s x / max x t

private theorem continuous_cutoffDiv {t s : ℝ} (ht : 0 < t) : Continuous (cutoffDiv t s) :=
  (continuous_cutoff t s).div (continuous_id.max continuous_const)
    fun x ↦ (ht.trans_le (le_max_right x t)).ne'

private theorem cutoffDiv_mul {t s : ℝ} (ht : 0 < t) (hts : t < s) (x : ℝ) :
    cutoffDiv t s x * x = cutoff t s x := by
  rcases le_or_gt x t with hx | hx
  · simp [cutoffDiv, cutoff_eq_zero hts hx]
  · rw [cutoffDiv, max_eq_left hx.le, div_mul_cancel₀ _ (ht.trans hx).ne']

private theorem norm_cutoffDiv_le {t s : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖cutoffDiv t s x‖ ≤ t⁻¹ := by
  have hm : 0 < max x t := ht.trans_le (le_max_right x t)
  rw [Real.norm_eq_abs, cutoffDiv, abs_div, abs_of_nonneg (cutoff_nonneg t s x),
    abs_of_pos hm, div_le_iff₀ hm]
  calc cutoff t s x ≤ 1 := cutoff_le_one t s x
    _ = t⁻¹ * t := (inv_mul_cancel₀ ht.ne').symm
    _ ≤ t⁻¹ * max x t := by gcongr; exact le_max_right x t

/-- The bump `max 0 ((x - s) / (1 - s))`, vanishing on `(-∞, s]` and `1` at `1`. -/
private def bump (s x : ℝ) : ℝ :=
  max 0 ((x - s) / (1 - s))

private theorem continuous_bump (s : ℝ) : Continuous (bump s) := by
  unfold bump
  fun_prop

private theorem bump_one {s : ℝ} (hs : s < 1) : bump s 1 = 1 := by
  rw [bump, div_self (by linarith), max_eq_right zero_le_one]

private theorem bump_mul_cutoff {t s : ℝ} (hts : t < s) (hs1 : s < 1) (x : ℝ) :
    bump s x * cutoff t s x = bump s x := by
  rcases le_or_gt x s with hx | hx
  · have : bump s x = 0 :=
      max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    rw [this, zero_mul]
  · rw [cutoff_eq_one hts hx.le, mul_one]

private theorem cfc_bump_mul_cfc_cutoff {C : Type*} [CStarAlgebra C] {t s : ℝ} (hts : t < s)
    (hs1 : s < 1) (x : C) : cfc (bump s) x * cfc (cutoff t s) x = cfc (bump s) x := by
  by_cases hx : IsSelfAdjoint x
  · rw [← cfc_mul (bump s) (cutoff t s) x (continuous_bump s).continuousOn
      (continuous_cutoff t s).continuousOn]
    exact cfc_congr fun y _ ↦ bump_mul_cutoff hts hs1 y
  · simp [cfc_apply_of_not_predicate x hx]

private theorem cfc_cutoff_eq {C : Type*} [CStarAlgebra C] {t s : ℝ} (ht0 : 0 < t) (hts : t < s)
    (x : C) (hx : IsSelfAdjoint x) : cfc (cutoff t s) x = cfc (cutoffDiv t s) x * x := by
  have h := cfc_mul (cutoffDiv t s) (fun y : ℝ ↦ y) x (continuous_cutoffDiv ht0).continuousOn
  rw [cfc_id' ℝ x] at h
  rw [← h]
  exact cfc_congr fun y _ ↦ (cutoffDiv_mul ht0 hts y).symm

private theorem norm_cfc_cutoffDiv_le {C : Type*} [CStarAlgebra C] {t s : ℝ} (ht0 : 0 < t)
    (x : C) : ‖cfc (cutoffDiv t s) x‖ ≤ t⁻¹ :=
  norm_cfc_le (inv_nonneg.2 ht0.le) fun y _ ↦ norm_cutoffDiv_le ht0 y

private theorem cfc_bump_ne_zero {C : Type*} [CStarAlgebra C] {s : ℝ} (hs1 : s < 1) (x : C)
    (hx : IsSelfAdjoint x) (h1 : (1 : ℝ) ∈ spectrum ℝ x) : cfc (bump s) x ≠ 0 := by
  intro h0
  have := norm_apply_le_norm_cfc (bump s) x h1 (continuous_bump s).continuousOn hx
  rw [h0, norm_zero, bump_one hs1, norm_one] at this
  exact absurd this (by norm_num)

/-- For `0 ≤ c < 1` there are `0 < t < s < 1` with `c / t ^ 2 < 1`. -/
private theorem exists_cutoff_params {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ t s : ℝ, 0 < t ∧ t < s ∧ s < 1 ∧ t⁻¹ * t⁻¹ * c < 1 := by
  set q : ℝ := (1 + c) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have ht0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have ht1 : Real.sqrt q < 1 := by
    rw [Real.sqrt_lt' zero_lt_one, one_pow, hq]; linarith
  refine ⟨Real.sqrt q, (Real.sqrt q + 1) / 2, ht0, by linarith, by linarith, ?_⟩
  rw [← mul_inv, ← pow_two, Real.sq_sqrt hq0.le, inv_mul_lt_iff₀ hq0, mul_one, hq]
  linarith

/-- The core of `TauCeti.norm_apply_tmul_of_injective`: for an injective `Ψ` and positive `a`, `b`
of norm one, `‖Ψ (a ⊗ b)‖ ≥ 1`. -/
theorem one_le_norm_apply_tmul_of_injective [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B] {Ψ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D}
    (hΨ : Function.Injective Ψ) {a : A} {b : B} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : ‖a‖ = 1)
    (hb1 : ‖b‖ = 1) : 1 ≤ ‖Ψ (a ⊗ₜ b)‖ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, s, ht0, hts, hs1, hc⟩ := exists_cutoff_params (norm_nonneg _) hlt
  have haA : Nontrivial A := ⟨⟨a, 0, fun h ↦ by simp [h] at ha1⟩⟩
  have hbB : Nontrivial B := ⟨⟨b, 0, fun h ↦ by simp [h] at hb1⟩⟩
  have ha_mem : (1 : ℝ) ∈ spectrum ℝ a := ha1 ▸ CStarAlgebra.norm_mem_spectrum_of_nonneg a
  have hb_mem : (1 : ℝ) ∈ spectrum ℝ b := hb1 ▸ CStarAlgebra.norm_mem_spectrum_of_nonneg b
  have hsa := IsSelfAdjoint.of_nonneg ha
  have hsb := IsSelfAdjoint.of_nonneg hb
  -- `w₂ = Ψ (g(a) ⊗ g(b))` has norm `< 1`.
  have hw₂ : ‖Ψ (cfc (cutoff t s) a ⊗ₜ cfc (cutoff t s) b)‖ < 1 := by
    rw [cfc_cutoff_eq ht0 hts a hsa, cfc_cutoff_eq ht0 hts b hsb,
      ← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
    refine lt_of_le_of_lt ((norm_mul_le _ _).trans ?_) hc
    refine mul_le_mul_of_nonneg_right ((Ψ.norm_apply_tmul_le _ _).trans ?_) (norm_nonneg _)
    exact mul_le_mul (norm_cfc_cutoffDiv_le ht0 a) (norm_cfc_cutoffDiv_le ht0 b)
      (norm_nonneg _) (inv_nonneg.2 ht0.le)
  -- `w₁ = Ψ (f(a) ⊗ f(b))` satisfies `w₁ = w₁ w₂`, so `w₁ = 0`.
  have hw₁ := eq_zero_of_eq_mul_of_norm_lt_one (w₁ := Ψ (cfc (bump s) a ⊗ₜ cfc (bump s) b))
    (by rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, cfc_bump_mul_cfc_cutoff hts hs1 a,
      cfc_bump_mul_cfc_cutoff hts hs1 b]) hw₂
  exact tmul_ne_zero (cfc_bump_ne_zero hs1 a hsa ha_mem)
    (cfc_bump_ne_zero hs1 b hsb hb_mem) (hΨ (hw₁.trans (map_zero Ψ).symm))

/-- **Every C*-norm on the algebraic tensor product of unital C*-algebras is a cross norm**:
an injective star homomorphism `Ψ : A ⊗[ℂ] B → D` into a C*-algebra has
`‖Ψ (a ⊗ b)‖ = ‖a‖ ‖b‖`. -/
theorem norm_apply_tmul_of_injective {Ψ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] D} (hΨ : Function.Injective Ψ)
    (a : A) (b : B) : ‖Ψ (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm (Ψ.norm_apply_tmul_le a b) ?_
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  let _ := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  let _ := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  set a' : A := (‖a‖ ^ 2)⁻¹ • (star a * a)
  set b' : B := (‖b‖ ^ 2)⁻¹ • (star b * b)
  have ha' : 0 ≤ a' := smul_nonneg (by positivity) (star_mul_self_nonneg a)
  have hb' : 0 ≤ b' := smul_nonneg (by positivity) (star_mul_self_nonneg b)
  have key := one_le_norm_apply_tmul_of_injective hΨ ha' hb'
    (CStarRing.norm_inv_norm_sq_smul_star_mul_self ha)
    (CStarRing.norm_inv_norm_sq_smul_star_mul_self hb)
  have heq : Ψ (a' ⊗ₜ b') =
      (((‖a‖ ^ 2)⁻¹ * (‖b‖ ^ 2)⁻¹ : ℝ) : ℂ) • (star (Ψ (a ⊗ₜ b)) * Ψ (a ⊗ₜ b)) := by
    rw [← map_star, ← map_mul, TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      ← map_smul]
    congr 1
    simp only [a', b', ← Complex.coe_smul]
    rw [tmul_smul, ← smul_tmul', smul_smul, Complex.ofReal_mul, mul_comm]
  rw [heq, norm_smul, CStarRing.norm_star_mul_self, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)] at key
  have : (‖a‖ * ‖b‖) ^ 2 ≤ ‖Ψ (a ⊗ₜ b)‖ ^ 2 := by
    rw [mul_pow]
    calc ‖a‖ ^ 2 * ‖b‖ ^ 2 = (‖a‖ ^ 2 * ‖b‖ ^ 2) * 1 := (mul_one _).symm
      _ ≤ (‖a‖ ^ 2 * ‖b‖ ^ 2) * ((‖a‖ ^ 2)⁻¹ * (‖b‖ ^ 2)⁻¹ *
          (‖Ψ (a ⊗ₜ b)‖ * ‖Ψ (a ⊗ₜ b)‖)) := by gcongr
      _ = ‖Ψ (a ⊗ₜ b)‖ ^ 2 := by field_simp
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 this

end TauCeti
