/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.RCLike.TangentCone
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Complex.HasPrimitives.Basic
import TauCeti.Basic.Complex.Basic

/-!
# Vertical strips

Mathlib's three-lines theorem is stated on the open strip `verticalStrip a b` and the closed
strip `verticalClosedStrip a b`, the preimages of `Ioo a b` and `Icc a b` under `Complex.re`.
This file records their membership criteria, behavior under reflection, convexity, closure, unique
differentiability (`uniqueDiffOn_verticalClosedStrip`), vanishing of imaginary parts of iterated
derivatives along the real segment for functions real-valued on `[a, b]`
(`ContDiffOn.im_iteratedDerivWithin_verticalClosedStrip_eq_zero`), the vertical Taylor–Lagrange
expansion of `Im f(c + i y)` (`TauCeti.exists_im_add_mul_I_eq_taylor_odd`), the exponential gauge
multiplier `scaleFactor` normalizing strip boundary bounds, holomorphic primitives
`Complex.wedgeIntegral` for functions satisfying `DiffContOnCl` on a vertical strip (specializing
`TauCeti.Analysis.Complex.HasPrimitives.Basic` to `verticalClosedStrip a b = Icc a b ×ℂ univ`),
and the Cauchy rectangle contour-shift identity `DiffContOnCl.intervalIntegral_add_mul_I_eq`
equating vertical line integrals of vertically periodic holomorphic strip functions.
-/

public section

open Complex Complex.HadamardThreeLines Set
open scoped Interval Topology

namespace TauCeti.Complex.HadamardThreeLines

variable {a b : ℝ} {z : ℂ}

@[simp] theorem mem_verticalStrip_iff : z ∈ verticalStrip a b ↔ z.re ∈ Ioo a b := Iff.rfl

@[simp] theorem mem_verticalClosedStrip_iff : z ∈ verticalClosedStrip a b ↔ z.re ∈ Icc a b :=
  Iff.rfl

/-- The closed vertical strip `verticalClosedStrip a b` as a set comprehension. -/
theorem verticalClosedStrip_eq_setOf (a b : ℝ) :
    verticalClosedStrip a b = {z : ℂ | a ≤ z.re ∧ z.re ≤ b} := by
  ext z; exact mem_verticalClosedStrip_iff

/-- Reflection by `z ↦ w - z` reverses the real endpoints of an open vertical strip. -/
theorem sub_mem_verticalStrip_iff (w z : ℂ) :
    w - z ∈ verticalStrip a b ↔ z ∈ verticalStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalStrip_iff, mem_Ioo, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection by `z ↦ w - z` reverses the real endpoints of a closed vertical strip. -/
theorem sub_mem_verticalClosedStrip_iff (w z : ℂ) :
    w - z ∈ verticalClosedStrip a b ↔ z ∈ verticalClosedStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalClosedStrip_iff, mem_Icc, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection in the middle of the unit strip preserves open-strip membership. -/
theorem one_sub_mem_verticalStrip_iff : 1 - z ∈ verticalStrip 0 1 ↔ z ∈ verticalStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalStrip_iff (a := 0) (b := 1) (1 : ℂ) z

/-- Reflection in the middle of the unit strip preserves closed-strip membership. -/
theorem one_sub_mem_verticalClosedStrip_iff :
    1 - z ∈ verticalClosedStrip 0 1 ↔ z ∈ verticalClosedStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalClosedStrip_iff (a := 0) (b := 1) (1 : ℂ) z

/-- Complex conjugation preserves open vertical strips. -/
theorem mapsTo_conj_verticalStrip (a b : ℝ) :
    MapsTo (starRingEnd ℂ) (verticalStrip a b) (verticalStrip a b) :=
  fun _ hz => by simpa only [mem_verticalStrip_iff, conj_re] using hz

/-- Complex conjugation preserves closed vertical strips. -/
theorem mapsTo_conj_verticalClosedStrip (a b : ℝ) :
    MapsTo (starRingEnd ℂ) (verticalClosedStrip a b) (verticalClosedStrip a b) :=
  fun _ hz => by simpa only [mem_verticalClosedStrip_iff, conj_re] using hz

theorem isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  isOpen_Ioo.preimage continuous_re

theorem convex_verticalStrip (a b : ℝ) : Convex ℝ (verticalStrip a b) :=
  (convex_Ioo a b).linear_preimage reLm

theorem convex_verticalClosedStrip (a b : ℝ) : Convex ℝ (verticalClosedStrip a b) :=
  (convex_Icc a b).linear_preimage reLm

theorem verticalStrip_subset_verticalClosedStrip (a b : ℝ) :
    verticalStrip a b ⊆ verticalClosedStrip a b :=
  preimage_mono Ioo_subset_Icc_self

theorem closure_verticalStrip_subset (a b : ℝ) :
    closure (verticalStrip a b) ⊆ verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re]
  exact preimage_mono (closure_minimal Ioo_subset_Icc_self isClosed_Icc)

/-- When `a < b`, the closure of the open vertical strip `verticalStrip a b` is the closed strip
`verticalClosedStrip a b`. -/
theorem closure_verticalStrip (hab : a < b) :
    closure (verticalStrip a b) = verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo hab.ne, verticalClosedStrip]

/-- A closed vertical strip `verticalClosedStrip a b` with `a < b` has unique complex derivatives
at every point, including on both vertical boundary lines `Re z = a` and `Re z = b`. -/
theorem uniqueDiffOn_verticalClosedStrip (hab : a < b) :
    UniqueDiffOn ℂ (verticalClosedStrip a b) := by
  have hconv : Convex ℝ (verticalClosedStrip a b) :=
    (convex_Icc a b).linear_preimage reLm
  have hsub : verticalStrip a b ⊆ interior (verticalClosedStrip a b) :=
    interior_maximal (verticalStrip_subset_verticalClosedStrip a b) (isOpen_verticalStrip a b)
  refine uniqueDiffOn_convex_of_isRCLikeNormedField hconv ⟨(((a + b) / 2 : ℝ) : ℂ), hsub ?_⟩
  simp only [mem_verticalStrip_iff, mem_Ioo, ofReal_re]
  constructor <;> linarith

end TauCeti.Complex.HadamardThreeLines

/-- If `f : ℂ → ℂ` is `C^n` on the closed vertical strip `verticalClosedStrip a b` (`a < b`)
and real-valued on `[a, b]`, then every iterated derivative
`iteratedDerivWithin k f (verticalClosedStrip a b) c` (`k ≤ n`, `c ∈ [a, b]`) has vanishing
imaginary part. -/
theorem ContDiffOn.im_iteratedDerivWithin_verticalClosedStrip_eq_zero {f : ℂ → ℂ} {a b c : ℝ}
    {n : WithTop ℕ∞} {k : ℕ} (hf : ContDiffOn ℂ n f (verticalClosedStrip a b))
    (hab : a < b) (hc : c ∈ Icc a b) (hk : (k : WithTop ℕ∞) ≤ n)
    (hreal : ∀ x ∈ Icc a b, (f x).im = 0) :
    (iteratedDerivWithin k f (verticalClosedStrip a b) c).im = 0 := by
  have huniqS : UniqueDiffOn ℂ (verticalClosedStrip a b) :=
    TauCeti.Complex.HadamardThreeLines.uniqueDiffOn_verticalClosedStrip hab
  have hmaps : MapsTo (fun t : ℝ => (0 : ℂ) + t • (1 : ℂ)) (Icc a b) (verticalClosedStrip a b) :=
    fun t ht => by simp [TauCeti.Complex.HadamardThreeLines.mem_verticalClosedStrip_iff,
      Complex.real_smul, ht]
  simpa [Complex.real_smul] using
    hf.map_pow_smul_iteratedDerivWithin_eq_zero huniqS (uniqueDiffOn_Icc hab) hmaps
      Complex.imCLM (fun t ht => by simpa [Complex.real_smul] using hreal t ht) hk hc

namespace TauCeti.Complex.HadamardThreeLines

variable {a b : ℝ} {z : ℂ}

section ScaleFactor

/-- The exponential gauge multiplier `exp ((z - 1) * log M₀ - z * log M₁)` on the unit vertical
strip, equal to `M₀ ^ (z - 1) * M₁ ^ (-z)` for `0 < M₀` and `0 < M₁`, with modulus `M₀⁻¹` on
`re z = 0` and `M₁⁻¹` on `re z = 1`. -/
noncomputable def scaleFactor (M₀ M₁ : ℝ) (z : ℂ) : ℂ :=
  exp ((z - 1) * Real.log M₀ - z * Real.log M₁)

theorem scaleFactor_def (M₀ M₁ : ℝ) (z : ℂ) :
    scaleFactor M₀ M₁ z = exp ((z - 1) * Real.log M₀ - z * Real.log M₁) := (rfl)

@[simp] theorem scaleFactor_ne_zero (M₀ M₁ : ℝ) (z : ℂ) : scaleFactor M₀ M₁ z ≠ 0 := exp_ne_zero _

variable {M₀ M₁ : ℝ}

theorem differentiable_scaleFactor (M₀ M₁ : ℝ) : Differentiable ℂ (scaleFactor M₀ M₁) := by
  unfold scaleFactor; fun_prop

theorem norm_scaleFactor (z : ℂ) :
    ‖scaleFactor M₀ M₁ z‖ = Real.exp ((z.re - 1) * Real.log M₀ - z.re * Real.log M₁) := by
  simp [scaleFactor, norm_exp]

theorem norm_scaleFactor_le {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖scaleFactor M₀ M₁ z‖ ≤ Real.exp (|Real.log M₀| + |Real.log M₁|) := by
  rw [norm_scaleFactor]; refine Real.exp_le_exp.2 ?_
  nlinarith [hz.1, hz.2, neg_abs_le (Real.log M₀), le_abs_self (Real.log M₀),
    neg_abs_le (Real.log M₁), le_abs_self (Real.log M₁), abs_nonneg (Real.log M₀)]

theorem norm_scaleFactor_mul_I (hM₀ : 0 < M₀) (t : ℝ) : ‖scaleFactor M₀ M₁ (t * I)‖ = M₀⁻¹ := by
  simp [norm_scaleFactor, Real.exp_neg, Real.exp_log hM₀]

theorem norm_scaleFactor_one_add_mul_I (hM₁ : 0 < M₁) (t : ℝ) :
    ‖scaleFactor M₀ M₁ (1 + t * I)‖ = M₁⁻¹ := by
  simp [norm_scaleFactor, Real.exp_neg, Real.exp_log hM₁]

theorem norm_scaleFactor_mul_rpow (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (θ : ℝ) :
    ‖scaleFactor M₀ M₁ θ‖ * (M₀ ^ (1 - θ) * M₁ ^ θ) = 1 := by
  rw [norm_scaleFactor, Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_zero]
  congr 1; simp only [ofReal_re]; ring

theorem hasDerivAt_scaleFactor (M₀ M₁ : ℝ) (z : ℂ) :
    HasDerivAt (scaleFactor M₀ M₁) ((Real.log M₀ - Real.log M₁ : ℂ) * scaleFactor M₀ M₁ z) z :=
  (((((hasDerivAt_id z).sub_const 1).mul_const (Real.log M₀ : ℂ)).sub
    ((hasDerivAt_id z).mul_const (Real.log M₁ : ℂ))).cexp).congr_deriv (by simp [scaleFactor]; ring)

theorem integral_mul_scaleFactor_add_mul_I (M₀ M₁ c t₀ t : ℝ) :
    (∫ u in t₀..t, ((Real.log M₀ - Real.log M₁ : ℂ) * I) * scaleFactor M₀ M₁ (c + u * I)) =
      scaleFactor M₀ M₁ (c + t * I) - scaleFactor M₀ M₁ (c + t₀ * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => scaleFactor M₀ M₁ (c + u * I)) (fun u _ => ?_)
    ((((differentiable_scaleFactor M₀ M₁).continuous.comp
      (by fun_prop : Continuous fun x : ℝ => (c : ℂ) + x * I)).const_mul _).intervalIntegrable _ _)
  have hφ : HasDerivAt (fun x : ℝ => (c : ℂ) + (x : ℂ) * I) I u := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (c : ℂ)
  exact ((hasDerivAt_scaleFactor M₀ M₁ (c + u * I)).comp u hφ).congr_deriv (mul_right_comm _ _ _)

end ScaleFactor

end TauCeti.Complex.HadamardThreeLines

section Primitive

open TauCeti.Complex.HadamardThreeLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a b : ℝ}

private theorem verticalClosedStrip_eq_reProdIm (a b : ℝ) :
    verticalClosedStrip a b = Icc a b ×ℂ (univ : Set ℝ) := by
  ext; simp [verticalClosedStrip, mem_reProdIm]

/-- For `a < b`, a function satisfying `DiffContOnCl ℂ f (verticalStrip a b)` is continuous on
`verticalClosedStrip a b`. -/
theorem DiffContOnCl.continuousOn_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) : ContinuousOn f (verticalClosedStrip a b) :=
  closure_verticalStrip hab ▸ hf.continuousOn

/-- Cauchy–Goursat on the closed vertical strip: a function holomorphic on `verticalStrip a b` and
continuous up to its boundary has zero integral around every closed rectangle in
`verticalClosedStrip a b`, even when the rectangle meets the boundary lines. -/
theorem DiffContOnCl.isConservativeOn_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) : IsConservativeOn f (verticalClosedStrip a b) :=
  Complex.isConservativeOn_of_continuousOn_of_differentiableOn_interior
    (hf.continuousOn_verticalClosedStrip hab)
    (by simpa [verticalClosedStrip, Complex.interior_preimage_re, interior_Icc, verticalStrip] using
      hf.differentiableOn)

/-- Wedge integrals of a function satisfying `DiffContOnCl` on a vertical strip are additive across
arbitrary points of the closed strip, including boundary points. -/
theorem DiffContOnCl.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ z w : ℂ}
    (hz₀ : z₀ ∈ verticalClosedStrip a b) (hz : z ∈ verticalClosedStrip a b)
    (hw : w ∈ verticalClosedStrip a b) :
    wedgeIntegral z₀ w f - wedgeIntegral z₀ z f = wedgeIntegral z w f := by
  have hc := hf.isConservativeOn_verticalClosedStrip hab
  have hcont := hf.continuousOn_verticalClosedStrip hab
  rw [verticalClosedStrip_eq_reProdIm] at hc hcont hz₀ hz hw
  exact hc.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_reProdIm ordConnected_Icc ordConnected_univ
    hcont hz₀ hz hw

/-- The wedge integral on a closed vertical strip is continuous up to the boundary. -/
theorem DiffContOnCl.continuousOn_wedgeIntegral_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ : ℂ} (hz₀ : z₀ ∈ verticalClosedStrip a b) :
    ContinuousOn (fun z => wedgeIntegral z₀ z f) (verticalClosedStrip a b) := by
  have hc := hf.isConservativeOn_verticalClosedStrip hab
  have hcont := hf.continuousOn_verticalClosedStrip hab
  rw [verticalClosedStrip_eq_reProdIm] at hc hcont hz₀ ⊢
  exact hc.continuousOn_wedgeIntegral_of_mem_reProdIm ordConnected_Icc ordConnected_univ hcont hz₀

/-- On the open vertical strip, the wedge integral from any base point in the closed strip has
complex derivative equal to its integrand. -/
theorem DiffContOnCl.hasDerivAt_wedgeIntegral_verticalStrip [CompleteSpace E]
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ z : ℂ}
    (hz₀ : z₀ ∈ verticalClosedStrip a b) (hz : z ∈ verticalStrip a b) :
    HasDerivAt (fun w => wedgeIntegral z₀ w f) (f z) z := by
  have hc := hf.isConservativeOn_verticalClosedStrip (hz.1.trans hz.2)
  have hcont := hf.continuousOn_verticalClosedStrip (hz.1.trans hz.2)
  have hnhds : verticalClosedStrip a b ∈ 𝓝 z := Filter.mem_of_superset
    ((isOpen_verticalStrip a b).mem_nhds hz) (verticalStrip_subset_verticalClosedStrip a b)
  rw [verticalClosedStrip_eq_reProdIm] at hc hcont hz₀ hnhds
  exact hc.hasDerivAt_wedgeIntegral_of_mem_reProdIm ordConnected_Icc ordConnected_univ hcont hz₀
    hnhds

/-- The wedge integral of a function satisfying `DiffContOnCl` on a vertical strip again satisfies
`DiffContOnCl` on that strip. -/
theorem DiffContOnCl.diffContOnCl_wedgeIntegral_verticalStrip [CompleteSpace E] (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ : ℂ} (hz₀ : z₀ ∈ verticalClosedStrip a b) :
    DiffContOnCl ℂ (fun w => wedgeIntegral z₀ w f) (verticalStrip a b) :=
  ⟨fun _ hz =>
      (hf.hasDerivAt_wedgeIntegral_verticalStrip hz₀ hz).differentiableAt.differentiableWithinAt,
    closure_verticalStrip hab ▸ hf.continuousOn_wedgeIntegral_verticalClosedStrip hab hz₀⟩

end Primitive

section ContourShift

open TauCeti.Complex.HadamardThreeLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a b : ℝ}

/-- **Contour shift across a vertical strip.** If `f : ℂ → E` is holomorphic on `verticalStrip a b`
(`a ≤ b`), continuous on its closure, and vertically periodic of period `T` on `[a, b]`, then its
vertical interval integrals along `re z = a` and `re z = b` over `0..T` agree. -/
theorem DiffContOnCl.intervalIntegral_add_mul_I_eq (hf : DiffContOnCl ℂ f (verticalStrip a b))
    (hab : a ≤ b) (T : ℝ) (hper : ∀ x ∈ Icc a b, f (x + T * I) = f x) :
    (∫ y : ℝ in 0..T, f (a + y * I)) = ∫ y : ℝ in 0..T, f (b + y * I) := by
  rcases hab.eq_or_lt with rfl | hab; · rfl
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
    ⟨a, 0⟩ ⟨b, T⟩
    (hf.continuousOn.mono fun _ hz => by
      rw [closure_verticalStrip hab]; simpa [uIcc_of_le hab.le] using hz.1)
    (hf.differentiableOn.mono fun _ hz => by
      simpa [min_eq_left hab.le, max_eq_right hab.le] using hz.1)
  have htop : (∫ x : ℝ in a..b, f (x + T * I)) = ∫ x : ℝ in a..b, f (x + (0 : ℝ) * I) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [ofReal_zero, zero_mul, add_zero]; exact hper x (uIcc_of_le hab.le ▸ hx)
  rw [htop, sub_self, zero_add, sub_eq_zero, smul_right_inj I_ne_zero] at hrect; exact hrect.symm

/-- Twisting a `T`-vertically periodic strip function by `exp (-(2π m / T) z)` (`m : ℤ`) preserves
vertical `T`-periodicity, so its vertical integrals over `0..T` along `re z = a` and `re z = b`
agree. -/
theorem DiffContOnCl.intervalIntegral_exp_smul_add_mul_I_eq
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) (hab : a ≤ b) (T : ℝ)
    (hper : ∀ x ∈ Icc a b, f (x + T * I) = f x) (m : ℤ) :
    (∫ y : ℝ in 0..T, exp (-(2 * Real.pi * m / T : ℂ) * (a + y * I)) • f (a + y * I)) =
      ∫ y : ℝ in 0..T, exp (-(2 * Real.pi * m / T : ℂ) * (b + y * I)) • f (b + y * I) := by
  rcases eq_or_ne T 0 with rfl | hT; · simp
  set ω : ℂ := -(2 * Real.pi * m / T : ℂ)
  refine ((by fun_prop : Differentiable ℂ fun z : ℂ => exp (ω * z)).diffContOnCl.smul
    hf).intervalIntegral_add_mul_I_eq hab T fun x hx => ?_
  have hωT : ω * (T * I) = ((-m : ℤ) : ℂ) * (2 * Real.pi * I) := by
    have : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT; simp only [ω]; push_cast; field_simp
  simp only [hper x hx, mul_add, Complex.exp_add, hωT, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end ContourShift

section VerticalTaylor

open scoped Nat

namespace TauCeti

/-- The degree-`(2 * m - 1)` Taylor polynomial of `t ↦ Im f(c + i t)` on `[0, y]` collapses to
the odd-order sum over `Finset.Icc 1 m` when `f` is real on `[a, b]`. -/
private lemma taylorWithinEval_im_comp {f : ℂ → ℂ} {a b c y : ℝ} {m : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b) (hm : 1 ≤ m) (hy : 0 < y)
    (hf : ContDiffOn ℂ (2 * m : ℕ) f (verticalClosedStrip a b))
    (hreal : ∀ x ∈ Icc a b, (f x).im = 0)
    (hψ : ContDiff ℝ (2 * m : ℕ) (_root_.Complex.imCLM ∘ (f ∘ fun t : ℝ => (c : ℂ) + t • I)))
    (hψ_deriv : ∀ {k : ℕ}, k ≤ 2 * m →
      iteratedDeriv k (_root_.Complex.imCLM ∘ (f ∘ fun t : ℝ => (c : ℂ) + t • I)) 0 =
        (I ^ k * iteratedDerivWithin k f (verticalClosedStrip a b) c).im) :
    taylorWithinEval (_root_.Complex.imCLM ∘ (f ∘ fun t : ℝ => (c : ℂ) + t • I))
        (2 * m - 1) (uIcc 0 y) 0 y =
      ∑ s ∈ Finset.Icc 1 m,
        (-1 : ℝ) ^ (s - 1) *
          (iteratedDerivWithin (2 * s - 1) f (verticalClosedStrip a b) c).re *
          y ^ (2 * s - 1) / (2 * s - 1)! := by
  let S : Set ℂ := verticalClosedStrip a b
  let ψ : ℝ → ℝ := _root_.Complex.imCLM ∘ (f ∘ fun t : ℝ => (c : ℂ) + t • I)
  have h2m : (2 * m - 1) + 1 = 2 * m := by omega
  rw [taylor_within_apply, h2m]
  have hcongr : ∑ k ∈ Finset.range (2 * m),
        ((k ! : ℝ)⁻¹ * (y - 0) ^ k) • iteratedDerivWithin k ψ (uIcc 0 y) 0 =
      ∑ k ∈ Finset.range (2 * m),
        (I ^ k * iteratedDerivWithin k f S c).im * y ^ k / (k ! : ℝ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ 2 * m := (Finset.mem_range.mp hk).le
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy.ne)
      (hψ.contDiffAt.of_le (by exact_mod_cast hk_le)) left_mem_uIcc,
      hψ_deriv hk_le, sub_zero, smul_eq_mul]
    ring
  rw [hcongr, Finset.sum_range_two_mul]
  have heven : ∑ j ∈ Finset.range m,
      (I ^ (2 * j) * iteratedDerivWithin (2 * j) f S c).im * y ^ (2 * j) / ((2 * j)! : ℝ) =
      0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj_le : 2 * j ≤ 2 * m := by
      have := Finset.mem_range.mp hj; omega
    have him0 : (iteratedDerivWithin (2 * j) f S c).im = 0 :=
      hf.im_iteratedDerivWithin_verticalClosedStrip_eq_zero hab hc (by exact_mod_cast hj_le) hreal
    rw [_root_.Complex.im_I_pow_two_mul_mul, him0, mul_zero, zero_mul, zero_div]
  rw [heven, zero_add]
  symm
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, add_tsub_cancel_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : 2 * (1 + j) - 1 = 2 * j + 1 := by omega
  rw [Nat.add_sub_cancel_left, hsub, _root_.Complex.im_I_pow_two_mul_add_one_mul]

/-- Pointwise Taylor–Lagrange identity along a vertical line: if `f : ℂ → ℂ` is `C^{2m}`
(`1 ≤ m`) on the closed vertical strip `verticalClosedStrip a b` (`a < b`) and real-valued on
`[a, b]`, then for any `c ∈ [a, b]` and `y > 0` there exists `θ ∈ (0, 1)` such that
`Im f(c + y i)` equals its odd-order Taylor polynomial of degree `2m - 1` plus the Lagrange
remainder `(-1)^m * Im f^{(2m)}(c + θ y i) * y^{2m} / (2m)!`. -/
theorem exists_im_add_mul_I_eq_taylor_odd {f : ℂ → ℂ} {a b c y : ℝ} {m : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b) (hm : 1 ≤ m) (hy : 0 < y)
    (hf : ContDiffOn ℂ (2 * m : ℕ) f (verticalClosedStrip a b))
    (hreal : ∀ x ∈ Icc a b, (f x).im = 0) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      (f (c + y * I)).im =
        (∑ s ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (s - 1) *
            (iteratedDerivWithin (2 * s - 1) f (verticalClosedStrip a b) c).re *
            y ^ (2 * s - 1) / (2 * s - 1)!) +
        (-1 : ℝ) ^ m *
          (iteratedDerivWithin (2 * m) f (verticalClosedStrip a b)
            (c + ((θ * y : ℝ) : ℂ) * I)).im *
          y ^ (2 * m) / (2 * m)! := by
  let S : Set ℂ := verticalClosedStrip a b
  have huniqS : UniqueDiffOn ℂ S :=
    TauCeti.Complex.HadamardThreeLines.uniqueDiffOn_verticalClosedStrip hab
  let γ : ℝ → ℂ := fun t => (c : ℂ) + t • I
  have hγ_mem : ∀ t : ℝ, γ t ∈ S := fun t => by
    simp [S, TauCeti.Complex.HadamardThreeLines.mem_verticalClosedStrip_iff, γ,
      _root_.Complex.real_smul, hc.1, hc.2]
  have hfγ : ContDiff ℝ (2 * m : ℕ) (f ∘ γ) :=
    (hf.restrict_scalars ℝ).comp_contDiff (by fun_prop) hγ_mem
  let ψ : ℝ → ℝ := _root_.Complex.imCLM ∘ (f ∘ γ)
  have hψ : ContDiff ℝ (2 * m : ℕ) ψ := _root_.Complex.imCLM.contDiff.comp hfγ
  -- Line derivatives along `t ↦ c + t * I`.
  have hψ_deriv : ∀ {k : ℕ}, k ≤ 2 * m → ∀ t : ℝ,
      iteratedDeriv k ψ t = (I ^ k * iteratedDerivWithin k f S ((c : ℂ) + (t : ℂ) * I)).im := by
    intro k hk t
    have hk' : (k : WithTop ℕ∞) ≤ ((2 * m : ℕ) : WithTop ℕ∞) := by exact_mod_cast hk
    rw [_root_.Complex.imCLM.iteratedDeriv_comp_left hfγ.contDiffAt hk']
    have hline := hf.iteratedDeriv_comp_add_smul huniqS hγ_mem hk' t
    simpa [γ, S, Function.comp_def, _root_.Complex.real_smul, smul_eq_mul] using
      congrArg _root_.Complex.im hline
  -- Lagrange remainder on `[0, y]`.
  have h2m : (2 * m - 1) + 1 = 2 * m := by omega
  have hψ_on : ContDiffOn ℝ (((2 * m - 1 : ℕ) : WithTop ℕ∞) + 1) ψ (uIcc 0 y) := by
    have h1 : ContDiffOn ℝ (2 * m : ℕ) ψ (uIcc 0 y) := hψ.contDiffOn
    rwa [← h2m, Nat.cast_add, Nat.cast_one] at h1
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hy.ne hψ_on
  rw [uIoo_of_lt hy] at hξ_mem
  refine ⟨ξ / y, ⟨div_pos hξ_mem.1 hy, (div_lt_one hy).mpr hξ_mem.2⟩, ?_⟩
  have hθy : ξ / y * y = ξ := div_mul_cancel₀ ξ hy.ne'
  -- Polynomial part (even terms vanish since `f` is real on `[a, b]`).
  have htaylor := taylorWithinEval_im_comp hab hc hm hy hf hreal hψ fun hk => by
    simpa only [ofReal_zero, zero_mul, add_zero] using hψ_deriv hk 0
  -- Remainder part.
  have hrem : iteratedDeriv ((2 * m - 1) + 1) ψ ξ * (y - 0) ^ ((2 * m - 1) + 1) /
        ((2 * m - 1) + 1)! =
      (-1 : ℝ) ^ m * (iteratedDerivWithin (2 * m) f S (c + ((ξ / y * y : ℝ) : ℂ) * I)).im *
        y ^ (2 * m) / (2 * m)! := by
    rw [h2m, hψ_deriv le_rfl ξ, hθy, sub_zero, _root_.Complex.im_I_pow_two_mul_mul]
  have hψy : ψ y = (f (c + (y : ℂ) * I)).im := by simp [ψ, γ, _root_.Complex.real_smul]
  linarith [hξ_eq, htaylor, hrem, hψy]

end TauCeti

end VerticalTaylor
