/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.MeasureTheory.Function.AEEqOfIntegralContinuous
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness of Fourier coefficients and Fourier coefficients of products on the circle

Mathlib's `fourierCoeff f n = ∫ t, e_{-n}(t) • f t` is defined for every function `f` on
`AddCircle T`, and Parseval's theorem shows that an `L²` function is determined by its Fourier
coefficients. This file proves the corresponding statements for integrable functions and for
products of two square-integrable functions, which in general are only integrable.

*Uniqueness.* An integrable function, with values in any complete normed complex space, whose
Fourier coefficients all vanish is zero almost everywhere. Integration against `f` is a continuous
linear functional on `C(AddCircle T, ℂ)` of norm at most `‖f‖₁`; it vanishes on the monomials by
hypothesis, hence on the uniformly dense span of trigonometric polynomials and on every continuous
function. An integrable function orthogonal to all bounded continuous functions vanishes almost
everywhere (`MeasureTheory.Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero`). Lifting a
function from a period interval to the circle gives the same statement for Mathlib's Fourier
coefficients `fourierCoeffOn` on an interval `[a, b]`.

*Products.* If `f` and `g` are square integrable, then `f * g` is integrable (Mathlib's
`MeasureTheory.MemLp.integrable_mul`) and its Fourier coefficients are the convolution of those of
`f` and `g`: `(f g)^(n) = ∑ₘ f̂(m) ĝ(n - m)`, the series converging
unconditionally. This is Parseval's
identity `⟪u, v⟫ = ∑ₘ conj(û(m)) v̂(m)` for `u = conj f` and `v = e_{-n} g`. Consequently, if the
Fourier coefficients of `f` and `g` vanish below `a` and `b` respectively, then those of `f * g`
vanish below `a + b`, and similarly above.

Together these compute products in the boundary Hardy theory: for instance, if `f` has only
negative and `g` only nonpositive Fourier modes, then all modes of `f * g` are negative, and a
product of square-integrable functions with no Fourier modes at all is zero almost everywhere.
This is the Fourier-analytic input to Coburn's theorem that a nonzero Toeplitz operator or its
adjoint is injective.

## Main results

* `MeasureTheory.Integrable.ae_eq_zero_of_forall_fourierCoeff_eq_zero`: an integrable function on
  the circle with vanishing Fourier coefficients is zero almost everywhere;
* `MeasureTheory.Integrable.ae_eq_of_forall_fourierCoeff_eq`: integrable functions with the same
  Fourier coefficients agree almost everywhere;
* `MeasureTheory.IntegrableOn.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero`: a function integrable
  on `(a, b]` with vanishing Fourier coefficients on `[a, b]` is zero almost everywhere there;
* `MeasureTheory.IntegrableOn.integral_re_inner_continuousMap_eq_zero_of_dense`: a function on
  `[0, T]` orthogonal to a dense set of continuous loops of period `T` is orthogonal to all of them;
* `MeasureTheory.IntegrableOn.ae_eq_zero_of_forall_integral_re_inner_continuousMap_eq_zero`: a
  function on `[0, T]` whose pairing with every continuous loop of period `T` vanishes is zero
  almost everywhere;
* `MeasureTheory.MemLp.hasSum_fourierCoeff_mul`: for square-integrable `f` and `g`,
  `(f g)^(n) = ∑ₘ f̂(m) ĝ(n - m)`;
* `MeasureTheory.MemLp.fourierCoeff_mul_eq_zero_of_lt_add` and
  `MeasureTheory.MemLp.fourierCoeff_mul_eq_zero_of_add_lt`: one-sided spectral support of a product.

## References

* Y. Katznelson, *An Introduction to Harmonic Analysis*, third edition, Cambridge University Press
  (2004), Chapter I, §§1–2 (Fourier coefficients of products, and uniqueness).
* E. Park, *Toeplitz operators*, for the use of these facts in Coburn's theorem.
-/

public section

open AddCircle Set
open scoped ComplexConjugate ENNReal InnerProductSpace

namespace MeasureTheory

variable {T : ℝ} [Fact (0 < T)]

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f g : AddCircle T → E}

/-- **Uniqueness of Fourier coefficients for integrable functions.** An integrable function on the
circle whose Fourier coefficients all vanish is zero almost everywhere. -/
theorem Integrable.ae_eq_zero_of_forall_fourierCoeff_eq_zero (hf : Integrable f haarAddCircle)
    (h : ∀ n, fourierCoeff f n = 0) : f =ᵐ[haarAddCircle] 0 :=
  hf.ae_eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ by
    simpa [Complex.coe_smul] using hf.integral_smul_eq_zero_of_span_closure_eq_top
      span_fourier_closure_eq_top (forall_mem_range.2 fun n ↦ by
        simpa [fourierCoeff, -fourier_apply] using h (-n))
      ⟨fun t ↦ (φ t : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩

/-- Integrable functions on the circle with the same Fourier coefficients agree almost
everywhere. -/
theorem Integrable.ae_eq_of_forall_fourierCoeff_eq (hf : Integrable f haarAddCircle)
    (hg : Integrable g haarAddCircle) (h : ∀ n, fourierCoeff f n = fourierCoeff g n) :
    f =ᵐ[haarAddCircle] g := by
  have hfg := (hf.sub hg).ae_eq_zero_of_forall_fourierCoeff_eq_zero fun n ↦ by
    have hn := h n
    simp only [fourierCoeff, Pi.sub_apply, smul_sub] at hn ⊢
    rw [integral_sub (hf.fourier_smul _) (hg.fourier_smul _), hn, sub_self]
  filter_upwards [hfg] with t ht
  simpa [sub_eq_zero] using ht

/-- **Uniqueness of Fourier coefficients on an interval.** A function integrable on `(a, b]` whose
Fourier coefficients on `[a, b]` all vanish is zero almost everywhere on `(a, b]`. -/
theorem IntegrableOn.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero {a b : ℝ} (hab : a < b)
    {f : ℝ → E} (hf : IntegrableOn f (Ioc a b)) (h : ∀ n : ℤ, fourierCoeffOn hab f n = 0) :
    f =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  have hIoc : Ioc a (a + (b - a)) = Ioc a b := by rw [add_sub_cancel]
  have hc : ENNReal.ofReal (b - a) ≠ 0 := by simpa using hab
  -- Transport `f` to the circle of length `b - a`. By definition, `fourierCoeffOn` is the
  -- Fourier coefficient of this lift.
  have hlift : (fun x : ℝ ↦ liftIoc (b - a) a f x) =ᵐ[volume.restrict (Ioc a b)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact liftIoc_coe_apply (hIoc ▸ hx)
  have hint : Integrable (liftIoc (b - a) a f) haarAddCircle := by
    rw [← integrable_smul_measure hc ENNReal.ofReal_ne_top, ← volume_eq_smul_haarAddCircle]
    exact ((measurePreserving_subtypeVal measurableSet_Ioc).comp
      (measurePreserving_equivIoc _)).integrable_comp_of_integrable (hIoc ▸ hf)
  have hzero := hint.ae_eq_zero_of_forall_fourierCoeff_eq_zero fun n ↦ by
    simpa only [fourierCoeffOn] using h n
  rw [Filter.EventuallyEq, ← Measure.ae_ennreal_smul_measure_eq hc,
    ← volume_eq_smul_haarAddCircle] at hzero
  exact hlift.symm.trans
    ((hIoc ▸ AddCircle.measurePreserving_mk (b - a) a).quasiMeasurePreserving.ae_eq_comp hzero)

end Uniqueness

section Product

/- The measure is written `AddCircle.haarAddCircle` below: in the `MemLp` namespace the short name
would resolve to the lemma `MeasureTheory.MemLp.haarAddCircle`. -/

variable {f g : AddCircle T → ℂ}

/-- **Fourier coefficients of a product.** If `f` and `g` are square integrable on the circle,
then the Fourier coefficients of `f * g` are the convolution of those of `f` and `g`:
`(f g)^(n) = ∑ₘ f̂(m) ĝ(n - m)`. -/
theorem MemLp.hasSum_fourierCoeff_mul (hf : MemLp f 2 AddCircle.haarAddCircle)
    (hg : MemLp g 2 AddCircle.haarAddCircle) (n : ℤ) :
    HasSum (fun m ↦ fourierCoeff f m * fourierCoeff g (n - m)) (fourierCoeff (f * g) n) := by
  -- Parseval's identity for `F = conj f` and `G = e_{-n} g`.
  set F : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) := hf.star.toLp (star f)
  set G : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) := fourierLp (T := T) ∞ (-n) • hg.toLp g
  have hF : ⇑F =ᵐ[AddCircle.haarAddCircle] star f := hf.star.coeFn_toLp
  have hG : ⇑G =ᵐ[AddCircle.haarAddCircle] fun t ↦ fourier (-n) t * g t := by
    filter_upwards [TauCeti.coeFn_fourierLp_smul (-n) (hg.toLp g), hg.coeFn_toLp] with t h₁ h₂
    rw [h₁, h₂]
  have hFG : ⟪F, G⟫_ℂ = fourierCoeff (f * g) n := by
    rw [L2.inner_def, fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [hF, hG] with t h₁ h₂
    simp only [h₁, h₂, RCLike.inner_apply, Pi.star_apply, RCLike.star_def, RCLike.conj_conj,
      smul_eq_mul, Pi.mul_apply]
    ring
  have hFb (m : ℤ) : ⟪F, fourierBasis m⟫_ℂ = fourierCoeff f (-m) := by
    rw [← inner_conj_symm, TauCeti.inner_fourierBasis_left,
      fourierCoeff_congr_ae hF, fourierCoeff, fourierCoeff, ← integral_conj]
    congr 1 with t
    simp only [smul_eq_mul, map_mul, Pi.star_apply, RCLike.star_def, RCLike.conj_conj, neg_neg,
      fourier_neg]
  have hbG (m : ℤ) : ⟪fourierBasis m, G⟫_ℂ = fourierCoeff g (m + n) := by
    rw [TauCeti.inner_fourierBasis_left, fourierCoeff_congr_ae hG,
      fourierCoeff, fourierCoeff]
    congr 1 with t
    rw [smul_eq_mul, smul_eq_mul, neg_add, fourier_add, mul_assoc]
  have hsum := fourierBasis.hasSum_inner_mul_inner F G
  simp only [hFb, hbG, hFG] at hsum
  rw [← (Equiv.neg ℤ).hasSum_iff]
  convert hsum using 2 with m
  simp [sub_neg_eq_add, add_comm]

/-- If the Fourier coefficients of the square-integrable functions `f` and `g` vanish below `a` and
`b` respectively, then those of `f * g` vanish below `a + b`. -/
theorem MemLp.fourierCoeff_mul_eq_zero_of_lt_add (hf : MemLp f 2 AddCircle.haarAddCircle)
    (hg : MemLp g 2 AddCircle.haarAddCircle) {a b n : ℤ} (hfa : ∀ m < a, fourierCoeff f m = 0)
    (hgb : ∀ m < b, fourierCoeff g m = 0) (hn : n < a + b) : fourierCoeff (f * g) n = 0 := by
  have hzero : (fun m ↦ fourierCoeff f m * fourierCoeff g (n - m)) = 0 := by
    ext m
    rcases lt_or_ge m a with hm | hm
    · rw [hfa m hm, zero_mul, Pi.zero_apply]
    · rw [hgb (n - m) (by omega), mul_zero, Pi.zero_apply]
  have hsum := hf.hasSum_fourierCoeff_mul hg n
  rw [hzero] at hsum
  exact hsum.unique hasSum_zero

/-- If the Fourier coefficients of the square-integrable functions `f` and `g` vanish above `a` and
`b` respectively, then those of `f * g` vanish above `a + b`. -/
theorem MemLp.fourierCoeff_mul_eq_zero_of_add_lt (hf : MemLp f 2 AddCircle.haarAddCircle)
    (hg : MemLp g 2 AddCircle.haarAddCircle) {a b n : ℤ} (hfa : ∀ m, a < m → fourierCoeff f m = 0)
    (hgb : ∀ m, b < m → fourierCoeff g m = 0) (hn : a + b < n) : fourierCoeff (f * g) n = 0 := by
  have hzero : (fun m ↦ fourierCoeff f m * fourierCoeff g (n - m)) = 0 := by
    ext m
    rcases lt_or_ge a m with hm | hm
    · rw [hfa m hm, zero_mul, Pi.zero_apply]
    · rw [hgb (n - m) (by omega), mul_zero, Pi.zero_apply]
  have hsum := hf.hasSum_fourierCoeff_mul hg n
  rw [hzero] at hsum
  exact hsum.unique hasSum_zero

end Product

end MeasureTheory

namespace MeasureTheory

section Orthogonal

open Set Complex

variable {T : ℝ} [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Orthogonality to a dense set of loops.** A function on `[0, T]`, integrable there, whose
pairing `∫_{[0, T]} Re ⟪ψ, f⟫` vanishes for every loop `ψ` in a dense set of continuous loops of
period `T`, has vanishing pairing with every continuous loop, since the pairing is continuous in
the loop for the sup norm. -/
theorem IntegrableOn.integral_re_inner_continuousMap_eq_zero_of_dense {f : ℝ → F}
    (hf : IntegrableOn f (Icc 0 T))
    {D : Set C(AddCircle T, F)} (hD : Dense D)
    (h : ∀ ψ ∈ D, ∫ t in Icc 0 T, (inner ℂ (ψ t) (f t)).re = 0) (ψ : C(AddCircle T, F)) :
    ∫ t in Icc 0 T, (inner ℂ (ψ t) (f t)).re = 0 := by
  have hle (χ : C(AddCircle T, F)) (t : ℝ) : ‖(inner ℂ (χ t) (f t)).re‖ ≤ ‖χ‖ * ‖f t‖ :=
    (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (χ.norm_coe_le_norm _) (norm_nonneg _)))
  have hint (χ : C(AddCircle T, F)) :
      IntegrableOn (fun t : ℝ ↦ (inner ℂ (χ t) (f t)).re) (Icc 0 T) :=
    (hf.norm.const_mul ‖χ‖).mono' ((χ.continuous.comp (AddCircle.continuous_mk' T)
      ).aestronglyMeasurable.inner (𝕜 := ℂ) hf.aestronglyMeasurable).re (ae_of_all _ (hle χ))
  -- The pairing is additive in the loop and bounded by `‖χ‖ ∫_{[0, T]} ‖f‖`.
  let Λ : C(AddCircle T, F) →+ ℝ :=
    AddMonoidHom.mk' (fun χ ↦ ∫ t in Icc 0 T, (inner ℂ (χ t) (f t)).re) fun χ χ' ↦ by
      simp only [ContinuousMap.add_apply, inner_add_left, add_re]
      exact integral_add (hint χ) (hint χ')
  have hΛ : Continuous Λ :=
    AddMonoidHomClass.continuous_of_bound Λ (∫ t in Icc 0 T, ‖f t‖) fun χ ↦ by
      rw [mul_comm, ← integral_const_mul]
      exact norm_integral_le_of_norm_le (hf.norm.const_mul _) (ae_of_all _ (hle χ))
  exact congrFun (hΛ.ext_on hD continuous_const h) ψ

/-- **A function orthogonal to all continuous loops vanishes.** A function on `[0, T]`, integrable
there, whose pairing `∫_{[0, T]} Re ⟪ψ, f⟫` with every continuous loop `ψ` of period `T` vanishes,
is zero almost everywhere on `[0, T]`: testing against the loops `g(t) v` with `g` supported in
`(0, T)` shows that `Re ⟪v, f⟫` vanishes almost everywhere for every vector `v`. -/
theorem IntegrableOn.ae_eq_zero_of_forall_integral_re_inner_continuousMap_eq_zero
    [SecondCountableTopology F] {f : ℝ → F}
    (hf : IntegrableOn f (Icc 0 T))
    (h : ∀ ψ : C(AddCircle T, F), ∫ t in Icc 0 T, (inner ℂ (ψ t) (f t)).re = 0) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), f t = 0 := by
  have hv (v : F) : ∀ᵐ t, t ∈ Ioo 0 T → (inner ℂ v (f t)).re = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (IntegrableOn.mono_set (t := Icc 0 T) (hf.const_inner (𝕜 := ℂ) v).re
        Ioo_subset_Icc_self).locallyIntegrableOn
      fun g hg _ hgs ↦ ?_
    have hg0 (t : ℝ) (ht : t ∉ Ioo 0 T) : g t = 0 :=
      image_eq_zero_of_notMem_tsupport fun h' ↦ ht (hgs h')
    -- The loop `g(t) v`, continuous since `g` vanishes at `0` and `T`.
    let ψ : C(AddCircle T, F) :=
      ⟨AddCircle.liftIco T 0 fun t ↦ g t • v, AddCircle.liftIco_continuous
        (by rw [hg0 0 (by simp), hg0 (0 + T) (by simp)])
        (hg.continuous.smul continuous_const).continuousOn⟩
    have hψ (t : ℝ) (ht : t ∈ Icc 0 T) : ψ t = g t • v := by
      simp only [ψ, ContinuousMap.coe_mk]
      rcases eq_or_lt_of_le ht.2 with htT | ht1
      · -- At the endpoint `t = T` the loop takes its value at `0`, where `g` vanishes.
        rw [htT, show ((T : ℝ) : AddCircle T) = ((0 : ℝ) : AddCircle T) by
          rw [AddCircle.coe_period, QuotientAddGroup.mk_zero], AddCircle.liftIco_coe_apply
          (by simp [hT.out]), hg0 0 (by simp), hg0 T (by simp)]
      · exact AddCircle.liftIco_coe_apply ⟨ht.1, by simpa using ht1⟩
    have h0 := h ψ
    rw [setIntegral_congr_fun measurableSet_Icc fun t ht ↦ by rw [hψ t ht]] at h0
    simp only [inner_smul_left_eq_smul, Complex.smul_re, smul_eq_mul] at h0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by
      rw [hg0 t fun h' ↦ ht (Ioo_subset_Icc_self h'), zero_mul]] at h0
    simpa [smul_eq_mul] using h0
  -- These are the real inner products `⟪v, f⟫_ℝ` for the underlying real inner product space.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  refine ae_eq_zero_of_forall_inner (𝕜 := ℝ) fun v ↦ ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 (hv v)] with t ht
  exact (real_inner_eq_re_inner ℂ v (f t)).trans ht

end Orthogonal

end MeasureTheory
