/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.MeasureTheory.Function.AEEqOfIntegralContinuous

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
everywhere (`MeasureTheory.Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero`).

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

omit [CompleteSpace E] in
/-- If all Fourier coefficients of an integrable `f` vanish, then the integral of `f` against
every continuous function on the circle vanishes. -/
private theorem Integrable.integral_smul_eq_zero_of_forall_fourierCoeff_eq_zero
    (hf : Integrable f haarAddCircle) (h : ∀ n, fourierCoeff f n = 0)
    (φ : C(AddCircle T, ℂ)) : ∫ t, φ t • f t ∂haarAddCircle = 0 := by
  have hint (φ : C(AddCircle T, ℂ)) : Integrable (fun t ↦ φ t • f t) haarAddCircle :=
    hf.bdd_smul ‖φ‖ φ.continuous.aestronglyMeasurable (ae_of_all _ φ.norm_coe_le_norm)
  -- Integration against `f`, as a continuous linear functional on `C(AddCircle T, ℂ)`.
  let L : C(AddCircle T, ℂ) →ₗ[ℂ] E :=
    { toFun := fun φ ↦ ∫ t, φ t • f t ∂haarAddCircle
      map_add' := fun φ ψ ↦ by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (hint φ) (hint ψ)
      map_smul' := fun c φ ↦ by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact MeasureTheory.integral_smul c _ }
  let Lc := L.mkContinuous (∫ t, ‖f t‖ ∂haarAddCircle) fun φ ↦ by
    refine (norm_integral_le_of_norm_le (hf.norm.const_mul ‖φ‖) (ae_of_all _ fun t ↦ ?_)).trans_eq
      (by rw [integral_const_mul, mul_comm])
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm t) (norm_nonneg _)
  have hLc (φ : C(AddCircle T, ℂ)) : Lc φ = ∫ t, φ t • f t ∂haarAddCircle := by
    simp [Lc, L]
  -- It vanishes on the Fourier monomials, hence on their dense span.
  have hspan : Submodule.span ℂ (range (fourier (T := T))) ≤ LinearMap.ker (Lc : _ →ₗ[ℂ] E) :=
    Submodule.span_le.2 <| range_subset_iff.2 fun n ↦ LinearMap.mem_ker.2 <| by
      simpa [hLc, fourierCoeff, -fourier_apply] using h (-n)
  have htop := Submodule.topologicalClosure_minimal _ hspan Lc.isClosed_ker
  rw [span_fourier_closure_eq_top, top_le_iff] at htop
  have hφ : φ ∈ LinearMap.ker (Lc : _ →ₗ[ℂ] E) := htop ▸ Submodule.mem_top
  rw [← hLc]
  exact LinearMap.mem_ker.1 hφ

/-- **Uniqueness of Fourier coefficients for integrable functions.** An integrable function on the
circle whose Fourier coefficients all vanish is zero almost everywhere. -/
theorem Integrable.ae_eq_zero_of_forall_fourierCoeff_eq_zero (hf : Integrable f haarAddCircle)
    (h : ∀ n, fourierCoeff f n = 0) : f =ᵐ[haarAddCircle] 0 :=
  hf.ae_eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ by
    simpa [Complex.coe_smul] using hf.integral_smul_eq_zero_of_forall_fourierCoeff_eq_zero h
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
    rw [← inner_conj_symm, ← HilbertBasis.repr_apply_apply, fourierBasis_repr,
      fourierCoeff_congr_ae hF, fourierCoeff, fourierCoeff, ← integral_conj]
    congr 1 with t
    simp only [smul_eq_mul, map_mul, Pi.star_apply, RCLike.star_def, RCLike.conj_conj, neg_neg,
      fourier_neg]
  have hbG (m : ℤ) : ⟪fourierBasis m, G⟫_ℂ = fourierCoeff g (m + n) := by
    rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_congr_ae hG,
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
