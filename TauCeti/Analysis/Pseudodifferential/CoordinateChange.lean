/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Classical
public import TauCeti.Analysis.Calculus.Hadamard
public import TauCeti.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Abs
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Fourier.Parametric

/-!
# Changes of coordinates for pseudodifferential operators

Let `κ` be a diffeomorphism of `ℝⁿ` and `a` a symbol of order `m` vanishing at positions outside
a compact set `K`. In the coordinates `x` with `z = κ x`, the operator `Op(a)` acting on functions
cut off by `ψ` becomes

`u ↦ Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ`.

This file shows that it is again a pseudodifferential operator `Op(b)`, for a symbol `b` of order
`m` whose full asymptotic expansion is given by the amplitude calculus, and whose leading term is
the pullback of `a` by the cotangent map of `κ`:

`b(x, ξ) = ψ(x) a(κ x, (Dκ(x)*)⁻¹ ξ)` modulo symbols of order `m - 1`.

If `a` is a classical symbol, then so is `b`, and its principal symbol is
`ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`.

The hypothesis is that the averaged derivative `Φ(x, y) = ∫₀¹ Dκ(y + t (x - y)) dt` of `κ` along
the segment from `y` to `x` (`hadamardFactor κ y x`) is invertible for `κ x ∈ K` and `y` in the
support of `ψ`, where `Dκ` is invertible. It holds whenever these sets are small enough, since
`Φ(x, x) = Dκ(x)` (`ContDiff.exists_mem_nhds_isUnit_hadamardFactor`); this is how operators on
manifolds are localized to charts.

## Kuranishi's trick

Since `κ x - κ y = Φ(x, y) (x - y)`, the phase of the transported operator is
`⟪κ x - κ y, η⟫ = ⟪x - y, Φ* η⟫`. After the substitution `η = M ξ` with `M = (Φ⁻¹)*`, it is
the amplitude quantization of

`c(x, y, ξ) = ψ(y) |det Dκ(y)| |det M(x, y)| a(κ x, M(x, y) ξ)`,

an amplitude of order `m` with proper input support (`TauCeti.Symbol.compAmplitude`). Its left
symbol `b` (`TauCeti.Amplitude.leftSymbol`) satisfies `b ∼ ∑ₖ leftTerm c k`, and the leading term
`c(x, x, ξ)` is the pullback of `a` described above, since `M(x, x) = (Dκ(x)*)⁻¹`.

The oscillatory integrals do not converge absolutely, so the substitution is carried out for the
regularized symbols `ρ(η / t) a(z, η)` with a compactly supported `ρ` equal to `1` at `0`, for
which all integrals converge absolutely, and `t → ∞`. On the amplitude side the regularization
becomes `ρ(M(x, y) ξ / t)`, whose position derivatives are bounded uniformly in `t`.

## Main results

* `TauCeti.exists_forall_quantizeSchwartzValue_comp_eq_compAmplitude`: Kuranishi's trick, with the
  frequency map `M` and the weight `g` chosen once for all the symbols vanishing outside `K`.
* `TauCeti.Symbol.exists_amplitude_quantizeSchwartzValue_comp_eq`: the transported operator is the
  quantization of the amplitude `g(x, y) • a(κ x, M(x, y) ξ)` (`TauCeti.Symbol.compAmplitude`),
  for data `M` and `g` with `g(x, x) = ψ(x)` wherever `κ x ∈ K`, and `M(x, x) = (Dκ(x)*)⁻¹`
  wherever also `x ∈ tsupport ψ`.
* `TauCeti.Symbol.exists_quantizeSchwartzValue_comp_eq`: the transported operator is `Op(b)` for a
  symbol `b` of order `m` with `b(x, ξ) - ψ(x) a(κ x, (Dκ(x)*)⁻¹ ξ)` of order `m - 1`.
* `TauCeti.ClassicalSymbol.exists_quantizeSchwartzValue_comp_eq`: if `a` is classical, so is `b`,
  and its principal symbol is `ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`: the principal symbol transforms by
  the cotangent map of `κ`. The homogeneous terms of `b` come from those of `a` through
  `TauCeti.ClassicalAmplitude.leftSymbol`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.17 and its proof.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Module Filter Set
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-! ### The change of variables in absolutely convergent integrals -/

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace W] in
private theorem fourierChar_smul_fourierChar_smul (a b : ℝ) (w : W) :
    𝐞 a • 𝐞 b • w = 𝐞 (a + b) • w := by
  rw [smul_smul, ← AddChar.map_add_eq_mul]

/-- **Transport of an absolutely convergent quantization.** Let `κ` be a `C¹` homeomorphism of `E`
and `A` a continuous compactly supported coefficient of the frequency. If `v ∘ κ = ψ • u` and
`N(y)` is invertible with `⟪N(y) ζ, Φ(y) h⟫ = ⟪ζ, h⟫` for `y` in the support of `ψ`, where
`Φ(y) = hadamardFactor κ y x` satisfies `κ x - κ y = Φ(y) (x - y)`, then the absolutely
convergent integral `∫ e(⟪ζ, κ x⟫) A(ζ) (𝓕 v ζ) dζ` is the corresponding integral for the
amplitude `(y, ζ) ↦ ψ(y) |det Dκ(y)| |det N(y)| A(N(y) ζ)` at `x`. -/
private theorem integral_fourierChar_smul_apply_fourier_comp_eq {κ : E ≃ₜ E}
    (hκ : ContDiff ℝ 1 κ) (x : E) {A : E → V →L[ℂ] W} (hA : Continuous A)
    (hAc : HasCompactSupport A) {ψ : E → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {N : E → E →L[ℝ] E} (hN : Continuous N) (hNu : ∀ y ∈ tsupport ψ, IsUnit (N y))
    (hNΦ : ∀ y ∈ tsupport ψ, ∀ ζ h, ⟪N y ζ, hadamardFactor κ y x h⟫ = ⟪ζ, h⟫)
    {u v : 𝓢(E, V)} (huv : ∀ y, v (κ y) = ψ y • u y) :
    ∫ ζ, 𝐞 ⟪ζ, κ x⟫ • A ζ (𝓕 v ζ) =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦
        ((ψ y * |(fderiv ℝ κ y).det| * |(N y).det|) • A (N y ζ)) (u y)) ζ := by
  set s : E → ℝ := fun y ↦ ψ y * |(fderiv ℝ κ y).det| * |(N y).det|
  have hs : Continuous s := (hψ.mul ((ContinuousLinearMap.continuous_det.comp
    (hκ.continuous_fderiv one_ne_zero)).abs)).mul (ContinuousLinearMap.continuous_det.comp hN).abs
  -- The integrand of the left side on `E × E`, in the frequency `ζ` and the position `y'`.
  set f : E → E → W := fun ζ y' ↦ 𝐞 ⟪ζ, κ x - y'⟫ • A ζ (v y')
  have hf_cont : Continuous (Function.uncurry f) :=
    (Real.continuous_fourierChar.comp (continuous_fst.inner
      (continuous_const.sub continuous_snd))).smul
      (isBoundedBilinearMap_apply.continuous.comp ((hA.comp continuous_fst).prodMk
        (v.continuous.comp continuous_snd)))
  have hf_int : Integrable (Function.uncurry f) (volume.prod volume) := by
    refine ((hA.norm.integrable_of_hasCompactSupport hAc.norm).mul_prod
      v.integrable.norm).mono' hf_cont.aestronglyMeasurable (ae_of_all _ fun q ↦ ?_)
    simp only [Function.uncurry, f, Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    exact (A q.1).le_opNorm _
  -- The integrand of the right side, in the position `y` and the frequency `ζ`.
  set k : E → E → W := fun y ζ ↦ 𝐞 ⟪ζ, x - y⟫ • (s y • A (N y ζ)) (u y)
  have hk_cont : Continuous (Function.uncurry k) :=
    (Real.continuous_fourierChar.comp (continuous_snd.inner
      (continuous_const.sub continuous_fst))).smul
      (isBoundedBilinearMap_apply.continuous.comp (((hs.comp continuous_fst).smul
        (hA.comp (isBoundedBilinearMap_apply.continuous.comp ((hN.comp continuous_fst).prodMk
          continuous_snd)))).prodMk (u.continuous.comp continuous_fst)))
  have hk_supp : HasCompactSupport (Function.uncurry k) := by
    set T : Set E := (fun q : E × E ↦ Ring.inverse (N q.1) q.2) '' (tsupport ψ ×ˢ tsupport A)
    have hT : IsCompact T := (hψc.prod hAc).image_of_continuousOn fun q hq ↦
      (((hN.comp continuous_fst).continuousAt.ringInverse (hNu q.1 hq.1)).clm_apply
        continuous_snd.continuousAt).continuousWithinAt
    refine HasCompactSupport.intro (hψc.prod hT) fun q hq ↦ ?_
    by_contra hne
    have hψq : ψ q.1 ≠ 0 := fun h0 ↦ hne (by simp [Function.uncurry, k, s, h0])
    have hAq : A (N q.1 q.2) ≠ 0 := fun h0 ↦ hne (by simp [Function.uncurry, k, h0])
    have hy : q.1 ∈ tsupport ψ := subset_tsupport _ hψq
    exact hq ⟨hy, ⟨(q.1, N q.1 q.2), ⟨hy, subset_tsupport _ hAq⟩,
      ContinuousLinearMap.ringInverse_apply_apply (hNu _ hy) _⟩⟩
  have hk_int : Integrable (Function.uncurry k) (volume.prod volume) :=
    hk_cont.integrable_of_hasCompactSupport hk_supp
  -- The left side is the iterated integral of `f`.
  have h1 : ∫ ζ, 𝐞 ⟪ζ, κ x⟫ • A ζ (𝓕 v ζ) = ∫ ζ, ∫ y', f ζ y' := by
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    dsimp only
    rw [← SchwartzMap.fourier_postcompCLM_apply, SchwartzMap.fourier_coe, Real.fourier_eq,
      Circle.smul_def, ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun y' ↦ ?_)
    simp only [f, SchwartzMap.postcompCLM_apply, ← Circle.smul_def,
      fourierChar_smul_fourierChar_smul, real_inner_comm, sub_eq_add_neg, inner_add_right,
      inner_neg_right]
  -- Change of variables `y' = κ y`, then `ζ = N(y) ζ'` for each `y`.
  have h3 : ∫ y', ∫ ζ, f ζ y' = ∫ y, |(fderiv ℝ κ y).det| • ∫ ζ, f ζ (κ y) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun y _ ↦ ((hκ.differentiable one_ne_zero) y).hasFDerivAt.hasFDerivWithinAt)
      κ.injective.injOn (fun y' ↦ ∫ ζ, f ζ y')
    rw [image_univ_of_surjective κ.surjective] at h
    simpa only [Measure.restrict_univ] using h
  have h4 : ∀ y, |(fderiv ℝ κ y).det| • ∫ ζ, f ζ (κ y) = ∫ ζ, k y ζ := by
    intro y
    by_cases hy : ψ y = 0
    · simp [f, k, s, huv, hy]
    have hy' : y ∈ tsupport ψ := subset_tsupport _ hy
    rw [Measure.integral_eq_abs_det_smul_integral_comp volume (hNu y hy') (fun ζ ↦ f ζ (κ y)),
      smul_smul, ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    have hΦ := ContDiff.sub_eq_hadamardFactor_apply κ hκ y x
    simp only [f, k, s, huv, hΦ, hNΦ y hy', ContinuousLinearMap.map_smul_of_tower,
      smul_apply, smul_comm _ (𝐞 _), smul_smul]
    ring_nf
  -- The right side is the iterated integral of `k`.
  have h6 : ∀ ζ, ∫ y, k y ζ = 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ (s y • A (N y ζ)) (u y)) ζ := by
    intro ζ
    rw [Real.fourier_eq, Circle.smul_def, ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only [k, ← Circle.smul_def, fourierChar_smul_fourierChar_smul,
      real_inner_comm, sub_eq_add_neg, inner_add_right, inner_neg_right]
  rw [h1, integral_integral_swap hf_int, h3, integral_congr_ae (ae_of_all _ h4),
    integral_integral_swap hk_int]
  exact integral_congr_ae (ae_of_all _ h6)

end ChangeOfVariables

/-! ### Removing the regularization on the amplitude side -/

section Limit

variable {m : ℝ}

omit [CompleteSpace V] [CompleteSpace W] in
/-- The input-position slices `y ↦ c(x, y, ξ) (u y)` of an amplitude, applied to a Schwartz
function, are smooth. -/
private theorem contDiff_coefficient_slice_apply (c : Amplitude n V W m)
    (x ξ : CoordinateSpace n) (u : 𝓢(CoordinateSpace n, V)) :
    ContDiff ℝ ∞ fun y ↦ c.coefficient (x, y, ξ) (u y) := by
  have h := ((ContinuousLinearMap.id ℂ (V →L[ℂ] W)).bilinearRestrictScalars
    ℝ).isBoundedBilinearMap.contDiff.comp
      ((c.contDiff_coefficient.comp (by fun_prop : ContDiff ℝ ∞
        fun y : CoordinateSpace n ↦ (x, y, ξ))).prodMk (u.smooth ⊤))
  simpa only [Function.comp_def, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.id_apply] using h

omit [CompleteSpace V] [CompleteSpace W] in
/-- The derivatives of `y ↦ r(y) • c(x, y, ξ) (u y)` are bounded by `B ⟨ξ⟩ ^ m` on the input
support of `c`, if the derivatives of `r` are bounded there. -/
private theorem exists_norm_iteratedFDeriv_smul_apply_le {c : Amplitude n V W m}
    (hc : c.HasProperInputSupport) (x : CoordinateSpace n) (u : 𝓢(CoordinateSpace n, V))
    {L : Set (CoordinateSpace n)} {ι : Type*} {r : ι → CoordinateSpace n → ℝ}
    (hr : ∀ i, ContDiff ℝ ∞ (r i)) (k : ℕ) {R : ℕ → ℝ}
    (hR : ∀ j ≤ k, ∀ i, ∀ y ∈ L, ‖iteratedFDeriv ℝ j (r i) y‖ ≤ R j) :
    ∃ B, ∀ i, ∀ y ∈ L, ∀ ξ,
      ‖iteratedFDeriv ℝ k (fun y ↦ r i y • c.coefficient (x, y, ξ) (u y)) y‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  choose D hD0 hD using fun l : ℕ ↦ hc.exists_norm_iteratedFDeriv_slice_le
    (isCompact_singleton (x := x)) l
  set P : (V →L[ℂ] W) →L[ℝ] V →L[ℝ] W :=
    (ContinuousLinearMap.id ℂ (V →L[ℂ] W)).bilinearRestrictScalars ℝ
  set S : ℕ → ℝ := fun j ↦ SchwartzMap.seminorm ℝ 0 j u
  set G : ℕ → ℝ := fun j ↦ ‖P‖ * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * D l * S (j - l)
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * R i * G (k - i),
    fun i₀ y hy ξ ↦ ?_⟩
  have hcs : ContDiff ℝ ∞ fun y ↦ c.coefficient (x, y, ξ) :=
    c.contDiff_coefficient.comp (by fun_prop)
  have hP : (fun y ↦ c.coefficient (x, y, ξ) (u y)) =
      fun y ↦ P (c.coefficient (x, y, ξ)) (u y) := funext fun y ↦ by
    simp only [P, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      ContinuousLinearMap.id_apply]
  have hg := contDiff_coefficient_slice_apply c x ξ u
  -- The derivatives of `y ↦ c(x, y, ξ) (u y)`.
  have hgj : ∀ j, ‖iteratedFDeriv ℝ j (fun y ↦ c.coefficient (x, y, ξ) (u y)) y‖ ≤
      G j * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
    intro j
    have h := P.norm_iteratedFDeriv_le_of_bilinear hcs u.smooth' y (n := j) (by simp)
    rw [hP]
    refine h.trans ?_
    have hterm : ∀ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l (fun y ↦ c.coefficient (x, y, ξ)) y‖ *
          ‖iteratedFDeriv ℝ (j - l) u y‖ ≤
        (j.choose l : ℝ) * D l * S (j - l) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
      intro l _
      have h1 := hD l x rfl y ξ
      have h2 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ u (j - l) y
      have h3 : 0 ≤ D l * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := mul_nonneg (hD0 l) (by positivity)
      calc (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y ↦ c.coefficient (x, y, ξ)) y‖ *
            ‖iteratedFDeriv ℝ (j - l) u y‖
          ≤ (j.choose l : ℝ) * (D l * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) * S (j - l) := by gcongr
        _ = _ := by ring
    calc ‖P‖ * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
          ‖iteratedFDeriv ℝ l (fun y ↦ c.coefficient (x, y, ξ)) y‖ *
            ‖iteratedFDeriv ℝ (j - l) u y‖
        ≤ ‖P‖ * ∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) * D l * S (j - l) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) P.opNorm_nonneg
      _ = G j * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by simp only [G, Finset.sum_mul, mul_assoc]
  refine (norm_iteratedFDeriv_smul_le (hr i₀) hg y (n := k) (by simp)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 := hR i hi' i₀ y hy
  have h2 := hgj (k - i)
  have hR0 : 0 ≤ R i := (norm_nonneg _).trans h1
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (r i₀) y‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun y ↦ c.coefficient (x, y, ξ) (u y)) y‖
      ≤ (k.choose i : ℝ) * R i * (G (k - i) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by gcongr
    _ = (k.choose i : ℝ) * R i * G (k - i) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Removing a uniformly bounded regularization.** Let `c` be an amplitude vanishing for input
positions outside a compact set `L`, and let `r t (y, ξ)` be smooth in `y`, with derivatives
bounded on `L` uniformly in `t ≥ 1` and `ξ`, and tending to `1` as `t → ∞`. Then the
quantization of `r t • c` at `x` tends to that of `c`. -/
private theorem tendsto_quantizeAmplitudeValue_smul {c : Amplitude n V W m}
    (hc : c.HasProperInputSupport) (x : CoordinateSpace n) (u : 𝓢(CoordinateSpace n, V))
    {L : Set (CoordinateSpace n)} (hL : IsCompact L)
    (hLc : ∀ y ∉ L, ∀ ξ, c.coefficient (x, y, ξ) = 0)
    {r : ℝ → CoordinateSpace n → CoordinateSpace n → ℝ}
    (hr : ∀ t ξ, ContDiff ℝ ∞ fun y ↦ r t y ξ)
    (hrc : ∀ t, Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ r t q.1 q.2)
    (hrb : ∀ k, ∃ R, ∀ t, 1 ≤ t → ∀ y ∈ L, ∀ ξ,
      ‖iteratedFDeriv ℝ k (fun y ↦ r t y ξ) y‖ ≤ R)
    (hr1 : ∀ y ξ, Tendsto (fun t ↦ r t y ξ) atTop (𝓝 1)) :
    Tendsto (fun t ↦ quantizeAmplitudeValue (fun p ↦ r t p.2.1 p.2.2 • c.coefficient p) u x)
      atTop (𝓝 (quantizeAmplitudeValue c.coefficient u x)) := by
  choose R hR using hrb
  set N : ℕ := ⌈|m|⌉₊ + n + 1
  -- The family of cutoffs, indexed by `t ≥ 1` and the frequency.
  have hρ : ∀ i : {t : ℝ // 1 ≤ t} × CoordinateSpace n, ContDiff ℝ ∞ (fun y ↦ r i.1 y i.2) :=
    fun i ↦ hr i.1 i.2
  have hρR : ∀ k, ∀ j ≤ k, ∀ i : {t : ℝ // 1 ≤ t} × CoordinateSpace n, ∀ y ∈ L,
      ‖iteratedFDeriv ℝ j (fun y ↦ r i.1 y i.2) y‖ ≤ R j :=
    fun _ j _ i y hy ↦ hR j i.1 i.1.property y hy i.2
  choose B hB using fun p ↦ exists_norm_iteratedFDeriv_smul_apply_le hc x u hρ p (hρR p)
  set B' := ∑ p ∈ Finset.range (N + 1), max (B p) 0
  have hB' : 0 ≤ B' := Finset.sum_nonneg fun p _ ↦ le_max_right _ _
  set C := 2 ^ N * B' * volume.real L * (2 * π) ^ |m|
  -- The input slices at the frequency `ξ = 2π ζ`, and their Fourier transforms.
  obtain ⟨g, hg⟩ : ∃ g : ℝ → CoordinateSpace n → CoordinateSpace n → W,
      g = fun t ζ y ↦ r t y ((2 * π) • ζ) • c.coefficient (x, y, (2 * π) • ζ) (u y) := ⟨_, rfl⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : CoordinateSpace n → CoordinateSpace n → W,
      g₀ = fun ζ y ↦ c.coefficient (x, y, (2 * π) • ζ) (u y) := ⟨_, rfl⟩
  have hgL : ∀ t ζ, ∀ y ∉ L, g t ζ y = 0 := fun t ζ y hy ↦ by simp [hg, hLc y hy]
  have hg₀L : ∀ ζ, ∀ y ∉ L, g₀ ζ y = 0 := fun ζ y hy ↦ by simp [hg₀, hLc y hy]
  have hgT : ∀ t ζ, tsupport (g t ζ) ⊆ L := fun t ζ ↦
    closure_minimal (Function.support_subset_iff'.2 (hgL t ζ)) hL.isClosed
  have hgs : ∀ t ζ, ContDiff ℝ ∞ (g t ζ) := fun t ζ ↦ by
    rw [hg]
    exact (hr t _).smul (contDiff_coefficient_slice_apply c x _ u)
  -- The derivatives of the slices up to order `N` are bounded by `B' ⟨2π ζ⟩ ^ m`.
  have hgB : ∀ t, 1 ≤ t → ∀ ζ, ∀ p ≤ N, ∀ y, ‖iteratedFDeriv ℝ p (g t ζ) y‖ ≤
      B' * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) := by
    intro t ht ζ p hp y
    by_cases hy : y ∈ L
    · have hb := hB p (⟨t, ht⟩, (2 * π) • ζ) y hy ((2 * π) • ζ)
      simp only at hb
      rw [hg]
      refine hb.trans (mul_le_mul_of_nonneg_right ((le_max_left _ 0).trans ?_) (by positivity))
      exact Finset.single_le_sum (f := fun p ↦ max (B p) 0) (fun _ _ ↦ le_max_right _ _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hp))
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦
        hy (hgT t ζ (tsupport_iteratedFDeriv_subset p h)), norm_zero]
      exact mul_nonneg hB' (by positivity)
  have hN : (finrank ℝ (CoordinateSpace n) : ℝ) < (N : ℝ) - |m| := by
    simp only [finrank_euclideanSpace, Fintype.card_fin, N]
    push_cast
    linarith [Nat.le_ceil |m|]
  -- The integrands converge pointwise.
  have hg₀c : ∀ ζ, Continuous (g₀ ζ) := by
    intro ζ
    have hcs : Continuous fun y ↦ c.coefficient (x, y, (2 * π) • ζ) :=
      c.contDiff_coefficient.continuous.comp (by fun_prop)
    rw [hg₀]
    exact hcs.clm_apply u.continuous
  have hlim : ∀ ζ, Tendsto (fun t ↦ 𝐞 ⟪ζ, x⟫ • 𝓕 (g t ζ) ζ) atTop
      (𝓝 (𝐞 ⟪ζ, x⟫ • 𝓕 (g₀ ζ) ζ)) := by
    intro ζ
    refine tendsto_const_nhds.smul ?_
    simp only [Real.fourier_eq]
    have hg₀i : Integrable (g₀ ζ) :=
      (hg₀c ζ).integrable_of_hasCompactSupport (HasCompactSupport.intro hL (hg₀L ζ))
    refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ R 0 * ‖g₀ ζ y‖) ?_ ?_
      (hg₀i.norm.const_mul _) ?_
    · exact .of_forall fun t ↦ ((Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const).neg).smul
          ((hgs t ζ).continuous)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with t ht
      refine .of_forall fun y ↦ ?_
      rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
      by_cases hy : y ∈ L
      · have h0 := hR 0 t ht y hy ((2 * π) • ζ)
        rw [norm_iteratedFDeriv_zero] at h0
        rw [hg, hg₀]
        simp only [norm_smul]
        exact mul_le_mul_of_nonneg_right h0 (norm_nonneg _)
      · simp [hgL t ζ y hy, hg₀L ζ y hy]
    · refine .of_forall fun y ↦ ?_
      have := (hr1 y ((2 * π) • ζ)).smul_const (c.coefficient (x, y, (2 * π) • ζ) (u y))
      rw [one_smul] at this
      rw [hg, hg₀]
      exact tendsto_const_nhds.smul this
  have key : ∀ t, quantizeAmplitudeValue (fun p ↦ r t p.2.1 p.2.2 • c.coefficient p) u x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (g t ζ) ζ := fun t ↦ by
    rw [quantizeAmplitudeValue_def, hg]
    simp only [smul_apply]
  have key₀ : quantizeAmplitudeValue c.coefficient u x = ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (g₀ ζ) ζ := by
    rw [quantizeAmplitudeValue_def, hg₀]
  simp only [key, key₀]
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
    ((integrable_rpow_neg_one_add_norm_sq hN).const_mul C) (.of_forall hlim)
  · refine .of_forall fun t ↦ ?_
    have hgc : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ g t q.2 q.1 := by
      have h1 : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
          r t q.1 ((2 * π) • q.2) :=
        (hrc t).comp (continuous_fst.prodMk (continuous_snd.const_smul (2 * π)))
      have h2 : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
          c.coefficient (x, q.1, (2 * π) • q.2) :=
        c.contDiff_coefficient.continuous.comp
          (continuous_const.prodMk (continuous_fst.prodMk (continuous_snd.const_smul (2 * π))))
      rw [hg]
      exact h1.smul (h2.clm_apply (u.continuous.comp continuous_fst))
    -- The Fourier transforms of the slices are the diagonal of a jointly continuous integral.
    have hcont : Continuous fun ζ ↦ 𝓕 (g t ζ) ζ := by
      simp only [Real.fourier_eq, Circle.smul_def]
      exact (continuous_integral_fourierChar_smul (K := L) (g := fun q ↦ g t q.2 q.1) hgc hL
        fun y hy ζ ↦ hgL t ζ y hy).comp (continuous_id.prodMk continuous_id)
    exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      hcont).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with t ht
    refine .of_forall fun ζ ↦ ?_
    rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    exact norm_fourier_le_of_tsupport_subset ((hgs t ζ).of_le (by exact_mod_cast le_top))
      hL.measure_lt_top.ne (hgT t ζ) ζ (hgB t ht ζ)

end Limit

/-! ### The symbol side and the regularizing cutoffs -/

section Main

variable {m : ℝ}

/-- The regularizing cutoffs `ρ(t⁻¹ w)` tend to `ρ 0 = 1` as `t → ∞`. -/
private theorem tendsto_cutoff_inv_smul {ρ : CoordinateSpace n → ℝ} (hρ : Continuous ρ)
    (hρ0 : ρ 0 = 1) (w : CoordinateSpace n) :
    Tendsto (fun t : ℝ ↦ ρ (t⁻¹ • w)) atTop (𝓝 1) := by
  rw [← hρ0]
  refine hρ.continuousAt.tendsto.comp ?_
  simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const w

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Removing the regularization on the symbol side.** For a compactly supported continuous
`ρ` with `ρ 0 = 1`, the quantizations of the regularized coefficients `ρ(ξ / t) a(z, ξ)` tend to
the quantization of `a` as `t → ∞`. -/
private theorem tendsto_integral_cutoff_smul_quantizeSchwartzValue' (a : Symbol n V W m)
    (z : CoordinateSpace n) (v : 𝓢(CoordinateSpace n, V)) {ρ : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ρ 0 = 1) :
    Tendsto (fun t : ℝ ↦ ∫ ζ, 𝐞 ⟪ζ, z⟫ •
        (ρ (t⁻¹ • (2 * π) • ζ) • a.coefficient (z, (2 * π) • ζ)) (𝓕 v ζ))
      atTop (𝓝 (quantizeSchwartzValue a.coefficient v z)) := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice z
  obtain ⟨Rρ, hRρ⟩ := hρ.bounded_above_of_compact_support hρc
  have hint := integrable_quantizeSchwartzValue_integrand
    (a.continuous_coefficient_slice z).aestronglyMeasurable hC (𝓕 v)
  rw [quantizeSchwartzValue_def]
  refine tendsto_integral_filter_of_dominated_convergence (fun ζ ↦ Rρ *
    ‖𝐞 ⟪ζ, z⟫ • a.coefficient (z, (2 * π) • ζ) (𝓕 v ζ)‖) ?_ ?_ (hint.norm.const_mul _) ?_
  · refine .of_forall fun t ↦ Continuous.aestronglyMeasurable ?_
    exact (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      (((hρ.comp ((continuous_const_smul _).comp (continuous_const_smul _))).smul
        ((a.continuous_coefficient_slice z).comp (continuous_const_smul _))).clm_apply
        (𝓕 v).continuous)
  · refine .of_forall fun t ↦ .of_forall fun ζ ↦ ?_
    simp only [Circle.smul_def, norm_smul, smul_apply, Circle.norm_coe, one_mul]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm ▸ (hRρ _)) (norm_nonneg _)
  · refine .of_forall fun ζ ↦ ?_
    have h2 := (tendsto_cutoff_inv_smul hρ hρ0 ((2 * π) • ζ)).smul_const
      (a.coefficient (z, (2 * π) • ζ))
    rw [one_smul] at h2
    exact tendsto_const_nhds.smul
      (((ContinuousLinearMap.apply ℂ W (𝓕 v ζ)).continuous.tendsto _).comp h2)

/-- A smooth family of operators on `ℝⁿ × ℝⁿ` agreeing with the inverse adjoint `(Φ⁻¹)*` of a
smooth family `Φ` on a compact set where `Φ` is invertible. -/
private theorem exists_contDiff_eqOn_adjoint_ringInverse
    {Φ : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
    (hΦ : ContDiff ℝ ∞ Φ) {S : Set (CoordinateSpace n × CoordinateSpace n)} (hS : IsCompact S)
    (hSΦ : ∀ w ∈ S, IsUnit (Φ w)) :
    ∃ M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n,
      ContDiff ℝ ∞ M ∧ ∀ w ∈ S, M w = ContinuousLinearMap.adjoint (Ring.inverse (Φ w)) := by
  have hO : IsOpen {w | IsUnit (Φ w)} := Units.isOpen.preimage hΦ.continuous
  obtain ⟨χ, hχ, -, hχ1, -, hχO⟩ := hS.exists_contDiff_cutoff hO hSΦ
  have hon : ContDiffOn ℝ ∞ (fun w ↦ ContinuousLinearMap.adjoint (Ring.inverse (Φ w)))
      {w | IsUnit (Φ w)} := by
    intro w hw
    have := (ContinuousLinearMap.adjointRealCLM (𝕜 := ℝ) (V := CoordinateSpace n)
      (W := CoordinateSpace n)).contDiff.contDiffAt.comp w (hΦ.contDiffAt.inverse hw)
    simpa only [Function.comp_def, ContinuousLinearMap.adjointRealCLM_apply] using
      this.contDiffWithinAt
  refine ⟨fun w ↦ χ w • ContinuousLinearMap.adjoint (Ring.inverse (Φ w)),
    hon.contDiff_smul_of_tsupport_subset hO hχ.contDiffOn hχO, fun w hw ↦ ?_⟩
  have h1 : χ w = 1 := interior_subset (hχ1 hw)
  simp [h1]

/-- **Uniform bounds for the regularizing cutoffs.** If `ρ` vanishes outside the unit ball and
`M(x, y)` is invertible for `y` in a compact set `L`, the position derivatives of
`y ↦ ρ(t⁻¹ M(x, y) ξ)` are bounded on `L` uniformly in `t` and `ξ`. -/
private theorem exists_norm_iteratedFDeriv_cutoff_le
    {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
    (hM : ContDiff ℝ ∞ M) {ρ : CoordinateSpace n → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρs : ∀ η, 1 ≤ ‖η‖ → ρ η = 0) (x : CoordinateSpace n) {L : Set (CoordinateSpace n)}
    (hL : IsCompact L) (hLM : ∀ y ∈ L, IsUnit (M (x, y))) (k : ℕ) :
    ∃ R, ∀ t : ℝ, ∀ y ∈ L, ∀ ξ,
      ‖iteratedFDeriv ℝ k (fun y ↦ ρ (t⁻¹ • M (x, y) ξ)) y‖ ≤ R := by
  -- The cutoffs are slices `y ↦ h((x, ζ), y)` of `h((x, ζ), y) = ρ(M(x, y) ζ)`.
  set h : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n → ℝ :=
    fun q ↦ ρ (M (q.1.1, q.2) q.1.2)
  have hh : ContDiff ℝ ∞ h := hρ.comp ((hM.comp (by fun_prop)).clm_apply (by fun_prop))
  have hMx : Continuous fun y ↦ M (x, y) := hM.continuous.comp (by fun_prop)
  set Q := (fun q : CoordinateSpace n × CoordinateSpace n ↦
    ((x, Ring.inverse (M (x, q.1)) q.2), q.1)) '' (L ×ˢ Metric.closedBall 0 1)
  have hQ : IsCompact Q := (hL.prod (isCompact_closedBall 0 1)).image_of_continuousOn
    fun q hq ↦ ((continuousAt_const.prodMk
      (((hMx.comp continuous_fst).continuousAt.ringInverse (hLM q.1 hq.1)).clm_apply
        continuous_snd.continuousAt)).prodMk continuous_fst.continuousAt).continuousWithinAt
  obtain ⟨R, hR⟩ := hQ.exists_bound_of_continuousOn
    (hh.continuous_iteratedFDeriv (m := k) (by simp)).continuousOn
  refine ⟨max R 0, fun t y hy ξ ↦ ?_⟩
  set ζ := t⁻¹ • ξ
  have e : (fun y ↦ ρ (t⁻¹ • M (x, y) ξ)) = fun y ↦ h ((x, ζ), y) := by
    funext y
    simp [h, ζ, map_smul]
  rw [e]
  by_cases hζ : ‖M (x, y) ζ‖ ≤ 1
  · refine (ContDiffAt.norm_iteratedFDeriv_prod_right_le (p := (x, ζ)) (x := y) hh.contDiffAt k
      (by simp)).trans ((hR _ ?_).trans (le_max_left _ _))
    exact ⟨(y, M (x, y) ζ), ⟨hy, by simpa using hζ⟩,
      by simp [ContinuousLinearMap.ringInverse_apply_apply (hLM y hy)]⟩
  · -- Near `y` the argument of `ρ` stays outside the unit ball, so the slice vanishes there.
    have hev : (fun y ↦ h ((x, ζ), y)) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      have hopen : IsOpen {y' | 1 < ‖M (x, y') ζ‖} :=
        isOpen_lt continuous_const ((hMx.clm_apply continuous_const).norm)
      filter_upwards [hopen.mem_nhds (not_le.1 hζ)] with y' hy'
      exact hρs _ hy'.le
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [iteratedFDeriv_const_of_ne hk.ne']
      simp

/-- The weight `f(x, y) |det Dκ(y)| |det M(x, y)|` is smooth if `f` is smooth and `Dκ(y)` and
`M(x, y)` are invertible on the support of `f`. -/
private theorem contDiff_mul_abs_det_mul_abs_det {κ : CoordinateSpace n → CoordinateSpace n}
    (hκ : ContDiff ℝ ∞ κ)
    {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
    (hM : ContDiff ℝ ∞ M) {f : CoordinateSpace n × CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfu : ∀ w ∈ tsupport f, IsUnit (fderiv ℝ κ w.2) ∧ IsUnit (M w)) :
    ContDiff ℝ ∞ fun w ↦ f w * (|(fderiv ℝ κ w.2).det| * |(M w).det|) := by
  have hdet : ∀ {A : CoordinateSpace n →L[ℝ] CoordinateSpace n}, IsUnit A → A.det ≠ 0 :=
    fun hA ↦
      (LinearMap.isUnit_det _ (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.1 hA)).ne_zero
  have h1 : ContDiff ℝ ∞ fun w : CoordinateSpace n × CoordinateSpace n ↦ (fderiv ℝ κ w.2).det :=
    ContinuousLinearMap.contDiff_det.comp ((hκ.fderiv_right (m := ∞) (by simp)).comp contDiff_snd)
  have h2 : ContDiff ℝ ∞ fun w ↦ (M w).det := ContinuousLinearMap.contDiff_det.comp hM
  -- The determinants do not vanish near the support of `f`.
  have hO : IsOpen {w | (M w).det ≠ 0 ∧ (fderiv ℝ κ w.2).det ≠ 0} :=
    (isOpen_ne_fun h2.continuous continuous_const).inter
      (isOpen_ne_fun h1.continuous continuous_const)
  have hon : ContDiffOn ℝ ∞ (fun w : CoordinateSpace n × CoordinateSpace n ↦
      |(fderiv ℝ κ w.2).det| * |(M w).det|) {w | (M w).det ≠ 0 ∧ (fderiv ℝ κ w.2).det ≠ 0} :=
    fun w hw ↦ ((h1.contDiffAt.abs hw.2).mul (h2.contDiffAt.abs hw.1)).contDiffWithinAt
  exact hon.contDiff_smul_of_tsupport_subset hO hf.contDiffOn
    fun w hw ↦ ⟨hdet (hfu w hw).2, hdet (hfu w hw).1⟩

/-- On the diagonal, the weight `g(x, x) = ψ(x)` and the frequency map `M(x, x) = (Dκ(x)*)⁻¹` of
a change of coordinates turn `g(x, x) • f(κ x, M(x, x) ξ)` into `ψ(x) • f(κ x, (Dκ(x)*)⁻¹ ξ)`, for
any function `f` vanishing at positions outside `K`. -/
private theorem smul_apply_eq_of_diagonal_eq {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : CoordinateSpace n × CoordinateSpace n → F) {K : Set (CoordinateSpace n)}
    (hf : ∀ z ∉ K, ∀ η, f (z, η) = 0) {κ : CoordinateSpace n → CoordinateSpace n}
    {ψ : CoordinateSpace n → ℝ}
    {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
    {g : CoordinateSpace n × CoordinateSpace n → ℝ} (hg₁ : ∀ x, κ x ∈ K → g (x, x) = ψ x)
    (hM₁ : ∀ x, κ x ∈ K → x ∈ tsupport ψ →
      M (x, x) = ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)))
    (x ξ : CoordinateSpace n) :
    g (x, x) • f (κ x, M (x, x) ξ) =
      ψ x • f (κ x, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)) ξ) := by
  by_cases hx : κ x ∈ K
  · by_cases hψx : ψ x = 0
    · simp [hg₁ x hx, hψx]
    · rw [hg₁ x hx, hM₁ x hx (subset_tsupport _ hψx)]
  · simp [hf _ hx]

/-- **Kuranishi's trick.** Let `κ` be a smooth homeomorphism of `ℝⁿ`, `K` a compact set, and `ψ`
a smooth compactly supported cutoff such that `Dκ` is invertible on the support of `ψ`. Suppose the
averaged derivative `hadamardFactor κ y x` of `κ` on the segment from `y` to `x` is invertible
whenever `κ x ∈ K` and `y` lies in the support of `ψ`. Then there are a smooth family `M(x, y)` of
linear maps and a smooth compactly supported weight `g(x, y)`, with `M(x, y)` invertible on the
support of `g`, such that for **every** symbol `a` vanishing at positions outside `K`, whenever
`v ∘ κ = ψ • u`,

`Op(a) v (κ x) = Op(b) u (x)` for the left symbol `b` of the amplitude
`c(x, y, ξ) = g(x, y) • a(κ x, M(x, y) ξ)` (`TauCeti.Symbol.compAmplitude`),

and on the diagonal `g(x, x) = ψ(x)` and `M(x, x) = (Dκ(x)*)⁻¹` (the latter on the support of
`ψ`) wherever `κ x ∈ K`. The data `M` and `g` do not depend on `a` or its order, so the
transported operators of all the symbols vanishing outside `K` are left quantizations of
amplitudes of the same form; `TauCeti.Symbol.exists_amplitude_quantizeSchwartzValue_comp_eq` is
the statement for a single symbol. -/
theorem exists_forall_quantizeSchwartzValue_comp_eq_compAmplitude {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (κ : CoordinateSpace n ≃ₜ CoordinateSpace n) (hκ : ContDiff ℝ ∞ κ)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hκ' : ∀ y ∈ tsupport ψ, IsUnit (fderiv ℝ κ y))
    (hΦ : ∀ x, κ x ∈ K → ∀ y ∈ tsupport ψ, IsUnit (hadamardFactor κ y x)) :
    ∃ (M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n)
      (g : CoordinateSpace n × CoordinateSpace n → ℝ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g)
      (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)),
      (∀ x, κ x ∈ K → g (x, x) = ψ x) ∧
      (∀ x, κ x ∈ K → x ∈ tsupport ψ →
        M (x, x) = ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x))) ∧
      ∀ {m : ℝ} (a : Symbol n V W m), (∀ z ∉ K, ∀ η, a.coefficient (z, η) = 0) →
        ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y, v (κ y) = ψ y • u y) → ∀ x,
          quantizeSchwartzValue a.coefficient v (κ x) =
            quantizeSchwartzValue ((a.compAmplitude hκ hM hg hgc hgM).leftSymbol
              (a.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM)).coefficient u x := by
  -- The Kuranishi factor `Φ(x, y)`, with `κ x - κ y = Φ(x, y) (x - y)`.
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : CoordinateSpace n × CoordinateSpace n →
      CoordinateSpace n →L[ℝ] CoordinateSpace n, Φ = fun w ↦ hadamardFactor κ w.2 w.1 :=
    ⟨_, rfl⟩
  have hΦs : ContDiff ℝ ∞ Φ := by
    rw [hΦdef]
    exact (ContDiff.contDiff_hadamardFactor_uncurry κ hκ).comp (contDiff_snd.prodMk contDiff_fst)
  -- A cutoff `φ` equal to one on `κ⁻¹ K` such that `Φ` is invertible on `supp φ × supp ψ`.
  have hKx : IsCompact (κ ⁻¹' K) := by
    rw [← κ.image_symm]
    exact hK.image κ.symm.continuous
  have hO : IsOpen {w | IsUnit (Φ w)} := Units.isOpen.preimage hΦs.continuous
  obtain ⟨U, U', hU, -, hKU, hψU', hUU'⟩ := generalized_tube_lemma hKx hψc hO
    (fun w hw ↦ by rw [hΦdef]; exact hΦ w.1 hw.1 w.2 hw.2)
  obtain ⟨φ, hφ, -, hφ1, hφc, hφU⟩ := hKx.exists_contDiff_cutoff hU hKU
  have hφ1' : ∀ x, κ x ∈ K → φ x = 1 := fun x hx ↦ interior_subset (hφ1 hx)
  have hS : IsCompact (tsupport φ ×ˢ tsupport ψ) := hφc.prod hψc
  have hSΦ : ∀ w ∈ tsupport φ ×ˢ tsupport ψ, IsUnit (Φ w) :=
    fun w hw ↦ hUU' ⟨hφU hw.1, hψU' hw.2⟩
  -- The frequency map `M = (Φ⁻¹)*` on `supp φ × supp ψ`.
  obtain ⟨M, hM, hMS⟩ := exists_contDiff_eqOn_adjoint_ringInverse hΦs hS hSΦ
  have hMu : ∀ w ∈ tsupport φ ×ˢ tsupport ψ, IsUnit (M w) :=
    fun w hw ↦ hMS w hw ▸ ContinuousLinearMap.isUnit_adjoint_iff.2 (hSΦ w hw).ringInverse
  -- The weight `g(x, y) = φ(x) ψ(y) |det Dκ(y)| |det M(x, y)|`.
  obtain ⟨g, hgdef⟩ : ∃ g : CoordinateSpace n × CoordinateSpace n → ℝ,
      g = fun w ↦ (φ w.1 * ψ w.2) * (|(fderiv ℝ κ w.2).det| * |(M w).det|) := ⟨_, rfl⟩
  have hφψ : tsupport (fun w : CoordinateSpace n × CoordinateSpace n ↦ φ w.1 * ψ w.2) ⊆
      tsupport φ ×ˢ tsupport ψ :=
    closure_minimal (fun w hw ↦ ⟨subset_tsupport _ (left_ne_zero_of_mul hw),
      subset_tsupport _ (right_ne_zero_of_mul hw)⟩)
      ((isClosed_tsupport _).prod (isClosed_tsupport _))
  have hg : ContDiff ℝ ∞ g := by
    rw [hgdef]
    exact contDiff_mul_abs_det_mul_abs_det hκ hM ((hφ.comp contDiff_fst).mul (hψ.comp contDiff_snd))
      fun w hw ↦ ⟨hκ' w.2 (hφψ hw).2, hMu w (hφψ hw)⟩
  have hgS : tsupport g ⊆ tsupport φ ×ˢ tsupport ψ := by
    rw [hgdef]
    exact tsupport_mul_subset_left.trans hφψ
  have hgc : HasCompactSupport g := hS.of_isClosed_subset (isClosed_tsupport _) hgS
  have hgM : ∀ w ∈ tsupport g, IsUnit (M w) := fun w hw ↦ hMu w (hgS hw)
  have hΦx : ∀ x, Φ (x, x) = fderiv ℝ κ x := fun x ↦ by rw [hΦdef]; exact hadamardFactor_self κ x
  have hφx : ∀ x, κ x ∈ K → x ∈ tsupport φ := fun x hx ↦
    subset_tsupport _ (Function.mem_support.2 (by rw [hφ1' x hx]; exact one_ne_zero))
  refine ⟨M, g, hM, hg, hgc, hgM, fun x hx ↦ ?_, fun x hx hxψ ↦ ?_, fun {m} a haK u v huv x ↦ ?_⟩
  · -- On the diagonal `φ(x) = 1`, `M(x, x) = (Dκ(x)⁻¹)*` and `|det Dκ(x)| |det M(x, x)| = 1`.
    rw [hgdef]
    by_cases hψx : ψ x = 0
    · simp [hψx]
    have hxS : (x, x) ∈ tsupport φ ×ˢ tsupport ψ := ⟨hφx x hx, subset_tsupport _ hψx⟩
    have hu : IsUnit (fderiv ℝ κ x) := hΦx x ▸ hSΦ _ hxS
    simp only
    rw [hMS _ hxS, hΦx, hφ1' x hx, ← abs_mul,
      ContinuousLinearMap.det_mul_det_adjoint_ringInverse hu]
    simp
  · have hxS : (x, x) ∈ tsupport φ ×ˢ tsupport ψ := ⟨hφx x hx, hxψ⟩
    rw [hMS _ hxS, hΦx]
  · set c := a.compAmplitude hκ hM hg hgc hgM with hc_def
    have hc : c.HasProperInputSupport := a.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM
    rw [Amplitude.quantizeSchwartzValue_leftSymbol hc]
    by_cases hx : κ x ∈ K
    swap
    · -- Both sides vanish, since `a(κ x, ·) = 0`.
      simp [quantizeSchwartzValue_def, quantizeAmplitudeValue_def, hc_def, haK _ hx,
        Real.fourier_eq]
    -- A cutoff `ρ` with `ρ 0 = 1`, vanishing outside the unit ball, regularizes the symbol.
    obtain ⟨ρ, hρ, -, hρ1, hρc, hρU⟩ := IsCompact.exists_contDiff_cutoff
      (isCompact_singleton (x := (0 : CoordinateSpace n))) Metric.isOpen_ball
      (by simp : {(0 : CoordinateSpace n)} ⊆ Metric.ball 0 1)
    have hρ0 : ρ 0 = 1 := interior_subset (hρ1 rfl)
    have hρs : ∀ η, 1 ≤ ‖η‖ → ρ η = 0 := fun η hη ↦ image_eq_zero_of_notMem_tsupport
      fun h ↦ (not_lt.2 hη) (by simpa using hρU h)
    have hxS : ∀ y ∈ tsupport ψ, (x, y) ∈ tsupport φ ×ˢ tsupport ψ := fun y hy ↦ ⟨hφx x hx, hy⟩
    have hMx : Continuous fun y ↦ M (x, y) :=
      hM.continuous.comp (continuous_const.prodMk continuous_id)
    -- The amplitude side: the regularized amplitudes `ρ(t⁻¹ M(x, y) ξ) c(x, y, ξ)`.
    have hRHS := tendsto_quantizeAmplitudeValue_smul hc x u hψc
      (fun y hy ξ ↦ by
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [hc_def, hgdef, this])
      (r := fun t y ξ ↦ ρ (t⁻¹ • M (x, y) ξ))
      (fun t ξ ↦ hρ.comp ((((hM.comp (contDiff_const.prodMk contDiff_id)).clm_apply
        contDiff_const).const_smul t⁻¹)))
      (fun t ↦ hρ.continuous.comp ((((hM.continuous.comp (continuous_const.prodMk
        continuous_fst)).clm_apply continuous_snd).const_smul t⁻¹)))
      (fun k ↦ (exists_norm_iteratedFDeriv_cutoff_le hM hρ hρs x hψc
        (fun y hy ↦ hMu _ (hxS y hy)) k).imp fun _ hR t _ ↦ hR t)
      (fun y ξ ↦ tendsto_cutoff_inv_smul hρ.continuous hρ0 (M (x, y) ξ))
    -- The symbol side: the regularized symbols `ρ(t⁻¹ η) a(z, η)`.
    have hLHS := tendsto_integral_cutoff_smul_quantizeSchwartzValue' a (κ x) v hρ.continuous
      hρc hρ0
    refine tendsto_nhds_unique hLHS (hRHS.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with t ht
    -- For fixed `t` all integrals converge absolutely, and the change of variables applies.
    have hA : Continuous fun ζ : CoordinateSpace n ↦
        ρ (t⁻¹ • (2 * π) • ζ) • a.coefficient (κ x, (2 * π) • ζ) :=
      (hρ.continuous.comp ((continuous_const_smul _).comp (continuous_const_smul _))).smul
        ((a.continuous_coefficient_slice _).comp (continuous_const_smul _))
    have hAc : HasCompactSupport fun ζ : CoordinateSpace n ↦
        ρ (t⁻¹ • (2 * π) • ζ) • a.coefficient (κ x, (2 * π) • ζ) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : CoordinateSpace n) (t / (2 * π)))
        fun ζ hζ ↦ ?_
      rw [hρs _ ?_, zero_smul]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hζ
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
        Real.norm_of_nonneg (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hζ
      calc (1 : ℝ) = t⁻¹ * t := (inv_mul_cancel₀ ht.ne').symm
        _ ≤ t⁻¹ * (2 * π * ‖ζ‖) := by gcongr; linarith
    rw [integral_fourierChar_smul_apply_fourier_comp_eq (hκ.of_le (by simp)) x hA hAc
      hψ.continuous hψc hMx (fun y hy ↦ hMu _ (hxS y hy))
      (fun y hy ζ h ↦ by
        have hu := hSΦ _ (hxS y hy)
        rw [hMS _ (hxS y hy)]
        simp only [hΦdef] at hu ⊢
        rw [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.ringInverse_apply_apply hu]) huv, quantizeAmplitudeValue_def]
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    dsimp only
    congr 1
    refine congrArg (fun f : CoordinateSpace n → W ↦ 𝓕 f ζ) (funext fun y ↦ ?_)
    simp only [hc_def, Symbol.coefficient_compAmplitude, hgdef, hφ1' x hx, one_mul, map_smul,
      smul_apply, smul_smul]
    congr 1
    ring

/-- **Changes of coordinates for pseudodifferential operators.** Let `κ` be a smooth homeomorphism
of `ℝⁿ`, `a` a symbol of order `m` vanishing at positions outside a compact set `K`, and `ψ` a
smooth compactly supported cutoff such that `Dκ` is invertible on the support of `ψ`. Suppose the
averaged derivative `hadamardFactor κ y x` of `κ` on the segment from `y` to `x` is invertible
whenever `κ x ∈ K` and `y` lies in the support of `ψ`. Then there are a smooth family `M(x, y)` of
linear maps and a smooth compactly supported weight `g(x, y)`, with `M(x, y)` invertible on the
support of `g`, such that, whenever `v ∘ κ = ψ • u`,

`Op(a) v (κ x) = Op(b) u (x)` for the left symbol `b` of the amplitude
`c(x, y, ξ) = g(x, y) • a(κ x, M(x, y) ξ)` (`TauCeti.Symbol.compAmplitude`),

and on the diagonal `g(x, x) = ψ(x)` and `M(x, x) = (Dκ(x)*)⁻¹` (the latter on the support of
`ψ`) wherever `κ x ∈ K`; so the restriction of `c` to the diagonal is `ψ(x) a(κ x, (Dκ(x)*)⁻¹ ξ)`.
In particular the operator `u ↦ Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ` is the quantization of a symbol of order
`m`, whose full asymptotic expansion is `b ∼ ∑ₖ c.leftTerm k`
(`TauCeti.Amplitude.isAsymptoticSum_leftSymbol`). -/
theorem Symbol.exists_amplitude_quantizeSchwartzValue_comp_eq (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ z ∉ K, ∀ η, a.coefficient (z, η) = 0)
    (κ : CoordinateSpace n ≃ₜ CoordinateSpace n) (hκ : ContDiff ℝ ∞ κ)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hκ' : ∀ y ∈ tsupport ψ, IsUnit (fderiv ℝ κ y))
    (hΦ : ∀ x, κ x ∈ K → ∀ y ∈ tsupport ψ, IsUnit (hadamardFactor κ y x)) :
    ∃ (M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n)
      (g : CoordinateSpace n × CoordinateSpace n → ℝ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g)
      (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)),
      (∀ x, κ x ∈ K → g (x, x) = ψ x) ∧
      (∀ x, κ x ∈ K → x ∈ tsupport ψ →
        M (x, x) = ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x))) ∧
      ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y, v (κ y) = ψ y • u y) → ∀ x,
        quantizeSchwartzValue a.coefficient v (κ x) =
          quantizeSchwartzValue ((a.compAmplitude hκ hM hg hgc hgM).leftSymbol
            (a.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM)).coefficient u x := by
  obtain ⟨M, g, hM, hg, hgc, hgM, hg₁, hM₁, hop⟩ :=
    exists_forall_quantizeSchwartzValue_comp_eq_compAmplitude (V := V) (W := W) hK κ hκ hψ hψc hκ'
      hΦ
  exact ⟨M, g, hM, hg, hgc, hgM, hg₁, hM₁, hop a haK⟩

/-- **Changes of coordinates, the leading term.** Under the hypotheses of
`TauCeti.Symbol.exists_amplitude_quantizeSchwartzValue_comp_eq`, the transported operator
`u ↦ Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ` is `Op(b)` for a symbol `b` of order `m` with

`b(x, ξ) = ψ(x) a(κ x, (Dκ(x)*)⁻¹ ξ) + r(x, ξ)`

for a symbol `r` of order `m - 1`: the principal part of `b` is the pullback of `a` by the cotangent
map of `κ`. -/
theorem Symbol.exists_quantizeSchwartzValue_comp_eq (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ z ∉ K, ∀ η, a.coefficient (z, η) = 0)
    (κ : CoordinateSpace n ≃ₜ CoordinateSpace n) (hκ : ContDiff ℝ ∞ κ)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hκ' : ∀ y ∈ tsupport ψ, IsUnit (fderiv ℝ κ y))
    (hΦ : ∀ x, κ x ∈ K → ∀ y ∈ tsupport ψ, IsUnit (hadamardFactor κ y x)) :
    ∃ b : Symbol n V W m, (∃ r : Symbol n V W (m - 1), ∀ x ξ, b.coefficient (x, ξ) =
        ψ x • a.coefficient (κ x, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)) ξ) +
          r.coefficient (x, ξ)) ∧
      ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y, v (κ y) = ψ y • u y) → ∀ x,
        quantizeSchwartzValue a.coefficient v (κ x) = quantizeSchwartzValue b.coefficient u x := by
  obtain ⟨M, g, hM, hg, hgc, hgM, hg₁, hM₁, hop⟩ :=
    a.exists_amplitude_quantizeSchwartzValue_comp_eq hK haK κ hκ hψ hψc hκ' hΦ
  have hc := a.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM
  refine ⟨_, ⟨Symbol.inclusion (by simp)
    ((a.compAmplitude hκ hM hg hgc hgM).leftRemainder hc 1), fun x ξ ↦ ?_⟩, hop⟩
  rw [Amplitude.leftSymbol_eq_diagonal_add_leftRemainder_one hc]
  simp [smul_apply_eq_of_diagonal_eq a.coefficient haK hg₁ hM₁ x ξ]

/-- **Changes of coordinates for classical symbols.** Under the hypotheses of
`TauCeti.Symbol.exists_amplitude_quantizeSchwartzValue_comp_eq`, if `a` is a classical symbol, then
the transported operator `u ↦ Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ` is `Op(b)` for a classical symbol `b` of
order `m`, and **the principal symbol transforms by the cotangent map**:

`σ(b)(x, ξ) = ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`. -/
theorem ClassicalSymbol.exists_quantizeSchwartzValue_comp_eq (a : ClassicalSymbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ z ∉ K, ∀ η, a.toSymbol.coefficient (z, η) = 0)
    (κ : CoordinateSpace n ≃ₜ CoordinateSpace n) (hκ : ContDiff ℝ ∞ κ)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hκ' : ∀ y ∈ tsupport ψ, IsUnit (fderiv ℝ κ y))
    (hΦ : ∀ x, κ x ∈ K → ∀ y ∈ tsupport ψ, IsUnit (hadamardFactor κ y x)) :
    ∃ b : ClassicalSymbol n V W m, (∀ x ξ, b.principal.coefficient (x, ξ) =
        ψ x • a.principal.coefficient
          (κ x, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)) ξ)) ∧
      ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y, v (κ y) = ψ y • u y) → ∀ x,
        quantizeSchwartzValue a.toSymbol.coefficient v (κ x) =
          quantizeSchwartzValue b.toSymbol.coefficient u x := by
  obtain ⟨M, g, hM, hg, hgc, hgM, hg₁, hM₁, hop⟩ :=
    a.toSymbol.exists_amplitude_quantizeSchwartzValue_comp_eq hK haK κ hκ hψ hψc hκ' hΦ
  refine ⟨(a.compAmplitude hκ hM hg hgc hgM).leftSymbol
    (a.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM), fun x ξ ↦ ?_, fun u v huv x ↦ ?_⟩
  · rw [ClassicalSymbol.coefficient_principal_leftSymbol_compAmplitude]
    exact smul_apply_eq_of_diagonal_eq a.principal.coefficient
      (fun z hz ξ ↦ a.coefficient_principal_eq_zero_of_forall (haK z hz) ξ) hg₁ hM₁ x ξ
  · rw [hop u v huv x]
    simp

end Main

end TauCeti
