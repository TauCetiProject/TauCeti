/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Properly supported quantization by a kernel cutoff

The left quantization `Op(a)` of a symbol `a ∈ S^m` has the distribution kernel
`K_a(x, y) = (2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) dξ`. It is smooth off the diagonal but in general
not supported near it, so `Op(a)` need not preserve compact supports. Multiplying the kernel by
`χ(x - y)`, for a cutoff `χ` supported near `0`, localizes it near the diagonal. On the symbol side
this is the **kernel cutoff**

`a_χ(x, ξ) = ∫ 𝓕 χ(η) a(x, ξ - 2πη) dη`

(`TauCeti.Symbol.kernelCutoff`), the average of the frequency translates of `a` against the
Fourier transform of `χ`, again a symbol of order `m`. If `χ` has compact support and equals `1`
near `0`, then `Op(a_χ)` is properly supported and differs from `Op(a)` by a smoothing operator.
This is how a pseudodifferential operator is replaced by a properly supported one before it is
composed, patched in charts, or applied to distributions.

## Main results

* `TauCeti.Symbol.mixedDeriv_kernelCutoff`: the mixed derivatives of `a_χ` are the kernel cutoffs
  of the mixed derivatives of `a`.
* `TauCeti.Symbol.quantizeSchwartzValue_kernelCutoff`: `Op(a_χ) u (x) = Op(a) (χ(x - ·) u) (x)`,
  so the kernel of `Op(a_χ)` is `χ(x - y) K_a(x, y)`.
* `TauCeti.Symbol.support_quantizeSchwartzValue_kernelCutoff_subset`,
  `TauCeti.Symbol.tsupport_quantizeSchwartzValue_kernelCutoff_subset`: `Op(a_χ)` moves supports by
  at most the support of `χ`, `supp Op(a_χ) u ⊆ supp u + supp χ`.
* `TauCeti.Symbol.hasCompactSupport_quantizeSchwartzValue_kernelCutoff`: for compactly supported
  `χ`, `Op(a_χ)` maps compactly supported Schwartz functions to compactly supported functions.
* `TauCeti.Symbol.isSmoothing_kernelCutoff_sub`: if `χ = 1` near `0`, the cutoff correction
  `a_χ - a` is a smoothing symbol.
* `TauCeti.Symbol.exists_isSmoothing_sub_and_tsupport_quantizeSchwartzValue_subset`: every symbol
  is, modulo smoothing symbols, one whose quantization moves supports by at most a given `ε > 0`.

## Proof outline

The quantization identity is a change of the order of integration. Writing `χ(x - y)` by Fourier
inversion turns the Fourier transform of `χ(x - ·) u` into a convolution of `𝓕 χ` with `𝓕 u`, and
translating the frequency variable gives the defining integral of `a_χ`.

Every Fréchet derivative of `a_χ` is the average of the corresponding derivative of `a`, by
differentiation under the integral sign (Mathlib's `hasFTaylorSeriesUpToOn_integral_of_le_bound`).
Peetre's inequality `⟨ξ - 2πη⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨2πη⟩ ^ |s| ⟨ξ⟩ ^ s` and the rapid decay of
`𝓕 χ` give the integrable majorants, and the estimate `‖∂_x^α ∂_ξ^β a_χ(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m - |β|)`.

For the smoothing estimate, expand `η ↦ ∂_x^α ∂_ξ^β a(x, ξ - 2πη)` by Taylor's formula to order
`N`. If `χ = 1` near `0`, then `∫ 𝓕 χ = χ(0) = 1` and the moments of positive order of `𝓕 χ`
vanish (`SchwartzMap.integral_fourier_smul_apply_eq_zero`), so averaging the Taylor polynomial
returns `∂_x^α ∂_ξ^β a(x, ξ)`. Only the remainder survives, and it is controlled by the
frequency derivatives of order `N + 1`, which are symbols of order `m - |β| - N - 1`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Filter Nat
open scoped SchwartzMap RealInnerProductSpace ContDiff Topology Pointwise

namespace TauCeti

variable {n : ℕ}

/-! ### Averages of frequency translates -/

section ShiftIntegral

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The average `∫ g(η) f(x, ξ - 2πη) dη` of the frequency translates of `f` against `g`. -/
private def shiftIntegral (g : 𝓢(CoordinateSpace n, ℂ))
    (f : CoordinateSpace n × CoordinateSpace n → G) (p : CoordinateSpace n × CoordinateSpace n) :
    G :=
  ∫ η, g η • f (p.1, p.2 - (2 * π) • η)

/-- All derivatives of `f` grow at most polynomially in the frequency, locally uniformly in the
position. -/
private def HasLocalGrowth (f : CoordinateSpace n × CoordinateSpace n → G) : Prop :=
  ∀ k : ℕ, ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C s : ℝ, ∀ x ∈ K, ∀ ξ,
    ‖iteratedFDeriv ℝ k f (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (s / 2)

/-- A point of the unit ball around `p₀` has its position in the closed unit ball around `p₀.1`
and its frequency within distance one of `p₀.2`. -/
private lemma mem_closedBall_and_norm_sub_le {p p₀ : CoordinateSpace n × CoordinateSpace n}
    (hp : p ∈ Metric.ball p₀ 1) : p.1 ∈ Metric.closedBall p₀.1 1 ∧ ‖p.2 - p₀.2‖ ≤ 1 := by
  rw [Metric.mem_ball, Prod.dist_eq] at hp
  exact ⟨Metric.mem_closedBall.2 ((le_max_left _ _).trans hp.le),
    (dist_eq_norm p.2 p₀.2).symm.le.trans ((le_max_right _ _).trans hp.le)⟩

/-- The derivatives of a frequency translate of `f`, scaled by `c`, are the scaled translates of
the derivatives of `f`. -/
private lemma iteratedFDeriv_smul_comp_shift {f : CoordinateSpace n × CoordinateSpace n → G}
    (hf : ContDiff ℝ ∞ f) (c : ℂ) (η : CoordinateSpace n) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    iteratedFDeriv ℝ k (fun q : CoordinateSpace n × CoordinateSpace n ↦
        c • f (q.1, q.2 - (2 * π) • η)) p =
      c • iteratedFDeriv ℝ k f (p.1, p.2 - (2 * π) • η) := by
  have hq (q : CoordinateSpace n × CoordinateSpace n) :
      (q.1, q.2 - (2 * π) • η) = q - (0, (2 * π) • η) := by
    ext <;> simp
  have hd : ContDiff ℝ ∞ fun q ↦ f (q - (0, (2 * π) • η)) :=
    hf.comp (contDiff_id.sub contDiff_const)
  simp only [hq]
  rw [iteratedFDeriv_const_smul_apply' (hd.contDiffAt.of_le (mod_cast le_top)),
    iteratedFDeriv_comp_sub]

/-- **Differentiation under the integral sign** for an average of frequency translates. On the
unit ball around `p₀`, the Taylor series of `shiftIntegral g f` is the average of the translated
Taylor series of `f`, by Mathlib's `hasFTaylorSeriesUpToOn_integral_of_le_bound`. Peetre's
inequality and the decay of `g` give the integrable majorants. -/
private lemma hasFTaylorSeriesUpToOn_shiftIntegral (g : 𝓢(CoordinateSpace n, ℂ))
    {f : CoordinateSpace n × CoordinateSpace n → G} (hf : ContDiff ℝ ∞ f)
    (hb : HasLocalGrowth f) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFTaylorSeriesUpToOn ∞ (shiftIntegral g f)
      (fun p k ↦ ∫ η, g η • iteratedFDeriv ℝ k f (p.1, p.2 - (2 * π) • η))
      (Metric.ball p₀ 1) := by
  choose C s hC using fun k ↦ hb k _ (isCompact_closedBall p₀.1 1)
  refine hasFTaylorSeriesUpToOn_integral_of_le_bound
    (F := fun (p : CoordinateSpace n × CoordinateSpace n) η ↦ g η • f (p.1, p.2 - (2 * π) • η))
    (p := fun p η k ↦ g η • iteratedFDeriv ℝ k f (p.1, p.2 - (2 * π) • η))
    (bound := fun k η ↦ C k * (2 ^ (|s k| / 2) * 2 ^ |s k| * (1 + ‖p₀.2‖ ^ 2) ^ (s k / 2)) *
      ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|s k| / 2) * ‖g η‖))
    Metric.isOpen_ball (fun p _ k _ ↦ ?_) (.of_forall fun η p hp k _ ↦ ?_)
    (fun k _ ↦ (g.integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |s k|).const_mul _)
    (.of_forall fun η ↦ ?_)
  · exact (g.continuous.smul ((hf.continuous_iteratedFDeriv (mod_cast le_top)).comp
      (by fun_prop))).aestronglyMeasurable
  · obtain ⟨h₁, h₂⟩ := mem_closedBall_and_norm_sub_le hp
    exact g.norm_smul_apply_sub_smul_le (f := fun ζ ↦ iteratedFDeriv ℝ k f (p.1, ζ))
      (hC k p.1 h₁) (2 * π) h₂ η
  · have hc : ContDiff ℝ ∞ fun q : CoordinateSpace n × CoordinateSpace n ↦
        g η • f (q.1, q.2 - (2 * π) • η) :=
      (hf.comp (by fun_prop)).const_smul (g η)
    exact ((contDiff_iff_ftaylorSeries.1 hc).hasFTaylorSeriesUpToOn _).congr_series
      fun k _ q _ ↦ iteratedFDeriv_smul_comp_shift hf (g η) η k q

/-- The average of the frequency translates of a smooth function of locally uniform polynomial
growth is smooth. -/
private lemma contDiff_shiftIntegral (g : 𝓢(CoordinateSpace n, ℂ))
    {f : CoordinateSpace n × CoordinateSpace n → G} (hf : ContDiff ℝ ∞ f)
    (hb : HasLocalGrowth f) : ContDiff ℝ ∞ (shiftIntegral g f) :=
  contDiff_iff_contDiffAt.2 fun p₀ ↦ (hasFTaylorSeriesUpToOn_shiftIntegral g hf hb p₀).contDiffOn
    |>.contDiffAt (Metric.ball_mem_nhds p₀ one_pos)

/-- The derivatives of an average of frequency translates are the averages of the translates of
the derivatives. -/
private lemma iteratedFDeriv_shiftIntegral (g : 𝓢(CoordinateSpace n, ℂ))
    {f : CoordinateSpace n × CoordinateSpace n → G} (hf : ContDiff ℝ ∞ f)
    (hb : HasLocalGrowth f) (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    iteratedFDeriv ℝ k (shiftIntegral g f) p =
      ∫ η, g η • iteratedFDeriv ℝ k f (p.1, p.2 - (2 * π) • η) := by
  have hp : p ∈ Metric.ball p 1 := Metric.mem_ball_self one_pos
  have h := (hasFTaylorSeriesUpToOn_shiftIntegral g hf hb p).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := k) (mod_cast le_top) Metric.isOpen_ball.uniqueDiffOn hp
  rw [iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball hp] at h
  exact h.symm

end ShiftIntegral

/-! ### The kernel cutoff of a symbol -/

namespace Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

private lemma hasLocalGrowth_coefficient (a : Symbol n V W m) : HasLocalGrowth a.coefficient :=
  fun k _ hK ↦ by
    obtain ⟨C, -, hC⟩ := a.exists_norm_iteratedFDeriv_coefficient_le hK k
    exact ⟨C, m, hC⟩

private lemma integrable_smul_coefficient_shift (g : 𝓢(CoordinateSpace n, ℂ))
    (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    Integrable fun η ↦ g η • a.coefficient (x, ξ - (2 * π) • η) := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  exact g.integrable_smul_apply_sub_smul (f := fun ζ ↦ a.coefficient (x, ζ))
    (a.continuous_coefficient_slice x) (hC x (Set.mem_singleton x)) (2 * π) ξ

private lemma mixedDeriv_shiftIntegral (g : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (shiftIntegral g a.coefficient) x ξ =
      ∫ η, g η • mixedDeriv α β a.coefficient x (ξ - (2 * π) • η) := by
  have hs := contDiff_shiftIntegral g a.contDiff_coefficient a.hasLocalGrowth_coefficient
  obtain ⟨C, -, hC⟩ :=
    a.exists_norm_iteratedFDeriv_coefficient_le isCompact_singleton (mixedDirections α β).length
  rw [mixedDeriv_eq_iteratedFDeriv α β (hs.of_le (mod_cast le_top)),
    iteratedFDeriv_shiftIntegral g a.contDiff_coefficient a.hasLocalGrowth_coefficient,
    ContinuousMultilinearMap.integral_apply (g.integrable_smul_apply_sub_smul
      (f := fun ζ ↦ iteratedFDeriv ℝ _ a.coefficient (x, ζ))
      ((a.contDiff_coefficient.continuous_iteratedFDeriv (mod_cast le_top)).comp (by fun_prop))
      (hC x (Set.mem_singleton x)) (2 * π) ξ)]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  dsimp only
  rw [mixedDeriv_eq_iteratedFDeriv α β (a.contDiff_coefficient.of_le (mod_cast le_top)),
    smul_apply]

/-- The **kernel cutoff** `a_χ` of a symbol `a` by a Schwartz function `χ`: the symbol
`a_χ(x, ξ) = ∫ 𝓕 χ(η) a(x, ξ - 2πη) dη` of the same order, obtained by averaging the frequency
translates of `a` against the Fourier transform of `χ`. Its quantization is
`Op(a_χ) u (x) = Op(a) (χ(x - ·) u) (x)` (`TauCeti.Symbol.quantizeSchwartzValue_kernelCutoff`):
the kernel of `Op(a)` multiplied by `χ(x - y)`. -/
def kernelCutoff (χ : 𝓢(CoordinateSpace n, ℂ)) : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := shiftIntegral (𝓕 χ) a.coefficient
      contDiff_coefficient :=
        contDiff_shiftIntegral (𝓕 χ) a.contDiff_coefficient a.hasLocalGrowth_coefficient
      exists_bound := fun K hK α β ↦ by
        obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α β
        refine ⟨C * 2 ^ (|m - β.length| / 2) * 2 ^ |m - β.length| *
          ∫ η, (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m - β.length| / 2) * ‖𝓕 χ η‖,
          mul_nonneg (by positivity) (integral_nonneg fun _ ↦ by positivity), fun x hx ξ ↦ ?_⟩
        rw [mixedDeriv_shiftIntegral]
        exact SchwartzMap.norm_integral_smul_apply_sub_smul_le _ (hC x hx) (2 * π) ξ }
  map_add' a b := Symbol.ext <| funext fun p ↦ by
    simp only [coefficient_add, shiftIntegral, Pi.add_apply, smul_add]
    exact integral_add (integrable_smul_coefficient_shift _ a _ _)
      (integrable_smul_coefficient_shift _ b _ _)
  map_smul' c a := Symbol.ext <| funext fun p ↦ by
    simp only [coefficient_smul, shiftIntegral, Pi.smul_apply, RingHom.id_apply,
      smul_comm (𝓕 χ _) c]
    exact integral_smul c _

variable {χ : 𝓢(CoordinateSpace n, ℂ)}

/-- The coefficient of the kernel cutoff is the average of the frequency translates of `a` against
`𝓕 χ`. -/
@[simp]
theorem coefficient_kernelCutoff (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (kernelCutoff χ a).coefficient (x, ξ) = ∫ η, 𝓕 χ η • a.coefficient (x, ξ - (2 * π) • η) :=
  (rfl)

/-- The mixed derivatives of a kernel cutoff are the kernel cutoffs of the mixed derivatives. -/
theorem mixedDeriv_kernelCutoff (a : Symbol n V W m) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (kernelCutoff χ a).coefficient x ξ =
      ∫ η, 𝓕 χ η • mixedDeriv α β a.coefficient x (ξ - (2 * π) • η) :=
  mixedDeriv_shiftIntegral (𝓕 χ) a α β x ξ

/-- **The cutoff correction is smoothing.** If `χ = 1` near `0`, the kernel cutoff `a_χ` differs
from `a` by a smoothing symbol: the kernel `(χ(x - y) - 1) K_a(x, y)` of the cutoff correction
`a_χ - a` vanishes near the diagonal. -/
theorem isSmoothing_kernelCutoff_sub [CompleteSpace W] (hχ : (χ : CoordinateSpace n → ℂ) =ᶠ[𝓝 0] 1)
    (a : Symbol n V W m) : (kernelCutoff χ a - a).IsSmoothing := by
  refine isSmoothing_iff_forall_exists_bound.2 fun m' K hK α β ↦ ?_
  set N := ⌈m - m'⌉₊
  set t : ℝ := m - ((N + 1 : ℕ) + β.length)
  choose A hA0 hA using fun r : Fin (N + 1) → Fin n ↦ a.exists_bound K hK α (List.ofFn r ++ β)
  refine ⟨(∑ r, A r) * 2 ^ (|t| / 2) / N ! *
    ∫ η, (1 + ‖(2 * π) • η‖ ^ 2) ^ ((|t| + (N + 1)) / 2) * ‖𝓕 χ η‖,
    mul_nonneg (div_nonneg (mul_nonneg (Finset.sum_nonneg fun r _ ↦ hA0 r) (by positivity))
      (by positivity)) (integral_nonneg fun _ ↦ by positivity), fun x hx ξ ↦ ?_⟩
  set h : CoordinateSpace n → V →L[ℂ] W := fun ζ ↦ mixedDeriv α β a.coefficient x ζ
  have hh : ContDiff ℝ ∞ h :=
    (a.contDiff_coefficient.mixedDeriv α β).comp (contDiff_prodMk_right x)
  -- The `(N + 1)`-st frequency derivatives of `h` have order `t`.
  have hD (ζ : CoordinateSpace n) :
      ‖iteratedFDeriv ℝ (N + 1) h ζ‖ ≤ (∑ r, A r) * (1 + ‖ζ‖ ^ 2) ^ (t / 2) := by
    refine (norm_iteratedFDeriv_le_sum_coordinateDeriv (hh.of_le (by simp)) ζ).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ ↦ ?_
    rw [coordinateDeriv_mixedDeriv a.contDiff_coefficient]
    refine (hA r x hx ζ).trans (le_of_eq ?_)
    simp only [t, List.length_append, List.length_ofFn]
    push_cast
    ring_nf
  have hsub : mixedDeriv α β (kernelCutoff χ a - a).coefficient x ξ =
      (∫ η, 𝓕 χ η • h (ξ - (2 * π) • η)) - h ξ := by
    rw [coefficient_sub, sub_eq_add_neg, mixedDeriv_add (kernelCutoff χ a).contDiff_coefficient
      (b := -a.coefficient) a.contDiff_coefficient.neg, mixedDeriv_neg, mixedDeriv_kernelCutoff,
      ← sub_eq_add_neg]
  rw [hsub]
  refine (SchwartzMap.norm_integral_fourier_smul_sub_smul_sub_le χ hχ (hh.of_le (by simp))
    hD (2 * π) ξ).trans
    (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ ?_)
      (mul_nonneg (div_nonneg (mul_nonneg (Finset.sum_nonneg fun r _ ↦ hA0 r) (by positivity))
        (by positivity)) (integral_nonneg fun _ ↦ by positivity)))
  have hN := Nat.le_ceil (m - m')
  simp only [t, Nat.cast_add, Nat.cast_one]
  linarith

end Symbol

/-! ### The quantization of a kernel cutoff -/

section Quantization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {m : ℝ}

namespace Symbol

omit [CompleteSpace V] [CompleteSpace W] in
/-- The integrand `(ζ', η) ↦ 𝓕 χ(η) exp(2πi ⟪ζ', x⟫) a(x, 2πζ' - 2πη) 𝓕 u(ζ')` of `Op(a_χ) u (x)`
is integrable: by Peetre's inequality it is dominated by a product of integrable functions of
`ζ'` and of `η`. -/
private lemma integrable_kernelCutoff_integrand (χ : 𝓢(CoordinateSpace n, ℂ))
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun p : CoordinateSpace n × CoordinateSpace n ↦ 𝓕 χ p.2 • (𝐞 ⟪p.1, x⟫ : ℂ) •
      a.coefficient (x, (2 * π) • p.1 - (2 * π) • p.2) (𝓕 u p.1)) (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  have hc : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦ 𝓕 χ p.2 •
      (𝐞 ⟪p.1, x⟫ : ℂ) • a.coefficient (x, (2 * π) • p.1 - (2 * π) • p.2) (𝓕 u p.1) := by
    have h₁ : Continuous ⇑(𝓕 χ : 𝓢(CoordinateSpace n, ℂ)) := (𝓕 χ).continuous
    have h₂ : Continuous fun t : ℝ ↦ (𝐞 t : ℂ) :=
      continuous_subtype_val.comp Real.continuous_fourierChar
    have h₃ : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
        a.coefficient (x, (2 * π) • p.1 - (2 * π) • p.2) :=
      a.contDiff_coefficient.continuous.comp (by fun_prop)
    have h₄ : Continuous ⇑(𝓕 u : 𝓢(CoordinateSpace n, V)) := (𝓕 u).continuous
    exact (h₁.comp continuous_snd).smul
      ((h₂.comp (by fun_prop)).smul (h₃.clm_apply (h₄.comp continuous_fst)))
  refine ((((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m).mul_prod
    ((𝓕 χ).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |m|)).const_mul
      (C * 2 ^ (|m| / 2))).mono' hc.aestronglyMeasurable (.of_forall fun p ↦ ?_)
  have hP := one_add_norm_sq_rpow_le_mul_sub m ((2 * π) • p.1 - (2 * π) • p.2) ((2 * π) • p.1)
  rw [sub_sub_cancel_left, norm_neg] at hP
  simp only [norm_smul, Circle.norm_coe, one_mul]
  calc ‖𝓕 χ p.2‖ * ‖a.coefficient (x, (2 * π) • p.1 - (2 * π) • p.2) (𝓕 u p.1)‖
      ≤ ‖𝓕 χ p.2‖ * (C * (1 + ‖(2 * π) • p.1 - (2 * π) • p.2‖ ^ 2) ^ (m / 2) *
          ‖𝓕 u p.1‖) := by
        gcongr
        exact ((a.coefficient _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC x (Set.mem_singleton x) _) (norm_nonneg _))
    _ ≤ ‖𝓕 χ p.2‖ * (C * (2 ^ (|m| / 2) * (1 + ‖(2 * π) • p.2‖ ^ 2) ^ (|m| / 2) *
          (1 + ‖(2 * π) • p.1‖ ^ 2) ^ (m / 2)) * ‖𝓕 u p.1‖) := by gcongr
    _ = _ := by
      simp only [norm_smul]
      ring

omit [CompleteSpace V] [CompleteSpace W] in
/-- `Op(a_χ) u (x)` as an iterated integral over `(ζ', η)`, by expanding `a_χ`. -/
private lemma quantizeSchwartzValue_kernelCutoff_eq_integral (χ : 𝓢(CoordinateSpace n, ℂ))
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (kernelCutoff χ a).coefficient u x = ∫ ζ', ∫ η, 𝓕 χ η •
      (𝐞 ⟪ζ', x⟫ : ℂ) • a.coefficient (x, (2 * π) • ζ' - (2 * π) • η) (𝓕 u ζ') := by
  rw [quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ' ↦ ?_)
  dsimp only
  rw [coefficient_kernelCutoff, ContinuousLinearMap.integral_apply
    (integrable_smul_coefficient_shift (𝓕 χ) a x _), Circle.smul_def, ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [smul_apply, smul_comm (𝓕 χ η)]

/-- `Op(a)` on the cut-off input `y ↦ χ(x - y) u(y)` as an iterated integral over `(ζ, η)`, by the
convolution formula `SchwartzMap.fourier_smulLeftCLM_sub_apply`. -/
private lemma quantizeSchwartzValue_smulLeftCLM_sub_eq_integral (χ : 𝓢(CoordinateSpace n, ℂ))
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x =
      ∫ ζ, ∫ η, 𝓕 χ η • (𝐞 ⟪η + ζ, x⟫ : ℂ) • a.coefficient (x, (2 * π) • ζ) (𝓕 u (η + ζ)) := by
  have h₂ : Continuous fun t : ℝ ↦ (𝐞 t : ℂ) :=
    continuous_subtype_val.comp Real.continuous_fourierChar
  rw [quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  dsimp only
  have hi : Integrable fun η ↦ 𝓕 χ η • (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 u (ζ + η) := by
    refine ((𝓕 χ).integrable.norm.mul_const (SchwartzMap.seminorm ℂ 0 0 (𝓕 u))).mono'
      ((𝓕 χ).continuous.smul ((h₂.comp (by fun_prop)).smul
        ((𝓕 u).continuous.comp (continuous_const.add continuous_id)))).aestronglyMeasurable
      (.of_forall fun η ↦ ?_)
    rw [norm_smul, norm_smul, Circle.norm_coe, one_mul]
    gcongr
    exact SchwartzMap.norm_le_seminorm ℂ (𝓕 u) _
  rw [SchwartzMap.fourier_smulLeftCLM_sub_apply, ← (a.coefficient _).integral_comp_comm hi,
    Circle.smul_def,
    ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [map_smul, smul_smul]
  rw [add_comm η ζ]
  congr 1
  have e : (𝐞 ⟪ζ + η, x⟫ : ℂ) = 𝐞 ⟪ζ, x⟫ * 𝐞 ⟪η, x⟫ := by
    rw [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
  rw [e]
  ring

omit [CompleteSpace V] [CompleteSpace W] in
/-- **The quantization of a kernel cutoff.** `Op(a_χ)` evaluated at `x` is `Op(a)` evaluated at
`x` on the cut-off input `y ↦ χ(x - y) u(y)`: the kernel `K_a(x, y)` of `Op(a)` is multiplied by
`χ(x - y)`. -/
theorem quantizeSchwartzValue_kernelCutoff (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (kernelCutoff χ a).coefficient u x =
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x := by
  -- If `V` is not complete then `𝓕 u = 0`, and if `W` is not complete then every `W`-valued
  -- integral is `0`; either way both sides vanish.
  by_cases hV : CompleteSpace V
  swap
  · simp [quantizeSchwartzValue_def, SchwartzMap.fourier_eq_zero_of_not_completeSpace hV]
  by_cases hW : CompleteSpace W
  swap
  · simp [quantizeSchwartzValue_def, integral_of_not_completeSpace hW]
  set G : CoordinateSpace n × CoordinateSpace n → W := fun p ↦
    𝓕 χ p.2 • (𝐞 ⟪p.1, x⟫ : ℂ) • a.coefficient (x, (2 * π) • p.1 - (2 * π) • p.2) (𝓕 u p.1)
  set F : CoordinateSpace n × CoordinateSpace n → W := fun p ↦
    𝓕 χ p.2 • (𝐞 ⟪p.2 + p.1, x⟫ : ℂ) • a.coefficient (x, (2 * π) • p.1) (𝓕 u (p.2 + p.1))
  have hG : Integrable G (volume.prod volume) := integrable_kernelCutoff_integrand χ a u x
  -- The right integrand is the left one after the shear `(ζ, η) ↦ (η + ζ, η)`.
  have hT : MeasurePreserving (fun p : CoordinateSpace n × CoordinateSpace n ↦ (p.2 + p.1, p.2))
      (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_swap.comp (measurePreserving_prod_add volume volume)).comp
      Measure.measurePreserving_swap
  have hFG : F = G ∘ fun p ↦ (p.2 + p.1, p.2) := by
    funext p
    simp [F, G, smul_add]
  have hF : Integrable F (volume.prod volume) := hFG ▸ hT.integrable_comp_of_integrable hG
  rw [quantizeSchwartzValue_kernelCutoff_eq_integral,
    quantizeSchwartzValue_smulLeftCLM_sub_eq_integral,
    integral_integral_swap (f := fun ζ' η ↦ G (ζ', η)) hG,
    integral_integral_swap (f := fun ζ η ↦ F (ζ, η)) hF]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  dsimp only
  rw [← integral_add_right_eq_self (fun ζ' ↦ G (ζ', η)) η, hFG]
  simp [add_comm]

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Proper support.** The quantization of a kernel cutoff `a_χ` moves supports by at most the
support of `χ`: `Op(a_χ) u` vanishes outside `supp u + supp χ`. -/
theorem support_quantizeSchwartzValue_kernelCutoff_subset (χ : 𝓢(CoordinateSpace n, ℂ))
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) :
    Function.support (quantizeSchwartzValue (kernelCutoff χ a).coefficient u) ⊆
      Function.support u + Function.support χ := by
  intro x hx
  by_contra hcon
  refine hx ?_
  have hχx : (fun y : CoordinateSpace n ↦ χ (x - y)).HasTemperateGrowth :=
    χ.hasTemperateGrowth.comp (by fun_prop)
  have hzero : SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u = 0 := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hχx, zero_apply]
    by_cases hy : u y = 0
    · rw [hy, smul_zero]
    by_cases hχy : χ (x - y) = 0
    · rw [hχy, zero_smul]
    have hmem := Set.add_mem_add (Function.mem_support.2 hy) (Function.mem_support.2 hχy)
    rw [add_sub_cancel] at hmem
    exact absurd hmem hcon
  rw [quantizeSchwartzValue_kernelCutoff, hzero, quantizeSchwartzValue_zero_right]

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Proper support**, closed form: for a compactly supported `χ`,
`supp Op(a_χ) u ⊆ supp u + supp χ`. -/
theorem tsupport_quantizeSchwartzValue_kernelCutoff_subset {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) :
    tsupport (quantizeSchwartzValue (kernelCutoff χ a).coefficient u) ⊆ tsupport u + tsupport χ :=
  closure_minimal ((support_quantizeSchwartzValue_kernelCutoff_subset χ a u).trans
      (Set.add_subset_add (subset_tsupport _) (subset_tsupport _)))
    ((isClosed_tsupport _).add_right_of_isCompact hχ.isCompact)

omit [CompleteSpace V] [CompleteSpace W] in
/-- For a compactly supported `χ`, the quantization of a kernel cutoff sends compactly supported
Schwartz functions to compactly supported functions. -/
theorem hasCompactSupport_quantizeSchwartzValue_kernelCutoff {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport u) :
    HasCompactSupport (quantizeSchwartzValue (kernelCutoff χ a).coefficient u) :=
  (hu.isCompact.add hχ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_quantizeSchwartzValue_kernelCutoff_subset hχ a u)

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Properly supported representatives.** Every symbol differs by a smoothing symbol from one
whose quantization moves supports by at most `ε`: `supp Op(b) u ⊆ supp u + closedBall 0 ε` for
every Schwartz function `u`. The symbol `b` is the kernel cutoff of `a` by a bump function equal to
`1` near `0` and supported in the closed ball of radius `ε`. -/
theorem exists_isSmoothing_sub_and_tsupport_quantizeSchwartzValue_subset (a : Symbol n V W m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Symbol n V W m, (b - a).IsSmoothing ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      tsupport (quantizeSchwartzValue b.coefficient u) ⊆
        tsupport u + Metric.closedBall (0 : CoordinateSpace n) ε := by
  -- If `W` is not complete, every `W`-valued integral is `0`, so `b = a` works.
  by_cases hW : CompleteSpace W
  swap
  · refine ⟨a, by simp, fun u ↦ ?_⟩
    have h0 : quantizeSchwartzValue a.coefficient u = 0 := funext fun x ↦ by
      rw [quantizeSchwartzValue_def, integral_of_not_completeSpace hW, Pi.zero_apply]
    rw [h0, tsupport_zero]
    exact Set.empty_subset _
  let f : ContDiffBump (0 : CoordinateSpace n) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hfc : HasCompactSupport fun y ↦ (f y : ℂ) :=
    f.hasCompactSupport.comp_left Complex.ofReal_zero
  let χ : 𝓢(CoordinateSpace n, ℂ) :=
    hfc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp f.contDiff)
  have hχ : (χ : CoordinateSpace n → ℂ) = fun y ↦ (f y : ℂ) := funext (hfc.toSchwartzMap_toFun _)
  have hχ₁ : (χ : CoordinateSpace n → ℂ) =ᶠ[𝓝 0] 1 := by
    filter_upwards [Metric.closedBall_mem_nhds 0 (half_pos hε)] with y hy
    simp [hχ, f.one_of_mem_closedBall hy]
  have hχ₂ : tsupport χ ⊆ Metric.closedBall 0 ε := by
    rw [hχ]
    refine (tsupport_comp_subset Complex.ofReal_zero f).trans ?_
    rw [f.tsupport_eq]
  have hχc : HasCompactSupport χ := by
    rw [HasCompactSupport, hχ]
    exact hfc
  refine ⟨kernelCutoff χ a, isSmoothing_kernelCutoff_sub hχ₁ a, fun u ↦ ?_⟩
  exact (tsupport_quantizeSchwartzValue_kernelCutoff_subset hχc a u).trans
    (Set.add_subset_add le_rfl hχ₂)

end Symbol

end Quantization

end TauCeti
