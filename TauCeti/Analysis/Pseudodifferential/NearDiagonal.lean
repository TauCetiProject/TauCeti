/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Expansion
public import TauCeti.Analysis.Pseudodifferential.Amplitude.ProperSupport
public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
import TauCeti.Analysis.Calculus.BumpFunction.DiagonalCutoff

/-!
# Near-diagonal localization of pseudodifferential operators

For any symbol `a(x, ξ)` of order `m` on `ℝⁿ` and any smooth spatial cutoff `χ(x, y)` equal to `1`
near `y = x`, when `V` is complete and `u` is a compactly supported Schwartz function, splitting `u`
at `x` into `y ↦ χ(x, y) u(y)` and `y ↦ (1 - χ(x, y)) u(y)` decomposes `Op(a) u (x)` into the
amplitude quantization of `χ(x, y) a(x, ξ)` (`TauCeti.Symbol.localizeAmplitude`) plus the integral
operator with residual kernel `(1 - χ(x, y)) K_a(x, y)`
(`TauCeti.Symbol.localizedOffDiagonalKernel` in
`TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel`), which is globally `C^∞` when `χ = 1` on
a joint neighborhood of every diagonal point `(x, x)`.

Choosing `χ` properly supported via
`TauCeti.exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal` exhibits every
pseudodifferential operator on `ℝⁿ` (for complete `V` and `W`, on compactly supported Schwartz
inputs) as a properly supported amplitude operator whose global left symbol differs from `a` by a
smoothing symbol (`TauCeti.Symbol.isSmoothing_leftSymbol_localizeAmplitude_sub`, for complete `W`)
plus an integral operator with a globally smooth kernel
(`TauCeti.Symbol.exists_hasProperSupport_amplitude_and_contDiff_kernel`).

Compare `TauCeti.Analysis.Pseudodifferential.ProperSupport.Basic`, which cuts off kernels directly
at the symbol level for translation-invariant Schwartz factors `χ(x - y)`: here `χ(x, y)` is an
arbitrary smooth cutoff, giving both the localized amplitude and the explicit `C^∞` kernel.

## Main declarations

* `TauCeti.Symbol.localizeAmplitude`, `TauCeti.Symbol.diagonal_localizeAmplitude`,
  `TauCeti.Symbol.leftTerm_localizeAmplitude_succ`,
  `TauCeti.Symbol.isSmoothing_leftSymbol_localizeAmplitude_sub`.
* Near-diagonal decompositions:
  `TauCeti.Symbol.quantizeSchwartzValue_eq_quantizeSchwartzValue_leftSymbol_add_integral`,
  `TauCeti.Symbol.exists_hasProperSupport_amplitude_and_contDiff_kernel`, and
  `quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel`.

## References

* M. E. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II,
  §§1–2.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, pp. 68–72.
-/

public section

noncomputable section

open Filter Function MeasureTheory Real FourierTransform Set
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

variable {n : ℕ}

namespace Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- Localize a symbol `a(x, ξ)` near the diagonal by multiplying its left-quantization amplitude by
a smooth spatial cutoff `χ(x, y)`, giving the amplitude `(x, y, ξ) ↦ χ(x, y) • a(x, ξ)`. -/
def localizeAmplitude (a : Symbol n V W m) (χ : CoordinateSpace n → CoordinateSpace n → ℝ)
    (hχ : ContDiff ℝ ∞ (uncurry χ)) : Amplitude n V W m :=
  (Amplitude.ofLeft a).smulPositions (fun p ↦ (χ p.1 p.2 : ℂ)) (Complex.ofRealCLM.contDiff.comp hχ)

@[simp]
theorem coefficient_localizeAmplitude (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ))
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (a.localizeAmplitude χ hχ).coefficient p = χ p.1 p.2.1 • a.coefficient (p.1, p.2.2) := by
  simp [localizeAmplitude, ← Complex.coe_algebraMap]

theorem hasProperInputSupport_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : HasProperOutputSupport χ) :
    (a.localizeAmplitude χ hχ).HasProperInputSupport :=
  Amplitude.hasProperInputSupport_smulPositions_of_cutoff _ _
    (hχ_out.of_tsupport_subset (tsupport_comp_subset Complex.ofReal_zero (uncurry χ)))

theorem hasProperOutputSupport_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_in : HasProperInputSupport χ) :
    (a.localizeAmplitude χ hχ).HasProperOutputSupport :=
  Amplitude.hasProperOutputSupport_smulPositions_of_cutoff _ _
    (hχ_in.of_tsupport_subset (tsupport_comp_subset Complex.ofReal_zero (uncurry χ)))

theorem hasProperSupport_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_prop : HasProperSupport χ) :
    (a.localizeAmplitude χ hχ).HasProperSupport :=
  Amplitude.hasProperSupport_iff.mpr
    ⟨a.hasProperInputSupport_localizeAmplitude hχ hχ_prop.out,
      a.hasProperOutputSupport_localizeAmplitude hχ hχ_prop.inp⟩

/-- When `χ(x, x) = 1` for every `x`, the diagonal restriction of `a.localizeAmplitude χ hχ`
recovers `a`. -/
theorem diagonal_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_diag : ∀ x, χ x x = 1) :
    (a.localizeAmplitude χ hχ).diagonal = a := by
  ext1
  funext ⟨x, ξ⟩
  simp [hχ_diag x]

private theorem eventuallyEq_ofLeft_slice_of_eventuallyEq_one (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    {x ξ : CoordinateSpace n} (hχ_diag : (fun y ↦ χ x y) =ᶠ[𝓝 x] 1) :
    (fun q : CoordinateSpace n × CoordinateSpace n ↦
        (a.localizeAmplitude χ hχ).coefficient (x, q.1, q.2))
      =ᶠ[𝓝 (x, ξ)] fun q ↦ (Amplitude.ofLeft a).coefficient (x, q.1, q.2) := by
  filter_upwards [(continuous_fst.tendsto (x, ξ)).eventually hχ_diag] with q hq
  have hq1 : χ x q.1 = 1 := hq
  simp [hq1]

/-- When `χ(x, ·) = 1` near `x` for every `x`, every positive-index term `leftTerm (k + 1)` of
`a.localizeAmplitude χ hχ` vanishes identically because `a(x, ξ)` does not depend on `y` and all
`y`-derivatives of `χ` vanish on the diagonal. -/
theorem leftTerm_localizeAmplitude_succ (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_diag : ∀ x, (fun y ↦ χ x y) =ᶠ[𝓝 x] 1) (k : ℕ) :
    (a.localizeAmplitude χ hχ).leftTerm (k + 1) = 0 := by
  ext1
  funext ⟨x, ξ⟩
  rw [Amplitude.coefficient_leftTerm_congr_of_eventuallyEq_snd
      (a.eventuallyEq_ofLeft_slice_of_eventuallyEq_one hχ (hχ_diag x)) (k + 1),
    Amplitude.leftTerm_ofLeft_succ, coefficient_zero]

/-- **Symbol equivalence under near-diagonal localization.** Requires `W` to be complete; when `χ`
has proper output support and `χ(x, ·) = 1` near `x` for every `x`, the left symbol of
`a.localizeAmplitude χ hχ` differs from `a` by a smoothing symbol (`S^{-∞}`). -/
theorem isSmoothing_leftSymbol_localizeAmplitude_sub [CompleteSpace W] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : HasProperOutputSupport χ) (hχ_diag : ∀ x, (fun y ↦ χ x y) =ᶠ[𝓝 x] 1) :
    (((a.localizeAmplitude χ hχ).leftSymbol
      (a.hasProperInputSupport_localizeAmplitude hχ hχ_out)) - a).IsSmoothing := by
  have hA := a.hasProperInputSupport_localizeAmplitude hχ hχ_out
  have hdiag : (a.localizeAmplitude χ hχ).diagonal = a :=
    a.diagonal_localizeAmplitude hχ fun x ↦ (hχ_diag x).eq_of_nhds
  refine isSmoothing_iff_forall_nat.2 fun N ↦ ?_
  cases N with
  | zero =>
    exact ⟨inclusion (by simp) ((a.localizeAmplitude χ hχ).leftSymbol hA - a),
      coefficient_inclusion _ _⟩
  | succ N =>
    refine ⟨(a.localizeAmplitude χ hχ).leftRemainder hA (N + 1), funext fun ⟨x, ξ⟩ ↦ ?_⟩
    rw [Amplitude.coefficient_leftRemainder, Finset.sum_range_succ',
      Finset.sum_eq_zero fun k _ ↦ by
        rw [a.leftTerm_localizeAmplitude_succ hχ hχ_diag k, coefficient_zero],
      zero_add, coefficient_sub, Pi.sub_apply, Pi.sub_apply, Amplitude.leftTerm_zero,
      coefficient_inclusion, hdiag]

private theorem quantizeSchwartzValue_eq_integral_localizedOffDiagonalKernel_of_eq
    [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hχ_diag : (fun y ↦ χ x y) =ᶠ[𝓝 x] 1) {u w : 𝓢(CoordinateSpace n, V)}
    (hs : HasCompactSupport fun y ↦ (1 - χ x y) • u y)
    (hw : ∀ y, w y = (1 - χ x y) • u y) :
    quantizeSchwartzValue a.coefficient w x =
      ∫ y, a.localizedOffDiagonalKernel χ x y (u y) := by
  have hx_notMem : x ∉ tsupport (w : CoordinateSpace n → V) := by
    refine notMem_tsupport_iff_eventuallyEq.2 ?_
    filter_upwards [hχ_diag] with y hy
    have hy1 : χ x y = 1 := hy
    simp [hw, hy1]
  rw [a.quantizeSchwartzValue_eq_integral_offDiagonalKernel ((funext hw).symm ▸ hs) hx_notMem]
  congr 1 with y
  rw [hw, ContinuousLinearMap.map_smul_of_tower, localizedOffDiagonalKernel_apply, smul_apply]

/-- **Near-diagonal decomposition of a pseudodifferential operator.** Requires `V` to be complete;
for any symbol `a`, any smooth cutoff `χ` with `χ(x, ·) = 1` near `x`, and any compactly
supported Schwartz input `u`, `Op(a) u (x)` splits as the amplitude quantization of
`χ(x, y) a(x, ξ)` plus the integral operator with kernel `(1 - χ(x, y)) K_a(x, y)`. -/
theorem quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel
    [CompleteSpace V] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport (u : CoordinateSpace n → V))
    (x : CoordinateSpace n) (hχ_diag : (fun y ↦ χ x y) =ᶠ[𝓝 x] 1) :
    quantizeSchwartzValue a.coefficient u x =
      quantizeAmplitudeValue (a.localizeAmplitude χ hχ).coefficient u x +
        ∫ y, a.localizedOffDiagonalKernel χ x y (u y) := by
  by_cases hW : CompleteSpace W; swap
  · simp [quantizeSchwartzValue_def, quantizeAmplitudeValue_def, integral_of_not_completeSpace hW]
  have hχx : ContDiff ℝ ∞ fun y ↦ χ x y := hχ.comp (contDiff_const.prodMk contDiff_id)
  have hf₁ : ContDiff ℝ ∞ fun y ↦ χ x y • u y := hχx.smul (u.smooth ⊤)
  have hf₂ : ContDiff ℝ ∞ fun y ↦ (1 - χ x y) • u y := (contDiff_const.sub hχx).smul (u.smooth ⊤)
  have hs₁ : HasCompactSupport fun y ↦ χ x y • u y := hu.smul_left
  have hs₂ : HasCompactSupport fun y ↦ (1 - χ x y) • u y := hu.smul_left
  set w₁ := hs₁.toSchwartzMap hf₁
  set w₂ := hs₂.toSchwartzMap hf₂
  have hw₁ : ∀ y, w₁ y = χ x y • u y := HasCompactSupport.toSchwartzMap_toFun hs₁ hf₁
  have hw₂ : ∀ y, w₂ y = (1 - χ x y) • u y := HasCompactSupport.toSchwartzMap_toFun hs₂ hf₂
  have hu_split : u = w₁ + w₂ := by
    ext y; rw [add_apply, hw₁, hw₂, ← add_smul, add_sub_cancel, one_smul]
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  conv_lhs => rw [hu_split]
  rw [quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable
    hC w₁ w₂, a.quantizeSchwartzValue_eq_integral_localizedOffDiagonalKernel_of_eq
    hχ_diag hs₂ hw₂]
  congr 1
  rw [← quantizeAmplitudeValue_eq_quantizeSchwartzValue a.coefficient w₁ x]
  refine quantizeAmplitudeValue_congr_apply_at fun y ξ ↦ ?_
  rw [hw₁, ContinuousLinearMap.map_smul_of_tower, coefficient_localizeAmplitude, smul_apply]

/-- Requires `V` to be complete; when `χ` also has proper output support and `χ(x, ·) = 1` near
`x`, for any compactly supported Schwartz input `u`, `Op(a) u (x)` decomposes into the symbol
quantization of the left symbol of `a.localizeAmplitude χ hχ` (which agrees with `a` modulo `S^{-∞}`
when `W` is complete) plus the integral operator with kernel `a.localizedOffDiagonalKernel χ`. -/
theorem quantizeSchwartzValue_eq_quantizeSchwartzValue_leftSymbol_add_integral
    [CompleteSpace V] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : HasProperOutputSupport χ) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) (x : CoordinateSpace n)
    (hχ_diag : (fun y ↦ χ x y) =ᶠ[𝓝 x] 1) :
    quantizeSchwartzValue a.coefficient u x =
      quantizeSchwartzValue
          ((a.localizeAmplitude χ hχ).leftSymbol
            (a.hasProperInputSupport_localizeAmplitude hχ hχ_out)).coefficient u x +
        ∫ y, a.localizedOffDiagonalKernel χ x y (u y) := by
  by_cases hW : CompleteSpace W; swap
  · simp [quantizeSchwartzValue_def, integral_of_not_completeSpace hW]
  rw [Amplitude.quantizeSchwartzValue_leftSymbol]
  exact a.quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel
    hχ hu x hχ_diag

/-- **Decomposition of a pseudodifferential operator into a properly supported part and a smooth
kernel.** Requires `V` and `W` to be complete; given `r < R` with `0 < R`, every symbol `a` of order
`m` on `ℝⁿ` admits:
* a properly supported amplitude `A` of order `m` whose closed spatial support
  `tsupport (uncurry fun x y ξ ↦ A.coefficient (x, y, ξ))` is contained in `{(x, y) | ‖x - y‖ < R}`,
  and whose global left symbol differs from `a` by a smoothing symbol, and
* a globally `C^∞` operator kernel `K` on `ℝⁿ × ℝⁿ`, vanishing where `‖x - y‖ ≤ r`,
such that `Op(a) u (x) = Op(A) u (x) + ∫ K(x, y) u(y) dy` for all compactly supported Schwartz
functions `u`. -/
theorem exists_hasProperSupport_amplitude_and_contDiff_kernel
    [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m) {r R : ℝ}
    (hR : 0 < R) (hrR : r < R) :
    ∃ (A : Amplitude n V W m) (hA : A.HasProperSupport)
      (K : CoordinateSpace n → CoordinateSpace n → V →L[ℂ] W),
      ContDiff ℝ ∞ (uncurry K) ∧ ((A.leftSymbol hA.inp) - a).IsSmoothing ∧
      tsupport (uncurry fun x y ξ ↦ A.coefficient (x, y, ξ)) ⊆
        {p : CoordinateSpace n × CoordinateSpace n | ‖p.1 - p.2‖ < R} ∧
      (∀ x y, ‖x - y‖ ≤ r → K x y = 0) ∧
      ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport (u : CoordinateSpace n → V) →
        ∀ x, quantizeSchwartzValue a.coefficient u x =
          quantizeAmplitudeValue A.coefficient u x + ∫ y, K x y (u y) := by
  set R' : ℝ := (max r 0 + R) / 2
  have hmax : max r 0 < R := max_lt hrR hR
  have hR' : 0 < R' := lt_of_le_of_lt (le_max_right r 0) (by dsimp [R']; linarith)
  have hrR' : r < R' := lt_of_le_of_lt (le_max_left r 0) (by dsimp [R']; linarith)
  have hR'R : R' < R := by dsimp [R']; linarith
  obtain ⟨χ, hχ, -, hχ_prop, hχ_diag, hχ_one, hχ_zero⟩ :=
    exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal (E := CoordinateSpace n) hR' hrR'
  have hχ_fiber : ∀ x, (fun y ↦ χ x y) =ᶠ[𝓝 x] 1 := fun x ↦
    ((continuous_const.prodMk continuous_id).tendsto x).eventually (hχ_diag x)
  have hsupp : tsupport (uncurry fun x y ξ ↦
        (a.localizeAmplitude χ hχ).coefficient (x, y, ξ)) ⊆
      {p : CoordinateSpace n × CoordinateSpace n | ‖p.1 - p.2‖ < R} := by
    have hcl : IsClosed {p : CoordinateSpace n × CoordinateSpace n | ‖p.1 - p.2‖ ≤ R'} :=
      isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const
    refine (closure_minimal (fun p hp ↦ ?_) hcl).trans (fun p hp ↦ lt_of_le_of_lt hp hR'R)
    by_contra hgt
    refine hp (funext fun ξ ↦ ?_)
    simp [uncurry_def, hχ_zero p.1 p.2 (not_le.1 hgt).le]
  exact ⟨a.localizeAmplitude χ hχ, a.hasProperSupport_localizeAmplitude hχ hχ_prop,
    a.localizedOffDiagonalKernel χ, a.contDiff_localizedOffDiagonalKernel hχ hχ_diag,
    a.isSmoothing_leftSymbol_localizeAmplitude_sub hχ hχ_prop.out hχ_fiber, hsupp,
    fun x y hxy ↦ by simp [hχ_one x y hxy], fun u hu x ↦
      a.quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel
        hχ hu x (hχ_fiber x)⟩

end Symbol

end TauCeti
