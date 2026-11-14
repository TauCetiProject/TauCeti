/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.ProperSupport
public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel

/-!
# Near-diagonal localization of pseudodifferential operators

For any symbol `a(x, ξ)` of order `m` on `ℝⁿ` and any smooth spatial cutoff `χ(x, y)` equal to `1`
on a neighborhood of every diagonal point `(x, x)`, splitting a compactly supported Schwartz input
`u` at each output point `x` into `y ↦ χ(x, y) u(y)` and `y ↦ (1 - χ(x, y)) u(y)` decomposes
`Op(a) u (x)` into the amplitude quantization of `χ(x, y) a(x, ξ)`
(`TauCeti.Symbol.localizeAmplitude`) plus the integral operator with globally `C^∞` residual kernel
`(1 - χ(x, y)) K_a(x, y)` (`TauCeti.Symbol.localizedOffDiagonalKernel`).

Choosing `χ` properly supported via
`TauCeti.exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal` exhibits every
pseudodifferential operator on `ℝⁿ` as a properly supported amplitude operator whose global left
symbol differs from `a` by a smoothing symbol
(`TauCeti.Symbol.isSmoothing_properLeftSymbol_localizeAmplitude_sub`) plus an integral operator with
a globally smooth kernel (`TauCeti.Symbol.exists_hasProperSupport_amplitude_and_contDiff_kernel`).

## Main declarations

* `TauCeti.Symbol.localizeAmplitude`, `TauCeti.Symbol.diagonal_localizeAmplitude`,
  `TauCeti.Symbol.leftTerm_localizeAmplitude_succ`,
  `TauCeti.Symbol.isSmoothing_properLeftSymbol_localizeAmplitude_sub`.
* `TauCeti.Symbol.localizedOffDiagonalKernel`, `TauCeti.Symbol.contDiff_localizedOffDiagonalKernel`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_quantizeSchwartzValue_properLeftSymbol_add_integral`,
  `TauCeti.Symbol.exists_hasProperSupport_amplitude_and_contDiff_kernel`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, pp. 68–72.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1–§2.
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
  (Amplitude.ofLeft a).smulSpatial χ hχ

@[simp]
theorem coefficient_localizeAmplitude (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ))
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (a.localizeAmplitude χ hχ).coefficient p = χ p.1 p.2.1 • a.coefficient (p.1, p.2.2) := by
  simp [localizeAmplitude]

theorem hasProperOutputSupport_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : HasProperOutputSupport χ) :
    (a.localizeAmplitude χ hχ).HasProperOutputSupport :=
  Amplitude.hasProperOutputSupport_smulSpatial_of_cutoff _ hχ hχ_out

theorem hasProperInputSupport_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_in : HasProperInputSupport χ) :
    (a.localizeAmplitude χ hχ).HasProperInputSupport :=
  Amplitude.hasProperInputSupport_smulSpatial_of_cutoff _ hχ hχ_in

theorem hasProperSupport_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_prop : HasProperSupport χ) :
    (a.localizeAmplitude χ hχ).HasProperSupport :=
  Amplitude.hasProperSupport_smulSpatial_of_cutoff _ hχ hχ_prop

/-- When `χ` equals `1` on a neighborhood of each diagonal point `(x, x)`, the diagonal restriction
of `a.localizeAmplitude χ hχ` recovers `a`. -/
theorem diagonal_localizeAmplitude (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_diag : ∀ x, uncurry χ =ᶠ[𝓝 (x, x)] 1) :
    (a.localizeAmplitude χ hχ).diagonal = a := by
  ext1
  funext ⟨x, ξ⟩
  simp [show χ x x = 1 from (hχ_diag x).eq_of_nhds]

/-- When `χ` equals `1` near the diagonal, every positive-index term `leftTerm (k + 1)` of
`a.localizeAmplitude χ hχ` vanishes identically because `a(x, ξ)` does not depend on `y` and all
`y`-derivatives of `χ` vanish on the diagonal. -/
theorem leftTerm_localizeAmplitude_succ (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_diag : ∀ x, uncurry χ =ᶠ[𝓝 (x, x)] 1) (k : ℕ) :
    (a.localizeAmplitude χ hχ).leftTerm (k + 1) = 0 := by
  ext1
  funext ⟨x, ξ⟩
  have hev : (a.localizeAmplitude χ hχ).coefficient =ᶠ[𝓝 (x, x, ξ)]
      (Amplitude.ofLeft a).coefficient := by
    have hcont : Continuous fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
        (p.1, p.2.1) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    filter_upwards [(hcont.tendsto (x, x, ξ)).eventually (hχ_diag x)] with p hp
    simp [show χ p.1 p.2.1 = 1 from hp]
  rw [Amplitude.coefficient_leftTerm, coefficient_zero, Pi.zero_apply]
  suffices hsum : ∑ w : Fin (k + 1) → Fin n, iteratedFDerivAlong ℝ
      (amplitudeDirections [] (List.ofFn w) (List.ofFn w))
      (a.localizeAmplitude χ hχ).coefficient (x, x, ξ) = 0 by
    rw [hsum, smul_zero]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [(hev.iteratedFDerivAlong (𝕜 := ℝ) _).eq_of_nhds]
  have hperm : (amplitudeDirections [] (List.ofFn w) (List.ofFn w)).Perm
      (amplitudeDirections [] (List.ofFn (Fin.tail w)) (List.ofFn w) ++
        [(0, EuclideanSpace.single (w 0) 1, 0)]) := by
    rw [List.ofFn_succ]
    simp only [amplitudeDirections_def, List.map_nil, List.nil_append, List.map_cons,
      List.cons_append]
    exact (List.perm_append_singleton _ _).symm
  rw [hperm.iteratedFDerivAlong_eq (Amplitude.ofLeft a).contDiff_coefficient (by simp),
    iteratedFDerivAlong_append, ← Amplitude.coefficient_spatialDerivSnd_eq_iteratedFDerivAlong,
    Amplitude.spatialDerivSnd_ofLeft, Amplitude.coefficient_zero, iteratedFDerivAlong_zero,
    Pi.zero_apply]

/-- **Symbol equivalence under near-diagonal localization.** When `χ` has proper output support and
equals `1` near the diagonal, the left symbol of `a.localizeAmplitude χ hχ` differs from `a` by a
smoothing symbol (`S^{-∞}`). -/
theorem isSmoothing_properLeftSymbol_localizeAmplitude_sub [CompleteSpace W] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : HasProperOutputSupport χ) (hχ_diag : ∀ x, uncurry χ =ᶠ[𝓝 (x, x)] 1) :
    (((a.localizeAmplitude χ hχ).properLeftSymbol
      (a.hasProperOutputSupport_localizeAmplitude hχ hχ_out)) - a).IsSmoothing := by
  have hA := a.hasProperOutputSupport_localizeAmplitude hχ hχ_out
  refine isSmoothing_iff_forall_nat.2 fun N ↦ ?_
  cases N with
  | zero =>
    exact ⟨inclusion (by simp) ((a.localizeAmplitude χ hχ).properLeftSymbol hA - a),
      coefficient_inclusion _ _⟩
  | succ N =>
    refine ⟨(a.localizeAmplitude χ hχ).properLeftRemainder hA (N + 1), funext fun ⟨x, ξ⟩ ↦ ?_⟩
    rw [Amplitude.coefficient_properLeftRemainder, Finset.sum_range_succ',
      Finset.sum_eq_zero fun k _ ↦ by
        rw [a.leftTerm_localizeAmplitude_succ hχ hχ_diag k, coefficient_zero],
      zero_add, coefficient_sub, Pi.sub_apply, Pi.sub_apply, Amplitude.leftTerm_zero,
      coefficient_inclusion, a.diagonal_localizeAmplitude hχ hχ_diag]

/-- The residual off-diagonal kernel `(1 - χ(x, y)) • K_a(x, y)` obtained after cutting out a
neighborhood of the diagonal by `χ`. -/
def localizedOffDiagonalKernel (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (x y : CoordinateSpace n) : V →L[ℂ] W :=
  (1 - χ x y) • a.offDiagonalKernel x y

@[simp]
theorem localizedOffDiagonalKernel_apply (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (x y : CoordinateSpace n) :
    a.localizedOffDiagonalKernel χ x y = (1 - χ x y) • a.offDiagonalKernel x y := (rfl)

theorem localizedOffDiagonalKernel_self (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    a.localizedOffDiagonalKernel χ x x = 0 := by
  simp

/-- **Global smoothness of the localized off-diagonal kernel.** Because `1 - χ` vanishes on a
neighborhood of every diagonal point `(x, x)` and `offDiagonalKernel a` is `C^∞` away from the
diagonal, `(x, y) ↦ (1 - χ(x, y)) • K_a(x, y)` is `C^∞` on the *entire* product `ℝⁿ × ℝⁿ`. -/
theorem contDiff_localizedOffDiagonalKernel (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_diag : ∀ x, uncurry χ =ᶠ[𝓝 (x, x)] 1) :
    ContDiff ℝ ∞ (uncurry (a.localizedOffDiagonalKernel χ)) := by
  refine contDiff_iff_contDiffAt.2 fun ⟨x, y⟩ ↦ ?_
  rcases eq_or_ne x y with rfl | hxy
  · refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [hχ_diag x] with ⟨x', y'⟩ h1
    simp [localizedOffDiagonalKernel, show χ x' y' = 1 from h1]
  · exact ((contDiff_const.sub hχ).contDiffAt (x := (x, y))).smul
      (a.contDiffOn_offDiagonalKernel.contDiffAt (isClosed_diagonal.isOpen_compl.mem_nhds hxy))

private theorem quantizeSchwartzValue_eq_integral_localizedOffDiagonalKernel_of_eq
    [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hχ_diag : uncurry χ =ᶠ[𝓝 (x, x)] 1) {u w : 𝓢(CoordinateSpace n, V)}
    (hs : HasCompactSupport fun y ↦ (1 - χ x y) • u y)
    (hw : ∀ y, w y = (1 - χ x y) • u y) :
    quantizeSchwartzValue a.coefficient w x =
      ∫ y, a.localizedOffDiagonalKernel χ x y (u y) := by
  have hx_notMem : x ∉ tsupport (w : CoordinateSpace n → V) := by
    refine notMem_tsupport_iff_eventuallyEq.2 ?_
    filter_upwards [((continuous_const.prodMk continuous_id).tendsto x).eventually hχ_diag]
      with y hy
    simp [hw, show χ x y = 1 from hy]
  rw [a.quantizeSchwartzValue_eq_integral_offDiagonalKernel ((funext hw).symm ▸ hs) hx_notMem]
  congr 1 with y
  rw [hw, ContinuousLinearMap.map_smul_of_tower, localizedOffDiagonalKernel_apply, smul_apply]

/-- **Near-diagonal decomposition of a pseudodifferential operator.** For any symbol `a`, any
smooth cutoff `χ` equal to `1` near the diagonal, and any compactly supported Schwartz input `u`,
`Op(a) u (x)` splits as the amplitude quantization of `χ(x, y) a(x, ξ)` plus the integral operator
with globally smooth kernel `(1 - χ(x, y)) K_a(x, y)`. -/
theorem quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel
    [CompleteSpace V] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_diag : ∀ x, uncurry χ =ᶠ[𝓝 (x, x)] 1) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) (x : CoordinateSpace n) :
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
    (hχ_diag x) hs₂ hw₂]
  congr 1
  rw [← quantizeAmplitudeValue_eq_quantizeSchwartzValue a.coefficient w₁ x,
    quantizeAmplitudeValue_def, quantizeAmplitudeValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  dsimp only
  rw [show (fun y ↦ a.coefficient (x, (2 * π) • ζ) (w₁ y)) =
      fun y ↦ (a.localizeAmplitude χ hχ).coefficient (x, y, (2 * π) • ζ) (u y) from
    funext fun y ↦ by
      rw [hw₁, ContinuousLinearMap.map_smul_of_tower, coefficient_localizeAmplitude, smul_apply]]

/-- When `χ` also has proper output support, `Op(a) u (x)` decomposes into the symbol quantization
of the left symbol of `a.localizeAmplitude χ hχ` (which agrees with `a` modulo `S^{-∞}`) plus the
smooth integral operator with kernel `a.localizedOffDiagonalKernel χ`. -/
theorem quantizeSchwartzValue_eq_quantizeSchwartzValue_properLeftSymbol_add_integral
    [CompleteSpace V] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : HasProperOutputSupport χ) (hχ_diag : ∀ x, uncurry χ =ᶠ[𝓝 (x, x)] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport (u : CoordinateSpace n → V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient u x =
      quantizeSchwartzValue
          ((a.localizeAmplitude χ hχ).properLeftSymbol
            (a.hasProperOutputSupport_localizeAmplitude hχ hχ_out)).coefficient u x +
        ∫ y, a.localizedOffDiagonalKernel χ x y (u y) := by
  rw [Amplitude.quantizeSchwartzValue_properLeftSymbol]
  exact a.quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel
    hχ hχ_diag hu x

/-- **Decomposition of a pseudodifferential operator into a properly supported part and a smooth
kernel.** Given `r < R` with `0 < R`, every symbol `a` of order `m` on `ℝⁿ` admits:
* a properly supported amplitude `A` of order `m`, supported in `{(x, y) | ‖x - y‖ < R}`, whose
  global left symbol differs from `a` by a smoothing symbol, and
* a globally `C^∞` operator kernel `K` on `ℝⁿ × ℝⁿ`, vanishing where `‖x - y‖ ≤ r`,
such that `Op(a) u (x) = Op(A) u (x) + ∫ K(x, y) u(y) dy` for all compactly supported Schwartz
functions `u`. -/
theorem exists_hasProperSupport_amplitude_and_contDiff_kernel
    [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m) {r R : ℝ}
    (hR : 0 < R) (hrR : r < R) :
    ∃ (A : Amplitude n V W m) (hA : A.HasProperSupport)
      (K : CoordinateSpace n → CoordinateSpace n → V →L[ℂ] W),
      ContDiff ℝ ∞ (uncurry K) ∧ ((A.properLeftSymbol hA.out) - a).IsSmoothing ∧
      (∀ x y ξ, R ≤ ‖x - y‖ → A.coefficient (x, y, ξ) = 0) ∧
      (∀ x y, ‖x - y‖ ≤ r → K x y = 0) ∧
      ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport (u : CoordinateSpace n → V) →
        ∀ x, quantizeSchwartzValue a.coefficient u x =
          quantizeAmplitudeValue A.coefficient u x + ∫ y, K x y (u y) := by
  obtain ⟨χ, hχ, -, hχ_prop, hχ_diag, hχ_one, hχ_zero⟩ :=
    exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal (E := CoordinateSpace n) hR hrR
  exact ⟨a.localizeAmplitude χ hχ, a.hasProperSupport_localizeAmplitude hχ hχ_prop,
    a.localizedOffDiagonalKernel χ, a.contDiff_localizedOffDiagonalKernel hχ hχ_diag,
    a.isSmoothing_properLeftSymbol_localizeAmplitude_sub hχ hχ_prop.out hχ_diag,
    fun x y ξ hxy ↦ by simp [hχ_zero x y hxy], fun x y hxy ↦ by simp [hχ_one x y hxy],
    fun u hu x ↦
      a.quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel
        hχ hχ_diag hu x⟩

end Symbol

end TauCeti
