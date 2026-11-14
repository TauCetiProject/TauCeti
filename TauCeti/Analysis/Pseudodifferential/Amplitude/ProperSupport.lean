/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Expansion
public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
public import TauCeti.Analysis.Pseudodifferential.ProperSupport
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Properly supported amplitudes and near-diagonal kernel localization

An amplitude `a(x, y, ξ)` of order `m` on `ℝⁿ` has *proper output support*
(`TauCeti.Amplitude.HasProperOutputSupport`) if the projection `(x, y) ↦ x` is proper on the
closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}` — equivalently, over every compact set of output
positions `x`, `a(x, y, ξ)` vanishes for `y` outside a compact set and all `ξ`. It has *proper
input support* (`TauCeti.Amplitude.HasProperInputSupport`) if `(x, y) ↦ y` is proper on that
support, and is *properly supported* (`TauCeti.Amplitude.HasProperSupport`) if both projections are
proper.

In `TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol` and `Amplitude.Expansion`, an
amplitude with global compact input support (`HasCompactInputSupport`) was reduced to a left symbol
`c(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πθ) dθ` with asymptotic expansion
`c ∼ ∑_k ((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)`. Because `c(x, ξ)` and all its mixed
derivatives near a compact set `K` of output positions depend only on `a(x, y, ξ)` for `x` near
`K`, multiplying `a` by a compactly supported output cutoff equal to `1` near `K` turns an
amplitude with proper output support into one with compact input support without changing `c` near
`K`. Every output-proper amplitude therefore reduces globally to a left symbol
(`TauCeti.Amplitude.properLeftSymbol`) with the same quantization on Schwartz functions and the
full asymptotic expansion (`TauCeti.Amplitude.isAsymptoticSum_properLeftSymbol`), while a properly
supported amplitude maps compactly supported Schwartz functions into compactly supported Schwartz
functions (`TauCeti.Amplitude.HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue`).

Conversely, for any symbol `a(x, ξ)` of order `m` and any smooth cutoff `χ(x, y)` equal to `1` near
the diagonal, splitting a compactly supported Schwartz input `u` at each output point `x` into
`y ↦ χ(x, y) u(y)` and `y ↦ (1 - χ(x, y)) u(y)` decomposes `Op(a)` into the amplitude operator of
`χ(x, y) a(x, ξ)` plus the smooth integral operator with kernel `(1 - χ(x, y)) K_a(x, y)`.
Choosing `χ` properly supported via
`TauCeti.exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal` exhibits every
pseudodifferential operator on `ℝⁿ` as a properly supported amplitude operator whose left symbol
agrees with `a` up to a smoothing symbol
(`TauCeti.Symbol.isSmoothing_properLeftSymbol_localizeAmplitude_sub`) plus an integral operator
with a globally `C^∞` kernel
(`TauCeti.Symbol.exists_hasProperSupport_amplitude_and_contDiff_kernel`).

## Main declarations

* `TauCeti.Amplitude.ofLeft`, `TauCeti.Amplitude.smulSpatial`: the left-quantization amplitude
  `(x, y, ξ) ↦ b(x, ξ)` of a symbol `b`, and multiplication of an amplitude by a smooth spatial
  cutoff `χ(x, y)`.
* `TauCeti.Amplitude.HasProperOutputSupport`, `TauCeti.Amplitude.HasProperInputSupport`,
  `TauCeti.Amplitude.HasProperSupport`: proper support conditions on amplitudes, with compact-slice
  characterizations and compact-support preservation
  `TauCeti.Amplitude.HasProperInputSupport.hasCompactSupport_quantizeAmplitudeValue`.
* `TauCeti.Amplitude.properLeftSymbol`, `TauCeti.Amplitude.properLeftRemainder`: the global left
  symbol and asymptotic remainder of an amplitude with proper output support, with
  `TauCeti.Amplitude.quantizeSchwartzValue_properLeftSymbol` and
  `TauCeti.Amplitude.isAsymptoticSum_properLeftSymbol`.
* `TauCeti.Symbol.localizeAmplitude`, `TauCeti.Symbol.localizedOffDiagonalKernel`: near-diagonal
  localization of a symbol by a smooth cutoff `χ`, with global smoothness
  `TauCeti.Symbol.contDiff_localizedOffDiagonalKernel`, smoothing symbol comparison
  `TauCeti.Symbol.isSmoothing_properLeftSymbol_localizeAmplitude_sub`, and operator decomposition
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

namespace Amplitude

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m m' : ℝ}

/-! ### Module structure and order inclusion -/

section Module

theorem coefficient_injective :
    Function.Injective
      (coefficient : Amplitude n V W m →
        CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) :=
  fun _ _ h ↦ Amplitude.ext h

instance : Zero (Amplitude n V W m) where
  zero :=
    { coefficient := 0
      contDiff_coefficient := contDiff_const
      exists_bound := fun _ _ _ _ _ ↦ ⟨0, le_rfl, fun _ _ _ _ ↦ by simp⟩ }

instance : Add (Amplitude n V W m) where
  add a b :=
    { coefficient := a.coefficient + b.coefficient
      contDiff_coefficient := a.contDiff_coefficient.add b.contDiff_coefficient
      exists_bound := fun K hK α γ β ↦ by
        obtain ⟨C, hC0, ha⟩ := a.exists_bound K hK α γ β
        obtain ⟨D, hD0, hb⟩ := b.exists_bound K hK α γ β
        refine ⟨C + D, add_nonneg hC0 hD0, fun x y hxy ξ ↦ ?_⟩
        rw [iteratedFDerivAlong_add a.contDiff_coefficient b.contDiff_coefficient _ (by simp),
          Pi.add_apply, add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha x y hxy ξ) (hb x y hxy ξ)) }

instance : SMul ℂ (Amplitude n V W m) where
  smul c a :=
    { coefficient := c • a.coefficient
      contDiff_coefficient := a.contDiff_coefficient.const_smul c
      exists_bound := fun K hK α γ β ↦ by
        obtain ⟨C, hC0, ha⟩ := a.exists_bound K hK α γ β
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC0, fun x y hxy ξ ↦ ?_⟩
        rw [iteratedFDerivAlong_const_smul a.contDiff_coefficient c _ (by simp),
          Pi.smul_apply, norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha x y hxy ξ) (norm_nonneg c) }

instance : Neg (Amplitude n V W m) where
  neg a :=
    { coefficient := -a.coefficient
      contDiff_coefficient := a.contDiff_coefficient.neg
      exists_bound := fun K hK α γ β ↦ by
        obtain ⟨C, hC0, ha⟩ := a.exists_bound K hK α γ β
        refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
        rw [iteratedFDerivAlong_neg, Pi.neg_apply, norm_neg]
        exact ha x y hxy ξ }

instance : Sub (Amplitude n V W m) where
  sub a b := a + -b

instance : SMul ℕ (Amplitude n V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (Amplitude n V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : Amplitude n V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : Amplitude n V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : Amplitude n V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : Amplitude n V W m) : (-a).coefficient = -a.coefficient := (rfl)

@[simp]
theorem coefficient_sub (a b : Amplitude n V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : Amplitude n V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : Amplitude n V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (Amplitude n V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k ↦ coefficient_nsmul k a) (fun a k ↦ coefficient_zsmul k a)

instance : Module ℂ (Amplitude n V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

/-- Order inclusion `A^m ⊆ A^{m'}` for `m ≤ m'`. -/
def inclusion (h : m ≤ m') (a : Amplitude n V W m) : Amplitude n V W m' where
  coefficient := a.coefficient
  contDiff_coefficient := a.contDiff_coefficient
  exists_bound K hK α γ β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α γ β
    refine ⟨C, hC0, fun x y hxy ξ ↦ (hC x y hxy ξ).trans ?_⟩
    gcongr
    nlinarith [sq_nonneg ‖ξ‖]

@[simp]
theorem coefficient_inclusion (h : m ≤ m') (a : Amplitude n V W m) :
    (inclusion h a).coefficient = a.coefficient := (rfl)

end Module

/-! ### Left quantization amplitudes and smooth spatial cutoffs -/

section SpatialSMul

private theorem exists_bound_ofLeft (b : Symbol n V W m)
    {K : Set (CoordinateSpace n × CoordinateSpace n)} (hK : IsCompact K)
    (α γ β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β)
          (fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
            b.coefficient (p.1, p.2.2)) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set L : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n →L[ℝ]
      CoordinateSpace n × CoordinateSpace n :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  have hL : ∀ p, HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ×
      CoordinateSpace n ↦ (p.1, p.2.2)) L p :=
    fun p ↦ hasFDerivAt_fst.prodMk (hasFDerivAt_snd.comp p hasFDerivAt_snd)
  obtain ⟨C, hC0, hC⟩ := b.exists_bound (Prod.fst '' K) (hK.image continuous_fst) α β
  refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
  rw [iteratedFDerivAlong_comp_of_hasFDerivAt hL b.contDiff_coefficient _ (by simp)]
  cases γ with
  | nil =>
    have hmap : (amplitudeDirections α [] β).map L = mixedDirections α β := by
      simp [amplitudeDirections_def, mixedDirections_def, L, Function.comp_def]
    rw [hmap, ← mixedDeriv_eq_iteratedFDerivAlong _ _ (b.contDiff_coefficient.of_le (by simp))]
    exact hC x ⟨(x, y), hxy, rfl⟩ ξ
  | cons j γ' =>
    have hperm : ((amplitudeDirections α (j :: γ') β).map L).Perm
        ((0 : CoordinateSpace n × CoordinateSpace n) ::
          (amplitudeDirections α γ' β).map L) := by
      simp only [amplitudeDirections_def, List.map_cons, List.append_assoc, List.map_append,
        List.cons_append]
      have hL0 : L (0, EuclideanSpace.single j 1, 0) = 0 := by simp [L]
      rw [hL0]
      exact List.perm_middle
    rw [hperm.iteratedFDerivAlong_eq b.contDiff_coefficient (by simp),
      iteratedFDerivAlong_cons_apply, map_zero, norm_zero]
    positivity

/-- The amplitude `a(x, y, ξ) = b(x, ξ)` of the **left quantization** of a symbol `b`. -/
def ofLeft (b : Symbol n V W m) : Amplitude n V W m where
  coefficient p := b.coefficient (p.1, p.2.2)
  contDiff_coefficient :=
    b.contDiff_coefficient.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  exists_bound _ hK α γ β := exists_bound_ofLeft b hK α γ β

@[simp]
theorem coefficient_ofLeft (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (ofLeft b).coefficient p = b.coefficient (p.1, p.2.2) := (rfl)

@[simp]
theorem diagonal_ofLeft (b : Symbol n V W m) : (ofLeft b).diagonal = b := by
  ext1
  funext ⟨x, ξ⟩
  simp

@[simp]
theorem spatialDerivSnd_ofLeft (j : Fin n) (b : Symbol n V W m) :
    spatialDerivSnd j (ofLeft b) = 0 := by
  refine Amplitude.ext (funext fun p ↦ ?_)
  have h : HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      b.coefficient (p.1, p.2.2))
      ((fderiv ℝ b.coefficient (p.1, p.2.2)).comp
        ((ContinuousLinearMap.fst ℝ _ _).prod
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))) p :=
    (b.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp p
      (hasFDerivAt_fst.prodMk (hasFDerivAt_snd.comp p hasFDerivAt_snd))
  rw [coefficient_spatialDerivSnd, coefficient_zero, Pi.zero_apply]
  dsimp only [ofLeft]
  rw [h.fderiv]
  simp [Prod.mk_zero_zero]

private def spatialSmulFun (χ : CoordinateSpace n → CoordinateSpace n → ℝ)
    (f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  χ p.1 p.2.1 • f p

private theorem hasFDerivAt_spatialSmulFun {χ : CoordinateSpace n → CoordinateSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ (uncurry χ)) {a : Amplitude n V W m}
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (spatialSmulFun χ a.coefficient)
      ((((fderiv ℝ (uncurry χ) (p.1, p.2.1)).comp
        ((ContinuousLinearMap.fst ℝ _ _).prod
          ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))).smulRight
            (a.coefficient p)) +
        χ p.1 p.2.1 • fderiv ℝ a.coefficient p) p := by
  have hπ : HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      (p.1, p.2.1))
      ((ContinuousLinearMap.fst ℝ _ _).prod
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) p :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_fst.comp p hasFDerivAt_snd)
  have hχ' := (hχ.differentiable (by simp) _).hasFDerivAt.comp p hπ
  have ha' := (a.contDiff_coefficient.differentiable (by simp) p).hasFDerivAt
  have hsmul : HasFDerivAt (spatialSmulFun χ a.coefficient) _ p := hχ'.smul ha'
  exact hsmul.congr_fderiv (add_comm _ _)

private theorem iteratedFDerivAlong_spatialSmulFun_freq
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (a : Amplitude n V W m) (j : Fin n) :
    iteratedFDerivAlong ℝ [(0, 0, EuclideanSpace.single j 1)] (spatialSmulFun χ a.coefficient) =
      spatialSmulFun χ (frequencyDeriv j a).coefficient := by
  funext p
  rw [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil,
    (hasFDerivAt_spatialSmulFun hχ p).fderiv]
  simp [spatialSmulFun, coefficient_frequencyDeriv, Prod.mk_zero_zero]

private theorem iteratedFDerivAlong_spatialSmulFun_fst
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (a : Amplitude n V W m) (j : Fin n) :
    iteratedFDerivAlong ℝ [(EuclideanSpace.single j 1, 0)] (spatialSmulFun χ a.coefficient) =
      spatialSmulFun (fun x y ↦ fderiv ℝ (uncurry χ) (x, y) (EuclideanSpace.single j 1, 0))
          a.coefficient +
        spatialSmulFun χ (spatialDerivFst j a).coefficient := by
  funext p
  rw [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil,
    (hasFDerivAt_spatialSmulFun hχ p).fderiv]
  simp [spatialSmulFun, coefficient_spatialDerivFst]

private theorem iteratedFDerivAlong_spatialSmulFun_snd
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (a : Amplitude n V W m) (j : Fin n) :
    iteratedFDerivAlong ℝ [(0, EuclideanSpace.single j 1, 0)] (spatialSmulFun χ a.coefficient) =
      spatialSmulFun (fun x y ↦ fderiv ℝ (uncurry χ) (x, y) (0, EuclideanSpace.single j 1))
          a.coefficient +
        spatialSmulFun χ (spatialDerivSnd j a).coefficient := by
  funext p
  rw [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil,
    (hasFDerivAt_spatialSmulFun hχ p).fderiv]
  simp [spatialSmulFun, coefficient_spatialDerivSnd]

private theorem contDiff_spatialSmulFun {χ : CoordinateSpace n → CoordinateSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ (uncurry χ)) (a : Amplitude n V W m) :
    ContDiff ℝ ∞ (spatialSmulFun χ a.coefficient) :=
  (hχ.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).smul a.contDiff_coefficient

private theorem exists_bound_spatialSmulFun_add_step
    {χ χ' : CoordinateSpace n → CoordinateSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ (uncurry χ)) (hχ' : ContDiff ℝ ∞ (uncurry χ'))
    (a da : Amplitude n V W m) {K : Set (CoordinateSpace n × CoordinateSpace n)}
    (α γ : List (Fin n)) (v : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n)
    (hv : iteratedFDerivAlong ℝ [v] (spatialSmulFun χ a.coefficient) =
      spatialSmulFun χ' a.coefficient + spatialSmulFun χ da.coefficient)
    (h₁ : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ [])
          (spatialSmulFun χ' a.coefficient) (x, y, ξ)‖ ≤
        C₁ * (1 + ‖ξ‖ ^ 2) ^ ((m - ([] : List (Fin n)).length) / 2))
    (h₂ : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ [])
          (spatialSmulFun χ da.coefficient) (x, y, ξ)‖ ≤
        C₂ * (1 + ‖ξ‖ ^ 2) ^ ((m - ([] : List (Fin n)).length) / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ [] ++ [v])
          (spatialSmulFun χ a.coefficient) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - ([] : List (Fin n)).length) / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x y hxy ξ ↦ ?_⟩
  rw [iteratedFDerivAlong_append, hv,
    iteratedFDerivAlong_add (contDiff_spatialSmulFun hχ' a)
      (contDiff_spatialSmulFun hχ da) _ (by simp),
    Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ x y hxy ξ) (hC₂ x y hxy ξ))

private theorem exists_bound_spatialSmulFun_nil {m : ℝ}
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (a : Amplitude n V W m) {K : Set (CoordinateSpace n × CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections [] [] [])
          (spatialSmulFun χ a.coefficient) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - ([] : List (Fin n)).length) / 2) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK [] [] []
  refine ⟨max B 0 * C, mul_nonneg (le_max_right B 0) hC0, fun x y hxy ξ ↦ ?_⟩
  simp only [amplitudeDirections_def, List.map_nil, List.nil_append, iteratedFDerivAlong_nil,
    spatialSmulFun, norm_smul, List.length_nil, Nat.cast_zero, sub_zero] at hC ⊢
  rw [mul_assoc]
  exact mul_le_mul ((hB (x, y) hxy).trans (le_max_left B 0)) (hC x y hxy ξ)
    (norm_nonneg _) (le_max_right B 0)

private theorem exists_bound_spatialSmulFun_freq_step {m : ℝ}
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (a : Amplitude n V W m) {K : Set (CoordinateSpace n × CoordinateSpace n)}
    (α γ β' : List (Fin n)) (j : Fin n)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β')
          (spatialSmulFun χ (frequencyDeriv j a).coefficient) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - β'.length) / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ (β' ++ [j]))
          (spatialSmulFun χ a.coefficient) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - (β' ++ [j]).length) / 2) := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
  have happ : amplitudeDirections α γ (β' ++ [j]) =
      amplitudeDirections α γ β' ++ [(0, 0, EuclideanSpace.single j 1)] := by
    simp [amplitudeDirections_def, List.append_assoc]
  have hexp : (m - 1 - β'.length) / 2 = (m - (β' ++ [j]).length) / 2 := by
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    ring
  rw [happ, iteratedFDerivAlong_append, iteratedFDerivAlong_spatialSmulFun_freq hχ a j, ← hexp]
  exact hC x y hxy ξ

private theorem exists_bound_spatialSmulFun :
    ∀ (D : ℕ) {m : ℝ} {χ : CoordinateSpace n → CoordinateSpace n → ℝ},
      ContDiff ℝ ∞ (uncurry χ) → ∀ (a : Amplitude n V W m)
        {K : Set (CoordinateSpace n × CoordinateSpace n)}, IsCompact K →
        ∀ (α γ β : List (Fin n)), α.length + γ.length + β.length = D →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
          ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β)
              (spatialSmulFun χ a.coefficient) (x, y, ξ)‖ ≤
            C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)
  | 0, _, χ, hχ, a, _, hK, α, γ, β, hD => by
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (α = [] ∧ γ = []) ∧ β = [] := by
      simpa [Nat.add_eq_zero_iff, List.length_eq_zero_iff] using hD
    exact exists_bound_spatialSmulFun_nil hχ a hK
  | D + 1, _, χ, hχ, a, _, hK, α, γ, β, hD => by
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' γ with rfl | ⟨γ', j, rfl⟩
      · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
        · simp at hD
        · have hlen : α'.length + ([] : List (Fin n)).length + ([] : List (Fin n)).length = D := by
            simpa using hD
          have hχ' : ContDiff ℝ ∞
              (uncurry fun x y ↦ fderiv ℝ (uncurry χ) (x, y) (EuclideanSpace.single j 1, 0)) :=
            (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
          have happ : amplitudeDirections (α' ++ [j]) [] [] =
              amplitudeDirections α' [] [] ++ [(EuclideanSpace.single j 1, 0)] := by
            simp [amplitudeDirections_def]
          rw [happ]
          exact exists_bound_spatialSmulFun_add_step hχ hχ' a (spatialDerivFst j a) α' [] _
            (iteratedFDerivAlong_spatialSmulFun_fst hχ a j)
            (exists_bound_spatialSmulFun D hχ' a hK α' [] [] hlen)
            (exists_bound_spatialSmulFun D hχ (spatialDerivFst j a) hK α' [] [] hlen)
      · have hlen : α.length + γ'.length + ([] : List (Fin n)).length = D := by
          simp only [List.length_append, List.length_singleton, List.length_nil] at hD ⊢
          omega
        have hχ' : ContDiff ℝ ∞
            (uncurry fun x y ↦ fderiv ℝ (uncurry χ) (x, y) (0, EuclideanSpace.single j 1)) :=
          (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
        have happ : amplitudeDirections α (γ' ++ [j]) [] =
            amplitudeDirections α γ' [] ++ [(0, EuclideanSpace.single j 1, 0)] := by
          simp [amplitudeDirections_def, List.append_assoc]
        rw [happ]
        exact exists_bound_spatialSmulFun_add_step hχ hχ' a (spatialDerivSnd j a) α γ' _
          (iteratedFDerivAlong_spatialSmulFun_snd hχ a j)
          (exists_bound_spatialSmulFun D hχ' a hK α γ' [] hlen)
          (exists_bound_spatialSmulFun D hχ (spatialDerivSnd j a) hK α γ' [] hlen)
    · have hlen : α.length + γ.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      exact exists_bound_spatialSmulFun_freq_step hχ a α γ β' j
        (exists_bound_spatialSmulFun D hχ (frequencyDeriv j a) hK α γ β' hlen)

/-- Multiply an amplitude `a(x, y, ξ)` by a smooth spatial cutoff `χ(x, y)`: the product
`(x, y, ξ) ↦ χ(x, y) • a(x, y, ξ)` is again an amplitude of order `m`. -/
def smulSpatial (a : Amplitude n V W m) (χ : CoordinateSpace n → CoordinateSpace n → ℝ)
    (hχ : ContDiff ℝ ∞ (uncurry χ)) : Amplitude n V W m where
  coefficient := spatialSmulFun χ a.coefficient
  contDiff_coefficient := contDiff_spatialSmulFun hχ a
  exists_bound _ hK α γ β :=
    exists_bound_spatialSmulFun (α.length + γ.length + β.length) hχ a hK α γ β rfl

@[simp]
theorem coefficient_smulSpatial (a : Amplitude n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ))
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (a.smulSpatial χ hχ).coefficient p = χ p.1 p.2.1 • a.coefficient p := (rfl)

theorem frequencyDeriv_smulSpatial (j : Fin n) (a : Amplitude n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    frequencyDeriv j (a.smulSpatial χ hχ) = (frequencyDeriv j a).smulSpatial χ hχ := by
  refine Amplitude.ext ?_
  rw [coefficient_frequencyDeriv_eq_iteratedFDerivAlong]
  exact iteratedFDerivAlong_spatialSmulFun_freq hχ a j

theorem spatialDerivFst_smulSpatial (j : Fin n) (a : Amplitude n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    spatialDerivFst j (a.smulSpatial χ hχ) =
      a.smulSpatial (fun x y ↦ fderiv ℝ (uncurry χ) (x, y) (EuclideanSpace.single j 1, 0))
        ((hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) +
      (spatialDerivFst j a).smulSpatial χ hχ := by
  refine Amplitude.ext ?_
  rw [coefficient_spatialDerivFst_eq_iteratedFDerivAlong, coefficient_add]
  exact iteratedFDerivAlong_spatialSmulFun_fst hχ a j

theorem spatialDerivSnd_smulSpatial (j : Fin n) (a : Amplitude n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    spatialDerivSnd j (a.smulSpatial χ hχ) =
      a.smulSpatial (fun x y ↦ fderiv ℝ (uncurry χ) (x, y) (0, EuclideanSpace.single j 1))
        ((hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) +
      (spatialDerivSnd j a).smulSpatial χ hχ := by
  refine Amplitude.ext ?_
  rw [coefficient_spatialDerivSnd_eq_iteratedFDerivAlong, coefficient_add]
  exact iteratedFDerivAlong_spatialSmulFun_snd hχ a j

end SpatialSMul

/-! ### Proper support of amplitudes -/

section ProperSupport

/-- An amplitude `a(x, y, ξ)` has **proper output support** if the first projection `(x, y) ↦ x`
is proper on the closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}`. Equivalently, over every compact
set of output positions `x`, `a(x, y, ξ)` vanishes for all `y` outside a compact set and all `ξ`
(`TauCeti.Amplitude.hasProperOutputSupport_iff`). -/
def HasProperOutputSupport (a : Amplitude n V W m) : Prop :=
  TauCeti.HasProperOutputSupport fun x y ξ ↦ a.coefficient (x, y, ξ)

/-- An amplitude `a(x, y, ξ)` has **proper input support** if the second projection `(x, y) ↦ y`
is proper on the closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}`. Equivalently, for `y` in any compact
set of input positions, `a(x, y, ξ)` vanishes for all `x` outside a compact set and all `ξ`
(`TauCeti.Amplitude.hasProperInputSupport_iff`). -/
def HasProperInputSupport (a : Amplitude n V W m) : Prop :=
  TauCeti.HasProperInputSupport fun x y ξ ↦ a.coefficient (x, y, ξ)

/-- An amplitude `a(x, y, ξ)` is **properly supported** if both spatial projections from the
closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}` to `ℝⁿ` are proper maps. -/
def HasProperSupport (a : Amplitude n V W m) : Prop :=
  TauCeti.HasProperSupport fun x y ξ ↦ a.coefficient (x, y, ξ)

theorem HasProperSupport.out {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperOutputSupport :=
  TauCeti.HasProperSupport.out ha

theorem HasProperSupport.inp {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperInputSupport :=
  TauCeti.HasProperSupport.inp ha

theorem hasProperSupport_iff {a : Amplitude n V W m} :
    a.HasProperSupport ↔ a.HasProperOutputSupport ∧ a.HasProperInputSupport :=
  TauCeti.hasProperSupport_iff

/-- Characterization of proper output support for amplitudes: over every compact set `K` of output
positions, `a(x, y, ξ)` vanishes for `y` outside some compact set `L` and all frequencies `ξ`. -/
theorem hasProperOutputSupport_iff {a : Amplitude n V W m} :
    a.HasProperOutputSupport ↔
      ∀ K : Set (CoordinateSpace n), IsCompact K →
        ∃ L : Set (CoordinateSpace n), IsCompact L ∧
          ∀ x ∈ K, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 := by
  simpa [HasProperOutputSupport, funext_iff] using
    (TauCeti.hasProperOutputSupport_iff (K := fun x y ξ ↦ a.coefficient (x, y, ξ)))

/-- Characterization of proper input support for amplitudes: over every compact set `L` of input
positions, `a(x, y, ξ)` vanishes for `x` outside some compact set `K` and all frequencies `ξ`. -/
theorem hasProperInputSupport_iff {a : Amplitude n V W m} :
    a.HasProperInputSupport ↔
      ∀ L : Set (CoordinateSpace n), IsCompact L →
        ∃ K : Set (CoordinateSpace n), IsCompact K ∧
          ∀ x ∉ K, ∀ y ∈ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 := by
  simpa [HasProperInputSupport, funext_iff] using
    (TauCeti.hasProperInputSupport_iff (K := fun x y ξ ↦ a.coefficient (x, y, ξ)))

/-- Global compact input support implies proper output support. -/
theorem HasCompactInputSupport.hasProperOutputSupport {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) : a.HasProperOutputSupport := by
  obtain ⟨L, hL, hLa⟩ := hasCompactInputSupport_iff.mp ha
  exact hasProperOutputSupport_iff.2 fun _ _ ↦ ⟨L, hL, fun x _ y hy ξ ↦ hLa x y hy ξ⟩

@[simp]
theorem hasProperOutputSupport_zero : (0 : Amplitude n V W m).HasProperOutputSupport :=
  TauCeti.hasProperOutputSupport_zero

@[simp]
theorem hasProperInputSupport_zero : (0 : Amplitude n V W m).HasProperInputSupport :=
  TauCeti.hasProperInputSupport_zero

@[simp]
theorem hasProperSupport_zero : (0 : Amplitude n V W m).HasProperSupport :=
  TauCeti.hasProperSupport_zero

theorem HasProperOutputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasProperOutputSupport) :
    (a + b).HasProperOutputSupport :=
  TauCeti.HasProperOutputSupport.add ha hb

theorem HasProperInputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (hb : b.HasProperInputSupport) :
    (a + b).HasProperInputSupport :=
  TauCeti.HasProperInputSupport.add ha hb

theorem HasProperSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperSupport) (hb : b.HasProperSupport) :
    (a + b).HasProperSupport :=
  TauCeti.HasProperSupport.add ha hb

theorem HasProperOutputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) :
    (-a).HasProperOutputSupport :=
  TauCeti.HasProperOutputSupport.neg ha

theorem HasProperInputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperInputSupport) :
    (-a).HasProperInputSupport :=
  TauCeti.HasProperInputSupport.neg ha

theorem HasProperSupport.neg {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    (-a).HasProperSupport :=
  TauCeti.HasProperSupport.neg ha

theorem HasProperOutputSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasProperOutputSupport) :
    (a - b).HasProperOutputSupport := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem HasProperInputSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (hb : b.HasProperInputSupport) :
    (a - b).HasProperInputSupport := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem HasProperSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperSupport) (hb : b.HasProperSupport) :
    (a - b).HasProperSupport := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem HasProperOutputSupport.smul {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (c : ℂ) : (c • a).HasProperOutputSupport :=
  TauCeti.HasProperOutputSupport.smul_left (fun _ _ ↦ c) ha

theorem HasProperInputSupport.smul {a : Amplitude n V W m} (ha : a.HasProperInputSupport)
    (c : ℂ) : (c • a).HasProperInputSupport :=
  TauCeti.HasProperInputSupport.smul_left (fun _ _ ↦ c) ha

theorem HasProperSupport.smul {a : Amplitude n V W m} (ha : a.HasProperSupport)
    (c : ℂ) : (c • a).HasProperSupport :=
  TauCeti.HasProperSupport.smul_left (fun _ _ ↦ c) ha

private theorem tsupport_iteratedFDerivAlong_slice_subset (a : Amplitude n V W m)
    (d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    tsupport (uncurry fun x y ξ ↦ iteratedFDerivAlong ℝ [d] a.coefficient (x, y, ξ)) ⊆
      tsupport (uncurry fun x y ξ ↦ a.coefficient (x, y, ξ)) := by
  set S := tsupport (uncurry fun x y ξ ↦ a.coefficient (x, y, ξ))
  refine closure_minimal (fun ⟨x, y⟩ hxy ↦ by_contra fun hnot ↦ mem_support.1 hxy ?_)
    (isClosed_tsupport _)
  funext ξ
  refine iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero ?_ [d]
  have hopen : IsOpen {p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n |
      (p.1, p.2.1) ∉ S} :=
    (isClosed_tsupport _).isOpen_compl.preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  filter_upwards [hopen.mem_nhds hnot] with p hp
  exact congrFun (image_eq_zero_of_notMem_tsupport hp) p.2.2

theorem HasProperOutputSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (spatialDerivFst j a).HasProperOutputSupport := by
  refine ha.of_tsupport_subset ?_
  rw [coefficient_spatialDerivFst_eq_iteratedFDerivAlong]
  exact tsupport_iteratedFDerivAlong_slice_subset a _

theorem HasProperOutputSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperOutputSupport := by
  refine ha.of_tsupport_subset ?_
  rw [coefficient_spatialDerivSnd_eq_iteratedFDerivAlong]
  exact tsupport_iteratedFDerivAlong_slice_subset a _

theorem HasProperOutputSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (frequencyDeriv j a).HasProperOutputSupport := by
  refine ha.of_tsupport_subset ?_
  rw [coefficient_frequencyDeriv_eq_iteratedFDerivAlong]
  exact tsupport_iteratedFDerivAlong_slice_subset a _

theorem HasProperInputSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (spatialDerivFst j a).HasProperInputSupport := by
  refine ha.of_tsupport_subset ?_
  rw [coefficient_spatialDerivFst_eq_iteratedFDerivAlong]
  exact tsupport_iteratedFDerivAlong_slice_subset a _

theorem HasProperInputSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperInputSupport := by
  refine ha.of_tsupport_subset ?_
  rw [coefficient_spatialDerivSnd_eq_iteratedFDerivAlong]
  exact tsupport_iteratedFDerivAlong_slice_subset a _

theorem HasProperInputSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (frequencyDeriv j a).HasProperInputSupport := by
  refine ha.of_tsupport_subset ?_
  rw [coefficient_frequencyDeriv_eq_iteratedFDerivAlong]
  exact tsupport_iteratedFDerivAlong_slice_subset a _

theorem HasProperSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivFst j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.spatialDerivFst j, ha.inp.spatialDerivFst j⟩

theorem HasProperSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.spatialDerivSnd j, ha.inp.spatialDerivSnd j⟩

theorem HasProperSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (frequencyDeriv j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.frequencyDeriv j, ha.inp.frequencyDeriv j⟩

/-- Multiplying any amplitude by a cutoff `χ` with proper output support yields an amplitude with
proper output support. -/
theorem hasProperOutputSupport_smulSpatial_of_cutoff (a : Amplitude n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : TauCeti.HasProperOutputSupport χ) :
    (a.smulSpatial χ hχ).HasProperOutputSupport :=
  hχ_out.smul_right _

/-- Multiplying any amplitude by a cutoff `χ` with proper input support yields an amplitude with
proper input support. -/
theorem hasProperInputSupport_smulSpatial_of_cutoff (a : Amplitude n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_in : TauCeti.HasProperInputSupport χ) :
    (a.smulSpatial χ hχ).HasProperInputSupport :=
  hχ_in.smul_right _

/-- Multiplying any amplitude by a properly supported cutoff `χ` yields a properly supported
amplitude. -/
theorem hasProperSupport_smulSpatial_of_cutoff (a : Amplitude n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_prop : TauCeti.HasProperSupport χ) :
    (a.smulSpatial χ hχ).HasProperSupport :=
  hχ_prop.smul_right _

theorem HasProperOutputSupport.smulSpatial {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    (a.smulSpatial χ hχ).HasProperOutputSupport :=
  ha.smul_left χ

theorem HasProperInputSupport.smulSpatial {a : Amplitude n V W m} (ha : a.HasProperInputSupport)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    (a.smulSpatial χ hχ).HasProperInputSupport :=
  ha.smul_left χ

theorem HasProperSupport.smulSpatial {a : Amplitude n V W m} (ha : a.HasProperSupport)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    (a.smulSpatial χ hχ).HasProperSupport :=
  ha.smul_left χ

/-- Cutting an amplitude with proper output support off in the output position by a compactly
supported smooth function `φ(x)` produces an amplitude with global compact input support. -/
theorem HasProperOutputSupport.hasCompactInputSupport_smulSpatial_fst
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ (uncurry fun x (_ : CoordinateSpace n) ↦ φ x))
    (hφ_supp : HasCompactSupport φ) :
    (a.smulSpatial (fun x _ ↦ φ x) hφ).HasCompactInputSupport := by
  obtain ⟨L, hL, hLa⟩ := (hasProperOutputSupport_iff.mp ha) (tsupport φ) hφ_supp
  refine hasCompactInputSupport_iff.mpr ⟨L, hL, fun x y hy ξ ↦ ?_⟩
  rw [coefficient_smulSpatial]
  by_cases hx : x ∈ tsupport φ
  · simp [hLa x hx y hy ξ]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Proper input support preserves compact support under amplitude quantization.** If `a` has
proper input support and `u : 𝓢(ℝⁿ, V)` has compact support, then `Op(a) u` has compact support. -/
theorem HasProperInputSupport.hasCompactSupport_quantizeAmplitudeValue
    {a : Amplitude n V W m} (ha : a.HasProperInputSupport) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    HasCompactSupport (quantizeAmplitudeValue a.coefficient u) := by
  obtain ⟨C, hC, hCa⟩ := (hasProperInputSupport_iff.mp ha) (tsupport (u : CoordinateSpace n → V)) hu
  refine HasCompactSupport.intro hC fun x hx ↦ ?_
  rw [quantizeAmplitudeValue_def]
  have hzero : ∀ ζ, (fun y ↦ a.coefficient (x, y, (2 * π) • ζ) (u y)) = 0 :=
    fun ζ ↦ funext fun y ↦ by
      by_cases hy : y ∈ tsupport (u : CoordinateSpace n → V)
      · simp [hCa x hx y hy ((2 * π) • ζ)]
      · simp [image_eq_zero_of_notMem_tsupport hy]
  simp [hzero, Real.fourier_eq]

end ProperSupport

/-! ### Global left symbol and asymptotic expansion for output-proper amplitudes -/

section ProperLeftSymbol

/-- The coefficient `c(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πθ) dθ` of the global left symbol of
an amplitude. -/
private def properLeftCoeff (a : Amplitude n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ∫ θ, (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (p.1, y, p.2 + (2 * π) • θ)) θ

/-- Near any compact set `K` of output positions, an amplitude `a` with proper output support
agrees on an open neighborhood `U` of `K` with an amplitude `b` of compact input support:
`properLeftCoeff a` and all `leftTerm a k` coincide with those of `b` on `U`. -/
private theorem HasProperOutputSupport.exists_local_leftSymbol {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ (U : Set (CoordinateSpace n)) (b : Amplitude n V W m) (hb : b.HasCompactInputSupport),
      IsOpen U ∧ K ⊆ U ∧
      (∀ x ∈ U, ∀ y ξ, b.coefficient (x, y, ξ) = a.coefficient (x, y, ξ)) ∧
      (∀ x ∈ U, ∀ ξ, properLeftCoeff a (x, ξ) = (b.leftSymbol hb).coefficient (x, ξ)) ∧
      ∀ k, ∀ x ∈ U, ∀ ξ, (b.leftTerm k).coefficient (x, ξ) = (a.leftTerm k).coefficient (x, ξ) := by
  obtain ⟨φ, hφ, -, hK_int, hφ_supp, -⟩ :=
    hK.exists_contDiff_cutoff isOpen_univ (subset_univ K)
  have hφ_uncurry : ContDiff ℝ ∞ (uncurry fun x (_ : CoordinateSpace n) ↦ φ x) :=
    hφ.comp contDiff_fst
  set b := a.smulSpatial (fun x _ ↦ φ x) hφ_uncurry with hb_def
  have hb : b.HasCompactInputSupport := ha.hasCompactInputSupport_smulSpatial_fst hφ_uncurry hφ_supp
  have hcoeff : ∀ x ∈ interior (φ ⁻¹' {1}), ∀ y ξ,
      b.coefficient (x, y, ξ) = a.coefficient (x, y, ξ) := fun x hx y ξ ↦ by
    have h1 : φ x = 1 := interior_subset hx
    rw [hb_def, coefficient_smulSpatial, h1, one_smul]
  refine ⟨interior (φ ⁻¹' {1}), b, hb, isOpen_interior, hK_int, hcoeff,
    fun x hx ξ ↦ ?_, fun k x hx ξ ↦ ?_⟩
  · simp only [properLeftCoeff, coefficient_leftSymbol]
    refine integral_congr_ae (.of_forall fun θ ↦ ?_)
    have hslice : (fun y ↦ a.coefficient (x, y, ξ + (2 * π) • θ)) =
        fun y ↦ b.coefficient (x, y, ξ + (2 * π) • θ) :=
      funext fun y ↦ (hcoeff x hx y _).symm
    dsimp only
    rw [hslice]
  · have hev : b.coefficient =ᶠ[𝓝 (x, x, ξ)] a.coefficient := by
      have hopen : IsOpen {p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n |
          p.1 ∈ interior (φ ⁻¹' {1})} :=
        isOpen_interior.preimage continuous_fst
      filter_upwards [hopen.mem_nhds hx] with p hp
      exact hcoeff p.1 hp p.2.1 p.2.2
    simp only [coefficient_leftTerm]
    congr 1
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    exact (hev.iteratedFDerivAlong (𝕜 := ℝ) _).eq_of_nhds

private theorem contDiff_properLeftCoeff {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) :
    ContDiff ℝ ∞ (properLeftCoeff a) := by
  refine contDiff_iff_contDiffAt.2 fun ⟨x₀, ξ₀⟩ ↦ ?_
  obtain ⟨U, b, hb, hU, hx₀U, -, heq, -⟩ :=
    ha.exists_local_leftSymbol (isCompact_singleton (x := x₀))
  refine (b.leftSymbol hb).contDiff_coefficient.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [(hU.prod isOpen_univ).mem_nhds ⟨hx₀U rfl, mem_univ ξ₀⟩] with ⟨x, ξ⟩ hx
  exact heq x hx.1 ξ

private theorem exists_bound_properLeftCoeff {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (K : Set (CoordinateSpace n)) (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ : CoordinateSpace n,
      ‖mixedDeriv α β (properLeftCoeff a) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨U, b, hb, hU, hKU, -, heq, -⟩ := ha.exists_local_leftSymbol hK
  obtain ⟨C, hC0, hC⟩ := (b.leftSymbol hb).exists_bound K hK α β
  refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
  have hcongr : mixedDeriv α β (properLeftCoeff a) x ξ =
      mixedDeriv α β (b.leftSymbol hb).coefficient x ξ := by
    refine mixedDeriv_congr_of_eventually ?_ α β ξ
    filter_upwards [hU.mem_nhds (hKU hx)] with x' hx' η
    exact heq x' hx' η
  rw [hcongr]
  exact hC x hx ξ

/-- **Global left symbol of an amplitude with proper output support.** If `a(x, y, ξ)` has proper
output support, `c(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πθ) dθ` defines a symbol of order `m`
on all of `ℝⁿ` without requiring global compact spatial support. -/
def properLeftSymbol (a : Amplitude n V W m) (ha : a.HasProperOutputSupport) : Symbol n V W m where
  coefficient := properLeftCoeff a
  contDiff_coefficient := contDiff_properLeftCoeff ha
  exists_bound := exists_bound_properLeftCoeff ha

@[simp]
theorem coefficient_properLeftSymbol (a : Amplitude n V W m) (ha : a.HasProperOutputSupport)
    (x ξ : CoordinateSpace n) :
    (a.properLeftSymbol ha).coefficient (x, ξ) =
      ∫ θ, (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (x, y, ξ + (2 * π) • θ)) θ := (rfl)

/-- When `a` has global compact input support, `properLeftSymbol` agrees with `leftSymbol`. -/
@[simp]
theorem properLeftSymbol_eq_leftSymbol {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) :
    a.properLeftSymbol ha.hasProperOutputSupport = a.leftSymbol ha := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_properLeftSymbol, coefficient_leftSymbol]

/-- **Reduction of an output-proper amplitude to its left symbol.** For any amplitude `a` with
proper output support and every Schwartz function `u`, `Op(a.properLeftSymbol ha) u = Op(a) u`. -/
theorem quantizeSchwartzValue_properLeftSymbol [CompleteSpace V]
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.properLeftSymbol ha).coefficient u x =
      quantizeAmplitudeValue a.coefficient u x := by
  by_cases hW : CompleteSpace W
  swap
  · simp [quantizeSchwartzValue_def, quantizeAmplitudeValue_def, integral_of_not_completeSpace hW]
  obtain ⟨U, b, hb, -, hxU, hcoeff, heq, -⟩ :=
    ha.exists_local_leftSymbol (isCompact_singleton (x := x))
  have hx : x ∈ U := hxU rfl
  have heq_x : ∀ ξ, (a.properLeftSymbol ha).coefficient (x, ξ) =
      (b.leftSymbol hb).coefficient (x, ξ) := heq x hx
  rw [quantizeSchwartzValue_congr_left heq_x, quantizeSchwartzValue_leftSymbol hb u x,
    quantizeAmplitudeValue_def, quantizeAmplitudeValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have hslice : (fun y ↦ b.coefficient (x, y, (2 * π) • ζ) (u y)) =
      fun y ↦ a.coefficient (x, y, (2 * π) • ζ) (u y) :=
    funext fun y ↦ by rw [hcoeff x hx y]
  dsimp only
  rw [hslice]

/-- **Proper output support implies smooth outputs.** For any amplitude `a` with proper output
support and any Schwartz function `u`, `Op(a) u` is `C^∞` on `ℝⁿ`. -/
theorem HasProperOutputSupport.contDiff_quantizeAmplitudeValue [CompleteSpace V]
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) (u : 𝓢(CoordinateSpace n, V)) :
    ContDiff ℝ ∞ (quantizeAmplitudeValue a.coefficient u) := by
  have heq : quantizeAmplitudeValue a.coefficient u =
      quantizeSchwartzValue (a.properLeftSymbol ha).coefficient u :=
    funext fun x ↦ (quantizeSchwartzValue_properLeftSymbol ha u x).symm
  rw [heq]
  exact (a.properLeftSymbol ha).contDiff_quantizeSchwartzValue u

/-- **Properly supported amplitudes preserve `C_c^∞` inside Schwartz space.** If `a` is properly
supported and `u : 𝓢(ℝⁿ, V)` has compact support, `Op(a) u` is the underlying function of a
compactly supported Schwartz map `v : 𝓢(ℝⁿ, W)`, so properly supported amplitude operators can be
composed directly without spatial cutoffs. -/
theorem HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue
    [CompleteSpace V] {a : Amplitude n V W m} (ha : a.HasProperSupport)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    ∃ v : 𝓢(CoordinateSpace n, W),
      (v : CoordinateSpace n → W) = quantizeAmplitudeValue a.coefficient u ∧
      HasCompactSupport (v : CoordinateSpace n → W) := by
  have hsupp := ha.inp.hasCompactSupport_quantizeAmplitudeValue hu
  have hsmooth := ha.out.contDiff_quantizeAmplitudeValue u
  let v := hsupp.toSchwartzMap hsmooth
  have hv : (v : CoordinateSpace n → W) = quantizeAmplitudeValue a.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun hsupp hsmooth)
  exact ⟨v, hv, hv.symm ▸ hsupp⟩

private theorem properLeftCoeff_eq_leftSymbol_of_eqOn {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasCompactInputSupport) {x : CoordinateSpace n}
    (h : ∀ y η, b.coefficient (x, y, η) = a.coefficient (x, y, η)) (ξ : CoordinateSpace n) :
    (b.leftSymbol hb).coefficient (x, ξ) = (a.properLeftSymbol ha).coefficient (x, ξ) := by
  rw [coefficient_leftSymbol, coefficient_properLeftSymbol]
  refine integral_congr_ae (.of_forall fun θ ↦ ?_)
  have hslice : (fun y ↦ b.coefficient (x, y, ξ + (2 * π) • θ)) =
      fun y ↦ a.coefficient (x, y, ξ + (2 * π) • θ) :=
    funext fun y ↦ h y _
  dsimp only
  rw [hslice]

/-- Position derivatives of the global left symbol: `∂_{x_j} c` is the left symbol of
`∂_{x_j} a + ∂_{y_j} a`. -/
theorem spatialDeriv_properLeftSymbol {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (j : Fin n) :
    Symbol.spatialDeriv j (a.properLeftSymbol ha) =
      (spatialDerivFst j a).properLeftSymbol (ha.spatialDerivFst j) +
        (spatialDerivSnd j a).properLeftSymbol (ha.spatialDerivSnd j) := by
  ext1
  funext ⟨x, ξ⟩
  obtain ⟨U, b, hb, hU, hxU, hcoeff, heq, -⟩ :=
    ha.exists_local_leftSymbol (isCompact_singleton (x := x))
  have hx : x ∈ U := hxU rfl
  have hev_sym : (fun x' ↦ (a.properLeftSymbol ha).coefficient (x', ξ)) =ᶠ[𝓝 x]
      fun x' ↦ (b.leftSymbol hb).coefficient (x', ξ) := by
    filter_upwards [hU.mem_nhds hx] with x' hx' using heq x' hx' ξ
  have hev_pt : ∀ y η, b.coefficient =ᶠ[𝓝 (x, y, η)] a.coefficient := fun y η ↦ by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hx] with p hp
    exact hcoeff p.1 hp p.2.1 p.2.2
  have hbfst : ∀ y η, (spatialDerivFst j b).coefficient (x, y, η) =
      (spatialDerivFst j a).coefficient (x, y, η) := fun y η ↦ by
    rw [coefficient_spatialDerivFst, coefficient_spatialDerivFst, (hev_pt y η).fderiv_eq]
  have hbsnd : ∀ y η, (spatialDerivSnd j b).coefficient (x, y, η) =
      (spatialDerivSnd j a).coefficient (x, y, η) := fun y η ↦ by
    rw [coefficient_spatialDerivSnd, coefficient_spatialDerivSnd, (hev_pt y η).fderiv_eq]
  rw [Symbol.coefficient_spatialDeriv, (hev_sym.coordinateDeriv [j]).eq_of_nhds,
    ← Symbol.coefficient_spatialDeriv, spatialDeriv_leftSymbol hb j, Symbol.coefficient_add,
    Symbol.coefficient_add, Pi.add_apply, Pi.add_apply,
    properLeftCoeff_eq_leftSymbol_of_eqOn (ha.spatialDerivFst j) (hb.spatialDerivFst j) hbfst,
    properLeftCoeff_eq_leftSymbol_of_eqOn (ha.spatialDerivSnd j) (hb.spatialDerivSnd j) hbsnd]

/-- Frequency derivatives of the global left symbol: `∂_{ξ_j} c` is the left symbol of
`∂_{ξ_j} a`. -/
theorem frequencyDeriv_properLeftSymbol {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (j : Fin n) :
    Symbol.frequencyDeriv j (a.properLeftSymbol ha) =
      (frequencyDeriv j a).properLeftSymbol (ha.frequencyDeriv j) := by
  ext1
  funext ⟨x, ξ⟩
  obtain ⟨U, b, hb, hU, hxU, hcoeff, heq, -⟩ :=
    ha.exists_local_leftSymbol (isCompact_singleton (x := x))
  have hx : x ∈ U := hxU rfl
  have hfreq : (fun η ↦ (a.properLeftSymbol ha).coefficient (x, η)) =
      fun η ↦ (b.leftSymbol hb).coefficient (x, η) := funext (heq x hx)
  have hbfreq : ∀ y η, (frequencyDeriv j b).coefficient (x, y, η) =
      (frequencyDeriv j a).coefficient (x, y, η) := fun y η ↦ by
    have hev : b.coefficient =ᶠ[𝓝 (x, y, η)] a.coefficient := by
      filter_upwards [(hU.preimage continuous_fst).mem_nhds hx] with p hp
      exact hcoeff p.1 hp p.2.1 p.2.2
    rw [coefficient_frequencyDeriv, coefficient_frequencyDeriv, hev.fderiv_eq]
  rw [Symbol.coefficient_frequencyDeriv, hfreq, ← Symbol.coefficient_frequencyDeriv,
    frequencyDeriv_leftSymbol hb j,
    properLeftCoeff_eq_leftSymbol_of_eqOn (ha.frequencyDeriv j) (hb.frequencyDeriv j) hbfreq]

private theorem exists_bound_properLeftRemainder [CompleteSpace W] {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (N : ℕ) (K : Set (CoordinateSpace n)) (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ : CoordinateSpace n,
      ‖mixedDeriv α β
          ((a.properLeftSymbol ha).coefficient -
            ∑ k ∈ Finset.range N, (a.leftTerm k).coefficient) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2) := by
  obtain ⟨U, b, hb, hU, hKU, -, heq, hterm⟩ := ha.exists_local_leftSymbol hK
  obtain ⟨C, hC0, hC⟩ := (b.leftRemainder hb N).exists_bound K hK α β
  refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
  have hcongr : mixedDeriv α β
      ((a.properLeftSymbol ha).coefficient -
        ∑ k ∈ Finset.range N, (a.leftTerm k).coefficient) x ξ =
      mixedDeriv α β (b.leftRemainder hb N).coefficient x ξ := by
    refine mixedDeriv_congr_of_eventually ?_ α β ξ
    filter_upwards [hU.mem_nhds (hKU hx)] with x' hx' η
    have heq' : (a.properLeftSymbol ha).coefficient (x', η) =
        (b.leftSymbol hb).coefficient (x', η) := heq x' hx' η
    simp only [coefficient_leftRemainder, Pi.sub_apply, Finset.sum_apply, heq']
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ (hterm k x' hx' η).symm
  rw [hcongr]
  exact hC x hx ξ

/-- **Remainder symbol of an output-proper amplitude.** For an amplitude `a` of order `m` with
proper output support and every `N : ℕ`, `c - ∑_{k < N} leftTerm a k` is a symbol of order
`m - N`. -/
def properLeftRemainder [CompleteSpace W] (a : Amplitude n V W m) (ha : a.HasProperOutputSupport)
    (N : ℕ) : Symbol n V W (m - N) where
  coefficient := (a.properLeftSymbol ha).coefficient -
    ∑ k ∈ Finset.range N, (a.leftTerm k).coefficient
  contDiff_coefficient := (a.properLeftSymbol ha).contDiff_coefficient.sub
    (Symbol.contDiff_sum_coefficient (Finset.range N) a.leftTerm)
  exists_bound := exists_bound_properLeftRemainder ha N

@[simp]
theorem coefficient_properLeftRemainder [CompleteSpace W] (a : Amplitude n V W m)
    (ha : a.HasProperOutputSupport) (N : ℕ) :
    (a.properLeftRemainder ha N).coefficient =
      (a.properLeftSymbol ha).coefficient - ∑ k ∈ Finset.range N, (a.leftTerm k).coefficient :=
  (rfl)

/-- **Asymptotic expansion of the left symbol of an output-proper amplitude.** For every `N : ℕ`,
`a.properLeftSymbol ha = ∑_{k < N} leftTerm a k + properLeftRemainder a ha N`. -/
theorem properLeftSymbol_eq_sum_leftTerm_add_properLeftRemainder [CompleteSpace W]
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) (N : ℕ) :
    a.properLeftSymbol ha =
      ∑ k ∈ Finset.range N, Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.leftTerm k) +
        Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.properLeftRemainder ha N) := by
  ext1
  simp

/-- The global left symbol of an amplitude `a` with proper output support agrees with its diagonal
restriction `a(x, x, ξ)` up to a symbol of order `m - 1`. -/
theorem properLeftSymbol_eq_diagonal_add_properLeftRemainder_one [CompleteSpace W]
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) :
    a.properLeftSymbol ha =
      a.diagonal + Symbol.inclusion (by simp) (a.properLeftRemainder ha 1) := by
  ext1
  funext p
  simp [leftTerm_zero]

/-- The global left symbol of an amplitude `a` with proper output support is an asymptotic sum of
the terms `leftTerm a k` of order `m - k`. -/
theorem isAsymptoticSum_properLeftSymbol [CompleteSpace W] {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) :
    (Symbol.inclusion (by simp) (a.properLeftSymbol ha) :
      Symbol n V W (m - ((0 : ℕ) : ℝ))).IsAsymptoticSum a.leftTerm :=
  Symbol.isAsymptoticSum_iff.2 fun N ↦ ⟨a.properLeftRemainder ha N, by simp⟩

end ProperLeftSymbol

end Amplitude

/-! ### Near-diagonal localization of pseudodifferential operators -/

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
    (a.localizeAmplitude χ hχ).coefficient p = χ p.1 p.2.1 • a.coefficient (p.1, p.2.2) :=
  (rfl)

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
  have h1 : χ x x = 1 := (hχ_diag x).eq_of_nhds
  simp [h1]

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
    have hp1 : χ p.1 p.2.1 = 1 := hp
    simp [hp1]
  rw [Amplitude.coefficient_leftTerm, coefficient_zero, Pi.zero_apply]
  suffices hsum : ∑ w : Fin (k + 1) → Fin n, iteratedFDerivAlong ℝ
      (amplitudeDirections [] (List.ofFn w) (List.ofFn w))
      (a.localizeAmplitude χ hχ).coefficient (x, x, ξ) = 0 by
    rw [hsum, smul_zero]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [(hev.iteratedFDerivAlong (𝕜 := ℝ) _).eq_of_nhds]
  set j := w 0
  have hperm : (amplitudeDirections [] (List.ofFn w) (List.ofFn w)).Perm
      (amplitudeDirections [] (List.ofFn (Fin.tail w)) (List.ofFn w) ++
        [(0, EuclideanSpace.single j 1, 0)]) := by
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
  rw [isSmoothing_iff_forall_nat]
  intro N
  cases N with
  | zero =>
    exact ⟨inclusion (by simp) ((a.localizeAmplitude χ hχ).properLeftSymbol hA - a),
      coefficient_inclusion _ _⟩
  | succ N =>
    refine ⟨(a.localizeAmplitude χ hχ).properLeftRemainder hA (N + 1), ?_⟩
    funext ⟨x, ξ⟩
    rw [Amplitude.coefficient_properLeftRemainder, Finset.sum_range_succ']
    have hsum0 : ∑ k ∈ Finset.range N,
        ((a.localizeAmplitude χ hχ).leftTerm (k + 1)).coefficient = 0 :=
      Finset.sum_eq_zero fun k _ ↦ by
        rw [a.leftTerm_localizeAmplitude_succ hχ hχ_diag k, coefficient_zero]
    have h0 : ((a.localizeAmplitude χ hχ).leftTerm 0).coefficient (x, ξ) =
        a.coefficient (x, ξ) := by
      rw [Amplitude.leftTerm_zero, coefficient_inclusion,
        a.diagonal_localizeAmplitude hχ hχ_diag]
    rw [hsum0, zero_add, coefficient_sub, Pi.sub_apply, Pi.sub_apply, h0]

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
    have hχ1 : χ x' y' = 1 := h1
    simp [localizedOffDiagonalKernel, hχ1]
  · have hopen : IsOpen {p : CoordinateSpace n × CoordinateSpace n | p.1 ≠ p.2} :=
      isClosed_diagonal.isOpen_compl
    have hoff : ContDiffAt ℝ ∞ (uncurry a.offDiagonalKernel) (x, y) :=
      a.contDiffOn_offDiagonalKernel.contDiffAt (hopen.mem_nhds hxy)
    exact ((contDiff_const.sub hχ).contDiffAt (x := (x, y))).smul hoff

private theorem quantizeSchwartzValue_eq_integral_localizedOffDiagonalKernel_of_eq
    [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hχ_diag : uncurry χ =ᶠ[𝓝 (x, x)] 1) {u w : 𝓢(CoordinateSpace n, V)}
    (hs : HasCompactSupport fun y ↦ (1 - χ x y) • u y)
    (hw : ∀ y, w y = (1 - χ x y) • u y) :
    quantizeSchwartzValue a.coefficient w x =
      ∫ y, a.localizedOffDiagonalKernel χ x y (u y) := by
  have hw_supp : HasCompactSupport (w : CoordinateSpace n → V) := (funext hw).symm ▸ hs
  have hx_notMem : x ∉ tsupport (w : CoordinateSpace n → V) := by
    refine notMem_tsupport_iff_eventuallyEq.2 ?_
    have hcont : Continuous fun y : CoordinateSpace n ↦ (x, y) :=
      continuous_const.prodMk continuous_id
    filter_upwards [(hcont.tendsto x).eventually hχ_diag] with y hy
    have hy1 : χ x y = 1 := hy
    simp [hw, hy1]
  rw [a.quantizeSchwartzValue_eq_integral_offDiagonalKernel hw_supp hx_notMem]
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
  by_cases hW : CompleteSpace W
  swap
  · simp [quantizeSchwartzValue_def, quantizeAmplitudeValue_def, integral_of_not_completeSpace hW]
  have hχx : ContDiff ℝ ∞ fun y ↦ χ x y := hχ.comp (contDiff_const.prodMk contDiff_id)
  have hf₁ : ContDiff ℝ ∞ fun y ↦ χ x y • u y := hχx.smul (u.smooth ⊤)
  have hf₂ : ContDiff ℝ ∞ fun y ↦ (1 - χ x y) • u y :=
    (contDiff_const.sub hχx).smul (u.smooth ⊤)
  have hs₁ : HasCompactSupport fun y ↦ χ x y • u y := hu.smul_left
  have hs₂ : HasCompactSupport fun y ↦ (1 - χ x y) • u y := hu.smul_left
  set w₁ := hs₁.toSchwartzMap hf₁
  set w₂ := hs₂.toSchwartzMap hf₂
  have hw₁ : ∀ y, w₁ y = χ x y • u y := HasCompactSupport.toSchwartzMap_toFun hs₁ hf₁
  have hw₂ : ∀ y, w₂ y = (1 - χ x y) • u y := HasCompactSupport.toSchwartzMap_toFun hs₂ hf₂
  have hu_split : u = w₁ + w₂ := by
    ext y
    rw [add_apply, hw₁, hw₂, ← add_smul, add_sub_cancel, one_smul]
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  conv_lhs => rw [hu_split]
  rw [quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable
    hC w₁ w₂, a.quantizeSchwartzValue_eq_integral_localizedOffDiagonalKernel_of_eq
    (hχ_diag x) hs₂ hw₂]
  congr 1
  rw [← quantizeAmplitudeValue_eq_quantizeSchwartzValue a.coefficient w₁ x,
    quantizeAmplitudeValue_def, quantizeAmplitudeValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have hslice : (fun y ↦ a.coefficient (x, (2 * π) • ζ) (w₁ y)) =
      fun y ↦ (a.localizeAmplitude χ hχ).coefficient (x, y, (2 * π) • ζ) (u y) :=
    funext fun y ↦ by
      rw [hw₁, ContinuousLinearMap.map_smul_of_tower, coefficient_localizeAmplitude, smul_apply]
  dsimp only
  rw [hslice]

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
      ContDiff ℝ ∞ (uncurry K) ∧
      ((A.properLeftSymbol hA.out) - a).IsSmoothing ∧
      (∀ x y ξ, R ≤ ‖x - y‖ → A.coefficient (x, y, ξ) = 0) ∧
      (∀ x y, ‖x - y‖ ≤ r → K x y = 0) ∧
      ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport (u : CoordinateSpace n → V) →
        ∀ x, quantizeSchwartzValue a.coefficient u x =
          quantizeAmplitudeValue A.coefficient u x + ∫ y, K x y (u y) := by
  obtain ⟨χ, hχ, -, hχ_prop, hχ_diag, hχ_one, hχ_zero⟩ :=
    exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal (E := CoordinateSpace n) hR hrR
  refine ⟨a.localizeAmplitude χ hχ, a.hasProperSupport_localizeAmplitude hχ hχ_prop,
    a.localizedOffDiagonalKernel χ,
    a.contDiff_localizedOffDiagonalKernel hχ hχ_diag,
    a.isSmoothing_properLeftSymbol_localizeAmplitude_sub hχ hχ_prop.out hχ_diag,
    fun x y ξ hxy ↦ by simp [hχ_zero x y hxy],
    fun x y hxy ↦ by simp [hχ_one x y hxy],
    fun u hu x ↦
      a.quantizeSchwartzValue_eq_quantizeAmplitudeValue_add_integral_localizedOffDiagonalKernel
        hχ hχ_diag hu x⟩

end Symbol

end TauCeti
