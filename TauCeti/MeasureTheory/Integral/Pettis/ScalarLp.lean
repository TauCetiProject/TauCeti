/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Function.Lp.ScalarEvaluation
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Pettis integrals of scalarly `Lᵖ` functions against `L^q` multipliers

Let `X` be a Banach space over `𝕜 = ℝ` or `ℂ`, let `1 < p ≤ ∞` and let `q < ∞` be its conjugate
exponent. If `f : S → X` is almost everywhere strongly measurable and every scalar test
`s ↦ x' (f s)`, `x' ∈ X*`, lies in `Lᵖ(μ)`, then for every scalar `φ ∈ L^q(μ)` the function
`φ • f` has a Pettis integral: there is a unique `x ∈ X` with

`x' x = ∫ s, φ s * x' (f s) ∂μ` for every `x' ∈ X*`.

The function `φ • f` need not be Bochner integrable, since `f` itself need not be in `Lᵖ(μ; X)`.
The vector `x` depends linearly and boundedly on `φ`, and this file bundles it as the continuous
linear operator `TauCeti.pettisIntegralCLM f hf hfp hq : Lp 𝕜 q μ →L[𝕜] X`. Its norm is at most
the norm of the scalar-evaluation operator `T_f = TauCeti.scalarEvalLp`, `x' ↦ [x' ∘ f]`.
Applied to the indicator of a measurable set of finite measure, it gives the Pettis integral of
`f` over that set (`TauCeti.exists_forall_strongDual_apply_eq_setIntegral`); on a finite measure
space every measurable set qualifies.

The hypothesis `q < ∞` cannot be dropped: for `p = 1` the unit vectors `n ↦ eₙ` of `c₀`, on `ℕ`
with counting measure, have integrable scalar tests, but the functional `x' ↦ ∑ₙ x' eₙ` given by
`φ = 1 ∈ L^∞` is the sequence `(1, 1, …)`, which does not lie in `c₀`.

## Main declarations

* `TauCeti.pettisIntegralCLM`: the operator `φ ↦ (P)∫ φ • f` from `L^q(μ)` to `X`.
* `TauCeti.strongDual_apply_pettisIntegralCLM`: its scalar pairing
  `x' (pettisIntegralCLM f hf hfp hq φ) = ∫ s, φ s * x' (f s) ∂μ`.
* `TauCeti.pettisIntegralCLM_apply_eq_iff`: this pairing characterizes its values.
* `TauCeti.norm_pettisIntegralCLM_le`: its norm is at most that of `TauCeti.scalarEvalLp`.
* `ContinuousLinearMap.pettisIntegralCLM_comp_comm`: bounded operators commute with it.
* `TauCeti.pettisIntegralCLM_apply_eq_integral`: it agrees with the Bochner integral of `φ • f`
  whenever the latter is integrable.
* `TauCeti.exists_forall_strongDual_apply_eq_setIntegral`: Pettis integrals of `f` over measurable
  sets of finite measure.

## Implementation notes

Pairing `φ` with `T_f` gives the functional `x' ↦ ∫ φ * x' ∘ f` on `X*`, an element of the bidual
`X**` depending continuously on `φ`. The canonical image of `X` in `X**` is closed because `X` is
complete. For the indicator `𝟙_A` of a set of finite measure, the truncations `𝟙_{A ∩ {‖f‖ ≤ n}}`
converge to `𝟙_A` in `L^q` because `q < ∞`, and on `A ∩ {‖f‖ ≤ n}` the function `f` is bounded, so
its Bochner integral represents the functional there. Closedness of the image then puts the
functional of every indicator, and by density of simple functions in `L^q` that of every `φ`, in
the image of `X`.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, Theorem 1.2.37 and Corollary 1.2.38.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal symmDiff

namespace TauCeti

variable {S 𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {mS : MeasurableSpace S} {μ : Measure S} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The functional `x' ↦ ∫ φ * x' ∘ f` on `X*`, as an element of the bidual depending continuously
on `φ ∈ L^q(μ)`: the pairing of `φ` with the scalar-evaluation operator of `f`. -/
private def dunfordLpCLM (f : S → X) (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) :
    Lp 𝕜 q μ →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X) :=
  ContinuousLinearMap.precomp 𝕜 (scalarEvalLp f (.id 𝕜 _) hfp) ∘L
    (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q p

private theorem dunfordLpCLM_apply_eq_lpPairing (f : S → X)
    (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) (φ : Lp 𝕜 q μ)
    (x' : StrongDual 𝕜 X) :
    dunfordLpCLM f hfp φ x' =
      (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q p φ (scalarEvalLp f (.id 𝕜 _) hfp x') := by
  simp only [dunfordLpCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.precomp_apply]

private theorem dunfordLpCLM_apply (f : S → X)
    (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) (φ : Lp 𝕜 q μ)
    (x' : StrongDual 𝕜 X) : dunfordLpCLM f hfp φ x' = ∫ s, φ s * x' (f s) ∂μ := by
  rw [dunfordLpCLM_apply_eq_lpPairing, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_scalarEvalLp (ι := .id 𝕜 _) (hf := hfp) x'] with s hs
  rw [ContinuousLinearMap.mul_apply', hs, ContinuousLinearMap.id_apply]

/-- The functional of a constant multiple of an indicator lies in the image of `X` when `f` is
bounded on the set. -/
private theorem dunfordLpCLM_indicatorConstLp_mem_of_bounded [CompleteSpace X] {f : S → X}
    (hf : AEStronglyMeasurable f μ) (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ)
    {A : Set S} (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (c : 𝕜) {M : ℝ}
    (hM : ∀ᵐ s ∂μ.restrict A, ‖f s‖ ≤ M) :
    dunfordLpCLM f hfp (indicatorConstLp q hA hμA c) ∈
      range (NormedSpace.inclusionInDoubleDual 𝕜 X) := by
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have hfA : IntegrableOn f A μ := Measure.integrableOn_of_bounded hμA hf hM
  refine ⟨c • ∫ s in A, f s ∂μ, ContinuousLinearMap.ext fun x' ↦ ?_⟩
  rw [NormedSpace.dual_def, dunfordLpCLM_apply, map_smul, ← x'.integral_comp_comm hfA,
    smul_eq_mul, integral_indicatorConstLp_mul]

/-- The functional of a constant multiple of the indicator of a set of finite measure lies in the
image of `X`. -/
private theorem dunfordLpCLM_indicatorConstLp_mem [CompleteSpace X] {f : S → X}
    (hf : AEStronglyMeasurable f μ) (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ)
    (hq : q ≠ ∞) {A : Set S} (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (c : 𝕜) :
    dunfordLpCLM f hfp (indicatorConstLp q hA hμA c) ∈
      range (NormedSpace.inclusionInDoubleDual 𝕜 X) := by
  set g := hf.mk f
  -- The truncations `A ∩ {‖g‖ ≤ n}` of `A`, on which `f` is essentially bounded by `n`.
  set B : ℕ → Set S := fun n ↦ A ∩ {s | ‖g s‖ ≤ n}
  have hBm (n : ℕ) : MeasurableSet (B n) :=
    hA.inter (measurableSet_le hf.stronglyMeasurable_mk.norm.measurable measurable_const)
  have hμB (n : ℕ) : μ (B n) ≠ ∞ := (measure_mono inter_subset_left).trans_lt hμA.lt_top |>.ne
  -- The measure of `A \ B n` tends to zero, so the indicators of `B n` converge in `L^q`.
  have hsymm : Tendsto (fun n ↦ μ (B n ∆ A)) atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ ↦ A \ B n := fun m n hmn ↦
      sdiff_subset_sdiff_right <| inter_subset_inter_right _ fun s (hs : ‖g s‖ ≤ m) ↦
        (hs.trans (Nat.cast_le.2 hmn) : ‖g s‖ ≤ n)
    have hempty : ⋂ n : ℕ, A \ B n = ∅ := by
      refine eq_empty_of_forall_notMem fun s hs ↦ ?_
      obtain ⟨n, hn⟩ := exists_nat_ge ‖g s‖
      exact (mem_iInter.1 hs n).2 ⟨(mem_iInter.1 hs n).1, hn⟩
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun n ↦ (hA.diff (hBm n)).nullMeasurableSet) hanti ⟨0, (measure_mono sdiff_subset).trans_lt
        hμA.lt_top |>.ne⟩
    rw [hempty, measure_empty] at h
    refine Tendsto.congr (fun n ↦ ?_) h
    rw [Function.comp_apply, symmDiff_of_le inter_subset_left]
  have hlim := tendsto_indicatorConstLp_set (c := c) (hs := hA) (hμs := hμA) (ht := hBm)
    (hμt := hμB) hq hsymm
  refine (NormedSpace.isClosed_range_inclusionInDoubleDual 𝕜 X).mem_of_tendsto
    ((dunfordLpCLM f hfp).continuous.tendsto _ |>.comp hlim) (Eventually.of_forall fun n ↦ ?_)
  refine dunfordLpCLM_indicatorConstLp_mem_of_bounded hf hfp (hBm n) (hμB n) c (M := n) ?_
  filter_upwards [ae_restrict_mem (hBm n), ae_restrict_of_ae hf.ae_eq_mk] with s hs hfs
  rw [hfs]
  exact hs.2

/-- The functional of every `φ ∈ L^q(μ)` lies in the image of `X`. -/
private theorem dunfordLpCLM_mem [CompleteSpace X] {f : S → X} (hf : AEStronglyMeasurable f μ)
    (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) (hq : q ≠ ∞) (φ : Lp 𝕜 q μ) :
    dunfordLpCLM f hfp φ ∈ range (NormedSpace.inclusionInDoubleDual 𝕜 X) := by
  refine Lp.induction hq
    (fun φ ↦ dunfordLpCLM f hfp φ ∈ range (NormedSpace.inclusionInDoubleDual 𝕜 X)) ?_ ?_ ?_ φ
  · intro c A hA hμA
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact dunfordLpCLM_indicatorConstLp_mem hf hfp hq hA hμA.ne c
  · rintro u v _ _ _ ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩
  · exact (NormedSpace.isClosed_range_inclusionInDoubleDual 𝕜 X).preimage
      (dunfordLpCLM f hfp).continuous

/-- Hölder's inequality for the bidual functional of `φ`: its norm is at most `‖T_f‖ ‖φ‖_q`. -/
private theorem norm_dunfordLpCLM_apply_le (f : S → X)
    (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) (φ : Lp 𝕜 q μ) :
    ‖dunfordLpCLM f hfp φ‖ ≤ ‖scalarEvalLp f (.id 𝕜 (StrongDual 𝕜 X)) hfp‖ * ‖φ‖ := by
  set T := scalarEvalLp f (.id 𝕜 (StrongDual 𝕜 X)) hfp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x' ↦ ?_
  rw [dunfordLpCLM_apply_eq_lpPairing]
  calc _ ≤ ‖ContinuousLinearMap.mul 𝕜 𝕜‖ * ‖φ‖ * ‖T x'‖ :=
        (ContinuousLinearMap.mul 𝕜 𝕜).norm_lpPairing_apply_apply_le φ (T x')
    _ ≤ 1 * ‖φ‖ * (‖T‖ * ‖x'‖) := by
      gcongr
      exacts [ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜, T.le_opNorm x']
    _ = ‖T‖ * ‖φ‖ * ‖x'‖ := by ring

/-- The Pettis integral `φ ↦ (P)∫ φ • f` as a linear map: the bidual functional of `φ`, pulled back
along the canonical embedding of `X` into its bidual. -/
private def pettisIntegralₗ [CompleteSpace X] (f : S → X) (hf : AEStronglyMeasurable f μ)
    (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) (hq : q ≠ ∞) :
    Lp 𝕜 q μ →ₗ[𝕜] X :=
  LinearMap.codRestrictOfInjective (dunfordLpCLM f hfp).toLinearMap
    (NormedSpace.inclusionInDoubleDual 𝕜 X).toLinearMap
    (NormedSpace.inclusionInDoubleDual_injective 𝕜 X) fun φ ↦
      LinearMap.mem_range.2 (dunfordLpCLM_mem hf hfp hq φ)

private theorem inclusionInDoubleDual_pettisIntegralₗ [CompleteSpace X] {f : S → X}
    (hf : AEStronglyMeasurable f μ) (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ)
    (hq : q ≠ ∞) (φ : Lp 𝕜 q μ) :
    NormedSpace.inclusionInDoubleDual 𝕜 X (pettisIntegralₗ f hf hfp hq φ) =
      dunfordLpCLM f hfp φ := by
  rw [pettisIntegralₗ, ← ContinuousLinearMap.coe_coe (NormedSpace.inclusionInDoubleDual 𝕜 X),
    LinearMap.codRestrictOfInjective_comp_apply, ContinuousLinearMap.coe_coe]

/-- The Pettis integral `φ ↦ (P)∫ φ • f` as a bounded operator from `L^q(μ)` to `X`, for an almost
everywhere strongly measurable `f` all of whose scalar tests `x' ∘ f` lie in `Lᵖ(μ)`, where `p` and
`q < ∞` are conjugate exponents. Its value at `φ` is the unique `x ∈ X` with
`x' x = ∫ s, φ s * x' (f s) ∂μ` for every `x' ∈ X*`
(`TauCeti.strongDual_apply_pettisIntegralCLM`, `TauCeti.pettisIntegralCLM_apply_eq_iff`). -/
def pettisIntegralCLM [CompleteSpace X] (f : S → X) (hf : AEStronglyMeasurable f μ)
    (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) (hq : q ≠ ∞) :
    Lp 𝕜 q μ →L[𝕜] X :=
  (pettisIntegralₗ f hf hfp hq).mkContinuous ‖scalarEvalLp f (.id 𝕜 (StrongDual 𝕜 X)) hfp‖
    fun φ ↦ NormedSpace.norm_le_dual_bound 𝕜 _ (by positivity) fun x' ↦ by
      rw [← NormedSpace.dual_def 𝕜 X, inclusionInDoubleDual_pettisIntegralₗ]
      exact ((dunfordLpCLM f hfp φ).le_opNorm x').trans
        (mul_le_mul_of_nonneg_right (norm_dunfordLpCLM_apply_le f hfp φ) (norm_nonneg x'))

variable [CompleteSpace X] {f : S → X} {hf : AEStronglyMeasurable f μ}
  {hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ} {hq : q ≠ ∞}

/-- The scalar pairing of the Pettis integral `(P)∫ φ • f`: its value at `x' ∈ X*` is
`∫ s, φ s * x' (f s) ∂μ`. -/
@[simp]
theorem strongDual_apply_pettisIntegralCLM (φ : Lp 𝕜 q μ) (x' : StrongDual 𝕜 X) :
    x' (pettisIntegralCLM f hf hfp hq φ) = ∫ s, φ s * x' (f s) ∂μ := by
  rw [← dunfordLpCLM_apply f hfp φ x', pettisIntegralCLM, LinearMap.mkContinuous_apply,
    ← inclusionInDoubleDual_pettisIntegralₗ hf hfp hq, NormedSpace.dual_def]

/-- The Pettis integral `(P)∫ φ • f` is the unique vector whose scalar pairings are the integrals
`∫ s, φ s * x' (f s) ∂μ`. -/
theorem pettisIntegralCLM_apply_eq_iff (φ : Lp 𝕜 q μ) (x : X) :
    pettisIntegralCLM f hf hfp hq φ = x ↔
      ∀ x' : StrongDual 𝕜 X, x' x = ∫ s, φ s * x' (f s) ∂μ := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)]
  refine forall_congr' fun x' ↦ ?_
  rw [strongDual_apply_pettisIntegralCLM, eq_comm]

/-- The Pettis integral operator has norm at most the norm of the scalar-evaluation operator
`x' ↦ [x' ∘ f]` from `X*` to `Lᵖ(μ)`. -/
theorem norm_pettisIntegralCLM_le :
    ‖pettisIntegralCLM f hf hfp hq‖ ≤ ‖scalarEvalLp f (.id 𝕜 (StrongDual 𝕜 X)) hfp‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- A bounded operator `T : X → Y` commutes with the Pettis integral: `(P)∫ φ • (T ∘ f)` is
`T ((P)∫ φ • f)`. -/
theorem _root_.ContinuousLinearMap.pettisIntegralCLM_comp_comm {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] [CompleteSpace Y] (T : X →L[𝕜] Y) (φ : Lp 𝕜 q μ) :
    pettisIntegralCLM (fun s ↦ T (f s)) (T.continuous.comp_aestronglyMeasurable hf)
        (fun y' ↦ hfp (y'.comp T)) hq φ =
      T (pettisIntegralCLM f hf hfp hq φ) := by
  refine (pettisIntegralCLM_apply_eq_iff φ _).2 fun y' ↦ ?_
  rw [← ContinuousLinearMap.comp_apply, strongDual_apply_pettisIntegralCLM]
  simp

/-- When `φ • f` is Bochner integrable, its Pettis integral is its Bochner integral. -/
theorem pettisIntegralCLM_apply_eq_integral [NormedSpace ℝ X] (φ : Lp 𝕜 q μ)
    (hφf : Integrable (fun s ↦ φ s • f s) μ) :
    pettisIntegralCLM f hf hfp hq φ = ∫ s, φ s • f s ∂μ := by
  refine (pettisIntegralCLM_apply_eq_iff φ _).2 fun x' ↦ ?_
  rw [← x'.integral_comp_comm hφf]
  simp

/-- An almost everywhere strongly measurable function all of whose scalar tests lie in `Lᵖ(μ)` for
some `1 < p ≤ ∞` has a Pettis integral over every measurable set of finite measure. -/
theorem exists_forall_strongDual_apply_eq_setIntegral (hf : AEStronglyMeasurable f μ)
    (hfp : ∀ x' : StrongDual 𝕜 X, MemLp (fun s ↦ x' (f s)) p μ) (hq : q ≠ ∞) {A : Set S}
    (hA : MeasurableSet A) (hμA : μ A ≠ ∞) :
    ∃ x : X, ∀ x' : StrongDual 𝕜 X, x' x = ∫ s in A, x' (f s) ∂μ := by
  refine ⟨pettisIntegralCLM f hf hfp hq (indicatorConstLp q hA hμA 1), fun x' ↦ ?_⟩
  rw [strongDual_apply_pettisIntegralCLM, integral_indicatorConstLp_mul, one_mul]

end TauCeti
