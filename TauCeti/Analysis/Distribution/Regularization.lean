/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.TestFunction.Translation
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.MeasureTheory.Function.SimpleFunc.Dense
import TauCeti.MeasureTheory.Function.SimpleFunc.RiemannSum
import TauCeti.Topology.Algebra.Monoid
import TauCeti.Topology.Algebra.Support

/-!
# Regularization of distributions

For a distribution `T` on an open set `Ω` and a test function `ρ`, the **regularization**
`T.translatePairing ρ` is the function `x ↦ T (ρ (· - x))`, defined at every `x` for which the
translate `ρ (· - x)` is supported in `Ω`; it is the convolution of `T` with the reflection
`ρ (- ·)` of `ρ`. This file shows that it is smooth on the open set of such `x`, with derivatives
given by the distributional derivatives of `T`:

`∂_v (x ↦ T (ρ (· - x))) = x ↦ (∂_v T) (ρ (· - x))`.

Consequently, if every distributional derivative of `T` vanishes, the regularization is constant
on each preconnected open set of admissible translations. This is the regularization step in the
classical proof that a distribution whose derivatives all vanish on a connected open set is a
constant multiple of Lebesgue measure. The admissible translations form an open set by
`IsCompact.isOpen_setOf_mapsTo_add`, since `ρ` has compact support.

Differentiability rests on the finite order of a distribution on each compact set,
`Distribution.exists_norm_apply_le` from `TauCeti.Analysis.Distribution.Order`: the first-order
Taylor remainder of `x ↦ ρ (· - x)` is supported in a fixed compact set and all of its
derivatives are `o(‖h‖)` uniformly, so its image under `T` is `o(‖h‖)` as well.

The regularization also computes `T` on convolutions: for a Haar measure `μ` and a compactly
supported continuous `φ`, `T` maps the convolution `x ↦ ∫ y, φ y * ρ (x - y) ∂μ` to
`∫ y, φ y • T (ρ (· - y)) ∂μ`. This interchanges `T` with an integral of translates of `ρ`. Both
sides are compared with Riemann sums over a common partition of the support of `φ`, given by the
fibres of a simple function close to the identity; on the test-function side the finite order of
`T` controls the error.

## Main declarations

* `Distribution.translatePairing`: the regularization `x ↦ T (ρ (· - x))`.
* `Distribution.fderiv_translatePairing_apply`: the derivative identity.
* `Distribution.contDiffOn_translatePairing`: the regularization is smooth.
* `Distribution.translatePairing_eq_of_lineDerivOp_eq_zero`: if all derivatives of `T` vanish,
  the regularization is constant on preconnected open sets of admissible translations.
* `Distribution.apply_eq_integral_smul_translatePairing`: `T` applied to a convolution is the
  integral against the regularization.

## References

* [L. Hörmander, *The Analysis of Linear Partial Differential Operators I*][hormander2003],
  §2.1 for the local order estimate and §4.1 for the smoothness of regularizations, their
  derivatives, and their pairing with test functions.
-/

public section

noncomputable section

open Set Filter Topology TopologicalSpace TestFunction LineDeriv Metric MeasureTheory
open scoped Distributions ContDiff Convolution Pointwise

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω V : Opens E}

/-- The translate `ρ (· - x)` of a test function, as a test function on `Ω` when it is supported
there. -/
private def translateOfMapsTo (ρ : 𝓓(V, ℝ)) {x : E} (h : MapsTo (· + x) (tsupport ρ) Ω) :
    𝓓(Ω, ℝ) :=
  TauCeti.translateTestFunction
    (V := ⟨(· + x) ⁻¹' Ω, Ω.isOpen.preimage (continuous_add_const x)⟩) (mapsTo_preimage _ _)
    ⟨ρ, ρ.contDiff, ρ.hasCompactSupport, h⟩

private theorem translateOfMapsTo_apply (ρ : 𝓓(V, ℝ)) {x : E}
    (h : MapsTo (· + x) (tsupport ρ) Ω) (y : E) : translateOfMapsTo ρ h y = ρ (y - x) := by
  rw [translateOfMapsTo, TauCeti.translateTestFunction_apply]
  exact congrFun coe_mk (y - x)

/-- The regularization of a distribution `T` by a test function `ρ`: the function
`x ↦ T (ρ (· - x))`. Its value at `x` is `T` applied to the translate of `ρ` by `x` when this
translate is supported in `Ω`, and `0` otherwise. It is the convolution of `T` with the
reflection `ρ (- ·)` of `ρ`. -/
def translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) (x : E) : F :=
  open Classical in
  if h : MapsTo (· + x) (tsupport ρ) Ω then T (translateOfMapsTo ρ h) else 0

/-- The regularization at `x` is `T` applied to any test function on `Ω` which is the translate
of `ρ` by `x`. -/
theorem translatePairing_eq (T : 𝓓'(Ω, F)) {ρ : 𝓓(V, ℝ)} {x : E} {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = ρ (y - x)) : T.translatePairing ρ x = T φ := by
  have h : MapsTo (· + x) (tsupport ρ) Ω := by
    intro z hz
    apply φ.tsupport_subset
    rw [show (φ : E → ℝ) = fun y => ρ (y - x) from funext hφ, TauCeti.tsupport_comp_sub_right]
    simpa using hz
  simp only [translatePairing, h, ↓reduceDIte]
  congr 1
  ext y
  rw [translateOfMapsTo_apply, hφ]

/-- The regularization vanishes where the translate of `ρ` is not supported in `Ω`. -/
theorem translatePairing_eq_zero_of_not_mapsTo (T : 𝓓'(Ω, F)) {ρ : 𝓓(V, ℝ)} {x : E}
    (h : ¬MapsTo (· + x) (tsupport ρ) Ω) : T.translatePairing ρ x = 0 := by
  simp [translatePairing, h]

/-- The regularization of the zero distribution vanishes. -/
@[simp]
theorem translatePairing_zero (ρ : 𝓓(V, ℝ)) :
    (0 : 𝓓'(Ω, F)).translatePairing ρ = 0 := by
  ext x
  simp [translatePairing]

/-- Regularization is additive in the distribution. -/
@[simp]
theorem translatePairing_add (T S : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) :
    (T + S).translatePairing ρ = T.translatePairing ρ + S.translatePairing ρ := by
  ext x
  by_cases h : MapsTo (· + x) (tsupport ρ) Ω <;> simp [translatePairing, h]

/-- Regularization commutes with scalar multiplication of the distribution. -/
@[simp]
theorem translatePairing_smul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass ℝ M F]
    [ContinuousConstSMul M F] (c : M) (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) :
    (c • T).translatePairing ρ = c • T.translatePairing ρ := by
  ext x
  by_cases h : MapsTo (· + x) (tsupport ρ) Ω <;> simp [translatePairing, h]

/-- The translate `ρ (· - x)` has the translated topological support. -/
private theorem tsupport_translateOfMapsTo (ρ : 𝓓(V, ℝ)) {x : E}
    (h : MapsTo (· + x) (tsupport ρ) Ω) :
    tsupport (translateOfMapsTo ρ h) = (· - x) ⁻¹' tsupport ρ := by
  rw [show (translateOfMapsTo ρ h : E → ℝ) = fun y => ρ (y - x) from
    funext (translateOfMapsTo_apply ρ h), TauCeti.tsupport_comp_sub_right]

/-- Around an admissible translation `x`, a closed thickening of the support of `ρ (· - x)`
still lies in `Ω`, so all nearby translations are admissible. -/
private theorem exists_cthickening_tsupport_translateOfMapsTo_subset (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) :
    ∃ δ > 0, cthickening δ (tsupport (translateOfMapsTo ρ hx)) ⊆ Ω ∧
      ∀ h : E, ‖h‖ ≤ δ → MapsTo (· + (x + h)) (tsupport ρ) Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := (translateOfMapsTo ρ hx).hasCompactSupport.isCompact
    |>.exists_cthickening_subset_open Ω.isOpen (translateOfMapsTo ρ hx).tsupport_subset
  refine ⟨δ, hδ, hδΩ, fun h hh z hz => hδΩ ?_⟩
  refine mem_cthickening_of_dist_le _ (z + x) δ _ ?_ ?_
  · rw [tsupport_translateOfMapsTo]
    simpa using hz
  · simpa [dist_eq_norm, ← add_assoc] using hh

/-- The first-order Taylor remainder of the regularization at `x` in the direction `h` is `T`
applied to the first-order Taylor remainder of the translates of `ρ`. -/
private theorem translatePairing_add_sub_sub_eq (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x h : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) (hxh : MapsTo (· + (x + h)) (tsupport ρ) Ω) :
    T.translatePairing ρ (x + h) - T.translatePairing ρ x - (∂_{h} T).translatePairing ρ x =
      T (translateOfMapsTo ρ hxh - translateOfMapsTo ρ hx + ∂_{h} (translateOfMapsTo ρ hx)) := by
  rw [translatePairing_eq T (translateOfMapsTo_apply ρ hxh),
    translatePairing_eq T (translateOfMapsTo_apply ρ hx),
    translatePairing_eq _ (translateOfMapsTo_apply ρ hx), lineDerivOp_apply_apply]
  simp [sub_eq_add_neg]

variable [FiniteDimensional ℝ E]

/-- The regularization is differentiable at every admissible translation, with derivative given
by the regularizations of the distributional derivatives of `T`. -/
private theorem exists_hasFDerivAt_translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) :
    ∃ L : E →L[ℝ] F, HasFDerivAt (T.translatePairing ρ) L x ∧
      ∀ v, L v = (∂_{v} T).translatePairing ρ x := by
  let L : E →L[ℝ] F := LinearMap.toContinuousLinearMap
    { toFun := fun v => (∂_{v} T).translatePairing ρ x
      map_add' := fun v w => by simp [lineDerivOp_left_add]
      map_smul' := fun c v => by simp [lineDerivOp_left_smul] }
  refine ⟨L, ?_, fun v => rfl⟩
  -- The translate of `ρ` by `x` and a compact neighbourhood `K` of its support inside `Ω`.
  let φ₀ : 𝓓(Ω, ℝ) := translateOfMapsTo ρ hx
  have hφ₀ : ∀ y, φ₀ y = ρ (y - x) := translateOfMapsTo_apply ρ hx
  obtain ⟨δ, hδ, hδΩ, hδx⟩ := exists_cthickening_tsupport_translateOfMapsTo_subset ρ hx
  let K : Compacts E := ⟨cthickening δ (tsupport φ₀), φ₀.hasCompactSupport.isCompact.cthickening⟩
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_apply_le (K := K) hδΩ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- Choose a radius on which all derivatives of order at most `N` of the Taylor remainder are
  -- bounded by `c / (C + 1) * ‖h‖`.
  have hε : 0 < c / (C + 1) := div_pos hc (by linarith)
  have hrem := fun i => φ₀.hasCompactSupport.exists_norm_iteratedFDeriv_sub_sub_add_fderiv_le
    φ₀.contDiff (n := ∞) (i := i) (by exact_mod_cast le_top) hε
  choose r hr hrem using hrem
  let r₀ := min δ ((Finset.range (N + 1)).inf' (by simp) r)
  have hr₀ : 0 < r₀ := lt_min hδ ((Finset.lt_inf'_iff _).2 fun i _ => hr i)
  filter_upwards [ball_mem_nhds (0 : E) hr₀] with h hh
  rw [mem_ball_zero_iff] at hh
  have hhδ : ‖h‖ ≤ δ := hh.le.trans (min_le_left _ _)
  -- The translate of `ρ` by `x + h`, and the Taylor remainder as a test function on `Ω`.
  let φh : 𝓓(Ω, ℝ) := translateOfMapsTo ρ (hδx h hhδ)
  let R : 𝓓(Ω, ℝ) := φh - φ₀ + ∂_{h} φ₀
  have hR : (R : E → ℝ) = fun y => φ₀ (y - h) - φ₀ y + fderiv ℝ φ₀ y h := by
    ext y
    have hd := φ₀.contDiff.differentiable (by simp) y
    simp [R, φh, hφ₀, translateOfMapsTo_apply, hd.lineDeriv_eq_fderiv, sub_sub, add_comm h x]
  have hRK : tsupport R ⊆ K := by
    rw [hR]
    exact TauCeti.tsupport_sub_sub_add_fderiv_subset _ hhδ
  have hRbound : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i R y‖ ≤ c / (C + 1) * ‖h‖ := by
    intro i hi y
    have hri : ‖h‖ < r i := hh.trans_le ((min_le_right _ _).trans
      (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
    rw [hR]
    exact hrem i h hri y
  rw [show L h = (∂_{h} T).translatePairing ρ x from rfl,
    translatePairing_add_sub_sub_eq T ρ hx (hδx h hhδ)]
  calc ‖T R‖ ≤ C * (c / (C + 1) * ‖h‖) :=
        hT R hRK _ (by positivity) hRbound
    _ = C / (C + 1) * (c * ‖h‖) := by ring
    _ ≤ c * ‖h‖ :=
      mul_le_of_le_one_left (by positivity) ((div_le_one (by linarith)).2 (by linarith))

/-- The regularization is differentiable at every admissible translation. -/
theorem differentiableAt_translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) : DifferentiableAt ℝ (T.translatePairing ρ) x :=
  let ⟨_, hL, _⟩ := exists_hasFDerivAt_translatePairing T ρ hx
  hL.differentiableAt

/-- **The derivative of a regularization.** At every admissible translation, the derivative of
`x ↦ T (ρ (· - x))` in the direction `v` is the regularization of the distributional derivative
`∂_{v} T`. -/
theorem fderiv_translatePairing_apply (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) {x : E}
    (hx : MapsTo (· + x) (tsupport ρ) Ω) (v : E) :
    fderiv ℝ (T.translatePairing ρ) x v = (∂_{v} T).translatePairing ρ x := by
  obtain ⟨L, hL, hLv⟩ := exists_hasFDerivAt_translatePairing T ρ hx
  rw [hL.fderiv, hLv]

/-- **Regularizations are smooth.** The regularization `x ↦ T (ρ (· - x))` is smooth on the open
set of translations for which `ρ (· - x)` is supported in `Ω`. -/
theorem contDiffOn_translatePairing (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) :
    ContDiffOn ℝ ∞ (T.translatePairing ρ) {x | MapsTo (· + x) (tsupport ρ) Ω} := by
  have hU := ρ.hasCompactSupport.isCompact.isOpen_setOf_mapsTo_add Ω.isOpen
  rw [contDiffOn_infty]
  intro n
  induction n generalizing T with
  | zero =>
    exact contDiffOn_zero.2 fun x hx =>
      (differentiableAt_translatePairing T ρ hx).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (differentiableAt_translatePairing T ρ hx).differentiableWithinAt,
      by simp, ?_⟩
    refine contDiffOn_clm_apply.2 fun v => (ih (∂_{v} T)).congr fun x hx => ?_
    exact fderiv_translatePairing_apply T ρ hx v

/-- **Distributions with vanishing derivatives have locally constant regularizations.** If every
directional derivative of `T` vanishes, then `x ↦ T (ρ (· - x))` is constant on every
preconnected open set of translations for which `ρ (· - x)` is supported in `Ω`. -/
theorem translatePairing_eq_of_lineDerivOp_eq_zero {T : 𝓓'(Ω, F)}
    (hT : ∀ v : E, ∂_{v} T = 0) (ρ : 𝓓(V, ℝ)) {U : Set E} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hU : ∀ x ∈ U, MapsTo (· + x) (tsupport ρ) Ω) {x y : E}
    (hx : x ∈ U) (hy : y ∈ U) : T.translatePairing ρ x = T.translatePairing ρ y := by
  refine hUo.is_const_of_fderiv_eq_zero hUc
    (fun z hz => (differentiableAt_translatePairing T ρ (hU z hz)).differentiableWithinAt)
    (fun z hz => ?_) hx hy
  ext v
  simp [fderiv_translatePairing_apply T ρ (hU z hz), hT]

omit [FiniteDimensional ℝ E] in
/-- A finite linear combination of translates `ρ (· - z)` supported in `Ω` is a test function on
`Ω`, which `T` maps to the same combination of values of the regularization. -/
private theorem exists_coe_eq_sum_and_apply_eq_sum (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ)) (s : Finset E)
    (w : E → ℝ) (hw : ∀ z, w z ≠ 0 → MapsTo (· + z) (tsupport ρ) Ω) :
    ∃ χ : 𝓓(Ω, ℝ), ⇑χ = (∑ z ∈ s, fun x ↦ w z * ρ (x - z)) ∧
      T χ = ∑ z ∈ s, w z • T.translatePairing ρ z := by
  classical
  let τ : E → 𝓓(Ω, ℝ) := fun z ↦
    if h : MapsTo (· + z) (tsupport ρ) Ω then translateOfMapsTo ρ h else 0
  refine ⟨∑ z ∈ s, w z • τ z, (map_sum (FunLike.coeAddMonoidHom 𝓓(Ω, ℝ) E ℝ) _ _).trans
    (Finset.sum_congr rfl fun z _ ↦ ?_), ?_⟩
  · by_cases hz : MapsTo (· + z) (tsupport ρ) Ω
    · ext x
      simp [τ, hz, translateOfMapsTo_apply]
    · have hwz : w z = 0 := by_contra fun h ↦ hz (hw z h)
      ext x
      simp [hwz]
  · simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hz : MapsTo (· + z) (tsupport ρ) Ω <;> simp [τ, translatePairing, hz]

omit [FiniteDimensional ℝ E] in
/-- For a compactly supported continuous `φ`, the derivatives of order at most `N` of the
integrand `φ y * ρ (x - y)` of a convolution depend uniformly continuously on `(x, y)`. -/
private theorem uniformContinuous_smul_iteratedFDeriv_sub (ρ : 𝓓(V, ℝ)) {φ : E → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (N : ℕ) :
    UniformContinuous fun (p : E × E) (i : Fin (N + 1)) ↦
      φ p.2 • iteratedFDeriv ℝ i ρ (p.1 - p.2) := by
  refine HasCompactSupport.uniformContinuous_of_continuous ?_ ?_
  · refine HasCompactSupport.intro
      ((ρ.hasCompactSupport.isCompact.add hφc.isCompact).prod hφc.isCompact)
      fun p hp ↦ funext fun i ↦ ?_
    by_cases hp₂ : p.2 ∈ tsupport φ
    · have hp₁ : p.1 - p.2 ∉ tsupport ρ :=
        fun h ↦ hp ⟨⟨p.1 - p.2, h, p.2, hp₂, sub_add_cancel _ _⟩, hp₂⟩
      simp [image_eq_zero_of_notMem_tsupport
        (fun h ↦ hp₁ (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) i h))]
    · simp [image_eq_zero_of_notMem_tsupport hp₂]
  · exact continuous_pi fun i ↦ (hφ.comp continuous_snd).smul
      ((ρ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
        (continuous_fst.sub continuous_snd))

section Convolution

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The `i`-th derivative of a convolution `x ↦ ∫ y, φ y * ρ (x - y) ∂μ` falls on the test
function `ρ`. -/
private theorem iteratedFDeriv_integral_mul_sub (ρ : 𝓓(V, ℝ)) {φ : E → ℝ} (hφ : Continuous φ)
    (i : ℕ) (x : E) :
    iteratedFDeriv ℝ i (fun x ↦ ∫ y, φ y * ρ (x - y) ∂μ) x =
      ∫ y, φ y • iteratedFDeriv ℝ i ρ (x - y) ∂μ := by
  have hL : (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ E) ℝ ℝ).comp
      (ContinuousLinearMap.lsmul ℝ ℝ) = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext a m
    simp
  have h := ρ.hasCompactSupport.iteratedFDeriv_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (hφ.locallyIntegrable (μ := μ)) ρ.contDiff (n := i) (by exact_mod_cast le_top)
  rw [hL] at h
  have hc : (fun x ↦ ∫ y, φ y * ρ (x - y) ∂μ) = φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ρ := by
    ext x
    simp [convolution_def]
  rw [hc, h, convolution_def]
  simp

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- A convolution `x ↦ ∫ y, φ y * ρ (x - y) ∂μ` minus a finite combination of translates
`ρ (· - z)` with weights `c z * φ z` is supported in `tsupport ρ + tsupport φ`. -/
private theorem tsupport_sub_subset_add {ρ : 𝓓(V, ℝ)} {φ : E → ℝ} (hφc : HasCompactSupport φ)
    {s : Finset E} {c : E → ℝ} {ψ ψu : 𝓓(Ω, ℝ)} (hψ : ∀ x, ψ x = ∫ y, φ y * ρ (x - y) ∂μ)
    (hψu : ⇑ψu = ∑ z ∈ s, fun x ↦ c z * φ z * ρ (x - z)) :
    tsupport (ψ - ψu) ⊆ tsupport ρ + tsupport φ := by
  have hvan : ∀ x ∉ tsupport ρ + tsupport φ, ∀ y, φ y * ρ (x - y) = 0 := fun x hx y ↦ by
    by_cases hy : y ∈ tsupport φ
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨x - y, h, y, hy, sub_add_cancel x y⟩,
        mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  refine closure_minimal (fun x hx ↦ by_contra fun hxL ↦ hx ?_)
    (ρ.hasCompactSupport.isCompact.add hφc).isClosed
  simp [hψ, hψu, mul_assoc, hvan x hxL]

/-- **Riemann sums of a convolution.** Let `u` be a simple function such that the derivatives of
order at most `N` of the integrand `φ y * ρ (x - y)` change by at most `η` when `y ∈ tsupport φ`
is replaced by `u y`. Then the derivatives of order at most `N` of the convolution
`x ↦ ∫ y, φ y * ρ (x - y) ∂μ` and of its Riemann sum along `u`, a finite combination of translates
of `ρ`, differ by at most `η * μ.real (tsupport φ)`. -/
private theorem norm_iteratedFDeriv_sub_riemannSum_le (ρ : 𝓓(V, ℝ)) {φ : E → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (u : SimpleFunc E E) {N : ℕ} {η : ℝ}
    (hu : ∀ x, ∀ y ∈ tsupport φ,
      dist (fun i : Fin (N + 1) ↦ φ y • iteratedFDeriv ℝ i ρ (x - y))
        (fun i : Fin (N + 1) ↦ φ (u y) • iteratedFDeriv ℝ i ρ (x - u y)) ≤ η)
    {ψ ψu : 𝓓(Ω, ℝ)} (hψ : ∀ x, ψ x = ∫ y, φ y * ρ (x - y) ∂μ)
    (hψu : ⇑ψu = ∑ z ∈ u.range, fun x ↦ μ.real (tsupport φ ∩ u ⁻¹' {z}) * φ z * ρ (x - z))
    {i : ℕ} (hi : i ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ i ⇑(ψ - ψu) x‖ ≤ η * μ.real (tsupport φ) := by
  have hK : IsCompact (tsupport φ) := hφc
  have hiω : ((i : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hρz (z : E) : ContDiff ℝ ∞ fun x ↦ ρ (x - z) :=
    ρ.contDiff.comp (contDiff_id.sub contDiff_const)
  have hD : iteratedFDeriv ℝ i ⇑ψu x = ∑ z ∈ u.range,
      μ.real (tsupport φ ∩ u ⁻¹' {z}) • (φ z • iteratedFDeriv ℝ i ρ (x - z)) := by
    rw [hψu, iteratedFDeriv_sum_apply fun z _ ↦
      ((contDiff_const.mul (hρz z)).contDiffAt.of_le hiω)]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have hsmul : (fun x ↦ μ.real (tsupport φ ∩ u ⁻¹' {z}) * φ z * ρ (x - z)) =
        fun x ↦ (μ.real (tsupport φ ∩ u ⁻¹' {z}) * φ z) • ρ (x - z) := by
      simp_rw [smul_eq_mul]
    rw [hsmul, iteratedFDeriv_const_smul_apply' ((hρz z).contDiffAt.of_le hiω),
      iteratedFDeriv_comp_sub, mul_smul]
  have hsetint : ∫ y in tsupport φ, φ y • iteratedFDeriv ℝ i ρ (x - y) ∂μ =
      ∫ y, φ y • iteratedFDeriv ℝ i ρ (x - y) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  rw [FunLike.coe_sub, iteratedFDeriv_sub_apply (ψ.contDiff.contDiffAt.of_le hiω)
    (ψu.contDiff.contDiffAt.of_le hiω), hD, funext hψ, iteratedFDeriv_integral_mul_sub ρ hφ,
    norm_sub_rev, ← hsetint]
  refine SimpleFunc.norm_sum_measureReal_smul_sub_setIntegral_le u hK.isClosed.measurableSet
    hK.measure_lt_top.ne (Continuous.integrable_of_hasCompactSupport ?_ hφc.smul_right).integrableOn
    fun y hy ↦ ?_
  · exact hφ.smul ((ρ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_const.sub continuous_id))
  · rw [← dist_eq_norm]
    exact (dist_le_pi_dist _ _ ⟨i, Nat.lt_succ_of_le hi⟩).trans (hu x y hy)

/-- **Pairing a distribution with a convolution.** Let `φ` be a compactly supported continuous
function such that `ρ (· - y)` is supported in `Ω` for every `y` in the support of `φ`. Then the
convolution `x ↦ ∫ y, φ y * ρ (x - y) ∂μ`, a test function on `Ω`, is mapped by `T` to the integral
of `φ` against the regularization `y ↦ T (ρ (· - y))`.

Formally, `T` is interchanged with the integral `∫ y, φ y • ρ (· - y) ∂μ` of translates of `ρ`. -/
theorem apply_eq_integral_smul_translatePairing [CompleteSpace F] (T : 𝓓'(Ω, F)) (ρ : 𝓓(V, ℝ))
    {φ : E → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφΩ : ∀ y ∈ tsupport φ, MapsTo (· + y) (tsupport ρ) Ω) {ψ : 𝓓(Ω, ℝ)}
    (hψ : ∀ x, ψ x = ∫ y, φ y * ρ (x - y) ∂μ) :
    T ψ = ∫ y, φ y • T.translatePairing ρ y ∂μ := by
  -- Both sides are compared with Riemann sums over one partition of `K = tsupport φ` into small
  -- pieces. On the test-function side the Riemann sum is a finite combination `ψu` of translates
  -- of `ρ`, close to `ψ` with all derivatives up to the order `N` of `T` on a compact set `L`.
  set K := tsupport φ
  have hK : IsCompact K := hφc
  set L : Set E := tsupport ρ + K
  have hL : IsCompact L := ρ.hasCompactSupport.isCompact.add hK
  have hLΩ : L ⊆ Ω := by
    rintro _ ⟨z, hz, y, hy, rfl⟩
    exact hφΩ y hy hz
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_apply_le (K := ⟨L, hL⟩) hLΩ
  -- The integrand `φ • T.translatePairing ρ` is continuous with compact support.
  have hU := ρ.hasCompactSupport.isCompact.isOpen_setOf_mapsTo_add Ω.isOpen
  have hg : UniformContinuous fun y ↦ φ y • T.translatePairing ρ y := by
    refine hφc.smul_right.uniformContinuous_of_continuous ?_
    exact (hφ.continuousOn.smul (contDiffOn_translatePairing T ρ).continuousOn
      ).continuous_of_tsupport_subset hU ((tsupport_smul_subset_left _ _).trans hφΩ)
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  set m := μ.real K
  have hm : 0 ≤ m := measureReal_nonneg
  set η := ε / ((C + 1) * (m + 1))
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuous_iff.1 hg η hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.uniformContinuous_iff.1
    (uniformContinuous_smul_iteratedFDeriv_sub ρ hφ hφc N) η hη
  -- A simple function `u` moving every point of `K` by less than `min δ₁ δ₂`; its fibres over
  -- `K` are the pieces of the partition and its values are the sample points.
  obtain ⟨n, hu⟩ := (Metric.tendstoUniformlyOn_iff.1
    (SimpleFunc.tendstoUniformlyOn_nearestPt (e := denseSeq E) hK.totallyBounded
      (by simp [(denseRange_denseSeq E).closure_range])) _ (lt_min hδ₁ hδ₂)).exists
  set u := SimpleFunc.nearestPt (denseSeq E) n
  let w : E → ℝ := fun z ↦ μ.real (K ∩ u ⁻¹' {z}) * φ z
  obtain ⟨ψu, hψu, hTψu⟩ := exists_coe_eq_sum_and_apply_eq_sum T ρ u.range w fun z hz ↦
    hφΩ z (by_contra fun h ↦ hz (by simp [w, image_eq_zero_of_notMem_tsupport h]))
  have hμK : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsetint₁ : ∫ y in K, φ y • T.translatePairing ρ y ∂μ =
      ∫ y, φ y • T.translatePairing ρ y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  -- The Riemann sum on the regularization side.
  have hR₁ : ‖T ψu - ∫ y, φ y • T.translatePairing ρ y ∂μ‖ ≤ η * m := by
    rw [hTψu, ← hsetint₁]
    simp only [w, mul_smul]
    refine SimpleFunc.norm_sum_measureReal_smul_sub_setIntegral_le u hKm hμK
      (hg.continuous.integrable_of_hasCompactSupport hφc.smul_right).integrableOn fun y hy ↦ ?_
    rw [← dist_eq_norm]
    exact (h₁ ((hu y hy).trans_le (min_le_left _ _))).le
  -- The Riemann sums on the test-function side, uniformly for all derivatives of order `≤ N`.
  have hR₂ : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i ⇑(ψ - ψu) x‖ ≤ η * m := by
    refine fun i hi ↦ norm_iteratedFDeriv_sub_riemannSum_le ρ hφ hφc u (fun x y hy ↦ ?_) hψ hψu hi
    have hd : dist (x, y) (x, u y) < δ₂ := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact (hu y hy).trans_le (min_le_right _ _)
    exact (h₂ hd).le
  -- `ψ - ψu` is supported in `L`, so the finite order of `T` on `L` bounds `T (ψ - ψu)`.
  have hTd := hT (ψ - ψu) (tsupport_sub_subset_add hφc hψ hψu) (η * m) (by positivity) hR₂
  calc dist (T ψ) (∫ y, φ y • T.translatePairing ρ y ∂μ)
      ≤ ‖T (ψ - ψu)‖ + ‖T ψu - ∫ y, φ y • T.translatePairing ρ y ∂μ‖ := by
        rw [dist_eq_norm, map_sub]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * (η * m) + η * m := add_le_add hTd hR₁
    _ = ε * ((C + 1) * m / ((C + 1) * (m + 1))) := by
        simp only [η]
        field_simp
    _ ≤ ε := by
        refine mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).2 ?_)
        nlinarith

end Convolution

end Distribution
