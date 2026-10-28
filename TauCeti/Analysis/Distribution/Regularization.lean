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
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
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

## Main declarations

* `Distribution.translatePairing`: the regularization `x ↦ T (ρ (· - x))`.
* `Distribution.fderiv_translatePairing_apply`: the derivative identity.
* `Distribution.contDiffOn_translatePairing`: the regularization is smooth.
* `Distribution.translatePairing_eq_of_lineDerivOp_eq_zero`: if all derivatives of `T` vanish,
  the regularization is constant on preconnected open sets of admissible translations.

## References

* [L. Hörmander, *The Analysis of Linear Partial Differential Operators I*][hormander2003],
  §2.1 for the local order estimate and Theorem 4.1.1 for the smoothness of regularizations and
  their derivatives.
-/

public section

noncomputable section

open Set Filter Topology TopologicalSpace TestFunction LineDeriv Metric
open scoped Distributions ContDiff

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

end Distribution
