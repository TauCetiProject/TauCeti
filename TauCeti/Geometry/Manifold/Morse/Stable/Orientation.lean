/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Frame
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.LinearAlgebra.Orientation.Exact.Basic
import TauCeti.Geometry.Manifold.Orientation.Family
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Orientations of the manifold along stable and unstable manifolds

Let `X` be a pseudo-gradient adapted to a Morse function `f` on a compact manifold `M`, and `φ` a
Morse chart at a critical point `x` in which `X` is linear. Write `V⁻` and `V⁺` for its spaces of
coordinates of negative and of positive weight. At a point `y` of the unstable manifold `W^u(x)`,
the unstable frame of `X` and the normal coordinates of the stable manifold of `x` for `-X` form a
short exact sequence `0 → V⁻ → T_y M → V⁺ → 0`
(`TauCeti.IsAdaptedPseudoGradient.exact_unstableFrame_neg_stableNormal`), so orientations `op` of
`V⁻` and `op'` of `V⁺` orient `T_y M`, subspace first (`Orientation.ofExact`). At a point of the
stable manifold `W^s(x)` the sequence `0 → V⁺ → T_y M → V⁻ → 0` does the same
(`TauCeti.IsAdaptedPseudoGradient.exact_neg_unstableFrame_stableNormal`).

This file compares these orientations with an orientation `o` of `M`. Whether they agree with `o`
does not depend on the point: on `W^u(x)` the frame orientation is the orientation of `o` at one
point exactly when it is at any other
(`TauCeti.IsAdaptedPseudoGradient.reindex_ofExact_unstableFrame_eq_orientationAt_iff`), and
likewise on `W^s(x)`
(`TauCeti.IsAdaptedPseudoGradient.reindex_ofExact_stableNormal_eq_orientationAt_iff`). Taking
one of the points to be `x` itself, if `op` followed by `op'` orients `T_x M` like `o`, then the
frame orientation is the orientation of `o` all along `W^u(x)`. This is what makes the integral
Morse complex of `-f` the dual of that of `f` on an oriented manifold: the two orientations of the
tangent space at a point of a trajectory compared in
`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign` are then both the orientation of `o`.

The proof reads the tangent spaces in the model space through the chart, after flowing into the
part of the chart where the flow is linear. There the frame and the normal coordinates at `y` are
positive multiples of those at `x` (`Orientation.map_ofExact_of_pos`). The orientation of `o` is
carried along too: the flow preserves every orientation of `M`
(`TauCeti.IsAdaptedPseudoGradient.isOrientationPreservingAt_flow`), since its time-`t` maps are
joined to the identity, and the chart preserves `o` at the points of a trajectory converging to
`x` exactly when it does at `x`, since together with `x` they form a preconnected subset of the
source of the chart (`IsPreconnected.isOrientationPreservingAt_iff`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isOrientationPreservingAt_flow`: the time-`t` maps of the flow preserve every orientation.
* `reindex_ofExact_unstableFrame_eq_orientationAt_iff`: along the unstable manifold, the frame
  orientation agrees with `o` everywhere or nowhere.
* `reindex_ofExact_stableNormal_eq_orientationAt_iff`: the same along the stable manifold.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations) and §3, Exercise 5 (the Morse complex of
  `-f` and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (orientations of the stable and unstable manifolds).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {ι : Type*} [Fintype ι]

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- **The flow preserves orientations.** Every time-`t` map of the flow of an adapted
pseudo-gradient preserves every orientation of `M`, since it is joined to the identity by the
flow. -/
theorem isOrientationPreservingAt_flow (o : Manifold.Orientation 𝓘(ℝ, E) M ι) (t : ℝ) (y : M) :
    o.IsOrientationPreservingAt o (hX.flow t) y := by
  have h := Manifold.Orientation.isOrientationPreservingAt_family_iff o o
    (hX.contMDiff_flow_uncurry.of_le (by simp)) y
    (fun s ↦ by
      have hc : (hX.flowDiffeomorph s : M → M) = fun z ↦ hX.flow s z :=
        funext (hX.flowDiffeomorph_apply s)
      exact hc ▸ (hX.flowDiffeomorph s).isInvertible_mfderiv (by simp) (x := y)) t 0
  simp only at h
  rw [h, show hX.flow 0 = id from funext fun z ↦ hX.flow.map_zero_apply z]
  exact Manifold.Orientation.isOrientationPreservingAt_id o y

omit [Fintype ι] in
/-- Two equations between orientations are equivalent when both sides of each are carried to
the same orientations by a pair of linear equivalences. -/
private theorem eq_iff_eq_of_map_eq {V V' W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W] [Module ℝ W] {a b : Orientation ℝ V ι}
    {a' b' : Orientation ℝ V' ι} (eV : V ≃ₗ[ℝ] W) (eV' : V' ≃ₗ[ℝ] W)
    (ha : Orientation.map ι eV a = Orientation.map ι eV' a')
    (hb : Orientation.map ι eV b = Orientation.map ι eV' b') : a = b ↔ a' = b' := by
  rw [← (Orientation.map ι eV).injective.eq_iff, ha, hb,
    (Orientation.map ι eV').injective.eq_iff]

variable {hX} {φ : MorseChart E f x}

omit [CompactSpace M] [T2Space M] in
/-- Along a curve that stays in the source of a Morse chart and converges to its centre, the chart
preserves an orientation `o` of `M` at the start of the curve exactly when it does at the centre:
the curve and the centre form a preconnected subset of the source. -/
private theorem isOrientationPreservingAt_toChart_iff_of_tendsto
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι) (O : Manifold.Orientation 𝓘(ℝ, E) E ι) {γ : ℝ → M}
    (hγ : Continuous γ) (hγs : ∀ s, 0 ≤ s → γ s ∈ φ.toChart.source)
    (hγx : Tendsto γ atTop (𝓝 x)) :
    o.IsOrientationPreservingAt O φ.toChart (γ 0) ↔ o.IsOrientationPreservingAt O φ.toChart x := by
  have hpre : IsPreconnected (γ '' Ici 0) := isPreconnected_Ici.image γ hγ.continuousOn
  have hx : x ∈ closure (γ '' Ici 0) :=
    mem_closure_of_tendsto hγx ((eventually_ge_atTop 0).mono fun s hs ↦ mem_image_of_mem γ hs)
  have hsub : insert x (γ '' Ici 0) ⊆ φ.toChart.source := by
    rintro _ (rfl | ⟨s, hs, rfl⟩)
    exacts [φ.mem_source, hγs s hs]
  have hpre' : IsPreconnected (insert x (γ '' Ici 0)) :=
    hpre.subset_closure (subset_insert _ _) (insert_subset hx subset_closure)
  refine IsPreconnected.isOrientationPreservingAt_iff hpre'
    (fun z hz ↦ contMDiffAt_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) (hsub hz))
    (fun z hz ↦ isInvertible_mfderiv_chart
      (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) (hsub hz)) o O
    (mem_insert_of_mem _ (mem_image_of_mem γ self_mem_Ici)) (mem_insert x _)

/-- Let `γ` be a curve that starts at `Φ_τ y`, stays in the source of the Morse chart `φ` and
converges to its centre `x`. The derivatives of `φ ∘ Φ_τ` at `y` and of `φ` at `x` carry the
orientations of `o` at `y` and at `x` to the same orientation of the model space. -/
private theorem map_orientationAt_eq_of_tendsto (o : Manifold.Orientation 𝓘(ℝ, E) M ι) {y : M}
    {τ : ℝ} {γ : ℝ → M} (hγ : Continuous γ) (hγ0 : γ 0 = hX.flow τ y)
    (hγs : ∀ s, 0 ≤ s → γ s ∈ φ.toChart.source) (hγx : Tendsto γ atTop (𝓝 x))
    (eDy : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((φ.toChart ∘ hX.flow τ) y))
    (heDy : (eDy : TangentSpace 𝓘(ℝ, E) y →L[ℝ] _) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow τ) y)
    (eDx : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (φ.toChart x))
    (heDx : (eDx : TangentSpace 𝓘(ℝ, E) x →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x) :
    Orientation.map ι (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E) (o.orientationAt y) =
      Orientation.map ι (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (o.orientationAt x) := by
  -- The chart carries `o` at `x` to the constant orientation `O` of the model space, hence also
  -- at `Φ_τ y`, and the flow preserves `o`.
  let O := Manifold.Orientation.model (I := 𝓘(ℝ, E))
    (Orientation.map ι eDx.toLinearEquiv (o.orientationAt x)) o.card_eq
  have hPx : o.IsOrientationPreservingAt O φ.toChart x :=
    (Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq o O _ x eDx heDx).2
      (Manifold.Orientation.orientationAt_model _ _ _).symm
  have hPz := (isOrientationPreservingAt_toChart_iff_of_tendsto o O hγ hγs hγx).2 hPx
  rw [hγ0] at hPz
  exact ((Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq o O _ y eDy heDy).1
    (hPz.comp (hX.isOrientationPreservingAt_flow o τ y))).trans
    (Manifold.Orientation.orientationAt_model _ _ _)

/-- `0` is a time of linear backward flow of the centre of a Morse chart. -/
private theorem zero_mem_linearBackwardTimes (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    (0 : ℝ) ∈ hX.linearBackwardTimes φ x := by
  have hfix := hX.flow_apply_of_mfderiv_eq_zero hx
  refine (hX.mem_linearBackwardTimes φ).2 ⟨by simp [hfix], fun t _ ↦ ?_⟩
  have hl : φ.linearFlow t 0 = 0 := by
    funext i
    simp [MorseChart.linearFlow_apply]
  rw [hfix, φ.apply_self, map_zero, hl, map_zero, ← φ.apply_self]
  exact φ.toChart.map_source φ.mem_source

/-- `0` is a time of linear forward flow of the centre of a Morse chart. -/
private theorem zero_mem_linearForwardTimes (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    (0 : ℝ) ∈ hX.linearForwardTimes φ x := by
  have hfix := hX.flow_apply_of_mfderiv_eq_zero hx
  refine (hX.mem_linearForwardTimes φ).2 ⟨by simp [hfix], fun t _ ↦ ?_⟩
  have hl : φ.linearFlow t 0 = 0 := by
    funext i
    simp [MorseChart.linearFlow_apply]
  rw [hfix, φ.apply_self, map_zero, hl, map_zero, ← φ.apply_self]
  exact φ.toChart.map_source φ.mem_source

variable (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))

include hφ

/-- The comparison of the frame orientation along the unstable manifold with `o`, at a point of
`W^u(x)` and at `x`. -/
private theorem reindex_ofExact_unstableFrame_eq_orientationAt_iff_self (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E) (-f) x) ≃ ι)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (hxu : x ∈ hX.flow.unstableSet x) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    Orientation.reindex ℝ _ e (Orientation.ofExact (injective_unstableFrame_of_mem hφ hf hy)
        (exact_unstableFrame_neg_stableNormal hφ hf hx hy)
        (surjective_stableNormal_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)
          ((hX.unstableSet_eq_stableSet_neg hf x).subset hy)) op op'
        φ.finrank_negativeWeight_fun (φ.neg hx).finrank_negativeWeight_fun) =
        o.orientationAt y ↔
      Orientation.reindex ℝ _ e (Orientation.ofExact (injective_unstableFrame_of_mem hφ hf hxu)
        (exact_unstableFrame_neg_stableNormal hφ hf hx hxu)
        (surjective_stableNormal_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)
          ((hX.unstableSet_eq_stableSet_neg hf x).subset hxu)) op op'
        φ.finrank_negativeWeight_fun (φ.neg hx).finrank_negativeWeight_fun) =
        o.orientationAt x := by
  have h0 := zero_mem_linearBackwardTimes (hX := hX) (φ := φ)
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.mem_criticalPoints)
  have hfl0 : (φ.toChart ∘ hX.flow (-0) : M → E) = φ.toChart := funext fun z ↦ by simp
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφ hf hy).exists
  obtain ⟨eDy, heDy⟩ := isInvertible_mfderiv_toChart_comp_flow (hX := hX) (φ := φ)
    ((hX.mem_linearBackwardTimes φ).1 hT).1
  obtain ⟨eDx, heDx⟩ := isInvertible_mfderiv_chart
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) φ.mem_source
  -- Read both tangent spaces in the model space `E`, through `φ ∘ Φ_{-T}` and `φ`. There `o`
  -- gives the same orientation at `y` and at `x`.
  let Ly : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E := eDy.toLinearEquiv
  let Lx : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E := eDx.toLinearEquiv
  refine eq_iff_eq_of_map_eq Ly Lx ?_ (map_orientationAt_eq_of_tendsto o
    (γ := fun s ↦ hX.flow (-(T + s)) y) (hX.flow.continuous (by fun_prop) continuous_const)
    (by simp)
    (fun s hs ↦ ((hX.mem_linearBackwardTimes φ).1 (add_mem_linearBackwardTimes hφ hT hs).1).1)
    ((Flow.mem_unstableSet.1 hy).comp
      (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_left _ T tendsto_id)))
    eDy heDy eDx heDx)
  rw [Orientation.map_reindex, Orientation.map_reindex]
  congr 1
  -- So do the frame orientations: `Lx⁻¹ ∘ Ly` carries the frame and the normal coordinates at
  -- `y` to positive multiples of those at `x`.
  have hL : (Ly.trans Lx.symm).trans Lx = Ly := LinearEquiv.ext fun v ↦ by simp
  rw [← hL, Orientation.map_trans]
  congr 1
  refine Orientation.map_ofExact_of_pos _ _ _ _ _ _ _ (Real.exp_pos (-T)) (Real.exp_pos T)
    (fun c ↦ Lx.injective ?_) (fun w ↦ ?_) _ _ _ _
  · have hy' := mfderiv_unstableFrame hφ hT c
    have hx' := mfderiv_unstableFrame hφ h0 c
    rw [← heDy, ContinuousLinearEquiv.coe_coe] at hy'
    rw [hfl0, ← heDx, ContinuousLinearEquiv.coe_coe, neg_zero, Real.exp_zero, one_smul] at hx'
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_smul,
      ContinuousLinearMap.coe_coe]
    exact hy'.trans (congrArg (Real.exp (-T) • ·) hx').symm
  · have hq (t : ℝ) : ((φ.neg hx).toChart ∘ (hX.neg hf).flow t : M → E) =
        φ.toChart ∘ hX.flow (-t) := by
      funext z
      simp [hX.neg_flow hf]
    have hT' : T ∈ (hX.neg hf).linearForwardTimes (φ.neg hx) y := by
      rwa [neg_linearForwardTimes (hX := hX) (φ := φ) hf hx]
    have h0' : (0 : ℝ) ∈ (hX.neg hf).linearForwardTimes (φ.neg hx) x := by
      rwa [neg_linearForwardTimes (hX := hX) (φ := φ) hf hx]
    simp only [ContinuousLinearMap.coe_coe]
    rw [stableNormal_apply (φ.coord_mfderiv_neg hφ hx) hT',
      stableNormal_apply (φ.coord_mfderiv_neg hφ hx) h0', hq, hq, hfl0, ← heDy, ← heDx]
    simp only [smul_smul, ← Real.exp_add, add_neg_cancel, neg_zero, Real.exp_zero, one_smul,
      LinearEquiv.trans_apply]
    exact congrArg _ (eDx.apply_symm_apply (eDy w))

/-- The comparison of the frame orientation along the stable manifold with `o`, at a point of
`W^s(x)` and at `x`. -/
private theorem reindex_ofExact_stableNormal_eq_orientationAt_iff_self (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x + manifoldMorseIndex 𝓘(ℝ, E) f x) ≃ ι)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (hxs : x ∈ hX.flow.stableSet x) {y : M} (hy : y ∈ hX.flow.stableSet x) :
    Orientation.reindex ℝ _ e (Orientation.ofExact
        (injective_unstableFrame_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx) hf.neg
          ((hX.stableSet_eq_unstableSet_neg hf x).subset hy))
        (exact_neg_unstableFrame_stableNormal hφ hf hx hy)
        (surjective_stableNormal_of_mem hφ hy) op' op
        (φ.neg hx).finrank_negativeWeight_fun φ.finrank_negativeWeight_fun) =
        o.orientationAt y ↔
      Orientation.reindex ℝ _ e (Orientation.ofExact
        (injective_unstableFrame_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx) hf.neg
          ((hX.stableSet_eq_unstableSet_neg hf x).subset hxs))
        (exact_neg_unstableFrame_stableNormal hφ hf hx hxs)
        (surjective_stableNormal_of_mem hφ hxs) op' op
        (φ.neg hx).finrank_negativeWeight_fun φ.finrank_negativeWeight_fun) =
        o.orientationAt x := by
  have h0 := zero_mem_linearForwardTimes (hX := hX) (φ := φ)
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.mem_criticalPoints)
  have hfl0 : (φ.toChart ∘ hX.flow 0 : M → E) = φ.toChart := funext fun z ↦ by simp
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearForwardTimes hφ hy).exists
  obtain ⟨eDy, heDy⟩ := isInvertible_mfderiv_toChart_comp_flow (hX := hX) (φ := φ)
    ((hX.mem_linearForwardTimes φ).1 hT).1
  obtain ⟨eDx, heDx⟩ := isInvertible_mfderiv_chart
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) φ.mem_source
  -- Read both tangent spaces in the model space `E`, through `φ ∘ Φ_T` and `φ`. There `o` gives
  -- the same orientation at `y` and at `x`.
  let Ly : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E := eDy.toLinearEquiv
  let Lx : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E := eDx.toLinearEquiv
  refine eq_iff_eq_of_map_eq Ly Lx ?_ (map_orientationAt_eq_of_tendsto o
    (γ := fun s ↦ hX.flow (s + T) y) (hX.flow.continuous (by fun_prop) continuous_const)
    (by simp)
    (fun s hs ↦ ((hX.mem_linearForwardTimes φ).1 (add_mem_linearForwardTimes hφ hT hs).1).1)
    ((Flow.mem_stableSet.1 hy).comp (tendsto_atTop_add_const_right _ T tendsto_id))
    eDy heDy eDx heDx)
  rw [Orientation.map_reindex, Orientation.map_reindex]
  congr 1
  -- So do the frame orientations: `Lx⁻¹ ∘ Ly` carries the frame and the normal coordinates at
  -- `y` to positive multiples of those at `x`.
  have hL : (Ly.trans Lx.symm).trans Lx = Ly := LinearEquiv.ext fun v ↦ by simp
  rw [← hL, Orientation.map_trans]
  congr 1
  have hq (t : ℝ) : ((φ.neg hx).toChart ∘ (hX.neg hf).flow (-t) : M → E) =
      φ.toChart ∘ hX.flow t := by
    funext z
    simp [hX.neg_flow hf]
  refine Orientation.map_ofExact_of_pos _ _ _ _ _ _ _ (Real.exp_pos (-T)) (Real.exp_pos T)
    (fun c ↦ Lx.injective ?_) (fun w ↦ ?_) _ _ _ _
  · have hT' : T ∈ (hX.neg hf).linearBackwardTimes (φ.neg hx) y := by
      rwa [neg_linearBackwardTimes (hX := hX) (φ := φ) hf hx]
    have h0' : (0 : ℝ) ∈ (hX.neg hf).linearBackwardTimes (φ.neg hx) x := by
      rwa [neg_linearBackwardTimes (hX := hX) (φ := φ) hf hx]
    have hy' := mfderiv_unstableFrame (φ.coord_mfderiv_neg hφ hx) hT' c
    have hx' := mfderiv_unstableFrame (φ.coord_mfderiv_neg hφ hx) h0' c
    rw [hq, ← heDy, ContinuousLinearEquiv.coe_coe] at hy'
    rw [hq, hfl0, ← heDx, ContinuousLinearEquiv.coe_coe, neg_zero, Real.exp_zero,
      one_smul] at hx'
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_smul,
      ContinuousLinearMap.coe_coe]
    exact hy'.trans (congrArg (Real.exp (-T) • ·) hx').symm
  · simp only [ContinuousLinearMap.coe_coe]
    rw [stableNormal_apply hφ hT, stableNormal_apply hφ h0, hfl0, ← heDy, ← heDx]
    simp only [smul_smul, ← Real.exp_add, add_neg_cancel, neg_zero, Real.exp_zero, one_smul,
      LinearEquiv.trans_apply]
    exact congrArg _ (eDx.apply_symm_apply (eDy w))

/-- **The frame orientations along the unstable manifold.** Let `o` be an orientation of `M`, and
orient the coordinates of negative weight of a Morse chart `φ` at `x`, in which `X` is linear, by
`op`, and those of positive weight by `op'`. At each point `y` of `W^u(x)`, the unstable frame
of `X` and the normal coordinates of the stable manifold of `x` for `-X` form a short exact
sequence `0 → V⁻ → T_y M → V⁺ → 0`, so `op` and `op'` orient `T_y M` (`Orientation.ofExact`).
Whether this orientation is the one of `o` does not depend on the point of `W^u(x)`; in
particular, it is the one of `o` everywhere on `W^u(x)` as soon as it is at `x`. -/
theorem reindex_ofExact_unstableFrame_eq_orientationAt_iff (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E) (-f) x) ≃ ι)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    {y₁ y₂ : M} (hy₁ : y₁ ∈ hX.flow.unstableSet x) (hy₂ : y₂ ∈ hX.flow.unstableSet x) :
    Orientation.reindex ℝ _ e (Orientation.ofExact (injective_unstableFrame_of_mem hφ hf hy₁)
        (exact_unstableFrame_neg_stableNormal hφ hf hx hy₁)
        (surjective_stableNormal_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)
          ((hX.unstableSet_eq_stableSet_neg hf x).subset hy₁)) op op'
        φ.finrank_negativeWeight_fun (φ.neg hx).finrank_negativeWeight_fun) =
        o.orientationAt y₁ ↔
      Orientation.reindex ℝ _ e (Orientation.ofExact (injective_unstableFrame_of_mem hφ hf hy₂)
        (exact_unstableFrame_neg_stableNormal hφ hf hx hy₂)
        (surjective_stableNormal_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)
          ((hX.unstableSet_eq_stableSet_neg hf x).subset hy₂)) op op'
        φ.finrank_negativeWeight_fun (φ.neg hx).finrank_negativeWeight_fun) =
        o.orientationAt y₂ :=
  have hxu := (hX.mem_unstableSet_inter_stableSet_self
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.mem_criticalPoints)).1
  (reindex_ofExact_unstableFrame_eq_orientationAt_iff_self hφ hf hx o e op op' hxu hy₁).trans
    (reindex_ofExact_unstableFrame_eq_orientationAt_iff_self hφ hf hx o e op op' hxu hy₂).symm

/-- **The frame orientations along the stable manifold.** Let `o` be an orientation of `M`, and
orient the coordinates of positive weight of a Morse chart `φ` at `x`, in which `X` is linear, by
`op'`, and those of negative weight by `op`. At each point `y` of `W^s(x)`, the unstable frame
of `-X` and the normal coordinates of the stable manifold of `x` for `X` form a short exact
sequence `0 → V⁺ → T_y M → V⁻ → 0`, so `op'` and `op` orient `T_y M` (`Orientation.ofExact`).
Whether this orientation is the one of `o` does not depend on the point of `W^s(x)`; in
particular, it is the one of `o` everywhere on `W^s(x)` as soon as it is at `x`. -/
theorem reindex_ofExact_stableNormal_eq_orientationAt_iff (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x + manifoldMorseIndex 𝓘(ℝ, E) f x) ≃ ι)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    {y₁ y₂ : M} (hy₁ : y₁ ∈ hX.flow.stableSet x) (hy₂ : y₂ ∈ hX.flow.stableSet x) :
    Orientation.reindex ℝ _ e (Orientation.ofExact
        (injective_unstableFrame_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx) hf.neg
          ((hX.stableSet_eq_unstableSet_neg hf x).subset hy₁))
        (exact_neg_unstableFrame_stableNormal hφ hf hx hy₁)
        (surjective_stableNormal_of_mem hφ hy₁) op' op
        (φ.neg hx).finrank_negativeWeight_fun φ.finrank_negativeWeight_fun) =
        o.orientationAt y₁ ↔
      Orientation.reindex ℝ _ e (Orientation.ofExact
        (injective_unstableFrame_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx) hf.neg
          ((hX.stableSet_eq_unstableSet_neg hf x).subset hy₂))
        (exact_neg_unstableFrame_stableNormal hφ hf hx hy₂)
        (surjective_stableNormal_of_mem hφ hy₂) op' op
        (φ.neg hx).finrank_negativeWeight_fun φ.finrank_negativeWeight_fun) =
        o.orientationAt y₂ :=
  have hxs := (hX.mem_unstableSet_inter_stableSet_self
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.mem_criticalPoints)).2
  (reindex_ofExact_stableNormal_eq_orientationAt_iff_self hφ hf hx o e op' op hxs hy₁).trans
    (reindex_ofExact_stableNormal_eq_orientationAt_iff_self hφ hf hx o e op' op hxs hy₂).symm

end IsAdaptedPseudoGradient

end TauCeti
