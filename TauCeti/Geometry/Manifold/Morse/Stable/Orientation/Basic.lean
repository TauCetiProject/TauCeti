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
`V⁻` and `op'` of `V⁺` orient `T_y M`, subspace first (`Orientation.ofExact`): this is
`TauCeti.IsAdaptedPseudoGradient.unstableFrameOrientation`. At a point of the stable manifold
`W^s(x)` the sequence `0 → V⁺ → T_y M → V⁻ → 0` does the same
(`TauCeti.IsAdaptedPseudoGradient.exact_neg_unstableFrame_stableNormal`), giving
`TauCeti.IsAdaptedPseudoGradient.stableNormalOrientation`.

This file compares these orientations with an orientation `o` of `M`. Whether they agree with `o`
does not depend on the point: on `W^u(x)` the frame orientation is the orientation of `o` at one
point exactly when it is at any other
(`TauCeti.IsAdaptedPseudoGradient.reindex_unstableFrameOrientation_eq_orientationAt_iff`), and
likewise on `W^s(x)`
(`TauCeti.IsAdaptedPseudoGradient.reindex_stableNormalOrientation_eq_orientationAt_iff`). Taking
one of the points to be `x` itself, if `op` followed by `op'` orients `T_x M` like `o`, then the
frame orientation is the orientation of `o` all along `W^u(x)`. This supplies the `ε = 1` step in
comparing the signed trajectory counts of `-f` and of `f` on an oriented manifold: the two
orientations of the tangent space at a point of a trajectory compared in
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

* `unstableFrameOrientation`, `stableNormalOrientation`: the orientations of the tangent spaces
  along the unstable and the stable manifold induced by orientations of `V⁻` and `V⁺`.
* `isOrientationPreservingAt_flow`: the time-`t` maps of the flow preserve every orientation.
* `map_orientationAt_eq_of_tendsto`: read in the model space through the chart after flowing, an
  orientation of `M` is the same at a point and at the centre of the chart.
* `map_orientationAt_eq_of_mem_linearBackwardTimes`: the same along the backward flow from a point
  of the unstable manifold.
* `map_orientationAt_eq_of_mem_linearForwardTimes`: the same along the forward flow from a point
  of the stable manifold.
* `map_unstableFrameOrientation_eq`, `map_stableNormalOrientation_eq`: read in the chart after
  flowing into the part of the Morse chart where the flow is linear, the frame orientation at a
  point is the frame orientation at the critical point read in the Morse chart. No orientation of
  `M` is involved.
* `reindex_unstableFrameOrientation_eq_orientationAt_iff`: along the unstable manifold, the frame
  orientation agrees with `o` everywhere or nowhere.
* `reindex_stableNormalOrientation_eq_orientationAt_iff`: the same along the stable manifold.
* `stableNormalOrientation_self`: at the critical point the two frame orientations differ by
  `(-1) ^ (ind_f x * ind_{-f} x)`, the sign of exchanging the two factors.
* `reindex_stableNormalOrientation_eq_neg_one_pow_smul`: so if the frame orientation at `x` along
  the unstable manifold is that of `o`, the one along the stable manifold is
  `(-1) ^ (ind_f x * ind_{-f} x)` times that of `o` all along `W^s(x)`.
* `complementaryOrientation`, `reindex_unstableFrameOrientation_complementaryOrientation`,
  `complementaryOrientation_eq_iff`: the orientation of `V⁺` completing an orientation of `V⁻` to
  that of `o` at `x`, and its characterization.

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
    o.IsOrientationPreservingAt o (hX.flow t) y :=
  Manifold.Orientation.isOrientationPreservingAt_of_family_eq_id o
    (hX.contMDiff_flow_uncurry.of_le (by simp)) y
    (fun s ↦ by
      have hc : (hX.flowDiffeomorph s : M → M) = fun z ↦ hX.flow s z :=
        funext (hX.flowDiffeomorph_apply s)
      exact hc ▸ (hX.flowDiffeomorph s).isInvertible_mfderiv (by simp) (x := y))
    (funext fun z ↦ hX.flow.map_zero_apply z) t

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
    (fun z hz ↦ contMDiffAt_of_mem_maximalAtlas φ.mem_maximalAtlas_one (hsub hz))
    (fun z hz ↦ isInvertible_mfderiv_chart φ.mem_maximalAtlas_one (hsub hz)) o O
    (mem_insert_of_mem _ (mem_image_of_mem γ self_mem_Ici)) (mem_insert x _)

/-- **Reading an orientation of `M` in a Morse chart along the flow.** Let `γ` be a curve that
starts at `Φ_τ y`, stays in the source of the Morse chart `φ` and converges to its centre `x`. The
derivatives of `φ ∘ Φ_τ` at `y` and of `φ` at `x` carry the orientations of `o` at `y` and at `x`
to the same orientation of the model space. -/
theorem map_orientationAt_eq_of_tendsto (o : Manifold.Orientation 𝓘(ℝ, E) M ι) {y : M}
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

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Read in the model space through `eDy` and `eDx`, two short exact sequences
`0 → A → T_y M → C → 0` and `0 → A → T_x M → C → 0` induce the same orientation when `eDx⁻¹ ∘ eDy`
rescales the first sequence positively into the second. -/
private theorem map_ofExact_eq_of_map_eq_smul {y : M}
    (eDy : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] E) (eDx : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E)
    {A C : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup C] [Module ℝ C]
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ C] {m n : ℕ}
    {fy : A →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) y} {gy : TangentSpace 𝓘(ℝ, E) y →ₗ[ℝ] C}
    {fx : A →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x} {gx : TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] C}
    (hfy : Injective fy) (hfgy : Exact fy gy) (hgy : Surjective gy)
    (hfx : Injective fx) (hfgx : Exact fx gx) (hgx : Surjective gx)
    (oA : Orientation ℝ A (Fin m)) (oC : Orientation ℝ C (Fin n)) (hm : Module.finrank ℝ A = m)
    (hn : Module.finrank ℝ C = n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfe : ∀ c, eDy (fy c) = a • eDx (fx c)) (hge : ∀ w, gx (eDx.symm (eDy w)) = b • gy w) :
    Orientation.map _ (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E)
        (Orientation.ofExact hfy hfgy hgy oA oC hm hn) =
      Orientation.map _ (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (Orientation.ofExact hfx hfgx hgx oA oC hm hn) := by
  let Ly : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E := eDy.toLinearEquiv
  let Lx : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E := eDx.toLinearEquiv
  have hL : (Ly.trans Lx.symm).trans Lx = Ly := LinearEquiv.ext fun v ↦ by simp
  -- The statement coerces `eDy` and `eDx` to linear equivalences into `E`; name them to rewrite.
  change Orientation.map _ Ly _ = Orientation.map _ Lx _
  rw [← hL, Orientation.map_trans]
  congr 1
  refine Orientation.map_ofExact_of_pos _ _ _ _ _ _ _ ha hb (fun c ↦ Lx.injective ?_)
    (fun w ↦ hge w) _ _ _ _
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_smul]
  exact hfe c

variable (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))

include hφ

/-- **Reading an orientation of `M` in a Morse chart along the backward flow.** Let `y` be a point
of `W^u(x)` and `T` a time of linear backward flow from `y`. The derivatives of `φ ∘ Φ_{-T}` at `y`
and of `φ` at `x` carry the orientations of `o` at `y` and at `x` to the same orientation of the
model space. -/
theorem map_orientationAt_eq_of_mem_linearBackwardTimes (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    {y : M} (hy : y ∈ hX.flow.unstableSet x) {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y)
    (eDy : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((φ.toChart ∘ hX.flow (-T)) y))
    (heDy : (eDy : TangentSpace 𝓘(ℝ, E) y →L[ℝ] _) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y)
    (eDx : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (φ.toChart x))
    (heDx : (eDx : TangentSpace 𝓘(ℝ, E) x →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x) :
    Orientation.map ι (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E) (o.orientationAt y) =
      Orientation.map ι (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (o.orientationAt x) :=
  map_orientationAt_eq_of_tendsto o (γ := fun s ↦ hX.flow (-(T + s)) y)
    (hX.flow.continuous (by fun_prop) continuous_const) (by simp)
    (fun s hs ↦ ((hX.mem_linearBackwardTimes φ).1 (add_mem_linearBackwardTimes hφ hT hs).1).1)
    ((Flow.mem_unstableSet.1 hy).comp
      (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_left _ T tendsto_id)))
    eDy heDy eDx heDx

/-- **Reading an orientation of `M` in a Morse chart along the forward flow.** Let `y` be a point
of `W^s(x)` and `T` a time of linear forward flow from `y`. The derivatives of `φ ∘ Φ_T` at `y`
and of `φ` at `x` carry the orientations of `o` at `y` and at `x` to the same orientation of the
model space. -/
theorem map_orientationAt_eq_of_mem_linearForwardTimes (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    {y : M} (hy : y ∈ hX.flow.stableSet x) {T : ℝ} (hT : T ∈ hX.linearForwardTimes φ y)
    (eDy : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((φ.toChart ∘ hX.flow T) y))
    (heDy : (eDy : TangentSpace 𝓘(ℝ, E) y →L[ℝ] _) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y)
    (eDx : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (φ.toChart x))
    (heDx : (eDx : TangentSpace 𝓘(ℝ, E) x →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x) :
    Orientation.map ι (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E) (o.orientationAt y) =
      Orientation.map ι (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (o.orientationAt x) :=
  map_orientationAt_eq_of_tendsto o (γ := fun s ↦ hX.flow (s + T) y)
    (hX.flow.continuous (by fun_prop) continuous_const) (by simp)
    (fun s hs ↦ ((hX.mem_linearForwardTimes φ).1 (add_mem_linearForwardTimes hφ hT hs).1).1)
    ((Flow.mem_stableSet.1 hy).comp (tendsto_atTop_add_const_right _ T tendsto_id))
    eDy heDy eDx heDx

/-- **The frame orientation along the unstable manifold.** At a point `y` of `W^u(x)`, the unstable
frame of `X` and the normal coordinates of the stable manifold of `x` for `-X` form a short exact
sequence `0 → V⁻ → T_y M → V⁺ → 0`. This is the orientation of `T_y M` that it induces from the
orientations `op` of `V⁻` and `op'` of `V⁺`, subspace first (`Orientation.ofExact`). -/
noncomputable def unstableFrameOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E) (-f) x)) :=
  Orientation.ofExact (injective_unstableFrame_of_mem hφ hf hy)
    (exact_unstableFrame_neg_stableNormal hφ hf hx hy)
    (surjective_stableNormal_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)
      ((hX.unstableSet_eq_stableSet_neg hf x).subset hy)) op op'
    φ.finrank_negativeWeight_fun (φ.neg hx).finrank_negativeWeight_fun

/-- The defining formula of `unstableFrameOrientation`. -/
theorem unstableFrameOrientation_def (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    unstableFrameOrientation hφ hf hx op op' hy =
      Orientation.ofExact (injective_unstableFrame_of_mem hφ hf hy)
        (exact_unstableFrame_neg_stableNormal hφ hf hx hy)
        (surjective_stableNormal_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)
          ((hX.unstableSet_eq_stableSet_neg hf x).subset hy)) op op'
        φ.finrank_negativeWeight_fun (φ.neg hx).finrank_negativeWeight_fun :=
  (rfl)

/-- **The frame orientation along the stable manifold.** At a point `y` of `W^s(x)`, the unstable
frame of `-X` and the normal coordinates of the stable manifold of `x` for `X` form a short exact
sequence `0 → V⁺ → T_y M → V⁻ → 0`. This is the orientation of `T_y M` that it induces from the
orientations `op'` of `V⁺` and `op` of `V⁻`, subspace first (`Orientation.ofExact`). -/
noncomputable def stableNormalOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    {y : M} (hy : y ∈ hX.flow.stableSet x) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x + manifoldMorseIndex 𝓘(ℝ, E) f x)) :=
  Orientation.ofExact
    (injective_unstableFrame_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx) hf.neg
      ((hX.stableSet_eq_unstableSet_neg hf x).subset hy))
    (exact_neg_unstableFrame_stableNormal hφ hf hx hy)
    (surjective_stableNormal_of_mem hφ hy) op' op
    (φ.neg hx).finrank_negativeWeight_fun φ.finrank_negativeWeight_fun

/-- The defining formula of `stableNormalOrientation`. -/
theorem stableNormalOrientation_def (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    {y : M} (hy : y ∈ hX.flow.stableSet x) :
    stableNormalOrientation hφ hf hx op' op hy =
      Orientation.ofExact
        (injective_unstableFrame_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx) hf.neg
          ((hX.stableSet_eq_unstableSet_neg hf x).subset hy))
        (exact_neg_unstableFrame_stableNormal hφ hf hx hy)
        (surjective_stableNormal_of_mem hφ hy) op' op
        (φ.neg hx).finrank_negativeWeight_fun φ.finrank_negativeWeight_fun :=
  (rfl)

/-- **The two frame orientations at the critical point.** At the centre `x` of the chart, the
unstable frame of `X` and that of `-X` are the inclusions of the coordinates of negative and of
positive weight, and the normal coordinates of the stable manifolds of `X` and of `-X` read off
the same coordinates. So `T_x M = V⁻ ⊕ V⁺`, the frame orientation along the stable manifold puts
`V⁺` first and the one along the unstable manifold puts `V⁻` first, and they differ by
`(-1) ^ (ind_f x * ind_{-f} x)`. -/
theorem stableNormalOrientation_self (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (hxs : x ∈ hX.flow.stableSet x) (hxu : x ∈ hX.flow.unstableSet x) :
    stableNormalOrientation hφ hf hx op' op hxs =
      (-1 : ℝˣ) ^ (manifoldMorseIndex 𝓘(ℝ, E) f x * manifoldMorseIndex 𝓘(ℝ, E) (-f) x) •
        Orientation.reindex ℝ _ (finCongr (add_comm _ _))
          (unstableFrameOrientation hφ hf hx op op' hxu) := by
  rw [stableNormalOrientation_def, unstableFrameOrientation_def]
  exact Orientation.ofExact_comm _ _ _ _ _ _ (stableNormal_unstableFrame_self hφ)
    (stableNormal_unstableFrame_self (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)) _ _ _ _

/-! ### Frame orientations read in a chart -/

/-- **The frame orientation along the unstable manifold, read in a chart.** Let `y` be a point of
`W^u(x)` and `T` a time of linear backward flow from `y`. The derivative of `φ ∘ Φ_{-T}` at `y`
carries the frame orientation at `y` to the orientation of the model space to which the
derivative of `φ` at `x` carries the frame orientation at `x`. -/
theorem map_unstableFrameOrientation_eq (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (hxu : x ∈ hX.flow.unstableSet x) {y : M} (hy : y ∈ hX.flow.unstableSet x) {T : ℝ}
    (hT : T ∈ hX.linearBackwardTimes φ y)
    (eDy : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((φ.toChart ∘ hX.flow (-T)) y))
    (heDy : (eDy : TangentSpace 𝓘(ℝ, E) y →L[ℝ] _) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y)
    (eDx : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (φ.toChart x))
    (heDx : (eDx : TangentSpace 𝓘(ℝ, E) x →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x) :
    Orientation.map _ (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E)
        (unstableFrameOrientation hφ hf hx op op' hy) =
      Orientation.map _ (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (unstableFrameOrientation hφ hf hx op op' hxu) := by
  have hx0 := mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.mem_criticalPoints
  rw [unstableFrameOrientation_def, unstableFrameOrientation_def]
  -- Read in the model space, the frame and the normal coordinates at `y` are positive multiples
  -- of those at `x`.
  refine map_ofExact_eq_of_map_eq_smul eDy eDx _ _ _ _ _ _ _ _ _ _ (Real.exp_pos (-T))
    (Real.exp_pos T) (fun c ↦ ?_) (fun w ↦ ?_)
  · have h := mfderiv_unstableFrame_eq_exp_smul_self hφ hx0 hT c
    rw [← heDy, ← heDx, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe] at h
    exact h
  · have hT' : T ∈ (hX.neg hf).linearForwardTimes (φ.neg hx) y := by
      rwa [neg_linearForwardTimes (hX := hX) (φ := φ) hf hx]
    have h0' : (0 : ℝ) ∈ (hX.neg hf).linearForwardTimes (φ.neg hx) x := by
      rw [neg_linearForwardTimes (hX := hX) (φ := φ) hf hx]
      exact mem_linearBackwardTimes_self hx0 0
    simp only [ContinuousLinearMap.coe_coe]
    rw [stableNormal_apply (φ.coord_mfderiv_neg hφ hx) hT',
      stableNormal_apply (φ.coord_mfderiv_neg hφ hx) h0',
      neg_toChart_comp_neg_flow (hX := hX) hf hx, neg_toChart_comp_neg_flow (hX := hX) hf hx,
      neg_zero, Flow.map_zero, comp_id, ← heDy, ← heDx]
    simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
    exact congrArg _ (eDx.apply_symm_apply (eDy w))

/-- **The frame orientation along the stable manifold, read in a chart.** Let `y` be a point of
`W^s(x)` and `T` a time of linear forward flow from `y`. The derivative of `φ ∘ Φ_T` at `y`
carries the frame orientation at `y` to the orientation of the model space to which the
derivative of `φ` at `x` carries the frame orientation at `x`. -/
theorem map_stableNormalOrientation_eq (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (hxs : x ∈ hX.flow.stableSet x) {y : M} (hy : y ∈ hX.flow.stableSet x) {T : ℝ}
    (hT : T ∈ hX.linearForwardTimes φ y)
    (eDy : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((φ.toChart ∘ hX.flow T) y))
    (heDy : (eDy : TangentSpace 𝓘(ℝ, E) y →L[ℝ] _) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y)
    (eDx : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (φ.toChart x))
    (heDx : (eDx : TangentSpace 𝓘(ℝ, E) x →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x) :
    Orientation.map _ (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E)
        (stableNormalOrientation hφ hf hx op' op hy) =
      Orientation.map _ (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (stableNormalOrientation hφ hf hx op' op hxs) := by
  have h0 : (0 : ℝ) ∈ hX.linearForwardTimes φ x :=
    mem_linearForwardTimes_self (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.mem_criticalPoints) 0
  rw [stableNormalOrientation_def, stableNormalOrientation_def]
  refine map_ofExact_eq_of_map_eq_smul eDy eDx _ _ _ _ _ _ _ _ _ _ (Real.exp_pos (-T))
    (Real.exp_pos T) (fun c ↦ ?_) (fun w ↦ ?_)
  · have hT' : T ∈ (hX.neg hf).linearBackwardTimes (φ.neg hx) y := by
      rwa [neg_linearBackwardTimes (hX := hX) (φ := φ) hf hx]
    have h := mfderiv_unstableFrame_eq_exp_smul_self (φ.coord_mfderiv_neg hφ hx)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx.neg.mem_criticalPoints) hT' c
    rw [neg_toChart_comp_neg_flow (hX := hX) hf hx, neg_neg, MorseChart.neg_toChart, ← heDy,
      ← heDx, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe] at h
    exact h
  · simp only [ContinuousLinearMap.coe_coe]
    rw [stableNormal_apply hφ hT, stableNormal_apply hφ h0, Flow.map_zero, comp_id, ← heDy,
      ← heDx]
    simp only [smul_smul, ← Real.exp_add, add_neg_cancel, neg_zero, Real.exp_zero, one_smul]
    exact congrArg _ (eDx.apply_symm_apply (eDy w))

/-- The comparison of the frame orientation along the unstable manifold with `o`, at a point of
`W^u(x)` and at `x`. -/
private theorem reindex_unstableFrameOrientation_eq_orientationAt_iff_self
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E) (-f) x) ≃ ι)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (hxu : x ∈ hX.flow.unstableSet x) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    Orientation.reindex ℝ _ e (unstableFrameOrientation hφ hf hx op op' hy) = o.orientationAt y ↔
      Orientation.reindex ℝ _ e (unstableFrameOrientation hφ hf hx op op' hxu) =
        o.orientationAt x := by
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφ hf hy).exists
  obtain ⟨eDy, heDy⟩ := isInvertible_mfderiv_toChart_comp_flow (hX := hX) (φ := φ)
    ((hX.mem_linearBackwardTimes φ).1 hT).1
  obtain ⟨eDx, heDx⟩ := isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source
  -- Read both tangent spaces in the model space `E`, through `φ ∘ Φ_{-T}` and `φ`, where `o` and
  -- the frame orientations at `y` and at `x` agree.
  refine Orientation.eq_iff_eq_of_map_eq (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E)
    (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E) ?_
    (map_orientationAt_eq_of_mem_linearBackwardTimes hφ o hy hT eDy heDy eDx heDx)
  exact (Orientation.map_reindex _ _ _).trans ((congrArg (Orientation.reindex ℝ E e)
    (map_unstableFrameOrientation_eq hφ hf hx op op' hxu hy hT eDy heDy eDx heDx)).trans
      (Orientation.map_reindex _ _ _).symm)

/-- The comparison of the frame orientation along the stable manifold with `o`, at a point of
`W^s(x)` and at `x`. -/
private theorem reindex_stableNormalOrientation_eq_orientationAt_iff_self
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x + manifoldMorseIndex 𝓘(ℝ, E) f x) ≃ ι)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (hxs : x ∈ hX.flow.stableSet x) {y : M} (hy : y ∈ hX.flow.stableSet x) :
    Orientation.reindex ℝ _ e (stableNormalOrientation hφ hf hx op' op hy) = o.orientationAt y ↔
      Orientation.reindex ℝ _ e (stableNormalOrientation hφ hf hx op' op hxs) =
        o.orientationAt x := by
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearForwardTimes hφ hy).exists
  obtain ⟨eDy, heDy⟩ := isInvertible_mfderiv_toChart_comp_flow (hX := hX) (φ := φ)
    ((hX.mem_linearForwardTimes φ).1 hT).1
  obtain ⟨eDx, heDx⟩ := isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source
  -- Read both tangent spaces in the model space `E`, through `φ ∘ Φ_T` and `φ`, where `o` and the
  -- frame orientations at `y` and at `x` agree.
  refine Orientation.eq_iff_eq_of_map_eq (eDy.toLinearEquiv : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E)
    (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E) ?_
    (map_orientationAt_eq_of_mem_linearForwardTimes hφ o hy hT eDy heDy eDx heDx)
  exact (Orientation.map_reindex _ _ _).trans ((congrArg (Orientation.reindex ℝ E e)
    (map_stableNormalOrientation_eq hφ hf hx op' op hxs hy hT eDy heDy eDx heDx)).trans
      (Orientation.map_reindex _ _ _).symm)

/-- **The frame orientations along the unstable manifold.** Let `o` be an orientation of `M`, and
orient the coordinates of negative weight of a Morse chart `φ` at `x`, in which `X` is linear, by
`op`, and those of positive weight by `op'`. At each point `y` of `W^u(x)`, the unstable frame
of `X` and the normal coordinates of the stable manifold of `x` for `-X` form a short exact
sequence `0 → V⁻ → T_y M → V⁺ → 0`, so `op` and `op'` orient `T_y M` (`unstableFrameOrientation`).
Whether this orientation is the one of `o` does not depend on the point of `W^u(x)`; in
particular, it is the one of `o` everywhere on `W^u(x)` as soon as it is at `x`. -/
theorem reindex_unstableFrameOrientation_eq_orientationAt_iff
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E) (-f) x) ≃ ι)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    {y₁ y₂ : M} (hy₁ : y₁ ∈ hX.flow.unstableSet x) (hy₂ : y₂ ∈ hX.flow.unstableSet x) :
    Orientation.reindex ℝ _ e (unstableFrameOrientation hφ hf hx op op' hy₁) =
        o.orientationAt y₁ ↔
      Orientation.reindex ℝ _ e (unstableFrameOrientation hφ hf hx op op' hy₂) =
        o.orientationAt y₂ :=
  have hxu := hX.mem_unstableSet_self hx.mem_criticalPoints
  (reindex_unstableFrameOrientation_eq_orientationAt_iff_self hφ hf hx o e op op' hxu hy₁).trans
    (reindex_unstableFrameOrientation_eq_orientationAt_iff_self hφ hf hx o e op op' hxu hy₂).symm

/-- **The frame orientations along the stable manifold.** Let `o` be an orientation of `M`, and
orient the coordinates of positive weight of a Morse chart `φ` at `x`, in which `X` is linear, by
`op'`, and those of negative weight by `op`. At each point `y` of `W^s(x)`, the unstable frame
of `-X` and the normal coordinates of the stable manifold of `x` for `X` form a short exact
sequence `0 → V⁺ → T_y M → V⁻ → 0`, so `op'` and `op` orient `T_y M` (`stableNormalOrientation`).
Whether this orientation is the one of `o` does not depend on the point of `W^s(x)`; in
particular, it is the one of `o` everywhere on `W^s(x)` as soon as it is at `x`. -/
theorem reindex_stableNormalOrientation_eq_orientationAt_iff
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x + manifoldMorseIndex 𝓘(ℝ, E) f x) ≃ ι)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    {y₁ y₂ : M} (hy₁ : y₁ ∈ hX.flow.stableSet x) (hy₂ : y₂ ∈ hX.flow.stableSet x) :
    Orientation.reindex ℝ _ e (stableNormalOrientation hφ hf hx op' op hy₁) = o.orientationAt y₁ ↔
      Orientation.reindex ℝ _ e (stableNormalOrientation hφ hf hx op' op hy₂) =
        o.orientationAt y₂ :=
  have hxs := hX.mem_stableSet_self hx.mem_criticalPoints
  (reindex_stableNormalOrientation_eq_orientationAt_iff_self hφ hf hx o e op' op hxs hy₁).trans
    (reindex_stableNormalOrientation_eq_orientationAt_iff_self hφ hf hx o e op' op hxs hy₂).symm


/-- **The frame orientations along the stable manifold, from the order at the critical point.** If
`op` followed by `op'` orients `T_x M` like `o`, then at every point `y` of `W^s(x)` the frame
orientation along the stable manifold, which puts `op'` first, is `(-1) ^ (ind_f x * ind_{-f} x)`
times the orientation of `o`: the factors are exchanged at `x` (`stableNormalOrientation_self`),
and the comparison with `o` does not depend on the point of `W^s(x)`. -/
theorem reindex_stableNormalOrientation_eq_neg_one_pow_smul (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (hop : Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
        hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
      (unstableFrameOrientation hφ hf hx op op' (hX.mem_unstableSet_self hx.mem_criticalPoints)) =
      o.orientationAt x)
    {y : M} (hy : y ∈ hX.flow.stableSet x) :
    Orientation.reindex ℝ _ (finCongr hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank)
        (stableNormalOrientation hφ hf hx op' op hy) =
      (-1 : ℝˣ) ^ (manifoldMorseIndex 𝓘(ℝ, E) f x * manifoldMorseIndex 𝓘(ℝ, E) (-f) x) •
        o.orientationAt y := by
  have hxs := hX.mem_stableSet_self hx.mem_criticalPoints
  have hx' : Orientation.reindex ℝ _
      (finCongr hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank)
      (stableNormalOrientation hφ hf hx op' op hxs) =
      (-1 : ℝˣ) ^ (manifoldMorseIndex 𝓘(ℝ, E) f x * manifoldMorseIndex 𝓘(ℝ, E) (-f) x) •
        o.orientationAt x := by
    rw [stableNormalOrientation_self hφ hf hx op op' hxs
      (hX.mem_unstableSet_self hx.mem_criticalPoints), Orientation.reindex_units_smul,
      Orientation.reindex_finCongr_reindex_finCongr, hop]
  -- Compare with `o` or with `-o` along `W^s(x)`, according to the parity of the exponent.
  rcases Nat.even_or_odd (manifoldMorseIndex 𝓘(ℝ, E) f x * manifoldMorseIndex 𝓘(ℝ, E) (-f) x)
    with hk | hk
  · rw [hk.neg_one_pow, one_smul] at hx' ⊢
    exact (reindex_stableNormalOrientation_eq_orientationAt_iff hφ hf hx o _ op' op hy hxs).2 hx'
  · rw [hk.neg_one_pow, Module.Ray.neg_units_smul, one_smul,
      ← Manifold.Orientation.orientationAt_neg] at hx' ⊢
    exact (reindex_stableNormalOrientation_eq_orientationAt_iff hφ hf hx (-o) _ op' op hy hxs).2 hx'


variable (hX) in
/-- **The complementary orientation.** At the centre `x` of a Morse chart `φ` in which `X` is
linear, the orientation of the coordinates of positive weight `V⁺` such that the orientation `op`
of the coordinates of negative weight `V⁻` followed by it is the orientation `o` of `M` at `x`,
through the exact sequence `0 → V⁻ → T_x M → V⁺ → 0` of `unstableFrameOrientation`. The
coordinates of positive weight are those of negative weight of the negated chart, so this orients
the unstable manifold of `x` for `-X`. -/
noncomputable def complementaryOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))) :
    Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)) :=
  have hxu := hX.mem_unstableSet_self hx.mem_criticalPoints
  Orientation.cokerOfExact (injective_unstableFrame_of_mem hφ hf hxu)
    (exact_unstableFrame_neg_stableNormal hφ hf hx hxu)
    (surjective_stableNormal_of_mem (hX := hX.neg hf) (φ.coord_mfderiv_neg hφ hx)
      ((hX.unstableSet_eq_stableSet_neg hf x).subset hxu)) op
    (Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
      hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank).symm) (o.orientationAt x))
    φ.finrank_negativeWeight_fun (φ.neg hx).finrank_negativeWeight_fun

/-- **The complementary orientation completes `op` to the orientation of `M`.** The orientation
`op` of the coordinates of negative weight followed by the complementary orientation of those of
positive weight is the orientation of `o` at the critical point. -/
theorem reindex_unstableFrameOrientation_complementaryOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))) :
    Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
        hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
      (unstableFrameOrientation hφ hf hx op (hX.complementaryOrientation hφ hf hx o op)
        (hX.mem_unstableSet_self hx.mem_criticalPoints)) =
      o.orientationAt x := by
  rw [unstableFrameOrientation_def, complementaryOrientation, Orientation.ofExact_cokerOfExact,
    Orientation.reindex_finCongr_reindex_finCongr, finCongr_refl, Orientation.reindex_refl,
    Equiv.refl_apply]

/-- **The characterization of the complementary orientation**: it is the only orientation of the
coordinates of positive weight which, following `op`, orients `M` like `o` at the critical
point. -/
theorem complementaryOrientation_eq_iff (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x))) :
    hX.complementaryOrientation hφ hf hx o op = op' ↔
      Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
          hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
        (unstableFrameOrientation hφ hf hx op op'
          (hX.mem_unstableSet_self hx.mem_criticalPoints)) =
        o.orientationAt x := by
  refine ⟨fun h ↦ h ▸ reindex_unstableFrameOrientation_complementaryOrientation hφ hf hx o op,
    fun h ↦ ?_⟩
  rw [complementaryOrientation, Orientation.cokerOfExact_eq_iff, ← h,
    Orientation.reindex_finCongr_reindex_finCongr, finCongr_refl, Orientation.reindex_refl,
    Equiv.refl_apply, unstableFrameOrientation_def]

end IsAdaptedPseudoGradient

end TauCeti
