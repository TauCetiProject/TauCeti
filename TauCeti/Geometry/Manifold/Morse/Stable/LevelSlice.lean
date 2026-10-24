/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Level slices of transverse trajectories of an adapted pseudo-gradient

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient field adapted to `f`, and `a ≠ b` critical points of `f`. Along a trajectory from
`a` to `b` the function `f` strictly decreases from `f a` to `f b`, so the trajectory crosses each
intermediate level `{f = c}` exactly once
(`TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet`). The
level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` therefore contains one point of each unparametrized
trajectory from `a` to `b`.

This file shows that, where `W^u(a)` and `W^s(b)` meet transversally, the slice is an embedded
submanifold of dimension `ind a - ind b - 1`. The level `{f = c}` cuts `W^u(a) ∩ W^s(b)`
transversally: the velocity `X y` of the trajectory through a point `y` of the slice is tangent to
`W^u(a) ∩ W^s(b)`, while `df_y (X y) < 0`. Hence a chart of the maximal atlas flattens the slice
onto the tangent space of `W^u(a) ∩ W^s(b)` at `y` cut by `ker df_y`, which has one dimension less.

Under the Morse–Smale condition the slice is therefore a smooth manifold of dimension
`ind a - ind b - 1`, and when the Morse indices differ by one it is discrete: its points are the
isolated trajectories that the Morse differential counts. These are the manifold forms of the
results of `TauCeti.Analysis.Calculus.Morse.TrajectorySpace` for a negative-gradient flow on a
vector space.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet`: a
  trajectory from `a` to `b` crosses each value strictly between `f b` and `f a` exactly once.
* `TauCeti.IsAdaptedPseudoGradient.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top`:
  every level of `f` is transverse to `W^u(a) ∩ W^s(b)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_inter_stableSet_level_chart`: under
  transversality, a chart of the maximal atlas flattens the level slice.
* `TauCeti.IsAdaptedPseudoGradient.span_mtangentConeAt_unstableSet_inter_stableSet_level`: its
  tangent space is the intersection of the tangent spaces of `W^u(a)` and `W^s(b)` with
  `ker df_y`.
* `finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex` (in the
  namespace `TauCeti.IsAdaptedPseudoGradient`): the slice has dimension `ind a - ind b - 1`.
* `TauCeti.IsAdaptedPseudoGradient.isDiscrete_unstableSet_inter_stableSet_level`: if the Morse
  indices differ by one, the transverse slice is discrete.
* `IsMorseSmale.exists_unstableSet_inter_stableSet_level_isManifold` (in the namespace
  `TauCeti.IsAdaptedPseudoGradient`): under the Morse–Smale condition, the slice is a smooth
  manifold of dimension `ind a - ind b - 1`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of trajectories).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b y : M} {c : ℝ}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- Along a trajectory joining distinct critical points, `df_y (X y) < 0`, read in the preferred
chart at `y`. -/
private theorem fderiv_comp_chartAt_symm_apply_lt_zero (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) (X y) < 0 := by
  rw [MDifferentiableAt.fderiv_comp_chartAt_symm hd]
  exact hX.mvfderiv_apply_lt_zero y (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hab hy)

/-- Along a trajectory joining distinct critical points, `df_y` is onto `ℝ`, read in the preferred
chart at `y`: it does not vanish on `X y`. -/
private theorem surjective_fderiv_comp_chartAt_symm (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Function.Surjective (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y)) := by
  -- A linear form that is negative on some vector `v` of the model space is nonzero.
  have key : ∀ v : E, fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) v < 0 →
      (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ) ≠ 0 := fun v hv h0 ↦
    hv.ne (by rw [← ContinuousLinearMap.coe_coe, h0, LinearMap.zero_apply])
  exact LinearMap.surjective_of_ne_zero
    (key _ (hX.fderiv_comp_chartAt_symm_apply_lt_zero hd hab hy))

/-- **A trajectory crosses each intermediate level exactly once.** Along a trajectory from a
critical point `a` to a different critical point `b`, the function `f` strictly decreases from
`f a` to `f b`, so it takes each value `c` with `f b < c < f a` at exactly one time. -/
theorem existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (hbc : f b < c)
    (hca : c < f a) :
    ∃! t : ℝ, f (hX.flow t y) = c := by
  have hfc : Continuous f := hf.continuous
  have hγ : Continuous fun t ↦ f (hX.flow t y) :=
    hfc.comp (hX.contMDiff_flow_uncurry.continuous.comp (continuous_id.prodMk continuous_const))
  -- The trajectory never meets a critical point, so `f` is strictly antitone along it.
  have hanti : StrictAnti fun t ↦ f (hX.flow t y) :=
    hX.strictAnti_comp (fun _ ↦ hf _)
      (hX.isMIntegralCurve_flow y) fun t ↦ hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet
        hab (hX.flow.isInvariant_unstableSet_inter_stableSet a b t hy)
  have hbot : Tendsto (fun t ↦ f (hX.flow t y)) atBot (𝓝 (f a)) :=
    (hfc.tendsto a).comp (Flow.mem_unstableSet.1 hy.1)
  have htop : Tendsto (fun t ↦ f (hX.flow t y)) atTop (𝓝 (f b)) :=
    (hfc.tendsto b).comp (Flow.mem_stableSet.1 hy.2)
  obtain ⟨t, ht⟩ := mem_range_of_exists_le_of_exists_ge hγ
    ((htop.eventually (eventually_lt_nhds hbc)).exists.imp fun _ h ↦ h.le)
    ((hbot.eventually (eventually_gt_nhds hca)).exists.imp fun _ h ↦ h.le)
  exact ⟨t, ht, fun s hs ↦ hanti.injective (hs.trans ht.symm)⟩

/-- **Levels are transverse to connecting trajectories.** At a point `y` of `W^u(a) ∩ W^s(b)` with
`a ≠ b`, the tangent space of `W^u(a) ∩ W^s(b)` and the kernel of `df_y`, the tangent space of the
level of `f` through `y`, span the tangent space of `M`. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊔
      (mvfderiv 𝓘(ℝ, E) f y).ker = ⊤ := by
  have hmem := hX.mem_span_mtangentConeAt_unstableSet_inter_stableSet hy
  rw [hf.ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm]
  refine top_unique ?_
  rw [← LinearMap.span_singleton_sup_ker_eq_top
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ)
    (hX.fderiv_comp_chartAt_symm_apply_lt_zero hf hab hy).ne]
  exact sup_le_sup_right ((Submodule.span_singleton_le_iff_mem (R := ℝ) (M := E) _ _).2 hmem) _

/-- Under transversality, the level slice through `y` is cut out of `W^u(a) ∩ W^s(b)` by a
transverse regular level set: it is flattened by a chart of the maximal atlas, and its tangent
space is that of `W^u(a) ∩ W^s(b)` cut by `ker df_y`. -/
private theorem level_slice (hf : IsMorse 𝓘(ℝ, E) f) (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0)
    (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    (∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ
          (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊓
          (mvfderiv 𝓘(ℝ, E) f y).ker : Submodule ℝ E) : Set E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c})) ∧
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y) =
      Submodule.span ℝ
          (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊓
        (mvfderiv 𝓘(ℝ, E) f y).ker := by
  obtain ⟨q, hyq, hq, hs⟩ := hX.exists_unstableSet_inter_stableSet_chart hf ha hb hy htr
  rw [← hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy htr] at hs
  -- The level `{f = c}` is a regular level set near `y`, since `df_y (X y) < 0`.
  have hlevel : {x | f x = c} = f ⁻¹' {c} := by
    ext
    simp
  have hrange : (mvfderiv 𝓘(ℝ, E) f y).range = ⊤ := by
    rw [← MDifferentiableAt.fderiv_comp_chartAt_symm (hf.contMDiff.mdifferentiable (by simp) y)]
    exact LinearMap.range_eq_top_of_surjective _
      (hX.surjective_fderiv_comp_chartAt_symm (hf.contMDiff.mdifferentiable (by simp) y) hab hy)
  have htr' := hX.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top
    (hf.contMDiff.mdifferentiable (by simp) y) hab hy
  rw [hlevel]
  exact ⟨exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (by simp) hq hs
      hyq hy isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn hyc hrange htr',
    span_mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (by simp) hq hs hyq
      hy isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn hyc hrange htr'⟩

/-- **The level slice of a transverse intersection is an embedded submanifold.** If the unstable
manifold of a critical point `a` and the stable manifold of a different critical point `b` meet
transversally at `y`, and `f y = c`, then near `y` a chart of the maximal atlas flattens the level
slice `W^u(a) ∩ W^s(b) ∩ {f = c}` onto the intersection of the tangent spaces of `W^u(a)` and
`W^s(b)` with `ker df_y`. -/
theorem exists_unstableSet_inter_stableSet_level_chart (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) ⊓
          (mvfderiv 𝓘(ℝ, E) f y).ker : Submodule ℝ E) : Set E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) := by
  obtain ⟨⟨q, hyq, hq, hs⟩, -⟩ := hX.level_slice hf ha hb hab hy htr hyc
  rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy htr] at hs
  exact ⟨q, hyq, hq, hs⟩

/-- **The tangent space of a transverse level slice.** If the unstable manifold of a critical point
`a` and the stable manifold of a different critical point `b` meet transversally at `y`, and
`f y = c`, then the tangent space of the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` at `y` is the
intersection of the tangent spaces of `W^u(a)` and `W^s(b)` with `ker df_y`. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet_level (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) ⊓
        (mvfderiv 𝓘(ℝ, E) f y).ker := by
  rw [(hX.level_slice hf ha hb hab hy htr hyc).2,
    hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy htr]

/-- **The level slice has dimension the index difference minus one.** If the unstable manifold of a
critical point `a` and the stable manifold of a different critical point `b` meet transversally at
`y`, then the tangent space at `y` of the level slice `W^u(a) ∩ W^s(b) ∩ {f = f y}` has dimension
`ind a - ind b - 1`. -/
theorem finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex
    (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f b + 1 = manifoldMorseIndex 𝓘(ℝ, E) f a := by
  have hd := hf.contMDiff.mdifferentiable (by simp)
  have hsup := hX.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top (hd y) hab hy
  have hslice := (hX.level_slice hf ha hb hab hy htr hyc).2
  rw [(hd y).ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm] at hsup hslice
  -- Cutting by the hyperplane `ker df_y`, which is transverse, lowers the dimension by one.
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y))
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y)).ker
  rw [hsup, finrank_top, ← hslice] at hdim
  have hker := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ)
  rw [LinearMap.range_eq_top_of_surjective _
      (hX.surjective_fderiv_comp_chartAt_symm (hd y) hab hy), finrank_top,
    Module.finrank_self] at hker
  have hW :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf ha hb hy
      htr
  omega

/-- **Index-difference-one level slices are discrete.** If the Morse indices of critical points `a`
and `b` differ by one and the unstable manifold of `a` meets the stable manifold of `b`
transversally at every point of the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}`, then the slice is
discrete: each of the trajectories it parametrizes is isolated. -/
theorem isDiscrete_unstableSet_inter_stableSet_level (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1)
    (htr : ∀ y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c},
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    IsDiscrete (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) := by
  have hab : a ≠ b := by rintro rfl; omega
  refine isDiscrete_of_forall_exists_isSliceChart_zero (F := E) fun y hy ↦ ?_
  have htry := htr y hy
  obtain ⟨hyab, hyc⟩ := hy
  -- The slice is zero-dimensional, so the chart at `y` flattens it onto the point `0`.
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf ha
      hb hab hyab htry hyc
  obtain ⟨q, hyq, -, hq⟩ :=
    hX.exists_unstableSet_inter_stableSet_level_chart hf ha hb hab hyab htry hyc
  have h0 : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y)) = 0 := by
    omega
  rw [← hX.span_mtangentConeAt_unstableSet_inter_stableSet_level hf ha hb hab hyab htry hyc,
    Submodule.finrank_eq_zero.1 h0, Submodule.bot_coe] at hq
  exact ⟨q, hyq, hq⟩

omit hX in
/-- **Spaces of unparametrized trajectories are manifolds.** Under the Morse–Smale condition, if
some trajectory from a critical point `a` to a different critical point `b` crosses the level
`{f = c}`, then the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` carries a smooth manifold structure,
modelled on a subspace of dimension `ind a - ind b - 1`, with its subspace topology and a smooth
inclusion into `M`. -/
theorem IsMorseSmale.exists_unstableSet_inter_stableSet_level_isManifold
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f b + 1 =
        manifoldMorseIndex 𝓘(ℝ, E) f a ∧
      ∃ C : ChartedSpace L ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}),
        letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) → M) := by
  obtain ⟨y₀, hy₀, hy₀c⟩ := hne
  have htr₀ := h.span_mtangentConeAt_sup_eq_top ha hb hy₀
  have hdim₀ :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf ha
      hb hab hy₀ htr₀ hy₀c
  -- Every tangent space of the slice has dimension `ind a - ind b - 1`; model it on one of them.
  refine ⟨Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y₀), hdim₀,
    exists_isManifold_of_finrankSubspaceCharts fun y hy ↦ ?_⟩
  obtain ⟨hyab, hyc⟩ := hy
  have htry := h.span_mtangentConeAt_sup_eq_top ha hb hyab
  obtain ⟨q, hyq, hq, hs⟩ :=
    hX.exists_unstableSet_inter_stableSet_level_chart hf ha hb hab hyab htry hyc
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf ha
      hb hab hyab htry hyc
  rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet_level hf ha hb hab hyab htry
    hyc] at hdim
  exact ⟨q, _, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, isSliceChart_iff.1 hs, by omega⟩

end IsAdaptedPseudoGradient

end TauCeti
