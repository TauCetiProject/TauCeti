/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Pulling forms back to open subsets of normed spaces

Let `φ : E' → M` be a map from a real normed space to a manifold, smooth on an open set `U`. The
pullback `φ^* η` of a form `η` on `M` (`TauCeti.mpullback`) is then a form on the model space `E'`,
that is, a function `E' → E' [⋀^Fin k]→L[ℝ] F`, which can be handled with the flat calculus of
Mathlib's `extDerivWithin` and `extDeriv`. This file records that this flat form is as good as `η`
on `U`:

* for a smooth form `η`, it is smooth on `U` (`TauCeti.SmoothForm.contDiffOn_mpullback`);
* for a closed smooth form `η`, it is closed at every point of `U`
  (`TauCeti.SmoothForm.IsClosed.extDeriv_mpullback_eq_zero`).

Both are the open-set cases of the corresponding statements for within-set pullbacks,
`ContMDiffAt.mpullback_form` and `TauCeti.extDerivWithin_mpullbackWithin`.

The typical `φ` is the inverse of a chart `e : M → E` other than a preferred one, for instance a
chart adapted to a group action, so that a form on `M` can be read in that chart and fed to flat
results such as Moser's lemma. When `e` is differentiable in both directions, pulling
`(e.symm)^* η` back along `e` recovers `η` on the source of `e`
(`OpenPartialHomeomorph.mpullback_mpullback_symm_apply`), so `η` is determined by its reading in
`e`. If `e` intertwines a self-map `f` of `M` preserving `η` with a map `A` of `E`, for instance the
action of a group element in an equivariant chart, the reading of `η` in `e` is `A`-invariant
(`OpenPartialHomeomorph.mpullback_mpullback_symm_apply_of_intertwines`).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {φ : E' → M} {U : Set E'}

omit [IsManifold I ∞ M] in
/-- Reading a form through the inverse of a partial homeomorphism `e : M → E` and pulling the
result back along `e` recovers the form at a point of the source of `e` where `e` and `e.symm` are
differentiable. -/
theorem _root_.OpenPartialHomeomorph.mpullback_mpullback_symm_apply (e : OpenPartialHomeomorph M E)
    (η : RoughForm I M F k) {x : M} (hx : x ∈ e.source) (hd : MDifferentiableAt I 𝓘(ℝ, E) e x)
    (hds : MDifferentiableAt 𝓘(ℝ, E) I e.symm (e x)) :
    mpullback I 𝓘(ℝ, E) e (mpullback 𝓘(ℝ, E) I e.symm η) x = η x := by
  have hid : e.symm ∘ e =ᶠ[𝓝 x] id := e.eventually_left_inverse hx
  rw [← mpullback_comp_at hd hds, hid.mpullback_eq, mpullback_id]

omit [IsManifold I ∞ M] in
/-- Let `e : M → E` be a partial homeomorphism, differentiable in the inverse direction, which
intertwines a self-map `f` of its source preserving the form `η` with a map `A` of `E`. Then `η`
read through `e.symm` is `A`-invariant at every point `y` of the target of `e` where `A` and `f`
are differentiable. -/
theorem _root_.OpenPartialHomeomorph.mpullback_mpullback_symm_apply_of_intertwines
    (e : OpenPartialHomeomorph M E) (hes : MDifferentiableOn 𝓘(ℝ, E) I e.symm e.target)
    {f : M → M} {A : E → E} {η : RoughForm I M F k} (hηf : mpullback I I f η = η)
    (hA : ∀ z ∈ e.source, f z ∈ e.source ∧ e (f z) = A (e z)) {y : E} (hy : y ∈ e.target)
    (hAd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) A y) (hf : MDifferentiableAt I I f (e.symm y)) :
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) A (mpullback 𝓘(ℝ, E) I e.symm η) y =
      mpullback 𝓘(ℝ, E) I e.symm η y := by
  have hds {z : E} (hz : z ∈ e.target) : MDifferentiableAt 𝓘(ℝ, E) I e.symm z :=
    (hes z hz).mdifferentiableAt (e.open_target.mem_nhds hz)
  have heq : e.symm ∘ A =ᶠ[𝓝 y] f ∘ e.symm := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact (e.symm_map_of_intertwines hA hz).2
  rw [← mpullback_comp_at hAd (hds (e.symm_map_of_intertwines hA hy).1), heq.mpullback_eq,
    mpullback_comp_at (hds hy) hf, hηf]

namespace SmoothForm

/-- The pullback of a smooth form along a map from a normed space, smooth on an open set `U`, is
smooth on `U` as a flat form. -/
theorem contDiffOn_mpullback (η : SmoothForm I M F k) (hU : IsOpen U)
    (hφ : ContMDiffOn 𝓘(ℝ, E') I ∞ φ U) :
    ContDiffOn ℝ (E := E') (F := E' [⋀^Fin k]→L[ℝ] F) ∞
      (TauCeti.mpullback 𝓘(ℝ, E') I φ η.1) U := fun y hy ↦
  RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
    ((η.contMDiff (φ y)).mpullback_form ((hφ y hy).contMDiffAt (hU.mem_nhds hy))
      (by simp)).contMDiffWithinAt

/-- The pullback of a closed smooth form along a map from a normed space, smooth on an open set
`U`, is closed at every point of `U` as a flat form. -/
theorem IsClosed.extDeriv_mpullback_eq_zero {η : SmoothForm I M F k} (hη : η.IsClosed)
    (hU : IsOpen U) (hφ : ContMDiffOn 𝓘(ℝ, E') I 2 φ U) {y : E'} (hy : y ∈ U) :
    extDeriv (TauCeti.mpullback 𝓘(ℝ, E') I φ η.1 : E' → E' [⋀^Fin k]→L[ℝ] F) y = 0 := by
  -- On the open set `U`, the pullback is the within-set pullback, whose exterior derivative is
  -- the pullback of `dη = 0`.
  have hloc : EventuallyEq (𝓝 y) (β := E' [⋀^Fin k]→L[ℝ] F)
      (TauCeti.mpullback 𝓘(ℝ, E') I φ η.1) (TauCeti.mpullbackWithin 𝓘(ℝ, E') I φ U η.1) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact (TauCeti.mpullbackWithin_eq_mpullback (F := F) (hU.uniqueMDiffOn z hz)
      (((hφ z hz).contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp)) η.1).symm
  have h := extDerivWithin_mpullbackWithin (hφ y hy) hU.uniqueDiffOn
    (subset_closure (by rwa [hU.interior_eq])) hy
    ((η.contMDiff (φ y)).mdifferentiableAt (by simp))
  rw [(isClosed_def η).1 hη, TauCeti.mpullbackWithin_zero] at h
  exact hloc.extDeriv_eq.trans ((extDerivWithin_of_isOpen hU hy).symm.trans h)

end SmoothForm

end TauCeti
