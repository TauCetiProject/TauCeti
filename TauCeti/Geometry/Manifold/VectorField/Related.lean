/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Lie brackets of related vector fields

Let `f : N → M` be a map of manifolds. A vector field `V` on `N` and a vector field `V'` on `M` are
*`f`-related* when `df_z (V z) = V' (f z)` for every `z`. The Lie bracket is natural for this
relation: if `V, V'` and `W, W'` are `f`-related, then so are `[V, W]` and `[V', W']`. This file
proves the pointwise form of this statement, with the relations only assumed near the point.

Unlike Mathlib's `VectorField.mpullback_mlieBracket`, no invertibility of the derivative of `f` is
assumed, so the statement applies to maps that are neither immersions nor submersions. The basic
example is the orbit map `g ↦ g • x` of a Lie group action, which relates the right-invariant
vector fields of the group to the fundamental vector fields of the action.

## Main results

* `TauCeti.mfderiv_mlieBracket_of_eventually_related`: if `V, V'` and `W, W'` are `f`-related near
  `y`, then `df_y ([V, W] y) = [V', W'] (f y)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer, 2013, Chapter 8 (naturality of the Lie bracket for `F`-related vector fields).
-/

public section

noncomputable section

open Filter Manifold VectorField
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (minSmoothness 𝕜 2) M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J (minSmoothness 𝕜 2) N]

namespace TauCeti

/-- **Naturality of the Lie bracket.** Let `f : N → M` be `C²` at `y`, and let the differentiable
vector fields `V, W` on `N` be `f`-related near `y` to the vector fields `V', W'` on `M`, which are
differentiable at `f y`: `df_z (V z) = V' (f z)` and `df_z (W z) = W' (f z)` for `z` near `y`. Then
`df_y ([V, W] y) = [V', W'] (f y)`. -/
theorem mfderiv_mlieBracket_of_eventually_related {f : N → M} {V W : Π y : N, TangentSpace J y}
    {V' W' : Π x : M, TangentSpace I x} {y : N}
    (hf : CMDiffAt n f y) (hn : minSmoothness 𝕜 2 ≤ n)
    (hV : MDiffAt (T% V) y) (hW : MDiffAt (T% W) y)
    (hV' : MDiffAt (T% V') (f y)) (hW' : MDiffAt (T% W') (f y))
    (hVV' : ∀ᶠ z in 𝓝 y, mfderiv J I f z (V z) = V' (f z))
    (hWW' : ∀ᶠ z in 𝓝 y, mfderiv J I f z (W z) = W' (f z)) :
    mfderiv J I f y (mlieBracket J V W y) = mlieBracket I V' W' (f y) := by
  /- Test both sides against the extended chart `c` of `M` at `f y`, through the commutator formula
  `mvfderiv_mlieBracket` for `c ∘ f` on `N` and the characterization
  `eq_mlieBracket_of_mvfderiv_extChartAt` on `M`. -/
  have h1 : (1 : ℕ∞ω) ≤ minSmoothness 𝕜 2 :=
    (show (1 : ℕ∞ω) ≤ 2 by norm_num).trans le_minSmoothness
  have : IsManifold I 1 M := .of_le h1
  have : IsManifold J 1 N := .of_le h1
  set c := extChartAt I (f y)
  have hc : CMDiffAt (minSmoothness 𝕜 2) c (f y) := contMDiffAt_extChartAt
  have hf2 : CMDiffAt (minSmoothness 𝕜 2) f y := hf.of_le hn
  have hfy : MDiffAt f y := (hf2.of_le h1).mdifferentiableAt one_ne_zero
  have hcy : MDiffAt c (f y) := (hc.of_le h1).mdifferentiableAt one_ne_zero
  -- Near `y`, `f` is differentiable and lands in the chart source, so the chain rule applies.
  have hfd : ∀ᶠ z in 𝓝 y, MDiffAt f z :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hf2.of_le h1)).mono
      fun z hz ↦ hz.mdifferentiableAt one_ne_zero
  have hsrc : ∀ᶠ z in 𝓝 y, f z ∈ (chartAt H (f y)).source :=
    hf2.continuousAt.preimage_mem_nhds (chart_source_mem_nhds H (f y))
  -- Near `y`, differentiating `c ∘ f` along a field differentiates `c` along the related field.
  have hpush (U : Π y : N, TangentSpace J y) (U' : Π x : M, TangentSpace I x)
      (hUU' : ∀ᶠ z in 𝓝 y, mfderiv J I f z (U z) = U' (f z)) :
      (fun z ↦ mvfderiv J (c ∘ f) z (U z)) =ᶠ[𝓝 y]
        (fun x ↦ mvfderiv I c x (U' x)) ∘ f := by
    filter_upwards [hfd, hsrc, hUU'] with z hz hzs hzU
    rw [Function.comp_apply, mvfderiv_comp_apply z
      ((contMDiffAt_extChartAt' (n := 1) hzs).mdifferentiableAt one_ne_zero) hz, hzU]
  -- At `y`, differentiating such a composite along a related vector reads it at `f y`.
  have houter (U U' : Π x : M, TangentSpace I x) (hU : MDiffAt (T% U) (f y))
      (u : TangentSpace J y) (hu : mfderiv J I f y u = U' (f y)) :
      mvfderiv J ((fun x ↦ mvfderiv I c x (U x)) ∘ f) y u =
        mvfderiv I (fun x ↦ mvfderiv I c x (U x)) (f y) (U' (f y)) := by
    rw [mvfderiv_comp_apply y (mdifferentiableAt_mvfderiv_apply hc le_rfl hU) hfy, hu]
  have key := mvfderiv_mlieBracket (hc.comp y hf2) le_rfl hV hW
  rw [(hpush W W' hWW').mvfderiv_eq, (hpush V V' hVV').mvfderiv_eq,
    houter W' V' hW' (V y) hVV'.self_of_nhds, houter V' W' hV' (W y) hWW'.self_of_nhds,
    mvfderiv_comp_apply y hcy hfy] at key
  exact eq_mlieBracket_of_mvfderiv_extChartAt hV' hW' key

end TauCeti
