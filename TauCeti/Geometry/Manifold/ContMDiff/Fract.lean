/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Topology.Algebra.Order.Floor

/-!
# Smoothness of periodizations

A `C^n` map `G : X × ℝ → M` which is periodic in its second coordinate near `0`, in the sense that
`G (y, t + 1) = G (y, t)` for `t` slightly below `0`, has a `C^n` periodization
`(y, t) ↦ G (y, fract t)` (`ContMDiff.comp_fract_snd`): near every point it is a translate of `G`
(`TauCeti.apply_fract_snd_eventuallyEq`).
-/

public section

open scoped Manifold ContDiff

variable {E F HX H X M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace HX] {J : ModelWithCorners ℝ E HX} [TopologicalSpace X]
  [ChartedSpace HX X] [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [TopologicalSpace M]
  [ChartedSpace H M] {n : WithTop ℕ∞} {G : X × ℝ → M} {ε : ℝ}

/-- The periodization `(y, t) ↦ G (y, fract t)` in the second coordinate of a `C^n` map `G` which
is periodic in its second coordinate near `0` is `C^n`. -/
theorem ContMDiff.comp_fract_snd (hG : ContMDiff (J.prod 𝓘(ℝ, ℝ)) I n G) (hε : 0 < ε)
    (hper : ∀ y {t : ℝ}, -ε < t → t < 0 → G (y, t + 1) = G (y, t)) :
    ContMDiff (J.prod 𝓘(ℝ, ℝ)) I n fun w : X × ℝ ↦ G (w.1, Int.fract w.2) := fun z ↦
  ((hG.comp (contMDiff_fst.prodMk
    ((contDiff_id.sub contDiff_const).contMDiff.comp contMDiff_snd))) z).congr_of_eventuallyEq
    (TauCeti.apply_fract_snd_eventuallyEq hε hper z)
