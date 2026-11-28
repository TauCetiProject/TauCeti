/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Annulus.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Annulus.Line
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Conformal.Jordan.Annulus
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# The low-dimensional annulus theorem

This file proves the `n = 1` (`ℝ²`) case of the annulus conjecture without any local flatness
hypothesis, in any two-dimensional real normed space, and combines it with the `n = 0` (`ℝ¹`) case
from `TauCeti.Geometry.Manifold.LocallyFlat.Annulus.Line` to establish
`TauCeti.AnnulusConjecture n` for `n ≤ 1`.

* In dimension `2` (`n = 1`), continuous injections `S¹ → ℂ` trace nested Jordan curves, which
  cobound an annulus by the planar annulus theorem
  (`TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`), and transport along
  `ContinuousLinearEquiv.ofFinrankEq` and `TauCeti.sphereHomeomorphOfFinrankEq` yields
  `TauCeti.coboundAnnulus_of_continuous_injective_of_finrank_eq_two`,
  `TauCeti.annulusConjecture_one`, and `TauCeti.annulusConjecture_of_le_one`.

## Main results

* `TauCeti.coboundAnnulus_of_continuous_injective_of_finrank_eq_two`: any two nested continuous
  injections `S¹ → E` in a two-dimensional real normed space cobound an annulus.
* `TauCeti.annulusConjecture_one`, `TauCeti.annulusConjecture_of_le_one`: the annulus conjecture
  holds for `n = 1` and for `n ≤ 1`.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Metric Set

/-! ### Spheres of dimension one -/

section DimensionOne

open Function

private theorem coboundAnnulus_of_continuous_injective_complex {f g : sphere (0 : ℂ) 1 → ℂ}
    (hfc : Continuous f) (hfi : Injective f) (hgc : Continuous g) (hgi : Injective g)
    (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have hC₁ : IsJordanCurve (range f) :=
    (sphereCircleHomeomorph 0 one_pos).isJordanCurve_range hfc hfi
  have hC₂ : IsJordanCurve (range g) :=
    (sphereCircleHomeomorph 0 one_pos).isJordanCurve_range hgc hgi
  rw [coboundAnnulus_iff_exists_homeomorph]
  exact hC₁.exists_homeomorph_sphere_prod_unitInterval hC₂ hsub

/-- **The two-dimensional annulus theorem in any two-dimensional real normed space.** Any two
continuous injections `f g : sphere (0 : E) 1 → E` with
`range g ⊆ filledHull (range f) \ range f` cobound an annulus. No local flatness hypothesis is
needed. -/
theorem coboundAnnulus_of_continuous_injective_of_finrank_eq_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Module.finrank ℝ E = 2) {f g : sphere (0 : E) 1 → E}
    (hfc : Continuous f) (hfi : Injective f) (hgc : Continuous g) (hgi : Injective g)
    (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have hEF : Module.finrank ℝ E = Module.finrank ℝ ℂ := by simp [hE]
  let e : E ≃ₜ ℂ := (ContinuousLinearEquiv.ofFinrankEq hEF).toHomeomorph
  let es : sphere (0 : E) 1 ≃ₜ sphere (0 : ℂ) 1 := sphereHomeomorphOfFinrankEq hEF
  have he : ∀ s : Set E, IsBounded (e '' s) ↔ IsBounded s := fun _ => e.isBounded_image_iff
  rw [← coboundAnnulus_homeomorph_comp_iff e he, ← coboundAnnulus_comp_homeomorph_iff es.symm]
  exact coboundAnnulus_of_continuous_injective_complex
    (e.continuous.comp (hfc.comp es.symm.continuous))
    (e.injective.comp (hfi.comp es.symm.injective))
    (e.continuous.comp (hgc.comp es.symm.continuous))
    (e.injective.comp (hgi.comp es.symm.injective))
    (by simpa only [range_comp, es.symm.surjective.range_comp] using
      (e.image_subset_filledHull_sdiff_iff he (range g) (range f)).mpr hsub)

/-- **The annulus conjecture holds in dimension `2` (`n = 1`).** -/
theorem annulusConjecture_one : AnnulusConjecture 1 := by
  rw [annulusConjecture_iff]
  exact fun _ _ hf hg hsub =>
    coboundAnnulus_of_continuous_injective_of_finrank_eq_two (by simp)
      hf.continuous hf.injective hg.continuous hg.injective hsub

/-- **The annulus conjecture holds in dimensions `1` and `2` (`n ≤ 1`).** -/
theorem annulusConjecture_of_le_one {n : ℕ} (hn : n ≤ 1) : AnnulusConjecture n := by
  match n with
  | 0 => exact annulusConjecture_zero
  | 1 => exact annulusConjecture_one

end DimensionOne

end TauCeti
