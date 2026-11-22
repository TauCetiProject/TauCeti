/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Topological homotopies from smooth homotopies

A `C^k` map `F : ℝ × M → N` between charted spaces with `F (0, ·) = f` and `F (1, ·) = g`
restricts to `[0, 1] × M` as a `TopCat.Homotopy` between the morphisms induced by `f` and `g`
(`TauCeti.topCatHomotopyOfContMDiff`).

## Main definitions and results

* `TauCeti.topCatHomotopyOfContMDiff`: the `TopCat.Homotopy` on `[0, 1] × M` restricted from a
  `C^k` map `F : ℝ × M → N`.
* `TauCeti.topCatHomotopyOfContMDiff_apply`: evaluation formula for `topCatHomotopyOfContMDiff`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {f g : M → N} {F : ℝ × M → N}

/-- A `C^k` map `F : ℝ × M → N` with `F (0, ·) = f` and `F (1, ·) = g` restricts to `[0, 1] × M`
as a `TopCat.Homotopy` between the morphisms induced by `f` and `g`. -/
def topCatHomotopyOfContMDiff {k : ℕ∞ω} (hf : ContMDiff I J k f) (hg : ContMDiff I J k g)
    (hF : ContMDiff (𝓘(ℝ).prod I) J k F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    TopCat.Homotopy (TopCat.ofHom ⟨f, hf.continuous⟩) (TopCat.ofHom ⟨g, hg.continuous⟩) where
  toFun p := F (p.1, p.2)
  continuous_toFun := hF.continuous.comp (continuous_subtypeVal.prodMap continuous_id)
  map_zero_left := h₀
  map_one_left := h₁

/-- Evaluating `topCatHomotopyOfContMDiff` on `[0, 1] × M` applies the ambient map `F`. -/
@[simp]
theorem topCatHomotopyOfContMDiff_apply {k : ℕ∞ω} (hf : ContMDiff I J k f)
    (hg : ContMDiff I J k g) (hF : ContMDiff (𝓘(ℝ).prod I) J k F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) (p : unitInterval × M) :
    topCatHomotopyOfContMDiff hf hg hF h₀ h₁ p = F (p.1, p.2) := by
  rfl

end TauCeti
