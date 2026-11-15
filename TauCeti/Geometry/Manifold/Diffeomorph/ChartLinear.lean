/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Maps which are linear in the preferred charts

Let `M₁` and `M₂` be manifolds modelled on normed spaces `E₁` and `E₂` themselves. Suppose a
continuous map `g : M₁ → M₂` reads, near a point `p`, as a fixed map `L : E₁ → E₂` in the
preferred charts at `p` and at `g p`:

`chartAt E₂ (g p) (g q) = L (chartAt E₁ p q)` for all `q` near `p`.

Then `g` is `C^n` at `p` whenever `L` is `C^n` at the chart image of `p`
(`TauCeti.contMDiffAt_of_eventually_chartAt_apply_eq`). A homeomorphism which reads in this way as
one continuous linear equivalence `L` near every point is a diffeomorphism of every smoothness
(`Homeomorph.toDiffeomorphOfChartAt`): its inverse reads as `L.symm`.

This is how two atlases on the same points, built from the same coordinates up to a linear
change of model, are compared. For instance, the boundary charts of a manifold with boundary and
the charts of a submanifold may both be read from the same ambient coordinates, but take values in
different model spaces.
-/

public section

open Function Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂]
  [NormedSpace 𝕜 E₂] {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace E₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace E₂ M₂] {n : ℕ∞ω}

/-- A continuous map which, near a point `p`, reads as a fixed map `L` in the preferred charts at
`p` and at `g p` is `C^n` at `p` when `L` is `C^n` at the chart image of `p`. -/
theorem contMDiffAt_of_eventually_chartAt_apply_eq {g : M₁ → M₂} {p : M₁} (hg : ContinuousAt g p)
    {L : E₁ → E₂} (hL : ContDiffAt 𝕜 n L (chartAt E₁ p p))
    (h : ∀ᶠ q in 𝓝 p, chartAt E₂ (g p) (g q) = L (chartAt E₁ p q)) :
    ContMDiffAt 𝓘(𝕜, E₁) 𝓘(𝕜, E₂) n g p := by
  rw [contMDiffAt_iff]
  refine ⟨hg, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, CompTriple.comp_eq]
  refine (hL.congr_of_eventuallyEq ?_).contDiffWithinAt
  -- Near the chart image of `p`, the inverse chart lands where `h` holds.
  filter_upwards [((chartAt E₁ p).eventually_nhds' _ (mem_chart_source E₁ p)).2 h,
    (chartAt E₁ p).open_target.mem_nhds (mem_chart_target E₁ p)] with z hz hzt
  rw [comp_apply, comp_apply, hz, (chartAt E₁ p).right_inv hzt]

/-- A continuous map which, near every point `p`, reads as a fixed `C^n` map `L` in the preferred
charts at `p` and at `g p` is `C^n`. -/
theorem contMDiff_of_eventually_chartAt_apply_eq {g : M₁ → M₂} (hg : Continuous g) {L : E₁ → E₂}
    (hL : ContDiff 𝕜 n L) (h : ∀ p, ∀ᶠ q in 𝓝 p, chartAt E₂ (g p) (g q) = L (chartAt E₁ p q)) :
    ContMDiff 𝓘(𝕜, E₁) 𝓘(𝕜, E₂) n g := fun p ↦
  contMDiffAt_of_eventually_chartAt_apply_eq hg.continuousAt hL.contDiffAt (h p)

end TauCeti

namespace Homeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂]
  [NormedSpace 𝕜 E₂] {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace E₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace E₂ M₂]

/-- If a homeomorphism `g` reads, near every point `p`, as a fixed continuous linear equivalence
`L` in the preferred charts at `p` and at `g p`, then its inverse reads as `L.symm` near every
point. -/
theorem eventually_chartAt_symm_apply_eq (g : M₁ ≃ₜ M₂) (L : E₁ ≃L[𝕜] E₂)
    (h : ∀ p, ∀ᶠ q in 𝓝 p, chartAt E₂ (g p) (g q) = L (chartAt E₁ p q)) (y : M₂) :
    ∀ᶠ w in 𝓝 y, chartAt E₁ (g.symm y) (g.symm w) = L.symm (chartAt E₂ y w) := by
  filter_upwards [g.symm.continuous.continuousAt.tendsto.eventually (h (g.symm y))] with w hw
  rw [apply_symm_apply, apply_symm_apply] at hw
  rw [hw, ContinuousLinearEquiv.symm_apply_apply]

/-- A homeomorphism which, near every point `p`, reads as a fixed continuous linear equivalence `L`
in the preferred charts at `p` and at `g p` is a diffeomorphism of every smoothness `n`, for
manifolds modelled on the normed spaces themselves. -/
noncomputable def toDiffeomorphOfChartAt (g : M₁ ≃ₜ M₂) (L : E₁ ≃L[𝕜] E₂)
    (h : ∀ p, ∀ᶠ q in 𝓝 p, chartAt E₂ (g p) (g q) = L (chartAt E₁ p q)) (n : ℕ∞ω) :
    M₁ ≃ₘ^n⟮𝓘(𝕜, E₁), 𝓘(𝕜, E₂)⟯ M₂ where
  toEquiv := g.toEquiv
  contMDiff_toFun := contMDiff_of_eventually_chartAt_apply_eq g.continuous L.contDiff h
  contMDiff_invFun := contMDiff_of_eventually_chartAt_apply_eq g.symm.continuous L.symm.contDiff
    (g.eventually_chartAt_symm_apply_eq L h)

/-- The underlying map of `Homeomorph.toDiffeomorphOfChartAt` is the homeomorphism. -/
@[simp]
theorem coe_toDiffeomorphOfChartAt (g : M₁ ≃ₜ M₂) (L : E₁ ≃L[𝕜] E₂)
    (h : ∀ p, ∀ᶠ q in 𝓝 p, chartAt E₂ (g p) (g q) = L (chartAt E₁ p q)) (n : ℕ∞ω) :
    ⇑(g.toDiffeomorphOfChartAt L h n) = g :=
  (rfl)

/-- The underlying homeomorphism of `Homeomorph.toDiffeomorphOfChartAt` is the homeomorphism. -/
@[simp]
theorem toHomeomorph_toDiffeomorphOfChartAt (g : M₁ ≃ₜ M₂) (L : E₁ ≃L[𝕜] E₂)
    (h : ∀ p, ∀ᶠ q in 𝓝 p, chartAt E₂ (g p) (g q) = L (chartAt E₁ p q)) (n : ℕ∞ω) :
    (g.toDiffeomorphOfChartAt L h n).toHomeomorph = g :=
  (rfl)

end Homeomorph
