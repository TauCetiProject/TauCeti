/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv.ExtDeriv

/-!
# The time derivative of a family of closed forms

A smooth form `σ` on `ℝ × M` represents the time-dependent family of its slices
`σ_t = ι_t^* σ`, and its time derivative `∂_t σ = L_{∂_t} σ` (`TauCeti.SmoothForm.timeDeriv`)
represents the velocities of the slices. This file shows that if every slice `σ_t` is closed, so is
every slice of the time derivative
(`TauCeti.SmoothForm.isClosed_mpullback_prodMk_timeDeriv`): the velocity of a smooth family of
closed forms is a smooth family of closed forms. This is what Moser's argument needs to write the
velocity as the exterior derivative of a family of primitives by a Poincaré lemma for families.

The proof commutes the exterior derivative with the Lie derivative along `∂_t`,
`d (L_{∂_t} σ) = L_{∂_t} (d σ)` (`TauCeti.SmoothForm.mextDeriv_mlieDerivForm`). So the exterior
derivative of the slice of `∂_t σ` at time `t` is the slice of `∂_t (d σ)`, the velocity of the
slices of `d σ`. Those slices are `d σ_u = 0` for every time `u`, so their velocity vanishes.

## Main results

* `TauCeti.SmoothForm.isClosed_mpullback_prodMk_timeDeriv`: the slices of the time derivative of
  a family of closed forms are closed.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **The velocity of a family of closed forms is closed.** If every slice `σ_u = ι_u^* σ` of a
smooth form `σ` on `ℝ × M` is closed, then so is every slice of its time derivative `∂_t σ`. -/
theorem isClosed_mpullback_prodMk_timeDeriv (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1))
    (hσ : ∀ u, (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) σ).IsClosed)
    (t : ℝ) :
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ.timeDeriv).IsClosed
    := by
  have hι (u : ℝ) : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (Prod.mk u : M → ℝ × M) :=
    contMDiff_const.prodMk contMDiff_id
  -- The exterior derivative `dσ`, as a smooth form on `ℝ × M`.
  set τ := mextDerivₗ (𝓘(ℝ, ℝ).prod I) (k + 1) σ
  -- Its slices `ι_u^* dσ = d σ_u` all vanish.
  have hτ (u : ℝ) : (SmoothForm.mpullback (Prod.mk u) (hι u) τ).val = 0 := by
    rw [← SmoothForm.mextDerivₗ_mpullback, mextDerivₗ_apply]
    exact (SmoothForm.isClosed_def _).mp (hσ u)
  rw [SmoothForm.isClosed_def, ← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback (hf := hι t),
    SmoothForm.coe_mpullback, mextDerivₗ_apply, SmoothForm.coe_timeDeriv,
    mextDeriv_mlieDerivForm (V := fun _ ↦ ((1 : ℝ), (0 : E))) σ
      (contMDiff_const_prod_field 1 (X := 0)
      ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd))]
  -- The slice at `t` of `∂_t dσ` is the velocity of the vanishing slices of `dσ`.
  funext x
  have h := τ.hasDerivAt_mpullback_prodMk_timeDeriv t x
  simp only [hτ, SmoothForm.coe_mpullback, SmoothForm.coe_timeDeriv, τ, mextDerivₗ_apply] at h
  exact h.unique (hasDerivAt_const t (0 : E [⋀^Fin (k + 2)]→L[ℝ] F))

end SmoothForm

end TauCeti
