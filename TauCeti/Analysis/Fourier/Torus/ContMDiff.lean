/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Analysis.Fourier.Torus.Smooth
public import TauCeti.Geometry.Manifold.Instances.AddCircle

/-!
# Smooth functions on the torus as a product of two circles

The square torus is both the manifold `AddCircle 1 × AddCircle 1` and the torus
`UnitAddTorus (Fin 2)` of the Fourier series files, identified by `y ↦ (y 0, y 1)`. This file
shows that the smooth complex valued functions in the manifold sense on the first are exactly the
smooth functions `TauCeti.UnitAddTorus.smoothFunctions (Fin 2)` on the second, whose lifts to
`Fin 2 → ℝ` are `C^∞`.

## Main definitions

* `TauCeti.UnitAddTorus.prodEquiv`: the identification
  `UnitAddTorus (Fin 2) ≃ AddCircle 1 × AddCircle 1`.
* `TauCeti.UnitAddTorus.contMDiffMapEquiv`: smooth functions on `AddCircle 1 × AddCircle 1` are the
  smooth functions on `UnitAddTorus (Fin 2)`, as a real linear equivalence.

## Main results

* `TauCeti.UnitAddTorus.contMDiff_iff_comp_prodEquiv_mem_smoothFunctions`: a function on
  `AddCircle 1 × AddCircle 1` is smooth exactly when its composition with `prodEquiv` is a smooth
  function on `UnitAddTorus (Fin 2)`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.UnitAddTorus

/-- The identification `UnitAddTorus (Fin 2) ≃ AddCircle 1 × AddCircle 1`, `y ↦ (y 0, y 1)`. -/
abbrev prodEquiv : UnitAddTorus (Fin 2) ≃ UnitAddCircle × UnitAddCircle :=
  piFinTwoEquiv fun _ ↦ UnitAddCircle

/-- Smooth functions on `AddCircle 1 × AddCircle 1` are the smooth functions on
`UnitAddTorus (Fin 2)`. -/
theorem contMDiff_iff_comp_prodEquiv_mem_smoothFunctions {σ : UnitAddCircle × UnitAddCircle → ℂ} :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ σ ↔ σ ∘ prodEquiv ∈ smoothFunctions (Fin 2) := by
  -- The lift to `Fin 2 → ℝ` of `σ ∘ prodEquiv` is the lift of `σ` to `ℝ × ℝ`, read through the
  -- coordinates `Fin 2 → ℝ ≃ ℝ × ℝ`.
  have hlift : (fun y : Fin 2 → ℝ ↦ (σ ∘ prodEquiv) fun i ↦ (y i : UnitAddCircle)) =
      (σ ∘ Prod.map ((↑) : ℝ → UnitAddCircle) ((↑) : ℝ → UnitAddCircle)) ∘
        ContinuousLinearEquiv.piFinTwo ℝ fun _ ↦ ℝ :=
    rfl
  rw [mem_smoothFunctions, hlift, ContinuousLinearEquiv.contDiff_comp_iff,
    ← contMDiff_iff_contDiff,
    (AddCircle.isLocalDiffeomorph_prodMap_coe 1 1 ∞).contMDiff_comp_iff
      (AddCircle.prodMap_coe_surjective 1 1) le_rfl]

/-- Smooth functions on `AddCircle 1 × AddCircle 1` are the smooth functions on
`UnitAddTorus (Fin 2)`, through `prodEquiv`. -/
def contMDiffMapEquiv :
    C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℝ]
      smoothFunctions (Fin 2) where
  toFun σ := ⟨σ ∘ prodEquiv, contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.1 σ.contMDiff⟩
  invFun f := ⟨f ∘ prodEquiv.symm, contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.2 (by
    rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    exact f.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv σ := by
    ext x
    simp
  right_inv f := by
    ext y
    exact congrArg f.1 (prodEquiv.symm_apply_apply y)

@[simp]
theorem coe_contMDiffMapEquiv_apply
    (σ : C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯) :
    (contMDiffMapEquiv σ : UnitAddTorus (Fin 2) → ℂ) = σ ∘ prodEquiv :=
  (rfl)

@[simp]
theorem coe_contMDiffMapEquiv_symm_apply (f : smoothFunctions (Fin 2)) :
    (contMDiffMapEquiv.symm f : UnitAddCircle × UnitAddCircle → ℂ) = f ∘ prodEquiv.symm :=
  (rfl)

end TauCeti.UnitAddTorus
