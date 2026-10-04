/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

import Mathlib.Tactic.Abel

/-!
# Homogeneous cochains with trivial F₂ coefficients

A continuous function `f : G → ZMod 2` determines a homogeneous one-cochain with trivial
coefficients by `(g₀, g₁) ↦ f (g₀⁻¹ * g₁)`, lifted to the carrier of `trivialF2 G`.
This file gives the constructor `homogeneousCochain1OfInhomogeneous`, its pointwise evaluation
rule, and its cocycle criterion. They let explicit one-cochain formulas enter the canonical
continuous-cohomology complex without depending on a particular class-valued construction.
-/

public section

namespace TauCeti.ContCohomology

universe u

section Canonical

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous `ZMod 2`-valued one-cochain in the canonical homogeneous complex with trivial
coefficients. -/
noncomputable def homogeneousCochain1OfInhomogeneous (f : G → ZMod 2) (hf : Continuous f) :
    (TopRep.homogeneousCochains (trivialF2 G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦
      (trivialF2Equiv G).symm (f (q.1⁻¹ * q.2)),
      continuous_of_discreteTopology.comp
        (hf.comp (continuous_fst.inv.mul continuous_snd))⟩,
    fun g ↦ by
      ext h k
      simp only [ContRepresentation.coind₁_apply_apply, trivialF2_ρ_apply_apply,
        ContinuousMap.curry_apply, ContinuousMap.coe_mk]
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

/-- The value of `homogeneousCochain1OfInhomogeneous f hf` at `(g₀, g₁)` is `f (g₀⁻¹g₁)`, lifted to
the coefficient object. -/
@[simp]
theorem homogeneousCochain1OfInhomogeneous_apply (f : G → ZMod 2) (hf : Continuous f) (g₀ g₁ : G) :
    (homogeneousCochain1OfInhomogeneous f hf).val g₀ g₁ =
      (trivialF2Equiv G).symm (f (g₀⁻¹ * g₁)) :=
  (rfl)

/-- A continuous one-cochain for the trivial action is a canonical cocycle when it is additive
under multiplication. -/
theorem homogeneousCochain1OfInhomogeneous_d_eq_zero (f : G → ZMod 2) (hf : Continuous f)
    (hcocycle : ∀ g h : G, f (g * h) = f g + f h) :
    ((TopRep.homogeneousCochains (trivialF2 G)).d 1 2).hom
      (homogeneousCochain1OfInhomogeneous f hf) = 0 := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [_root_.TopRep.homogeneousCochains.d_one_apply, homogeneousCochain1OfInhomogeneous_apply,
    homogeneousCochain1OfInhomogeneous_apply, homogeneousCochain1OfInhomogeneous_apply,
    ← map_sub, ← map_sub,
    Submodule.coe_zero, ContinuousMap.zero_apply, ContinuousMap.zero_apply,
    ContinuousMap.zero_apply, ← map_zero (trivialF2Equiv G).symm]
  congr 1
  have h : f (g₀⁻¹ * g₂) = f (g₀⁻¹ * g₁) + f (g₁⁻¹ * g₂) := by
    rw [← hcocycle, mul_assoc, mul_inv_cancel_left]
  rw [h]
  abel

end Canonical

end TauCeti.ContCohomology
