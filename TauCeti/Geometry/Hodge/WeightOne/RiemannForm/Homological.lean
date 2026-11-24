/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.Homological
public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm.Basic

/-!
# The polarization of the homological Hodge structure by a Riemann form

For a complex torus `V_ℝ / Λ`, the lattice `Λ = H₁` carries two Hodge structures:
`TauCeti.AlmostComplexStructure.latticeHodgeStructure`, the effective weight-one structure with
Weil operator `J`, and the homological structure
`TauCeti.AlmostComplexStructure.RiemannForm.homological` of weight `-1`, with Weil operator
`C = -J`. On a flat integral module, a Riemann form `E` for `J`
polarizes the first, and `Q = -E` polarizes the second in Tau Ceti's sign convention
`0 < Q (C x) x`: indeed `Q (C v) v = E (J v) v > 0`. The homological structure is the Tate twist
by one of the weight-one structure of `-J`, and `-E` is a Riemann form for `-J`
(`TauCeti.AlmostComplexStructure.IsRiemannForm.neg`).

The construction follows the Stanford VIGRE notes, *Complex theory of abelian varieties*,
Lemma 1.16, and Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.

## Main declarations

* `TauCeti.AlmostComplexStructure.IsRiemannForm.isPolarization_homological`: on a flat integral
  module, a Riemann form `E` for `J` makes `-E` a polarization of the homological structure.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.homologicalPolarization`: the bundled
  polarization, on a flat integral module, with `homologicalPolarization_Qint` and
  `homologicalPolarization_Q`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

namespace IsRiemannForm

variable {J : AlmostComplexStructure (Hodge.Realification V)} {E : LinearMap.BilinForm ℤ V}

/-- **A Riemann form `E` for `J` makes `Q = -E` a polarization of the homological Hodge
structure**, on a flat integral module. The sign is forced by the convention `0 < Q (C x) x` with
Weil operator `C = -J`: `Q (C v) v = E (J v) v`. -/
theorem isPolarization_homological [Module.Flat ℤ V] (h : J.IsRiemannForm E)
    (hℂ : IsBaseChange ℂ ιℂ) : Hodge.IsPolarization hℂ (RiemannForm.homological J hℂ) (-E) :=
  RiemannForm.homological_def J hℂ ▸ (h.neg.isPolarization hℂ).tateTwist 1

/-- The polarization `Q = -E` of the homological Hodge structure defined by a Riemann form `E`, on
a flat integral module: the Tate twist by one of the polarization `-E` of the weight-one structure
of `-J` (`isPolarization_homological`). -/
noncomputable def homologicalPolarization [Module.Flat ℤ V] (h : J.IsRiemannForm E)
    (hℂ : IsBaseChange ℂ ιℂ) : Hodge.Polarization hℂ (RiemannForm.homological J hℂ) where
  Qint := -E
  isPolarization := h.isPolarization_homological hℂ

/-- The integral form of the homological polarization of a Riemann form `E` is `-E`. -/
@[simp]
theorem homologicalPolarization_Qint [Module.Flat ℤ V] (h : J.IsRiemannForm E)
    (hℂ : IsBaseChange ℂ ιℂ) : (h.homologicalPolarization hℂ).Qint = -E :=
  (rfl)

/-- The complex form of the homological polarization of a Riemann form `E` is the
complexification of `-E`. -/
@[simp]
theorem homologicalPolarization_Q [Module.Flat ℤ V] (h : J.IsRiemannForm E)
    (hℂ : IsBaseChange ℂ ιℂ) :
    (h.homologicalPolarization hℂ).Q = IsBaseChange.bilinForm hℂ (-E) := by
  rw [Hodge.Polarization.Q_def, homologicalPolarization_Qint]

end IsRiemannForm

end TauCeti.AlmostComplexStructure
