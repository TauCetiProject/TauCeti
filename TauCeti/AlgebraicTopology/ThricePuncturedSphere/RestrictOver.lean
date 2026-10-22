/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Basic

/-!
# Restricting a map to the Riemann sphere over the thrice-punctured sphere

A map `f : Z → OnePoint ℂ`, such as a Belyi map or the projection of a topological branched cover,
restricts to the points of `Z` lying over the thrice-punctured sphere: the complement of the fibres
over `0`, `1` and `∞`. Read through the open embedding `toOnePoint`, this restriction is a map to
`ThricePuncturedSphere`. It is a covering map whenever `f` is one away from the marked points, and
its fibres are the fibres of `f`.

## Main declarations

* `TauCeti.ThricePuncturedSphere.restrictOver`: the restriction of `f` over the thrice-punctured
  sphere.
* `TauCeti.ThricePuncturedSphere.isCoveringMap_restrictOver`: it is a covering map when `f` is a
  covering map away from the marked points.
* `TauCeti.ThricePuncturedSphere.image_val_restrictOver_preimage_singleton`,
  `TauCeti.ThricePuncturedSphere.ncard_restrictOver_preimage_singleton`: its fibres are the fibres
  of `f`.
-/

public noncomputable section

open Set Topology

namespace TauCeti

namespace ThricePuncturedSphere

variable {Z : Type*} (f : Z → OnePoint ℂ)

/-- The map `f` restricted to the complement of the fibres over `0`, `1` and `∞`, viewed as a map
to `ThricePuncturedSphere` through `toOnePoint`. -/
def restrictOver : f ⁻¹' range toOnePoint → ThricePuncturedSphere :=
  isOpenEmbedding_toOnePoint.isEmbedding.toHomeomorph.symm ∘ (range toOnePoint).restrictPreimage f

/-- The restriction of `f` agrees with `f`, read in the Riemann sphere. -/
@[simp]
theorem coe_restrictOver_apply (x : f ⁻¹' range toOnePoint) :
    (((restrictOver f x : ThricePuncturedSphere) : ℂ) : OnePoint ℂ) = f x := by
  have h : isOpenEmbedding_toOnePoint.isEmbedding.toHomeomorph (restrictOver f x) =
      (range toOnePoint).restrictPreimage f x :=
    Homeomorph.apply_symm_apply _ _
  simpa using congrArg Subtype.val h

/-- If `f` is a covering map away from `0`, `1` and `∞`, its restriction over the thrice-punctured
sphere is a covering map. -/
theorem isCoveringMap_restrictOver [TopologicalSpace Z] {f : Z → OnePoint ℂ}
    (hf : IsCoveringMapOn f markedᶜ) : IsCoveringMap (restrictOver f) := by
  rw [← range_toOnePoint] at hf
  exact hf.isCoveringMap_restrictPreimage.homeomorph_comp _

/-- The points over `z` of the restriction of `f` are the points of the fibre of `f` over `z`. -/
theorem image_val_restrictOver_preimage_singleton (z : ThricePuncturedSphere) :
    (Subtype.val : f ⁻¹' range toOnePoint → Z) '' (restrictOver f ⁻¹' {z}) =
      f ⁻¹' {toOnePoint z} := by
  simp only [restrictOver, preimage_comp, Homeomorph.preimage_symm, image_singleton,
    Set.image_val_preimage_restrictPreimage]
  rw [Topology.IsEmbedding.toHomeomorph_apply_coe]

/-- The fibre of the restriction of `f` over `z` is finite when the fibre of `f` over `z` is. -/
theorem finite_restrictOver_preimage_singleton {z : ThricePuncturedSphere}
    (h : (f ⁻¹' {toOnePoint z}).Finite) : (restrictOver f ⁻¹' {z}).Finite :=
  (finite_image_iff Subtype.val_injective.injOn).1 <|
    image_val_restrictOver_preimage_singleton f z ▸ h

/-- The fibre of the restriction of `f` over `z` has as many points as the fibre of `f`. -/
theorem ncard_restrictOver_preimage_singleton (z : ThricePuncturedSphere) :
    (restrictOver f ⁻¹' {z}).ncard = (f ⁻¹' {toOnePoint z}).ncard := by
  rw [← ncard_image_of_injective _ Subtype.val_injective,
    image_val_restrictOver_preimage_singleton]

end ThricePuncturedSphere

end TauCeti
