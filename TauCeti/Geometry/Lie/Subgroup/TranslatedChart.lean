/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Translating a subgroup slice chart

An identity-neighbourhood slice chart for a subgroup can be transported to every subgroup point
by left translation.  This is the topological atlas step used after the local Cartan chart: it
packages the translated source, subgroup cancellation, and unchanged coordinate slice in one
reusable theorem.

## Main results

* `Subgroup.translatedChart` translates an ambient identity chart to a subgroup point.
* `Subgroup.isSliceChart_translatedChart` shows that translation preserves the subgroup slice.

The result is purely topological.  It does not install a manifold structure on the subgroup or
assert smoothness of the translated charts.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* H. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

namespace Subgroup

open Set Topology

variable {G P : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [TopologicalSpace P]

/-- Translate an ambient chart at the subgroup identity to an ambient chart at `g`. -/
def translatedChart (K : Subgroup G) (φ : OpenPartialHomeomorph G P)
    (g : K) : OpenPartialHomeomorph G P :=
  (Homeomorph.smul (g : G)).symm.toOpenPartialHomeomorph.trans φ

/-- A translated subgroup chart first moves its argument back to the identity chart. -/
@[simp]
theorem translatedChart_apply (K : Subgroup G) (φ : OpenPartialHomeomorph G P)
    (g : K) (y : G) :
    K.translatedChart φ g y = φ ((g : G)⁻¹ * y) := by
  simp [translatedChart, OpenPartialHomeomorph.trans_apply, Homeomorph.smul_symm_apply,
    smul_eq_mul]

/-- The translated identity chart contains its translating subgroup point in its source. -/
theorem mem_translatedChart_source (K : Subgroup G) (φ : OpenPartialHomeomorph G P)
    (h1 : (1 : G) ∈ φ.source) (g : K) :
    (g : G) ∈ (K.translatedChart φ g).source := by
  rw [translatedChart, OpenPartialHomeomorph.trans_source]
  refine ⟨by simp, ?_⟩
  change (Homeomorph.smul (g : G)).symm (g : G) ∈ φ.source
  rw [Homeomorph.smul_symm_apply, smul_eq_mul, inv_mul_cancel]
  exact h1

/-- Translating an identity slice chart by a subgroup point preserves the subgroup slice. -/
theorem isSliceChart_translatedChart (K : Subgroup G)
    (φ : OpenPartialHomeomorph G P) {S : Set P}
    (hφ : TauCeti.IsSliceChart φ S (K : Set G)) (g : K) :
    TauCeti.IsSliceChart (K.translatedChart φ g) S
      (Set.range ((↑) : K → G)) := by
  let e : OpenPartialHomeomorph G G :=
    (Homeomorph.smul (g : G)).symm.toOpenPartialHomeomorph
  have he_apply (y : G) : e y = (g : G)⁻¹ * y := by
    change (Homeomorph.smul (g : G)).symm y = (g : G)⁻¹ * y
    rw [Homeomorph.smul_symm_apply, smul_eq_mul]
  have hset : e.source ∩ e ⁻¹' (K : Set G) = (K : Set G) := by
    ext y
    constructor
    · intro hy
      have hy' : e y ∈ K := hy.2
      rw [he_apply] at hy'
      exact (K.mul_mem_cancel_left (K.inv_mem g.property)).mp hy'
    · intro hy
      refine ⟨?_, ?_⟩
      · simp [e]
      · change e y ∈ K
        rw [he_apply]
        exact (K.mul_mem_cancel_left (K.inv_mem g.property)).mpr hy
  have hchart := hφ.comp e
  have hset' : e.source ∩ e ⁻¹' (K : Set G) = Set.range ((↑) : K → G) :=
    hset.trans Subtype.range_coe.symm
  rw [hset'] at hchart
  exact hchart

end Subgroup
