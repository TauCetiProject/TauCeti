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
by left translation. This file defines the translated ambient chart, records its source, target,
evaluation, and inverse, and proves that translation by a subgroup point preserves the subgroup
slice.

## Main definitions and results

* `OpenPartialHomeomorph.translatedChart` translates an ambient chart by a group element.
* `Subgroup.isSliceChart_translatedChart` shows that translation preserves the subgroup slice.

The result is purely topological.  It does not install a manifold structure on the subgroup or
assert smoothness of the translated charts.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* H. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

open Set Topology

namespace OpenPartialHomeomorph

variable {G P : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [TopologicalSpace P]

/-- Translate an ambient chart by a group element `g`. -/
def translatedChart (φ : OpenPartialHomeomorph G P) (g : G) : OpenPartialHomeomorph G P :=
  (Homeomorph.smul g).symm.transOpenPartialHomeomorph φ

/-- The source of a translated chart consists of the points moved into the source of the original
chart by multiplication by `g⁻¹`. -/
@[simp]
theorem translatedChart_source (φ : OpenPartialHomeomorph G P) (g : G) :
    (φ.translatedChart g).source = (fun y : G => g⁻¹ * y) ⁻¹' φ.source := by
  ext y
  simp [translatedChart, Homeomorph.smul_symm_apply, smul_eq_mul]

/-- Translation does not change the coordinate target of an ambient chart. -/
@[simp]
theorem translatedChart_target (φ : OpenPartialHomeomorph G P) (g : G) :
    (φ.translatedChart g).target = φ.target := by
  simp [translatedChart]

/-- Evaluating a chart translated by `g` first translates the argument by `g⁻¹`, then applies
the original chart. -/
@[simp]
theorem translatedChart_apply (φ : OpenPartialHomeomorph G P) (g y : G) :
    φ.translatedChart g y = φ (g⁻¹ * y) := by
  simp [translatedChart, Homeomorph.smul_symm_apply, smul_eq_mul]

/-- The inverse of a translated chart applies the original inverse and then translates by `g`. -/
@[simp]
theorem translatedChart_symm_apply (φ : OpenPartialHomeomorph G P) (g : G) (p : P) :
    (φ.translatedChart g).symm p = g * φ.symm p := by
  simp [translatedChart, smul_eq_mul]

/-- A chart containing `1` in its source, translated by `g`, contains `g` in its source. -/
theorem mem_translatedChart_source (φ : OpenPartialHomeomorph G P)
    (h1 : (1 : G) ∈ φ.source) (g : G) : g ∈ (φ.translatedChart g).source := by
  rw [translatedChart_source]
  simpa using h1

end OpenPartialHomeomorph

namespace Subgroup

open Set Topology

variable {G P : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [TopologicalSpace P]

/-- Translating a slice chart for a subgroup by a subgroup point preserves the subgroup slice. -/
theorem isSliceChart_translatedChart (K : Subgroup G)
    (φ : OpenPartialHomeomorph G P) {S : Set P}
    (hφ : TauCeti.IsSliceChart φ S (K : Set G)) (g : K) :
    TauCeti.IsSliceChart (φ.translatedChart (g : G)) S (K : Set G) := by
  let e : OpenPartialHomeomorph G G :=
    (Homeomorph.smul (g : G)).symm.toOpenPartialHomeomorph
  have hset : e.source ∩ e ⁻¹' (K : Set G) = (K : Set G) := by
    have hpre : e ⁻¹' (K : Set G) = K := by
      have he : ⇑e = fun y : G => (g : G)⁻¹ • y := by
        ext y
        simp [e, Homeomorph.smul_symm_apply]
      rw [he, Set.preimage_smul_inv, smul_coe_set g.property]
    rw [hpre]
    simp [e]
  have hchart := hφ.comp e
  rw [hset] at hchart
  simpa [OpenPartialHomeomorph.translatedChart, e,
    Homeomorph.transOpenPartialHomeomorph_eq_trans] using hchart

end Subgroup
