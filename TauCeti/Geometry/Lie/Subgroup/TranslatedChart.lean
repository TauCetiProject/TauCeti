/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Translating a subgroup slice chart

An identity-neighbourhood slice chart for a subgroup can be transported to every subgroup point
by left translation. Using the topology-level ambient chart translation, this file proves that
translation by a subgroup point preserves the subgroup slice.

## Main result

* `Subgroup.isSliceChart_smul_symm_transOpenPartialHomeomorph` shows that translation preserves
  the subgroup slice.

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

/-- Translating a slice chart for a subgroup by a subgroup point preserves the subgroup slice. -/
theorem isSliceChart_smul_symm_transOpenPartialHomeomorph (K : Subgroup G)
    (φ : OpenPartialHomeomorph G P) {S : Set P}
    (hφ : TauCeti.IsSliceChart φ S (K : Set G)) (g : K) :
    TauCeti.IsSliceChart
      ((Homeomorph.smul (g : G)).symm.transOpenPartialHomeomorph φ) S (K : Set G) := by
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
  simpa [e,
    Homeomorph.transOpenPartialHomeomorph_eq_trans] using hchart

end Subgroup
