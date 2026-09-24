/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Locally flat subgroup inclusions

An identity-neighbourhood slice chart for a subgroup can be transported by left translations to
charts around every subgroup element.  This file packages that elementary but useful step as local
flatness of the subtype inclusion.  The result is the topological chart boundary used when the
local Cartan chart is upgraded to an embedded Lie-subgroup atlas.

## Main result

* `Subgroup.isLocallyFlat_subtypeVal_of_isSliceChart`: transports one slice chart at the identity
  to a locally flat embedding of the subgroup carrier.

The argument is purely topological; smoothness of the charts and the Lie-group structure on the
subgroup are deliberately left to the later atlas construction.
-/

public section

open Set Topology

namespace Subgroup

variable {G F F' : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

/-- An identity slice chart for a subgroup gives a locally flat chart at every subgroup point.

The chart at `g : K` is obtained by precomposing the identity chart with the inverse of left
translation by `g`.  Since left translation preserves the subgroup carrier, the transported chart
still flattens it onto `univ × {0}`. -/
theorem isLocallyFlat_subtypeVal_of_isSliceChart {K : Subgroup G}
    (φ : OpenPartialHomeomorph G (F × F'))
    (hφ : TauCeti.IsSliceChart φ ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ φ.source) :
    TauCeti.IsLocallyFlat F F' ((↑) : K → G) := by
  have hflat : TauCeti.IsSliceEmbedding ((univ : Set F) ×ˢ ({0} : Set F'))
      ((↑) : K → G) := by
    refine ⟨IsEmbedding.subtypeVal, ?_⟩
    intro g
    let e : OpenPartialHomeomorph G G :=
      (Homeomorph.smul (g : G)).symm.toOpenPartialHomeomorph
    have he_apply (y : G) : e y = (g : G)⁻¹ * y := by
      -- Unfold the local chart abbreviation to expose the bundled homeomorphism action.
      change (Homeomorph.smul (g : G)).symm y = (g : G)⁻¹ * y
      rw [Homeomorph.smul_symm_apply]
      rfl
    have hset : e.source ∩ e ⁻¹' (K : Set G) = (K : Set G) := by
      ext y
      constructor
      · intro hy
        have hy' : e y ∈ K := hy.2
        have hmul : (g : G) * e y ∈ K := K.mul_mem g.property hy'
        rw [he_apply, mul_inv_cancel_left] at hmul
        exact hmul
      · intro hy
        refine ⟨?_, ?_⟩
        · simp [e]
        -- Unfold the preimage membership and local chart abbreviation before cancellation.
        · change e y ∈ K
          rw [he_apply]
          exact K.mul_mem (K.inv_mem g.property) hy
    have hchart := hφ.comp e
    refine ⟨e.trans φ, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_source]
      refine ⟨by simp [e], ?_⟩
      -- The source condition is stated through `e`; expose it before applying `he_apply`.
      change e (g : G) ∈ φ.source
      rw [he_apply, inv_mul_cancel]
      exact h1
    · have hset' : e.source ∩ e ⁻¹' (K : Set G) = Set.range ((↑) : K → G) :=
        hset.trans Subtype.range_coe.symm
      rw [hset'] at hchart
      exact hchart
  exact TauCeti.isLocallyFlat_iff_isSliceEmbedding.mpr hflat

end Subgroup
