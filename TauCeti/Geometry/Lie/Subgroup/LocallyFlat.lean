/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Locally flat subgroup inclusions

For a topological group, an identity-neighbourhood slice chart for a subgroup gives a locally flat
subtype inclusion.  The result records the standard `univ × {0}` slice for the subgroup carrier,
providing the local-flatness interface for geometric subgroup constructions.

## Main result

* `Subgroup.isLocallyFlat_subtypeVal_of_isSliceChart`: an identity slice chart implies local
  flatness of the subgroup subtype inclusion.
-/

public section

open Set Topology

namespace Subgroup

variable {G F F' : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

/-- An identity slice chart for a subgroup makes its subtype inclusion locally flat.

The hypothesis is an ambient chart around the identity that identifies the subgroup carrier with
the standard slice `univ × {0}`. -/
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
        rw [he_apply] at hy'
        exact (K.mul_mem_cancel_left (K.inv_mem g.property)).mp hy'
      · intro hy
        refine ⟨?_, ?_⟩
        · simp [e]
        -- The preimage notation must be unfolded before the translation identity can rewrite.
        · change e y ∈ K
          rw [he_apply]
          exact (K.mul_mem_cancel_left (K.inv_mem g.property)).mpr hy
    have hchart := hφ.comp e
    refine ⟨e.trans φ, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_source]
      refine ⟨by simp [e], ?_⟩
      -- Likewise expose the preimage membership in the translated chart source.
      change e (g : G) ∈ φ.source
      rw [he_apply, inv_mul_cancel]
      exact h1
    · have hset' : e.source ∩ e ⁻¹' (K : Set G) = Set.range ((↑) : K → G) :=
        hset.trans Subtype.range_coe.symm
      rw [hset'] at hchart
      exact hchart
  exact TauCeti.isLocallyFlat_iff_isSliceEmbedding.mpr hflat

end Subgroup
