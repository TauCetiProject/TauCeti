/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Lie.Subgroup.TranslatedChart

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

variable {G F F' : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

/-- An identity slice chart for a subgroup makes its subtype inclusion locally flat.

The hypothesis is an ambient chart around the identity that identifies the subgroup carrier with
the standard slice `univ × {0}`. -/
theorem isLocallyFlat_subtypeVal_of_isSliceChart (K : Subgroup G)
    (φ : OpenPartialHomeomorph G (F × F'))
    (hφ : TauCeti.IsSliceChart φ ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ φ.source) :
    TauCeti.IsLocallyFlat F F' ((↑) : K → G) := by
  have hflat : TauCeti.IsSliceEmbedding ((univ : Set F) ×ˢ ({0} : Set F'))
      ((↑) : K → G) := by
    refine ⟨IsEmbedding.subtypeVal, fun g => ?_⟩
    refine ⟨(Homeomorph.smul (g : G)).symm.transOpenPartialHomeomorph φ, ?_, ?_⟩
    · rw [Homeomorph.transOpenPartialHomeomorph_source]
      simpa [Homeomorph.smul_symm_apply, smul_eq_mul] using h1
    · rw [Subtype.range_coe]
      exact K.isSliceChart_smul_symm_transOpenPartialHomeomorph φ hφ g
  exact TauCeti.isLocallyFlat_iff_isSliceEmbedding.mpr hflat

end Subgroup
