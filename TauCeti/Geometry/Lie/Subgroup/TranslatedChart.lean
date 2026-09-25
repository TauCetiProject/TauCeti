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

## Main result

* `Subgroup.exists_isSliceChart_of_isSliceChart` gives a slice chart around every point of a
  subgroup from one chart around the identity, with arbitrary model space and slice.

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

/-- An identity slice chart for a subgroup translates to a slice chart around every subgroup point.

The target is the subtype range rather than the carrier set so that the result is immediately in
the form required by `TauCeti.IsSliceEmbedding` and `TauCeti.IsLocallyFlat`. -/
theorem exists_isSliceChart_of_isSliceChart (K : Subgroup G)
    (φ : OpenPartialHomeomorph G P) {S : Set P}
    (hφ : TauCeti.IsSliceChart φ S (K : Set G))
    (h1 : (1 : G) ∈ φ.source) (g : K) :
    ∃ ψ : OpenPartialHomeomorph G P,
      (g : G) ∈ ψ.source ∧
        TauCeti.IsSliceChart ψ S
          (Set.range ((↑) : K → G)) := by
  let e : OpenPartialHomeomorph G G :=
    (Homeomorph.smul (g : G)).symm.toOpenPartialHomeomorph
  have he_apply (y : G) : e y = (g : G)⁻¹ * y := by
    -- Unfold the local chart abbreviation to expose the bundled homeomorphism action.
    change (Homeomorph.smul (g : G)).symm y = (g : G)⁻¹ * y
    rw [Homeomorph.smul_symm_apply]
    rw [smul_eq_mul]
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
    -- Expose the preimage membership in the translated chart source.
    change e (g : G) ∈ φ.source
    rw [he_apply, inv_mul_cancel]
    exact h1
  · have hset' : e.source ∩ e ⁻¹' (K : Set G) = Set.range ((↑) : K → G) :=
      hset.trans Subtype.range_coe.symm
    rw [hset'] at hchart
    exact hchart

end Subgroup
