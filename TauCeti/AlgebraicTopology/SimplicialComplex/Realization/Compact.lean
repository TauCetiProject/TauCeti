/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.DiscreteSubset

/-!
# Compact subsets of weak polyhedra

A compact subset of a weak simplicial realization meets only finitely many open simplices,
and consequently uses only finitely many vertices. This permits maps from compact spaces,
including spheres and cubes, to be studied inside finite polyhedra even when the ambient
complex is neither finite nor locally finite.

The compact-support finiteness results provide a finite vertex set containing the support
of every point in a compact subset. They apply to arbitrary vertex types and require no
local finiteness assumption on the complex.

## References

* A. Hatcher, *Algebraic Topology*, Appendix A, Proposition A.1 (compact subsets of weak
  complexes are contained in finite subcomplexes).
-/

public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {K : AbstractSimplicialComplex ι}

attribute [local instance] Classical.decEq

/-- A set with at most one point in each open simplex is closed in the weak realization. -/
theorem isClosed_of_injOn_support {s : Set (Realization K)}
    (hs : InjOn (fun x : Realization K => x.1.support) s) : IsClosed s := by
  apply isClosed_iff_faceInclusion.mpr
  intro σ
  have hinj : InjOn (fun x : StandardSimplex σ.1 => x.1.support)
      (faceInclusion K σ ⁻¹' s) := by
    intro x hx y hy hxy
    have he := hs hx hy (by simpa only [faceInclusion_val] using hxy)
    apply Subtype.ext
    simpa only [faceInclusion_val] using congrArg Subtype.val he
  have hfin := σ.1.powerset.finite_toSet.of_injOn
    (fun x _ => Finset.mem_powerset.mpr (StandardSimplex.support_subset x)) hinj
  exact hfin.isClosed

/-- Only finitely many barycentric supports occur in a compact subset of a weak realization.
Equivalently, it meets only finitely many open simplices. -/
theorem finite_image_support_of_isCompact {s : Set (Realization K)} (hs : IsCompact s) :
    ((fun x : Realization K => x.1.support) '' s).Finite := by
  let S := (fun x : Realization K => x.1.support) '' s
  have hex (σ : S) : ∃ x ∈ s, x.1.support = σ.1 := σ.2
  choose r hr hsupport using hex
  have hinj : InjOn (fun x : Realization K => x.1.support) (range r) := by
    rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩ h
    have he : σ = τ := Subtype.ext (by simpa only [hsupport] using h)
    exact congrArg r he
  have hclosed := isClosed_of_injOn_support hinj
  have hdiscrete : IsDiscrete (range r) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro t ht
    exact ⟨t, isClosed_of_injOn_support (hinj.mono ht), inter_eq_left.mpr ht⟩
  let : DiscreteTopology (range r) := isDiscrete_iff_discreteTopology.mp hdiscrete
  have hc : IsCompact (range r) := hs.of_isClosed_subset hclosed (by
    rintro _ ⟨σ, rfl⟩
    exact hr σ)
  have hf : (range r).Finite := by
    let : CompactSpace (range r) := isCompact_iff_compactSpace.mp hc
    exact finite_coe_iff.mp finite_of_compact_of_discrete
  exact (hf.image (fun x : Realization K => x.1.support)).subset (by
    intro σ hσ
    exact ⟨r ⟨σ, hσ⟩, mem_range_self _, hsupport ⟨σ, hσ⟩⟩)

/-- Every compact subset of a weak realization uses only finitely many vertices. -/
theorem exists_finset_support_subset_of_isCompact {s : Set (Realization K)} (hs : IsCompact s) :
    ∃ V : Finset ι, ∀ x ∈ s, x.1.support ⊆ V := by
  let S := (fun x : Realization K => x.1.support) '' s
  have hS : S.Finite := finite_image_support_of_isCompact hs
  refine ⟨hS.toFinset.biUnion id, ?_⟩
  intro x hx v hv
  exact Finset.mem_biUnion.mpr ⟨x.1.support, hS.mem_toFinset.mpr ⟨x, hx, rfl⟩, hv⟩

end AbstractSimplicialComplex
