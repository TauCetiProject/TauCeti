/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

/-!
# Incompressible embeddings

An embedding of a surface in a 3-manifold is incompressible when it is injective on the
fundamental group.  This file records the dimension-independent topological core of that
condition.  The embedding and π₁-injectivity conditions are stated independently of surface and
manifold hypotheses so that this API can be reused in their presence.

The main predicate `IsIncompressible` combines a topological embedding with injectivity of the
fundamental-group map at every basepoint.  A continuous retraction supplies both properties, and
the product inclusion `x ↦ (x, y₀)` is the basic example.

The definition follows the standard usage in 3-manifold topology; see A. Hatcher,
*Algebraic Topology*, §1.2, and W. Jaco, *Lectures on Three-Manifold Topology*, Chapter II.
-/

public section

namespace TauCeti

open Topology

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- A continuous map is incompressible when it is a topological embedding and induces an injective
map on fundamental groups at every basepoint.  The separate embedding conjunct is intentional:
π₁-injectivity alone does not prevent a map from identifying points. -/
def IsIncompressible (f : C(S, M)) : Prop :=
  IsEmbedding f ∧ ∀ s : S, Function.Injective (FundamentalGroup.map f s)

/-- The defining embedding and fundamental-group injectivity conditions for an incompressible
map. -/
theorem isIncompressible_iff {f : C(S, M)} :
    IsIncompressible f ↔
      IsEmbedding f ∧ ∀ s : S, Function.Injective (FundamentalGroup.map f s) :=
  Iff.rfl

namespace IsIncompressible

variable {f : C(S, M)}

/-- The embedding part of an incompressible map. -/
theorem isEmbedding (h : IsIncompressible f) : IsEmbedding f :=
  h.1

/-- The induced map on `π₁` is injective at every basepoint. -/
theorem fundamentalGroup_injective (h : IsIncompressible f) (s : S) :
    Function.Injective (FundamentalGroup.map f s) :=
  h.2 s

/-- The composition of incompressible maps is incompressible. -/
theorem comp {T : Type*} [TopologicalSpace T] {g : C(M, T)}
    (hg : IsIncompressible g) (hf : IsIncompressible f) :
    IsIncompressible (g.comp f) := by
  refine ⟨hg.isEmbedding.comp hf.isEmbedding, fun s => ?_⟩
  intro γ₁ γ₂ hγ
  apply hf.fundamentalGroup_injective s
  apply hg.fundamentalGroup_injective (f s)
  have hcomp (γ : FundamentalGroup S s) :
      FundamentalGroup.map (g.comp f) s γ =
        FundamentalGroup.map g (f s) (FundamentalGroup.map f s γ) := by
    exact FundamentalGroupoid.map_comp_map g f γ
  rw [hcomp γ₁, hcomp γ₂] at hγ
  exact hγ

end IsIncompressible

/-- A continuous left inverse makes an embedding incompressible. -/
theorem isIncompressible_of_leftInverse {f : C(S, M)} {r : C(M, S)}
    (h : r.comp f = ContinuousMap.id S) : IsIncompressible f := by
  refine ⟨?_, fun s => ?_⟩
  · apply IsEmbedding.of_leftInverse (f := r) (g := f)
    · intro x
      exact congrFun (congrArg DFunLike.coe h) x
    · exact r.continuous
    · exact f.continuous
  · have hbase : r (f s) = s := congrFun (congrArg DFunLike.coe h) s
    have hleft : Function.LeftInverse (FundamentalGroup.mapOfEq r hbase)
        (FundamentalGroup.map f s) := by
      intro γ
      simpa only [FundamentalGroup.mapOfEq_rfl] using
        (FundamentalGroup.mapOfEq_mapOfEq_of_comp_eq_id r f rfl hbase h γ)
    exact hleft.injective

/-- The product inclusion into a slice is incompressible. -/
theorem isIncompressible_prodMk (y₀ : M) :
    IsIncompressible (ContinuousMap.prodMk (ContinuousMap.id S)
      (ContinuousMap.const S y₀)) := by
  apply isIncompressible_of_leftInverse (f :=
    ContinuousMap.prodMk (ContinuousMap.id S) (ContinuousMap.const S y₀))
    (r := ContinuousMap.fst)
  ext x
  rfl

end TauCeti
