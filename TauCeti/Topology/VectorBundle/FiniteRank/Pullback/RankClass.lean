/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Pullback on isomorphism classes of fixed-rank bundle cores

`FiniteRankBundleCore.pullbackRankClass` induces the contravariant pullback map on isomorphism
classes of rank-`n` finite-rank vector-bundle cores, together with its quotient evaluation and
functoriality simp lemmas (`pullbackRankClass_mk`, `pullbackRankClass_id`,
`pullbackRankClass_comp`).
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankBundleCore

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pullback of isomorphism classes of rank-`n` vector-bundle cores along `f : C(X, Y)`. -/
def pullbackRankClass (f : C(X, Y)) (n : ℕ) :
    Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 Y)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 Y // A.rank = n} → _)) →
      Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = n} → _)) :=
  Quotient.map (fun A ↦ ⟨A.val.pullback f, A.property⟩) fun _ _ ⟨α⟩ ↦ ⟨(pullbackFunctor f).mapIso α⟩

@[simp] theorem pullbackRankClass_mk (f : C(X, Y)) (n : ℕ)
    (A : {A : FiniteRankBundleCore 𝕜 Y // A.rank = n}) :
    pullbackRankClass f n (Quotient.mk _ A) = Quotient.mk _ ⟨A.val.pullback f, A.property⟩ := (rfl)

@[simp] theorem pullbackRankClass_id (n : ℕ)
    (c : Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 Y)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 Y // A.rank = n} → _))) :
    pullbackRankClass (ContinuousMap.id Y) n c = c :=
  Quotient.inductionOn c fun A ↦ congrArg (Quotient.mk _) (Subtype.ext (pullback_id A.val))

@[simp] theorem pullbackRankClass_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ)
    (c : Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 Z)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 Z // A.rank = n} → _))) :
    pullbackRankClass f n (pullbackRankClass g n c) = pullbackRankClass (g.comp f) n c :=
  Quotient.inductionOn c fun A ↦ congrArg (Quotient.mk _) (Subtype.ext (pullback_comp A.val f g))

end TauCeti.FiniteRankBundleCore
