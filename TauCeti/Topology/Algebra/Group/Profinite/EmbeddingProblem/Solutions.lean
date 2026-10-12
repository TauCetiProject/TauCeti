/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Group.Shrink
public import TauCeti.Topology.Algebra.Group.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.PGroupKernel

/-!
# Lifting and finiteness for finite embedding problems

The finite groups in an embedding problem can be moved to the universe of its source.
Consequently `HasPGroupSolutions` lifts open-kernel maps through finite surjections in
arbitrary universes. Finiteness of the solution set additionally follows from topological
finite generation of the source.
-/

public section

namespace TauCeti

universe u v w

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Solvability with `p`-group kernel applies to finite target groups in any universe. -/
theorem HasPGroupSolutions.exists_isSolution (hG : HasPGroupSolutions p G)
    (P : FiniteEmbeddingProblem.{u, v, w} G) (hP : IsPGroup p P.α.ker) :
    ∃ β : G →* P.E, P.IsSolution β := by
  classical
  let eE : Shrink.{u} P.E ≃* P.E := Shrink.mulEquiv
  let eQ : Shrink.{u} P.Q ≃* P.Q := Shrink.mulEquiv
  have : Finite (Shrink.{u} P.E) := Finite.of_injective eE eE.injective
  have : Finite (Shrink.{u} P.Q) := Finite.of_injective eQ eQ.injective
  let α := eQ.symm.toMonoidHom.comp (P.α.comp eE.toMonoidHom)
  let π := eQ.symm.toMonoidHom.comp P.π
  have hπ : IsOpen (π.ker : Set G) := by
    rw [MonoidHom.ker_comp_of_injective P.π _ eQ.symm.injective]
    exact P.isOpen_ker_π
  let P' : FiniteEmbeddingProblem.{u, u, u} G :=
    { Q := Shrink.{u} P.Q
      E := Shrink.{u} P.E
      π := π
      isOpen_ker_π := hπ
      π_surjective := eQ.symm.surjective.comp P.π_surjective
      α := α
      α_surjective := eQ.symm.surjective.comp (P.α_surjective.comp eE.surjective) }
  have hα : IsPGroup p α.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eQ.symm.injective]
    exact hP.comap_of_injective eE.toMonoidHom eE.injective
  obtain ⟨β, hβ⟩ := hasPGroupSolutions_iff.mp hG P' hα
  refine ⟨eE.toMonoidHom.comp β, FiniteEmbeddingProblem.isSolution_iff.mpr ⟨?_, ?_⟩⟩
  · rw [MonoidHom.ker_comp_of_injective β _ eE.injective]
    exact hβ.isOpen_ker
  · ext g
    have h := DFunLike.congr_fun hβ.comp_eq g
    simp only [P', α, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    exact eQ.symm.injective h

/-- An open-kernel map lifts through a finite surjection whose kernel is a `p`-group. -/
theorem HasPGroupSolutions.exists_comp_eq (hG : HasPGroupSolutions p G)
    {E : Type v} [Group E] [Finite E] {F : Type w} [Group F]
    (φ : E →* F) (hφ : Function.Surjective φ) (hker : IsPGroup p φ.ker)
    (β : G →* F) (hβ : IsOpen (β.ker : Set G)) :
    ∃ β' : G →* E, IsOpen (β'.ker : Set G) ∧ φ.comp β' = β := by
  let P := FiniteEmbeddingProblem.ofSurjective φ hφ β hβ
  have hP : IsPGroup p P.α.ker := by
    rw [FiniteEmbeddingProblem.ker_ofSurjective_α]
    exact hker.comap_subtype
  obtain ⟨β', hβ'⟩ := hG.exists_isSolution P hP
  exact ⟨(β.range.comap φ).subtype.comp β',
    hβ'.isOpen_ker_subtype_comp, hβ'.comp_subtype_comp⟩

/-- A finite embedding problem for a topologically finitely generated group has finitely
many solutions. -/
theorem IsTopologicallyFinitelyGenerated.finite_isSolution
    (hG : IsTopologicallyFinitelyGenerated G) (P : FiniteEmbeddingProblem.{u, v, w} G) :
    Finite {β : G →* P.E // P.IsSolution β} := by
  have := hG.finite_monoidHom_isOpen_ker P.E
  exact Finite.of_injective
    (fun β : {β : G →* P.E // P.IsSolution β} ↦
      (⟨β.1, β.2.isOpen_ker⟩ : {β : G →* P.E // IsOpen (β.ker : Set G)}))
    (fun _ _ h ↦ Subtype.ext
      (congrArg (fun β : {β : G →* P.E // IsOpen (β.ker : Set G)} ↦ β.1) h))

end TauCeti
