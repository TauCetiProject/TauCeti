/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Dense spans

A generating family, regarded as a family in the closure of its span, has dense span there.
This lets constructions on densely spanning families apply to arbitrary closed spans.
Conversely, a densely spanning family stays densely spanning when pushed forward along a
continuous linear map with dense range, such as the projection onto a quotient module, so that a
quotient of a module spanned densely by a countable family is again spanned densely by one.
Restricting a point-continuous family of maps to a dense-range index map likewise preserves the
closed span of all their ranges (`DenseRange.topologicalClosure_span_iUnion_range_comp_eq`).
No norm, separation, or completeness assumptions are needed.

Likewise, a continuous semilinear map sending a generating set into a closed submodule sends the
closure of its span there (`Continuous.apply_mem_of_mem_topologicalClosure_span`).

Over a complete nontrivially normed field, a closed subspace `S` of finite codimension together
with the span of a set `s` spans a dense subspace only if `S` and finitely many vectors of `s` span
the whole space (`Submodule.exists_finset_subset_sup_span_eq_top_of_dense`). This is how a
Fredholm operator is made surjective by adjoining finitely many directions from a prescribed
family, as in transversality arguments.
-/

public section

namespace TauCeti

open Set Submodule

/-- A family of vectors in the closure of its span still has dense span there. -/
theorem dense_span_in_topologicalClosure {R ι M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul R M] (v : ι → M) :
    Dense (span R (range (fun i ↦
      (⟨v i, (span R (range v)).le_topologicalClosure (subset_span (mem_range_self i))⟩ :
        (span R (range v)).topologicalClosure))) :
      Set (span R (range v)).topologicalClosure) := by
  rw [Subtype.dense_iff]
  have hspan := congrArg (fun p : Submodule R M ↦ (p : Set M))
    (Submodule.map_span (span R (range v)).topologicalClosure.subtype
      (range (fun i ↦
        (⟨v i, (span R (range v)).le_topologicalClosure (subset_span (mem_range_self i))⟩ :
          (span R (range v)).topologicalClosure))))
  simp only [Submodule.map_coe, Submodule.coe_subtype, ← range_comp, Function.comp_def,
    Submodule.subtype_apply] at hspan
  exact closure_mono hspan.symm.subset

end TauCeti

/-- If a continuous semilinear map `f` sends a generating set `s` into a closed submodule `p` of
`N`, then it sends `(Submodule.span R s).topologicalClosure` into `p`. -/
theorem Continuous.apply_mem_of_mem_topologicalClosure_span {R S M N F : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] [AddCommMonoid N] [Module S N]
    [TopologicalSpace N] [FunLike F M N] [SemilinearMapClass F σ M N] {f : F} (hfc : Continuous f)
    {s : Set M} {p : Submodule S N} (hp : IsClosed (p : Set N)) (hs : ∀ x ∈ s, f x ∈ p) {x : M}
    (hx : x ∈ (Submodule.span R s).topologicalClosure) :
    f x ∈ p :=
  Submodule.topologicalClosure_minimal _ (t := p.comap (LinearMap.ofClass f))
    (Submodule.span_le.mpr hs) (hp.preimage hfc) hx

/-- The image of a densely spanning family under a continuous linear map with dense range has
dense span. For instance, the image of a densely spanning family in a quotient module `M ⧸ p`
(take `f = p.mkQ`) has dense span. -/
theorem DenseRange.dense_span_range_comp {R M N ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [AddCommMonoid N] [Module R N]
    [TopologicalSpace N] {f : M →ₗ[R] N} (hf : DenseRange f) (hfc : Continuous f) {v : ι → M}
    (hv : Dense (Submodule.span R (Set.range v) : Set M)) :
    Dense (Submodule.span R (Set.range (f ∘ v)) : Set N) := by
  rw [Set.range_comp, ← Submodule.map_span, Submodule.map_coe]
  exact hf.dense_image hfc hv

/-- Restricting a point-continuous family of maps `L : α → X → Y` into a topological `R`-module `Y`
to a dense range `Set.range g` generates the same closed `R`-span in `Y`. -/
theorem DenseRange.topologicalClosure_span_iUnion_range_comp_eq {R α ι X Y : Type*} [Semiring R]
    [TopologicalSpace α] [AddCommMonoid Y] [TopologicalSpace Y] [Module R Y] [ContinuousAdd Y]
    [ContinuousConstSMul R Y] {g : ι → α} (hg : DenseRange g) {L : α → X → Y}
    (hL : ∀ x, Continuous fun a => L a x) :
    (Submodule.span R (⋃ i, Set.range (L (g i)))).topologicalClosure =
      (Submodule.span R (⋃ a, Set.range (L a))).topologicalClosure := by
  set S := Submodule.span R (⋃ i, Set.range (L (g i)))
  refine le_antisymm (Submodule.topologicalClosure_mono <| Submodule.span_mono <|
    Set.iUnion_subset fun i => Set.subset_iUnion (fun a => Set.range (L a)) (g i))
    (Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) S.isClosed_topologicalClosure)
  rintro _ ⟨_, ⟨a, rfl⟩, x, rfl⟩
  refine (S.isClosed_topologicalClosure.preimage (hL x)).closure_subset_iff.2 ?_ (hg a)
  rintro _ ⟨i, rfl⟩
  exact Submodule.le_topologicalClosure S (Submodule.subset_span (Set.mem_iUnion.2 ⟨i, x, rfl⟩))

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  {S : Submodule 𝕜 E}

/-- If a closed subspace `S` of finite codimension and the span of a set `s` together span a dense
subspace, then `S` and finitely many vectors of `s` already span the whole space. -/
theorem exists_finset_subset_sup_span_eq_top_of_dense (hS : IsClosed (S : Set E))
    [FiniteDimensional 𝕜 (E ⧸ S)] {s : Set E}
    (hs : Dense ((S ⊔ span 𝕜 s : Submodule 𝕜 E) : Set E)) :
    ∃ t : Finset E, ↑t ⊆ s ∧ S ⊔ span 𝕜 (t : Set E) = ⊤ := by
  have htop : S ⊔ span 𝕜 s = ⊤ := by
    simpa only [← sup_assoc, sup_idem] using sup_eq_top_of_dense hS hs
  -- The images of `s` span the finite-dimensional quotient `E ⧸ S`, so finitely many of them do.
  have hq : span 𝕜 (S.mkQ '' s) = ⊤ := by
    rw [← map_span, ← comap_injective_of_surjective S.mkQ_surjective |>.eq_iff, comap_map_mkQ,
      htop, comap_top]
  obtain ⟨t', ht's, -, ht', -⟩ := exists_finset_span_eq_linearIndepOn 𝕜 (S.mkQ '' s)
  obtain ⟨u, hus, hu, hut'⟩ :=
    (Set.exists_subset_image_finite_and (p := fun v ↦ v = (t' : Set (E ⧸ S)))).1
      ⟨_, ht's, t'.finite_toSet, rfl⟩
  refine ⟨hu.toFinset, by simpa using hus, ?_⟩
  rw [← comap_map_mkQ, map_span, Set.Finite.coe_toFinset, hut', ht', hq, comap_top]

end Submodule
