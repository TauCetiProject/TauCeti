/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# The signless algebra of a bipartite graph

A two-colouring of a simple graph gives a source--sink orientation by directing every edge toward
its `true` endpoint. Symmetrifying this oriented quiver recovers the doubled quiver. Under that
identification, the signless relation of the graph becomes the signless relation of the
symmetrified orientation.

Since every arrow of the oriented quiver goes from a `false` vertex to a `true` vertex, the
signless/preprojective comparison needs no further arrow rescaling. Thus the signless
preprojective algebra of the doubled graph is explicitly isomorphic to the additive
preprojective algebra of its source--sink orientation.

## Main definitions

* `TauCeti.DoubledQuiver.Orientation.sourceSink`: the orientation directed toward colour `true`.
* `TauCeti.DoubledQuiver.sourceSinkPathAlgebraEquiv`: the path-algebra comparison induced by
  restoring the orientation.
* `TauCeti.DoubledQuiver.sourceSinkSignlessPreprojectiveAlgebraEquiv`: the comparison between the
  graph's signless algebra and the preprojective algebra of the source--sink orientation.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060, for the signless relation and its comparison with the
preprojective relation of a bipartite graph.
-/

public section

attribute [local instance] Fintype.ofFinite

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u w

namespace DoubledQuiver

variable {V : Type u} {G : SimpleGraph V}

variable (C : G.Coloring Bool)

/-- The colour of a vertex of the oriented quiver, transported from the graph. -/
def sourceSinkColor (i : OrientedQuiver G (Orientation.sourceSink C)) : Bool :=
  C ((OrientedQuiver.vertexEquiv G (Orientation.sourceSink C)).symm i)

/-- The colour on the source--sink oriented quiver is the original graph colouring. -/
@[simp]
theorem sourceSinkColor_vertex (i : V) :
    sourceSinkColor C (OrientedQuiver.vertex G (Orientation.sourceSink C) i) = C i := by
  rw [sourceSinkColor, OrientedQuiver.vertexEquiv_symm_vertex]

/-- Every arrow of the source--sink orientation has differently coloured endpoints. -/
theorem sourceSinkColor_ne {i j : OrientedQuiver G (Orientation.sourceSink C)} (a : i ⟶ j) :
    sourceSinkColor C i ≠ sourceSinkColor C j := by
  exact C.valid a.1

/-- Every arrow of the source--sink orientation ends at a vertex of colour `true`. -/
theorem sourceSinkColor_target_eq_true
    {i j : OrientedQuiver G (Orientation.sourceSink C)} (a : i ⟶ j) :
    sourceSinkColor C j = true := by
  rw [sourceSinkColor]
  exact (Orientation.mem_sourceSink_iff C _).mp a.2

variable (k : Type w) [CommRing k] [Finite V]

/-- The path-algebra isomorphism which restores the source--sink orientation of a bipartite graph.
It sends every doubled arrow to the corresponding positive or negative arrow in the
symmetrification. -/
noncomputable def sourceSinkPathAlgebraEquiv :
    pathAlgebra k (DoubledQuiver G) ≃ₐ[k]
      pathAlgebra k (Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) :=
  PathAlgebra.mapAlgEquiv k
    (unsymmetrifyMap G (Orientation.sourceSink C))
    (symmetrifyMap G (Orientation.sourceSink C))
    (unsymmetrifyMap_comp_symmetrifyMap G (Orientation.sourceSink C))
    (symmetrifyMap_comp_unsymmetrifyMap G (Orientation.sourceSink C))

/-- The source--sink path-algebra comparison is induced by the inverse orientation prefunctor. -/
theorem sourceSinkPathAlgebraEquiv_apply (x : pathAlgebra k (DoubledQuiver G)) :
    sourceSinkPathAlgebraEquiv C k x =
      PathAlgebra.mapAlgHom k (unsymmetrifyMap G (Orientation.sourceSink C))
        ((unsymmetrifyMap G (Orientation.sourceSink C)).obj_bijective_of_comp_eq_id
          (symmetrifyMap G (Orientation.sourceSink C))
          (unsymmetrifyMap_comp_symmetrifyMap G (Orientation.sourceSink C))
          (symmetrifyMap_comp_unsymmetrifyMap G (Orientation.sourceSink C))) x := by
  rw [sourceSinkPathAlgebraEquiv, PathAlgebra.mapAlgEquiv_apply]

/-- The source--sink path-algebra comparison sends a basis path to the path obtained by restoring
the chosen orientation of each arrow. -/
@[simp]
theorem sourceSinkPathAlgebraEquiv_ofPath (x : Quiver.TotalPath (DoubledQuiver G)) :
    sourceSinkPathAlgebraEquiv C k (ofPath x) =
      ofPath ((unsymmetrifyMap G (Orientation.sourceSink C)).mapTotalPath x) := by
  rw [sourceSinkPathAlgebraEquiv_apply, PathAlgebra.mapAlgHom_ofPath]

/-- The inverse source--sink path-algebra comparison is induced by forgetting the orientation. -/
theorem sourceSinkPathAlgebraEquiv_symm_apply
    (x : pathAlgebra k (Symmetrify (OrientedQuiver G (Orientation.sourceSink C)))) :
    (sourceSinkPathAlgebraEquiv C k).symm x =
      PathAlgebra.mapAlgHom k (symmetrifyMap G (Orientation.sourceSink C))
        ((symmetrifyMap G (Orientation.sourceSink C)).obj_bijective_of_comp_eq_id
          (unsymmetrifyMap G (Orientation.sourceSink C))
          (symmetrifyMap_comp_unsymmetrifyMap G (Orientation.sourceSink C))
          (unsymmetrifyMap_comp_symmetrifyMap G (Orientation.sourceSink C))) x := by
  rw [sourceSinkPathAlgebraEquiv, PathAlgebra.mapAlgEquiv_symm_apply]

/-- The inverse path-algebra comparison sends a basis path to the path obtained by forgetting the
chosen orientation of each arrow. -/
@[simp]
theorem sourceSinkPathAlgebraEquiv_symm_ofPath
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver G (Orientation.sourceSink C)))) :
    (sourceSinkPathAlgebraEquiv C k).symm (ofPath x) =
      ofPath ((symmetrifyMap G (Orientation.sourceSink C)).mapTotalPath x) := by
  rw [sourceSinkPathAlgebraEquiv_symm_apply, PathAlgebra.mapAlgHom_ofPath]

/-- Restoring the source--sink orientation carries each signless graph relator to the signless
relator at the corresponding vertex of the symmetrified oriented quiver. -/
@[simp]
theorem sourceSinkPathAlgebraEquiv_signlessPreprojectiveRelator
    (i : DoubledQuiver G) :
    sourceSinkPathAlgebraEquiv C k (signlessPreprojectiveRelator k i) =
      signlessPreprojectiveRelator k
        ((unsymmetrifyMap G (Orientation.sourceSink C)).obj i) := by
  rw [sourceSinkPathAlgebraEquiv_apply,
    mapAlgHom_signlessPreprojectiveRelator k _ _
      ((unsymmetrifyMap_isCovering G (Orientation.sourceSink C)).star_bijective i)]

/-- The inverse path-algebra comparison also carries signless relators to signless relators. -/
@[simp]
theorem sourceSinkPathAlgebraEquiv_symm_signlessPreprojectiveRelator
    (i : Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) :
    (sourceSinkPathAlgebraEquiv C k).symm (signlessPreprojectiveRelator k i) =
      signlessPreprojectiveRelator k
        ((symmetrifyMap G (Orientation.sourceSink C)).obj i) := by
  rw [sourceSinkPathAlgebraEquiv_symm_apply,
    mapAlgHom_signlessPreprojectiveRelator k _ _
      ((symmetrifyMap_isCovering G (Orientation.sourceSink C)).star_bijective i)]

/-! ### Transporting the signless quotient -/

/-- The path-algebra comparison maps the doubled graph's signless ideal onto the signless ideal of
the symmetrified source--sink orientation. -/
private theorem sourceSinkSignlessPreprojectiveIdeal_map_eq :
    (signlessPreprojectiveIdeal k
        (Symmetrify (OrientedQuiver G (Orientation.sourceSink C)))).asIdeal =
      (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal.map
        (sourceSinkPathAlgebraEquiv C k : _ →+* _) := by
  have hforward : signlessPreprojectiveIdeal k (DoubledQuiver G) ≤
      (signlessPreprojectiveIdeal k
        (Symmetrify (OrientedQuiver G (Orientation.sourceSink C)))).comap
          (sourceSinkPathAlgebraEquiv C k).toRingHom := by
    rw [signlessPreprojectiveIdeal_eq_span, TwoSidedIdeal.span_le]
    rintro _ ⟨i, rfl⟩
    apply (TwoSidedIdeal.mem_comap (sourceSinkPathAlgebraEquiv C k).toRingHom).mpr
    -- Expose the algebra equivalence hidden by the underlying ring-hom coercion.
    change sourceSinkPathAlgebraEquiv C k (signlessPreprojectiveRelator k i) ∈ _
    rw [sourceSinkPathAlgebraEquiv_signlessPreprojectiveRelator]
    exact signlessPreprojectiveRelator_mem_signlessPreprojectiveIdeal k _
  have hbackward :
      signlessPreprojectiveIdeal k
          (Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) ≤
        (signlessPreprojectiveIdeal k (DoubledQuiver G)).comap
          (sourceSinkPathAlgebraEquiv C k).symm.toRingHom := by
    rw [signlessPreprojectiveIdeal_eq_span, TwoSidedIdeal.span_le]
    rintro _ ⟨i, rfl⟩
    apply (TwoSidedIdeal.mem_comap
      (sourceSinkPathAlgebraEquiv C k).symm.toRingHom).mpr
    -- Expose the algebra equivalence hidden by the underlying ring-hom coercion.
    change (sourceSinkPathAlgebraEquiv C k).symm (signlessPreprojectiveRelator k i) ∈ _
    rw [sourceSinkPathAlgebraEquiv_symm_signlessPreprojectiveRelator]
    exact signlessPreprojectiveRelator_mem_signlessPreprojectiveIdeal k _
  ext y
  constructor
  · intro hy
    apply (Ideal.mem_map_of_equiv (sourceSinkPathAlgebraEquiv C k) y).mpr
    exact ⟨(sourceSinkPathAlgebraEquiv C k).symm y,
      (TwoSidedIdeal.mem_comap
        (sourceSinkPathAlgebraEquiv C k).symm.toRingHom).mp (hbackward hy),
      (sourceSinkPathAlgebraEquiv C k).apply_symm_apply y⟩
  · intro hy
    obtain ⟨z, hz, rfl⟩ :=
      (Ideal.mem_map_of_equiv (sourceSinkPathAlgebraEquiv C k) y).mp hy
    exact (TwoSidedIdeal.mem_comap
      (sourceSinkPathAlgebraEquiv C k).toRingHom).mp (hforward hz)

/-- Restoring a source--sink orientation identifies the signless algebra of the doubled graph
with the signless algebra of the symmetrified oriented quiver. -/
private noncomputable def sourceSinkSignlessQuotientEquiv :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) ≃ₐ[k]
      signlessPreprojectiveAlgebra k
        (Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) :=
  Ideal.quotientEquivAlg (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal
    (signlessPreprojectiveIdeal k
      (Symmetrify (OrientedQuiver G (Orientation.sourceSink C)))).asIdeal
    (sourceSinkPathAlgebraEquiv C k) (sourceSinkSignlessPreprojectiveIdeal_map_eq C k)

/-- The signless-quotient comparison is induced by the path-algebra comparison. -/
@[simp]
private theorem sourceSinkSignlessQuotientEquiv_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    sourceSinkSignlessQuotientEquiv C k (signlessPreprojectiveMk k _ x) =
      signlessPreprojectiveMk k _ (sourceSinkPathAlgebraEquiv C k x) := by
  rw [signlessPreprojectiveMk_apply, signlessPreprojectiveMk_apply,
    sourceSinkSignlessQuotientEquiv, Ideal.quotientEquivAlg_mk]

/-! ### The preprojective comparison -/

/-- **The signless algebra of a bipartite graph is the additive preprojective algebra of its
source--sink orientation.** The isomorphism first identifies the doubled quiver with the
symmetrification of the oriented graph; no further arrow rescaling is needed. -/
noncomputable def sourceSinkSignlessPreprojectiveAlgebraEquiv :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) ≃ₐ[k]
      preprojectiveAlgebra k (OrientedQuiver G (Orientation.sourceSink C)) :=
  (sourceSinkSignlessQuotientEquiv C k).trans
    (symmetrifySignlessPreprojectiveAlgebraEquiv k
      (c := sourceSinkColor C) (fun {_ _} a => sourceSinkColor_ne (G := G) C a))

/-- The bipartite comparison sends the class of a doubled-path-algebra element to its image under
the source--sink identification, followed by the standard preprojective quotient map. -/
@[simp]
theorem sourceSinkSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    sourceSinkSignlessPreprojectiveAlgebraEquiv C k
        (signlessPreprojectiveMk k _ x) =
      preprojectiveMk k (OrientedQuiver G (Orientation.sourceSink C))
        (sourceSinkPathAlgebraEquiv C k x) := by
  rw [sourceSinkSignlessPreprojectiveAlgebraEquiv, AlgEquiv.trans_apply,
    sourceSinkSignlessQuotientEquiv_signlessPreprojectiveMk,
    symmetrifySignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk_of_forall_head
      k (c := sourceSinkColor C) (fun {_ _} a => sourceSinkColor_ne (G := G) C a)
        (fun {_ _} a => sourceSinkColor_target_eq_true (G := G) C a)]

/-- The inverse bipartite comparison sends a preprojective representative through the inverse
source--sink path-algebra identification. -/
@[simp]
theorem sourceSinkSignlessPreprojectiveAlgebraEquiv_symm_preprojectiveMk
    (x : pathAlgebra k (Symmetrify (OrientedQuiver G (Orientation.sourceSink C)))) :
    (sourceSinkSignlessPreprojectiveAlgebraEquiv C k).symm
        (preprojectiveMk k (OrientedQuiver G (Orientation.sourceSink C)) x) =
      signlessPreprojectiveMk k (DoubledQuiver G)
        ((sourceSinkPathAlgebraEquiv C k).symm x) := by
  apply (sourceSinkSignlessPreprojectiveAlgebraEquiv C k).injective
  rw [AlgEquiv.apply_symm_apply,
    sourceSinkSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
    AlgEquiv.apply_symm_apply]

end DoubledQuiver

end TauCeti
