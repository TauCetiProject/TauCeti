/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import TauCeti.RepresentationTheory.Quiver.Preprojective.Bipartite
import TauCeti.RepresentationTheory.Quiver.Zigzag.Connected

/-!
# Signless and preprojective relations of an oriented graph

A two-colouring of a simple graph gives a source--sink orientation by directing every edge toward
its `true` endpoint. Symmetrifying this oriented quiver recovers the doubled quiver. Under that
identification, the signless relation of the graph becomes the signless relation of the
symmetrified orientation.

Since every arrow of the oriented quiver goes from a `false` vertex to a `true` vertex, the
signless/preprojective comparison needs no further arrow rescaling. Thus the signless
preprojective algebra of the doubled graph is explicitly isomorphic to the additive
preprojective algebra of its source--sink orientation.

Conversely, suppose that a unit gauge makes every corner of the preprojective relator a scalar
multiple of the corresponding signless relator. The comparison scalars change sign along every
edge. A non-bipartite graph has an odd closed walk, which would therefore force `2 = 0`. Over a
coefficient ring in which `2 ≠ 0`, a non-bipartite graph therefore admits no such comparison, for
any choice of orientation.

## Main definitions

* `SimpleGraph.Coloring.sourceSink`: the orientation directed toward colour `true`.
* `TauCeti.DoubledQuiver.orientationPathAlgebraEquiv`: the path-algebra comparison induced by
  restoring an orientation.
* `TauCeti.DoubledQuiver.orientationSignlessPreprojectiveAlgebraEquiv`: the induced comparison
  between the signless algebra of the doubled graph and the signless algebra of a symmetrified
  orientation.
* `SimpleGraph.Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv`: the comparison between the
  graph's signless algebra and the preprojective algebra of the source--sink orientation.
* `TauCeti.DoubledQuiver.Orientation.not_exists_forall_vertexCorner_eq_smul_of_not_isBipartite`:
  over coefficients with `2 ≠ 0`, a non-bipartite graph admits no cornerwise unit-gauge
  comparison.

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

section PathAlgebra

variable (o : Orientation G) (k : Type w) [CommSemiring k] [Finite V]

/-- The path-algebra isomorphism which restores an orientation of a graph. It sends every doubled
arrow to the corresponding positive or negative arrow in the symmetrification. -/
noncomputable def orientationPathAlgebraEquiv :
    pathAlgebra k (DoubledQuiver G) ≃ₐ[k]
      pathAlgebra k (Symmetrify (OrientedQuiver G o)) :=
  PathAlgebra.mapAlgEquiv k
    (unsymmetrifyMap G o)
    (symmetrifyMap G o)
    (unsymmetrifyMap_comp_symmetrifyMap G o)
    (symmetrifyMap_comp_unsymmetrifyMap G o)

/-- The orientation path-algebra comparison is induced by the inverse orientation prefunctor. -/
theorem orientationPathAlgebraEquiv_apply (x : pathAlgebra k (DoubledQuiver G)) :
    orientationPathAlgebraEquiv o k x =
      PathAlgebra.mapAlgHom k (unsymmetrifyMap G o)
        ((unsymmetrifyMap G o).obj_bijective_of_comp_eq_id
          (symmetrifyMap G o)
          (unsymmetrifyMap_comp_symmetrifyMap G o)
          (symmetrifyMap_comp_unsymmetrifyMap G o)) x := by
  rw [orientationPathAlgebraEquiv, PathAlgebra.mapAlgEquiv_apply]

/-- The orientation path-algebra comparison sends a basis path to the path obtained by restoring
the orientation of each arrow. -/
@[simp]
theorem orientationPathAlgebraEquiv_ofPath (x : Quiver.TotalPath (DoubledQuiver G)) :
    orientationPathAlgebraEquiv o k (ofPath x) =
      ofPath ((unsymmetrifyMap G o).mapTotalPath x) := by
  rw [orientationPathAlgebraEquiv_apply, PathAlgebra.mapAlgHom_ofPath]

/-- The inverse orientation path-algebra comparison is induced by forgetting the orientation. -/
theorem orientationPathAlgebraEquiv_symm_apply
    (x : pathAlgebra k (Symmetrify (OrientedQuiver G o))) :
    (orientationPathAlgebraEquiv o k).symm x =
      PathAlgebra.mapAlgHom k (symmetrifyMap G o)
        ((symmetrifyMap G o).obj_bijective_of_comp_eq_id
          (unsymmetrifyMap G o)
          (symmetrifyMap_comp_unsymmetrifyMap G o)
          (unsymmetrifyMap_comp_symmetrifyMap G o)) x := by
  rw [orientationPathAlgebraEquiv, PathAlgebra.mapAlgEquiv_symm_apply]

/-- The inverse path-algebra comparison sends a basis path to the path obtained by forgetting the
chosen orientation of each arrow. -/
@[simp]
theorem orientationPathAlgebraEquiv_symm_ofPath
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver G o))) :
    (orientationPathAlgebraEquiv o k).symm (ofPath x) =
      ofPath ((symmetrifyMap G o).mapTotalPath x) := by
  rw [orientationPathAlgebraEquiv_symm_apply, PathAlgebra.mapAlgHom_ofPath]

/-- Restoring an orientation carries each signless graph relator to the signless relator at the
corresponding vertex of the symmetrified oriented quiver. -/
@[simp]
theorem orientationPathAlgebraEquiv_signlessPreprojectiveRelator
    (i : DoubledQuiver G) :
    orientationPathAlgebraEquiv o k (signlessPreprojectiveRelator k i) =
      signlessPreprojectiveRelator k
        ((unsymmetrifyMap G o).obj i) := by
  rw [orientationPathAlgebraEquiv_apply,
    mapAlgHom_signlessPreprojectiveRelator k _ _
      ((unsymmetrifyMap_isCovering G o).star_bijective i)]

/-- The inverse path-algebra comparison also carries signless relators to signless relators. -/
@[simp]
theorem orientationPathAlgebraEquiv_symm_signlessPreprojectiveRelator
    (i : Symmetrify (OrientedQuiver G o)) :
    (orientationPathAlgebraEquiv o k).symm (signlessPreprojectiveRelator k i) =
      signlessPreprojectiveRelator k
        ((symmetrifyMap G o).obj i) := by
  rw [orientationPathAlgebraEquiv_symm_apply,
    mapAlgHom_signlessPreprojectiveRelator k _ _
      ((symmetrifyMap_isCovering G o).star_bijective i)]

end PathAlgebra

/-! ### Transporting the signless quotient -/

section Quotient

variable (o : Orientation G) (k : Type w) [CommRing k] [Finite V]

/-- The path-algebra comparison maps the doubled graph's signless ideal onto the signless ideal of
the symmetrified orientation. -/
private theorem orientationSignlessPreprojectiveIdeal_map_eq :
    (signlessPreprojectiveIdeal k
        (Symmetrify (OrientedQuiver G o))).asIdeal =
      (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal.map
        (orientationPathAlgebraEquiv o k : _ →+* _) := by
  have hforward : signlessPreprojectiveIdeal k (DoubledQuiver G) ≤
      (signlessPreprojectiveIdeal k
        (Symmetrify (OrientedQuiver G o))).comap
          (orientationPathAlgebraEquiv o k).toRingHom := by
    rw [signlessPreprojectiveIdeal_eq_span, TwoSidedIdeal.span_le]
    rintro _ ⟨i, rfl⟩
    apply (TwoSidedIdeal.mem_comap
      (orientationPathAlgebraEquiv o k).toRingHom).mpr
    -- Expose the algebra equivalence hidden by the underlying ring-hom coercion.
    change orientationPathAlgebraEquiv o k
      (signlessPreprojectiveRelator k i) ∈ _
    rw [orientationPathAlgebraEquiv_signlessPreprojectiveRelator]
    exact signlessPreprojectiveRelator_mem_signlessPreprojectiveIdeal k _
  have hbackward :
      signlessPreprojectiveIdeal k
          (Symmetrify (OrientedQuiver G o)) ≤
        (signlessPreprojectiveIdeal k (DoubledQuiver G)).comap
          (orientationPathAlgebraEquiv o k).symm.toRingHom := by
    rw [signlessPreprojectiveIdeal_eq_span, TwoSidedIdeal.span_le]
    rintro _ ⟨i, rfl⟩
    apply (TwoSidedIdeal.mem_comap
      (orientationPathAlgebraEquiv o k).symm.toRingHom).mpr
    -- Expose the algebra equivalence hidden by the underlying ring-hom coercion.
    change (orientationPathAlgebraEquiv o k).symm
      (signlessPreprojectiveRelator k i) ∈ _
    rw [orientationPathAlgebraEquiv_symm_signlessPreprojectiveRelator]
    exact signlessPreprojectiveRelator_mem_signlessPreprojectiveIdeal k _
  have hforward' : (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal ≤
      (signlessPreprojectiveIdeal k
        (Symmetrify (OrientedQuiver G o))).asIdeal.comap
          (orientationPathAlgebraEquiv o k).toRingHom :=
    fun _ hx => by
      simpa only [Ideal.mem_comap, TwoSidedIdeal.mem_asIdeal,
        TwoSidedIdeal.mem_comap] using hforward hx
  have hbackward' :
      (signlessPreprojectiveIdeal k
        (Symmetrify (OrientedQuiver G o))).asIdeal ≤
      (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal.comap
        (orientationPathAlgebraEquiv o k).symm.toRingHom :=
    fun _ hx => by
      simpa only [Ideal.mem_comap, TwoSidedIdeal.mem_asIdeal,
        TwoSidedIdeal.mem_comap] using hbackward hx
  apply le_antisymm
  · calc
      _ ≤ (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal.comap
          (orientationPathAlgebraEquiv o k).symm.toRingHom := hbackward'
      _ = (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal.map
          (orientationPathAlgebraEquiv o k).toRingHom :=
        (Ideal.map_comap_of_equiv
          (orientationPathAlgebraEquiv o k).toRingEquiv).symm
  · exact Ideal.map_le_iff_le_comap.mpr hforward'

/-- Restoring an orientation identifies the signless algebra of the doubled graph with the
signless algebra of the symmetrified oriented quiver. -/
noncomputable def orientationSignlessPreprojectiveAlgebraEquiv :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) ≃ₐ[k]
      signlessPreprojectiveAlgebra k
        (Symmetrify (OrientedQuiver G o)) :=
  Ideal.quotientEquivAlg (signlessPreprojectiveIdeal k (DoubledQuiver G)).asIdeal
    (signlessPreprojectiveIdeal k
      (Symmetrify (OrientedQuiver G o))).asIdeal
    (orientationPathAlgebraEquiv o k)
    (orientationSignlessPreprojectiveIdeal_map_eq o k)

/-- The signless-quotient comparison is induced by the path-algebra comparison. -/
@[simp]
theorem orientationSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    orientationSignlessPreprojectiveAlgebraEquiv o k (signlessPreprojectiveMk k _ x) =
      signlessPreprojectiveMk k _
        (orientationPathAlgebraEquiv o k x) := by
  rw [signlessPreprojectiveMk_apply, signlessPreprojectiveMk_apply,
    orientationSignlessPreprojectiveAlgebraEquiv, Ideal.quotientEquivAlg_mk]

end Quotient

end DoubledQuiver

end TauCeti

namespace SimpleGraph.Coloring

open TauCeti TauCeti.DoubledQuiver TauCeti.PathAlgebra _root_.Quiver

universe u w

variable {V : Type u} {G : SimpleGraph V}

variable (C : G.Coloring Bool)

/-- The colour of a vertex of the oriented quiver, transported from the graph. -/
def sourceSinkColor (i : OrientedQuiver G C.sourceSink) : Bool :=
  C ((OrientedQuiver.vertexEquiv G C.sourceSink).symm i)

/-- The colour on the source--sink oriented quiver is the original graph colouring. -/
@[simp]
theorem sourceSinkColor_vertex (i : V) :
    C.sourceSinkColor (OrientedQuiver.vertex G C.sourceSink i) = C i := by
  rw [sourceSinkColor, OrientedQuiver.vertexEquiv_symm_vertex]

/-- Every arrow of the source--sink orientation has differently coloured endpoints. -/
theorem sourceSinkColor_ne {i j : OrientedQuiver G C.sourceSink} (a : i ⟶ j) :
    C.sourceSinkColor i ≠ C.sourceSinkColor j := by
  exact C.valid a.1

/-- Every arrow of the source--sink orientation ends at a vertex of colour `true`. -/
theorem sourceSinkColor_target_eq_true
    {i j : OrientedQuiver G C.sourceSink} (a : i ⟶ j) :
    C.sourceSinkColor j = true := by
  rw [sourceSinkColor]
  exact (mem_sourceSink_iff C _).mp a.2

/-! ### The preprojective comparison -/

variable (k : Type w) [CommRing k] [Finite V]

/-- **The signless algebra of a bipartite graph is the additive preprojective algebra of its
source--sink orientation.** The isomorphism first identifies the doubled quiver with the
symmetrification of the oriented graph; no further arrow rescaling is needed. -/
noncomputable def sourceSinkSignlessPreprojectiveAlgebraEquiv :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) ≃ₐ[k]
      preprojectiveAlgebra k (OrientedQuiver G C.sourceSink) :=
  (orientationSignlessPreprojectiveAlgebraEquiv C.sourceSink k).trans
    (symmetrifySignlessPreprojectiveAlgebraEquiv k
      (c := C.sourceSinkColor) (fun {_ _} a => C.sourceSinkColor_ne a))

/-- The bipartite comparison sends the class of a doubled-path-algebra element to its image under
the source--sink identification, followed by the standard preprojective quotient map. -/
@[simp]
theorem sourceSinkSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    C.sourceSinkSignlessPreprojectiveAlgebraEquiv k
        (signlessPreprojectiveMk k _ x) =
      preprojectiveMk k (OrientedQuiver G C.sourceSink)
        (orientationPathAlgebraEquiv C.sourceSink k x) := by
  rw [sourceSinkSignlessPreprojectiveAlgebraEquiv, AlgEquiv.trans_apply,
    orientationSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
    symmetrifySignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk_of_forall_head
      k (c := C.sourceSinkColor) (fun {_ _} a => C.sourceSinkColor_ne a)
        (fun {_ _} a => C.sourceSinkColor_target_eq_true a)]

/-- The inverse bipartite comparison sends a preprojective representative through the inverse
source--sink path-algebra identification. -/
@[simp]
theorem sourceSinkSignlessPreprojectiveAlgebraEquiv_symm_preprojectiveMk
    (x : pathAlgebra k (Symmetrify (OrientedQuiver G C.sourceSink))) :
    (C.sourceSinkSignlessPreprojectiveAlgebraEquiv k).symm
        (preprojectiveMk k (OrientedQuiver G C.sourceSink) x) =
      signlessPreprojectiveMk k (DoubledQuiver G)
        ((orientationPathAlgebraEquiv C.sourceSink k).symm x) := by
  apply (C.sourceSinkSignlessPreprojectiveAlgebraEquiv k).injective
  rw [AlgEquiv.apply_symm_apply,
    sourceSinkSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
    AlgEquiv.apply_symm_apply]

end SimpleGraph.Coloring

namespace TauCeti.DoubledQuiver.Orientation

open _root_.Quiver

universe u w

variable {V : Type u} {G : SimpleGraph V}

/-! ### The non-bipartite obstruction -/

/-- **A non-bipartite graph admits no cornerwise signless comparison.** For any orientation of a
finite simple graph, an odd closed graph walk maps to an odd closed path in the symmetrified
oriented quiver. Hence, when `2 ≠ 0`, no unit gauge makes every corner of the gauged
preprojective relator a scalar multiple of the corresponding signless relator. -/
theorem not_exists_forall_vertexCorner_eq_smul_of_not_isBipartite
    (o : Orientation G) (k : Type w) [CommRing k] [Finite V]
    (hG : ¬ G.IsBipartite)
    {ε : ∀ ⦃i j : OrientedQuiver G o⦄, (i ⟶ j) → k}
    (hε : ∀ ⦃i j : OrientedQuiver G o⦄ (a : i ⟶ j), IsUnit (ε a))
    (h2 : (2 : k) ≠ 0) :
    ¬ ∃ c : OrientedQuiver G o → k,
        ∀ v : OrientedQuiver G o,
          doubledVertexIdempotent k v * gaugedPreprojectiveRelator k ε *
              doubledVertexIdempotent k v =
            c v • signlessPreprojectiveRelator k (Symmetrify.of.obj v) := by
  classical
  -- `SimpleGraph.IsBipartite` is an abbreviation for `SimpleGraph.Colorable 2`.
  have hwalk : ¬ ∀ u, ∀ w : G.Walk u u, Even w.length := fun h =>
    hG (SimpleGraph.two_colorable_iff_forall_loop_even.mpr h)
  push Not at hwalk
  obtain ⟨v, p, hp⟩ := hwalk
  have hpodd : Odd p.length := Nat.not_even_iff_odd.mp hp
  let q₀ := (unsymmetrifyMap G o).mapPath (walkToPath G p)
  have hq₀odd : Odd q₀.length := by simpa [q₀] using hpodd
  have hobj : (unsymmetrifyMap G o).obj (vertex G v) =
      Symmetrify.of.obj (OrientedQuiver.vertex G o v) :=
    unsymmetrifyMap_obj G o v
  let q : Quiver.Path (Symmetrify.of.obj (OrientedQuiver.vertex G o v))
      (Symmetrify.of.obj (OrientedQuiver.vertex G o v)) :=
    q₀.cast hobj hobj
  have length_cast : ∀ {a b c d : Symmetrify (OrientedQuiver G o)}
      (ha : a = c) (hb : b = d) (r : Quiver.Path a b),
      (r.cast ha hb).length = r.length := by
    intro a b c d ha hb r
    subst c
    subst d
    rfl
  have hlength : q.length = q₀.length := length_cast hobj hobj q₀
  have hqodd : Odd q.length := by
    rw [hlength]
    exact hq₀odd
  apply TauCeti.not_exists_forall_vertexCorner_eq_smul_of_odd_length k hε h2 q
  exact hqodd

end TauCeti.DoubledQuiver.Orientation
