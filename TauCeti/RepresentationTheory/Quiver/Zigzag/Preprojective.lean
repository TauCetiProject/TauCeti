/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

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

namespace Orientation

/-- The **source--sink orientation** supplied by a two-colouring: an edge is directed toward its
endpoint of colour `true`. -/
def sourceSink (C : G.Coloring Bool) : Orientation G where
  carrier := {d | C d.snd = true}
  symm_mem_iff_not_mem d := by
    -- Unfolding membership exposes the two endpoint colours, which `C.valid` says are unequal.
    change C d.fst = true ↔ C d.snd ≠ true
    have h := C.valid d.adj
    cases hi : C d.fst <;> cases hj : C d.snd <;> simp_all

/-- A dart belongs to the source--sink orientation exactly when its target has colour `true`. -/
@[simp]
theorem mem_sourceSink_iff (C : G.Coloring Bool) (d : G.Dart) :
    d ∈ sourceSink C ↔ C d.snd = true :=
  Iff.rfl

end Orientation

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
  exact a.2

variable (k : Type w) [CommRing k] [Finite V]

/-- The path-algebra isomorphism which forgets the source--sink orientation of a bipartite graph.
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

/-- Forgetting the source--sink orientation carries each signless graph relator to the signless
relator at the corresponding vertex of the symmetrified oriented quiver. -/
@[simp]
theorem sourceSinkPathAlgebraEquiv_signlessPreprojectiveRelator
    (i : DoubledQuiver G) :
    sourceSinkPathAlgebraEquiv C k (signlessPreprojectiveRelator k i) =
      signlessPreprojectiveRelator k
        ((unsymmetrifyMap G (Orientation.sourceSink C)).obj i) := by
  rw [sourceSinkPathAlgebraEquiv_apply,
    mapAlgHom_signlessPreprojectiveRelator k _ _
      ((unsymmetrifyMapIsCovering G (Orientation.sourceSink C)).star_bijective i)]

/-- The inverse path-algebra comparison also carries signless relators to signless relators. -/
@[simp]
theorem sourceSinkPathAlgebraEquiv_symm_signlessPreprojectiveRelator
    (i : Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) :
    (sourceSinkPathAlgebraEquiv C k).symm (signlessPreprojectiveRelator k i) =
      signlessPreprojectiveRelator k
        ((symmetrifyMap G (Orientation.sourceSink C)).obj i) := by
  rw [sourceSinkPathAlgebraEquiv_symm_apply,
    mapAlgHom_signlessPreprojectiveRelator k _ _
      ((symmetrifyMapIsCovering G (Orientation.sourceSink C)).star_bijective i)]

/-! ### Transporting the signless quotient -/

/-- The forward map between the signless quotients. It is kept private because the algebra
equivalence below is the canonical public comparison. -/
private noncomputable def sourceSinkSignlessPreprojectiveHom :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) →ₐ[k]
      signlessPreprojectiveAlgebra k
        (Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) :=
  signlessPreprojectiveLift
    ((signlessPreprojectiveMk k _).comp (sourceSinkPathAlgebraEquiv C k).toAlgHom) fun i => by
      rw [AlgHom.comp_apply]
      calc
        signlessPreprojectiveMk k _
            ((sourceSinkPathAlgebraEquiv C k) (signlessPreprojectiveRelator k i)) =
          signlessPreprojectiveMk k _
            (signlessPreprojectiveRelator k
              ((unsymmetrifyMap G (Orientation.sourceSink C)).obj i)) :=
          congrArg (signlessPreprojectiveMk k _)
            (sourceSinkPathAlgebraEquiv_signlessPreprojectiveRelator C k i)
        _ = 0 := signlessPreprojectiveMk_signlessPreprojectiveRelator k _

/-- The forward quotient map sends a representative to the class of its image under the
source--sink path-algebra comparison. -/
private theorem sourceSinkSignlessPreprojectiveHom_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    sourceSinkSignlessPreprojectiveHom C k (signlessPreprojectiveMk k _ x) =
      signlessPreprojectiveMk k _ (sourceSinkPathAlgebraEquiv C k x) :=
  signlessPreprojectiveLift_signlessPreprojectiveMk _ _ x

/-- The inverse map between the signless quotients. -/
private noncomputable def sourceSinkSignlessPreprojectiveHomInv :
    signlessPreprojectiveAlgebra k
        (Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) →ₐ[k]
      signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  signlessPreprojectiveLift
    ((signlessPreprojectiveMk k _).comp (sourceSinkPathAlgebraEquiv C k).symm.toAlgHom) fun i => by
      rw [AlgHom.comp_apply]
      calc
        signlessPreprojectiveMk k _
            ((sourceSinkPathAlgebraEquiv C k).symm (signlessPreprojectiveRelator k i)) =
          signlessPreprojectiveMk k _
            (signlessPreprojectiveRelator k
              ((symmetrifyMap G (Orientation.sourceSink C)).obj i)) :=
          congrArg (signlessPreprojectiveMk k _)
            (sourceSinkPathAlgebraEquiv_symm_signlessPreprojectiveRelator C k i)
        _ = 0 := signlessPreprojectiveMk_signlessPreprojectiveRelator k _

/-- The inverse quotient map sends a representative to the class of its image under the inverse
path-algebra comparison. -/
private theorem sourceSinkSignlessPreprojectiveHomInv_signlessPreprojectiveMk
    (x : pathAlgebra k (Symmetrify (OrientedQuiver G (Orientation.sourceSink C)))) :
    sourceSinkSignlessPreprojectiveHomInv C k (signlessPreprojectiveMk k _ x) =
      signlessPreprojectiveMk k _ ((sourceSinkPathAlgebraEquiv C k).symm x) :=
  signlessPreprojectiveLift_signlessPreprojectiveMk _ _ x

/-- Forgetting a source--sink orientation identifies the signless algebra of the doubled graph
with the signless algebra of the symmetrified oriented quiver. -/
private noncomputable def sourceSinkSignlessQuotientEquiv :
    signlessPreprojectiveAlgebra k (DoubledQuiver G) ≃ₐ[k]
      signlessPreprojectiveAlgebra k
        (Symmetrify (OrientedQuiver G (Orientation.sourceSink C))) :=
  AlgEquiv.ofAlgHom (sourceSinkSignlessPreprojectiveHom C k)
    (sourceSinkSignlessPreprojectiveHomInv C k)
    (Ideal.Quotient.algHom_ext k (AlgHom.ext fun x => by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        ← signlessPreprojectiveMk_apply,
        sourceSinkSignlessPreprojectiveHom_signlessPreprojectiveMk,
        sourceSinkSignlessPreprojectiveHomInv_signlessPreprojectiveMk,
        AlgEquiv.apply_symm_apply, AlgHom.id_apply]))
    (Ideal.Quotient.algHom_ext k (AlgHom.ext fun x => by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        ← signlessPreprojectiveMk_apply,
        sourceSinkSignlessPreprojectiveHom_signlessPreprojectiveMk,
        sourceSinkSignlessPreprojectiveHomInv_signlessPreprojectiveMk,
        AlgEquiv.symm_apply_apply, AlgHom.id_apply]))

/-- The signless-quotient comparison is induced by the path-algebra comparison. -/
@[simp]
private theorem sourceSinkSignlessQuotientEquiv_signlessPreprojectiveMk
    (x : pathAlgebra k (DoubledQuiver G)) :
    sourceSinkSignlessQuotientEquiv C k (signlessPreprojectiveMk k _ x) =
      signlessPreprojectiveMk k _ (sourceSinkPathAlgebraEquiv C k x) := by
  rw [sourceSinkSignlessQuotientEquiv, AlgEquiv.ofAlgHom_apply,
    sourceSinkSignlessPreprojectiveHom_signlessPreprojectiveMk]

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

end DoubledQuiver

end TauCeti
