/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Resolution
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.KoszulComplex
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Koszul.Resolution
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Koszul resolutions of zigzag simples from the preprojective Koszul complex

Let `G` be a finite simple graph and `Q` an orientation of `G`. The zigzag Koszul resolution
`TauCeti.zigzagKoszulResolution` of the graded simple modules `S_v` of the zigzag algebra `Z(G)`
exists as soon as the Koszul complexes `0 → e_w Π → ⨁_{j ∼ w} e_j Π` of the **signless**
preprojective algebra `Π` of the doubled graph, the quadratic dual of `Z(G)`, are exact at their
left ends. The Etingof--Eu Koszulity theorem is instead a statement about the **signed**
preprojective algebra `Π_k(Q)`: its left Koszul differentials `y ↦ (b* y)_b` are injective.

For a bipartite graph the two algebras agree: a colouring identifies the doubled graph with the
symmetrification of `Q`, and then rescales each arrow of `Q` by the sign of the colour of its head
(`TauCeti.symmetrifySignlessPreprojectiveAlgebraEquiv`). This identification fixes the vertex
idempotents and carries each doubled arrow to a unit multiple of the corresponding arrow, so it
transports left-end exactness from `Π_k(Q)` to the signless algebra. Hence, for a bipartite graph,
injectivity of the left Koszul differentials of `Π_k(Q)` gives linear resolutions of all the
zigzag simples. Every acyclic graph is bipartite, and every connected graph which is not a tree
already has such resolutions
(`TauCeti.exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_isAcyclic`), so for
a connected graph Koszulity of `Π_k(Q)` for one orientation implies Koszulity of `Z(G)`.

## Main results

* `TauCeti.forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_coloring`: for a
  two-coloured graph, left-end exactness of the preprojective Koszul complex of any orientation
  at `w` gives left-end exactness of the signless Koszul complex of the doubled graph at `w`.
* `TauCeti.exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_coloring`: for a
  two-coloured graph, if the left Koszul differentials of `Π_k(Q)` are injective, every graded
  zigzag simple has a linear resolution.
The same result for every connected graph is
`exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_preprojectiveKoszulLeft_injective`

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001), Section 3, for the quadratic dual of the zigzag algebra and its comparison with the
  preprojective algebra of a bipartite graph.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the vertex Koszul complexes of `Π_k(Q)`.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  J. Amer. Math. Soc. 9 (1996), Section 2, for Koszulity in terms of linear resolutions.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} {G : SimpleGraph V}

/-! ### Transporting left-end exactness -/

section LeftEnd

variable [CommRing k] [Finite V] [∀ v, Fintype (G.neighborSet v)]

/-- **Exactness of the signless Koszul complex at its left end, for a bipartite graph.** Let `C`
be a two-colouring of `G` and `o` any orientation of `G`. If the Koszul complex of the
preprojective algebra `Π_k(o)` is exact at its left end at `w`, then so is the Koszul complex of
the signless algebra `Π` of the doubled graph: for `y ∈ e_w Π`, `b* y = 0` for every arrow `b`
into `w` exactly when `y = 0`. -/
theorem forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_coloring
    (C : G.Coloring Bool) (o : Orientation G) (w : V)
    (hw : ∀ y : preprojectiveAlgebra k (OrientedQuiver G o),
      preprojectiveMk k _ (doubledVertexIdempotent k (OrientedQuiver.vertex G o w)) * y = y →
        (∀ (i : Symmetrify (OrientedQuiver G o))
          (b : i ⟶ Symmetrify.of.obj (OrientedQuiver.vertex G o w)),
          preprojectiveMk k _ (ofArrow (reverse b)) * y = 0) → y = 0)
    {y : signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hy : signlessPreprojectiveMk k _ (vertexIdempotent k (DoubledQuiver.vertex G w)) * y = y) :
    (∀ (i : DoubledQuiver G) (b : i ⟶ DoubledQuiver.vertex G w),
      signlessPreprojectiveMk k _ (ofArrow (reverse b)) * y = 0) ↔ y = 0 := by
  -- Use the finiteness instances of the orientation comparison; all such instances agree.
  obtain rfl : ‹∀ v, Fintype (G.neighborSet v)› = fun v => Fintype.ofFinite _ :=
    Subsingleton.elim _ _
  let _ : ∀ v, Fintype (G.neighborSet v) := fun v => Fintype.ofFinite _
  refine ⟨fun h => ?_, fun h i b => by rw [h, mul_zero]⟩
  -- The orientation comparison sends the class of `x` to that of its image under the
  -- prefunctor `φ` restoring the orientation.
  have hφ := (unsymmetrifyMap G o).obj_bijective_of_comp_eq_id (symmetrifyMap G o)
    (unsymmetrifyMap_comp_symmetrifyMap G o) (symmetrifyMap_comp_unsymmetrifyMap G o)
  have hF (x : pathAlgebra k (DoubledQuiver G)) :
      orientationSignlessPreprojectiveAlgebraEquiv o k (signlessPreprojectiveMk k _ x) =
        signlessPreprojectiveMk k _ (mapAlgHom k (unsymmetrifyMap G o) hφ x) := by
    rw [orientationSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
      orientationPathAlgebraEquiv_apply]
  suffices orientationSignlessPreprojectiveAlgebraEquiv o k y = 0 by
    rwa [map_eq_zero_iff _ (orientationSignlessPreprojectiveAlgebraEquiv o k).injective] at this
  have ht : (unsymmetrifyMap G o).obj (DoubledQuiver.vertex G w) =
      Symmetrify.of.obj (OrientedQuiver.vertex G o w) :=
    unsymmetrifyMap_obj G o w
  -- The colouring of `G` is a colouring of the oriented quiver.
  have hc : ∀ ⦃i j : OrientedQuiver G o⦄, (i ⟶ j) →
      C ((OrientedQuiver.vertexEquiv G o).symm i) ≠ C ((OrientedQuiver.vertexEquiv G o).symm j) :=
    fun _ _ a => C.valid a.1
  refine (forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_bipartite k hc _ hw
    ?_).1 ?_ <;> rw [← ht]
  · simpa only [map_mul, hF, mapAlgHom_vertexIdempotent] using
      congrArg (orientationSignlessPreprojectiveAlgebraEquiv o k) hy
  · -- Every arrow into the image of `w` is the image of an arrow into `w`, since `φ` is a covering.
    intro i' b'
    obtain ⟨⟨i, b⟩, hb⟩ :=
      ((unsymmetrifyMap_isCovering G o).costar_bijective _).2 (Quiver.Costar.mk b')
    obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.1 hb
    obtain rfl := eq_of_heq hb
    simpa only [map_mul, hF, mapAlgHom_ofArrow, Prefunctor.map_reverse, map_zero] using
      congrArg (orientationSignlessPreprojectiveAlgebraEquiv o k) (h i b)

end LeftEnd

/-! ### Linear resolutions of zigzag simples -/

section Resolution

variable [Field k] [Finite V]

/-- **The zigzag simples of a bipartite graph have linear resolutions when the preprojective
algebra is Koszul.** Let `C` be a two-colouring of a finite simple graph `G` and `o` an orientation
of `G` whose preprojective algebra has injective left Koszul differentials
`y ↦ (b* y)_b` at every vertex. Then every graded simple module `S_v` of the zigzag algebra,
concentrated in degree zero, has a linear graded projective resolution, namely
`TauCeti.zigzagKoszulResolution`. -/
theorem exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_coloring
    (C : G.Coloring Bool) (o : Orientation G)
    (ho : ∀ v : OrientedQuiver G o, Function.Injective (preprojectiveKoszulLeft k v)) (v : V) :
    ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w} (zigzagIntegerGrade k G)
      (zigzagGradedSimple k G v).grading, r.IsLinear := by
  classical
  have := Fintype.ofFinite V
  have hinj (w : V) (y : signlessPreprojectiveAlgebra k (DoubledQuiver G))
      (hy : signlessPreprojectiveMk k _ (vertexIdempotent k (DoubledQuiver.vertex G w)) * y = y)
      (h : ∀ (i : DoubledQuiver G) (b : i ⟶ DoubledQuiver.vertex G w),
        signlessPreprojectiveMk k _ (ofArrow (reverse b)) * y = 0) : y = 0 :=
    (forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_coloring k C o w
      ((preprojectiveKoszulLeft_injective_iff k _).1 (ho _)) hy).1 h
  exact ⟨zigzagKoszulResolution k G hinj v, isLinear_zigzagKoszulResolution k G hinj v⟩

/-- **Koszulity of the preprojective algebra gives Koszulity of the zigzag algebra.** Let `G` be a
finite preconnected simple graph and `o` an orientation of `G` whose preprojective algebra has
injective left Koszul differentials `y ↦ (b* y)_b` at every vertex. Then every graded simple
module `S_v` of the zigzag algebra, concentrated in degree zero, has a linear graded projective
resolution. An acyclic graph is two-coloured, and a graph which is not acyclic needs no hypothesis
on `o`. -/
theorem
exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_preprojectiveKoszulLeft_injective
    (hG : G.Preconnected) (o : Orientation G)
    (ho : ∀ v : OrientedQuiver G o, Function.Injective (preprojectiveKoszulLeft k v)) (v : V) :
    ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w} (zigzagIntegerGrade k G)
      (zigzagGradedSimple k G v).grading, r.IsLinear := by
  by_cases hc : G.IsAcyclic
  · exact exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_coloring k
      (G.recolorOfEquiv finTwoEquiv hc.isBipartite.some) o ho v
  · exact exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_isAcyclic k hG hc v

end Resolution

end TauCeti
