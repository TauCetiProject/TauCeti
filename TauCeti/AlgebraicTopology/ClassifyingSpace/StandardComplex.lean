/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex
public import Mathlib.RepresentationTheory.Homological.Resolution

/-!
# From Milnor's join chains to the standard complex

An oriented simplex of Milnor's countable join has vertices
`(i₀, g₀), …, (iₙ, gₙ)` with strictly increasing indices. Forgetting the indices gives the
basis element `(g₀, …, gₙ)` of Mathlib's `Rep.standardComplex`. Deleting a vertex commutes
with forgetting its index, so this prescription defines a chain map.

`TauCeti.universalGSpaceToStandardComplex` has as source the existing ordered simplicial chain
complex of the countable join and as target the underlying module complex of Mathlib's standard
complex. Its degreewise maps are equivariant for translation and preserve the augmentations.
This is an explicit comparison of complexes of modules; its equivariant form, a homotopy
equivalence of projective resolutions, is in
`TauCeti.AlgebraicTopology.ClassifyingSpace.StandardResolution`. For a nonzero coefficient ring
it is not an isomorphism: even for the trivial group, the join has countably many vertices and the
standard complex has just one.

The source orientation agrees with the CW structure on `universalGSpace`: its characteristic
maps enumerate the vertices by increasing index. The target is Mathlib's standard complex from
`Mathlib.RepresentationTheory.Homological.Resolution`, by Amelia Livingston, not a new version
of the bar resolution.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I and III.
-/

public section

noncomputable section

open CategoryTheory Finsupp AbstractSimplicialComplex

namespace TauCeti

universe u v

variable {G : Type u}

attribute [local instance] universalGSpaceVertexOrder

/-- The labels of an oriented simplex of the countable join, enumerated by increasing index. -/
def universalGSpaceCellLabels {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) : Fin (n + 1) → G :=
  fun j => (c.vertexEmbedding j).2

/-- The entry at a given position is the label of the vertex at that position. -/
@[simp]
theorem universalGSpaceCellLabels_apply {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (j : Fin (n + 1)) :
    universalGSpaceCellLabels c j = (c.vertexEmbedding j).2 :=
  (rfl)

/-- Deleting a vertex deletes the corresponding entry of the label tuple. -/
@[simp]
theorem universalGSpaceCellLabels_face {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell (n + 1)) (j : Fin (n + 2)) :
    universalGSpaceCellLabels (c.face j) = universalGSpaceCellLabels c ∘ j.succAbove := by
  funext i
  exact congrArg Sigma.snd (congrFun (c.vertexEmbedding_face j) i)

/-- Translation of a simplex translates its entire label tuple diagonally. -/
@[simp]
theorem universalGSpaceCellLabels_smul [Group G] {n : ℕ} (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    universalGSpaceCellLabels (g • c) = g • universalGSpaceCellLabels c := by
  funext j
  exact congrArg Sigma.snd (vertexEmbedding_smul_universalGSpace g c j)

section Semiring

variable (k : Type v) [Semiring k]

/-- The degreewise comparison from join chains to standard chains: forget the indices of
vertices, retaining their increasing-index order and the coefficient of each simplex. -/
def universalGSpaceToStandard (n : ℕ) :
    OrderedSimplicialChain (indexedJoin fun _ : ℕ => G) k n →ₗ[k]
      MonoidAlgebra k (Fin (n + 1) → G) :=
  (MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.lmapDomain k k universalGSpaceCellLabels

/-- The comparison sends an individual simplex to its ordered tuple of labels. -/
@[simp]
theorem universalGSpaceToStandard_single {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (a : k) :
    universalGSpaceToStandard k n (single c a) =
      MonoidAlgebra.single (universalGSpaceCellLabels c) a := by
  simp [universalGSpaceToStandard]

/-- The comparison is equivariant: translating every simplex before forgetting its indices is
the diagonal translation of the resulting standard chain. The source action is the linear
extension of the action on the simplices. -/
theorem universalGSpaceToStandard_smul [Group G] (n : ℕ) (g : G)
    (x : OrderedSimplicialChain (indexedJoin fun _ : ℕ => G) k n) :
    universalGSpaceToStandard k n (Finsupp.lmapDomain k k (g • ·) x) =
      Representation.ofMulAction k G (Fin (n + 1) → G) g
        (universalGSpaceToStandard k n x) := by
  have h : (universalGSpaceToStandard k n).comp (Finsupp.lmapDomain k k (g • ·)) =
      (Representation.ofMulAction k G (Fin (n + 1) → G) g).comp
        (universalGSpaceToStandard k n) := by
    refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
    simp [Representation.ofMulAction_single]
  exact DFunLike.congr_fun h x

end Semiring

variable (k : Type u) [CommRing k]

/-- The explicit comparison commutes with the alternating boundaries. -/
theorem universalGSpaceToStandard_boundary (n : ℕ) :
    (universalGSpaceToStandard (G := G) k n).comp
        (OrderedSimplicialChain.boundary k n) =
      (Rep.standardComplex.d k G (n + 1)).comp (universalGSpaceToStandard k (n + 1)) := by
  classical
  refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
  simp [OrderedSimplicialChain.boundary_single, Rep.standardComplex.d_of]

/-- **The explicit join-to-standard chain map.** Its source is the ordered simplicial chain
complex of the countable join, and its target is the module complex underlying Mathlib's
standard complex. -/
def universalGSpaceToStandardComplex [Monoid G] :
    orderedSimplicialChainComplex (indexedJoin fun _ : ℕ => G) k ⟶
      Rep.standardComplex.forget₂ToModuleCat k G where
  f n := eqToHom (orderedSimplicialChainComplex_X
      (K := indexedJoin fun _ : ℕ => G) k n) ≫
    ModuleCat.ofHom (universalGSpaceToStandard k n) ≫
      (forget₂ (Rep k G) (ModuleCat k)).map (Rep.standardComplex.xIso k G n).inv
  comm' i j (h : j + 1 = i) := by
    subst i
    rw [orderedSimplicialChainComplex_d]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    apply (cancel_epi (eqToHom (orderedSimplicialChainComplex_X
      (K := indexedJoin fun _ : ℕ => G) k (j + 1)))).2
    apply ModuleCat.hom_ext
    -- The forgotten complex uses the representation differential, and xIso is Iso.refl.
    -- Expose these to apply d_eq, which is stated before forgetting to modules and does
    -- not include the xIso transports.
    dsimp [Rep.standardComplex.forget₂ToModuleCat, Rep.standardComplex.xIso]
    rw [Rep.standardComplex.d_eq]
    exact (universalGSpaceToStandard_boundary (G := G) k j).symm

/-- In each degree the chain map is the explicit comparison on simplex coefficients. -/
@[simp]
theorem universalGSpaceToStandardComplex_f [Monoid G] (n : ℕ) :
    (universalGSpaceToStandardComplex (G := G) k).f n =
      eqToHom (orderedSimplicialChainComplex_X
        (K := indexedJoin fun _ : ℕ => G) k n) ≫
      ModuleCat.ofHom (universalGSpaceToStandard k n) ≫
        (forget₂ (Rep k G) (ModuleCat k)).map (Rep.standardComplex.xIso k G n).inv :=
  (rfl)

/-- The comparison preserves the augmentations, each of which sums the coefficients of the
vertices. The target augmentation is `Rep.standardComplex.ε`. -/
theorem universalGSpaceToStandard_augmentation [Monoid G]
    (x : OrderedSimplicialChain (indexedJoin fun _ : ℕ => G) k 0) :
    (Rep.standardComplex.ε k G).hom (universalGSpaceToStandard k 0 x) =
      Finsupp.linearCombination k (fun _ => (1 : k)) x := by
  have h : (Rep.standardComplex.ε k G).hom.toLinearMap.comp
      (universalGSpaceToStandard k 0) = Finsupp.linearCombination k (fun _ => (1 : k)) := by
    refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
    simp [Rep.standardComplex.ε]
  exact DFunLike.congr_fun h x

end TauCeti
