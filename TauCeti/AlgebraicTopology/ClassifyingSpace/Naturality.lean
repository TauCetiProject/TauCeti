/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CellMap
public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardResolution

/-!
# Naturality of the join-to-standard comparison

A group homomorphism induces an equivariant chain map on the ordered chains of Milnor's
countable join. In every degree it relabels each simplex, preserving its increasing-index
orientation. The cell maps are those of the continuous maps `MonoidHom.universalGSpaceMap`,
as witnessed by `MonoidHom.universalGSpaceMap_characteristicMap`.

`MonoidHom.universalGSpaceChainComplexToStandardComplex_naturality` proves that the explicit
comparison with Mathlib's standard complex commutes with these induced maps, as an equality
of chain maps of representations. Both routes send a simplex to the tuple of images of its
labels. Thus the forward map of `TauCeti.universalGSpaceStandardHomotopyEquiv` is natural
in the group. Restriction of the target action makes the square a square in `Rep k G`,
without any injectivity assumption on the homomorphism.

The join chain maps preserve augmentation by
`MulActionHom.toRepRes_comp_permutationAugmentation` and its reassociated form.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I and III.
-/

public section

noncomputable section

open CategoryTheory TauCeti

namespace MonoidHom

universe u

attribute [local instance] universalGSpaceVertexOrder

variable {k G H : Type u} [Group G] [Group H]

section Ring

variable [Ring k]

/-- Linear extension of relabelling simplices, equivariant along the group homomorphism. -/
abbrev universalGSpaceChainHom (φ : G →* H) (n : ℕ) :
    Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) ⟶
      Rep.res φ (Rep.ofMulAction k H ((indexedJoin fun _ : ℕ => H).RealizationCell n)) :=
  (φ.universalGSpaceCellMulActionHom n).toRepRes

/-- The chain map on Milnor join chains induced by a group homomorphism. -/
def universalGSpaceChainMap (φ : G →* H) :
    universalGSpaceChainComplex k G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj (universalGSpaceChainComplex k H) where
  f n := φ.universalGSpaceChainHom n
  comm' i j h := by
    subst i
    rw [Functor.mapHomologicalComplex_obj_d, universalGSpaceChainComplex_d,
      universalGSpaceChainComplex_d]
    apply Rep.ofMulAction_hom_ext
    intro c
    -- The restricted boundary carries the chain complex's implicit object arguments.
    -- Evaluate on permutation coordinates so the representation lemmas can match.
    change (universalGSpaceBoundary k H j).hom
        ((φ.universalGSpaceChainHom (j + 1)).hom (MonoidAlgebra.single c 1)) =
      (φ.universalGSpaceChainHom j).hom
        ((universalGSpaceBoundary k G j).hom (MonoidAlgebra.single c 1))
    simp only [Rep.res_obj_ρ, MulActionHom.toRepRes_hom_single,
      universalGSpaceBoundary_hom_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one, map_sum]
    exact Finset.sum_congr rfl fun i _ => congrArg
      (fun c => MonoidAlgebra.single c ((-1 : k) ^ (i : ℕ)))
      (universalGSpaceCellMap_face φ c i).symm

/-- The components of the induced join chain map are the linear extensions of the cell maps. -/
@[simp]
theorem universalGSpaceChainMap_f (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceChainMap (k := k)).f n = φ.universalGSpaceChainHom n :=
  (rfl)

/-- The identity homomorphism induces the identity map on join chains. -/
@[simp]
theorem universalGSpaceChainMap_id :
    (MonoidHom.id G).universalGSpaceChainMap (k := k) = 𝟙 (universalGSpaceChainComplex k G) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (congrArg (MulActionHom.toRepRes (k := k) (φ := MonoidHom.id G))
    (universalGSpaceCellMulActionHom_id (G := G) n)).trans MulActionHom.toRepRes_id

/-- Join chain maps respect composition, restricting the second map along the first
homomorphism. -/
@[simp]
theorem universalGSpaceChainMap_comp {K : Type u} [Group K] (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceChainMap (k := k) =
      φ.universalGSpaceChainMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map ψ.universalGSpaceChainMap := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (congrArg (MulActionHom.toRepRes (k := k) (φ := ψ.comp φ))
    (universalGSpaceCellMulActionHom_comp ψ φ n)).trans
    (MulActionHom.toRepRes_comp (ψ.universalGSpaceCellMulActionHom n)
      (φ.universalGSpaceCellMulActionHom n))

end Ring

variable [CommRing k]

/-- **The join-to-standard comparison is natural in the group.** Relabelling simplices before
forgetting their indices agrees with first forgetting indices and then relabelling the tuples.
This is an equality of chain maps in `Rep k G`, with target actions restricted along `φ`. -/
@[reassoc]
theorem universalGSpaceChainComplexToStandardComplex_naturality (φ : G →* H) :
    φ.universalGSpaceChainMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceChainComplexToStandardComplex k H) =
      universalGSpaceChainComplexToStandardComplex k G ≫ φ.standardComplexMap := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.ofMulAction_hom_ext
  intro c
  -- Remove the chain complexes' implicit object arguments before evaluating the maps;
  -- hom_comp and resMap_hom_apply cannot rewrite the transported morphisms directly.
  change ((universalGSpaceChainComplexToStandardComplex k H).f n).hom
      ((φ.universalGSpaceChainHom n).hom (MonoidAlgebra.single c 1)) =
    ((φ.standardComplexMap).f n).hom
      (((universalGSpaceChainComplexToStandardComplex k G).f n).hom
        (MonoidAlgebra.single c 1))
  simp only [universalGSpaceChainComplex_X, Rep.res_obj_ρ, MulActionHom.toRepRes_hom_single,
    universalGSpaceChainComplexToStandardComplex_f_hom_single,
    Functor.mapHomologicalComplex_obj_X, standardComplexMap_f]
  exact (congrArg (fun x => MonoidAlgebra.single x (1 : k))
    (universalGSpaceCellLabels_universalGSpaceCellMap φ c)).trans
    (MulActionHom.toRepRes_hom_single (k := k) (φ.standardComplexMulActionHom n)
      (universalGSpaceCellLabels c) 1).symm

end MonoidHom
