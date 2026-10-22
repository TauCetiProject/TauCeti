/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CellMap
public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardResolution
public import TauCeti.RepresentationTheory.Homological.StandardComplex

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
def universalGSpaceChainHom (φ : G →* H) (n : ℕ) :
    Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) ⟶
      Rep.res φ (Rep.ofMulAction k H ((indexedJoin fun _ : ℕ => H).RealizationCell n)) :=
  Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k φ.universalGSpaceCellMap
      isIntertwining' g := by
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        simp [Representation.ofMulAction_single] }

/-- An individual simplex maps to its relabelled simplex with the same coefficient. -/
@[simp]
theorem universalGSpaceChainHom_single (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (r : k) :
    (dsimp% only ((φ.universalGSpaceChainHom (k := k) n).hom
      (MonoidAlgebra.single c r))) =
        MonoidAlgebra.single (φ.universalGSpaceCellMap c) r := by
  simp [universalGSpaceChainHom]

/-- The chain map on Milnor join chains induced by a group homomorphism. -/
def universalGSpaceChainMap (φ : G →* H) :
    universalGSpaceChainComplex k G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj (universalGSpaceChainComplex k H) where
  f n := φ.universalGSpaceChainHom n
  comm' i j h := by
    subst i
    rw [Functor.mapHomologicalComplex_obj_d, universalGSpaceChainComplex_d,
      universalGSpaceChainComplex_d]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    -- Composition and restriction act by composition of the underlying linear maps.
    change (universalGSpaceBoundary k H j).hom
        ((φ.universalGSpaceChainHom (j + 1)).hom (MonoidAlgebra.single c 1)) =
      (φ.universalGSpaceChainHom j).hom
        ((universalGSpaceBoundary k G j).hom (MonoidAlgebra.single c 1))
    simp

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
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  -- Restriction along the identity does not change the underlying permutation module.
  change ((MonoidHom.id G).universalGSpaceChainHom n).hom (MonoidAlgebra.single c 1) =
    MonoidAlgebra.single c 1
  simp

/-- Join chain maps respect composition, restricting the second map along the first
homomorphism. -/
@[simp]
theorem universalGSpaceChainMap_comp {K : Type u} [Group K] (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceChainMap (k := k) =
      φ.universalGSpaceChainMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map ψ.universalGSpaceChainMap := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  -- Iterated restriction is restriction along the composite on underlying modules.
  change ((ψ.comp φ).universalGSpaceChainHom n).hom (MonoidAlgebra.single c 1) =
    (ψ.universalGSpaceChainHom n).hom
      ((φ.universalGSpaceChainHom n).hom (MonoidAlgebra.single c 1))
  simp

/-- Relabelling simplices preserves the degree-zero augmentation. -/
@[reassoc (attr := simp)]
theorem universalGSpaceChainHom_comp_augmentation (φ : G →* H) :
    φ.universalGSpaceChainHom (k := k) 0 ≫
        (Rep.resFunctor φ).map (permutationAugmentation k H _) =
      permutationAugmentation k G _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  -- Restriction does not alter the coefficient-sum augmentation.
  change (permutationAugmentation k H _).hom
      ((φ.universalGSpaceChainHom 0).hom (MonoidAlgebra.single c 1)) =
    (permutationAugmentation k G _).hom (MonoidAlgebra.single c 1)
  rw [universalGSpaceChainHom_single, permutationAugmentation_apply,
    permutationAugmentation_apply]
  simp

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
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  -- xIso is the identity in permutation coordinates; the source complex is already
  -- presented on simplices. Remove these transports to evaluate both composites.
  change ((universalGSpaceChainComplexToStandardComplex k H).f n).hom
      ((φ.universalGSpaceChainHom n).hom (MonoidAlgebra.single c 1)) =
    ((φ.standardComplexMap).f n).hom
      (((universalGSpaceChainComplexToStandardComplex k G).f n).hom
        (MonoidAlgebra.single c 1))
  simp only [universalGSpaceChainComplex_X, Rep.res_obj_ρ, universalGSpaceChainHom_single,
    universalGSpaceChainComplexToStandardComplex_f_hom_single, universalGSpaceCellLabels_map,
    Functor.mapHomologicalComplex_obj_X, standardComplexMap_f]
  exact (standardComplexHom_single (k := k) φ (universalGSpaceCellLabels c) (1 : k)).symm

end MonoidHom
