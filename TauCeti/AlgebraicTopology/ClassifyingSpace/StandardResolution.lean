/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Resolution
public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardComplex
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.RepresentationTheory.Homological.Resolution

/-!
# Milnor's join resolution is homotopy equivalent to the standard resolution

The ordered chains of Milnor's countable join form a projective resolution
`TauCeti.universalGSpaceResolution k G` of the trivial representation, and Mathlib's standard
complex forms another, `Rep.standardResolution k G`. This file compares them by an explicit map.

Sending an oriented simplex `{(i₀, g₀), …, (iₙ, gₙ)}` of the countable join, with
`i₀ < ⋯ < iₙ`, to the basis element `(g₀, …, gₙ)` of the standard complex is a chain map of
complexes of representations of `G` (`TauCeti.universalGSpaceChainComplexToStandardComplex`).
Forgetting the action, it is the module-level comparison
`TauCeti.universalGSpaceToStandardComplex`, degree by degree. It commutes with the two
augmentations, which both sum coefficients
(`TauCeti.universalGSpaceChainComplexToStandardComplex_comp_εToSingle₀`), so it lifts the identity
of the trivial representation. A lift of the identity between projective resolutions is a homotopy
equivalence (`TauCeti.universalGSpaceStandardHomotopyEquiv`), and it is homotopic to the
comparison `ProjectiveResolution.homotopyEquiv` that Mathlib constructs abstractly from the
projectivity of the terms (`TauCeti.universalGSpaceChainComplexToStandardComplexHomotopy`).

The comparison is a homotopy equivalence and not an isomorphism: for the trivial group and a
nonzero coefficient ring, the join has countably many vertices, while the standard complex has a
single basis element in degree `0`.

## Main definitions

* `TauCeti.universalGSpaceChainComplexToStandardComplex`: the join-to-standard chain map of
  complexes of representations.
* `TauCeti.universalGSpaceStandardHomotopyEquiv`: the homotopy equivalence of projective
  resolutions whose forward map is the join-to-standard chain map.
* `TauCeti.universalGSpaceChainComplexToStandardComplexHomotopy`: the join-to-standard chain map
  is homotopic to Mathlib's abstract comparison of the two resolutions.

## Main results

* `TauCeti.universalGSpaceChainComplexToStandardComplex_comp_εToSingle₀`: the chain map commutes
  with the augmentations.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter I, Section 7.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

attribute [local instance] universalGSpaceVertexOrder

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- The explicit comparison in degree `n` as a morphism of permutation representations: it sends
an `n`-simplex of the countable join to the tuple of its labels, enumerated by increasing
index. -/
def universalGSpaceToStandardHom (n : ℕ) :
    Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) ⟶
      Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Rep.ofHom
    { toLinearMap := universalGSpaceToStandard k n ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
      isIntertwining' g := LinearMap.ext fun x ↦ by
        simpa [Representation.ofMulAction_def] using
          universalGSpaceToStandard_smul k n g (MonoidAlgebra.coeffLinearEquiv k x) }

/-- The comparison sends a simplex to the tuple of its labels. -/
@[simp]
theorem universalGSpaceToStandardHom_hom_single {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (a : k) :
    (dsimp% only ((universalGSpaceToStandardHom k G n).hom (MonoidAlgebra.single c a))) =
      MonoidAlgebra.single (universalGSpaceCellLabels c) a := by
  simp [universalGSpaceToStandardHom]

/-- **The join-to-standard chain map of complexes of representations.** It sends an oriented
simplex `{(i₀, g₀), …, (iₙ, gₙ)}` of the countable join, with `i₀ < ⋯ < iₙ`, to the basis
element `(g₀, …, gₙ)` of Mathlib's standard complex. -/
def universalGSpaceChainComplexToStandardComplex :
    universalGSpaceChainComplex k G ⟶ Rep.standardComplex k G where
  f n := universalGSpaceToStandardHom k G n ≫ (Rep.standardComplex.xIso k G n).inv
  comm' i j (h : j + 1 = i) := by
    subst i
    rw [universalGSpaceChainComplex_d]
    -- Expand the chain-map components in the commutativity goal. Composition in `Rep`
    -- is definitionally associative; the displayed source objects are the permutation
    -- representations underlying `universalGSpaceChainComplex_X`.
    change (universalGSpaceToStandardHom k G (j + 1) ≫
        (Rep.standardComplex.xIso k G (j + 1)).inv) ≫
          (Rep.standardComplex k G).d (j + 1) j =
      universalGSpaceBoundary k G j ≫
        universalGSpaceToStandardHom k G j ≫ (Rep.standardComplex.xIso k G j).inv
    refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ ?_
    -- The standard-complex coordinate isomorphisms are definitionally identities.
    dsimp only [Rep.standardComplex.xIso]
    simp only [Rep.hom_comp_toLinearMap]
    rw [Rep.standardComplex.d_eq]
    -- After morphism extensionality, the comparison homomorphism is its defining linear
    -- map: coefficient conversion from `MonoidAlgebra` followed by the simplex comparison.
    -- The identity coordinate isomorphisms contribute no further map on either side.
    change (Rep.standardComplex.d k G (j + 1))
        ((universalGSpaceToStandard k (j + 1)) (MonoidAlgebra.coeffLinearEquiv k x)) =
      (universalGSpaceToStandard k j)
        (MonoidAlgebra.coeffLinearEquiv k ((universalGSpaceBoundary k G j).hom x))
    have hb := congr(ModuleCat.Hom.hom $(universalGSpaceBoundary_comp_coeff k G j) x)
    -- Evaluating the transported `ModuleCat` morphism equality at `x` unfolds composition
    -- of the underlying linear maps. The forgetful image of the representation boundary
    -- acts by `(universalGSpaceBoundary k G j).hom`, giving the coefficient identity below.
    change MonoidAlgebra.coeffLinearEquiv k ((universalGSpaceBoundary k G j).hom x) =
      OrderedSimplicialChain.boundary k j (MonoidAlgebra.coeffLinearEquiv k x) at hb
    rw [hb]
    exact congr($(universalGSpaceToStandard_boundary (G := G) k j)
      (MonoidAlgebra.coeffLinearEquiv k x)).symm

/-- In degree `n` the chain map is the comparison of permutation representations. -/
theorem universalGSpaceChainComplexToStandardComplex_f (n : ℕ) :
    (universalGSpaceChainComplexToStandardComplex k G).f n =
      universalGSpaceToStandardHom k G n ≫ (Rep.standardComplex.xIso k G n).inv :=
  (rfl)

/-- In degree `n` the chain map sends a simplex to the tuple of its labels. -/
@[simp]
theorem universalGSpaceChainComplexToStandardComplex_f_hom_single {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (a : k) :
    (dsimp% only [universalGSpaceChainComplex_X]
      (((universalGSpaceChainComplexToStandardComplex k G).f n).hom (MonoidAlgebra.single c a))) =
      MonoidAlgebra.single (universalGSpaceCellLabels c) a :=
  universalGSpaceToStandardHom_hom_single k G c a

/-- In degree `0` the comparison preserves the augmentations: both sum the coefficients. -/
@[reassoc (attr := simp)]
theorem universalGSpaceToStandardHom_comp_ε :
    universalGSpaceToStandardHom k G 0 ≫ Rep.standardComplex.ε k G =
      permutationAugmentation k G _ := by
  apply (forget₂ (Rep k G) (ModuleCat k)).map_injective
  rw [Functor.map_comp, forget₂_map_permutationAugmentation]
  ext x
  simpa [universalGSpaceToStandardHom] using
    universalGSpaceToStandard_augmentation k (MonoidAlgebra.coeffLinearEquiv k x)

/-- **The join-to-standard chain map preserves the augmentations**: both sum the coefficients of
a `0`-chain. -/
@[reassoc (attr := simp)]
theorem universalGSpaceChainComplexToStandardComplex_comp_εToSingle₀ :
    universalGSpaceChainComplexToStandardComplex k G ≫ Rep.standardComplex.εToSingle₀ k G =
      universalGSpaceAugmentation k G := by
  refine HomologicalComplex.to_single_hom_ext ?_
  simp [universalGSpaceChainComplexToStandardComplex_f]

/-- The join-to-standard chain map lifts the identity of the trivial representation along the
augmentations of the two projective resolutions. -/
theorem universalGSpaceChainComplexToStandardComplex_comp_standardResolution_π :
    universalGSpaceChainComplexToStandardComplex k G ≫ (Rep.standardResolution k G).π =
      (universalGSpaceResolution k G).π :=
  universalGSpaceChainComplexToStandardComplex_comp_εToSingle₀ k G

/-- **Milnor's join resolution is homotopy equivalent to the standard resolution**, by a homotopy
equivalence whose forward map is the explicit join-to-standard chain map. Its homotopy inverse is
the lift of the identity of the trivial representation from the standard resolution to the join
resolution. -/
def universalGSpaceStandardHomotopyEquiv :
    HomotopyEquiv (universalGSpaceChainComplex k G) (Rep.standardComplex k G) :=
  ProjectiveResolution.homotopyEquivOfComm (universalGSpaceResolution k G)
    (Rep.standardResolution k G) (universalGSpaceChainComplexToStandardComplex k G)
    (universalGSpaceChainComplexToStandardComplex_comp_standardResolution_π k G)

/-- The forward map of the homotopy equivalence is the join-to-standard chain map. -/
@[simp]
theorem universalGSpaceStandardHomotopyEquiv_hom :
    (universalGSpaceStandardHomotopyEquiv k G).hom =
      universalGSpaceChainComplexToStandardComplex k G :=
  ProjectiveResolution.homotopyEquivOfComm_hom _ _ _ _

/-- The homotopy inverse is the lift of the identity of the trivial representation from the
standard resolution to the join resolution. -/
@[simp]
theorem universalGSpaceStandardHomotopyEquiv_inv :
    (universalGSpaceStandardHomotopyEquiv k G).inv =
      ProjectiveResolution.lift (𝟙 _) (Rep.standardResolution k G)
        (universalGSpaceResolution k G) :=
  ProjectiveResolution.homotopyEquivOfComm_inv _ _ _ _

/-- **The join-to-standard chain map is homotopic to Mathlib's comparison** of the two projective
resolutions, the lift of the identity of the trivial representation constructed by
`ProjectiveResolution.homotopyEquiv`. -/
def universalGSpaceChainComplexToStandardComplexHomotopy :
    Homotopy (universalGSpaceChainComplexToStandardComplex k G)
      (ProjectiveResolution.homotopyEquiv (universalGSpaceResolution k G)
        (Rep.standardResolution k G)).hom :=
  ProjectiveResolution.homotopyOfComm (universalGSpaceResolution k G)
    (Rep.standardResolution k G) (universalGSpaceChainComplexToStandardComplex k G)
    (universalGSpaceChainComplexToStandardComplex_comp_standardResolution_π k G)

end TauCeti
