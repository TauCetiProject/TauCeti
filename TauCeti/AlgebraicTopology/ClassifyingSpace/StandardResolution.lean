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
* `TauCeti.not_isIso_universalGSpaceChainComplexToStandardComplex`: for a nontrivial coefficient
  ring, the join-to-standard comparison is not an isomorphism of chain complexes in `Rep k G`.

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

/-- The underlying linear map of `universalGSpaceToStandardHom` reads permutation coefficients and
applies `universalGSpaceToStandard`. -/
@[simp]
theorem universalGSpaceToStandardHom_hom_toLinearMap (n : ℕ) :
    (universalGSpaceToStandardHom k G n).hom.toLinearMap =
      universalGSpaceToStandard k n ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap :=
  (rfl)

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

/-- Forgetting the group action identifies `universalGSpaceChainComplexToStandardComplex` with
the module-level comparison `universalGSpaceToStandardComplex`. -/
theorem forget₂_mapHomologicalComplex_map_universalGSpaceChainComplexToStandardComplex :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        (universalGSpaceChainComplexToStandardComplex k G) =
      (universalGSpaceChainComplexForget₂Iso k G).hom ≫
        universalGSpaceToStandardComplex (G := G) k := by
  ext n : 1
  simp only [Functor.mapHomologicalComplex_map_f, universalGSpaceChainComplexToStandardComplex_f,
    HomologicalComplex.comp_f, universalGSpaceChainComplexForget₂Iso_hom_f,
    universalGSpaceToStandardComplex_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X,
    Rep.standardComplex.forget₂ToModuleCat]
  rw [Functor.map_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← Category.assoc]
  refine congrArg (· ≫ (forget₂ (Rep k G) (ModuleCat k)).map (Rep.standardComplex.xIso k G n).inv)
    ?_
  rw [Rep.forget₂_moduleCat_map, universalGSpaceToStandardHom_hom_toLinearMap,
    LinearEquiv.toModuleIso_hom, ← ModuleCat.ofHom_comp]

/-- For any group `G` and nontrivial coefficient ring `k`, the module-level chain map obtained by
forgetting the `G`-action on `universalGSpaceChainComplexToStandardComplex` is **not** an
isomorphism of chain complexes. -/
theorem not_isIso_forget₂_mapHomologicalComplex_map_universalGSpaceChainComplexToStandardComplex
    [Nontrivial k] :
    ¬ IsIso (((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
      (universalGSpaceChainComplexToStandardComplex k G)) := fun h ↦
  not_isIso_universalGSpaceToStandardComplex (G := G) k <|
    (isIso_comp_left_iff (universalGSpaceChainComplexForget₂Iso k G).hom
      (universalGSpaceToStandardComplex (G := G) k)).mp
      (forget₂_mapHomologicalComplex_map_universalGSpaceChainComplexToStandardComplex k G ▸ h)

/-- For a nontrivial coefficient ring `k`, the degree-zero component of
`universalGSpaceChainComplexToStandardComplex` is not injective on underlying elements: distinct
index copies `(0, g)` and `(1, g)` of a group element `g` have the same standard generator. -/
theorem not_injective_universalGSpaceChainComplexToStandardComplex_f_zero [Nontrivial k] :
    ¬ Function.Injective ((universalGSpaceChainComplexToStandardComplex k G).f 0).hom := by
  intro hinj
  have : Mono (universalGSpaceToStandardHom k G 0 ≫ (Rep.standardComplex.xIso k G 0).inv) :=
    universalGSpaceChainComplexToStandardComplex_f k G 0 ▸ (Rep.mono_iff_injective _).2 hinj
  have hhom : Function.Injective ⇑(universalGSpaceToStandardHom k G 0).hom.toLinearMap :=
    (Rep.mono_iff_injective (universalGSpaceToStandardHom k G 0)).1
      (mono_of_mono (universalGSpaceToStandardHom k G 0) (Rep.standardComplex.xIso k G 0).inv)
  rw [universalGSpaceToStandardHom_hom_toLinearMap] at hhom
  refine not_injective_universalGSpaceToStandard_zero (G := G) k fun x y hxy ↦ ?_
  apply (MonoidAlgebra.coeffLinearEquiv k).symm.injective
  apply hhom
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hxy

/-- For any group `G` and nontrivial coefficient ring `k`, the join-to-standard chain map
`universalGSpaceChainComplexToStandardComplex` is **not** an isomorphism of chain complexes in
`Rep k G`. -/
theorem not_isIso_universalGSpaceChainComplexToStandardComplex [Nontrivial k] :
    ¬ IsIso (universalGSpaceChainComplexToStandardComplex k G) := fun _ ↦
  not_isIso_forget₂_mapHomologicalComplex_map_universalGSpaceChainComplexToStandardComplex k G
    (Functor.map_isIso _ _)

end TauCeti
