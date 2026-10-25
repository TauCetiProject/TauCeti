/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Comparison.Basic

/-!
# From simplicial to cubical chains with local coefficients

The comparison `TauCeti.singularToCubical` of the simplicial singular chains with the normalized
cubical chains is natural, and the model `Δⁿ` is contractible, so it extends to chains with local
coefficients exactly as the comparison in the other direction does
(`TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap`).  For a singular `n`-simplex `σ` of
`X` and a coefficient `a` in the fibre at its initial vertex, the image is the twisted cubical
pushforward (`TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.pushforward`) along
`σ`, regarded as a map from the model, of the image `TauCeti.singularToCubicalGen n` of the
identity simplex of the model, with the coefficient `a` at the initial vertex of the model.

The decisive property is the compatibility with pushforwards from simply connected spaces
(`TauCeti.LocalCoefficientSystem.twistedSingularToCubical_twistedPushforward`): the comparison
carries the simplicial pushforward of a chain of a simply connected space `Z` to the cubical
pushforward of its image.  Every simplex with a coefficient is such a pushforward from a standard
simplex, so identities between natural maps reduce, generator by generator, to the model, where
they are the untwisted ones.  Here this gives the chain map property.  The analogous
compatibility of the comparison in the other direction is
`TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalToSingular_pushforward`.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedSingularToCubical L n`: the comparison on the
  `n`-chains with coefficients in `L`.
* `TauCeti.LocalCoefficientSystem.twistedSingularToCubicalMap L`: the comparison chain map from
  `TauCeti.LocalCoefficientSystem.twistedChainComplex L` to the normalized cubical chain
  complex with coefficients in `L`.

## Main results

* `TauCeti.LocalCoefficientSystem.twistedSingularToCubical_ιTwistedChainComplex_const`: on a point
  simplex the comparison is the class of the point cube.
* `TauCeti.LocalCoefficientSystem.twistedSingularToCubical_twistedPushforward`: compatibility
  with pushforwards from simply connected spaces.
* `TauCeti.LocalCoefficientSystem.twistedSingularToCubicalMap_naturality`,
  `TauCeti.LocalCoefficientSystem.twistedSingularToCubicalMap_coefficientMap_naturality`:
  naturality in the space and in the local system.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters VII and XIV.
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory

open scoped Simplicial

universe u v

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, v} R X)

/-- The comparison from the summand of a simplex `σ`: the pushforward along `σ`, from the initial
vertex of the model, of the image of the identity simplex. -/
def twistedSingularToCubicalSummand {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    L.obj (initialVertex σ) →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  NormalizedTwistedCubicalChain.pushforward (Z := simplexModel.{v} n) L (simplexToHom σ).hom
    (SimplexCategory.toTopInitialVertex ⦋n⦌) n (singularToCubicalGen (ULift.{v} ℤ) n)

/-- The comparison on the summand of a simplex is the cubical pushforward of the model generator
along the simplex.  This is the defining equation of `twistedSingularToCubicalSummand`. -/
theorem twistedSingularToCubicalSummand_apply {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (a : L.obj (initialVertex σ)) :
    twistedSingularToCubicalSummand L σ a =
      NormalizedTwistedCubicalChain.pushforward (Z := simplexModel.{v} n) L (simplexToHom σ).hom
        (SimplexCategory.toTopInitialVertex ⦋n⦌) n (singularToCubicalGen (ULift.{v} ℤ) n) a :=
  (rfl)

/-- The comparison from the simplicial chains with coefficients in `L` to the normalized cubical
chains with coefficients in `L`: a simplex `σ` with a coefficient goes to the pushforward along
`σ` of the image of the identity simplex of the model. -/
def twistedSingularToCubical (n : ℕ) :
    (twistedChainComplex L).X n ⟶ ModuleCat.of R (L.NormalizedTwistedCubicalChain n) :=
  twistedChainComplexDesc L fun σ ↦ ModuleCat.ofHom (twistedSingularToCubicalSummand L σ)

/-- The comparison on the summand of a simplex. -/
@[reassoc (attr := simp)]
theorem ιTwistedChainComplex_comp_twistedSingularToCubical {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChainComplex L n σ ≫ twistedSingularToCubical L n =
      ModuleCat.ofHom (twistedSingularToCubicalSummand L σ) :=
  ιTwistedChainComplex_twistedChainComplexDesc L _ σ

/-- The comparison on a simplex with a coefficient. -/
@[simp]
theorem twistedSingularToCubical_ιTwistedChainComplex {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : L.obj (initialVertex σ)) :
    (twistedSingularToCubical L n).hom (ιTwistedChainComplex L n σ a) =
      twistedSingularToCubicalSummand L σ a :=
  ConcreteCategory.congr_hom (ιTwistedChainComplex_comp_twistedSingularToCubical L σ) a

/-- On a point simplex, the comparison to cubical chains is the class of the point cube. -/
theorem twistedSingularToCubical_ιTwistedChainComplex_const (x : X)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    (twistedSingularToCubical L 0).hom
        (ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) a) =
      NormalizedTwistedCubicalChain.ofCube L (ContinuousMap.const _ x) a := by
  -- The point simplex is named so that the fibres of its summand and of the pushforward agree.
  set σ : (TopCat.toSSet.obj X) _⦋0⦌ := ULift.up (TopCat.ofHom (ContinuousMap.const _ x))
  -- Unfold the summand to the pushforward of the point cube of the model.
  refine (twistedSingularToCubical_ιTwistedChainComplex L σ a).trans
    ((twistedSingularToCubicalSummand_apply L σ a).trans
      ((congrArg (fun y ↦ NormalizedTwistedCubicalChain.pushforward
        (Z := simplexModel.{v} 0) L (simplexToHom σ).hom
        (SimplexCategory.toTopInitialVertex ⦋0⦌) 0 y a)
        (singularToCubicalGen_zero (k := ULift.{v} ℤ))).trans
        ((NormalizedTwistedCubicalChain.pushforward_ofCube (L := L)
          (f := (simplexToHom σ).hom) (z₀ := SimplexCategory.toTopInitialVertex ⦋0⦌) _ a).trans
          ?_)))
  -- The pushed cube is the point cube at `x`, and the transport of `a` is trivial.
  exact NormalizedTwistedCubicalChain.ofCube_congr (L := L) (ContinuousMap.ext fun _ ↦ rfl)
    (map_pathClass_heq (L := L) (simplexToHom σ).hom
      (z := SimplexCategory.toTopInitialVertex ⦋0⦌) (Subsingleton.elim _ _) a)

/-- **Compatibility with pushforwards.** The comparison carries the simplicial pushforward of a
chain of a simply connected space `Z` to the cubical pushforward of the image of the chain. -/
theorem twistedSingularToCubical_twistedPushforward {Z : TopCat.{v}} [SimplyConnectedSpace Z]
    (f : Z ⟶ X) (z₀ : Z) {n : ℕ} (y : ((singularChains (ULift.{v} ℤ)).obj Z).X n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    twistedSingularToCubical L n (twistedPushforward L f z₀ n y a) =
      NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n
        (((singularToCubical (ULift.{v} ℤ)).app Z).f n y) a := by
  have h := singularChains_linearMap_ext
    (L := (((twistedSingularToCubical L n).hom.toAddMonoidHom.toIntLinearMap).restrictScalars
      (ULift.{v} ℤ)) ∘ₗ ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      twistedPushforward L f z₀ n)
    (L' := ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n ∘ₗ
      (((singularToCubical (ULift.{v} ℤ)).app Z).f n).hom) fun σ ↦ ?_
  · exact congrArg (fun φ ↦ φ y) h
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.applyₗ'_apply_apply, LinearMap.toAddMonoidHom_coe]
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change (twistedSingularToCubical L n).hom (twistedPushforward L f z₀ n (simplexChain σ 1) a) =
    NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n
      (((singularToCubical (ULift.{v} ℤ)).app Z).f n (simplexChain σ 1)) a
  rw [singularToCubical_app_f_simplexChain, twistedPushforward_simplexChain_one]
  refine (ConcreteCategory.congr_hom
    (ιTwistedChainComplex_comp_twistedSingularToCubical (L := L) _) _).trans ?_
  exact (NormalizedTwistedCubicalChain.pushforward_map (L := L) (f := f.hom) (z₀ := z₀)
    (Z' := simplexModel.{v} n) (simplexToHom σ).hom
    (SimplexCategory.toTopInitialVertex ⦋n⦌) _ a).symm

/-- The comparison carries the simplicial pushforward along a simplex to the cubical pushforward
of the image under the comparison without coefficients. -/
lemma twistedSingularToCubical_simplexPushforward {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) :
    (twistedSingularToCubical L m).hom (simplexPushforward L σ m y a) =
      simplexCubicalPushforward L σ m
        (((singularToCubical (ULift.{v} ℤ)).app (simplexModel.{v} n)).f m y) a :=
  (congrArg (twistedSingularToCubical L m).hom (simplexPushforward_apply L σ m y a)).trans
    ((twistedSingularToCubical_twistedPushforward L (simplexToHom σ) _ y a).trans
      (simplexCubicalPushforward_apply L σ m _ a).symm)

/-- The comparison from simplicial to cubical chains commutes with the boundaries. -/
theorem twistedSingularToCubical_comm (n : ℕ) :
    (twistedChainComplex L).d (n + 1) n ≫ twistedSingularToCubical L n =
      twistedSingularToCubical L (n + 1) ≫ L.normalizedTwistedCubicalChainComplex.d (n + 1) n := by
  refine twistedChainComplex_hom_ext L fun σ ↦ ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change (twistedSingularToCubical L n).hom
      ((twistedChainComplex L).d (n + 1) n (ιTwistedChainComplex L (n + 1) σ a)) =
    L.normalizedTwistedCubicalChainComplex.d (n + 1) n
      ((twistedSingularToCubical L (n + 1)).hom (ιTwistedChainComplex L (n + 1) σ a))
  erw [ιTwistedChainComplex_eq_twistedPushforward σ a, ← simplexPushforward_apply,
    d_simplexPushforward,
    twistedSingularToCubical_simplexPushforward, twistedSingularToCubical_simplexPushforward,
    normalizedTwistedCubicalChainComplex_d_apply, boundary_simplexCubicalPushforward]
  exact congrArg (fun y ↦ simplexCubicalPushforward L σ n y a)
    (HomologicalComplex.Hom.comm_apply ((singularToCubical (ULift.{v} ℤ)).app _) (n + 1) n _).symm

/-- The **comparison chain map** from the simplicial chain complex with coefficients in `L` to the
normalized cubical chain complex with coefficients in `L`. -/
def twistedSingularToCubicalMap :
    twistedChainComplex L ⟶ L.normalizedTwistedCubicalChainComplex where
  f n := twistedSingularToCubical L n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact (twistedSingularToCubical_comm L j).symm

/-- The components of the comparison chain map. -/
@[simp]
theorem twistedSingularToCubicalMap_f (n : ℕ) :
    (twistedSingularToCubicalMap L).f n = twistedSingularToCubical L n :=
  (rfl)

/-- **Naturality in the space** of the comparison chain map. -/
theorem twistedSingularToCubicalMap_naturality {Y : TopCat.{v}} (f : X ⟶ Y)
    (L : LocalCoefficientSystem.{u, v, v} R Y) :
    twistedChainComplexMap f L ≫ twistedSingularToCubicalMap L =
      twistedSingularToCubicalMap ((pullback f.hom).obj L) ≫
        normalizedTwistedCubicalChainComplexMap f.hom L := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ twistedChainComplex_hom_ext _ fun σ ↦ ?_
  simp only [HomologicalComplex.comp_f, twistedSingularToCubicalMap_f,
    normalizedTwistedCubicalChainComplexMap_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change (twistedSingularToCubical L n).hom ((twistedChainComplexMap f L).f n
      (ιTwistedChainComplex ((pullback f.hom).obj L) n σ a)) =
    NormalizedTwistedCubicalChain.map f.hom L n
      ((twistedSingularToCubical ((pullback f.hom).obj L) n).hom
        (ιTwistedChainComplex ((pullback f.hom).obj L) n σ a))
  refine ((congrArg (twistedSingularToCubical L n).hom (ConcreteCategory.congr_hom
    (ιTwistedChainComplex_twistedChainComplexMap_f f L n σ) a)).trans
    (twistedSingularToCubical_ιTwistedChainComplex L _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (NormalizedTwistedCubicalChain.map f.hom L n)
    (twistedSingularToCubical_ιTwistedChainComplex ((pullback f.hom).obj L) σ a)).symm
  -- The pushed-forward simplex is `f ∘ σ`, whose map from the model is `σ.down ≫ f`.
  exact (NormalizedTwistedCubicalChain.map_pushforward (Z := simplexModel.{v} n) f.hom L
    (f := (simplexToHom σ).hom) (z₀ := SimplexCategory.toTopInitialVertex ⦋n⦌)
    (singularToCubicalGen (ULift.{v} ℤ) n) a).symm

/-- **Naturality in the local system** of the comparison chain map. -/
theorem twistedSingularToCubicalMap_coefficientMap_naturality
    {K : LocalCoefficientSystem.{u, v, v} R X} (η : L ⟶ K) :
    twistedChainComplexCoefficientMap η ≫ twistedSingularToCubicalMap K =
      twistedSingularToCubicalMap L ≫ normalizedTwistedCubicalChainComplexCoefficientMap η := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ twistedChainComplex_hom_ext L fun σ ↦ ?_
  simp only [HomologicalComplex.comp_f, twistedSingularToCubicalMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change (twistedSingularToCubical K n).hom ((twistedChainComplexCoefficientMap η).f n
      (ιTwistedChainComplex L n σ a)) =
    NormalizedTwistedCubicalChain.coefficientMap η n
      ((twistedSingularToCubical L n).hom (ιTwistedChainComplex L n σ a))
  refine ((congrArg (twistedSingularToCubical K n).hom (ConcreteCategory.congr_hom
    (ιTwistedChainComplex_twistedChainComplexCoefficientMap_f η n σ) a)).trans
    (twistedSingularToCubical_ιTwistedChainComplex K σ _)).trans ?_
  exact (NormalizedTwistedCubicalChain.coefficientMap_pushforward (L := L) η _ _).symm.trans
    (congrArg (NormalizedTwistedCubicalChain.coefficientMap η n)
      (twistedSingularToCubical_ιTwistedChainComplex L σ a).symm)

/-- The comparison to cubical chains carries the simplicial pushforward along a cube to the cubical
pushforward of the image under the untwisted comparison. -/
lemma twistedSingularToCubical_twistedCubePushforward {n m : ℕ} (c : SingularCube X n)
    (y : ((singularChains (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    (twistedSingularToCubical L m).hom (twistedCubePushforward L c m y a) =
      cubeCubicalPushforward L c m
        (((singularToCubical (ULift.{v} ℤ)).app (cubeModel.{v} n)).f m y) a :=
  (congrArg (twistedSingularToCubical L m).hom (twistedCubePushforward_apply c m y a)).trans
    ((twistedSingularToCubical_twistedPushforward L (cubeToHom c) _ y a).trans
      (cubeCubicalPushforward_apply L c m _ a).symm)

end LocalCoefficientSystem

end TauCeti
