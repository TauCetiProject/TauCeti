/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Comparison

/-!
# From simplicial to cubical chains with local coefficients

The comparison `TauCeti.singularToCubical` of the simplicial singular chains with the normalized
cubical chains is natural, and the model `Δⁿ` is contractible, so it extends to chains with local
coefficients exactly as the comparison in the other direction does
(`TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap`).  For a singular `n`-simplex `σ` of
`X` and a coefficient `a` in the fibre at its initial vertex, the image is the twisted cubical
pushforward (`TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.pushforward`) along
`σ`, regarded as a map from the model, of the image `singularToCubicalGen n` of the identity simplex
of the model, with the coefficient `a` at the initial vertex of the model.

The decisive property is the compatibility with pushforwards from simply connected spaces
(`TauCeti.LocalCoefficientSystem.twistedSingularToCubical_twistedPushforward`): the comparison
carries the simplicial pushforward of a chain of a simply connected space `Z` to the cubical
pushforward of its image.  Every chain with local coefficients is such a pushforward from a
standard simplex, which reduces the verification of identities between natural constructions to the
model, where they are the untwisted ones.  Here it gives the chain map property.  The analogous
compatibility of the comparison in the other direction is
`TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalToSingular_pushforward`.

## Main definitions

* `TauCeti.singularToCubicalGen k n`: the image of the identity simplex of the model under the
  comparison.
* `TauCeti.LocalCoefficientSystem.twistedSingularToCubical L n`: the comparison on the
  `n`-chains with coefficients in `L`.
* `TauCeti.LocalCoefficientSystem.twistedSingularToCubicalMap L`: the comparison chain map from
  `TauCeti.LocalCoefficientSystem.twistedChainComplex L` to the normalized cubical chain
  complex with coefficients in `L`.

## Main results

* `TauCeti.LocalCoefficientSystem.twistedSingularToCubical_twistedPushforward`: compatibility
  with pushforwards from simply connected spaces.
* `TauCeti.LocalCoefficientSystem.twistedSingularToCubicalMap_coefficientMap_naturality`:
  naturality in the local system.

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

/-- A singular simplex of `X`, as a map from the model simplex. -/
abbrev simplexHom {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) : simplexModel.{v} n ⟶ X := σ.down

/-- The comparison from the summand of a simplex `σ`: the pushforward along `σ`, from the initial
vertex of the model, of the image of the identity simplex. -/
def twistedSingularToCubicalSummand {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    L.obj (initialVertex σ) →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  NormalizedTwistedCubicalChain.pushforward (Z := simplexModel.{v} n) L (simplexHom σ).hom
    (SimplexCategory.toTopInitialVertex ⦋n⦌) n (singularToCubicalGen (ULift.{v} ℤ) n)

/-- The summands of equal simplices agree on heterogeneously equal coefficients. -/
private theorem ιTwistedChainComplex_congr {n : ℕ} {ρ τ : (TopCat.toSSet.obj X) _⦋n⦌} (h : ρ = τ)
    {b : L.obj (initialVertex ρ)} {b' : L.obj (initialVertex τ)} (hb : b ≍ b') :
    ιTwistedChainComplex L n ρ b = ιTwistedChainComplex L n τ b' := by
  subst h
  rw [eq_of_heq hb]

/-- Transport along the path class to a point equal to the starting point does not change the
coefficient, up to the identification of the fibres. -/
private theorem map_pathClass_heq {Z : Type*} [TopologicalSpace Z] [SimplyConnectedSpace Z]
    (f : C(Z, X)) {z z' : Z} (h : z' = z) (b : L.obj (FundamentalGroupoid.mk (f z))) :
    (L.map (f.pathClass z z') b) ≍ b := by
  subst h
  rw [ContinuousMap.pathClass_self]
  simp

/-- Every twisted simplex is the pushforward along itself of the identity simplex of the
model: the summand of `σ` is reached by the pushforward from the initial vertex of the
model. -/
theorem ιTwistedChainComplex_eq_twistedPushforward {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (b : L.obj (initialVertex σ)) :
    ιTwistedChainComplex L n σ b =
      twistedPushforward (Z := simplexModel.{v} n) L (simplexHom σ)
        (SimplexCategory.toTopInitialVertex ⦋n⦌) n (simplexChain (idSimplex n) 1) b := by
  rw [twistedPushforward_simplexChain_one (Z := simplexModel.{v} n)]
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  exact ιTwistedChainComplex_congr L (toSSet_map_down_idSimplex σ).symm
    (map_pathClass_heq L _ (simplexMap_idSimplex n _) b).symm

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
    (Z' := simplexModel.{v} n) (simplexHom σ).hom
    (SimplexCategory.toTopInitialVertex ⦋n⦌) _ a).symm

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
  -- The fibre at the initial vertex of `σ` is the fibre at the initial vertex of the model
  -- mapped by `σ` by definition, so the coefficient `a` serves for the pushforwards, and the
  -- steps are composed as terms.
  have h1 := ιTwistedChainComplex_eq_twistedPushforward L σ a
  have h2 : (twistedChainComplex L).d (n + 1) n (ιTwistedChainComplex L (n + 1) σ a) =
      twistedPushforward L (simplexHom σ) (SimplexCategory.toTopInitialVertex _) n
        (((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} (n + 1))).d (n + 1) n
          (simplexChain (idSimplex (n + 1)) 1)) a :=
    (congrArg _ h1).trans (twistedPushforward_d _ _)
  have h3 := twistedSingularToCubical_twistedPushforward L (simplexHom σ)
    (SimplexCategory.toTopInitialVertex _) (simplexChain (idSimplex (n + 1)) (1 : ULift.{v} ℤ)) a
  have h4 := twistedSingularToCubical_twistedPushforward L (simplexHom σ)
    (SimplexCategory.toTopInitialVertex _)
    (((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} (n + 1))).d (n + 1) n
      (simplexChain (idSimplex (n + 1)) 1)) a
  refine Eq.trans ?_ (normalizedTwistedCubicalChainComplex_d_apply L n _).symm
  calc
    _ = (twistedSingularToCubical L n).hom (twistedPushforward L (simplexHom σ)
          (SimplexCategory.toTopInitialVertex _) n
          (((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} (n + 1))).d (n + 1) n
            (simplexChain (idSimplex (n + 1)) 1)) a) := congrArg _ h2
    _ = _ := h4
    _ = _ := congrArg (fun y ↦ NormalizedTwistedCubicalChain.pushforward L (simplexHom σ).hom
          (SimplexCategory.toTopInitialVertex _) n y a)
        (HomologicalComplex.Hom.comm_apply ((singularToCubical (ULift.{v} ℤ)).app _) (n + 1) n
          _).symm
    _ = _ := congrArg (fun y ↦ NormalizedTwistedCubicalChain.pushforward L (simplexHom σ).hom
          (SimplexCategory.toTopInitialVertex _) n y a)
        (normalizedCubicalChainComplex_obj_d_apply _ n _)
    _ = _ := (NormalizedTwistedCubicalChain.boundary_pushforward (L := L)
        (f := (simplexHom σ).hom) (z₀ := SimplexCategory.toTopInitialVertex _) _ a).symm
    _ = _ := congrArg _ h3.symm
    _ = _ := congrArg _ (congrArg _ h1.symm)

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
    (ConcreteCategory.congr_hom (ιTwistedChainComplex_comp_twistedSingularToCubical (L := K) σ)
      _)).trans ?_
  exact (NormalizedTwistedCubicalChain.coefficientMap_pushforward (L := L) η _ _).symm.trans
    (congrArg (NormalizedTwistedCubicalChain.coefficientMap η n) (ConcreteCategory.congr_hom
      (ιTwistedChainComplex_comp_twistedSingularToCubical (L := L) σ) a).symm)

end LocalCoefficientSystem

end TauCeti
