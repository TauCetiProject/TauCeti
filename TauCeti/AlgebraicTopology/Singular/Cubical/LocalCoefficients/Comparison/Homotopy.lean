/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import
  TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Comparison.SingularToCubical

/-!
# The comparison of cubical and simplicial chains with local coefficients

The comparison chain maps `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap` and
`TauCeti.LocalCoefficientSystem.twistedSingularToCubicalMap` between the normalized cubical chains
with coefficients in a local system `L` and the simplicial singular chains with coefficients in `L`
are inverse chain homotopy equivalences.  The homotopies are obtained from the natural homotopies
of the comparison without coefficients (`TauCeti.singularToCubicalCompHomotopy` and
`TauCeti.cubicalToSingularCompHomotopy`) in the same way as the comparison maps themselves: the
component of the homotopy on a simplex, or a cube, with a coefficient is the pushforward along it,
from the model, of the value of the untwisted homotopy on the model generator.

Identities between constructions of this kind reduce to the model, generator by generator.  A
simplex, or a cube, with a coefficient is a pushforward from a model
(`TauCeti.LocalCoefficientSystem.ιTwistedChainComplex_eq_twistedPushforward`), the constructions are
compatible with pushforwards
(`TauCeti.LocalCoefficientSystem.twistedSingularToCubical_twistedPushforward`,
`TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalToSingular_pushforward`, and their analogues
for the homotopies), and on the model the identities are those of the untwisted homotopies.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedSingularHomotopy`: the components of the homotopy on
  simplicial chains with coefficients, and
  `TauCeti.LocalCoefficientSystem.twistedSingularToCubicalCompHomotopy`: the homotopy from the
  composite `to ∘ from` of the comparison maps on simplicial chains to the identity.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalHomotopy`: the components of the
  homotopy on normalized cubical chains with coefficients, and
  `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularCompHomotopy`: the homotopy from the
  composite `from ∘ to` on normalized cubical chains to the identity.
* `TauCeti.LocalCoefficientSystem.twistedCubicalSingularHomotopyEquiv L`: the chain homotopy
  equivalence between the normalized cubical chain complex with coefficients in `L` and the
  simplicial chain complex with coefficients in `L`.

## Main results

* `TauCeti.LocalCoefficientSystem.twistedSingularHomotopy_twistedPushforward` and
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalHomotopy_pushforward`: compatibility of
  the homotopies with pushforwards from simply connected spaces.
* The instances `QuasiIso (twistedCubicalToSingularMap L)` and
  `QuasiIso (twistedSingularToCubicalMap L)`: both comparison maps are quasi-isomorphisms.

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

/-! ### The homotopy on simplicial chains -/

/-- The component of the homotopy on the summand of a simplex `σ`: the pushforward along `σ` of
the value of the untwisted homotopy on the identity simplex of the model. -/
def twistedSingularHomotopySummand {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    L.obj (initialVertex σ) →ₗ[R] (twistedChainComplex L).X (n + 1) :=
  twistedPushforward (Z := simplexModel.{v} n) L (simplexToHom σ)
    (SimplexCategory.toTopInitialVertex ⦋n⦌) (n + 1)
    (((singularToCubicalCompHomotopy (ULift.{v} ℤ) (simplexModel.{v} n)).hom n (n + 1)).hom
      (simplexChain (idSimplex n) 1))

/-- The homotopy on a summand is the pushforward of the value of the untwisted homotopy on the
model generator. -/
theorem twistedSingularHomotopySummand_apply {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (a : L.obj (initialVertex σ)) :
    twistedSingularHomotopySummand L σ a =
      twistedPushforward (Z := simplexModel.{v} n) L (simplexToHom σ)
        (SimplexCategory.toTopInitialVertex ⦋n⦌) (n + 1)
        (((singularToCubicalCompHomotopy (ULift.{v} ℤ) (simplexModel.{v} n)).hom n (n + 1)).hom
          (simplexChain (idSimplex n) 1)) a :=
  (rfl)

/-- The component of the homotopy on simplicial chains with coefficients: a simplex `σ` with a
coefficient goes to the pushforward along `σ` of the value of the untwisted homotopy on the
identity simplex of the model. -/
def twistedSingularHomotopy (n : ℕ) :
    (twistedChainComplex L).X n ⟶ (twistedChainComplex L).X (n + 1) :=
  twistedChainComplexDesc L fun σ ↦ ModuleCat.ofHom (twistedSingularHomotopySummand L σ)

/-- The homotopy on the summand of a simplex. -/
@[reassoc (attr := simp)]
theorem ιTwistedChainComplex_comp_twistedSingularHomotopy {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChainComplex L n σ ≫ twistedSingularHomotopy L n =
      ModuleCat.ofHom (twistedSingularHomotopySummand L σ) :=
  ιTwistedChainComplex_twistedChainComplexDesc L _ σ

/-- The homotopy on a simplex with a coefficient. -/
@[simp]
theorem twistedSingularHomotopy_ιTwistedChainComplex {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (a : L.obj (initialVertex σ)) :
    (twistedSingularHomotopy L n).hom (ιTwistedChainComplex L n σ a) =
      twistedSingularHomotopySummand L σ a :=
  ConcreteCategory.congr_hom (ιTwistedChainComplex_comp_twistedSingularHomotopy L σ) a

/-- **Compatibility with pushforwards.** The homotopy carries the simplicial pushforward of a
chain of a simply connected space to the pushforward of its image under the untwisted
homotopy. -/
theorem twistedSingularHomotopy_twistedPushforward {Z : TopCat.{v}} [SimplyConnectedSpace Z]
    (f : Z ⟶ X) (z₀ : Z) {n : ℕ} (y : ((singularChains (ULift.{v} ℤ)).obj Z).X n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    (twistedSingularHomotopy L n).hom (twistedPushforward L f z₀ n y a) =
      twistedPushforward L f z₀ (n + 1)
        (((singularToCubicalCompHomotopy (ULift.{v} ℤ) Z).hom n (n + 1)).hom y) a := by
  have h := singularChains_linearMap_ext
    (L := (((twistedSingularHomotopy L n).hom.toAddMonoidHom.toIntLinearMap).restrictScalars
      (ULift.{v} ℤ)) ∘ₗ ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      twistedPushforward L f z₀ n)
    (L' := ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      twistedPushforward L f z₀ (n + 1) ∘ₗ
      (((singularToCubicalCompHomotopy (ULift.{v} ℤ) Z).hom n (n + 1)).hom)) fun σ ↦ ?_
  · exact congrArg (fun φ ↦ φ y) h
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.applyₗ'_apply_apply, LinearMap.toAddMonoidHom_coe]
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change (twistedSingularHomotopy L n).hom (twistedPushforward L f z₀ n (simplexChain σ 1) a) =
    twistedPushforward L f z₀ (n + 1)
      (((singularToCubicalCompHomotopy (ULift.{v} ℤ) Z).hom n (n + 1)).hom (simplexChain σ 1)) a
  rw [singularToCubicalCompHomotopy_hom_simplexChain, twistedPushforward_simplexChain_one]
  refine (twistedSingularHomotopy_ιTwistedChainComplex L _ _).trans ?_
  exact (twistedPushforward_map (L := L) (f := f) (z₀ := z₀) (Z' := simplexModel.{v} n)
    (simplexToHom σ) (SimplexCategory.toTopInitialVertex ⦋n⦌) _ a).symm

/-- The homotopy carries the simplicial pushforward along a simplex to the pushforward of the
image under the untwisted homotopy. -/
lemma twistedSingularHomotopy_simplexPushforward {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) :
    (twistedSingularHomotopy L m).hom (simplexPushforward L σ m y a) =
      simplexPushforward L σ (m + 1) (((singularToCubicalCompHomotopy (ULift.{v} ℤ)
        (simplexModel.{v} n)).hom m (m + 1)).hom y) a :=
  (congrArg (twistedSingularHomotopy L m).hom (simplexPushforward_apply L σ m y a)).trans
    ((twistedSingularHomotopy_twistedPushforward L (simplexToHom σ) _ y a).trans
      (simplexPushforward_apply L σ (m + 1) _ a).symm)

/-- The homotopy identity of the composite on simplicial chains in degree zero, on a summand. -/
private lemma homotopy_identity_zero (σ : (TopCat.toSSet.obj X) _⦋0⦌)
    (a : L.obj (initialVertex σ)) :
    normalizedTwistedCubicalToSingular L 0 ((twistedSingularToCubical L 0).hom
        (ιTwistedChainComplex L 0 σ a)) - ιTwistedChainComplex L 0 σ a =
      (twistedChainComplex L).d 1 0 ((twistedSingularHomotopy L 0).hom
        (ιTwistedChainComplex L 0 σ a)) := by
  have hm := Homotopy.comm_zero_apply
    (singularToCubicalCompHomotopy (ULift.{v} ℤ) (simplexModel.{v} 0))
    (simplexChain (idSimplex 0) 1)
  -- The coefficient lies in the fibre at the initial vertex of `σ`, which is the fibre at the
  -- initial vertex of the model mapped by `σ` only by definition, so the first rewrite is `erw`.
  erw [ιTwistedChainComplex_eq_twistedPushforward σ a, ← simplexPushforward_apply,
    twistedSingularToCubical_simplexPushforward,
    normalizedTwistedCubicalToSingular_simplexCubicalPushforward,
    twistedSingularHomotopy_simplexPushforward, d_simplexPushforward, ← simplexPushforward_sub]
  exact congrArg (fun y ↦ simplexPushforward L σ 0 y a) (sub_eq_iff_eq_add.2 hm)

/-- The homotopy identity of the composite on simplicial chains in positive degrees, on a
summand. -/
private lemma homotopy_identity_succ (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (a : L.obj (initialVertex σ)) :
    normalizedTwistedCubicalToSingular L (n + 1) ((twistedSingularToCubical L (n + 1)).hom
        (ιTwistedChainComplex L (n + 1) σ a)) - ιTwistedChainComplex L (n + 1) σ a =
      (twistedSingularHomotopy L n).hom ((twistedChainComplex L).d (n + 1) n
        (ιTwistedChainComplex L (n + 1) σ a)) +
      (twistedChainComplex L).d (n + 2) (n + 1) ((twistedSingularHomotopy L (n + 1)).hom
        (ιTwistedChainComplex L (n + 1) σ a)) := by
  have hm := Homotopy.comm_succ_apply
    (singularToCubicalCompHomotopy (ULift.{v} ℤ) (simplexModel.{v} (n + 1))) n
    (simplexChain (idSimplex (n + 1)) 1)
  -- The coefficient lies in the fibre at the initial vertex of `σ`, which is the fibre at the
  -- initial vertex of the model mapped by `σ` only by definition, so the first rewrite is `erw`.
  erw [ιTwistedChainComplex_eq_twistedPushforward σ a, ← simplexPushforward_apply,
    twistedSingularToCubical_simplexPushforward,
    normalizedTwistedCubicalToSingular_simplexCubicalPushforward, d_simplexPushforward,
    twistedSingularHomotopy_simplexPushforward, twistedSingularHomotopy_simplexPushforward,
    d_simplexPushforward,
    ← simplexPushforward_sub, ← simplexPushforward_add]
  exact congrArg (fun y ↦ simplexPushforward L σ (n + 1) y a) (sub_eq_iff_eq_add.2 hm)

/-- The composite of the comparison maps on simplicial chains is homotopic to the identity. -/
def twistedSingularToCubicalCompHomotopy :
    Homotopy (twistedSingularToCubicalMap L ≫ twistedCubicalToSingularMap L)
      (𝟙 (twistedChainComplex L)) :=
  Homotopy.equivSubZero.symm
    (Homotopy.mkChainComplex _ (twistedSingularHomotopy L)
      (twistedChainComplex_hom_ext L fun σ ↦ ModuleCat.hom_ext (LinearMap.ext fun a ↦
        by
          simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
            HomologicalComplex.id_f, twistedSingularToCubicalMap_f, twistedCubicalToSingularMap_f,
            Preadditive.comp_sub, ModuleCat.hom_comp, ModuleCat.hom_sub,
            LinearMap.comp_apply, LinearMap.sub_apply, Category.comp_id]
          exact homotopy_identity_zero L σ a))
      fun n ↦ twistedChainComplex_hom_ext L fun σ ↦ ModuleCat.hom_ext (LinearMap.ext fun a ↦
        by
          simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
            HomologicalComplex.id_f, twistedSingularToCubicalMap_f, twistedCubicalToSingularMap_f,
            Preadditive.comp_sub, Preadditive.comp_add, ModuleCat.hom_comp, ModuleCat.hom_sub,
            ModuleCat.hom_add, LinearMap.comp_apply, LinearMap.sub_apply,
            LinearMap.add_apply, Category.comp_id]
          exact homotopy_identity_succ L n σ a))

/-- The components of the homotopy `twistedSingularToCubicalCompHomotopy` are the maps
`twistedSingularHomotopy`. -/
@[simp]
theorem twistedSingularToCubicalCompHomotopy_hom (n : ℕ) :
    (twistedSingularToCubicalCompHomotopy L).hom n (n + 1) = twistedSingularHomotopy L n :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ n

/-! ### The homotopy on cubical chains -/

/-- The value on the identity cube of the model of the homotopy on cubical chains. -/
private def cubicalHomotopyGen (n : ℕ) :
    ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X (n + 1) :=
  ((cubicalToSingularCompHomotopy (ULift.{v} ℤ) (cubeModel.{v} n)).hom n (n + 1)).hom
    (NormalizedCubicalChain.ofCube (cubeModel.{v} n) (ULift.{v} ℤ) (upCube n))

/-- The value of the untwisted homotopy on the model generator vanishes under the projection of
the model forgetting a coordinate: the projection carries the identity cube to a degenerate
cube, which is zero in the normalized chains. -/
private lemma map_forgetCoordinate_cubicalHomotopyGen {m : ℕ} (i : Fin (m + 1)) :
    ((normalizedCubicalChainComplex (ULift.{v} ℤ)).map (cubeToHom ((upCube.{v} m).comp
        (SingularCube.forgetCoordinate i)))).f (m + 1 + 1) (cubicalHomotopyGen (m + 1)) = 0 := by
  set g : cubeModel.{v} (m + 1) ⟶ cubeModel.{v} m := cubeToHom ((upCube.{v} m).comp
    (SingularCube.forgetCoordinate i)) with hg
  have hdeg : SingularCube.IsDegenerate
      (g.hom.comp (upCube.{v} (m + 1)) : SingularCube (cubeModel.{v} m : Type v) (m + 1)) := by
    rw [hg, cubeToHom_hom_comp_upCube, ← SingularCube.degeneracy_eq_comp]
    exact SingularCube.isDegenerate_degeneracy (upCube.{v} m) i
  have hup : NormalizedCubicalChain.ofCube (cubeModel.{v} m) (ULift.{v} ℤ)
      (g.hom.comp (upCube.{v} (m + 1))) = 0 :=
    NormalizedCubicalChain.ofCube_eq_zero (R := ULift.{v} ℤ) hdeg
  -- Naturality of the untwisted homotopy moves the projection past it, onto the generator.
  have hn := congrArg (fun φ ↦ φ (NormalizedCubicalChain.ofCube (cubeModel.{v} (m + 1))
    (ULift.{v} ℤ) (upCube (m + 1))))
    (congrArg ModuleCat.Hom.hom (cubicalToSingularCompHomotopy_hom_naturality
      (ULift.{v} ℤ) g (m + 1) (m + 1 + 1)))
  refine hn.symm.trans ?_
  -- The composite of `ModuleCat` morphisms is the composite of the linear maps by definition,
  -- which `rw` cannot see through the dependent chain-complex terms.
  change ((cubicalToSingularCompHomotopy (ULift.{v} ℤ) (cubeModel.{v} m)).hom (m + 1)
    (m + 1 + 1)).hom (((normalizedCubicalChainComplex (ULift.{v} ℤ)).map g).f (m + 1)
      (NormalizedCubicalChain.ofCube (cubeModel.{v} (m + 1)) (ULift.{v} ℤ) (upCube (m + 1)))) = 0
  rw [normalizedCubicalChainComplex_map_f_apply, NormalizedCubicalChain.map_ofCube, hup]
  exact map_zero _

/-- A degenerate cube gives zero: its pushforward of the value of the homotopy on the model
generator vanishes.  The cube is a degeneracy `s ∘ π`, the pushforward along it factors through
the pushforward along `s` of the image of the generator under the projection `π`, and the
latter vanishes by `map_forgetCoordinate_cubicalHomotopyGen`. -/
private lemma cubeCubicalPushforward_cubicalHomotopyGen_eq_zero {n : ℕ} {c : SingularCube X n}
    (hc : SingularCube.IsDegenerate c) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    cubeCubicalPushforward L c (n + 1) (cubicalHomotopyGen n) a = 0 := by
  cases n with
  | zero => exact (SingularCube.not_isDegenerate_zero c hc).elim
  | succ m =>
    obtain ⟨i, s, hs⟩ := SingularCube.isDegenerate_iff_exists_eq_degeneracy.1 hc
    obtain rfl : c = s.comp (SingularCube.forgetCoordinate i) :=
      hs.trans (SingularCube.degeneracy_eq_comp s i)
    have h0 := map_forgetCoordinate_cubicalHomotopyGen.{v} i
    -- Transport the generator along the projection `g` of the model.
    set g : cubeModel.{v} (m + 1) ⟶ cubeModel.{v} m := cubeToHom ((upCube.{v} m).comp
      (SingularCube.forgetCoordinate i)) with hg
    have key := NormalizedTwistedCubicalChain.pushforward_map (L := L)
      (f := (cubeToHom s).hom) (z₀ := cubeModelOrigin m) (Z' := cubeModel.{v} (m + 1)) g.hom
      (cubeModelOrigin (m + 1)) (cubicalHomotopyGen (m + 1)) a
    have hmap : NormalizedCubicalChain.map (ULift.{v} ℤ) g.hom (m + 1 + 1)
        (cubicalHomotopyGen (m + 1)) = 0 :=
      (normalizedCubicalChainComplex_map_f_apply g _ _).symm.trans h0
    rw [hmap, map_zero] at key
    -- The projection sends the origin to the origin, so the transport is the identity.
    have e : L.map ((cubeToHom s).hom.pathClass (cubeModelOrigin m)
        (g.hom (cubeModelOrigin (m + 1)))) a = a :=
      map_pathClass_self_apply (cubeToHom s).hom (cubeModelOrigin m) a
    -- Evaluating the zero linear map gives zero by definition.
    have key2 : NormalizedTwistedCubicalChain.pushforward L
        ((cubeToHom s).hom.comp g.hom) (cubeModelOrigin (m + 1)) (m + 1 + 1)
        (cubicalHomotopyGen (m + 1)) (L.map ((cubeToHom s).hom.pathClass (cubeModelOrigin m)
          (g.hom (cubeModelOrigin (m + 1)))) a) = 0 := key.symm
    rw [e] at key2
    exact (cubeCubicalPushforward_apply L _ _ _ _).trans key2

/-- The homotopy on cubical chains with coefficients, before normalization. -/
private def cubicalHomotopyUnnormalized (n : ℕ) :
    L.TwistedCubicalChain n →ₗ[R] L.NormalizedTwistedCubicalChain (n + 1) :=
  TwistedCubicalChain.desc L fun c ↦ NormalizedTwistedCubicalChain.pushforward
    (Z := cubeModel.{v} n) L (cubeToHom c).hom (cubeModelOrigin n) (n + 1) (cubicalHomotopyGen n)

/-- The component of the homotopy on normalized cubical chains with coefficients: a cube `c`
with a coefficient goes to the pushforward along `c` of the value of the untwisted homotopy on the
identity cube of the model. -/
def normalizedTwistedCubicalHomotopy (n : ℕ) :
    L.NormalizedTwistedCubicalChain n →ₗ[R] L.NormalizedTwistedCubicalChain (n + 1) :=
  Submodule.liftQ _ (cubicalHomotopyUnnormalized L n)
    (TwistedCubicalChain.degenerate_le fun c hc a ↦
      (TwistedCubicalChain.desc_ofCube _ c a).trans
        ((cubeCubicalPushforward_apply L c _ _ a).symm.trans
          (cubeCubicalPushforward_cubicalHomotopyGen_eq_zero L hc a)))

/-- The homotopy on a cube with a coefficient: the pushforward along the cube of the value of the
untwisted homotopy on the identity cube of the model. -/
@[simp]
theorem normalizedTwistedCubicalHomotopy_ofCube {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalHomotopy L n (NormalizedTwistedCubicalChain.ofCube L c a) =
      NormalizedTwistedCubicalChain.pushforward (Z := cubeModel.{v} n) L (cubeToHom c).hom
        (cubeModelOrigin n) (n + 1)
        (((cubicalToSingularCompHomotopy (ULift.{v} ℤ) (cubeModel.{v} n)).hom n (n + 1)).hom
          (NormalizedCubicalChain.ofCube (cubeModel.{v} n) (ULift.{v} ℤ) (upCube n))) a := by
  rw [NormalizedTwistedCubicalChain.ofCube_apply]
  exact (Submodule.liftQ_apply _ _ _).trans (TwistedCubicalChain.desc_ofCube _ c a)

/-- **Compatibility with pushforwards.** The homotopy carries the cubical pushforward of a chain
of a simply connected space to the pushforward of its image under the untwisted homotopy. -/
theorem normalizedTwistedCubicalHomotopy_pushforward {Z : TopCat.{v}} [SimplyConnectedSpace Z]
    (f : Z ⟶ X) (z₀ : Z) {n : ℕ} (y : NormalizedCubicalChain Z (ULift.{v} ℤ) n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    normalizedTwistedCubicalHomotopy L n
        (NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n y a) =
      NormalizedTwistedCubicalChain.pushforward L f.hom z₀ (n + 1)
        (((cubicalToSingularCompHomotopy (ULift.{v} ℤ) Z).hom n (n + 1)).hom y) a := by
  have h := NormalizedCubicalChain.linearMap_ext (R := ULift.{v} ℤ)
    (f := ((normalizedTwistedCubicalHomotopy L n).toAddMonoidHom.toIntLinearMap.restrictScalars
      (ULift.{v} ℤ)) ∘ₗ ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n)
    (g := ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      NormalizedTwistedCubicalChain.pushforward L f.hom z₀ (n + 1) ∘ₗ
      (((cubicalToSingularCompHomotopy (ULift.{v} ℤ) Z).hom n (n + 1)).hom)) fun d ↦ ?_
  · exact congrArg (fun φ ↦ φ y) h
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.applyₗ'_apply_apply, LinearMap.toAddMonoidHom_coe]
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change normalizedTwistedCubicalHomotopy L n (NormalizedTwistedCubicalChain.pushforward L f.hom
      z₀ n (NormalizedCubicalChain.ofCube Z (ULift.{v} ℤ) d) a) =
    NormalizedTwistedCubicalChain.pushforward L f.hom z₀ (n + 1)
      (((cubicalToSingularCompHomotopy (ULift.{v} ℤ) Z).hom n (n + 1)).hom
        (NormalizedCubicalChain.ofCube Z (ULift.{v} ℤ) d)) a
  -- The pushforward of a cube is the cube `f ∘ d` with the transported coefficient, and the
  -- untwisted homotopy carries the cube `d` to the pushforward of its model value under `d`.
  have e1 := NormalizedTwistedCubicalChain.pushforward_ofCube (L := L) (f := f.hom)
    (z₀ := z₀) d a
  have e2 := cubicalToSingularCompHomotopy_hom_ofCube (k := ULift.{v} ℤ) d
  refine (congrArg _ e1).trans ((normalizedTwistedCubicalHomotopy_ofCube L (f.hom.comp d) _).trans
    ?_)
  refine Eq.trans ?_ (congrArg (fun y ↦ NormalizedTwistedCubicalChain.pushforward L f.hom z₀
    (n + 1) y a) e2).symm
  exact (NormalizedTwistedCubicalChain.pushforward_map (L := L) (f := f.hom) (z₀ := z₀)
    (Z' := cubeModel.{v} n) (cubeToHom d).hom (cubeModelOrigin n) (cubicalHomotopyGen n) a).symm

/-- The homotopy on cubical chains carries the cubical pushforward along a cube to the pushforward
of the image under the untwisted homotopy. -/
lemma normalizedTwistedCubicalHomotopy_cubeCubicalPushforward {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalHomotopy L m (cubeCubicalPushforward L c m y a) =
      cubeCubicalPushforward L c (m + 1) (((cubicalToSingularCompHomotopy (ULift.{v} ℤ)
        (cubeModel.{v} n)).hom m (m + 1)).hom y) a :=
  (congrArg (normalizedTwistedCubicalHomotopy L m) (cubeCubicalPushforward_apply L c m y a)).trans
    ((normalizedTwistedCubicalHomotopy_pushforward L (cubeToHom c) (cubeModelOrigin n) y a).trans
      (cubeCubicalPushforward_apply L c (m + 1) _ a).symm)

/-- The homotopy identity of the composite on cubical chains in degree zero, on a cube. -/
private lemma cubical_identity_zero (c : SingularCube X 0)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    (twistedSingularToCubical L 0).hom (normalizedTwistedCubicalToSingular L 0
        (NormalizedTwistedCubicalChain.ofCube L c a)) -
        NormalizedTwistedCubicalChain.ofCube L c a =
      L.normalizedTwistedCubicalChainComplex.d 1 0
        (normalizedTwistedCubicalHomotopy L 0 (NormalizedTwistedCubicalChain.ofCube L c a)) := by
  have hm := Homotopy.comm_zero_apply
    (cubicalToSingularCompHomotopy (ULift.{v} ℤ) (cubeModel.{v} 0))
    ((cubicalModelPresentation (ULift.{v} ℤ)).gen 0)
  -- The model generator is typed through the model presentation, which `rw` does not unfold.
  erw [ofCube_eq_cubeCubicalPushforward,
    normalizedTwistedCubicalToSingular_cubeCubicalPushforward,
    twistedSingularToCubical_twistedCubePushforward,
    normalizedTwistedCubicalHomotopy_cubeCubicalPushforward, d_cubeCubicalPushforward,
    ← cubeCubicalPushforward_sub]
  exact congrArg (fun y ↦ cubeCubicalPushforward L c 0 y a) (sub_eq_iff_eq_add.2 hm)

/-- The homotopy identity of the composite on cubical chains in positive degrees, on a cube. -/
private lemma cubical_identity_succ (n : ℕ) (c : SingularCube X (n + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    (twistedSingularToCubical L (n + 1)).hom (normalizedTwistedCubicalToSingular L (n + 1)
        (NormalizedTwistedCubicalChain.ofCube L c a)) -
        NormalizedTwistedCubicalChain.ofCube L c a =
      normalizedTwistedCubicalHomotopy L n (NormalizedTwistedCubicalChain.boundary L n
        (NormalizedTwistedCubicalChain.ofCube L c a)) +
      NormalizedTwistedCubicalChain.boundary L (n + 1)
        (normalizedTwistedCubicalHomotopy L (n + 1)
          (NormalizedTwistedCubicalChain.ofCube L c a)) := by
  have hm := Homotopy.comm_succ_apply
    (cubicalToSingularCompHomotopy (ULift.{v} ℤ) (cubeModel.{v} (n + 1))) n
    ((cubicalModelPresentation (ULift.{v} ℤ)).gen (n + 1))
  -- The model generator is typed through the model presentation, which `rw` does not unfold.
  erw [ofCube_eq_cubeCubicalPushforward,
    normalizedTwistedCubicalToSingular_cubeCubicalPushforward,
    twistedSingularToCubical_twistedCubePushforward, boundary_cubeCubicalPushforward,
    normalizedTwistedCubicalHomotopy_cubeCubicalPushforward,
    normalizedTwistedCubicalHomotopy_cubeCubicalPushforward, boundary_cubeCubicalPushforward,
    ← cubeCubicalPushforward_sub, ← cubeCubicalPushforward_add]
  exact congrArg (fun y ↦ cubeCubicalPushforward L c (n + 1) y a) (sub_eq_iff_eq_add.2 hm)

/-- The composite of the comparison maps on normalized cubical chains is homotopic to the
identity. -/
def twistedCubicalToSingularCompHomotopy :
    Homotopy (twistedCubicalToSingularMap L ≫ twistedSingularToCubicalMap L)
      (𝟙 L.normalizedTwistedCubicalChainComplex) :=
  Homotopy.equivSubZero.symm
    (Homotopy.mkChainComplex _ (fun n ↦ ModuleCat.ofHom (normalizedTwistedCubicalHomotopy L n))
      (by
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
          HomologicalComplex.id_f, twistedSingularToCubicalMap_f, twistedCubicalToSingularMap_f,
          normalizedTwistedCubicalChainComplex_d]
        exact ModuleCat.hom_ext (NormalizedTwistedCubicalChain.hom_ext fun c ↦
          LinearMap.ext fun a ↦ cubical_identity_zero L c a))
      fun n ↦ by
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
          HomologicalComplex.id_f, twistedSingularToCubicalMap_f, twistedCubicalToSingularMap_f,
          normalizedTwistedCubicalChainComplex_d]
        exact ModuleCat.hom_ext (NormalizedTwistedCubicalChain.hom_ext fun c ↦
          LinearMap.ext fun a ↦ cubical_identity_succ L n c a))

/-- The components of the homotopy `twistedCubicalToSingularCompHomotopy` are the maps
`normalizedTwistedCubicalHomotopy`. -/
@[simp]
theorem twistedCubicalToSingularCompHomotopy_hom (n : ℕ) :
    (twistedCubicalToSingularCompHomotopy L).hom n (n + 1) =
      ModuleCat.ofHom (normalizedTwistedCubicalHomotopy L n) :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ n

/-- **Cubical and simplicial chains with local coefficients are chain homotopy equivalent.** -/
def twistedCubicalSingularHomotopyEquiv :
    HomotopyEquiv L.normalizedTwistedCubicalChainComplex (twistedChainComplex L) where
  hom := twistedCubicalToSingularMap L
  inv := twistedSingularToCubicalMap L
  homotopyHomInvId := twistedCubicalToSingularCompHomotopy L
  homotopyInvHomId := twistedSingularToCubicalCompHomotopy L

@[simp]
theorem twistedCubicalSingularHomotopyEquiv_hom :
    (twistedCubicalSingularHomotopyEquiv L).hom = twistedCubicalToSingularMap L :=
  (rfl)

@[simp]
theorem twistedCubicalSingularHomotopyEquiv_inv :
    (twistedCubicalSingularHomotopyEquiv L).inv = twistedSingularToCubicalMap L :=
  (rfl)

/-- The comparison map from cubical to simplicial chains with local coefficients is a
quasi-isomorphism. -/
instance : QuasiIso (twistedCubicalToSingularMap L) := by
  rw [← twistedCubicalSingularHomotopyEquiv_hom]
  infer_instance

/-- The comparison map from simplicial to cubical chains with local coefficients is a
quasi-isomorphism. -/
instance : QuasiIso (twistedSingularToCubicalMap L) := by
  rw [← twistedCubicalSingularHomotopyEquiv_inv]
  infer_instance

end LocalCoefficientSystem

end TauCeti
