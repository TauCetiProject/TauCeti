/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.SingularToCubical

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

* `TauCeti.LocalCoefficientSystem.twistedSingularHomotopy`,
  `TauCeti.LocalCoefficientSystem.twistedCubicalHomotopy`: the components of the homotopies.
* `TauCeti.LocalCoefficientSystem.twistedCubicalSingularHomotopyEquiv L`: the chain homotopy
  equivalence between the simplicial chain complex with coefficients in `L` and the normalized
  cubical chain complex with coefficients in `L`.

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

/-- The component of the homotopy on simplicial chains with coefficients: a simplex `σ` with a
coefficient goes to the pushforward along `σ` of the value of the untwisted homotopy on the
identity simplex of the model. -/
def twistedSingularHomotopy (n : ℕ) :
    (twistedChainComplex L).X n ⟶ (twistedChainComplex L).X (n + 1) :=
  twistedChainComplexDesc L fun σ ↦ ModuleCat.ofHom
    (twistedPushforward (Z := simplexModel.{v} n) L (simplexToHom σ)
      (SimplexCategory.toTopInitialVertex ⦋n⦌) (n + 1)
      (((singularToCubicalCompHomotopy (ULift.{v} ℤ) (simplexModel.{v} n)).hom n (n + 1)).hom
        (simplexChain (idSimplex n) 1)))

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
  refine (ConcreteCategory.congr_hom
    (ιTwistedChainComplex_twistedChainComplexDesc L _ ((TopCat.toSSet.map f).app _ σ)) _).trans ?_
  exact (twistedPushforward_map (L := L) (f := f) (z₀ := z₀) (Z' := simplexModel.{v} n)
    (simplexToHom σ) (SimplexCategory.toTopInitialVertex ⦋n⦌) _ a).symm

/-- The simplicial pushforward along a simplex `σ` from the initial vertex of the model, with the
coefficient at the initial vertex of `σ`. -/
private def spush {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) (m : ℕ)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) : (twistedChainComplex L).X m :=
  twistedPushforward (Z := simplexModel.{v} n) L (simplexToHom σ)
    (SimplexCategory.toTopInitialVertex ⦋n⦌) m y a

/-- The cubical pushforward along a simplex `σ` from the initial vertex of the model, with the
coefficient at the initial vertex of `σ`. -/
private def cpush {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) (m : ℕ)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) : L.NormalizedTwistedCubicalChain m :=
  NormalizedTwistedCubicalChain.pushforward (Z := simplexModel.{v} n) L (simplexToHom σ).hom
    (SimplexCategory.toTopInitialVertex ⦋n⦌) m y a

private lemma spush_add {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y y' : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) :
    spush L σ m (y + y') a = spush L σ m y a + spush L σ m y' a := by
  -- Evaluating a sum of linear maps is the sum of the evaluations by definition.
  exact congrArg (fun φ ↦ φ a) (map_add (twistedPushforward (Z := simplexModel.{v} n) L
    (simplexToHom σ) (SimplexCategory.toTopInitialVertex ⦋n⦌) m) y y')

private lemma spush_sub {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y y' : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) :
    spush L σ m (y - y') a = spush L σ m y a - spush L σ m y' a := by
  -- Evaluating a difference of linear maps is the difference of the evaluations by definition.
  exact congrArg (fun φ ↦ φ a) (map_sub (twistedPushforward (Z := simplexModel.{v} n) L
    (simplexToHom σ) (SimplexCategory.toTopInitialVertex ⦋n⦌) m) y y')

/-- The identity simplex of the model pushes forward to the summand of the simplex. -/
private lemma ι_eq_spush {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : L.obj (initialVertex σ)) :
    ιTwistedChainComplex L n σ a = spush L σ n (simplexChain (idSimplex n) 1) a :=
  ιTwistedChainComplex_eq_twistedPushforward σ a

private lemma d_spush {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X (m + 1))
    (a : L.obj (initialVertex σ)) :
    (twistedChainComplex L).d (m + 1) m (spush L σ (m + 1) y a) =
      spush L σ m (((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).d (m + 1) m y) a :=
  twistedPushforward_d (Z := simplexModel.{v} n) y a

private lemma homotopy_spush {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) :
    (twistedSingularHomotopy L m).hom (spush L σ m y a) =
      spush L σ (m + 1) (((singularToCubicalCompHomotopy (ULift.{v} ℤ)
        (simplexModel.{v} n)).hom m (m + 1)).hom y) a :=
  twistedSingularHomotopy_twistedPushforward L (simplexToHom σ) _ y a

private lemma from_spush {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) :
    (twistedSingularToCubical L m).hom (spush L σ m y a) =
      cpush L σ m (((singularToCubical (ULift.{v} ℤ)).app (simplexModel.{v} n)).f m y) a :=
  twistedSingularToCubical_twistedPushforward L (simplexToHom σ) _ y a

private lemma to_cpush {n m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex σ)) :
    normalizedTwistedCubicalToSingular L m (cpush L σ m y a) =
      spush L σ m (((cubicalToSingular (ULift.{v} ℤ)).app (simplexModel.{v} n)).f m y) a :=
  normalizedTwistedCubicalToSingular_pushforward (L := L) (simplexToHom σ) _ y a

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
  rw [ι_eq_spush, from_spush, to_cpush, homotopy_spush, d_spush, ← spush_sub]
  exact congrArg (fun y ↦ spush L σ 0 y a) (sub_eq_iff_eq_add.2 hm)

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
  rw [ι_eq_spush, from_spush, to_cpush, d_spush, homotopy_spush, homotopy_spush, d_spush,
    ← spush_sub, ← spush_add]
  exact congrArg (fun y ↦ spush L σ (n + 1) y a) (sub_eq_iff_eq_add.2 hm)

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

/-! ### The homotopy on cubical chains -/

/-- The cubical pushforward along a cube `c` from the origin of the model, with the coefficient at
the origin of `c`. -/
private def cpushC {n : ℕ} (c : SingularCube X n) (m : ℕ)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) : L.NormalizedTwistedCubicalChain m :=
  NormalizedTwistedCubicalChain.pushforward (Z := cubeModel.{v} n) L (cubeToHom c).hom
    (cubeModelOrigin n) m y a

/-- The identity cube of the model, as a normalized cubical chain. -/
private def cubeGen (n : ℕ) :
    ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X n :=
  NormalizedCubicalChain.ofCube (cubeModel.{v} n) (ULift.{v} ℤ) (upCube n)

/-- The value on the identity cube of the model of the homotopy on cubical chains. -/
private def cubicalHomotopyGen (n : ℕ) :
    ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X (n + 1) :=
  ((cubicalToSingularCompHomotopy (ULift.{v} ℤ) (cubeModel.{v} n)).hom n (n + 1)).hom
    (cubeGen n)

/-- A degenerate cube gives zero: its pushforward of the value of the homotopy on the model
generator vanishes. -/
private lemma cpushC_cubicalHomotopyGen_eq_zero {n : ℕ} {c : SingularCube X n}
    (hc : SingularCube.IsDegenerate c) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    cpushC L c (n + 1) (cubicalHomotopyGen n) a = 0 := by
  cases n with
  | zero => exact (SingularCube.not_isDegenerate_zero c hc).elim
  | succ m =>
    obtain ⟨i, s, hs⟩ := SingularCube.isDegenerate_iff_exists_eq_degeneracy.1 hc
    -- the degeneracy is the precomposition with the projection, by definition
    obtain rfl : c = s.comp (ContinuousMap.precomp
        (X := fun _ : Fin (m + 1) ↦ unitInterval) i.succAbove) :=
      hs.trans (ContinuousMap.ext fun x ↦ by rw [SingularCube.degeneracy_apply]; rfl)
    -- the projection of the model `Iᵐ⁺¹` forgetting the `i`-th coordinate
    set g : cubeModel.{v} (m + 1) ⟶ cubeModel.{v} m := cubeToHom ((upCube.{v} m).comp
      (ContinuousMap.precomp (X := fun _ : Fin (m + 1) ↦ unitInterval) i.succAbove)) with hg
    have hdeg : SingularCube.IsDegenerate
        (g.hom.comp (upCube.{v} (m + 1)) : SingularCube (cubeModel.{v} m : Type v) (m + 1)) := by
      rw [hg, cubeToHom_hom_comp_upCube]
      -- The degeneracy is the precomposition with the projection, by definition.
      have hu : (upCube.{v} m).comp
          (ContinuousMap.precomp (X := fun _ : Fin (m + 1) ↦ unitInterval) i.succAbove) =
          SingularCube.degeneracy (upCube.{v} m) i :=
        ContinuousMap.ext fun x ↦ by rw [SingularCube.degeneracy_apply]; rfl
      rw [hu]
      exact SingularCube.isDegenerate_degeneracy (upCube.{v} m) i
    have hup : NormalizedCubicalChain.ofCube (cubeModel.{v} m) (ULift.{v} ℤ)
        (g.hom.comp (upCube.{v} (m + 1))) = 0 :=
      NormalizedCubicalChain.ofCube_eq_zero (R := ULift.{v} ℤ) hdeg
    have h0 : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).map g).f (m + 1 + 1)
        (cubicalHomotopyGen (m + 1)) = 0 := by
      have hn := congrArg (fun φ ↦ φ (NormalizedCubicalChain.ofCube (cubeModel.{v} (m + 1))
        (ULift.{v} ℤ) (upCube (m + 1))))
        (congrArg ModuleCat.Hom.hom (cubicalToSingularCompHomotopy_hom_naturality
          (ULift.{v} ℤ) g (m + 1) (m + 1 + 1)))
      refine hn.symm.trans ?_
      -- the image of the identity cube under the projection is the degenerate cube
      change ((cubicalToSingularCompHomotopy (ULift.{v} ℤ) (cubeModel.{v} m)).hom (m + 1)
        (m + 1 + 1)).hom (((normalizedCubicalChainComplex (ULift.{v} ℤ)).map g).f (m + 1)
          (NormalizedCubicalChain.ofCube (cubeModel.{v} (m + 1)) (ULift.{v} ℤ) (upCube (m + 1)))) =
        0
      rw [normalizedCubicalChainComplex_map_f_apply, NormalizedCubicalChain.map_ofCube, hup]
      exact map_zero _
    have key := NormalizedTwistedCubicalChain.pushforward_map (L := L)
      (f := (cubeToHom s).hom) (z₀ := cubeModelOrigin m) (Z' := cubeModel.{v} (m + 1)) g.hom
      (cubeModelOrigin (m + 1)) (cubicalHomotopyGen (m + 1)) a
    have hmap : NormalizedCubicalChain.map (ULift.{v} ℤ) g.hom (m + 1 + 1)
        (cubicalHomotopyGen (m + 1)) = 0 := h0
    rw [hmap, map_zero] at key
    -- The projection sends the origin to the origin, so the transport is the identity.
    have e : L.map ((cubeToHom s).hom.pathClass (cubeModelOrigin m)
        (g.hom (cubeModelOrigin (m + 1)))) a = a :=
      (congrArg (fun p : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _ ↦ L.map p a)
        (ContinuousMap.pathClass_self (cubeToHom s).hom (cubeModelOrigin m))).trans
          ((congrArg (fun φ ↦ φ a) (congrArg ModuleCat.Hom.hom
            (L.map_id (FundamentalGroupoid.mk ((cubeToHom s) (cubeModelOrigin m)))))).trans rfl)
    -- Evaluating the zero linear map gives zero by definition.
    have key2 : NormalizedTwistedCubicalChain.pushforward L
        ((cubeToHom s).hom.comp g.hom) (cubeModelOrigin (m + 1)) (m + 1 + 1)
        (cubicalHomotopyGen (m + 1)) (L.map ((cubeToHom s).hom.pathClass (cubeModelOrigin m)
          (g.hom (cubeModelOrigin (m + 1)))) a) = 0 := key.symm
    rw [e] at key2
    exact key2

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
        (cpushC_cubicalHomotopyGen_eq_zero L hc a))

/-- The homotopy on a cube with a coefficient. -/
private lemma normalizedTwistedCubicalHomotopy_ofCube {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalHomotopy L n (NormalizedTwistedCubicalChain.ofCube L c a) =
      cpushC L c (n + 1) (cubicalHomotopyGen n) a := by
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
  have e1 : NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n
      (NormalizedCubicalChain.ofCube Z (ULift.{v} ℤ) d) a =
      NormalizedTwistedCubicalChain.ofCube L (f.hom.comp d)
        (L.map (f.hom.pathClass z₀ (d 0)) a) :=
    (NormalizedTwistedCubicalChain.pushforward_ofCube d a).trans
      ((congrArg Submodule.Quotient.mk (TwistedCubicalChain.pushCube_apply d a)).trans
        (NormalizedTwistedCubicalChain.ofCube_apply _ _).symm)
  have e2 := cubicalToSingularCompHomotopy_hom_ofCube (k := ULift.{v} ℤ) d
  refine (congrArg _ e1).trans ((normalizedTwistedCubicalHomotopy_ofCube L (f.hom.comp d) _).trans
    ?_)
  refine Eq.trans ?_ (congrArg (fun y ↦ NormalizedTwistedCubicalChain.pushforward L f.hom z₀
    (n + 1) y a) e2).symm
  exact (NormalizedTwistedCubicalChain.pushforward_map (L := L) (f := f.hom) (z₀ := z₀)
    (Z' := cubeModel.{v} n) (cubeToHom d).hom (cubeModelOrigin n) (cubicalHomotopyGen n) a).symm

private lemma cpushC_add {n m : ℕ} (c : SingularCube X n)
    (y y' : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    cpushC L c m (y + y') a = cpushC L c m y a + cpushC L c m y' a :=
  -- Evaluating a sum of linear maps is the sum of the evaluations by definition.
  congrArg (fun φ ↦ φ a) (map_add (NormalizedTwistedCubicalChain.pushforward
    (Z := cubeModel.{v} n) L (cubeToHom c).hom (cubeModelOrigin n) m) y y')

private lemma cpushC_sub {n m : ℕ} (c : SingularCube X n)
    (y y' : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    cpushC L c m (y - y') a = cpushC L c m y a - cpushC L c m y' a :=
  -- Evaluating a difference of linear maps is the difference of the evaluations by definition.
  congrArg (fun φ ↦ φ a) (map_sub (NormalizedTwistedCubicalChain.pushforward
    (Z := cubeModel.{v} n) L (cubeToHom c).hom (cubeModelOrigin n) m) y y')

/-- A cube with a coefficient is the pushforward along itself of the identity cube of the model. -/
private lemma ofCube_eq_cpushC {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    NormalizedTwistedCubicalChain.ofCube L c a =
      cpushC L c n (cubeGen n) a := by
  refine Eq.symm ((NormalizedTwistedCubicalChain.pushforward_ofCube (L := L)
    (f := (cubeToHom c).hom) (z₀ := cubeModelOrigin n) (upCube n) a).trans ?_)
  refine (congrArg Submodule.Quotient.mk (TwistedCubicalChain.pushCube_apply (L := L)
    (f := (cubeToHom c).hom) (z₀ := cubeModelOrigin n) (upCube n) a)).trans
    ((NormalizedTwistedCubicalChain.ofCube_apply _ _).symm.trans ?_)
  -- The path class from the origin of the model to itself is the identity.
  exact congrArg (NormalizedTwistedCubicalChain.ofCube L c)
    ((congrArg (fun q : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _ ↦ L.map q a)
      (ContinuousMap.pathClass_self (cubeToHom c).hom (cubeModelOrigin n))).trans
        ((congrArg (fun φ ↦ φ a) (congrArg ModuleCat.Hom.hom
          (L.map_id (FundamentalGroupoid.mk ((cubeToHom c) (cubeModelOrigin n)))))).trans rfl))

private lemma boundary_cpushC {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X (m + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    NormalizedTwistedCubicalChain.boundary L m (cpushC L c (m + 1) y a) =
      cpushC L c m (((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).d
        (m + 1) m y) a :=
  (NormalizedTwistedCubicalChain.boundary_pushforward (L := L) (f := (cubeToHom c).hom)
    (z₀ := cubeModelOrigin n) y a).trans
    (congrArg (fun z ↦ NormalizedTwistedCubicalChain.pushforward L (cubeToHom c).hom
      (cubeModelOrigin n) m z a) (normalizedCubicalChainComplex_obj_d_apply _ m y).symm)

private lemma d_cpushC {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X (m + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    L.normalizedTwistedCubicalChainComplex.d (m + 1) m (cpushC L c (m + 1) y a) =
      cpushC L c m (((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).d
        (m + 1) m y) a :=
  (normalizedTwistedCubicalChainComplex_d_apply L m _).trans
    ((NormalizedTwistedCubicalChain.boundary_pushforward (L := L) (f := (cubeToHom c).hom)
      (z₀ := cubeModelOrigin n) y a).trans
      (congrArg (fun z ↦ NormalizedTwistedCubicalChain.pushforward L (cubeToHom c).hom
        (cubeModelOrigin n) m z a) (normalizedCubicalChainComplex_obj_d_apply _ m y).symm))

private lemma homotopy_cpushC {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalHomotopy L m (cpushC L c m y a) =
      cpushC L c (m + 1) (((cubicalToSingularCompHomotopy (ULift.{v} ℤ)
        (cubeModel.{v} n)).hom m (m + 1)).hom y) a :=
  normalizedTwistedCubicalHomotopy_pushforward L (cubeToHom c) (cubeModelOrigin n) y a

private lemma from_twistedCubePushforward {n m : ℕ} (c : SingularCube X n)
    (y : ((singularChains (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    (twistedSingularToCubical L m).hom (twistedCubePushforward L c m y a) =
      cpushC L c m (((singularToCubical (ULift.{v} ℤ)).app (cubeModel.{v} n)).f m y) a :=
  (congrArg (twistedSingularToCubical L m).hom (twistedCubePushforward_apply c m y a)).trans
    (twistedSingularToCubical_twistedPushforward L (cubeToHom c) _ y a)

private lemma to_cpushC {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalToSingular L m (cpushC L c m y a) =
      twistedCubePushforward L c m
        (((cubicalToSingular (ULift.{v} ℤ)).app (cubeModel.{v} n)).f m y) a :=
  (normalizedTwistedCubicalToSingular_pushforward (L := L) (cubeToHom c) _ y a).trans
    (twistedCubePushforward_apply c m _ a).symm

/-- The component of the homotopy on normalized cubical chains, as a morphism of modules. -/
def twistedCubicalHomotopy (n : ℕ) :
    L.normalizedTwistedCubicalChainComplex.X n ⟶ L.normalizedTwistedCubicalChainComplex.X (n + 1) :=
  ModuleCat.ofHom (normalizedTwistedCubicalHomotopy L n)

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
    (cubeGen.{v} 0)
  rw [ofCube_eq_cpushC, to_cpushC, from_twistedCubePushforward, homotopy_cpushC, d_cpushC,
    ← cpushC_sub]
  exact congrArg (fun y ↦ cpushC L c 0 y a) (sub_eq_iff_eq_add.2 hm)

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
    (cubeGen.{v} (n + 1))
  rw [ofCube_eq_cpushC, to_cpushC, from_twistedCubePushforward, boundary_cpushC, homotopy_cpushC,
    homotopy_cpushC, boundary_cpushC, ← cpushC_sub, ← cpushC_add]
  exact congrArg (fun y ↦ cpushC L c (n + 1) y a) (sub_eq_iff_eq_add.2 hm)

/-- The composite of the comparison maps on normalized cubical chains is homotopic to the
identity. -/
def twistedCubicalSingularCompHomotopy :
    Homotopy (twistedCubicalToSingularMap L ≫ twistedSingularToCubicalMap L)
      (𝟙 L.normalizedTwistedCubicalChainComplex) :=
  Homotopy.equivSubZero.symm
    (Homotopy.mkChainComplex _ (twistedCubicalHomotopy L)
      (by
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
          HomologicalComplex.id_f, twistedSingularToCubicalMap_f, twistedCubicalToSingularMap_f,
          normalizedTwistedCubicalChainComplex_d, twistedCubicalHomotopy]
        exact ModuleCat.hom_ext (NormalizedTwistedCubicalChain.hom_ext fun c ↦
          LinearMap.ext fun a ↦ cubical_identity_zero L c a))
      fun n ↦ by
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
          HomologicalComplex.id_f, twistedSingularToCubicalMap_f, twistedCubicalToSingularMap_f,
          normalizedTwistedCubicalChainComplex_d, twistedCubicalHomotopy]
        exact ModuleCat.hom_ext (NormalizedTwistedCubicalChain.hom_ext fun c ↦
          LinearMap.ext fun a ↦ cubical_identity_succ L n c a))

/-- **Cubical and simplicial chains with local coefficients are chain homotopy equivalent.** -/
def twistedCubicalSingularHomotopyEquiv :
    HomotopyEquiv L.normalizedTwistedCubicalChainComplex (twistedChainComplex L) where
  hom := twistedCubicalToSingularMap L
  inv := twistedSingularToCubicalMap L
  homotopyHomInvId := twistedCubicalSingularCompHomotopy L
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
