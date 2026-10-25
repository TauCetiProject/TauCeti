/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Pushforward
public import TauCeti.AlgebraicTopology.Singular.Twisted.Pushforward

/-!
# From cubical to simplicial chains with local coefficients

The comparison `TauCeti.cubicalToSingular` of the normalized cubical chains with the simplicial
singular chains is natural, and the model `Iⁿ` is contractible.  A local system is trivialized on
a contractible space, so the comparison extends to chains with local coefficients by transporting
the coefficient inside the model.  For a singular `n`-cube `c` of `X` and a coefficient
`a ∈ L(c 0)`, the image is the twisted pushforward
(`TauCeti.LocalCoefficientSystem.twistedPushforward`) along `c`, regarded as a map from the model,
of the image `y_n` of the identity cube of the model (`TauCeti.cubicalToSingularGen`), with the
coefficient `a` at the origin of the model.

The key formula (`TauCeti.LocalCoefficientSystem.twistedCubicalToSingular_ofSubcube`) gives the
image of a subcube `c ∘ ι` of `c`, with its transported coefficient, as the pushforward along `c`
of the image of the subcube `upCube ∘ ι` of the model.  It shows that degenerate cubes go to zero,
because the comparison is defined on normalized chains, and that the boundary is respected, because
the comparison is a chain map and the boundary of a cube is an alternating sum of subcubes.

The resulting chain map `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap L` from the
normalized cubical chain complex with coefficients in `L` to
`TauCeti.LocalCoefficientSystem.twistedChainComplex L` is natural in the space and in the local
system.

## Main definitions

* `TauCeti.cubicalToSingularGen k n`: the image of the identity cube of the model under the
  comparison.
* `TauCeti.LocalCoefficientSystem.twistedCubicalToSingular L n`: the linear map from the cubical
  chains with coefficients in `L` to the simplicial ones.
* `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap L`: the induced chain map on the
  normalized chain complex.
* `TauCeti.LocalCoefficientSystem.simplexPushforward`,
  `TauCeti.LocalCoefficientSystem.simplexCubicalPushforward`,
  `TauCeti.LocalCoefficientSystem.cubeCubicalPushforward`: the pushforwards along a simplex or a
  cube, from the model, of simplicial or cubical chains, with their additivity, boundary and
  differential lemmas and their compatibility with the comparison to simplicial chains.

## Main results

* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalToSingular_ofCube_const`: on a point
  cube the comparison is the inclusion of the point simplex.
* `TauCeti.LocalCoefficientSystem.twistedCubicalToSingular_ofSubcube`: the image of a subcube.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalToSingular_pushforward`: compatibility
  with the pushforwards from simply connected spaces.
* `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap_naturality`,
  `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap_coefficientMap_naturality`:
  naturality in the space and in the local system.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter XIV.
-/

public section

noncomputable section

open CategoryTheory unitInterval

open scoped Simplicial

universe u v

namespace TauCeti

namespace LocalCoefficientSystem

open SingularCube
open ContinuousMap (pathClass pathClass_comp pathClass_self)

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, v} R X)

/-- The **pushforward along a cube**: a simplicial chain of the model `Iⁿ` goes to the simplicial
chains of `X` with coefficients in `L` by the twisted pushforward along `c`, regarded as a map
from the model, from the origin of the model. -/
def twistedCubePushforward {n : ℕ} (c : SingularCube X n) (m : ℕ) :
    ((singularChains (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m →ₗ[ULift.{v} ℤ]
      (L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R] (twistedChainComplex L).X m) :=
  twistedPushforward L (cubeToHom c) (cubeModelOrigin n) m

/-- The comparison from the unnormalized cubical chains with coefficients in `L` to the simplicial
chains with coefficients in `L`: a cube `c` with a coefficient goes to the pushforward along `c` of
the image of the identity cube of the model. -/
def twistedCubicalToSingular (n : ℕ) :
    L.TwistedCubicalChain n →ₗ[R] (twistedChainComplex L).X n :=
  TwistedCubicalChain.desc L fun c ↦
    twistedCubePushforward L c n (cubicalToSingularGen (ULift.{v} ℤ) n)

variable {L}

/-- The evaluation formula of the pushforward along a cube on a simplex `t` of the model with an
integral coefficient: the simplex pushed forward along `c`, with the coefficient transported along
the path class inside the image of `c`.  The definition of `twistedCubePushforward` is not
unfolded outside this file, so this is the way to evaluate it on generators. -/
@[simp]
theorem twistedCubePushforward_simplexChain {n m : ℕ} (c : SingularCube X n)
    (t : (TopCat.toSSet.obj (cubeModel.{v} n)) _⦋m⦌) (r : ULift.{v} ℤ)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    twistedCubePushforward L c m (simplexChain t r) a =
      r.down • ιTwistedChainComplex L m ((TopCat.toSSet.map (cubeToHom c)).app _ t)
        (L.map ((cubeToHom c).hom.pathClass (cubeModelOrigin n)
          (TopCat.simplexMap t (SimplexCategory.toTopInitialVertex _))) a) :=
  twistedPushforward_simplexChain (L := L) (f := cubeToHom c) (z₀ := cubeModelOrigin n) t r a

/-- The pushforward along a cube is the twisted pushforward along the cube regarded as a map from
the model, from the origin of the model.  This is the defining equation of
`twistedCubePushforward`. -/
theorem twistedCubePushforward_apply {n : ℕ} (c : SingularCube X n) (m : ℕ)
    (y : ((singularChains (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    twistedCubePushforward L c m y a =
      twistedPushforward L (cubeToHom c) (cubeModelOrigin n) m y a :=
  (rfl)

/-- The pushforward along a cube commutes with the boundaries. -/
theorem twistedCubePushforward_d {n : ℕ} (c : SingularCube X n) (m : ℕ)
    (y : ((singularChains (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X (m + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    (twistedChainComplex L).d (m + 1) m (twistedCubePushforward L c (m + 1) y a) =
      twistedCubePushforward L c m
        (((singularChains (ULift.{v} ℤ)).obj (cubeModel.{v} n)).d (m + 1) m y) a :=
  twistedPushforward_d (L := L) (f := cubeToHom c) (z₀ := cubeModelOrigin n) y a

/-- The comparison on a cube with a coefficient. -/
@[simp]
theorem twistedCubicalToSingular_ofCube {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    twistedCubicalToSingular L n (TwistedCubicalChain.ofCube L c a) =
      twistedCubePushforward L c n (cubicalToSingularGen (ULift.{v} ℤ) n) a :=
  TwistedCubicalChain.desc_ofCube _ c a

/-- **The comparison on a subcube.** The image of a subcube `c ∘ ι` of `c`, with the coefficient
transported inside `c`, is the pushforward along `c` of the image of the subcube `upCube ∘ ι` of
the model. -/
theorem twistedCubicalToSingular_ofSubcube {n m : ℕ} (c : SingularCube X n)
    (ι : C(Fin m → I, Fin n → I)) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    twistedCubicalToSingular L m (TwistedCubicalChain.ofSubcube L c ι a) =
      twistedCubePushforward L c m (cubicalToSingularSubcube (ULift.{v} ℤ) n ι) a := by
  -- the map from the model `Iᵐ` to the model `Iⁿ` underlying the subcube `ι`
  set g : cubeModel.{v} m ⟶ cubeModel.{v} n := cubeToHom ((upCube n).comp ι) with hg
  have hmap : ((singularChains (ULift.{v} ℤ)).map g).f m (cubicalToSingularGen (ULift.{v} ℤ) m) =
      cubicalToSingularSubcube (ULift.{v} ℤ) n ι := by
    have := singularChains_map_cubicalToSingularSubcube (ULift.{v} ℤ) ι
      (ContinuousMap.id (Fin m → I))
    rwa [ContinuousMap.comp_id, cubicalToSingularSubcube_id] at this
  have key := twistedPushforward_map (L := L) (f := cubeToHom c) (z₀ := cubeModelOrigin n) g
    (cubeModelOrigin m) (cubicalToSingularGen (ULift.{v} ℤ) m) a
  rw [hmap] at key
  rw [TwistedCubicalChain.ofSubcube_apply, twistedCubicalToSingular_ofCube]
  -- The transport inside `c` is the transport inside the image of `c ∘ down`, with `down` the
  -- projection of the model; the two maps `cubeToHom` agree by their definitions.
  have hp : pathClass c 0 (ι 0) =
      ((cubeToHom c).hom.pathClass (cubeModelOrigin n) (g (cubeModelOrigin m)) :
        FundamentalGroupoid.mk (c 0) ⟶ FundamentalGroupoid.mk (c (ι 0))) :=
    (pathClass_comp c ⟨ULift.down, continuous_uliftDown⟩ (cubeModelOrigin n)
      (g (cubeModelOrigin m))).symm
  exact (congrArg (fun p : FundamentalGroupoid.mk (c 0) ⟶ FundamentalGroupoid.mk (c (ι 0)) ↦
    twistedPushforward L (cubeToHom (c.comp ι)) (cubeModelOrigin m) m
      (cubicalToSingularGen (ULift.{v} ℤ) m)
      (L.map p a)) hp).trans key.symm

/-- The image of a cube which is a degeneracy `s ∘ π` is zero. -/
private theorem twistedCubePushforward_gen_eq_zero_of_eq_comp {m : ℕ} (s : SingularCube X m)
    (i : Fin (m + 1)) {c : SingularCube X (m + 1)} (hc : c = s.comp (forgetCoordinate i))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    twistedCubePushforward L c (m + 1) (cubicalToSingularGen (ULift.{v} ℤ) (m + 1)) a = 0 := by
  subst hc
  -- the origin of `Iᵐ⁺¹` goes to the origin of `Iᵐ`, so `a` is a coefficient at `s 0`
  have h := twistedCubicalToSingular_ofSubcube (L := L) s (forgetCoordinate i)
    (a : L.obj (FundamentalGroupoid.mk (s 0)))
  have h0 : cubicalToSingularSubcube (ULift.{v} ℤ) m (forgetCoordinate i) = 0 :=
    cubicalToSingularSubcube_eq_zero _
      ((degeneracy_eq_comp (upCube.{v} m) i) ▸ isDegenerate_degeneracy _ _)
  -- The origin goes to the origin, so the transport inside `s` is the identity.
  have hp : pathClass s 0 (forgetCoordinate i 0) = 𝟙 (FundamentalGroupoid.mk (s 0)) :=
    pathClass_self s 0
  have e : TwistedCubicalChain.ofSubcube L s (forgetCoordinate i) a =
      TwistedCubicalChain.ofCube L (s.comp (forgetCoordinate i)) a :=
    (TwistedCubicalChain.ofSubcube_apply s _ a).trans
      ((congrArg (fun p : FundamentalGroupoid.mk (s 0) ⟶ FundamentalGroupoid.mk (s 0) ↦
        TwistedCubicalChain.ofCube L (s.comp (forgetCoordinate i)) (L.map p a)) hp).trans
          -- `L.map (𝟙 _) a` is `a`, up to the identity function
          (by simp; rfl))
  rw [← twistedCubicalToSingular_ofCube, ← e, h, h0, LinearMap.map_zero]
  -- the zero linear map vanishes; the types of `a` agree by definition
  rfl

/-- A degenerate cube goes to zero: it is a degeneracy `s ∘ π` of a cube of lower dimension, and the
corresponding subcube `upCube ∘ π` of the model is degenerate. -/
theorem twistedCubePushforward_gen_eq_zero_of_isDegenerate {n : ℕ} {c : SingularCube X n}
    (hc : IsDegenerate c) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    twistedCubePushforward L c n (cubicalToSingularGen (ULift.{v} ℤ) n) a = 0 := by
  cases n with
  | zero => exact (not_isDegenerate_zero c hc).elim
  | succ m =>
    obtain ⟨i, s, hs⟩ := isDegenerate_iff_exists_eq_degeneracy.1 hc
    exact twistedCubePushforward_gen_eq_zero_of_eq_comp s i
      (hs.trans (degeneracy_eq_comp s i)) a

/-- The comparison commutes with the boundaries. -/
theorem twistedCubicalToSingular_boundary (n : ℕ) (x : L.TwistedCubicalChain (n + 1)) :
    twistedCubicalToSingular L n (TwistedCubicalChain.boundary L n x) =
      (twistedChainComplex L).d (n + 1) n (twistedCubicalToSingular L (n + 1) x) := by
  induction x using TwistedCubicalChain.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ofCube c a =>
    rw [twistedCubicalToSingular_ofCube, twistedCubePushforward_d,
      singularChains_d_cubicalToSingularGen, TwistedCubicalChain.boundary_ofCube]
    simp only [map_sum, map_sub, map_smul, map_zsmul, ULift.smul_def, ULift.pow_down,
      ULift.neg_down, ULift.one_down, twistedCubicalToSingular_ofSubcube, LinearMap.sum_apply,
      LinearMap.sub_apply, LinearMap.smul_apply]

variable (L) in
/-- The comparison from the normalized cubical chains with coefficients in `L` to the simplicial
chains with coefficients in `L`: degenerate cubes go to zero. -/
def normalizedTwistedCubicalToSingular (n : ℕ) :
    L.NormalizedTwistedCubicalChain n →ₗ[R] (twistedChainComplex L).X n :=
  Submodule.liftQ _ (twistedCubicalToSingular L n)
    (TwistedCubicalChain.degenerate_le fun c hc a ↦ by
      rw [LinearMap.mem_ker, twistedCubicalToSingular_ofCube]
      exact twistedCubePushforward_gen_eq_zero_of_isDegenerate hc a)

/-- The comparison on the class of a cube with a coefficient. -/
@[simp]
theorem normalizedTwistedCubicalToSingular_ofCube {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalToSingular L n (NormalizedTwistedCubicalChain.ofCube L c a) =
      twistedCubePushforward L c n (cubicalToSingularGen (ULift.{v} ℤ) n) a := by
  rw [NormalizedTwistedCubicalChain.ofCube_apply, normalizedTwistedCubicalToSingular,
    Submodule.liftQ_apply, twistedCubicalToSingular_ofCube]

variable (L) in
/-- On a point cube, the comparison to simplicial chains is the inclusion of the summand of the
point simplex. -/
theorem normalizedTwistedCubicalToSingular_ofCube_const (x : X)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    normalizedTwistedCubicalToSingular L 0
        (NormalizedTwistedCubicalChain.ofCube L (ContinuousMap.const _ x) a) =
      ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) a := by
  -- The coefficient `a` lies in the fibre at `x`, which is the fibre at the origin of the point
  -- cube only by definition, so the steps are composed as terms rather than rewritten.
  refine (normalizedTwistedCubicalToSingular_ofCube (L := L) (ContinuousMap.const _ x) a).trans
    ((twistedCubePushforward_apply (L := L) (ContinuousMap.const _ x) 0 _ a).trans
      ((congrArg (fun y ↦ twistedPushforward L (cubeToHom (ContinuousMap.const _ x))
        (cubeModelOrigin 0) 0 y a) (cubicalToSingularGen_zero (k := ULift.{v} ℤ))).trans ?_))
  rw [twistedPushforward_simplexChain_one (Z := cubeModel.{v} 0)]
  -- The simplex pushed forward along the point cube is the point simplex, and the transport
  -- from the origin of the model to itself is trivial.
  exact ιTwistedChainComplex_congr L
    ((TopCat.toSSet_map_app_toSSetObj₀Equiv_symm _ _).trans (TopCat.toSSetObj₀Equiv_symm_apply _))
    (map_pathClass_heq (L := L) (cubeToHom (ContinuousMap.const _ x)).hom
      (z := cubeModelOrigin 0) (Subsingleton.elim _ _) a)

variable (L) in
/-- The **comparison chain map** from the normalized cubical chain complex with coefficients in `L`
to the simplicial chain complex with coefficients in `L`. -/
def twistedCubicalToSingularMap :
    L.normalizedTwistedCubicalChainComplex ⟶ twistedChainComplex L :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (normalizedTwistedCubicalToSingular L n)) fun n ↦ by
    refine ModuleCat.hom_ext
      (NormalizedTwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_)
    -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
    have h1 : (ModuleCat.Hom.hom
          (ModuleCat.ofHom (L.normalizedTwistedCubicalToSingular (n + 1)) ≫
            (twistedChainComplex L).d (n + 1) n) ∘ₗ NormalizedTwistedCubicalChain.ofCube L c) a =
        (twistedChainComplex L).d (n + 1) n (normalizedTwistedCubicalToSingular L (n + 1)
          (NormalizedTwistedCubicalChain.ofCube L c a)) := rfl
    have h2 : (ModuleCat.Hom.hom
          (L.normalizedTwistedCubicalChainComplex.d (n + 1) n ≫
            ModuleCat.ofHom (L.normalizedTwistedCubicalToSingular n)) ∘ₗ
          NormalizedTwistedCubicalChain.ofCube L c) a =
        normalizedTwistedCubicalToSingular L n (L.normalizedTwistedCubicalChainComplex.d (n + 1) n
          (NormalizedTwistedCubicalChain.ofCube L c a)) := rfl
    have h3 : (twistedChainComplex L).d (n + 1) n (normalizedTwistedCubicalToSingular L (n + 1)
          (NormalizedTwistedCubicalChain.ofCube L c a)) =
        normalizedTwistedCubicalToSingular L n (L.normalizedTwistedCubicalChainComplex.d (n + 1) n
          (NormalizedTwistedCubicalChain.ofCube L c a)) := by
      rw [normalizedTwistedCubicalChainComplex_d_apply]
      simp only [NormalizedTwistedCubicalChain.ofCube_apply,
        NormalizedTwistedCubicalChain.boundary_mk, normalizedTwistedCubicalToSingular,
        Submodule.liftQ_apply]
      exact (twistedCubicalToSingular_boundary n _).symm
    exact h1.trans (h3.trans h2.symm)

/-- The components of the comparison chain map. -/
@[simp]
theorem twistedCubicalToSingularMap_f (n : ℕ) :
    (twistedCubicalToSingularMap L).f n =
      ModuleCat.ofHom (normalizedTwistedCubicalToSingular L n) := by
  unfold twistedCubicalToSingularMap
  rfl

/-- **Naturality in the space** of the comparison chain map. -/
theorem twistedCubicalToSingularMap_naturality
    {Y : TopCat.{v}} (f : X ⟶ Y) (L : LocalCoefficientSystem.{u, v, v} R Y) :
    normalizedTwistedCubicalChainComplexMap f.hom L ≫ twistedCubicalToSingularMap L =
      twistedCubicalToSingularMap ((pullback f.hom).obj L) ≫ twistedChainComplexMap f L := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext
    (NormalizedTwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_)
  simp only [HomologicalComplex.comp_f, normalizedTwistedCubicalChainComplexMap_f,
    twistedCubicalToSingularMap_f]
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change normalizedTwistedCubicalToSingular L n
      (NormalizedTwistedCubicalChain.map f.hom L n (NormalizedTwistedCubicalChain.ofCube _ c a)) =
    (twistedChainComplexMap f L).f n
      (normalizedTwistedCubicalToSingular ((pullback f.hom).obj L) n
        (NormalizedTwistedCubicalChain.ofCube _ c a))
  rw [NormalizedTwistedCubicalChain.map_ofCube,
    normalizedTwistedCubicalToSingular_ofCube (L := (pullback f.hom).obj L)]
  -- the cube `f ∘ c` is `c` followed by `f`, as a map from the model
  exact (normalizedTwistedCubicalToSingular_ofCube (L := L) (f.hom.comp c) a).trans
    (twistedChainComplexMap_twistedPushforward (f := cubeToHom c) (z₀ := cubeModelOrigin n) L f
      (cubicalToSingularGen (ULift.{v} ℤ) n) a).symm

/-- **Naturality in the local system** of the comparison chain map. -/
theorem twistedCubicalToSingularMap_coefficientMap_naturality
    {K : LocalCoefficientSystem.{u, v, v} R X} (η : L ⟶ K) :
    normalizedTwistedCubicalChainComplexCoefficientMap η ≫ twistedCubicalToSingularMap K =
      twistedCubicalToSingularMap L ≫ twistedChainComplexCoefficientMap η := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext
    (NormalizedTwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_)
  simp only [HomologicalComplex.comp_f, normalizedTwistedCubicalChainComplexCoefficientMap_f,
    twistedCubicalToSingularMap_f]
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change normalizedTwistedCubicalToSingular K n
      (NormalizedTwistedCubicalChain.coefficientMap η n
        (NormalizedTwistedCubicalChain.ofCube _ c a)) =
    (twistedChainComplexCoefficientMap η).f n
      (normalizedTwistedCubicalToSingular L n (NormalizedTwistedCubicalChain.ofCube _ c a))
  rw [NormalizedTwistedCubicalChain.coefficientMap_ofCube,
    normalizedTwistedCubicalToSingular_ofCube, normalizedTwistedCubicalToSingular_ofCube]
  exact (twistedChainComplexCoefficientMap_twistedPushforward (f := cubeToHom c)
    (z₀ := cubeModelOrigin n) η (cubicalToSingularGen (ULift.{v} ℤ) n) a).symm

/-- **Compatibility with pushforwards.** The comparison carries the cubical pushforward of a
chain of a simply connected space `Z` to the simplicial pushforward of the image of the chain. -/
theorem normalizedTwistedCubicalToSingular_pushforward {Z : TopCat.{v}} [SimplyConnectedSpace Z]
    (f : Z ⟶ X) (z₀ : Z) {n : ℕ} (y : NormalizedCubicalChain Z (ULift.{v} ℤ) n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    normalizedTwistedCubicalToSingular L n
        (NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n y a) =
      twistedPushforward L f z₀ n (((cubicalToSingular (ULift.{v} ℤ)).app Z).f n y) a := by
  have h := NormalizedCubicalChain.linearMap_ext (R := ULift.{v} ℤ)
    (f := ((normalizedTwistedCubicalToSingular L n).toAddMonoidHom.toIntLinearMap
      |>.restrictScalars (ULift.{v} ℤ)) ∘ₗ
      ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n)
    (g := ((LinearMap.applyₗ' ℤ a).restrictScalars (ULift.{v} ℤ)) ∘ₗ
      twistedPushforward L f z₀ n ∘ₗ
      (((cubicalToSingular (ULift.{v} ℤ)).app Z).f n).hom) fun d ↦ ?_
  · exact congrArg (fun φ ↦ φ y) h
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.applyₗ'_apply_apply, LinearMap.toAddMonoidHom_coe]
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  change normalizedTwistedCubicalToSingular L n
      (NormalizedTwistedCubicalChain.pushforward L f.hom z₀ n
        (NormalizedCubicalChain.ofCube Z (ULift.{v} ℤ) d) a) =
    twistedPushforward L f z₀ n (((cubicalToSingular (ULift.{v} ℤ)).app Z).f n
      (NormalizedCubicalChain.ofCube Z (ULift.{v} ℤ) d)) a
  rw [NormalizedTwistedCubicalChain.pushforward_ofCube, cubicalToSingular_app_f_ofCube,
    twistedPushforward_map (L := L) (f := f) (z₀ := z₀) (cubeToHom d) (cubeModelOrigin n),
    normalizedTwistedCubicalToSingular_ofCube]
  -- The pushforward along the cube `f ∘ d` is the pushforward along `cubeToHom d ≫ f`, which is
  -- `cubeToHom_comp`; the coefficients' fibres agree only by definition, which blocks `rw`.
  rfl

/-! ### Pushforwards along simplices and cubes -/

section PushforwardsAlongModels

variable (L)

/-- The simplicial pushforward along a simplex `ρ` from the initial vertex of the model, with the
coefficient at the initial vertex of `ρ`. -/
def simplexPushforward {n : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌) (m : ℕ)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex ρ)) : (twistedChainComplex L).X m :=
  twistedPushforward (Z := simplexModel.{v} n) L (simplexToHom ρ)
    (SimplexCategory.toTopInitialVertex ⦋n⦌) m y a

/-- The cubical pushforward along a simplex `ρ` from the initial vertex of the model, with the
coefficient at the initial vertex of `ρ`. -/
def simplexCubicalPushforward {n : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌) (m : ℕ)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex ρ)) : L.NormalizedTwistedCubicalChain m :=
  NormalizedTwistedCubicalChain.pushforward (Z := simplexModel.{v} n) L (simplexToHom ρ).hom
    (SimplexCategory.toTopInitialVertex ⦋n⦌) m y a

/-- The simplicial pushforward along a simplex is the twisted pushforward along the simplex
regarded as a map from the model. -/
theorem simplexPushforward_apply {n : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌) (m : ℕ)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex ρ)) :
    simplexPushforward L ρ m y a =
      twistedPushforward (Z := simplexModel.{v} n) L (simplexToHom ρ)
        (SimplexCategory.toTopInitialVertex ⦋n⦌) m y a :=
  (rfl)

/-- The cubical pushforward along a simplex is the cubical pushforward along the simplex regarded
as a map from the model. -/
theorem simplexCubicalPushforward_apply {n : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌) (m : ℕ)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex ρ)) :
    simplexCubicalPushforward L ρ m y a =
      NormalizedTwistedCubicalChain.pushforward (Z := simplexModel.{v} n) L (simplexToHom ρ).hom
        (SimplexCategory.toTopInitialVertex ⦋n⦌) m y a :=
  (rfl)

/-- The simplicial pushforward along a simplex is additive in the chain. -/
lemma simplexPushforward_add {n m : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y y' : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex ρ)) :
    simplexPushforward L ρ m (y + y') a =
      simplexPushforward L ρ m y a + simplexPushforward L ρ m y' a :=
  -- Evaluating a sum of linear maps is the sum of the evaluations.
  congrArg (fun φ ↦ φ a) (map_add (twistedPushforward (Z := simplexModel.{v} n) L
    (simplexToHom ρ) (SimplexCategory.toTopInitialVertex ⦋n⦌) m) y y')

/-- The simplicial pushforward along a simplex is compatible with differences of chains. -/
lemma simplexPushforward_sub {n m : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y y' : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex ρ)) :
    simplexPushforward L ρ m (y - y') a =
      simplexPushforward L ρ m y a - simplexPushforward L ρ m y' a :=
  -- Evaluating a difference of linear maps is the difference of the evaluations.
  congrArg (fun φ ↦ φ a) (map_sub (twistedPushforward (Z := simplexModel.{v} n) L
    (simplexToHom ρ) (SimplexCategory.toTopInitialVertex ⦋n⦌) m) y y')

/-- The simplicial pushforward along a simplex commutes with the boundaries. -/
lemma d_simplexPushforward {n m : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X (m + 1))
    (a : L.obj (initialVertex ρ)) :
    (twistedChainComplex L).d (m + 1) m (simplexPushforward L ρ (m + 1) y a) =
      simplexPushforward L ρ m
        (((singularChains (ULift.{v} ℤ)).obj (simplexModel.{v} n)).d (m + 1) m y) a :=
  twistedPushforward_d (Z := simplexModel.{v} n) y a

/-- The comparison to simplicial chains carries the cubical pushforward along a simplex to the
simplicial pushforward of the image under the untwisted comparison. -/
lemma normalizedTwistedCubicalToSingular_simplexCubicalPushforward {n m : ℕ}
    (ρ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X m)
    (a : L.obj (initialVertex ρ)) :
    normalizedTwistedCubicalToSingular L m (simplexCubicalPushforward L ρ m y a) =
      simplexPushforward L ρ m
        (((cubicalToSingular (ULift.{v} ℤ)).app (simplexModel.{v} n)).f m y) a :=
  (congrArg (normalizedTwistedCubicalToSingular L m)
    (simplexCubicalPushforward_apply L ρ m y a)).trans
    ((normalizedTwistedCubicalToSingular_pushforward (L := L) (simplexToHom ρ) _ y a).trans
      (simplexPushforward_apply L ρ m _ a).symm)

/-- The cubical pushforward along a simplex commutes with the boundaries. -/
lemma boundary_simplexCubicalPushforward {n m : ℕ} (ρ : (TopCat.toSSet.obj X) _⦋n⦌)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (simplexModel.{v} n)).X (m + 1))
    (a : L.obj (initialVertex ρ)) :
    NormalizedTwistedCubicalChain.boundary L m (simplexCubicalPushforward L ρ (m + 1) y a) =
      simplexCubicalPushforward L ρ m
        (((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (simplexModel.{v} n)).d
          (m + 1) m y) a :=
  (NormalizedTwistedCubicalChain.boundary_pushforward (L := L) (f := (simplexToHom ρ).hom)
    (z₀ := SimplexCategory.toTopInitialVertex _) y a).trans
    (congrArg (fun z ↦ simplexCubicalPushforward L ρ m z a)
      (normalizedCubicalChainComplex_obj_d_apply _ m y).symm)

/-- The cubical pushforward along a cube `c` from the origin of the model, with the coefficient at
the origin of `c`: the cubical counterpart of `twistedCubePushforward`. -/
def cubeCubicalPushforward {n : ℕ} (c : SingularCube X n) (m : ℕ)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) : L.NormalizedTwistedCubicalChain m :=
  NormalizedTwistedCubicalChain.pushforward (Z := cubeModel.{v} n) L (cubeToHom c).hom
    (cubeModelOrigin n) m y a

/-- The cubical pushforward along a cube is the cubical pushforward along the cube regarded as a
map from the model. -/
theorem cubeCubicalPushforward_apply {n : ℕ} (c : SingularCube X n) (m : ℕ)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    cubeCubicalPushforward L c m y a =
      NormalizedTwistedCubicalChain.pushforward (Z := cubeModel.{v} n) L (cubeToHom c).hom
        (cubeModelOrigin n) m y a :=
  (rfl)

/-- The cubical pushforward along a cube is additive in the chain. -/
lemma cubeCubicalPushforward_add {n m : ℕ} (c : SingularCube X n)
    (y y' : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    cubeCubicalPushforward L c m (y + y') a =
      cubeCubicalPushforward L c m y a + cubeCubicalPushforward L c m y' a :=
  -- Evaluating a sum of linear maps is the sum of the evaluations.
  congrArg (fun φ ↦ φ a) (map_add (NormalizedTwistedCubicalChain.pushforward
    (Z := cubeModel.{v} n) L (cubeToHom c).hom (cubeModelOrigin n) m) y y')

/-- The cubical pushforward along a cube is compatible with differences of chains. -/
lemma cubeCubicalPushforward_sub {n m : ℕ} (c : SingularCube X n)
    (y y' : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    cubeCubicalPushforward L c m (y - y') a =
      cubeCubicalPushforward L c m y a - cubeCubicalPushforward L c m y' a :=
  -- Evaluating a difference of linear maps is the difference of the evaluations.
  congrArg (fun φ ↦ φ a) (map_sub (NormalizedTwistedCubicalChain.pushforward
    (Z := cubeModel.{v} n) L (cubeToHom c).hom (cubeModelOrigin n) m) y y')

/-- A cube with a coefficient is the pushforward along itself of the identity cube of the model. -/
lemma ofCube_eq_cubeCubicalPushforward {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    NormalizedTwistedCubicalChain.ofCube L c a =
      cubeCubicalPushforward L c n ((cubicalModelPresentation (ULift.{v} ℤ)).gen n) a := by
  refine Eq.symm ((congrArg (fun y ↦ cubeCubicalPushforward L c n y a)
    (cubicalModelPresentation_gen (ULift.{v} ℤ) n)).trans
    ((cubeCubicalPushforward_apply L c n _ a).trans
      ((NormalizedTwistedCubicalChain.pushforward_ofCube (L := L)
        (f := (cubeToHom c).hom) (z₀ := cubeModelOrigin n) (upCube n) a).trans ?_)))
  -- The path class from the origin of the model to itself is the identity.
  exact congrArg (NormalizedTwistedCubicalChain.ofCube L c)
    (map_pathClass_self_apply (cubeToHom c).hom (cubeModelOrigin n) a)

/-- The cubical pushforward along a cube commutes with the boundaries. -/
lemma boundary_cubeCubicalPushforward {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X (m + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    NormalizedTwistedCubicalChain.boundary L m (cubeCubicalPushforward L c (m + 1) y a) =
      cubeCubicalPushforward L c m
        (((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).d
          (m + 1) m y) a :=
  (NormalizedTwistedCubicalChain.boundary_pushforward (L := L) (f := (cubeToHom c).hom)
    (z₀ := cubeModelOrigin n) y a).trans
    (congrArg (fun z ↦ NormalizedTwistedCubicalChain.pushforward L (cubeToHom c).hom
      (cubeModelOrigin n) m z a) (normalizedCubicalChainComplex_obj_d_apply _ m y).symm)

/-- The cubical pushforward along a cube commutes with the differentials of the normalized cubical
chain complex. -/
lemma d_cubeCubicalPushforward {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X (m + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    L.normalizedTwistedCubicalChainComplex.d (m + 1) m (cubeCubicalPushforward L c (m + 1) y a) =
      cubeCubicalPushforward L c m
        (((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).d
          (m + 1) m y) a :=
  (normalizedTwistedCubicalChainComplex_d_apply L m _).trans
    (boundary_cubeCubicalPushforward L c y a)

/-- The comparison to simplicial chains carries the cubical pushforward along a cube to the
simplicial pushforward of the image under the untwisted comparison. -/
lemma normalizedTwistedCubicalToSingular_cubeCubicalPushforward {n m : ℕ} (c : SingularCube X n)
    (y : ((normalizedCubicalChainComplex (ULift.{v} ℤ)).obj (cubeModel.{v} n)).X m)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalToSingular L m (cubeCubicalPushforward L c m y a) =
      twistedCubePushforward L c m
        (((cubicalToSingular (ULift.{v} ℤ)).app (cubeModel.{v} n)).f m y) a :=
  (normalizedTwistedCubicalToSingular_pushforward (L := L) (cubeToHom c) _ y a).trans
    (twistedCubePushforward_apply c m _ a).symm

end PushforwardsAlongModels

end LocalCoefficientSystem

end TauCeti
