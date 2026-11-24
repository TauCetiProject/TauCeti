/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.Topology.VectorBundle.Thom.Orientation.Cover
public import TauCeti.Topology.VectorBundle.Thom.SignClass
public import TauCeti.Topology.VectorBundle.Thom.TwistedRankDegreeHomology
import TauCeti.AlgebraicTopology.Cohomology.Local.Linear

/-!
# Chains of the Thom pair of the orientation cover as orientation-twisted chains

Let `E → B` be a real vector bundle of rank `r`, `B'` its orientation double cover, whose points
are the pairs of a point `b` of `B` and an orientation of `E_b`, and `E'` the pull-back of `E` to
`B'`.
The map `q : (E', E'₀) ⟶ (E, E₀)` of Thom pairs (`coverThomPairMap`) is a double cover, and the
deck involution of `B'` lifts to an involution `δ` of `(E', E'₀)` (`deckThomPairMap`) with
`δ ≫ q = q` (`deckThomPairMap_comp_coverThomPairMap`). Unqualified names here are in the namespace
`TauCeti.VectorBundleOrientationCover`.

Let `π^*o(E)` be the orientation local system of `E` pulled back to the total space
(`TauCeti.thomPairSignLocalSystem`), the coefficient system of the Thom class with coefficients in
the orientation system (`TauCeti.twistedThomClass`). Pulled back further along `q` it becomes
trivial, with no orientation of `E` chosen: over a vector `v` of `E'`, the point `v.proj` of the
cover is an orientation of the fibre of `E` containing `v`, and evaluation at it identifies the
fibre of `π^*o(E)` with the ring `R` (`pullbackThomPairSignLocalSystemIso`, the trivialization
`pullbackSignLocalSystemIsoOfLift` along the lift `v ↦ v.proj` of `E' → B` to `B'`). Over `δ v` the
evaluation is at the opposite orientation, so it changes sign.

This gives a chain map from the relative singular chains of `(E', E'₀)` with coefficients in `R`
to the relative chains `Λ` of `(E, E₀)` twisted by `π^*o(E)` (`thomPairSignChainMap`): a relative
simplex `σ` of `E'` with coefficient `r` goes to the simplex `q ∘ σ` with the coefficient of `o(E)`
taking the value `r` at the orientation `σ(0).proj` and `-r` at the opposite one. This is
antisymmetrization from the permutation local system of the double cover `q` to its sign local
system, read on the Thom pairs and with `π^*o(E)` in place of the sign local system (compare the
absolute `IsCoveringMap.singularChainComplexPermutationIso` and
`IsCoveringMap.permutationLocalSystemToSign`). The lifted involution reverses it on the nose, at the
level of chains: `δ_* ≫ Λ = -Λ`
(`singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMap`).

Dually, applying `Hom(-, M)` lifts the relative cochains of `(E, E₀)` twisted by `π^*o(E)` to the
relative singular cochains of `(E', E'₀)` (`thomPairSignCochainMap`), and `δ^*` acts by `-1` on
every lifted cochain
(`thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap`), hence on the lifted
cohomology classes
(`thomPairSignCohomologyMap_comp_singularCohomologyMap_deckThomPairMap`). In particular every
cocycle representing the Thom class `U ∈ Hʳ(E, E₀; π^*o(E), R)` lifts to a cocycle of `(E', E'₀)`
which `δ^*` negates exactly, not only up to a coboundary. Equivariance at the level of cochains is
what an equivariant cap product chain map on `(E', E'₀)` needs, in the descent of the oriented Thom
isomorphism of `E'` to the Thom isomorphism of `E` with coefficients in its orientation system;
anti-invariance of a cohomology class alone does not provide a cocycle with this property.

The lifted Thom class is a Thom class of `E'`, with coefficients in any commutative ring `K`,
over a compact base (`isThomClass_thomPairSignCohomologyMap_twistedThomClass`). On the fibre pair
of `E'` over a point `q` of the cover, `Λ` is the fibre inclusion of `E` over `q.proj` with the
coefficients trivialized by evaluation at `q.orientation`
(`singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap`), so it carries the class of
the fibre pair read through a trivialization to the fibre class of `π^*o(E)`
(`TauCeti.thomPairSignFiberClass_eq_twistedHomologyMap`), up to sign. The Kronecker pairing of the
lifted class with that class is therefore `±1`, since `U` takes the value `1` on every fibre class,
and a class of the local cohomology `Hʳ(E'_q, E'_q ∖ {0}; K)` whose pairing with a generator is a
unit generates it (`ContinuousLinearEquiv.span_singularCohomology_compl_zero_eq_top_iff`). So
`(E', E'₀)` has a cocycle representing a Thom class which `δ^*` negates exactly
(`exists_isThomClass_homologyπ_and_deckThomPairMap_eq_neg`).

The lift of the deck involution is stated for an index type `ι : Type` of the orientations, and
`TauCeti.thomPairSignLocalSystem` needs the base, the fibres and the ring in the universe of `ι`,
so they live in `Type` here.

## Main definitions and results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `pullbackThomPairSignLocalSystemIso`: the trivialization of `π^*o(E)` pulled back to `E'`, by
  evaluation at the tautological orientation.
* `thomPairSignChainMap`: the chain map `C(E', E'₀; R) ⟶ C(E, E₀; π^*o(E))`.
* `singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMap`: the lifted deck involution
  negates it.
* `thomPairSignCochainMap` and `thomPairSignCohomologyMap`: the lift of twisted cochains and of
  twisted cohomology to the Thom pair of `E'`, negated by the lifted deck involution.
* `singularKronecker_thomPairSignCohomologyMap`: evaluating a lifted class is evaluating the class
  after `Λ`.
* `singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap`: `Λ` on the fibre pair over a
  point `q` of the cover.
* `isThomClass_thomPairSignCohomologyMap_twistedThomClass`: the lift of the Thom class with
  coefficients in the orientation system is a Thom class of `E'`.
* `exists_isThomClass_homologyπ_and_deckThomPairMap_eq_neg`: a cocycle of `(E', E'₀)` representing
  a Thom class and negated by `δ^*` on the nose.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom class) and §12 (the orientation double cover and twisted
  coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (homology with
  local coefficients and the local system of a covering space) and Section 4.D (the Thom class).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type}

variable [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (R : Type) [Ring R]

variable (F E) in
/-- **The orientation system is trivial on the Thom pair of the orientation cover.** The pull-back
of `π^*o(E)` (`TauCeti.thomPairSignLocalSystem`, written out as a pull-back) along
`(E', E'₀) ⟶ (E, E₀)` is trivialized by evaluating, over a vector `v` of `E'`, at the
orientation `v.proj` of the fibre of `E` containing `v`: it is
`TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIsoOfLift` for the lift `v ↦ v.proj`
of the projection of `q` to the base. -/
def pullbackThomPairSignLocalSystemIso :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (coverThomPairMap F E ι)).hom).obj
        ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)) ≅
      (LocalCoefficientSystem.constantFunctor _).obj (ModuleCat.of R R) :=
  ((LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst (coverThomPairMap F E ι)).hom
      (Y := TopCat.of (TotalSpace F E)) (Z := TopCat.of B)
      ⟨π F E, FiberBundle.continuous_proj F E⟩).app (signLocalSystem F E R hι)).symm ≪≫
    pullbackSignLocalSystemIsoOfLift R hι _ ⟨TotalSpace.proj, Pullback.continuous_proj F E _⟩
      proj_proj_eq_proj_coverThomPairMap_fst

/-- Over a vector `v` of `E'`, the trivialization evaluates at the orientation `v.proj`. -/
@[simp]
theorem pullbackThomPairSignLocalSystemIso_hom_app_apply
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
    (f : (signLocalSystem F E R hι).obj
      (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj)) :
    (ModuleCat.Hom.hom (B := ModuleCat.of R R)
        ((pullbackThomPairSignLocalSystemIso F E hι R).hom.app (FundamentalGroupoid.mk v))) f =
      (signLocalSystemObjEquiv hι
          (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj) f :
        (proj ⁻¹' {(TopPair.Hom.fst (coverThomPairMap F E ι) v).proj} :
          Set (VectorBundleOrientationCover F E ι)) → R)
        ⟨v.proj, proj_proj_eq_proj_coverThomPairMap_fst v⟩ := by
  -- The component of the comparison of iterated pull-backs is the identity.
  have h := LocalCoefficientSystem.pullbackCompIso_inv_app_app (R := R)
    (TopPair.Hom.fst (coverThomPairMap F E ι)).hom (Y := TopCat.of (TotalSpace F E))
    (Z := TopCat.of B) ⟨π F E, FiberBundle.continuous_proj F E⟩ (signLocalSystem F E R hι)
    (FundamentalGroupoid.mk v)
  refine Eq.trans ?_ (pullbackSignLocalSystemIsoOfLift_hom_app_apply hι
    (g := (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
      (TopPair.Hom.fst (coverThomPairMap F E ι)).hom)
    (s := ⟨TotalSpace.proj, Pullback.continuous_proj F E _⟩)
    proj_proj_eq_proj_coverThomPairMap_fst v f)
  exact congrArg (ModuleCat.Hom.hom _) (congrArg (fun φ ↦ ModuleCat.Hom.hom φ f) h)

/-- Over a vector `v` of `E'`, the inverse of the trivialization sends `r` to the element of the
fibre of `o(E)` whose value at the orientation `v.proj` is `r`. -/
-- Not `@[simp]`: simp rewrites the coercion of the constant fibre on the left-hand side, so the
-- statement is not in simp normal form.
theorem signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) (r : R) :
    (signLocalSystemObjEquiv hι
        (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj)
        (((pullbackThomPairSignLocalSystemIso F E hι R).inv.app (FundamentalGroupoid.mk v)) r) :
        (proj ⁻¹' {(TopPair.Hom.fst (coverThomPairMap F E ι) v).proj} :
          Set (VectorBundleOrientationCover F E ι)) → R)
      ⟨v.proj, proj_proj_eq_proj_coverThomPairMap_fst v⟩ = r :=
  (pullbackThomPairSignLocalSystemIso_hom_app_apply hι R v _).symm.trans
    (congrArg (fun φ ↦ ModuleCat.Hom.hom φ r)
      ((pullbackThomPairSignLocalSystemIso F E hι R).inv_hom_id_app (FundamentalGroupoid.mk v)))

/-- Over the image of a vector `v` of `E'` under the lift of the deck involution, the inverse of the
trivialization sends `r` to the element of the fibre of `o(E)` whose value at the orientation
`v.proj` is `-r`: the image lies over the opposite orientation. -/
theorem signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply_deckThomPairMap
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) (r : R) :
    (signLocalSystemObjEquiv hι (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι)
          (TopPair.Hom.fst (deckThomPairMap F E ι) v)).proj)
        (((pullbackThomPairSignLocalSystemIso F E hι R).inv.app
          (FundamentalGroupoid.mk (TopPair.Hom.fst (deckThomPairMap F E ι) v))) r) :
        (proj ⁻¹' {(TopPair.Hom.fst (coverThomPairMap F E ι)
          (TopPair.Hom.fst (deckThomPairMap F E ι) v)).proj} :
          Set (VectorBundleOrientationCover F E ι)) → R)
      ⟨v.proj, (proj_proj_eq_proj_coverThomPairMap_fst v).trans
        (congrArg TotalSpace.proj (coverThomPairMap_fst_deckThomPairMap_fst v)).symm⟩ = -r := by
  set w := TopPair.Hom.fst (deckThomPairMap F E ι) v
  -- The orientation `v.proj` is the image of `w.proj` under the deck involution.
  have hv : v.proj = deck w.proj :=
    (deck_deck v.proj).symm.trans (congrArg (fun x ↦ deck x) (deckThomPairMap_fst_proj v)).symm
  refine (liftFiberEquiv_apply hι v.proj _ _).symm.trans ?_
  simp only [hv]
  exact (liftFiberEquiv_deck hι w.proj (proj_proj_eq_proj_coverThomPairMap_fst w) _ _).trans
    (congrArg Neg.neg ((liftFiberEquiv_apply hι _ _ _).trans
      (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply hι R w r)))

variable (F E) in
/-- The orientation local system `π^*o(E)` of `E` pulled back to its total space, written out as a
pull-back (`TauCeti.thomPairSignLocalSystem_def`). -/
private abbrev signSystem : LocalCoefficientSystem R (TopCat.of (TotalSpace F E)) :=
  (LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
    ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)

/-- The chain map `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap`, with the
orientation system `π^*o(E)` written out as a pull-back. -/
private def thomPairSignChainMapAux :
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).singularChainComplex
        (ModuleCat.of R R) ⟶
      (thomPair F E).twistedChainComplex (signSystem F E hι R) :=
  ((thomPair F _).twistedChainComplexConstantIso (ModuleCat.of R R)).inv ≫
    (thomPair F _).twistedChainComplexCoefficientMap
      (pullbackThomPairSignLocalSystemIso F E hι R).inv ≫
    TopPair.twistedChainComplexMap (coverThomPairMap F E ι) (signSystem F E hι R)

variable (F E) in
/-- **The chain map from the Thom pair of the orientation cover to orientation-twisted chains.**
It sends the relative singular chains `C(E', E'₀; R)` to the relative chains of `(E, E₀)` twisted by
`π^*o(E)`: a simplex `σ` of `E'` with coefficient `r` goes to `q ∘ σ` with the coefficient of `o(E)`
whose value at the orientation `σ(0).proj` is `r`. -/
def thomPairSignChainMap :
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).singularChainComplex
        (ModuleCat.of R R) ⟶
      (thomPair F E).twistedChainComplex (thomPairSignLocalSystem F E R hι) :=
  thomPairSignChainMapAux hι R ≫ (thomPair F E).twistedChainComplexCoefficientMap
    (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)

/-- The chain map `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap` is the comparison of
`C(E', E'₀; R)` with chains twisted by the constant system, followed by the inverse of the
trivialization `pullbackThomPairSignLocalSystemIso`, the push-forward along `q`, and the
identification of the pulled-back orientation system with `π^*o(E)`
(`TauCeti.thomPairSignLocalSystem_def`). -/
theorem thomPairSignChainMap_def :
    thomPairSignChainMap F E hι R =
      ((thomPair F _).twistedChainComplexConstantIso (ModuleCat.of R R)).inv ≫
        (thomPair F _).twistedChainComplexCoefficientMap
          (pullbackThomPairSignLocalSystemIso F E hι R).inv ≫
        TopPair.twistedChainComplexMap (coverThomPairMap F E ι)
          ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
            ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)) ≫
        (thomPair F E).twistedChainComplexCoefficientMap
          (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm) := by
  rw [thomPairSignChainMap, thomPairSignChainMapAux, Category.assoc, Category.assoc]

/-- The trivializations of the pulled-back orientation system at `v` and at `δ v` differ by sign,
read on the coefficient systems through the identification of `δ ≫ q` with `q`. -/
private theorem pullbackThomPairSignLocalSystemIso_inv_deckThomPairMap :
    (LocalCoefficientSystem.pullbackConstantIso
        (TopPair.Hom.fst (deckThomPairMap F E ι)).hom (ModuleCat.of R R)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (deckThomPairMap F E ι)).hom).map
        (pullbackThomPairSignLocalSystemIso F E hι R).inv ≫
      (TopPair.fstPullbackCompIso (deckThomPairMap F E ι) (coverThomPairMap F E ι)
        (signSystem F E hι R)).inv ≫
      eqToHom (congrArg (fun g : (thomPair F ((projection : C(VectorBundleOrientationCover F E ι,
          B)) *ᵖ E)).fst ⟶ (thomPair F E).fst ↦ (LocalCoefficientSystem.pullback g.hom).obj
        (signSystem F E hι R))
        (congrArg TopPair.Hom.fst (deckThomPairMap_comp_coverThomPairMap F E ι))) =
      -(pullbackThomPairSignLocalSystemIso F E hι R).inv := by
  refine NatTrans.ext (funext fun ⟨v⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun (r : R) ↦ ?_))
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    LocalCoefficientSystem.pullbackConstantIso_inv_app]
  -- `erw`: the composite comparison is stated for the pairs with their own instances.
  erw [TopPair.fstPullbackCompIso_inv_app]
  simp only [eqToHom_app]
  -- The remaining components are identities and a transport between equal base points, so the
  -- left side is the component of the inverse of the trivialization at `δ v`; compare both sides
  -- by their values at `v.proj`.
  refine (liftFiberEquiv (R := R) hι v.proj (proj_proj_eq_proj_coverThomPairMap_fst v)).injective
    ((liftFiberEquiv_apply hι _ _ _).trans
    (((signLocalSystemObjEquiv_eqToHom_apply hι
      (congrArg TotalSpace.proj (coverThomPairMap_fst_deckThomPairMap_fst v)) _ v.proj _ _).trans
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply_deckThomPairMap hι
      R v r)).trans ?_))
  -- The component of `-ψ` at `v` is `-(ψ.app v)` by definition of the negation of natural
  -- transformations, through which `map_neg` applies.
  exact (congrArg Neg.neg ((liftFiberEquiv_apply hι _ _ _).trans
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply hι R v r))).symm.trans
    (map_neg (liftFiberEquiv hι _ _) _).symm

private theorem singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMapAux :
    TopPair.singularChainComplexMap (deckThomPairMap F E ι) (ModuleCat.of R R) ≫
        thomPairSignChainMapAux hι R = -thomPairSignChainMapAux hι R := by
  set P := thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
  -- Since `δ ≫ q = q`, the twisted chain maps of `δ` and of `q` compose to that of `q`, up to the
  -- comparison of the coefficient systems.
  have h2 : TopPair.twistedChainComplexMap (deckThomPairMap F E ι)
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (coverThomPairMap F E ι)).hom).obj
          (signSystem F E hι R)) ≫
      TopPair.twistedChainComplexMap (coverThomPairMap F E ι) (signSystem F E hι R) =
      P.twistedChainComplexCoefficientMap ((TopPair.fstPullbackCompIso (deckThomPairMap F E ι)
        (coverThomPairMap F E ι) (signSystem F E hι R)).inv ≫
        eqToHom (congrArg (fun g : P.fst ⟶ (thomPair F E).fst ↦
          (LocalCoefficientSystem.pullback g.hom).obj (signSystem F E hι R))
          (congrArg TopPair.Hom.fst (deckThomPairMap_comp_coverThomPairMap F E ι)))) ≫
      TopPair.twistedChainComplexMap (coverThomPairMap F E ι) (signSystem F E hι R) := by
    have h3 := (TopPair.twistedChainComplexMap_congr (f := deckThomPairMap F E ι ≫
      coverThomPairMap F E ι) (signSystem F E hι R)
      (congrArg TopPair.Hom.fst (deckThomPairMap_comp_coverThomPairMap F E ι))).symm.trans
      (TopPair.twistedChainComplexMap_comp (deckThomPairMap F E ι) (coverThomPairMap F E ι)
        (signSystem F E hι R))
    rw [TopPair.twistedChainComplexCoefficientMap_comp_assoc, h3,
      ← TopPair.twistedChainComplexCoefficientMap_comp_assoc, Iso.inv_hom_id,
      TopPair.twistedChainComplexCoefficientMap_id, Category.id_comp]
  -- Move `δ_*` past the comparison of constant-coefficient chains with ordinary chains.
  rw [thomPairSignChainMapAux, ← Category.assoc,
    TopPair.twistedChainComplexConstantIso_inv_pair_naturality, Category.assoc, Category.assoc,
    ← Category.assoc (TopPair.twistedChainComplexMap (deckThomPairMap F E ι) _),
    TopPair.twistedChainComplexMap_naturality, Category.assoc, h2,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc, Category.assoc,
    pullbackThomPairSignLocalSystemIso_inv_deckThomPairMap,
    TopPair.twistedChainComplexCoefficientMap_neg, Preadditive.neg_comp, Preadditive.comp_neg]

/-- **The lifted deck involution negates the chain map to orientation-twisted chains**, at the
level of chains: `δ_* ≫ Λ = -Λ`. -/
theorem singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMap :
    TopPair.singularChainComplexMap (deckThomPairMap F E ι) (ModuleCat.of R R) ≫
        thomPairSignChainMap F E hι R = -thomPairSignChainMap F E hι R := by
  rw [thomPairSignChainMap, ← Category.assoc,
    singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMapAux, Preadditive.neg_comp]

variable (k : Type*) [Ring k] [Linear k (ModuleCat.{0} R)] (M : ModuleCat.{0} R)

variable (F E) in
/-- **The lift of orientation-twisted cochains to the Thom pair of the orientation cover**:
`Hom(-, M)` applied to `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap`, from the
relative cochains of `(E, E₀)` twisted by `π^*o(E)` to the relative singular cochains of
`(E', E'₀)`. -/
def thomPairSignCochainMap :
    (thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) k M ⟶
      TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of R R) k M :=
  (ChainComplex.linearYonedaFunctor k M).map (thomPairSignChainMap F E hι R).op

/-- The cochain map `TauCeti.VectorBundleOrientationCover.thomPairSignCochainMap` is `Hom(-, M)`
applied to the chain map `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap`. -/
theorem thomPairSignCochainMap_def :
    thomPairSignCochainMap F E hι R k M =
      (ChainComplex.linearYonedaFunctor k M).map (thomPairSignChainMap F E hι R).op := (rfl)

/-- In degree `n`, the lift of an orientation-twisted cochain `φ` is `φ` precomposed with the
degree-`n` component of `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap`. -/
-- Not `@[simp]`: simp rewrites the coercion of the projection `E' → B` in the type of the
-- left-hand side, so the statement is not in simp normal form.
theorem thomPairSignCochainMap_f_apply (n : ℕ)
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) k M).X n) :
    (thomPairSignCochainMap F E hι R k M).f n φ = (thomPairSignChainMap F E hι R).f n ≫ φ :=
  (rfl)

/-- **Lifted cochains are anti-invariant under the deck involution**: `δ^*` negates every cochain of
`(E', E'₀)` lifted from an orientation-twisted cochain of `(E, E₀)`. -/
theorem thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap :
    thomPairSignCochainMap F E hι R k M ≫
        TopPair.singularCochainComplexMap (deckThomPairMap F E ι) =
      -thomPairSignCochainMap F E hι R k M := by
  rw [thomPairSignCochainMap, TopPair.singularCochainComplexMap]
  -- `Functor.map_comp` as a term: `rw` does not match its composition with the one of cochain
  -- complexes.
  refine ((ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans ?_
  rw [← op_comp, singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMap, op_neg,
    Functor.map_neg]
  -- The two sides agree up to unfolding the instances of the cochain complexes, beyond the
  -- reducible unfolding with which `rw` tries `rfl`.
  rfl

variable (F E) in
/-- The lift of the cohomology of `(E, E₀)` with coefficients in `π^*o(E)` to the singular
cohomology of the Thom pair `(E', E'₀)` of the orientation cover. -/
def thomPairSignCohomologyMap (n : ℕ) :
    (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) k M n ⟶
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).singularCohomology
        (ModuleCat.of R R) k M n :=
  HomologicalComplex.homologyMap (thomPairSignCochainMap F E hι R k M) n

/-- The map `TauCeti.VectorBundleOrientationCover.thomPairSignCohomologyMap` is the map on
cohomology induced by the cochain map
`TauCeti.VectorBundleOrientationCover.thomPairSignCochainMap`. -/
theorem thomPairSignCohomologyMap_def (n : ℕ) :
    thomPairSignCohomologyMap F E hι R k M n =
      HomologicalComplex.homologyMap (thomPairSignCochainMap F E hι R k M) n := (rfl)

/-- The lift of a class of `(E, E₀)` with coefficients in `π^*o(E)` is negated by the lifted deck
involution. -/
theorem thomPairSignCohomologyMap_comp_singularCohomologyMap_deckThomPairMap (n : ℕ) :
    thomPairSignCohomologyMap F E hι R k M n ≫
        TopPair.singularCohomologyMap (deckThomPairMap F E ι) n =
      -thomPairSignCohomologyMap F E hι R k M n := by
  rw [thomPairSignCohomologyMap, TopPair.singularCohomologyMap,
    ← HomologicalComplex.homologyMap_comp,
    thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap,
    HomologicalComplex.homologyMap_neg]

/-- **The lift is adjoint to the chain map on homology**: evaluating the lift to `(E', E'₀)` of a
class with coefficients in `π^*o(E)` on a class of `Hₙ(E', E'₀; R)` is evaluating the class on the
image of that class under `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap`. -/
theorem singularKronecker_thomPairSignCohomologyMap (n : ℕ)
    (α : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) k M n) :
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).singularKronecker
        k n (thomPairSignCohomologyMap F E hι R k M n α) =
      HomologicalComplex.homologyMap (thomPairSignChainMap F E hι R) n ≫
        (thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) k n α := by
  -- `erw`: `π^*o(E)` is a system on the ambient space of `(E, E₀)` only after unfolding the pair.
  erw [TopPair.singularKronecker_def, TopPair.twistedKronecker_def, thomPairSignCohomologyMap_def,
    thomPairSignCochainMap_def]
  exact TauCeti.ChainComplex.kronecker_naturality (thomPairSignChainMap F E hι R) n α

/-! ### The fibres of the chain map to orientation-twisted chains -/

/-- On the fibre pair over a point `q` of the orientation cover, the coefficients of the chain map
`TauCeti.VectorBundleOrientationCover.thomPairSignChainMap` are trivialized by evaluation at the
orientation `q.orientation`. -/
private theorem thomPairSignChainMap_fiber_coefficients (q : VectorBundleOrientationCover F E ι) :
    (LocalCoefficientSystem.pullbackConstantIso
        (TopPair.Hom.fst (fiberThomPairMap F
          ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)).hom
        (ModuleCat.of R R)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)).hom).map
        (pullbackThomPairSignLocalSystemIso F E hι R).inv ≫
      (TopPair.fstPullbackCompIso (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)
        (coverThomPairMap F E ι) (signSystem F E hι R)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q ≫
          coverThomPairMap F E ι)).hom).map
        (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm) ≫
      eqToHom (congrArg (fun g : _ ⟶ thomPair F E ↦ (LocalCoefficientSystem.pullback
        (TopPair.Hom.fst g).hom).obj (thomPairSignLocalSystem F E R hι))
        (fiberThomPairMap_comp_coverThomPairMap q)) =
    (fiberThomPairSignLocalSystemIso F E R hι q.proj q.orientation).inv := by
  have hfg := fiberThomPairMap_comp_coverThomPairMap (F := F) (E := E) (ι := ι) q
  set f := fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q
  refine NatTrans.ext (funext fun ⟨v⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun (r : R) ↦ ?_))
  -- Both sides are determined by their values at the orientation `q.orientation` of `E_{q.proj}`.
  have hv : q.proj = (TopPair.Hom.fst (fiberThomPairMap F E q.proj) v).proj :=
    (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E q.proj v)).symm
  have hD := congrArg (fun L ↦ ((LocalCoefficientSystem.pullback
    (TopPair.Hom.fst (fiberThomPairMap F E q.proj)).hom).obj L).obj (FundamentalGroupoid.mk v))
    (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι)
  apply ((VectorBundleOrientationCover.liftFiberEquiv (R := R) hι q hv).injective.comp
    (eqToIso hD).toLinearEquiv.injective)
  refine (?_ : _ = r).trans (liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply hι q.proj
    q.orientation v hv r).symm
  simp only [NatTrans.comp_app, LocalCoefficientSystem.pullback_map_app,
    LocalCoefficientSystem.pullbackConstantIso_inv_app]
  -- `erw`: `π^*o(E)` is a system on the ambient space of `(E, E₀)` only after unfolding the
  -- pair, so the components of the comparisons of pull-backs are not reached by `rw`.
  erw [TopPair.fstPullbackCompIso_inv_app, Category.id_comp, eqToHom_app, Category.id_comp,
    eqToHom_app]
  -- What remains is evaluation at `q` after transports between fibres of `o(E)` over the points
  -- `q.proj` below `f v` and below `v`.
  have key {X Y Z W : ModuleCat.{0} R} (a : X = Y) (b : Y = Z) (c : Z = W) (x : X) :
      (eqToHom c).hom ((eqToHom b).hom ((eqToHom a).hom x)) =
        (eqToHom (a.trans (b.trans c))).hom x := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← ModuleCat.hom_comp, eqToHom_trans, eqToHom_trans]
  have hw : (TopPair.Hom.fst f v).proj = q :=
    congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q v :)
  have hab : (TopPair.Hom.fst (coverThomPairMap F E ι) (TopPair.Hom.fst f v)).proj =
      (TopPair.Hom.fst (fiberThomPairMap F E q.proj) v).proj :=
    congrArg (fun g : _ ⟶ thomPair F E ↦ (TopPair.Hom.fst g v : TotalSpace F E).proj) hfg
  -- `change`, not `rw`/`simp`: the goal applies `fiberThomPairMap F E q.proj` to `v`, a point of
  -- the fibre pair of `E'` over `q`, which is the fibre pair of `E` over `q.proj` only after
  -- unfolding the pull-back. So the goal is not type-correct at instance transparency:
  -- `rw [Function.comp_apply]` fails and `simp only [Function.comp_apply]` does nothing. `change`
  -- restates it with the transports as the components of `eqToHom`s, applied to the inverse of
  -- the trivialization over `f v`; for the same reason the rest of the proof is in term mode.
  change liftFiberEquiv hι q hv ((eqToHom hD).hom ((eqToHom (C := ModuleCat.{0} R) _).hom
    ((eqToHom (C := ModuleCat.{0} R) _).hom
      (((pullbackThomPairSignLocalSystemIso F E hι R).inv.app _).hom r)))) = r
  refine (congrArg (liftFiberEquiv hι q hv) (key _ _ _ _)).trans ?_
  refine (liftFiberEquiv_eqToHom_apply hι hab _ _ hv _).trans ((LinearEquiv.congr_fun
    (liftFiberEquiv_congr hι hw.symm _
      ((congrArg VectorBundleOrientationCover.proj hw).trans (hv.trans hab.symm))) _).trans
    ((VectorBundleOrientationCover.liftFiberEquiv_apply hι _ _ _).trans
      (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply hι R
        (TopPair.Hom.fst f v) r)))

/-- On the fibre pair over a point `q` of the orientation cover, the chain map
`TauCeti.VectorBundleOrientationCover.thomPairSignChainMap` is the fibre inclusion over `q.proj` in
chains twisted by `π^*o(E)`, with the coefficients on the fibre trivialized by the orientation
`q.orientation` (`TauCeti.fiberThomPairSignLocalSystemIso`). -/
theorem singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap
    (q : VectorBundleOrientationCover F E ι) :
    TopPair.singularChainComplexMap
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)
        (ModuleCat.of R R) ≫ thomPairSignChainMap F E hι R =
      (TopPair.twistedChainComplexConstantIso
          (TopPair.ofSubset (X := TopCat.of (E q.proj)) ({0}ᶜ : Set (E q.proj)))
          (ModuleCat.of R R)).inv ≫
        TopPair.twistedChainComplexCoefficientMap
          (TopPair.ofSubset (X := TopCat.of (E q.proj)) ({0}ᶜ : Set (E q.proj)))
          (fiberThomPairSignLocalSystemIso F E R hι q.proj q.orientation).inv ≫
        TopPair.twistedChainComplexMap (fiberThomPairMap F E q.proj)
          (thomPairSignLocalSystem F E R hι) := by
  have hfg := fiberThomPairMap_comp_coverThomPairMap (F := F) (E := E) (ι := ι) q
  set f := fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q
  -- Compose the fibre inclusion with `q`.
  have h2 : TopPair.twistedChainComplexMap f
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (coverThomPairMap F E ι)).hom).obj
          (signSystem F E hι R)) ≫
      TopPair.twistedChainComplexMap (coverThomPairMap F E ι) (signSystem F E hι R) =
      TopPair.twistedChainComplexCoefficientMap _ (TopPair.fstPullbackCompIso f
        (coverThomPairMap F E ι) (signSystem F E hι R)).inv ≫
      TopPair.twistedChainComplexMap (f ≫ coverThomPairMap F E ι) (signSystem F E hι R) := by
    have h := TopPair.twistedChainComplexMap_comp f (coverThomPairMap F E ι) (signSystem F E hι R)
    rw [h, ← TopPair.twistedChainComplexCoefficientMap_comp_assoc, Iso.inv_hom_id,
      TopPair.twistedChainComplexCoefficientMap_id, Category.id_comp]
  have h4 := TopPair.twistedChainComplexMap_congr (f := f ≫ coverThomPairMap F E ι)
    (f' := fiberThomPairMap F E q.proj) (thomPairSignLocalSystem F E R hι)
    (congrArg TopPair.Hom.fst hfg)
  have h5 := TopPair.twistedChainComplexMap_naturality (f ≫ coverThomPairMap F E ι)
    (signSystem F E hι R)
    (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)
  -- Move the fibre inclusion past the comparison of constant-coefficient chains with ordinary
  -- chains, then compose it with `q`.
  rw [thomPairSignChainMap_def, TopPair.twistedChainComplexConstantIso_inv_pair_naturality_assoc,
    TopPair.twistedChainComplexMap_naturality_assoc,
    reassoc_of% h2, h5, h4]
  simp only [← TopPair.twistedChainComplexCoefficientMap_comp_assoc]
  congr 3
  exact thomPairSignChainMap_fiber_coefficients hι R q

/-! ### The lifted Thom class is a Thom class -/

section ThomClass

variable [FiniteDimensional ℝ F] {K : Type} [CommRing K]

/-- On the fibre over a point `q` of the orientation cover, the chain map to orientation-twisted
chains sends the class of the fibre pair read through a linear trivialization `e` as the point class
of `1` to the fibre class of `E` over `q.proj` normalized by the orientation that `e` reads off
`q.orientation`. -/
private theorem homologyMap_thomPairSignChainMap_singularHomologyMap_fiberThomPairMap
    (q : VectorBundleOrientationCover F E ι) (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hb : q.proj ∈ e.baseSet) :
    (HomologicalComplex.homologyMap (thomPairSignChainMap F E hι K) (finrank ℝ F)).hom
        ((TopPair.singularHomologyMap
          (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)
          (ModuleCat.of K K) (finrank ℝ F)).hom
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ q.proj hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F)
            (complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K)))) =
      thomPairSignFiberClass F E K hι (e.mapOrientation ι hb q.orientation) q.proj := by
  rw [thomPairSignFiberClass_eq_twistedHomologyMap hι _ e hb, Equiv.symm_apply_apply]
  -- The map on homology of the identification of chain maps on the fibre pair.
  set y := TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ q.proj hb).complZeroPairIso.inv
    (ModuleCat.of K K) (finrank ℝ F)
    (complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K))
  have h := congr(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
    $(singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap hι K q) (finrank ℝ F)) y)
  refine (congrArg (ModuleCat.Hom.hom · y) (HomologicalComplex.homologyMap_comp
    (TopPair.singularChainComplexMap
      (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)
      (ModuleCat.of K K)) (thomPairSignChainMap F E hι K) (finrank ℝ F))).symm.trans
    (h.trans ?_)
  -- The right-hand side is the composite of the three maps on homology, applied to `y`.
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congrArg (ModuleCat.Hom.hom · y) ((HomologicalComplex.homologyMap_comp _ _ _).trans
    (congrArg₂ (· ≫ ·) (TopPair.twistedHomologyConstantIso_inv _ _ _).symm
      (HomologicalComplex.homologyMap_comp _ _ _)))

variable [CompactSpace B]

/-- **The Thom class with coefficients in the orientation system lifts to a Thom class of the
orientation cover.** Let `E → B` be a real vector bundle over a compact base, `B'` its orientation
double cover and `E'` the pull-back of `E` to `B'`. The lift to `(E', E'₀)` of the Thom class
`U ∈ Hʳ(E, E₀; π^*o(E), K)` (`TauCeti.twistedThomClass`) restricts on every fibre to a generator of
`Hʳ(E'_q, E'_q ∖ {0}; K)`: it is a Thom class of `E'`, with coefficients in any commutative ring
`K`. Its lift is negated by the lifted deck involution on the nose, already at the level of cochains
(`thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap`). -/
theorem isThomClass_thomPairSignCohomologyMap_twistedThomClass (ω : Orientation ℝ F ι) :
    IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι K K (ModuleCat.of K K) (finrank ℝ F)
        (twistedThomClass F E K hι ω)) := by
  refine isThomClass_iff.2 ⟨inferInstance, fun q ↦ ?_⟩
  set e := trivializationAt F E q.proj
  have hb : q.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q.proj
  set y := TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ q.proj hb).complZeroPairIso.inv
    (ModuleCat.of K K) (finrank ℝ F)
    (complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K))
  set U := twistedThomClass F E K hι ω
  refine ((e.continuousLinearEquivAt ℝ q.proj hb).span_singularCohomology_compl_zero_eq_top_iff
    (span_complZeroPairPointHom_one F K) _).2 ?_
  -- The Kronecker pairing is the value of `U` on a fibre class, normalized by `ω` or by `-ω`.
  have h₁ := congrArg (ModuleCat.Hom.hom · y) (TopPair.singularKronecker_naturality
    (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q) K
    (finrank ℝ F) (thomPairSignCohomologyMap F E hι K K (ModuleCat.of K K) (finrank ℝ F) U))
  have h₂ := congrArg (ModuleCat.Hom.hom · (TopPair.singularHomologyMap
    (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)
    (ModuleCat.of K K) (finrank ℝ F) y))
    (singularKronecker_thomPairSignCohomologyMap hι K K (ModuleCat.of K K) (finrank ℝ F) U)
  have h₃ := congrArg ((thomPair F E).twistedKronecker (thomPairSignLocalSystem F E K hι) K
    (finrank ℝ F) U).hom
    (homologyMap_thomPairSignChainMap_singularHomologyMap_fiberThomPairMap hι q e hb)
  dsimp only at h₁ h₂
  refine (congrArg IsUnit (h₁.trans (h₂.trans h₃))).mpr ?_
  rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb q.orientation) ω
    (Nat.card_eq_fintype_card.trans hι) with h | h
  · rw [h, twistedKronecker_twistedThomClass_thomPairSignFiberClass]
    exact isUnit_one
  · rw [h, thomPairSignFiberClass_neg, map_neg,
      twistedKronecker_twistedThomClass_thomPairSignFiberClass]
    exact isUnit_one.neg

include hι in
/-- **A Thom cocycle of the orientation cover negated by the deck involution.** For a real vector
bundle `E → B` over a compact base and any commutative ring `K`, the Thom pair `(E', E'₀)` of the
pull-back of `E` to its orientation double cover has a relative cocycle `φ` whose class is a Thom
class of `E'` and which the lifted deck involution `δ` negates exactly, at the level of cochains:
`δ^* φ = -φ`. It is the lift of a cocycle representing the Thom class with coefficients in the
orientation system (`TauCeti.twistedThomClass`). -/
theorem exists_isThomClass_homologyπ_and_deckThomPairMap_eq_neg :
    ∃ φ : (TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of K K) K (ModuleCat.of K K)).cycles (finrank ℝ F),
      IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        ((TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ) ∧
      (TopPair.singularCochainComplexMap (deckThomPairMap F E ι)).f (finrank ℝ F)
          ((TopPair.singularCochainComplex
            (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
            (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles (finrank ℝ F) φ) =
        -(TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles (finrank ℝ F) φ := by
  classical
  -- An orientation of the model fibre normalizes the Thom class with coefficients in `o(E)`.
  let ω : Orientation ℝ F ι :=
    ((Module.finBasis ℝ F).reindex (Fintype.equivFinOfCardEq hι).symm).orientation
  obtain ⟨ψ, hψ⟩ := (ModuleCat.epi_iff_surjective (((thomPair F E).twistedCochainComplex
    (thomPairSignLocalSystem F E K hι) K (ModuleCat.of K K)).homologyπ (finrank ℝ F))).1
    inferInstance (twistedThomClass F E K hι ω)
  refine ⟨HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι K K (ModuleCat.of K K))
    (finrank ℝ F) ψ, ?_, ?_⟩
  · -- The class of the lifted cocycle is the lift of the class of `ψ`.
    have h := congr(ModuleCat.Hom.hom $(HomologicalComplex.homologyπ_naturality
      (thomPairSignCochainMap F E hι K K (ModuleCat.of K K)) (finrank ℝ F)) ψ)
    exact (congrArg (IsThomClass F _) (h.symm.trans (congrArg (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (thomPairSignCochainMap F E hι K K (ModuleCat.of K K))
        (finrank ℝ F))) hψ))).mpr
      (isThomClass_thomPairSignCohomologyMap_twistedThomClass hι ω)
  · -- The lifted cocycle is the lift of `ψ` as a cochain, which `δ^*` negates.
    have h := congr(ModuleCat.Hom.hom $(HomologicalComplex.cyclesMap_i
      (thomPairSignCochainMap F E hι K K (ModuleCat.of K K)) (finrank ℝ F)) ψ)
    have hδ₀ := thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap (F := F)
      (E := E) (ι := ι) hι K K (ModuleCat.of K K)
    have hδ := congr(ModuleCat.Hom.hom ($(hδ₀).f (finrank ℝ F))
      ((((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E K hι) K
        (ModuleCat.of K K)).iCycles (finrank ℝ F)).hom ψ))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    simp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_neg, LinearMap.neg_apply] at hδ
    rw [h]
    exact hδ

end ThomClass

end TauCeti.VectorBundleOrientationCover
