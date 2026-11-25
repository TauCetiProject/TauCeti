/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Basic
public import TauCeti.Topology.VectorBundle.Thom.SignClass

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

The lift of `U` is a Thom class of `E'`, over a compact base and for every commutative ring `R`
(`isThomClass_thomPairSignCohomologyMap_twistedThomClass`), so that a cocycle representing `U`
lifts to a cocycle of `(E', E'₀)` representing a Thom class of `E'` which `δ^*` negates exactly
(`exists_isThomClass_homologyπ_and_cyclesMap_deckThomPairMap_eq_neg`). On
the fibre pair over a point `p` of the cover, `Λ` is in homology the inclusion of the fibre pair of
`E` over `p.proj`, with the coefficients trivialized by the orientation `p.orientation`
(`singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap`). This inclusion
carries the generator of `Hᵣ(E_b, E_b ∖ {0}; R)` attached to `p.orientation`
(`TauCeti.orientedFiberGenerator`) to the fibre class over `b = p.proj` on which `U` takes the value
`1` (`TauCeti.thomPairSignFiberClass_eq_thomPairSignFiberMap`), so the lift of `U` takes the value
`1` on that generator
(`singularKronecker_singularCohomologyMap_thomPairSignCohomologyMap_twistedThomClass`), and by the
universal coefficient theorem for the fibre pair it generates `Hʳ(E_b, E_b ∖ {0}; R)`. At the level
of chains, `Λ` on the fibre pair over `p` is the fibre inclusion of `E` over `p.proj` with the
coefficients trivialized by evaluation at `p.orientation`
(`singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap`). So `(E', E'₀)` has a cocycle
representing a Thom class which `δ^*` negates exactly
(`exists_isThomClass_homologyπ_and_deckThomPairMap_eq_neg`).

The orientations are indexed by a type `ι : Type`, and the base, the fibres and the ring lie in any
common universe.

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
* `singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap`: on the fibre pairs,
  `Λ` is the inclusion of the fibre pair of `E` with the coefficients trivialized by an orientation.
* `isThomClass_thomPairSignCohomologyMap_twistedThomClass`: the lift of the Thom class with
  coefficients in the orientation system is a Thom class of `E'`.
* `exists_isThomClass_homologyπ_and_deckThomPairMap_eq_neg`: a cocycle of `(E', E'₀)` representing
  a Thom class and negated by `δ^*` on the nose.
* `exists_isThomClass_homologyπ_and_cyclesMap_deckThomPairMap_eq_neg`: `E'` has a Thom class
  represented by a cocycle which the lifted deck involution negates.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (Thom classes) and §12 (the orientation double cover and twisted
  coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (homology with
  local coefficients and the local system of a covering space) and Section 4.D (the Thom class).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

universe w

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type}

variable [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (R : Type w) [Ring R]

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
  -- Move `δ_*` past the comparison of constant-coefficient chains with ordinary chains.
  have h1 : TopPair.singularChainComplexMap (deckThomPairMap F E ι) (ModuleCat.of R R) ≫
      (P.twistedChainComplexConstantIso (ModuleCat.of R R)).inv =
      (P.twistedChainComplexConstantIso (ModuleCat.of R R)).inv ≫
        P.twistedChainComplexCoefficientMap (LocalCoefficientSystem.pullbackConstantIso
          (TopPair.Hom.fst (deckThomPairMap F E ι)).hom (ModuleCat.of R R)).inv ≫
        TopPair.twistedChainComplexMap (deckThomPairMap F E ι)
          ((LocalCoefficientSystem.constantFunctor P.fst).obj (ModuleCat.of R R)) := by
    rw [Iso.comp_inv_eq, Category.assoc, Category.assoc,
      TopPair.twistedChainComplexConstantIso_hom_pair_naturality, ← Category.assoc
        (P.twistedChainComplexCoefficientMap _), ← TopPair.twistedChainComplexCoefficientMap_comp,
      Iso.inv_hom_id, TopPair.twistedChainComplexCoefficientMap_id, Category.id_comp,
      Iso.inv_hom_id_assoc]
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
  rw [thomPairSignChainMapAux, ← Category.assoc, h1, Category.assoc, Category.assoc,
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

/-- On the fibre pair over a point `q` of the orientation cover, the trivialization of the
pulled-back orientation system used by `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap`,
read through the covering map, is the trivialization of the fibre pair of `E` over `q.proj` by the
orientation `q.orientation`. -/
private theorem fiberThomPairSignLocalSystemIso_inv_eq (q : VectorBundleOrientationCover F E ι) :
    (LocalCoefficientSystem.pullbackConstantIso (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)).hom
        (ModuleCat.of R R)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)).hom).map
        (pullbackThomPairSignLocalSystemIso F E hι R).inv ≫
      (TopPair.fstPullbackCompIso (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q) (coverThomPairMap F E ι)
        (signSystem F E hι R)).inv ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        (signSystem F E hι R)) (fiberThomPairMap_comp_coverThomPairMap q)) =
    (fiberThomPairSignLocalSystemIso F E R hι q.proj q.orientation).inv := by
  ext v : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
  -- Both sides evaluate at the orientation `q` to `r`.
  apply (liftFiberEquiv hι q
    (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E q.proj v.as)).symm).injective
  refine Eq.trans ?_
    (liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply (R := R) hι q.proj q.orientation
      v r).symm
  simp only [NatTrans.comp_app, LocalCoefficientSystem.pullbackConstantIso_inv_app,
    LocalCoefficientSystem.pullback_map_app, eqToHom_app]
  -- `erw`: the comparison of iterated pull-backs is stated for the pairs with their own instances.
  erw [TopPair.fstPullbackCompIso_inv_app, ModuleCat.id_apply, Category.id_comp]
  -- The fibre inclusion of `E'` over `q` lands over `q`, where the trivialization evaluates.
  have hw : (TopPair.Hom.fst (fiberThomPairMap F
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q) v.as).proj = q := by
    -- `erw`: the fibre inclusion of `E'` is stated with the zero of its fibres read through their
    -- module structure, and the fibre pairs are reached through `TopCat.of`.
    erw [fiberThomPairMap_fst_apply]
  refine (liftFiberEquiv_eqToHom_apply (R := R) hι
    (congrArg (fun g ↦ π F E (TopPair.Hom.fst g v.as)) (fiberThomPairMap_comp_coverThomPairMap q))
    _ hw (proj_proj_eq_proj_coverThomPairMap_fst _) _ _).trans ?_
  exact (liftFiberEquiv_apply hι _ _ _).trans
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply hι R _ r)

/-- On the fibre pair over a point `q` of the orientation cover, the chain map to
orientation-twisted chains induces in homology the inclusion of the fibre pair of `E` over the base
point of `q`, with the coefficients trivialized by the orientation `q.orientation`
(`TauCeti.thomPairSignFiberMap`). -/
theorem singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap
    (q : VectorBundleOrientationCover F E ι) (n : ℕ) :
    TopPair.singularHomologyMap
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)
        (ModuleCat.of R R) n ≫
      HomologicalComplex.homologyMap (thomPairSignChainMap F E hι R) n =
    thomPairSignFiberMap F E R hι q.proj q.orientation n := by
  set fib := fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q
  -- Move the fibre inclusion past the comparison with chains twisted by the constant system.
  have hA : TopPair.singularHomologyMap fib (ModuleCat.of R R) n ≫
      ((thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        ).twistedHomologyConstantIso (ModuleCat.of R R) n).inv =
      (TopPair.twistedHomologyConstantIso _ (ModuleCat.of R R) n).inv ≫
        TopPair.twistedHomologyCoefficientMap _
          (LocalCoefficientSystem.pullbackConstantIso (TopPair.Hom.fst fib).hom
            (ModuleCat.of R R)).inv n ≫
        TopPair.twistedHomologyMap fib _ n := by
    rw [Iso.comp_inv_eq, Category.assoc, Category.assoc,
      TopPair.twistedHomologyConstantIso_hom_pair_naturality,
      ← TopPair.twistedHomologyCoefficientMap_comp_assoc, Iso.inv_hom_id,
      TopPair.twistedHomologyCoefficientMap_id, Category.id_comp, Iso.inv_hom_id_assoc]
  rw [thomPairSignChainMap_def, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    ← TopPair.twistedHomologyConstantIso_inv, reassoc_of% hA]
  -- Compose the fibre inclusion with the covering map: the composite is the fibre inclusion of `E`
  -- over `q.proj`.
  rw [TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyMap_comp_of_comp_eq_assoc fib (coverThomPairMap F E ι)
      (signSystem F E hι R) (fiberThomPairMap_comp_coverThomPairMap q)]
  -- Move the identification of `π^*o(E)` with its written-out form past the fibre inclusion.
  -- `erw`: the fibre pair of `E'` over `q` is the fibre pair of `E` over `q.proj` only up to
  -- unfolding the pull-back bundle.
  erw [TopPair.twistedHomologyMap_comp_twistedHomologyCoefficientMap_eqToHom
      (fiberThomPairMap F E q.proj) _ (thomPairSignLocalSystem_def hι).symm,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  rw [thomPairSignFiberMap_def, ← fiberThomPairSignLocalSystemIso_inv_eq]
  -- Both sides end with the same identification of `π^*o(E)` with its written-out form.
  congr 3

/-- The inverse of the trivialization `TauCeti.fiberThomPairSignIso` of `π^*o(E)` on the fibre pair
over `b` is the inverse of the trivialization of its written-out form, followed by the
identification of the written-out form with `π^*o(E)`. -/
private theorem fiberThomPairSignIso_inv_eq (b : B) (o : Orientation ℝ (E b) ι) :
    (fiberThomPairSignIso F E R hι b o).inv =
      (fiberThomPairSignLocalSystemIso F E R hι b o).inv ≫
        eqToHom (congrArg (LocalCoefficientSystem.pullback
          (TopPair.Hom.fst (fiberThomPairMap F E b)).hom).obj
          (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm) := by
  refine Iso.inv_ext ?_
  rw [fiberThomPairSignIso_hom_eq]
  -- `erw`: the transport is a morphism of local systems on the fibre pair, which is a functor
  -- category only after unfolding `LocalCoefficientSystem`.
  erw [Category.assoc, Iso.hom_inv_id_assoc, eqToHom_map, eqToHom_trans, eqToHom_refl]

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
    (fiberThomPairSignIso F E R hι q.proj q.orientation).inv := by
  rw [fiberThomPairSignIso_inv_eq, ← fiberThomPairSignLocalSystemIso_inv_eq]
  -- `erw`: as in `fiberThomPairSignIso_inv_eq`. Both sides end with transports to the same system.
  erw [Category.assoc, Category.assoc, Category.assoc, eqToHom_map, eqToHom_trans, eqToHom_trans]
  rfl

/-- On the fibre pair over a point `q` of the orientation cover, the chain map
`TauCeti.VectorBundleOrientationCover.thomPairSignChainMap` is the fibre inclusion over `q.proj` in
chains twisted by `π^*o(E)`, with the coefficients on the fibre trivialized by the orientation
`q.orientation` (`TauCeti.fiberThomPairSignIso`). -/
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
          (fiberThomPairSignIso F E R hι q.proj q.orientation).inv ≫
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

variable (k : Type*) [Ring k] [Linear k (ModuleCat.{w} R)] (M : ModuleCat.{w} R)

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

/-- The lift of a cocycle `φ` of `(E, E₀)` with coefficients in the orientation system is `φ`
precomposed with the chain map to orientation-twisted chains. -/
theorem iCycles_cyclesMap_thomPairSignCochainMap {n : ℕ}
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) k M).cycles n) :
    (TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of R R) k M).iCycles n
        (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R k M) n φ) =
      (thomPairSignChainMap F E hι R).f n ≫
        ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) k M).iCycles n φ :=
  (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ _) φ).trans
    (thomPairSignCochainMap_f_apply hι R k M _ _)

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

end TauCeti.VectorBundleOrientationCover

namespace TauCeti.VectorBundleOrientationCover

/-! ### The lift of the Thom class with coefficients in the orientation system -/

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) {R : Type w}
  [CommRing R] [CompactSpace B] (ω : Orientation ℝ F ι)

/-- **The lifted Thom class on a fibre.** The lift to the Thom pair `(E', E'₀)` of the orientation
cover of the Thom class `U` with coefficients in the orientation system, restricted to the fibre
pair over a point `q` of the cover, takes the value `1` on the generator of `Hᵣ(E_b, E_b ∖ {0}; R)`
attached to the orientation `q.orientation` of the fibre `E_b`, `b = q.proj`. -/
theorem singularKronecker_singularCohomologyMap_thomPairSignCohomologyMap_twistedThomClass
    (q : VectorBundleOrientationCover F E ι) :
    (TopPair.singularKronecker _ R (finrank ℝ F)
      (TopPair.singularCohomologyMap
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q)
        (finrank ℝ F) (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
          (twistedThomClass F E R hι ω)))).hom
      (orientedFiberGenerator (E := E) R ω q.orientation) = 1 := by
  rw [TopPair.singularKronecker_naturality, thomPairSignCohomologyMap_def,
    TopPair.singularKronecker_def, thomPairSignCochainMap_def, ChainComplex.kronecker_naturality,
    reassoc_of% singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap,
    ← TopPair.twistedKronecker_def (thomPair F E) (thomPairSignLocalSystem F E R hι)]
  -- The fibre map carries the generator of `q.orientation` to the fibre class over `q.proj`, on
  -- which the Thom class takes the value `1`.
  exact (ModuleCat.comp_apply _ _ _).trans ((congrArg _
    (thomPairSignFiberClass_eq_thomPairSignFiberMap (R := R) hι ω q.proj q.orientation).symm).trans
    (twistedKronecker_twistedThomClass_thomPairSignFiberClass (R := R) hι ω q.proj))

/-- **The lift of the Thom class with coefficients in the orientation system is a Thom class.**
Over a compact base, the lift to the Thom pair `(E', E'₀)` of the pull-back `E'` of `E` to its
orientation double cover of the Thom class `U ∈ Hʳ(E, E₀; π^*o(E), R)`
(`TauCeti.twistedThomClass`) restricts on the fibre over every point `q` of the cover to a
generator of `Hʳ(E_b, E_b ∖ {0}; R)`, `b = q.proj`: it takes the value `1` on the generator of
`Hᵣ(E_b, E_b ∖ {0}; R)` attached to the orientation `q.orientation`. -/
theorem isThomClass_thomPairSignCohomologyMap_twistedThomClass :
    IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
        (twistedThomClass F E R hι ω)) := by
  refine isThomClass_iff.2 ⟨inferInstance, fun q ↦ ?_⟩
  -- A linear trivialization at `q.proj` is a chart of the fibre at `0`, so the universal
  -- coefficient theorem identifies the cohomology of the fibre pair with the dual of its homology.
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) q.proj
  let t := (trivializationAt F E q.proj).continuousLinearEquivAt ℝ q.proj hb
  have : T1Space (E q.proj) := t.toHomeomorph.isEmbedding.t1Space
  have hK : Function.Injective (TopPair.singularKronecker (R := ModuleCat.of R R)
      (M := ModuleCat.of R R) (TopPair.ofSubset (X := TopCat.of (E q.proj)) ({0}ᶜ : Set (E q.proj)))
      R (finrank ℝ F)) := fun x y h ↦
    (singularCohomologyComplSingletonKroneckerEquiv (ModuleCat.of R R) (ModuleCat.of R R)
      t.toHomeomorph.toOpenPartialHomeomorph (x := (0 : E q.proj)) (by simp)
      (finrank ℝ F)).injective
      ((singularCohomologyComplSingletonKroneckerEquiv_apply _ _ _ _ _ x).trans
        (h.trans (singularCohomologyComplSingletonKroneckerEquiv_apply _ _ _ _ _ y).symm))
  have h1 := singularKronecker_singularCohomologyMap_thomPairSignCohomologyMap_twistedThomClass
    (R := R) hι ω q
  -- Every class `d` is the multiple of the lifted class by the value of `d` on the generator.
  refine Submodule.eq_top_iff'.2 fun d ↦ Submodule.mem_span_singleton.2
    ⟨(TopPair.singularKronecker _ R (finrank ℝ F) d).hom
      (orientedFiberGenerator (E := E) R ω q.orientation), hK ?_⟩
  refine ((TopPair.singularKronecker _ R (finrank ℝ F)).map_smul _ _).trans
    (orientedFiberGenerator_hom_ext ω q.orientation ?_)
  -- The scalar multiple of a morphism of modules is evaluated pointwise.
  exact (congrArg (fun r : R ↦ (TopPair.singularKronecker _ R (finrank ℝ F) d).hom
    (orientedFiberGenerator (E := E) R ω q.orientation) • r) h1).trans (mul_one _)


include hι in
/-- **A Thom cocycle of the orientation cover negated by the deck involution.** For a real vector
bundle `E → B` over a compact base and any commutative ring `R`, the Thom pair `(E', E'₀)` of the
pull-back of `E` to its orientation double cover has a relative cocycle `φ` whose class is a Thom
class of `E'` and which the lifted deck involution `δ` negates exactly, at the level of cochains:
`δ^* φ = -φ`. It is the lift of a cocycle representing the Thom class with coefficients in the
orientation system (`TauCeti.twistedThomClass`). -/
theorem exists_isThomClass_homologyπ_and_deckThomPairMap_eq_neg :
    ∃ φ : (TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of R R) R (ModuleCat.of R R)).cycles (finrank ℝ F),
      IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        ((TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of R R) R (ModuleCat.of R R)).homologyπ (finrank ℝ F) φ) ∧
      (TopPair.singularCochainComplexMap (deckThomPairMap F E ι)).f (finrank ℝ F)
          ((TopPair.singularCochainComplex
            (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
            (ModuleCat.of R R) R (ModuleCat.of R R)).iCycles (finrank ℝ F) φ) =
        -(TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of R R) R (ModuleCat.of R R)).iCycles (finrank ℝ F) φ := by
  classical
  -- An orientation of the model fibre normalizes the Thom class with coefficients in `o(E)`.
  let ω : Orientation ℝ F ι :=
    ((Module.finBasis ℝ F).reindex (Fintype.equivFinOfCardEq hι).symm).orientation
  obtain ⟨ψ, hψ⟩ := (ModuleCat.epi_iff_surjective (((thomPair F E).twistedCochainComplex
    (thomPairSignLocalSystem F E R hι) R (ModuleCat.of R R)).homologyπ (finrank ℝ F))).1
    inferInstance (twistedThomClass F E R hι ω)
  refine ⟨HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
    (finrank ℝ F) ψ, ?_, ?_⟩
  · -- The class of the lifted cocycle is the lift of the class of `ψ`.
    have h := congr(ModuleCat.Hom.hom $(HomologicalComplex.homologyπ_naturality
      (thomPairSignCochainMap F E hι R R (ModuleCat.of R R)) (finrank ℝ F)) ψ)
    exact (congrArg (IsThomClass F _) (h.symm.trans (congrArg (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
        (finrank ℝ F))) hψ))).mpr
      (isThomClass_thomPairSignCohomologyMap_twistedThomClass hι ω)
  · -- The lifted cocycle is the lift of `ψ` as a cochain, which `δ^*` negates.
    have h := congr(ModuleCat.Hom.hom $(HomologicalComplex.cyclesMap_i
      (thomPairSignCochainMap F E hι R R (ModuleCat.of R R)) (finrank ℝ F)) ψ)
    have hδ₀ := thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap (F := F)
      (E := E) (ι := ι) hι R R (ModuleCat.of R R)
    have hδ := congr(ModuleCat.Hom.hom ($(hδ₀).f (finrank ℝ F))
      ((((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
        (ModuleCat.of R R)).iCycles (finrank ℝ F)).hom ψ))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    simp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_neg, LinearMap.neg_apply] at hδ
    rw [h]
    exact hδ

variable (R) in
include hι in
/-- **An anti-invariant Thom cocycle of the orientation cover.** Over a compact base, the pull-back
`E'` of a real vector bundle to its orientation double cover has a Thom class, with coefficients in
any commutative ring, represented by a cocycle which the lift of the deck involution negates at the
level of cochains: the lift of a cocycle representing the Thom class with coefficients in the
orientation system. -/
theorem exists_isThomClass_homologyπ_and_cyclesMap_deckThomPairMap_eq_neg :
    ∃ φ : ((thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        ).singularCochainComplex (ModuleCat.of R R) R (ModuleCat.of R R)).cycles (finrank ℝ F),
      IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        ((TopPair.singularCochainComplex _ (ModuleCat.of R R) R (ModuleCat.of R R)).homologyπ
          (finrank ℝ F) φ) ∧
      HomologicalComplex.cyclesMap (TopPair.singularCochainComplexMap (deckThomPairMap F E ι))
        (finrank ℝ F) φ = -φ := by
  classical
  -- An orientation of the model fibre, from a basis indexed by `ι`.
  let ω : Orientation ℝ F ι :=
    ((Module.finBasisOfFinrankEq ℝ F hι.symm).reindex (Fintype.equivFin ι).symm).orientation
  obtain ⟨z, hz⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ _
    (twistedThomClass F E R hι ω)
  refine ⟨HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
    (finrank ℝ F) z, ?_, ?_⟩
  · have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      (thomPairSignCochainMap F E hι R R (ModuleCat.of R R)) (finrank ℝ F)) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hz] at h
    have hU := isThomClass_thomPairSignCohomologyMap_twistedThomClass (E := E) (R := R) hι ω
    rw [thomPairSignCohomologyMap_def] at hU
    exact (congrArg (IsThomClass F _) h).mp hU
  · have hn : HomologicalComplex.cyclesMap (-thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
        (finrank ℝ F) =
        -HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
          (finrank ℝ F) :=
      (HomologicalComplex.cyclesFunctor _ _ (finrank ℝ F)).map_neg
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.cyclesMap_comp,
      thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap, hn]
    -- Application of a morphism of modules is `ConcreteCategory.hom`, which is `ModuleCat.Hom.hom`
    -- by the concrete-category instance of `ModuleCat`, and that commutes with negation.
    exact (LinearMap.congr_fun (ModuleCat.hom_neg _) z).trans (LinearMap.neg_apply _ z)

end TauCeti.VectorBundleOrientationCover
