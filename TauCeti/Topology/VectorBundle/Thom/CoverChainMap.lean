/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality
public import TauCeti.Topology.VectorBundle.Thom.OrientationCover
public import TauCeti.Topology.VectorBundle.Thom.TwistedRankDegreeHomology

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
fibre of `π^*o(E)` with the ring `R` (`pullbackThomPairSignLocalSystemIso`). Over `δ v` the
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

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (homology with
  local coefficients and the local system of a covering space).
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

/-- Over a vector `v` of `E'`, evaluation at the orientation `v.proj` on the fibre of `o(E)` over
the image of `v` in the base. -/
private def coverFiberEquiv
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    (signLocalSystem F E R hι).obj
        (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj) ≃ₗ[R] R :=
  signLocalSystemObjEquiv hι _ ≪≫ₗ signFiberEquiv deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h)
    ⟨v.proj, proj_proj_eq_proj_coverThomPairMap_fst v⟩

private theorem coverFiberEquiv_apply
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
    (f : (signLocalSystem F E R hι).obj
      (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj)) :
    coverFiberEquiv hι R v f =
      (signLocalSystemObjEquiv hι
          (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj) f :
        (proj ⁻¹' {(TopPair.Hom.fst (coverThomPairMap F E ι) v).proj} :
          Set (VectorBundleOrientationCover F E ι)) → R)
        ⟨v.proj, proj_proj_eq_proj_coverThomPairMap_fst v⟩ :=
  signFiberEquiv_apply _ _ _ _

variable (F E) in
/-- **The orientation system is trivial on the Thom pair of the orientation cover.** The pull-back
of `π^*o(E)` (`TauCeti.thomPairSignLocalSystem`, written out as a pull-back) along
`(E', E'₀) ⟶ (E, E₀)` is trivialized by evaluating, over a vector `v` of `E'`, at the
orientation `v.proj` of the fibre of `E` containing `v`. -/
def pullbackThomPairSignLocalSystemIso :
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (coverThomPairMap F E ι)).hom).obj
        ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)) ≅
      (LocalCoefficientSystem.constantFunctor _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents (fun v ↦ (coverFiberEquiv hι R v.as).toModuleIso)
    fun {v v'} p ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦ by
      -- The image of `p` in the base, as a morphism of the fundamental groupoid.
      let γ : FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v.as).proj ⟶
          FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v'.as).proj :=
        (p.map (TopPair.Hom.fst (coverThomPairMap F E ι)).hom).map
          ⟨π F E, FiberBundle.continuous_proj F E⟩
      -- The projection `E' ⟶ B'` lifts `γ`, so monodromy in the cover carries `v.proj` to
      -- `v'.proj`.
      have hm := (isCoveringMap_proj (F := F) (E := E) hι).monodromy_map_of_lift
        (g := (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
          (TopPair.Hom.fst (coverThomPairMap F E ι)).hom)
        (Pullback.continuous_proj F E _) proj_proj_eq_proj_coverThomPairMap_fst p
      -- `erw`: the lemma writes the image path as `p.map (π ∘ q)`, which is `γ` by
      -- `Path.Homotopic.Quotient.map_comp`.
      erw [Path.Homotopic.Quotient.map_comp] at hm
      -- `change`: the components are the linear equivalences themselves, and the constant system
      -- transports by the identity.
      change coverFiberEquiv hι R v'.as ((signLocalSystem F E R hι).map γ f) =
        coverFiberEquiv hι R v.as f
      refine (coverFiberEquiv_apply hι R v'.as _).trans
        (.trans ?_ (coverFiberEquiv_apply hι R v.as f).symm)
      rw [← hm]
      exact signLocalSystemObjEquiv_map_apply_monodromy hι γ f _)

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
        ⟨v.proj, proj_proj_eq_proj_coverThomPairMap_fst v⟩ :=
  coverFiberEquiv_apply hι R v f

/-- Over a vector `v` of `E'`, the inverse of the trivialization sends `r` to the element of the
fibre of `o(E)` whose value at the orientation `v.proj` is `r`. -/
-- Not `@[simp]`: simp rewrites the coercion of the constant fibre on the left-hand side, so the
-- statement is not in simp normal form.
theorem signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) (r : R) :
    (signLocalSystemObjEquiv hι
        (FundamentalGroupoid.mk (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj)
        (((pullbackThomPairSignLocalSystemIso F E hι R).inv.app (FundamentalGroupoid.mk v)) r) :
        (proj ⁻¹' {(TopPair.Hom.fst (coverThomPairMap F E ι) v).proj} :
          Set (VectorBundleOrientationCover F E ι)) → R)
      ⟨v.proj, proj_proj_eq_proj_coverThomPairMap_fst v⟩ = r :=
  -- The component of the inverse at `v` is the inverse of `coverFiberEquiv`.
  (coverFiberEquiv_apply hι R v _).symm.trans (LinearEquiv.apply_symm_apply _ r)

/-- Over the image of a vector `v` of `E'` under the lift of the deck involution, the inverse of the
trivialization sends `r` to the element of the fibre of `o(E)` whose value at the orientation
`v.proj` is `-r`: the image lies over the opposite orientation. -/
theorem signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_deckThomPairMap
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
  -- The deck involution carries the point `w.proj` of the fibre to `v.proj`.
  have he : Function.fiberMap _ (funext proj_deck) (TopPair.Hom.fst (coverThomPairMap F E ι) w).proj
      ⟨w.proj, proj_proj_eq_proj_coverThomPairMap_fst w⟩ =
      ⟨v.proj, (proj_proj_eq_proj_coverThomPairMap_fst v).trans
        (congrArg TotalSpace.proj (coverThomPairMap_fst_deckThomPairMap_fst v)).symm⟩ :=
    Subtype.ext ((Function.fiberMap_apply_coe _ _ _ _).trans
      ((congrArg (fun x ↦ deck x) (deckThomPairMap_fst_proj v)).trans (deck_deck v.proj)))
  rw [← he, ← signFiberEquiv_apply deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h),
    signFiberEquiv_fiberMap, signFiberEquiv_apply]
  exact congrArg Neg.neg
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app hι R w r)

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
theorem thomPairSignChainMap_eq :
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
  refine (coverFiberEquiv hι R v).injective ((coverFiberEquiv_apply hι R v _).trans
    (((signLocalSystemObjEquiv_eqToHom_apply hι
      (congrArg TotalSpace.proj (coverThomPairMap_fst_deckThomPairMap_fst v)) _ v.proj _ _).trans
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_deckThomPairMap hι
      R v r)).trans ?_))
  -- The component of `-ψ` at `v` is `-(ψ.app v)` by definition of the negation of natural
  -- transformations, through which `map_neg` applies.
  exact (congrArg Neg.neg ((coverFiberEquiv_apply hι R v _).trans
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app hι R v r))).symm.trans
    (map_neg (coverFiberEquiv hι R v) _).symm

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

variable (k : Type) [Ring k] [Linear k (ModuleCat.{0} R)] (M : ModuleCat.{0} R)

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

end TauCeti.VectorBundleOrientationCover
