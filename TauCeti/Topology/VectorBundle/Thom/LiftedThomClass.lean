/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.Topology.VectorBundle.Thom.CoverChainMap
public import TauCeti.Topology.VectorBundle.Thom.SignClass
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# The Thom class of the orientation cover lifted from the twisted Thom class

Let `E → B` be a real vector bundle of rank `r` over a compact base, `B'` its orientation double
cover and `E'` the pull-back of `E` to `B'`, with the map of Thom pairs `q : (E', E'₀) ⟶ (E, E₀)`
and the lift `δ` of the deck involution (`coverThomPairMap`, `deckThomPairMap`; unqualified names
here are in the namespace `TauCeti.VectorBundleOrientationCover`). Every bundle, orientable or
not, has a Thom class `U ∈ Hʳ(E, E₀; π^*o(E), R)` with coefficients in its orientation system
(`TauCeti.twistedThomClass`), and twisted cochains of `(E, E₀)` lift to cochains of `(E', E'₀)`
that `δ^*` negates on the nose (`thomPairSignCochainMap`).
This file proves that the lift of `U` is a Thom class of `E'`, for every commutative ring `R`
(`isThomClass_thomPairSignCohomologyMap_twistedThomClass`).
So `E'` has a Thom class represented by a cocycle which the lifted deck involution negates
exactly, not only up to a coboundary
(`exists_isThomClass_homologyπ_and_cyclesMap_deckThomPairMap_eq_neg`).
Such a cocycle is what the equivariant cap product with a semi-invariant cocycle
(`TauCeti.quasiIso_singularChainsRepCap_thomPair`) asks for, with `ℤˣ` acting by the deck
involution and the sign character; descending it along the double cover `q` is the route to the
Thom isomorphism `Hₚ₊ᵣ(E, E₀; R) ≅ Hₚ(B; o(E) ⊗ R)` over every commutative ring, `ℤ` included.

## The proof

A class of `Hʳ(E'_p, E'_p ∖ {0}; R)` generates exactly when its Kronecker pairing with a generator
of `Hᵣ(E'_p, E'_p ∖ {0}; R) ≅ R` is a unit, by the universal coefficient theorem for the local
cohomology of a vector space (`TauCeti.span_singleton_eq_top_iff_isUnit_singularKronecker`). The
fibre of `E'` over a point `p` of the cover is the fibre `E_b` of `E` over `b = p.proj`, and on its
fibre pair the chain map `C(E', E'₀; R) ⟶ C(E, E₀; π^*o(E))` underlying the lift is the inclusion
of the fibre pair of `E`, with the coefficients over `E_b` trivialized by evaluation at the
orientation `p` of `E_b`
(`singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap`). So the lift of
`U` pairs the generator of the fibre pair read through a linear trivialization `e` with `U` paired
with the fibre class over `b` normalized by the orientation which `e` reads `p` as
(`TauCeti.thomPairSignFiberClass_eq_twistedHomologyMap`), which is `±1`.

## Main results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap`: the lift on the
  fibre pairs.
* `isThomClass_thomPairSignCohomologyMap_twistedThomClass`: the lift of the twisted Thom class is a
  Thom class of `E'`.
* `exists_isThomClass_homologyπ_and_cyclesMap_deckThomPairMap_eq_neg`: `E'` has a Thom class
  represented by a cocycle negated by the lifted deck involution.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Sections 3.3, 3.H and 4.D.
-/

public section

noncomputable section

open Bundle CategoryTheory Module

namespace TauCeti

namespace VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (R : Type) [Ring R]

/-- Two transports between fibres of the orientation system through an arbitrary module are
invisible to evaluation at a point of the orientation cover. -/
private theorem liftFiberEquiv_eqToHom_comp_eqToHom_comp_apply {x : B}
    (e : VectorBundleOrientationCover F E ι) (hx : e.proj = x) {Z : ModuleCat R}
    (h₂ : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk x) = Z)
    (h₃ : Z = (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk x)) {M : Type}
    [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk x)) (z : M) :
    liftFiberEquiv hι e hx (((eqToHom h₃).hom ∘ₗ (eqToHom h₂).hom ∘ₗ φ) z) =
      liftFiberEquiv hι e hx (φ z) := by
  subst h₂
  rfl

/-- On the fibre pair over a point `p` of the orientation cover, the trivialization of the
orientation system pulled back to `(E', E'₀)` is the trivialization by evaluation at the
orientation `p` of the fibre of `E`. -/
private theorem coefficient_comparison (p : VectorBundleOrientationCover F E ι) :
    (((LocalCoefficientSystem.pullbackConstantIso (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)).hom
          (ModuleCat.of R R)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)).hom).map
          (pullbackThomPairSignLocalSystemIso F E hι R).inv ≫
      (TopPair.fstPullbackCompIso (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) (coverThomPairMap F E ι)
        ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι))).inv) ≫
      eqToHom (congrArg (fun g ↦ (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
        ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)))
        (fiberThomPairMap_comp_coverThomPairMap p))) ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E p.proj)).hom).map
        (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm) =
    (fiberThomPairSignLocalSystemIso F E R hι p.proj p.orientation).inv := by
  -- Compare both sides after the identification of `π^*o(E)` with its defining pull-back, by
  -- evaluation at the orientation `p`.
  refine (cancel_mono ((LocalCoefficientSystem.pullback
    (TopPair.Hom.fst (fiberThomPairMap F E p.proj)).hom).mapIso
      (eqToIso (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι))).hom).1 ?_
  ext v : 2
  have he : p.proj = (TopPair.Hom.fst (fiberThomPairMap F E p.proj) v.as).proj :=
    (congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E p.proj v.as)).symm
  refine ModuleCat.hom_ext (LinearMap.ext_ring ((liftFiberEquiv hι p he).injective ?_))
  refine Eq.trans ?_ (liftFiberEquiv_fiberThomPairSignLocalSystemIso_inv_app_apply hι p.proj
    p.orientation v 1).symm
  -- `erw`: the goal reads the fibre pair of `E'` over `p` and that of `E` over `p.proj`, which
  -- agree only after unfolding the pull-back bundle, so it is not type-correct at the transparency
  -- of `rw`; the rewrites split the components into transports and evaluations.
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, Functor.mapIso_hom, eqToIso.hom,
    eqToHom_map, eqToHom_map, eqToHom_app, eqToHom_app, eqToHom_app]
  have hw : p.proj = (TopPair.Hom.fst (coverThomPairMap F E ι)
      (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) v.as)).proj :=
    he.trans (congrArg TotalSpace.proj (congrFun (congrArg (fun g ↦ ⇑(TopPair.Hom.fst g))
      (fiberThomPairMap_comp_coverThomPairMap p)) v.as)).symm
  simp only [ModuleCat.hom_comp]
  refine (liftFiberEquiv_eqToHom_comp_eqToHom_comp_apply hι R p he _ _ _ _).trans
    ((liftFiberEquiv_eqToHom_apply hι p hw he _ _).trans ?_)
  -- `erw`: as above, the source of `TopPair.fstPullbackCompIso` is read through the fibre pair of
  -- `E'` over `p`, the goal through that of `E` over `p.proj`; both comparisons are identities.
  erw [NatTrans.comp_app, NatTrans.comp_app, TopPair.fstPullbackCompIso_inv_app, Category.comp_id,
    LocalCoefficientSystem.pullbackConstantIso_inv_app, Category.id_comp]
  set w := TopPair.Hom.fst (fiberThomPairMap F
    ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) v.as
  have hp : w.proj = p := congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F
    ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p v.as)
  refine (liftFiberEquiv_apply hι p hw _).trans (Eq.trans ?_
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply hι R w 1))
  have hpt : (⟨p, hw⟩ : (proj ⁻¹' {(TopPair.Hom.fst (coverThomPairMap F E ι) w).proj} :
      Set (VectorBundleOrientationCover F E ι))) =
        ⟨w.proj, proj_proj_eq_proj_coverThomPairMap_fst w⟩ :=
    Subtype.ext hp.symm
  rw [hpt, LocalCoefficientSystem.pullback_map_app]
  -- `rfl`: the image of `v` in the fundamental groupoid of `E'` is `{ as := w }` by definition of
  -- `FundamentalGroupoid.map`.
  rfl

/-- **The chain map to orientation-twisted chains on a fibre pair.** On the fibre pair of `E'` over
a point `p` of the orientation cover, which is the fibre pair `(E_b, E_b ∖ {0})` of `E` over
`b = p.proj`, the chain map `TauCeti.VectorBundleOrientationCover.thomPairSignChainMap` induces in
homology the inclusion of the fibre pair into `(E, E₀)`, with the coefficients `π^*o(E)` over the
fibre trivialized by evaluation at the orientation `p` of `E_b`
(`TauCeti.fiberThomPairSignLocalSystemIso`). -/
theorem singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap
    (p : VectorBundleOrientationCover F E ι) (n : ℕ) :
    TopPair.singularHomologyMap
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
        (ModuleCat.of R R) n ≫
      HomologicalComplex.homologyMap (thomPairSignChainMap F E hι R) n =
    ((TopPair.ofSubset (X := TopCat.of (E p.proj))
        ({0}ᶜ : Set (E p.proj))).twistedHomologyConstantIso (ModuleCat.of R R) n).inv ≫
      (TopPair.ofSubset (X := TopCat.of (E p.proj))
        ({0}ᶜ : Set (E p.proj))).twistedHomologyCoefficientMap
          (fiberThomPairSignLocalSystemIso F E R hι p.proj p.orientation).inv n ≫
      TopPair.twistedHomologyMap (fiberThomPairMap F E p.proj)
        (thomPairSignLocalSystem F E R hι) n := by
  rw [thomPairSignChainMap_def]
  simp only [HomologicalComplex.homologyMap_comp]
  rw [← TopPair.twistedHomologyConstantIso_inv, ← Category.assoc,
    TopPair.singularHomologyMap_comp_twistedHomologyConstantIso_inv, Category.assoc,
    Category.assoc]
  -- The fibre inclusion followed by the covering map of Thom pairs is the fibre inclusion of `E`.
  have hq := TopPair.twistedHomologyMap_comp (fiberThomPairMap F
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) (coverThomPairMap F E ι)
    ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
      ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)) n
  -- `erw`: the fibre pairs of `E'` over `p` and of `E` over `p.proj` agree only up to unfolding
  -- the pull-back bundle.
  erw [TopPair.twistedHomologyMap_congr _
    (congrArg TopPair.Hom.fst (fiberThomPairMap_comp_coverThomPairMap p))] at hq
  rw [TopPair.twistedHomologyMap_naturality_assoc]
  have hq2 := congrArg (fun φ ↦ (TopPair.ofSubset (X := TopCat.of
      (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p))
        ({0}ᶜ : Set _)).twistedHomologyCoefficientMap
      (TopPair.fstPullbackCompIso (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) (coverThomPairMap F E ι)
        ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι))).inv n ≫ φ) hq
  simp only [TopPair.twistedHomologyCoefficientMap_inv_hom_id_assoc] at hq2
  rw [reassoc_of% hq2.symm]
  -- The last coefficient change identifies the pulled-back orientation system with `π^*o(E)`.
  have h4 : TopPair.twistedHomologyMap (fiberThomPairMap F E p.proj)
      ((LocalCoefficientSystem.pullback (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)) n ≫
      HomologicalComplex.homologyMap ((thomPair F E).twistedChainComplexCoefficientMap
        (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)) n =
      (TopPair.ofSubset (X := TopCat.of (E p.proj))
        ({0}ᶜ : Set (E p.proj))).twistedHomologyCoefficientMap
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E p.proj)).hom).map
          (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm)) n ≫
      TopPair.twistedHomologyMap (fiberThomPairMap F E p.proj)
        (thomPairSignLocalSystem F E R hι) n :=
    TopPair.twistedHomologyMap_naturality _ _ _ n
  -- `erw`: `thomPairSignLocalSystem` is a system on the space `TotalSpace F E`, read in the goal on
  -- `(thomPair F E).fst`, which is that space only after unfolding `thomPair`.
  erw [h4]
  simp only [← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 1
  -- `erw`: as for `h4`, the goal still reads `thomPairSignLocalSystem` on `(thomPair F E).fst`, so
  -- it is not type-correct at the transparency of `rw`.
  erw [← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 2
  exact coefficient_comparison hι R p

section ThomClass

variable [CompactSpace B] [FiniteDimensional ℝ F] (R : Type) [CommRing R]

/-- On the fibre pair over a point `p` of the orientation cover, the lift of the Thom class with
coefficients in the orientation system evaluates the class which a linear trivialization `e` at
`p.proj` reads as the point class of `1` as that Thom class evaluates the fibre class normalized by
the orientation `ω'` of the model fibre which `e` reads `p` as. -/
private theorem singularKronecker_singularCohomologyMap_fiberThomPairMap (ω ω' : Orientation ℝ F ι)
    (p : VectorBundleOrientationCover F E ι) (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hb : p.proj ∈ e.baseSet) (ho : p.orientation = (e.mapOrientation ι hb).symm ω') :
    ((TopPair.ofSubset (X := TopCat.of (E p.proj)) ({0}ᶜ : Set (E p.proj))).singularKronecker
      R (finrank ℝ F) (TopPair.singularCohomologyMap (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) (finrank ℝ F)
        (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
          (twistedThomClass F E R hι ω)))).hom
      (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ p.proj hb).complZeroPairIso.inv
        (ModuleCat.of R R) (finrank ℝ F)
        (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl 1)) =
      ((thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) R (finrank ℝ F)
        (twistedThomClass F E R hι ω)).hom (thomPairSignFiberClass F E R hι ω' p.proj) := by
  have h1 := TopPair.singularKronecker_naturality (fiberThomPairMap F
    ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) R (finrank ℝ F)
    (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
      (twistedThomClass F E R hι ω))
  have h2 := TauCeti.ChainComplex.kronecker_naturality (k := R) (Y := ModuleCat.of R R)
    (thomPairSignChainMap F E hι R) (finrank ℝ F) (twistedThomClass F E R hι ω)
  have h3 := singularHomologyMap_fiberThomPairMap_comp_homologyMap_thomPairSignChainMap hι R p
    (finrank ℝ F)
  have h4 := thomPairSignFiberClass_eq_twistedHomologyMap (R := R) hι ω' e hb
  rw [← ho] at h4
  obtain ⟨gen, hgen⟩ : ∃ gen, gen = TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ p.proj hb).complZeroPairIso.inv (ModuleCat.of R R)
      (finrank ℝ F) (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl 1) := ⟨_, rfl⟩
  rw [← hgen] at h4 ⊢
  rw [thomPairSignCohomologyMap_def, thomPairSignCochainMap_def,
    TopPair.singularKronecker_def (thomPair F _)] at h1
  rw [thomPairSignCohomologyMap_def, thomPairSignCochainMap_def]
  -- Naturality of the Kronecker pairing along the fibre inclusion and along the chain map to
  -- twisted chains, which carries the fibre class of `E'` to the fibre class of `E`.
  refine (congrArg (fun φ ↦ φ.hom gen) h1).trans ?_
  refine (congrArg (fun φ ↦ (TopPair.singularHomologyMap (fiberThomPairMap F
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) (ModuleCat.of R R)
        (finrank ℝ F) ≫ φ).hom gen) h2).trans ?_
  refine Eq.trans ?_ (congrArg (fun K ↦ (K (twistedThomClass F E R hι ω)).hom
    (thomPairSignFiberClass F E R hι ω' p.proj))
      (TopPair.twistedKronecker_def (thomPair F E) (thomPairSignLocalSystem F E R hι) R
        (M := ModuleCat.of R R) (finrank ℝ F))).symm
  refine (ConcreteCategory.comp_apply _ _ _).trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  exact congrArg _ ((ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom h3 gen).trans h4.symm))

/-- **The lifted Thom class is a Thom class of the pull-back to the orientation cover.** Let `E'`
be the pull-back of a real vector bundle `E` over a compact base to its orientation double cover.
The lift (`TauCeti.VectorBundleOrientationCover.thomPairSignCohomologyMap`) of the Thom class of
`E` with coefficients in its orientation system (`TauCeti.twistedThomClass`) restricts to a
generator of `Hʳ(E'_p, E'_p ∖ {0}; R)` on every fibre: it is a Thom class of `E'`. -/
theorem isThomClass_thomPairSignCohomologyMap_twistedThomClass (ω : Orientation ℝ F ι) :
    IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
        (twistedThomClass F E R hι ω)) := by
  refine isThomClass_iff.2 ⟨inferInstance, fun p ↦ ?_⟩
  let e := trivializationAt F E p.proj
  have hb : p.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.proj
  -- A class of the fibre pair generates when it pairs with a generator of the local homology to
  -- a unit: the generator read through `e` as the point class of `1`.
  let f := e.continuousLinearEquivAt ℝ p.proj hb
  have : T1Space (E p.proj) := f.toHomeomorph.isEmbedding.t1Space
  have hγ : Submodule.span R {(TopPair.singularHomologyMap f.complZeroPairIso.inv
      (ModuleCat.of R R) (finrank ℝ F)
        (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl 1))} = ⊤ :=
    ((asIso (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl) ≪≫
      TopPair.singularHomologyMapIso _ f.complZeroPairIso.symm _).toLinearEquiv
        ).span_singleton_apply_eq_top_iff.2 (Ideal.span_singleton_one)
  refine (span_singleton_eq_top_iff_isUnit_singularKronecker
    f.toHomeomorph.toOpenPartialHomeomorph (Set.mem_univ 0) hγ _).2 ?_
  -- The trivialization reads the orientation `p` of the fibre as `ω` or as `-ω`.
  obtain ⟨ω', hω', ho⟩ : ∃ ω' : Orientation ℝ F ι, (ω' = ω ∨ ω' = -ω) ∧
      p.orientation = (e.mapOrientation ι hb).symm ω' := by
    rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb p.orientation) ω
      (Nat.card_eq_fintype_card.trans hι) with h | h
    · exact ⟨ω, .inl rfl, (Equiv.eq_symm_apply _).2 h⟩
    · exact ⟨-ω, .inr rfl, (Equiv.eq_symm_apply _).2 h⟩
  refine (congrArg IsUnit
    (singularKronecker_singularCohomologyMap_fiberThomPairMap hι R ω ω' p e hb ho)).mpr ?_
  rcases hω' with rfl | rfl
  · rw [twistedKronecker_twistedThomClass_thomPairSignFiberClass]
    exact isUnit_one
  · rw [thomPairSignFiberClass_neg, map_neg,
      twistedKronecker_twistedThomClass_thomPairSignFiberClass]
    exact isUnit_one.neg

include hι in
/-- **An anti-invariant Thom cocycle of the orientation cover.** The pull-back `E'` of a real
vector bundle over a compact base to its orientation double cover has a Thom class, with
coefficients in any commutative ring, represented by a cocycle which the lift of the deck involution
negates at the level of cochains: the lift of a cocycle representing the Thom class with
coefficients in the orientation system. -/
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
    have hU := isThomClass_thomPairSignCohomologyMap_twistedThomClass (E := E) hι R ω
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

end ThomClass

end VectorBundleOrientationCover

end TauCeti
