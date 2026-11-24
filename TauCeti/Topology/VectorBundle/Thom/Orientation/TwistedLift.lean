/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Thom.CoverChainMap
public import TauCeti.Topology.VectorBundle.Thom.EquivariantCap
public import TauCeti.Topology.VectorBundle.Thom.SignClass
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic

/-!
# The Thom class with orientation-twisted coefficients, lifted to the orientation cover

Let `E → B` be a real vector bundle of rank `r` over a compact base, `B'` its orientation double
cover, whose points are the pairs `p = (b, o)` of a point `b` of `B` and an orientation `o` of
`E_b`, and `E'` the pull-back of `E` to `B'`. The units `ℤˣ` act on `B'`, `-1` reversing the
orientation, and on the Thom pair `(E', E'₀)`, `-1` acting by the lift `δ` of the deck involution
(`neg_one_smul_eq_deckThomPairMap_fst`). Let `R` be any commutative ring, `ℤ` included, and let
`U ∈ Hʳ(E, E₀; π^*o(E), R)` be the Thom class of `E` with coefficients in its orientation system
(`TauCeti.twistedThomClass`). Twisted cochains of `(E, E₀)` lift to cochains of `(E', E'₀)`
(`thomPairSignCochainMap`). This file proves that the lift of `U` is the input of the equivariant
form of the homology Thom isomorphism of `E'` (`TauCeti.quasiIso_singularChainsRepCap_thomPair`),
which is the descent of the oriented Thom isomorphism of `E'` to the Thom isomorphism
`Hₚ₊ᵣ(E, E₀; R) ≅ Hₚ(B; o(E) ⊗ R)` with no orientation of `E` and with no hypothesis on `R`:

* **The lift is a Thom class.** On the fibre over `p = (b, o)`, the class of the fibre pair
  `(E'_p, E'_p ∖ {0}) = (E_b, E_b ∖ {0})` read as the point class by a linear trivialization `e`
  goes, under the chain map to orientation-twisted chains, to the fibre class over `b` normalized
  by the orientation of the model fibre which `e` reads from `o`
  (`homologyMap_thomPairSignChainMap_singularHomologyMap_fiberThomPairMap`). The fibre classes
  normalized by `ω` and by `-ω` are opposite, and `U` takes the value `1` on the first, so the lift
  of `U` takes the value `±1` on the generator of each fibre pair and restricts to a generator of
  its cohomology (`isThomClass_thomPairSignCohomologyMap_twistedThomClass`).
* **Lifted cocycles are semi-invariant.** The lift of any twisted cocycle `φ` is negated by `δ` at
  the level of cochains, so `u ∈ ℤˣ` multiplies it by `u`
  (`isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`). This holds on the nose, not only in
  cohomology, which is what the equivariant cap product needs.
* **The equivariant Thom quasi-isomorphism.** Consequently, for a cocycle `φ` representing `U`, the
  equivariant cap product with the lift of `φ`, `C(E', E'₀; R) ⟶ (R_sign ⊗ C(B'; R))[r]`, is a
  quasi-isomorphism of complexes of representations of `ℤˣ`
  (`quasiIso_singularChainsRepCap_cyclesMap_thomPairSignCochainMap`).

The action of `ℤˣ` on `(E', E'₀)` is free, and `(E, E₀)` is its quotient
(`isQuotientCoveringMap_pullbackThomPairMap_fst`), so the relative chains of `(E', E'₀)` and the
chains of `B'` twisted by the sign representation are complexes of projective representations.
Taking coinvariants of this quasi-isomorphism therefore identifies the relative homology of
`(E, E₀)` with the homology of `B` with coefficients in the local system of the sign
representation (`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`), which is `o(E)`
(`associatedLocalSystemSignIso`). That identification is not carried out here. Over a ring in
which `2` is invertible the twisted Thom isomorphism is proved by a transfer instead
(`thomPairSingularHomologyEquivTwistedHomology`); the argument here needs no such hypothesis.

The lifted cocycles are those of `TauCeti.Topology.VectorBundle.Thom.CoverChainMap`, whose index
type of orientations lies in `Type`, so the base, the fibres and the ring live in `Type` here.

## Main results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap`: on the fibre over `p`, the
  chain map to orientation-twisted chains is the fibre inclusion over the base point of `p`, with
  the coefficients trivialized by the orientation `p`.
* `isThomClass_thomPairSignCohomologyMap_twistedThomClass`: the lift of the twisted Thom class is
  a Thom class of the pulled-back bundle.
* `isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`: lifted cocycles are semi-invariant
  for the sign character of `ℤˣ`.
* `quasiIso_singularChainsRepCap_cyclesMap_thomPairSignCochainMap`: the equivariant cap product
  with the lift of a cocycle representing the twisted Thom class is a quasi-isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (local
  coefficients and the orientation double cover).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (R : Type) [CommRing R]

/-- Evaluation at a point of the orientation cover commutes with the identification of the fibres
of `o(E)` over equal points. -/
private theorem liftFiberEquiv_eqToHom_apply {x y : B} (h : x = y)
    (e : VectorBundleOrientationCover F E ι) (hx : e.proj = x) (hy : e.proj = y)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk x)) :
    liftFiberEquiv hι e hy ((eqToHom (congrArg (fun b ↦ (signLocalSystem F E R hι).obj
      (FundamentalGroupoid.mk b)) h) : _ ⟶ _).hom f) = liftFiberEquiv hι e hx f := by
  subst h
  rfl

/-- On the fibre over a point `p` of the orientation cover, the trivialization of the orientation
system used by `thomPairSignChainMap`, transported to the fibre of `E` below, is the trivialization
by the orientation `p`. -/
private theorem pullbackThomPairSignLocalSystemIso_inv_comp_eq_thomPairSignFiberIso_inv
    (p : VectorBundleOrientationCover F E ι) :
    (((LocalCoefficientSystem.pullbackConstantIso (TopPair.Hom.fst
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)).hom
        (ModuleCat.of R R)).inv ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)).hom).map
        (pullbackThomPairSignLocalSystemIso F E hι R).inv) ≫
      (TopPair.fstPullbackCompIso
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
        (coverThomPairMap F E ι) ((LocalCoefficientSystem.pullback
          (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι))).inv ≫
      eqToHom (congrArg (fun g : _ ⟶ (thomPair F E).fst ↦
        (LocalCoefficientSystem.pullback g.hom).obj ((LocalCoefficientSystem.pullback
          (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι)))
        (congrArg TopPair.Hom.fst (fiberThomPairMap_comp_coverThomPairMap p)))) ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (fiberThomPairMap F E p.proj)).hom).map
        (eqToHom (thomPairSignLocalSystem_def (F := F) (E := E) (R := R) hι).symm) =
      (thomPairSignFiberIso F E R hι p.proj p.orientation).inv := by
  ext v : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
  -- Compare both sides by their values at the orientation `p` of the fibre.
  refine (liftFiberEquiv hι ⟨p.proj, p.orientation⟩
    (fiberThomPairMap_fst_proj (F := F) (E := E) p.proj v.as).symm).injective ?_
  refine Eq.trans ?_ (liftFiberEquiv_thomPairSignFiberIso_inv_app_apply (R := R) hι p.proj
    p.orientation v r).symm
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    LocalCoefficientSystem.pullbackConstantIso_inv_app, TopPair.fstPullbackCompIso_inv_app,
    eqToHom_app, LocalCoefficientSystem.pullback_map_app, LocalCoefficientSystem.pullback_map_app,
    eqToHom_app, Category.id_comp]
  on_goal 2 => rfl
  -- The base points of `v` along the two fibre inclusions agree.
  have H₁ : p.proj = (TopPair.Hom.fst (coverThomPairMap F E ι) (TopPair.Hom.fst (fiberThomPairMap F
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) v.as)).proj :=
    (congrArg proj (fiberThomPairMap_fst_proj (F := F)
      (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p v.as)).symm.trans
        (proj_proj_eq_proj_coverThomPairMap_fst _)
  have H₂ := congrArg (fun g ↦ TotalSpace.proj (TopPair.Hom.fst g v.as : TotalSpace F E))
    (fiberThomPairMap_comp_coverThomPairMap (F := F) (E := E) p)
  erw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    liftFiberEquiv_eqToHom_apply hι R (h := H₂) (hx := H₁.trans rfl),
    liftFiberEquiv_eqToHom_apply hι R (h := rfl) (hx := H₁)]
  -- The vector `v` of the fibre over `p` lies over `p`, at which the trivialization evaluates.
  have hgen : ∀ (e e' : VectorBundleOrientationCover F E ι) (_ : e = e') {x : B}
      (he : e.proj = x) (he' : e'.proj = x) (f : (signLocalSystem F E R hι).obj
        (FundamentalGroupoid.mk x)), liftFiberEquiv hι e he f = liftFiberEquiv hι e' he' f := by
    rintro e _ rfl x he _ f
    rfl
  refine (hgen _ _ (fiberThomPairMap_fst_proj (F := F)
    (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p v.as).symm _
    (proj_proj_eq_proj_coverThomPairMap_fst _) _).trans ?_
  exact (liftFiberEquiv_apply hι _ _ _).trans
    (signLocalSystemObjEquiv_pullbackThomPairSignLocalSystemIso_inv_app_apply hι R
      (TopPair.Hom.fst (fiberThomPairMap F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p) v.as) r)

/-- On the fibre over a point `p` of the orientation cover, the chain map to orientation-twisted
chains is the fibre inclusion over the base point of `p`, with the coefficients trivialized by the
orientation `p`. -/
theorem singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap
    (p : VectorBundleOrientationCover F E ι) :
    TopPair.singularChainComplexMap
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
        (ModuleCat.of R R) ≫ thomPairSignChainMap F E hι R =
      (TopPair.twistedChainComplexConstantIso
          (TopPair.ofSubset (X := TopCat.of
            (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p))
            ({0}ᶜ : Set (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)))
          (ModuleCat.of R R)).inv ≫
        TopPair.twistedChainComplexCoefficientMap
          (TopPair.ofSubset (X := TopCat.of
            (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p))
            ({0}ᶜ : Set (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)))
          (thomPairSignFiberIso F E R hι p.proj p.orientation).inv ≫
        TopPair.twistedChainComplexMap (fiberThomPairMap F E p.proj)
          (thomPairSignLocalSystem F E R hι) := by
  -- Writing `f` for the fibre inclusion of the pull-back and `q` for the covering map of Thom
  -- pairs, `f ≫ q` is the fibre inclusion of `E`.
  have h2 := TopPair.twistedChainComplexMap_comp
    (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
    (coverThomPairMap F E ι) ((LocalCoefficientSystem.pullback
      (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
      ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι))
  have hc := TopPair.twistedChainComplexMap_congr ((LocalCoefficientSystem.pullback
    (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
    ⟨π F E, FiberBundle.continuous_proj F E⟩).obj (signLocalSystem F E R hι))
    (congrArg TopPair.Hom.fst (fiberThomPairMap_comp_coverThomPairMap (F := F) (E := E) p))
  rw [hc] at h2
  rw [thomPairSignChainMap_def, ← Category.assoc,
    TopPair.twistedChainComplexConstantIso_inv_pair_naturality, Category.assoc, Category.assoc,
    ← Category.assoc (TopPair.twistedChainComplexMap _ _),
    TopPair.twistedChainComplexMap_naturality, Category.assoc]
  have h2' := congrArg (TopPair.twistedChainComplexCoefficientMap _
    (TopPair.fstPullbackCompIso _ _ _).inv ≫ ·) h2
  simp only [← TopPair.twistedChainComplexCoefficientMap_comp_assoc, Iso.inv_hom_id,
    TopPair.twistedChainComplexCoefficientMap_id, Category.id_comp] at h2'
  rw [← reassoc_of% h2']
  erw [TopPair.twistedChainComplexMap_naturality,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc]
  congr 3
  exact pullbackThomPairSignLocalSystemIso_inv_comp_eq_thomPairSignFiberIso_inv hι R p

variable [FiniteDimensional ℝ F]

/-- **The fibre generator of the orientation cover maps to a fibre class.** Let `p` be a point of
the orientation cover over `b`, and `e` a linear trivialization at `b`. The class of the fibre pair
over `p` which `e` reads as the point class goes, under the chain map to orientation-twisted chains,
to the fibre class over `b` normalized by the orientation of the model fibre which `e` reads from
the orientation `p` of `E_b`. -/
theorem homologyMap_thomPairSignChainMap_singularHomologyMap_fiberThomPairMap
    (p : VectorBundleOrientationCover F E ι) (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hb : p.proj ∈ e.baseSet) :
    HomologicalComplex.homologyMap (thomPairSignChainMap F E hι R) (finrank ℝ F)
        (TopPair.singularHomologyMap
          (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
          (ModuleCat.of R R) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ p.proj hb).complZeroPairIso.inv
            (ModuleCat.of R R) (finrank ℝ F)
            (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R)))) =
      thomPairSignFiberClass F E R hι (e.mapOrientation ι hb p.orientation) p.proj := by
  rw [thomPairSignFiberClass_eq hι _ e hb, Equiv.symm_apply_apply,
    TopPair.twistedHomologyConstantIso_inv]
  have h := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ (finrank ℝ F))
    (singularChainComplexMap_fiberThomPairMap_comp_thomPairSignChainMap hι R p)
  simp only [HomologicalComplex.homologyMap_comp] at h
  refine (ConcreteCategory.congr_hom (h.trans ((HomologicalComplex.homologyMap_comp _ _ _).trans
    (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ _)))) _).trans ?_
  rfl

/-- The lift of the twisted Thom class, restricted to the fibre over `p`, evaluates on the class of
the fibre pair read as the point class by a linear trivialization `e` as the twisted Thom class
evaluates on the fibre class normalized by the orientation which `e` reads from `p`. -/
private theorem singularKronecker_singularCohomologyMap_thomPairSignCohomologyMap_apply
    [CompactSpace B]
    (ω : Orientation ℝ F ι) (p : VectorBundleOrientationCover F E ι) (e : Trivialization F (π F E))
    [e.IsLinear ℝ] (hb : p.proj ∈ e.baseSet) :
    (TopPair.singularKronecker (R := ModuleCat.of R R) (M := ModuleCat.of R R)
      (TopPair.ofSubset (X := TopCat.of
        (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p))
        ({0}ᶜ : Set (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)))
      R (finrank ℝ F)
      (TopPair.singularCohomologyMap
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
        (finrank ℝ F) (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
          (twistedThomClass F E R hι ω)))).hom
      (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ p.proj hb).complZeroPairIso.inv
        (ModuleCat.of R R) (finrank ℝ F)
        (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R))) =
      ((thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) R (finrank ℝ F)
        (twistedThomClass F E R hι ω)).hom
        (thomPairSignFiberClass F E R hι (e.mapOrientation ι hb p.orientation) p.proj) := by
  -- By naturality of the Kronecker maps, the left side evaluates the twisted Thom class on the
  -- image of the class of the fibre pair, which is the fibre class.
  have key : TopPair.singularKronecker (R := ModuleCat.of R R) (M := ModuleCat.of R R)
      (TopPair.ofSubset (X := TopCat.of
        (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p))
        ({0}ᶜ : Set (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)))
      R (finrank ℝ F)
      (TopPair.singularCohomologyMap
        (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
        (finrank ℝ F) (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
          (twistedThomClass F E R hι ω))) =
      TopPair.singularHomologyMap
          (fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)
          (ModuleCat.of R R) (finrank ℝ F) ≫
        HomologicalComplex.homologyMap (thomPairSignChainMap F E hι R) (finrank ℝ F) ≫
          (thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) R (finrank ℝ F)
            (twistedThomClass F E R hι ω) := by
    rw [TopPair.singularKronecker_naturality, TopPair.singularKronecker_def,
      thomPairSignCohomologyMap_def, thomPairSignCochainMap_def]
    erw [TopPair.twistedKronecker_def]
    exact congrArg (_ ≫ ·) (TauCeti.ChainComplex.kronecker_naturality
      (thomPairSignChainMap F E hι R) (finrank ℝ F) (twistedThomClass F E R hι ω))
  rw [← homologyMap_thomPairSignChainMap_singularHomologyMap_fiberThomPairMap hι R p _ hb]
  exact ConcreteCategory.congr_hom key _

/-- **The lift of the Thom class with orientation-twisted coefficients is a Thom class of the
orientation cover.** Over a compact base, the Thom class `U ∈ Hʳ(E, E₀; π^*o(E), R)` with
coefficients in the orientation system (`TauCeti.twistedThomClass`), lifted to the Thom pair of the
bundle `E'` pulled back to the orientation cover (`thomPairSignCohomologyMap`), restricts to a
generator of `Hʳ(E'_p, E'_p ∖ {0}; R)` on the fibre over every point `p`. -/
theorem isThomClass_thomPairSignCohomologyMap_twistedThomClass [CompactSpace B]
    (ω : Orientation ℝ F ι) :
    IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
        (twistedThomClass F E R hι ω)) := by
  refine isThomClass_iff.2 ⟨inferInstance, fun p ↦ ?_⟩
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) p.proj
  -- The class of the fibre pair over `p` read as the point class by the chosen trivialization.
  let γ := TopPair.singularHomologyMap
    ((trivializationAt F E p.proj).continuousLinearEquivAt ℝ p.proj hb).complZeroPairIso.inv
    (ModuleCat.of R R) (finrank ℝ F)
    (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R))
  -- Evaluation on `γ`.
  let κ := LinearMap.applyₗ (R := R) γ ∘ₗ ModuleCat.homLinearEquiv.toLinearMap ∘ₗ
    TopPair.singularKronecker (R := ModuleCat.of R R) (M := ModuleCat.of R R)
      (TopPair.ofSubset (X := TopCat.of
        (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p))
        ({0}ᶜ : Set (((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) p)))
      R (finrank ℝ F)
  -- The cohomology of the fibre pair is free of rank one.
  let eM := (((TopPair.singularCohomologyFunctor (ModuleCat.of R R) R (ModuleCat.of R R)
      (finrank ℝ F)).mapIso ((trivializationAt F E p.proj).continuousLinearEquivAt ℝ p.proj
        hb).complZeroPairIso.op).toLinearEquiv.symm ≪≫ₗ
    singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of R R)
      (OpenPartialHomeomorph.refl F) (mem_univ 0))
  refine LinearMap.span_singleton_eq_top_of_span_singleton_apply_eq_top κ eM
    (LinearEquiv.refl R R) ?_
  -- `κ` evaluates the twisted Thom class on a fibre class normalized by the orientation of `F`
  -- which the trivialization reads from `p`.
  have hκ := singularKronecker_singularCohomologyMap_thomPairSignCohomologyMap_apply hι R ω p _ hb
  erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, hκ]
  rcases Orientation.eq_or_eq_neg_of_card_eq_finrank
    ((trivializationAt F E p.proj).mapOrientation ι hb p.orientation) ω hι with h | h <;>
    simp only [h, thomPairSignFiberClass_neg, map_neg] <;>
    erw [twistedKronecker_twistedThomClass_thomPairSignFiberClass] <;>
    exact Ideal.span_singleton_eq_top.2 (by simp)

omit [FiniteDimensional ℝ F] in
/-- The lift of a cocycle `φ` of `(E, E₀)` with coefficients in the orientation system is `φ`
precomposed with the chain map to orientation-twisted chains. -/
theorem iCycles_cyclesMap_thomPairSignCochainMap
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R)).cycles (finrank ℝ F)) :
    (TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of R R) R (ModuleCat.of R R)).iCycles (finrank ℝ F)
        (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
          (finrank ℝ F) φ) =
      (thomPairSignChainMap F E hι R).f (finrank ℝ F) ≫
        ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
          (ModuleCat.of R R)).iCycles (finrank ℝ F) φ :=
  (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ _) φ).trans
    (thomPairSignCochainMap_f_apply hι R R (ModuleCat.of R R) _ _)

section SemiInvariant

/-- The action `thomPairFstMulAction` of `ℤˣ` on the total space of the Thom pair of the bundle
pulled back to the orientation cover. -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction

/-- The action `thomPairSndMulAction` of `ℤˣ` on the nonzero vectors of the Thom pair of the bundle
pulled back to the orientation cover. -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
  thomPairSndMulAction

-- The same actions on the Thom pair of `TauCeti.pullbackThomPairMap`, whose fibres read their zeros
-- through `TauCeti.pullbackFiberZero`, as in
-- `TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient`.
attribute [local instance] thomPairFstMulAction thomPairSndMulAction

/-- The unit `-1` acts on the total space of the pulled-back bundle by the lift of the deck
involution. -/
theorem neg_one_smul_eq_deckThomPairMap_fst :
    TopCat.ofHom ⟨((-1 : ℤˣ) • · : (thomPair F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst → _),
      (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
        |>.continuous_const_smul _⟩ =
      TopPair.Hom.fst (deckThomPairMap F E ι) :=
  TopCat.ext fun v ↦ Pullback.totalSpace_ext
    ((neg_one_smul_eq_deck v.proj).trans (deckThomPairMap_fst_proj v).symm)
    ((lift_smul _ v).trans (lift_deckThomPairMap_fst v).symm)

/-- **Lifted cocycles are semi-invariant for the sign character.** A relative cocycle `φ` of
`(E, E₀)` with coefficients in the orientation system lifts to a cocycle of the Thom pair
`(E', E'₀)` of the orientation cover (`thomPairSignCochainMap`) on which the unit `u` of `ℤˣ`
acts by multiplication by `u`: the lifted deck involution negates it at the level of cochains. -/
theorem isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R)).cycles (finrank ℝ F)) :
    have : ContinuousConstSMul ℤˣ
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
      (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
    TopPair.IsSemiInvariantCocycle (P := thomPair F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (Units.map (Int.castRingHom R : ℤ →* R))
      (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
        (finrank ℝ F) φ) := by
  have : ContinuousConstSMul ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
    (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
  refine (TopPair.isSemiInvariantCocycle_iff _ _).2 fun g ↦ ?_
  rw [iCycles_cyclesMap_thomPairSignCochainMap]
  rcases Int.units_eq_one_or g with rfl | rfl
  · have h1 : TopCat.ofHom ⟨((1 : ℤˣ) • · : (thomPair F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst → _),
        continuous_const_smul _⟩ = 𝟙 _ := TopCat.ext fun v ↦ one_smul ℤˣ v
    rw [h1, CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.id_comp, map_one,
      Units.val_one, one_smul]
    rfl
  · -- `-1` acts by the lifted deck involution, which negates the chain map to twisted chains.
    have hd := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ (finrank ℝ F))
      (TopPair.singularChainComplexπ_pair_naturality (deckThomPairMap F E ι) (ModuleCat.of R R))
    have hΛ := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ (finrank ℝ F))
      (singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMap (F := F) (E := E) hι R)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply] at hΛ
    have e1 : ((singularChains R).map (TopPair.Hom.fst (deckThomPairMap F E ι))).f (finrank ℝ F) ≫
        (TopPair.singularChainComplexπ
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of R R)).f (finrank ℝ F) =
        (TopPair.singularChainComplexπ
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of R R)).f (finrank ℝ F) ≫
          (TopPair.singularChainComplexMap (deckThomPairMap F E ι) (ModuleCat.of R R)).f
            (finrank ℝ F) :=
      (HomologicalComplex.comp_f _ _ _).symm.trans hd
    rw [show ((Units.map (Int.castRingHom R : ℤ →* R) (-1) : Rˣ) : R) = -1 by simp, neg_one_smul]
    erw [neg_one_smul_eq_deckThomPairMap_fst hι]
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e1)).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hΛ).trans (Preadditive.neg_comp _ _)))).trans (Preadditive.comp_neg _ _))

/-- **The equivariant Thom quasi-isomorphism of the orientation cover.** Over a compact base, let
`φ` be a relative cocycle representing the Thom class of `E` with coefficients in its orientation
system. Its lift to the Thom pair `(E', E'₀)` of the orientation cover is a semi-invariant cocycle
representing a Thom class of `E'`, so the equivariant cap product with it,
`C(E', E'₀; R) ⟶ (R_sign ⊗ C(B'; R))[r]`, is a quasi-isomorphism of complexes of representations
of `ℤˣ`. -/
theorem quasiIso_singularChainsRepCap_cyclesMap_thomPairSignCochainMap [CompactSpace B]
    (ω : Orientation ℝ F ι)
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R)).cycles (finrank ℝ F))
    (hφ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R)).homologyπ (finrank ℝ F) φ = twistedThomClass F E R hι ω) :
    have : ContinuousConstSMul ℤˣ
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
      (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
    have : ContinuousConstSMul ℤˣ
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
      (isQuotientCoveringMap_pullbackThomPairMap_snd (F := F) (E := E) hι).toContinuousConstSMul
    have : ContinuousConstSMul ℤˣ (TopCat.of (VectorBundleOrientationCover F E ι)) :=
      (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
    QuasiIso (TopPair.singularChainsRepCap
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (G := ℤˣ) (p₀ := thomPairProj F _) (fun _ _ ↦ by rw [thomPairProj_def]; rfl)
      (Units.map (Int.castRingHom R : ℤ →* R))
      (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι R φ) (fun _ _ ↦ rfl)) := by
  intro _ _ _
  refine quasiIso_singularChainsRepCap_thomPair _ _ _ _ ?_
  -- The lifted cocycle represents the lift of the twisted Thom class, a Thom class of `E'`.
  have h : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of R R) R (ModuleCat.of R R)).homologyπ (finrank ℝ F)
      (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R))
        (finrank ℝ F) φ) =
      thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
        (twistedThomClass F E R hι ω) := by
    rw [thomPairSignCohomologyMap_def, ← hφ, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality]
  rw [h]
  exact isThomClass_thomPairSignCohomologyMap_twistedThomClass hι R ω

end SemiInvariant

end TauCeti.VectorBundleOrientationCover
