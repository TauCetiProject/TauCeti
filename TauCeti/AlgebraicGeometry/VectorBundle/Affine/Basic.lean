/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Dual
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank
import TauCeti.AlgebraicGeometry.Modules.Localization
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Finite locally free sheaves on an affine scheme

For a commutative ring `R`, Mathlib's equivalence `AlgebraicGeometry.tildeEquiv` identifies
`R`-modules with quasicoherent sheaves on `Spec R` by `M ↦ M~`, with inverse the global sections.
It restricts to an equivalence between finitely generated projective `R`-modules and finite locally
free sheaves on `Spec R`.

The sheaf `M~` is finite locally free exactly when `M` is finitely generated and projective. One
direction is `TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde`. Conversely, a finite locally
free sheaf is dualizable in the category of quasicoherent sheaves, and the dualizable quasicoherent
sheaves on `Spec R` are those whose global sections are finitely generated and projective
(`TauCeti.AlgebraicGeometry.QuasicoherentSheaf.nonempty_hasLeftDual_iff_finite_projective`).
Applied over the affine charts of an arbitrary scheme `X`, a quasi-coherent `𝒪_X`-module is finite
locally free if and only if its sections over every affine open `U` of `X` form a finitely
generated projective `Γ(X, U)`-module.

Under this equivalence, the rank of a finite locally free sheaf at a prime `p` is the rank of the
free `R_p`-module `M_p` (Mathlib's `Module.rankAtStalk`). Indeed, the pullback of `M~` along
`Spec R_p ⟶ Spec R` is the sheaf associated with `R_p ⊗_R M ≅ M_p`, hence free on a basis of `M_p`,
and its rank at the closed point is the rank of `M~` at `p`.

A finite locally free sheaf whose global sections have a basis is free on the same index type. Over
a local ring every finitely generated projective module is free, so a finite locally free sheaf on
the spectrum of a local ring is free, on as many generators as its rank.

## Main declarations

* `TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff`: `M~` is finite locally free if and
  only if `M` is finitely generated and projective;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_fromSpec_iff`: the pullback of a
  quasi-coherent module `M` along an affine chart `Spec Γ(X, U) ⟶ X` is finite locally free if
  and only if `Γ(M, U)` is finitely generated and projective over `Γ(X, U)`;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_finite_projective_sections`: a
  quasi-coherent module whose sections over each member of a chosen affine open cover are finitely
  generated and projective is finite locally free;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen`: a quasi-coherent
  module on `X` is finite locally free if and only if its sections on every affine open are
  finitely generated and projective;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ`: the global
  sections of a finite locally free sheaf on `Spec R` are finitely generated and projective;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finiteProjectiveEquiv`: the equivalence between
  finitely generated projective `R`-modules and finite locally free sheaves on `Spec R`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_finiteProjectiveEquiv_functor_obj_apply`
  and `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_apply_eq_rankAtStalk`: the rank of a
  finite locally free sheaf on `Spec R` is the rank at stalks of its module of global sections;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.isoFreeOfBasis`: a finite locally free sheaf on
  `Spec R` whose global sections have a basis indexed by `I` is the free sheaf on `I`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.tildePiIsoFree`: the sheaf `(R^d)~` on
  `Spec R` is the free sheaf on `d` generators;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.isoFreeOfIsLocalRing`: over a local ring, a
  finite locally free sheaf of rank `n` on `Spec R` is free on `n` generators.

## References

* R. Hartshorne, *Algebraic Geometry*, Corollary II.5.5
* [The Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [The Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}}

namespace FiniteLocallyFreeSheaf

/-- The global sections of a finite locally free sheaf on `Spec R` form a finitely generated
projective `R`-module. -/
theorem finite_projective_moduleSpecΓ (E : FiniteLocallyFreeSheaf (Spec R)) :
    Module.Finite R (moduleSpecΓFunctor.obj E.obj) ∧
      Module.Projective R (moduleSpecΓFunctor.obj E.obj) :=
  (QuasicoherentSheaf.nonempty_hasLeftDual_iff_finite_projective
    ((toQuasicoherent (Spec R)).obj E)).mp
      (QuasicoherentSheaf.nonempty_hasLeftDual_of_isFiniteLocallyFree _ E.property)

end FiniteLocallyFreeSheaf

/-- The sheaf `M~` on `Spec R` associated with an `R`-module `M` is finite locally free if and only
if `M` is finitely generated and projective. -/
theorem isFiniteLocallyFree_tilde_iff (M : ModuleCat.{u} R) :
    Scheme.Modules.isFiniteLocallyFree (Spec R) (tilde M) ↔
      Module.Finite R M ∧ Module.Projective R M := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ isFiniteLocallyFree_tilde M⟩
  -- `M` is the module of global sections of `M~`.
  obtain ⟨_, _⟩ : Module.Finite R ((tilde.functor R ⋙ moduleSpecΓFunctor).obj M) ∧
      Module.Projective R ((tilde.functor R ⋙ moduleSpecΓFunctor).obj M) :=
    FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ ⟨tilde M, h⟩
  let e := (tilde.toTildeΓNatIso.app M).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- For a quasi-coherent `𝒪_X`-module `M` and an affine open `U` of `X`, the pullback of `M`
along the affine chart `Spec Γ(X, U) ⟶ X` is finite locally free if and only if `Γ(M, U)` is a
finitely generated projective `Γ(X, U)`-module. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_fromSpec_iff
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Scheme.Modules.isFiniteLocallyFree (Spec Γ(X, U))
        ((Scheme.Modules.pullback hU.fromSpec).obj M) ↔
      Module.Finite Γ(X, U) Γ(M, U) ∧ Module.Projective Γ(X, U) Γ(M, U) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let K : (Spec Γ(X, U)).Modules := M.restrict hU.fromSpec
  let e : tilde (moduleSpecΓFunctor.obj K) ≅ (Scheme.Modules.pullback hU.fromSpec).obj M :=
    @asIso _ _ _ _ K.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent K) ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M
  have he : Scheme.Modules.isFiniteLocallyFree (Spec Γ(X, U))
        ((Scheme.Modules.pullback hU.fromSpec).obj M) ↔
      Module.Finite Γ(X, U) (moduleSpecΓFunctor.obj K) ∧
        Module.Projective Γ(X, U) (moduleSpecΓFunctor.obj K) :=
    ⟨fun h ↦ (isFiniteLocallyFree_tilde_iff (moduleSpecΓFunctor.obj K)).mp
        ((Scheme.Modules.isFiniteLocallyFree _).prop_of_iso e.symm h),
     fun h ↦ (Scheme.Modules.isFiniteLocallyFree _).prop_of_iso e
        ((isFiniteLocallyFree_tilde_iff (moduleSpecΓFunctor.obj K)).mpr h)⟩
  let eΓ : Γ(M, U) ≃ₗ[Γ(X, U)] moduleSpecΓFunctor.obj K := M.fromSpecSectionsEquiv hU
  exact he.trans ⟨fun ⟨_, _⟩ ↦ ⟨Module.Finite.equiv eΓ.symm, Module.Projective.of_equiv eΓ.symm⟩,
    fun ⟨_, _⟩ ↦ ⟨Module.Finite.equiv eΓ, Module.Projective.of_equiv eΓ⟩⟩

/-- A quasi-coherent `𝒪_X`-module is finite locally free if its sections over each member of an
affine open cover `U` of `X`, indexed by an arbitrary sort, form a finitely generated projective
module over the corresponding coordinate ring. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_finite_projective_sections
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {ι : Sort*} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hM : ∀ i, Module.Finite Γ(X, U i) Γ(M, U i) ∧ Module.Projective Γ(X, U i) Γ(M, U i)) :
    Scheme.Modules.isFiniteLocallyFree X M :=
  (Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback
    (Scheme.AffineOpenCover.ofIsOpenCover (fun i : PLift ι ↦ U i.down)
      (by simpa only [TopologicalSpace.IsOpenCover, iSup_plift_down] using hcov)
      fun i ↦ hU i.down).openCover M).mpr fun i ↦
    (Scheme.Modules.isFiniteLocallyFree_pullback_fromSpec_iff M (hU i.down)).mpr (hM i.down)

/-- A quasi-coherent `𝒪_X`-module is finite locally free if and only if, on every affine open `U`
of `X`, its sections `Γ(M, U)` form a finitely generated projective `Γ(X, U)`-module. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] :
    Scheme.Modules.isFiniteLocallyFree X M ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        Module.Finite Γ(X, U) Γ(M, U) ∧ Module.Projective Γ(X, U) Γ(M, U) := by
  refine ⟨fun ⟨_, _⟩ U hU ↦ (Scheme.Modules.isFiniteLocallyFree_pullback_fromSpec_iff M hU).mp
    ⟨Scheme.Modules.isLocallyFree_pullback hU.fromSpec M,
      Scheme.Modules.isFinitePresentation_pullback hU.fromSpec M⟩, fun h ↦ ?_⟩
  exact M.isFiniteLocallyFree_of_finite_projective_sections (fun U : X.affineOpens ↦ U.val)
    (fun U ↦ U.property) (iSup_affineOpens_eq_top X) fun U ↦ h U.val U.property

namespace FiniteLocallyFreeSheaf

-- The body is exposed because the dependent unit and counit component equations below only
-- typecheck when the corresponding functor projections reduce.
variable (R) in
/-- Finitely generated projective `R`-modules are equivalent to finite locally free sheaves on
`Spec R`, by `M ↦ M~` with inverse the global sections. This is the restriction of Mathlib's
`AlgebraicGeometry.tildeEquiv` to these full subcategories. -/
@[expose, simps! functor_obj_obj functor_map_hom inverse_obj_obj inverse_map_hom
  unitIso_hom_app_hom]
def finiteProjectiveEquiv :
    (finiteProjectiveModules R).FullSubcategory ≌ FiniteLocallyFreeSheaf (Spec R) where
  functor := (Scheme.Modules.isFiniteLocallyFree (Spec R)).lift
    ((finiteProjectiveModules R).ι ⋙ tilde.functor R) fun M ↦
      (isFiniteLocallyFree_tilde_iff M.obj).mpr (finiteProjectiveModules_iff.mp M.property)
  inverse := (finiteProjectiveModules R).lift
    ((Scheme.Modules.isFiniteLocallyFree (Spec R)).ι ⋙ moduleSpecΓFunctor)
      fun E ↦ finiteProjectiveModules_iff.mpr (finite_projective_moduleSpecΓ E)
  unitIso := ((finiteProjectiveModules R).fullyFaithfulι.whiskeringRight _).preimageIso
    ((finiteProjectiveModules R).ι.isoWhiskerLeft tilde.toTildeΓNatIso)
  counitIso := ((Scheme.Modules.isFiniteLocallyFree (Spec R)).fullyFaithfulι.whiskeringRight
    _).preimageIso (NatIso.ofComponents
      -- Instance search does not find quasi-coherence of `E.obj` through `X.Modules`, so the
      -- invertibility of `fromTildeΓ` is supplied explicitly.
      (fun E ↦ @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ E.obj)
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent E.obj))
      fun f ↦ (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f.hom)
  functor_unitIso_comp M :=
    ObjectProperty.hom_ext _ (tilde.adjunction.left_triangle_components M.obj)

/-- The counit of `finiteProjectiveEquiv` is the canonical isomorphism from the sheaf associated
with the global sections of a finite locally free sheaf to the sheaf itself. -/
@[simp]
theorem finiteProjectiveEquiv_counitIso_hom_app_hom (E : FiniteLocallyFreeSheaf (Spec R)) :
    ((finiteProjectiveEquiv R).counitIso.hom.app E).hom = Scheme.Modules.fromTildeΓ E.obj :=
  rfl

/-- The rank of the sheaf `M~` associated with a finitely generated projective `R`-module `M` at
a prime `p` is the rank of the free `R_p`-module `M_p`. -/
@[simp]
theorem rank_finiteProjectiveEquiv_functor_obj_apply
    (M : (finiteProjectiveModules R).FullSubcategory) (p : Spec R) :
    ((finiteProjectiveEquiv R).functor.obj M).rank p = Module.rankAtStalk M.obj p := by
  obtain ⟨_, _⟩ := finiteProjectiveModules_iff.mp M.property
  let q : PrimeSpectrum R := p
  let Rₚ := Localization.AtPrime q.asIdeal
  let φ : R ⟶ CommRingCat.of Rₚ := CommRingCat.ofHom (algebraMap R Rₚ)
  let N := LocalizedModule q.asIdeal.primeCompl M.obj
  have : Module.Free Rₚ N := Module.free_of_flat_of_isLocalRing
  let ι := Module.Free.ChooseBasisIndex Rₚ N
  let b : Module.Basis ι Rₚ N := Module.Free.chooseBasis Rₚ N
  -- The pullback of `M~` to `Spec Rₚ` is the sheaf associated with `Rₚ ⊗_R M ≅ Mₚ`, which is
  -- free on the basis `b`.
  let e : ((pullback (Spec.map φ)).obj ((finiteProjectiveEquiv R).functor.obj M)).obj ≅
      (free (Spec (.of Rₚ)) ι).obj :=
    eqToIso (pullback_obj_obj _ _) ≪≫ (tildeFunctorCompPullbackIso φ).app M.obj ≪≫
      (tilde.functor _).mapIso (M.obj.extendScalarsLocalizationIso _ ≪≫ b.repr.toModuleIso) ≪≫
      tildeFinsupp (R := .of Rₚ) ι ≪≫ eqToIso (free_obj _ ι).symm
  let x : Spec (.of Rₚ) := IsLocalRing.closedPoint Rₚ
  have h := rank_pullback_apply (Spec.map φ) ((finiteProjectiveEquiv R).functor.obj M) x
  rw [rank_eq_of_iso e, rank_free_apply] at h
  -- The closed point of `Spec Rₚ` lies over `p`.
  have hp : (Spec.map φ) x = p :=
    PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := q.asIdeal))
  rw [hp] at h
  rw [← h, Nat.card_eq_fintype_card, ← Module.finrank_eq_card_chooseBasisIndex]
  -- `Module.rankAtStalk M p` is by definition the rank of `Mₚ` over `Rₚ`.
  rfl

/-- The rank of a finite locally free sheaf `E` on `Spec R` at a prime `p` is the rank at `p` of
its module of global sections. -/
theorem rank_apply_eq_rankAtStalk (E : FiniteLocallyFreeSheaf (Spec R)) (p : Spec R) :
    E.rank p = Module.rankAtStalk (moduleSpecΓFunctor.obj E.obj) p :=
  -- `E` is the sheaf associated with its module of global sections.
  (DFunLike.congr_fun (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree (Spec R)).ι.mapIso
    ((finiteProjectiveEquiv R).counitIso.app E).symm)) p).trans
      (rank_finiteProjectiveEquiv_functor_obj_apply ((finiteProjectiveEquiv R).inverse.obj E) p)

/-- A finite locally free sheaf `E` on `Spec R` whose module of global sections has a basis
indexed by `I` is isomorphic to the free sheaf on `I`. -/
def isoFreeOfBasis (E : FiniteLocallyFreeSheaf (Spec R)) {I : Type u} [Finite I]
    (b : Module.Basis I R (moduleSpecΓFunctor.obj E.obj)) : E ≅ free (Spec R) I :=
  ((finiteProjectiveEquiv R).counitIso.app E).symm ≪≫
    ObjectProperty.isoMk _ ((tilde.functor R).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp I ≪≫
      eqToIso (free_obj (Spec R) I).symm)

/-- `isoFreeOfBasis` is the inverse of the counit `(Γ E)~ ≅ E`, followed by the sheafification
of `b.repr : Γ E ≃ (I →₀ R)` and `tildeFinsupp`. -/
lemma isoFreeOfBasis_hom (E : FiniteLocallyFreeSheaf (Spec R)) {I : Type u} [Finite I]
    (b : Module.Basis I R (moduleSpecΓFunctor.obj E.obj)) :
    (isoFreeOfBasis E b).hom = (finiteProjectiveEquiv R).counitIso.inv.app E ≫
      ObjectProperty.homMk ((tilde.functor R).map b.repr.toModuleIso.hom ≫
        (tildeFinsupp I).hom ≫ eqToHom (free_obj (Spec R) I).symm) :=
  (rfl)

variable (R) in
/-- The sheaf `(R^d)~` on `Spec R` is the free sheaf on a universe lift of `Fin d`, the
underlying sheaf of `FixedRank.free (Spec R) d`. -/
def tildePiIsoFree (d : ℕ) :
    tilde (.of R (Fin d → R)) ≅ (free (Spec R) (ULift.{u} (Fin d))).obj :=
  (tilde.functor R).mapIso (LinearEquiv.funCongrLeft R R Equiv.ulift ≪≫ₗ
    (Finsupp.linearEquivFunOnFinite R R _).symm).toModuleIso ≪≫ tildeFinsupp _ ≪≫
    eqToIso (free_obj (Spec R) _).symm

/-- The dimension of a free module of global sections of a finite locally free sheaf on `Spec R`
is the rank of the sheaf, at any point. -/
theorem finrank_moduleSpecΓ (E : FiniteLocallyFreeSheaf (Spec R))
    [Module.Free R (moduleSpecΓFunctor.obj E.obj)] (p : Spec R) :
    Module.finrank R (moduleSpecΓFunctor.obj E.obj) = E.rank p :=
  have := (finite_projective_moduleSpecΓ E).1
  ((rank_apply_eq_rankAtStalk E p).trans
    (congrFun Module.rankAtStalk_eq_finrank_of_free p)).symm

variable [IsLocalRing R]

/-- Over a local ring `R`, the global sections of a finite locally free sheaf on `Spec R` form a
free module. -/
instance free_moduleSpecΓ (E : FiniteLocallyFreeSheaf (Spec R)) :
    Module.Free R (moduleSpecΓFunctor.obj E.obj) :=
  have := (finite_projective_moduleSpecΓ E).1
  have := (finite_projective_moduleSpecΓ E).2
  Module.free_of_flat_of_isLocalRing

/-- **A finite locally free sheaf on the spectrum of a local ring is free.** If `E` has rank `n`
at the closed point of `Spec R`, then `E` is isomorphic to the free sheaf on `n` generators. -/
def isoFreeOfIsLocalRing (E : FiniteLocallyFreeSheaf (Spec R)) {n : ℕ}
    (hn : E.rank (IsLocalRing.closedPoint R) = n) : E ≅ free (Spec R) (ULift.{u} (Fin n)) :=
  have := (finite_projective_moduleSpecΓ E).1
  isoFreeOfBasis E ((Module.finBasisOfFinrankEq R _
    ((finrank_moduleSpecΓ E _).trans hn)).reindex Equiv.ulift.symm)

/-- `isoFreeOfIsLocalRing` is `isoFreeOfBasis` for the basis of the global sections indexed by
`ULift (Fin n)` given by `Module.finBasisOfFinrankEq`. -/
lemma isoFreeOfIsLocalRing_def (E : FiniteLocallyFreeSheaf (Spec R)) {n : ℕ}
    (hn : E.rank (IsLocalRing.closedPoint R) = n) :
    haveI := (finite_projective_moduleSpecΓ E).1
    isoFreeOfIsLocalRing E hn = isoFreeOfBasis E ((Module.finBasisOfFinrankEq R _
      ((finrank_moduleSpecΓ E _).trans hn)).reindex Equiv.ulift.symm) :=
  (rfl)

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
