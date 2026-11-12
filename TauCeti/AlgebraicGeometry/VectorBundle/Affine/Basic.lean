/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Dual
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank

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
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ`: the global
  sections of a finite locally free sheaf on `Spec R` are finitely generated and projective;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finiteProjectiveEquiv`: the equivalence between
  finitely generated projective `R`-modules and finite locally free sheaves on `Spec R`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_finiteProjectiveEquiv_functor_obj_apply`
  and `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_apply_eq_rankAtStalk`: the rank of a
  finite locally free sheaf on `Spec R` is the rank at stalks of its module of global sections;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.isoFreeOfBasis`: a finite locally free sheaf on
  `Spec R` whose global sections have a basis indexed by `I` is the free sheaf on `I`;
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
