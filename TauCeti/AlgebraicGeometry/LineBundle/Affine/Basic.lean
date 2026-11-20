/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Monoidal
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Dual
public import TauCeti.RingTheory.PicardGroup.RankOne

/-!
# Invertible sheaves on an affine scheme

For a commutative ring `R`, Mathlib's associated-sheaf equivalence `AlgebraicGeometry.tildeEquiv`
restricts to a monoidal equivalence between invertible `R`-modules and invertible sheaves on
`Spec R`, sending `M` to `M~` and `L` to its module of global sections.

By `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.isInvertible_iff_forall_rank_eq_one`, a sheaf
of modules on `Spec R` is invertible precisely when it is finite locally free of rank one at every
point. Combined with `TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff`, the stalk-rank
formula `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_apply_eq_rankAtStalk`, and the
algebraic characterization `Module.invertible_iff_rankAtStalk_eq_one`, this shows that `M~` is
invertible if and only if `M` is an invertible `R`-module, and that the global sections of any
invertible sheaf on `Spec R` form an invertible `R`-module.

The resulting equivalence `InvertibleSheaf.invertibleModuleEquiv` inherits the monoidal comparisons
of `AlgebraicGeometry.tilde.functor`, intertwines linear dualization on invertible modules with the
internal-Hom dual of invertible sheaves, characterizes globally trivial line bundles on `Spec R` as
those whose global sections are free, and commutes with pullback along affine scheme morphisms
`Spec φ : Spec S ⟶ Spec R` via extension of scalars.

## Main declarations

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.invertible_moduleSpecΓ`: the global sections of an
  invertible sheaf on `Spec R` form an invertible `R`-module;
* `TauCeti.AlgebraicGeometry.isInvertible_tilde` and
  `TauCeti.AlgebraicGeometry.isInvertible_tilde_iff`: `M~` is an invertible sheaf on `Spec R` if
  and only if `M` is an invertible `R`-module;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.invertibleModuleEquiv`: the monoidal equivalence
  `(invertibleModules R).FullSubcategory ≌ InvertibleSheaf (Spec R)`;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.invertibleModuleEquivDualIso`: compatibility of
  `invertibleModuleEquiv` with duals of invertible modules and line bundles;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.isoFreeOfBasis`,
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.isoTrivialOfLinearEquiv`, and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_iso_trivial_iff_free`: global
  trivializations of line bundles on `Spec R` from bases of global sections;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.invertibleModuleEquivCompPullbackIso`: compatibility
  of `invertibleModuleEquiv` with affine pullback and `InvertibleModules.extendScalars`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 and Corollary II.5.5
* [The Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [The Stacks Project, Tag 01IB](https://stacks.math.columbia.edu/tag/01IB)
* [The Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}}

namespace InvertibleSheaf

/-- The global sections of an invertible sheaf on `Spec R` form an invertible `R`-module. -/
instance invertible_moduleSpecΓ (L : InvertibleSheaf (Spec R)) :
    Module.Invertible R (moduleSpecΓFunctor.obj L.obj) := by
  let E : FiniteLocallyFreeSheaf (Spec R) := (toFiniteLocallyFree (Spec R)).obj L
  obtain ⟨hfin, hproj⟩ := FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ E
  refine Module.invertible_iff_rankAtStalk_eq_one.mpr ⟨hfin, hproj, fun p ↦ ?_⟩
  have hrank : E.rank p = Module.rankAtStalk (moduleSpecΓFunctor.obj L.obj) p :=
    FiniteLocallyFreeSheaf.rank_apply_eq_rankAtStalk E p
  exact hrank.symm.trans (rank_toFiniteLocallyFree_apply L p)

/-- Unbundled-ring form of `invertible_moduleSpecΓ`, allowing `CommRing.Pic.mk R` to synthesize
invertibility of global sections on `Spec (.of R)` directly. -/
instance invertible_moduleSpecΓ_of {R₀ : Type u} [CommRing R₀]
    (L : InvertibleSheaf (Spec (.of R₀))) :
    Module.Invertible R₀ ((moduleSpecΓFunctor (R := .of R₀)).obj L.obj) :=
  invertible_moduleSpecΓ L

end InvertibleSheaf

/-- The sheaf `M~` on `Spec R` associated with an invertible `R`-module `M` is an invertible
sheaf. -/
instance isInvertible_tilde (M : ModuleCat.{u} R) [Module.Invertible R M] :
    SheafOfModules.isInvertible (Spec R) (tilde M) := by
  let A : Type u := M
  have hfin : Module.Finite R M := inferInstanceAs (Module.Finite R A)
  have hproj : Module.Projective R M := inferInstanceAs (Module.Projective R A)
  let F : (finiteProjectiveModules R).FullSubcategory :=
    ⟨M, finiteProjectiveModules_iff.mpr ⟨hfin, hproj⟩⟩
  refine (FiniteLocallyFreeSheaf.isInvertible_iff_forall_rank_eq_one
    ((FiniteLocallyFreeSheaf.finiteProjectiveEquiv R).functor.obj F)).mpr fun p ↦ ?_
  rw [FiniteLocallyFreeSheaf.rank_finiteProjectiveEquiv_functor_obj_apply]
  exact Module.Invertible.rankAtStalk_eq_one p

/-- The sheaf `M~` on `Spec R` associated with an `R`-module `M` is invertible if and only if `M`
is an invertible `R`-module. -/
theorem isInvertible_tilde_iff (M : ModuleCat.{u} R) :
    SheafOfModules.isInvertible (Spec R) (tilde M) ↔ Module.Invertible R M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isInvertible_tilde M⟩
  have : Module.Invertible R ((tilde.functor R ⋙ moduleSpecΓFunctor).obj M) :=
    InvertibleSheaf.invertible_moduleSpecΓ ⟨tilde M, h⟩
  exact Module.Invertible.congr (tilde.toTildeΓNatIso.app M).symm.toLinearEquiv

namespace InvertibleSheaf

-- Exposed so the dependent unit and counit equations reduce on functor and inverse projections,
-- matching `FiniteLocallyFreeSheaf.finiteProjectiveEquiv`.
variable (R) in
/-- Invertible `R`-modules are equivalent to invertible sheaves on `Spec R`, via `M ↦ M~` with
inverse the global-sections functor. This is the restriction of
`FiniteLocallyFreeSheaf.finiteProjectiveEquiv` to rank-one objects. -/
@[expose, simps! functor_obj_obj functor_map_hom inverse_obj_obj inverse_map_hom
  unitIso_hom_app_hom]
def invertibleModuleEquiv :
    (invertibleModules R).FullSubcategory ≌ InvertibleSheaf (Spec R) where
  functor := (SheafOfModules.isInvertible (Spec R)).lift
    ((invertibleModules R).ι ⋙ tilde.functor R) fun M ↦
      (isInvertible_tilde_iff M.obj).mpr ((invertibleModules_iff R M.obj).mp M.property)
  inverse := (invertibleModules R).lift
    ((SheafOfModules.isInvertible (Spec R)).ι ⋙ moduleSpecΓFunctor)
      fun L ↦ (invertibleModules_iff R _).mpr (invertible_moduleSpecΓ L)
  unitIso := ((invertibleModules R).fullyFaithfulι.whiskeringRight _).preimageIso
    ((invertibleModules R).ι.isoWhiskerLeft tilde.toTildeΓNatIso)
  counitIso := ((SheafOfModules.isInvertible (Spec R)).fullyFaithfulι.whiskeringRight
    _).preimageIso (NatIso.ofComponents
      -- Supply quasi-coherence of `L.obj` explicitly to `fromTildeΓ`, matching
      -- `finiteProjectiveEquiv`.
      (fun L ↦ @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ L.obj)
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent L.obj))
      fun f ↦ (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f.hom)
  functor_unitIso_comp M :=
    ObjectProperty.hom_ext _ (tilde.adjunction.left_triangle_components M.obj)

/-- The counit of `invertibleModuleEquiv` is the canonical isomorphism `(Γ L)~ ≅ L`. -/
@[simp]
theorem invertibleModuleEquiv_counitIso_hom_app_hom (L : InvertibleSheaf (Spec R)) :
    ((invertibleModuleEquiv R).counitIso.hom.app L).hom = Scheme.Modules.fromTildeΓ L.obj :=
  (rfl)

/-- `invertibleModuleEquiv` commutes with the inclusions into finite projective modules and finite
locally free sheaves. -/
theorem invertibleModuleEquiv_functor_comp_toFiniteLocallyFree (R : CommRingCat.{u}) :
    (invertibleModuleEquiv R).functor ⋙ toFiniteLocallyFree (Spec R) =
      InvertibleModules.toFiniteProjective R ⋙
        (FiniteLocallyFreeSheaf.finiteProjectiveEquiv R).functor :=
  (rfl)

/-- The inverse of `invertibleModuleEquiv` commutes with the inclusions into finite locally free
sheaves and finite projective modules. -/
theorem toFiniteLocallyFree_comp_finiteProjectiveEquiv_inverse (R : CommRingCat.{u}) :
    toFiniteLocallyFree (Spec R) ⋙ (FiniteLocallyFreeSheaf.finiteProjectiveEquiv R).inverse =
      (invertibleModuleEquiv R).inverse ⋙ InvertibleModules.toFiniteProjective R :=
  (rfl)

section Monoidal

variable (R : CommRingCat.{u})

/-- The forward functor of `invertibleModuleEquiv` is strong monoidal, with unit and tensor
comparisons restricted from `AlgebraicGeometry.tilde.functor`. -/
instance invertibleModuleEquivFunctorMonoidal : (invertibleModuleEquiv R).functor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := ObjectProperty.isoMk (SheafOfModules.isInvertible (Spec R))
        (Functor.Monoidal.εIso (tilde.functor R))
      μIso M N := ObjectProperty.isoMk (SheafOfModules.isInvertible (Spec R))
        (Functor.Monoidal.μIso (tilde.functor R) M.obj N.obj)
      μIso_hom_natural_left f N := by
        apply ObjectProperty.hom_ext
        exact μ_natural_left (tilde.functor R) f.hom N.obj
      μIso_hom_natural_right M f := by
        apply ObjectProperty.hom_ext
        exact μ_natural_right (tilde.functor R) M.obj f.hom
      associativity M N P := by
        apply ObjectProperty.hom_ext
        exact Functor.LaxMonoidal.associativity (tilde.functor R) M.obj N.obj P.obj
      left_unitality M := by
        apply ObjectProperty.hom_ext
        exact Functor.LaxMonoidal.left_unitality (tilde.functor R) M.obj
      right_unitality M := by
        apply ObjectProperty.hom_ext
        exact Functor.LaxMonoidal.right_unitality (tilde.functor R) M.obj }

/-- On underlying sheaves, the lax unit comparison of `(invertibleModuleEquiv R).functor` is that
of `tilde.functor R`. -/
@[simp]
theorem invertibleModuleEquiv_functor_ε_hom :
    (ε (invertibleModuleEquiv R).functor).hom = ε (tilde.functor R) :=
  (rfl)

/-- On underlying sheaves, the lax tensor comparison of `(invertibleModuleEquiv R).functor` is that
of `tilde.functor R`. -/
@[simp]
theorem invertibleModuleEquiv_functor_μ_hom (M N : (invertibleModules R).FullSubcategory) :
    (μ (invertibleModuleEquiv R).functor M N).hom = μ (tilde.functor R) M.obj N.obj :=
  (rfl)

/-- On underlying sheaves, the oplax unit comparison of `(invertibleModuleEquiv R).functor` is that
of `tilde.functor R`. -/
@[simp]
theorem invertibleModuleEquiv_functor_η_hom :
    (η (invertibleModuleEquiv R).functor).hom = η (tilde.functor R) :=
  (rfl)

/-- On underlying sheaves, the oplax tensor comparison of `(invertibleModuleEquiv R).functor` is
that of `tilde.functor R`. -/
@[simp]
theorem invertibleModuleEquiv_functor_δ_hom (M N : (invertibleModules R).FullSubcategory) :
    (δ (invertibleModuleEquiv R).functor M N).hom = δ (tilde.functor R) M.obj N.obj :=
  (rfl)

/-- Global sections on invertible sheaves carries the monoidal structure inverse to that of the
associated-sheaf functor. -/
instance invertibleModuleEquivInverseMonoidal : (invertibleModuleEquiv R).inverse.Monoidal :=
  (invertibleModuleEquiv R).inverseMonoidal

/-- The affine invertible-sheaf equivalence, with its canonical unit and counit, is monoidal. -/
instance invertibleModuleEquiv_isMonoidal : (invertibleModuleEquiv R).IsMonoidal :=
  inferInstance

/-- Unbundled-ring form of `invertibleModuleEquivFunctorMonoidal`, allowing typeclass search on
`Spec (.of R₀)` where `(CommRingCat.of R₀).carrier` reduces to `R₀` in `DiscrTree` keys. -/
instance invertibleModuleEquivFunctorMonoidalOf {R₀ : Type u} [CommRing R₀] :
    (invertibleModuleEquiv (.of R₀)).functor.Monoidal :=
  invertibleModuleEquivFunctorMonoidal (.of R₀)

/-- Unbundled-ring form of `invertibleModuleEquivInverseMonoidal`, allowing typeclass search on
`Spec (.of R₀)` where `(CommRingCat.of R₀).carrier` reduces to `R₀` in `DiscrTree` keys. -/
instance invertibleModuleEquivInverseMonoidalOf {R₀ : Type u} [CommRing R₀] :
    (invertibleModuleEquiv (.of R₀)).inverse.Monoidal :=
  invertibleModuleEquivInverseMonoidal (.of R₀)

/-- Unbundled-ring form of `invertibleModuleEquiv_isMonoidal`. -/
instance invertibleModuleEquiv_isMonoidal_of {R₀ : Type u} [CommRing R₀] :
    (invertibleModuleEquiv (.of R₀)).IsMonoidal :=
  invertibleModuleEquiv_isMonoidal (.of R₀)

end Monoidal

section Dual

variable (R : CommRingCat.{u})

/-- The sheaf associated with the linear dual of an invertible `R`-module is canonically isomorphic
to the dual line bundle of its associated invertible sheaf. -/
def invertibleModuleEquivDualIso (M : (invertibleModules R).FullSubcategory) :
    (invertibleModuleEquiv R).functor.obj (InvertibleModules.dual R M) ≅
      dual ((invertibleModuleEquiv R).functor.obj M) :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible (Spec R))
    (((Scheme.Modules.isFiniteLocallyFree (Spec R)).ι.mapIso
      (FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso R
        ((InvertibleModules.toFiniteProjective R).obj M))) ≪≫
      eqToIso (dual_obj ((invertibleModuleEquiv R).functor.obj M)).symm)

/-- On underlying sheaves, `invertibleModuleEquivDualIso R M` agrees with
`FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso` up to `dual_obj`. -/
@[simp]
theorem invertibleModuleEquivDualIso_hom_hom (M : (invertibleModules R).FullSubcategory) :
    (invertibleModuleEquivDualIso R M).hom.hom =
      (FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso R
        ((InvertibleModules.toFiniteProjective R).obj M)).hom.hom ≫
        eqToHom (dual_obj ((invertibleModuleEquiv R).functor.obj M)).symm :=
  (rfl)

/-- The affine dual comparison for invertible modules is contravariantly natural. -/
@[reassoc]
theorem invertibleModuleEquivDualIso_naturality
    {M N : (invertibleModules R).FullSubcategory} (f : M ⟶ N) :
    (tilde.functor R).map (ModuleCat.ofHom f.hom.hom.dualMap) ≫
        (invertibleModuleEquivDualIso R M).hom.hom ≫
        eqToHom (dual_obj ((invertibleModuleEquiv R).functor.obj M)) =
      (invertibleModuleEquivDualIso R N).hom.hom ≫
        eqToHom (dual_obj ((invertibleModuleEquiv R).functor.obj N)) ≫
        (pre ((tilde.functor R).map f.hom)).app (𝟙_ (Spec R).Modules) := by
  -- `Scheme.Modules` is semireducible, so cancel `eqToHom` via `comp_eqToHom_iff` and
  -- term-mode chaining instead of `rw`.
  have hcancel (L : (invertibleModules R).FullSubcategory) :
      (invertibleModuleEquivDualIso R L).hom.hom ≫
          eqToHom (dual_obj ((invertibleModuleEquiv R).functor.obj L)) =
        (FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso R
          ((InvertibleModules.toFiniteProjective R).obj L)).hom.hom :=
    (comp_eqToHom_iff _ _ _).mpr (invertibleModuleEquivDualIso_hom_hom R L)
  exact (congrArg ((tilde.functor R).map (ModuleCat.ofHom f.hom.hom.dualMap) ≫ ·)
      (hcancel M)).trans
    ((FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso_naturality R
      ((InvertibleModules.toFiniteProjective R).map f)).trans
      ((reassoc_of% (hcancel N)) _).symm)

end Dual

section Trivialization

/-- An invertible sheaf `L` on `Spec R` whose global sections have a basis indexed by a
one-element type `I` is isomorphic to `InvertibleSheaf.free (Spec R) I`. -/
def isoFreeOfBasis (L : InvertibleSheaf (Spec R)) {I : Type u} [Nonempty I] [Subsingleton I]
    (b : Module.Basis I R (moduleSpecΓFunctor.obj L.obj)) : L ≅ free (Spec R) I :=
  have : Finite I := Finite.of_subsingleton
  ObjectProperty.isoMk (SheafOfModules.isInvertible (Spec R))
    (((Scheme.Modules.isFiniteLocallyFree (Spec R)).ι.mapIso
      (FiniteLocallyFreeSheaf.isoFreeOfBasis ((toFiniteLocallyFree (Spec R)).obj L) b)) ≪≫
      eqToIso ((FiniteLocallyFreeSheaf.free_obj (Spec R) I).trans (free_obj (Spec R) I).symm))

/-- A linear equivalence between the global sections of `L` and `R` trivializes `L` on `Spec R`. -/
def isoTrivialOfLinearEquiv (L : InvertibleSheaf (Spec R))
    (e : (moduleSpecΓFunctor.obj L.obj) ≃ₗ[R] R) : L ≅ trivial (Spec R) :=
  ((invertibleModuleEquiv R).counitIso.app L).symm ≪≫
    ObjectProperty.isoMk (SheafOfModules.isInvertible (Spec R))
      ((tilde.functor R).mapIso e.toModuleIso ≪≫
        Functor.Monoidal.εIso (tilde.functor R) ≪≫
        (trivialObjIsoUnit (Spec R)).symm)

/-- An invertible sheaf on `Spec R` is isomorphic to the trivial line bundle if and only if its
`R`-module of global sections is free. -/
theorem nonempty_iso_trivial_iff_free (L : InvertibleSheaf (Spec R)) :
    Nonempty (L ≅ trivial (Spec R)) ↔ Module.Free R (moduleSpecΓFunctor.obj L.obj) := by
  rw [Module.Invertible.free_iff_linearEquiv]
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ ⟨isoTrivialOfLinearEquiv L e⟩⟩
  let e₀ : L.obj ≅ tilde (𝟙_ (ModuleCat.{u} R)) :=
    ((SheafOfModules.isInvertible (Spec R)).ι.mapIso e) ≪≫
      trivialObjIsoUnit (Spec R) ≪≫
      (Functor.Monoidal.εIso (tilde.functor R)).symm
  exact ⟨(moduleSpecΓFunctor.mapIso e₀ ≪≫
    (tilde.toTildeΓNatIso.app (𝟙_ (ModuleCat.{u} R))).symm).toLinearEquiv⟩

end Trivialization

section BaseChange

variable {S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Pulling back the invertible sheaf associated with an invertible `R`-module along
`Spec φ : Spec S ⟶ Spec R` agrees with extending scalars along `φ.hom` and then taking the
associated invertible sheaf on `Spec S`. -/
def invertibleModuleEquivCompPullbackIso :
    (invertibleModuleEquiv R).functor ⋙ pullback (Spec.map φ) ≅
      InvertibleModules.extendScalars φ.hom ⋙ (invertibleModuleEquiv S).functor :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk (SheafOfModules.isInvertible (Spec S))
      (eqToIso (pullback_obj_obj (Spec.map φ) ((invertibleModuleEquiv R).functor.obj M)) ≪≫
        (tildeFunctorCompPullbackIso φ).app M.obj))
    (fun {M N} f ↦ by
      apply ObjectProperty.hom_ext
      simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, pullback_map]
      -- `invertibleModuleEquiv` is semireducible, so cancel `eqToHom` via `eqToHom_comp_iff`
      -- rather than `rw` across `Iso.trans_hom`.
      have hcancel :
          eqToHom (pullback_obj_obj (Spec.map φ) ((invertibleModuleEquiv R).functor.obj N)).symm ≫
              (eqToIso (pullback_obj_obj (Spec.map φ) ((invertibleModuleEquiv R).functor.obj N)) ≪≫
                (tildeFunctorCompPullbackIso φ).app N.obj).hom =
            (tildeFunctorCompPullbackIso φ).hom.app N.obj :=
        (eqToHom_comp_iff _ _ _).mpr (Iso.trans_hom _ _)
      rw [Category.assoc, Category.assoc]
      exact (congrArg (eqToHom _ ≫ _ ≫ ·) hcancel).trans
        ((congrArg (eqToHom _ ≫ ·) ((tildeFunctorCompPullbackIso φ).hom.naturality f.hom)).trans
          (Category.assoc _ _ _).symm))

/-- On underlying sheaves, `invertibleModuleEquivCompPullbackIso φ` is
`tildeFunctorCompPullbackIso φ`. -/
@[simp]
theorem invertibleModuleEquivCompPullbackIso_hom_app_hom
    (M : (invertibleModules R).FullSubcategory) :
    ((invertibleModuleEquivCompPullbackIso φ).hom.app M).hom =
      eqToHom (pullback_obj_obj (Spec.map φ) ((invertibleModuleEquiv R).functor.obj M)) ≫
        (tildeFunctorCompPullbackIso φ).hom.app M.obj :=
  (rfl)

/-- On underlying sheaves, the inverse of `invertibleModuleEquivCompPullbackIso φ` is the inverse
of `tildeFunctorCompPullbackIso φ`. -/
@[simp]
theorem invertibleModuleEquivCompPullbackIso_inv_app_hom
    (M : (invertibleModules R).FullSubcategory) :
    ((invertibleModuleEquivCompPullbackIso φ).inv.app M).hom =
      (tildeFunctorCompPullbackIso φ).inv.app M.obj ≫
        eqToHom (pullback_obj_obj (Spec.map φ) ((invertibleModuleEquiv R).functor.obj M)).symm :=
  Iso.trans_inv (eqToIso _) ((tildeFunctorCompPullbackIso φ).app M.obj)

end BaseChange

end InvertibleSheaf

end

end TauCeti.AlgebraicGeometry
