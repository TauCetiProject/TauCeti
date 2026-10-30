/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Affine
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction

/-!
# Quasicoherence of symmetric powers

The symmetric powers of a quasicoherent module sheaf are quasicoherent, with no finiteness,
flatness, or characteristic assumptions. Thus symmetric powers define endofunctors of the
category of quasicoherent sheaves. These are the components of its graded symmetric algebra.
-/

public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace TauCeti.AlgebraicGeometry

universe u

/-- Symmetric powers of quasicoherent modules on a spectrum are quasicoherent. -/
private theorem isQuasicoherent_symmetricPower_spec {R : CommRingCat.{u}} (n : ℕ)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.symmetricPower (Spec R).sheaf n).obj M).IsQuasicoherent := by
  let eΓ := @asIso _ _ _ _ M.fromTildeΓ
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M)
  let e := tildeSymmetricPowerIso n ((moduleSpecΓFunctor (R := R)).obj M) ≪≫
    (SheafOfModules.symmetricPower (Spec R).sheaf n).mapIso eΓ
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

private theorem isQuasicoherent_symmetricPower_affine {X : Scheme.{u}} [IsAffine X]
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.symmetricPower X.sheaf n).obj M).IsQuasicoherent := by
  have : (Scheme.Modules.restrict ((SheafOfModules.symmetricPower X.sheaf n).obj M)
      X.isoSpec.inv).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictSymmetricPowerIso X.isoSpec.inv n).app M)
      (isQuasicoherent_symmetricPower_spec n (M.restrict X.isoSpec.inv))
  exact isQuasicoherent_of_isQuasicoherent_restrict_iso X.isoSpec _

/-- Every symmetric power of a quasicoherent module sheaf on an arbitrary scheme is
quasicoherent. No finite-generation, flatness, or characteristic assumption is needed. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricPower
    {X : Scheme.{u}} (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.symmetricPower X.sheaf n).obj M).IsQuasicoherent := by
  refine isQuasicoherent_of_isQuasicoherent_restrict_affineOpens _ fun U ↦ ?_
  have : IsAffine U.1.toScheme := U.2
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictSymmetricPowerIso U.1.ι n).app M)
    (isQuasicoherent_symmetricPower_affine n (M.restrict U.1.ι))

namespace QuasicoherentSheaf

variable (X : Scheme.{u})

variable {X} in
/-- The symmetric powers of the underlying module sheaf of a quasicoherent sheaf are
quasicoherent. This restates `Scheme.Modules.isQuasicoherent_symmetricPower` for the underlying
object of a quasicoherent sheaf, whose type `SheafOfModules X.ringCatSheaf` instance search does
not identify with `X.Modules`. -/
instance isQuasicoherent_symmetricPower_obj (n : ℕ) (M : QuasicoherentSheaf X) :
    ((SheafOfModules.symmetricPower X.sheaf n).obj M.obj).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_symmetricPower n M.obj

/-- The symmetric-power endofunctor of quasicoherent sheaves on a scheme, inherited from
the symmetric-power endofunctor of all module sheaves. -/
def symmetricPower (n : ℕ) : QuasicoherentSheaf X ⥤ QuasicoherentSheaf X :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
      SheafOfModules.symmetricPower X.sheaf n)
    fun M ↦ isQuasicoherent_symmetricPower_obj n M

/-- The underlying module sheaf of a quasicoherent symmetric power. -/
@[simp]
theorem symmetricPower_obj_obj (n : ℕ) (M : QuasicoherentSheaf X) :
    ((symmetricPower X n).obj M).obj =
      (SheafOfModules.symmetricPower X.sheaf n).obj M.obj :=
  (rfl)

/-- Symmetric power acts on morphisms by the underlying symmetric-power map. The equality
transports identify the underlying objects of the lifted functor. -/
@[simp]
theorem symmetricPower_map_hom (n : ℕ) {M N : QuasicoherentSheaf X} (φ : M ⟶ N) :
    ((symmetricPower X n).map φ).hom =
      eqToHom (symmetricPower_obj_obj X n M) ≫
        (SheafOfModules.symmetricPower X.sheaf n).map φ.hom ≫
        eqToHom (symmetricPower_obj_obj X n N).symm := by
  cases symmetricPower_obj_obj X n M
  cases symmetricPower_obj_obj X n N
  -- The lifted category uses the same underlying arrows; the displayed transports
  -- are identities after identifying its objects.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end QuasicoherentSheaf

end TauCeti.AlgebraicGeometry
