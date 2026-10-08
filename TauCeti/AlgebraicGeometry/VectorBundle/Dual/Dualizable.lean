/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Dual
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Dualizable quasicoherent sheaves are finite locally free

On an arbitrary scheme, a quasicoherent sheaf has a left or right dual in the symmetric
monoidal category of quasicoherent sheaves if and only if it is finite locally free.
No affine, quasi-compactness, separation or noetherian hypothesis is needed.

Pullback preserves dualizability, so a dualizable sheaf restricts to a dualizable sheaf on
each affine chart. The affine criterion identifies its module of sections as finite projective;
finite local freeness then descends along the affine open cover. In the converse direction,
the internal-Hom dual of a finite locally free sheaf supplies its categorical dual.

## References

* The Stacks Project, *Sheaves of Modules*, finite locally free modules and duality.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.QuasicoherentSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

/-- A quasicoherent sheaf on an affine scheme `X` is dualizable in `QuasicoherentSheaf X` if and
only if it is finite locally free. -/
private theorem nonempty_hasLeftDual_iff_isFiniteLocallyFree_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (E : QuasicoherentSheaf X) :
    Nonempty (HasLeftDual E) ↔ Scheme.Modules.isFiniteLocallyFree X E.obj := by
  refine ⟨fun h ↦ ?_, nonempty_hasLeftDual_of_isFiniteLocallyFree E⟩
  -- Finite local freeness can be checked after pullback along the isomorphism
  -- `Spec Γ(X, ⊤) ≅ X`, which preserves dualizability since `X` is affine.
  refine (Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback
    (Scheme.coverOfIsIso.{u} (P := @IsOpenImmersion) X.isoSpec.inv) E.obj).mpr fun _ ↦ ?_
  let F := (pullback X.isoSpec.inv).obj E
  -- On `Spec Γ(X, ⊤)`, the dualizable sheaf `F` is the sheaf associated with its finite
  -- projective module of global sections.
  obtain ⟨_, _⟩ := (nonempty_hasLeftDual_iff_finite_projective F).mp
    (E.nonempty_hasLeftDual_pullback X.isoSpec.inv h)
  have hF : Scheme.Modules.isFiniteLocallyFree (Spec Γ(X, ⊤)) F.obj :=
    (Scheme.Modules.isFiniteLocallyFree _).prop_of_iso
      ((ObjectProperty.ι _).mapIso (tildeEquiv.counitIso.app F))
      (isFiniteLocallyFree_tilde (moduleSpecΓFunctor.obj F.obj))
  -- The single member of the cover is `X.isoSpec.inv` by definition (`Scheme.coverOfIsIso_X`,
  -- `Scheme.coverOfIsIso_f`). Neither `rw` nor `simp` can apply these equations: the goal states
  -- `E.obj : SheafOfModules X.ringCatSheaf` as an object of `X.Modules`, which is not
  -- type-correct at reducible transparency.
  exact (Scheme.Modules.isFiniteLocallyFree _).prop_of_iso
    (eqToIso (C := (Spec Γ(X, ⊤)).Modules) (pullback_obj_obj X.isoSpec.inv E)) hF

variable {X : Scheme.{u}}

/-- A quasicoherent sheaf on any scheme has a left dual in `QuasicoherentSheaf X` if and only
if it is finite locally free. -/
theorem nonempty_hasLeftDual_iff_isFiniteLocallyFree (E : QuasicoherentSheaf X) :
    Nonempty (HasLeftDual E) ↔ Scheme.Modules.isFiniteLocallyFree X E.obj := by
  refine ⟨fun hE ↦ ?_, nonempty_hasLeftDual_of_isFiniteLocallyFree E⟩
  refine (Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback X.affineCover E.obj).mpr
    fun i ↦ ?_
  let F := (pullback (X.affineCover.f i)).obj E
  have hF := (nonempty_hasLeftDual_iff_isFiniteLocallyFree_of_isAffine F).mp
    (E.nonempty_hasLeftDual_pullback (X.affineCover.f i) hE)
  exact (Scheme.Modules.isFiniteLocallyFree _).prop_of_iso
    (eqToIso (C := (X.affineCover.X i).Modules) (pullback_obj_obj (X.affineCover.f i) E)) hF

/-- A quasicoherent sheaf on any scheme has a right dual in `QuasicoherentSheaf X` if and only
if it is finite locally free. -/
theorem nonempty_hasRightDual_iff_isFiniteLocallyFree (E : QuasicoherentSheaf X) :
    Nonempty (HasRightDual E) ↔ Scheme.Modules.isFiniteLocallyFree X E.obj := by
  rw [← nonempty_hasLeftDual_iff_isFiniteLocallyFree]
  constructor
  · rintro ⟨hE⟩
    let _ : HasRightDual E := hE
    exact ⟨BraidedCategory.hasLeftDualOfHasRightDual⟩
  · rintro ⟨hE⟩
    let _ : HasLeftDual E := hE
    exact ⟨BraidedCategory.hasRightDualOfHasLeftDual⟩

end

end TauCeti.AlgebraicGeometry.QuasicoherentSheaf
