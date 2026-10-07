/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Dual

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
