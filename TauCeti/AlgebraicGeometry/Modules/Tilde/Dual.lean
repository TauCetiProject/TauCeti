/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Dualizable
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Monoidal
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Dualizable quasicoherent sheaves on an affine scheme

A quasicoherent sheaf `E` on `Spec R` is dualizable in the symmetric monoidal category
`QuasicoherentSheaf (Spec R)` if and only if its module of global sections is finitely generated
and projective, if and only if `E` is finite locally free.

Since `M ↦ M~` is a fully faithful monoidal functor whose essential image consists of the
quasicoherent sheaves, exact pairings between quasicoherent sheaves on `Spec R` are the images of
exact pairings between `R`-modules, and an `R`-module is dualizable exactly when it is finite
projective (`ModuleCat.nonempty_hasLeftDual_iff_finite_projective`). The sheaf associated with a
finite projective module is finite locally free
(`TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde`), and finite locally free sheaves are
dualizable
(`TauCeti.AlgebraicGeometry.QuasicoherentSheaf.nonempty_hasLeftDual_of_isFiniteLocallyFree`).

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.nonempty_hasLeftDual_iff_finite_projective`:
  a quasicoherent sheaf on `Spec R` is dualizable if and only if its global sections form a
  finite projective `R`-module;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.nonempty_hasLeftDual_iff_isFiniteLocallyFree`:
  a quasicoherent sheaf on `Spec R` is dualizable if and only if it is finite locally free.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace QuasicoherentSheaf

variable {R : CommRingCat.{u}}

/-- A quasicoherent sheaf on `Spec R` is dualizable in `QuasicoherentSheaf (Spec R)` if and only if
its global sections form a finitely generated projective `R`-module. -/
theorem nonempty_hasLeftDual_iff_finite_projective (E : QuasicoherentSheaf (Spec R)) :
    Nonempty (HasLeftDual E) ↔ Module.Finite R (moduleSpecΓFunctor.obj E.obj) ∧
      Module.Projective R (moduleSpecΓFunctor.obj E.obj) := by
  rw [← ModuleCat.nonempty_hasLeftDual_iff_finite_projective]
  constructor
  · rintro ⟨h⟩
    -- The exact pairing of `ᘁE` and `E` is one between sheaves associated with modules, so it
    -- comes from an exact pairing of `R`-modules.
    let D := ᘁE
    -- The monoidal structure of `QuasicoherentSheaf (Spec R)` is that of `(Spec R).Modules`, so
    -- the pairing is also one between the underlying sheaves.
    let : ExactPairing (C := (Spec R).Modules) D.obj E.obj :=
      { coevaluation' := (η_ D E).hom
        evaluation' := (ε_ D E).hom
        coevaluation_evaluation' := congrArg (·.hom) (ExactPairing.coevaluation_evaluation D E)
        evaluation_coevaluation' := congrArg (·.hom) (ExactPairing.evaluation_coevaluation D E) }
    let : ExactPairing ((tilde.functor R).obj (moduleSpecΓFunctor.obj D.obj))
        ((tilde.functor R).obj (moduleSpecΓFunctor.obj E.obj)) :=
      exactPairingCongr (C := (Spec R).Modules) (X' := D.obj) (Y' := E.obj)
        ((ObjectProperty.ι _).mapIso (tildeEquiv.counitIso.app D))
        ((ObjectProperty.ι _).mapIso (tildeEquiv.counitIso.app E))
    let : ExactPairing (moduleSpecΓFunctor.obj D.obj) (moduleSpecΓFunctor.obj E.obj) :=
      .ofFullyFaithful (tilde.functor R) _ _
    exact ⟨⟨moduleSpecΓFunctor.obj D.obj⟩⟩
  · rintro ⟨h⟩
    -- The image of the dual of the global sections is a dual of `E`.
    let M := moduleSpecΓFunctor.obj E.obj
    let h₁ : ExactPairing (C := (Spec R).Modules) ((tildeEquiv (R := R)).functor.obj (ᘁM)).obj
        ((tildeEquiv (R := R)).functor.obj M).obj :=
      (tilde.functor R).mapExactPairing (ᘁM) M
    -- `QuasicoherentSheaf (Spec R)` is a full monoidal subcategory of `(Spec R).Modules`.
    let : ExactPairing ((tildeEquiv (R := R)).functor.obj (ᘁM))
        ((tildeEquiv (R := R)).functor.obj M) :=
      @ObjectProperty.exactPairingFullSubcategory (Spec R).Modules _ _ _
        (Scheme.Modules.isMonoidal_isQuasicoherent (Spec R)) _ _ h₁
    let : ExactPairing ((tildeEquiv (R := R)).functor.obj (ᘁM)) E :=
      exactPairingCongrRight (Y' := (tildeEquiv (R := R)).functor.obj M)
        (tildeEquiv.counitIso.app E).symm
    exact ⟨⟨(tildeEquiv (R := R)).functor.obj (ᘁM)⟩⟩

/-- A quasicoherent sheaf on `Spec R` is dualizable in `QuasicoherentSheaf (Spec R)` if and only if
it is finite locally free. -/
theorem nonempty_hasLeftDual_iff_isFiniteLocallyFree (E : QuasicoherentSheaf (Spec R)) :
    Nonempty (HasLeftDual E) ↔ Scheme.Modules.isFiniteLocallyFree (Spec R) E.obj := by
  refine ⟨fun h ↦ ?_, nonempty_hasLeftDual_of_isFiniteLocallyFree E⟩
  obtain ⟨_, _⟩ := (nonempty_hasLeftDual_iff_finite_projective E).mp h
  exact (Scheme.Modules.isFiniteLocallyFree (Spec R)).prop_of_iso
    ((ObjectProperty.ι _).mapIso (tildeEquiv.counitIso.app E))
    (isFiniteLocallyFree_tilde (moduleSpecΓFunctor.obj E.obj))

end QuasicoherentSheaf

end

end AlgebraicGeometry

end TauCeti
