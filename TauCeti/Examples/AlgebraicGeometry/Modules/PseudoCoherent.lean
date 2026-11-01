/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.FinitePresentation
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation

/-!
# Tests for pseudo-coherent modules on schemes

Free modules of finite rank and zero modules are pseudo-coherent on every scheme. Over a
noetherian ring `R`, the sheaf on `Spec R` associated with any cyclic module `R ⧸ I` is
pseudo-coherent. Its resolution gives a finite global presentation; local resolutions on an
arbitrary scheme give finite presentation and quasi-coherence. Conversely, a sheaf associated
to a module that is not finitely presented cannot be pseudo-coherent.
-/

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- *IsPseudoCoherentSheaf_free*: on every scheme, the free module of rank `n` is
pseudo-coherent. -/
example (X : Scheme.{u}) (n : ℕ) :
    IsPseudoCoherent (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) :=
  isPseudoCoherent_free _

/-- *IsPseudoCoherentSheaf_zero*: on every scheme, the zero module is pseudo-coherent. -/
example (X : Scheme.{u}) : IsPseudoCoherent (0 : X.Modules) :=
  .of_isZero (isZero_zero _)

/-- An additional cyclic example: over a noetherian ring `R`, the sheaf associated with
`R ⧸ I` is pseudo-coherent for every ideal `I`. -/
example (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) :
    (tilde (ModuleCat.of R (R ⧸ I))).IsPseudoCoherent :=
  isPseudoCoherent_tilde .of_isNoetherianRing

/-- Local resolutions give finite presentation on every open restriction, even when there is
no single resolving open for the whole scheme. -/
example {X : Scheme.{u}} {F : X.Modules} (h : F.IsPseudoCoherent) (U : X.Opens) :
    (F.restrict U.ι).IsFinitePresentation :=
  (h.restrict U.ι).isFinitePresentation

/-- The quasi-coherence consequence is available without unfolding the resolution predicate. -/
example {X : Scheme.{u}} {F : X.Modules} (h : F.IsPseudoCoherent) : F.IsQuasicoherent :=
  h.isQuasicoherent

/-- A cyclic module over a Noetherian ring gives a finite global sheaf presentation by
extracting the first two terms of its finite free resolution. This includes nonreduced rings
and modules of infinite projective dimension. -/
example (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) :
    ∃ p : (tilde (ModuleCat.of R (R ⧸ I))).Presentation, p.IsFinite :=
  (hasFiniteFreeResolution_tilde (M := ModuleCat.of R (R ⧸ I))
    TauCeti.Huber.IsPseudoCoherentOver.of_isNoetherianRing).exists_isFinite_presentation

/-- On an affine scheme, failure of finite presentation of a module rules out local
finite free resolutions of its associated sheaf. -/
example {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (hM : ¬ Module.FinitePresentation R M) : ¬ (tilde M).IsPseudoCoherent := by
  intro h
  exact hM ((ModuleCat.isFinitePresentation_tilde_iff M).mp h.isFinitePresentation)

/-- Zero sheaves on arbitrary schemes also satisfy the finite-presentation consequence. -/
example (X : Scheme.{u}) : (0 : X.Modules).IsFinitePresentation :=
  (IsPseudoCoherent.of_isZero (isZero_zero _)).isFinitePresentation

end AlgebraicGeometry.Scheme.Modules
