/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent

/-!
# Tests for pseudo-coherent modules on schemes

Free modules of finite rank and zero modules are pseudo-coherent on every scheme. Over a
noetherian ring `R`, the sheaf on `Spec R` associated with a cyclic module `R ⧸ I` is
pseudo-coherent, although it is not free.
-/

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- *test_free*: on every scheme, the free module of rank `n` is pseudo-coherent. -/
example (X : Scheme.{u}) (n : ℕ) :
    IsPseudoCoherent (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) :=
  isPseudoCoherent_free _

/-- *test_zero*: on every scheme, the zero module is pseudo-coherent. -/
example (X : Scheme.{u}) : IsPseudoCoherent (0 : X.Modules) :=
  .of_isZero (isZero_zero _)

/-- *test_noetherian*: over a noetherian ring `R`, the sheaf associated with `R ⧸ I` is
pseudo-coherent. -/
example (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) :
    (tilde (ModuleCat.of R (R ⧸ I))).IsPseudoCoherent :=
  isPseudoCoherent_tilde .of_isNoetherianRing

end AlgebraicGeometry.Scheme.Modules
