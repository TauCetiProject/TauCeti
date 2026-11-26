/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Affine
import TauCeti.AlgebraicGeometry.Sites.Nisnevich.EtaleComparison

/-!
# Checks for Nisnevich coverings

The identity is a Nisnevich covering, while the spectrum of a quadratic field extension is not a
Nisnevich covering of the spectrum of the base field: its residue field extension is not an
isomorphism.

Presheaves of sets, of abelian groups and of `Λ`-modules on the small Nisnevich site can be
sheafified, sheaves of `Λ`-modules form a Grothendieck abelian category, and the inverse image of
the comparison morphism `Sh(X_ét) → Sh(X_Nis)` applies to Nisnevich sheafifications of presheaves
of `Λ`-modules.
-/

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

universe u

namespace TauCeti.Examples

-- `{𝟙 X}` is a Nisnevich covering.
example (X : Scheme.{u}) : IsNisnevichCovering (fun _ : PUnit.{1} ↦ 𝟙 X) :=
  isNisnevichCovering_of_isIso _

-- A quadratic field extension is not a Nisnevich covering.
example (k K : Type u) [Field k] [Field K] [Algebra k K] (h : Module.finrank k K = 2) :
    ¬ IsNisnevichCovering
      (fun _ : PUnit.{u + 1} ↦ Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  not_isNisnevichCovering_specMap_algebraMap_of_finrank_ne_one k K (by omega)

example (X : Scheme.{u}) : HasSheafify X.smallNisnevichTopology (Type u) := inferInstance

example (X : Scheme.{u}) : HasSheafify X.smallNisnevichTopology AddCommGrpCat.{u} := inferInstance

example (X : Scheme.{u}) (Λ : Type u) [Ring Λ] :
    HasSheafify X.smallNisnevichTopology (ModuleCat.{u} Λ) :=
  inferInstance

example (X : Scheme.{u}) (Λ : Type u) [Ring Λ] :
    IsGrothendieckAbelian.{u} (Sheaf X.smallNisnevichTopology (ModuleCat.{u} Λ)) :=
  inferInstance

-- Nisnevich sheafification followed by the inverse image to the étale site is exact.
example (X : Scheme.{u}) (Λ : Type u) [Ring Λ] :
    PreservesFiniteLimits (presheafToSheaf X.smallNisnevichTopology (ModuleCat.{u} Λ) ⋙
      X.etaleToNisnevichPullback (ModuleCat.{u} Λ)) :=
  inferInstance

end TauCeti.Examples
