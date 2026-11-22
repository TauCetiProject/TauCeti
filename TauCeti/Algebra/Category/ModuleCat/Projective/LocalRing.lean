/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Retract
public import TauCeti.RingTheory.LocalRing.Module

/-!
# Projective retracts over a local ring

A finite module over a local ring that admits a nonzero projective retract also admits `R` itself
as a retract (`CategoryTheory.Retract.nonempty_retract_ring_of_projective`), since a finitely
generated projective module over a local ring is free.

## Main results

* `CategoryTheory.Retract.nonempty_retract_ring_of_projective`: a nonzero projective retract of a
  finite module over a local ring produces a retract from `R`.
-/

public section

universe u

open CategoryTheory

namespace CategoryTheory.Retract

/-- A nonzero projective retract of a finite module over a local ring `R` yields a retract of `R`
itself into the module. -/
theorem nonempty_retract_ring_of_projective {R : Type u} [CommRing R] [_root_.IsLocalRing R]
    {M P : ModuleCat.{u} R} [Module.Finite R M] [Projective P] [Nontrivial P]
    (ret : Retract P M) :
    Nonempty (Retract (ModuleCat.of R R) M) := by
  have : Module.Finite R P := .of_surjective ret.r.hom
    (Function.LeftInverse.surjective fun p ↦ ConcreteCategory.congr_hom ret.retract p)
  have : Module.Projective R P := (IsProjective.iff_projective P).2 inferInstance
  have : Module.Free R P := Module.free_of_projective_of_isLocalRing
  let b := Module.Free.chooseBasis R P
  obtain ⟨i₀⟩ : Nonempty (Module.Free.ChooseBasisIndex R P) := by
    by_contra! hemp
    exact not_subsingleton P b.repr.subsingleton
  let _ := Classical.decEq (Module.Free.ChooseBasisIndex R P)
  refine ⟨Retract.trans
    { i := ModuleCat.ofHom (LinearMap.toSpanSingleton R P (b i₀))
      r := ModuleCat.ofHom (b.coord i₀)
      retract := ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by
        simp [b.coord_apply] }
    ret⟩

end CategoryTheory.Retract
