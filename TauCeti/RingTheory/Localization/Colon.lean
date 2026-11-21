/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Colon
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Localization of colon ideals

Colon by a finitely generated ideal commutes with localization. The numerator ideal need not
be finitely generated, and the ambient semiring need not be Noetherian. This compatibility
allows sectionwise colon ideals to define quasi-coherent ideal sheaves.
-/

public section

/-- Colon by a finitely generated ideal commutes with localization of commutative semirings. -/
theorem IsLocalization.map_colon {R : Type*} [CommSemiring R]
    (p : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization p S]
    (I J : Ideal R) (hJ : J.FG) :
    (I.colon (J : Set R)).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon (J.map (algebraMap R S) : Set S) := by
  simpa only [Ideal.localized'_eq_map] using
    Submodule.map_colon_localized' S I J hJ p (Algebra.linearMap R S)
