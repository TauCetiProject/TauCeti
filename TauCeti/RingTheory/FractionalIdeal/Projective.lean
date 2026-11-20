/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Invertible fractional ideals are finite projective

The finite generation and projectivity of invertible submodules give the corresponding
instances for invertible fractional ideals. These let fractional ideals represent objects
in the category of finite projective modules, and hence classes in projective `K₀`.
Over a Dedekind domain every nonzero fractional ideal is invertible, so every fractional ideal is
projective.
-/

public section

namespace FractionalIdeal

variable {R P : Type*} [CommRing R] {S : Submonoid R} [CommRing P] [Algebra R P]

/-- An invertible fractional ideal is finitely generated as a module. -/
instance finite_units (I : (FractionalIdeal S P)ˣ) : Module.Finite R (I : FractionalIdeal S P) :=
  Module.Finite.of_fg (fg_unit I)

/-- An invertible fractional ideal in a faithful algebra is projective as a module. -/
instance projective_units [FaithfulSMul R P] (I : (FractionalIdeal S P)ˣ) :
    Module.Projective R (I : FractionalIdeal S P) :=
  Submodule.projective_of_isUnit ((coeSubmoduleHom S P).isUnit_map I.isUnit)

open scoped nonZeroDivisors in
/-- Every fractional ideal of a Dedekind domain is projective as a module: the zero ideal is the
zero module, and a nonzero fractional ideal is invertible. -/
instance projective {K : Type*} [Field K] [Algebra R K] [IsDedekindDomain R] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) : Module.Projective R I := by
  rcases eq_or_ne I 0 with rfl | hI
  · have : Subsingleton (0 : FractionalIdeal R⁰ K) :=
      ⟨fun x y ↦ Subtype.ext <| by rw [(mem_zero_iff _).1 x.2, (mem_zero_iff _).1 y.2]⟩
    infer_instance
  · exact inferInstanceAs (Module.Projective R ((Units.mk0 I hI : (FractionalIdeal R⁰ K)ˣ) :
      FractionalIdeal R⁰ K))

end FractionalIdeal
