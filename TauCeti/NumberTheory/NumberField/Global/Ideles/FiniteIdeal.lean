/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Fractional ideals of ideles

This file relates the fractional ideal of an idele's finite component to its valuations at
finite places.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  IsDedekindDomain.FiniteAdeleRing NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The fractional ideal of an idele's finite component is trivial exactly when the idele is a
unit at every finite place. -/
@[simp] theorem toFractionalIdeal_toFiniteIdele_eq_one_iff {x : IdeleGroup (𝓞 K) K} :
    toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K x) = 1 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp only [toFractionalIdeal_eq_one_iff, adicOrd_eq_zero_iff, IdeleGroup.coe_toFiniteIdele,
    HeightOneSpectrum.coe_ideleFiniteCoord]

end TauCeti.GlobalNumberFields
