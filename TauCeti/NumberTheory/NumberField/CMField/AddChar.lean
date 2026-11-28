/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.Global.Adeles.AddChar
import TauCeti.Algebra.Group.AddChar.Star

/-!
# Standard additive characters of the adeles of a CM field

The standard additive characters of the finite and infinite adeles of a CM field are invariant
under complex conjugation. At the infinite places this follows from invariance of the real part;
on the finite adeles it follows from invariance under transport along field isomorphisms.
Consequently, both characters are trivial on skew-adjoint adeles. These properties supply the
character identities used to construct adelic Heisenberg data from skew-hermitian forms.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleAddChar_star` and
  `TauCeti.GlobalNumberFields.infiniteAdeleAddChar_star`: conjugation invariance of the standard
  characters.
* `TauCeti.GlobalNumberFields.infiniteAdeleTrace_star`: conjugation invariance of the infinite
  adelic trace.
* `TauCeti.GlobalNumberFields.finiteAdeleAddChar_eq_one_of_mem_skewAdjoint` and
  `TauCeti.GlobalNumberFields.infiniteAdeleAddChar_eq_one_of_mem_skewAdjoint`: triviality on
  skew-adjoint adeles.
-/

public section

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

namespace TauCeti.GlobalNumberFields

/-! ### Invariance of the standard characters under conjugation -/

/-- The standard character `ψ_f` of the finite adeles of a CM field is invariant under
conjugation. -/
@[simp]
theorem finiteAdeleAddChar_star (a : 𝔸ᶠ[E]) :
    finiteAdeleAddChar E (star a) = finiteAdeleAddChar E a := by
  rw [← IsCMField.finiteAdeleConj_apply, IsCMField.finiteAdeleConj_def,
    finiteAdeleAddChar_finiteAdeleEquiv]

/-- The standard character `ψ_f` of the finite adeles of a CM field is trivial on the skew-adjoint
finite adeles. -/
theorem finiteAdeleAddChar_eq_one_of_mem_skewAdjoint {a : 𝔸ᶠ[E]} (ha : a ∈ skewAdjoint 𝔸ᶠ[E]) :
    finiteAdeleAddChar E a = 1 :=
  letI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  AddChar.map_eq_one_of_mem_skewAdjoint E _ finiteAdeleAddChar_star ha

/-- The trace of the infinite adeles of a CM field is invariant under conjugation. -/
@[simp]
theorem infiniteAdeleTrace_star (a : InfiniteAdeleRing E) :
    infiniteAdeleTrace E (star a) = infiniteAdeleTrace E a := by
  simp only [infiniteAdeleTrace_apply, InfiniteAdeleRing.extensionEmbedding_star_apply,
    Complex.conj_re]

/-- The standard character `ψ_∞` of the infinite adeles of a CM field is invariant under
conjugation. -/
@[simp]
theorem infiniteAdeleAddChar_star (a : InfiniteAdeleRing E) :
    infiniteAdeleAddChar E (star a) = infiniteAdeleAddChar E a := by
  rw [infiniteAdeleAddChar_apply, infiniteAdeleAddChar_apply, infiniteAdeleTrace_star]

/-- The standard character `ψ_∞` of the infinite adeles of a CM field is trivial on the
skew-adjoint infinite adeles. -/
theorem infiniteAdeleAddChar_eq_one_of_mem_skewAdjoint {a : InfiniteAdeleRing E}
    (ha : a ∈ skewAdjoint (InfiniteAdeleRing E)) : infiniteAdeleAddChar E a = 1 :=
  letI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  AddChar.map_eq_one_of_mem_skewAdjoint E _ infiniteAdeleAddChar_star ha

end TauCeti.GlobalNumberFields
