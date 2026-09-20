/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.ClassFunction` is the object the extensionality principle below is stated for.
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
-- `TauCeti.exists_isConj_normalForm` is what the principle runs on, and `TauCeti.diagGL`,
-- `TauCeti.jordanGL` and `TauCeti.GL2NonSplitTorusHom` occur in its hypotheses.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NormalForm

/-!
# Class functions on `GL₂(𝔽_q)` are determined by the four normal forms

Over a finite field `F` with a supplied degree-`2` extension `E/F`, every element of `GL₂(F)` is
conjugate to a central scalar, to a split semisimple `diag (a, b)` with `a ≠ b`, to a Jordan block
`!![a, 1; 0, a]`, or to the matrix of multiplication by an element of `E` outside `F`
(`TauCeti.exists_isConj_normalForm`).  A class function is constant on conjugacy classes, so two
class functions agreeing on those four families are equal.

This is the extensionality principle behind every row of the character table of `GL₂(𝔽_q)`: the
character values there are computed at the four normal forms one family at a time, and this is
what turns four such computations into an identity of class functions.

## Main results

* `TauCeti.ClassFunction.ext_gl2NormalForm`: two class functions on `GL₂(F)` agreeing on
  the four normal forms are equal.
-/

public section

open Matrix

namespace TauCeti

namespace ClassFunction

variable {F : Type*} [Field F] [Finite F] {k : Type*} [Semiring k]

/-- **Two class functions on `GL₂(F)` that agree on the four normal forms are equal.**  `F` is a
finite field and `E/F` a supplied degree-`2` extension, which is what makes the elliptic family
available; the four hypotheses are read at the representatives of
`TauCeti.exists_isConj_normalForm`. -/
theorem ext_gl2NormalForm (E : Type*) [Field E] [Algebra F E]
    (hE : Module.finrank F E = 2) {f₁ f₂ : ClassFunction k (GL (Fin 2) F)}
    (hscalar : ∀ a : Fˣ, f₁.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      f₂.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) a))
    (hdiag : ∀ a b : Fˣ, a ≠ b → f₁.1 (diagGL ![a, b]) = f₂.1 (diagGL ![a, b]))
    (hjordan : ∀ a : Fˣ, f₁.1 (jordanGL a (1 : F)) = f₂.1 (jordanGL a (1 : F)))
    (helliptic : ∀ x : Eˣ, (x : E) ∉ Set.range (algebraMap F E) →
      f₁.1 (GL2NonSplitTorusHom F E hE x) = f₂.1 (GL2NonSplitTorusHom F E hE x)) :
    f₁ = f₂ := by
  refine Subtype.ext (funext fun g => ?_)
  rcases exists_isConj_normalForm E hE g with ⟨a, rfl⟩ | ⟨a, b, hab, h⟩ | ⟨a, h⟩ | ⟨x, hx, h⟩
  · exact hscalar a
  · rw [eq_of_isConj f₁ h, eq_of_isConj f₂ h]
    exact hdiag a b hab
  · rw [eq_of_isConj f₁ h, eq_of_isConj f₂ h]
    exact hjordan a
  · rw [eq_of_isConj f₁ h, eq_of_isConj f₂ h]
    exact helliptic x hx

end ClassFunction

end TauCeti
