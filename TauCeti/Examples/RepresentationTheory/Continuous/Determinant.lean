/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Continuous.Determinant

/-!
# Examples: the determinant character

* On the zero module the determinant character is `1`.
* The trivial representation has trivial determinant character.
* The determinant of a rank-one character line is the character itself, not its inverse.
-/

open TauCeti ContinuousRep

variable {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]

-- On the zero module the determinant character is `1`.
example (ρ : ContinuousRep Γ A PUnit) : ρ.det = 1 :=
  det_of_subsingleton ρ

-- The trivial representation on `A²` has trivial determinant character.
example : (trivial Γ A (Fin 2 → A)).det = 1 :=
  det_trivial

-- The determinant of a character line is the character.
example [IsTopologicalRing A] (χ : Γ →ₜ* Aˣ) : (ofCharacter χ).det = χ :=
  det_ofCharacter χ
