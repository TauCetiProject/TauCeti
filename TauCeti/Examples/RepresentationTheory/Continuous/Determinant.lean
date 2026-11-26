/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.ZMod
import TauCeti.RepresentationTheory.Continuous.Determinant.Basic
import TauCeti.RepresentationTheory.Continuous.Determinant.Operations

/-!
# Examples: the determinant character

* On the zero module the determinant character is `1`.
* The trivial representation has trivial determinant character.
* The determinant of a rank-one character line is the character itself, not its inverse.
* The determinant of the direct sum of two character lines is the product of the characters.
* After the nonflat coefficient change `ℤ → ℤ/2`, an element acting by `-1` on a character line
  over `ℤ` acts on the base-changed line with determinant `1`: the determinant character commutes
  with every coefficient change, flat or not.
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

-- The determinant of the direct sum of two character lines is the product `χψ`.
example [IsTopologicalRing A] (χ ψ : Γ →ₜ* Aˣ) :
    ((ofCharacter χ).prod (ofCharacter ψ)).det = (χ : Γ →* Aˣ) * ψ := by
  rw [det_prod, det_ofCharacter, det_ofCharacter]

-- After the nonflat coefficient change `ℤ → ℤ/2`, an element acting by `-1` acts with
-- determinant `1`.
open scoped TensorProduct in
example (χ : Γ →ₜ* ℤˣ) (g : Γ) (hg : χ g = -1) [TopologicalSpace (ZMod 2 ⊗[ℤ] ℤ)]
    [IsModuleTopology (ZMod 2) (ZMod 2 ⊗[ℤ] ℤ)] :
    ((ofCharacter χ).baseChange (ZMod 2)).det g = 1 := by
  ext
  rw [coe_det_baseChange_apply, det_ofCharacter, MonoidHom.coe_ofClass, hg]
  decide
