/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.Torsor.GaloisMap
import TauCeti.RingTheory.Etale.Torsor.Trivial
import Mathlib.Data.ZMod.Basic

/-!
# Tests for the Galois isomorphisms of a finite étale torsor

These checks fix the conventions of `galoisMap` and `iterGaloisMap`: the first tensor factor is
untwisted, each later factor is moved by its own group coordinate (vertex coordinates), and on
the regular three-cycle torsor the support of a Galois value distinguishes right translation from
its inverse.
-/

namespace TauCeti.Algebra.IsFiniteEtaleTorsor

open _root_.TensorProduct PiTensorProduct

variable {G A B : Type*} [Group G] [Finite G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B] [IsFiniteEtaleTorsor G A B]

/-- *galois_left*: the first tensor factor is untwisted. -/
example (b : B) (g : G) : galoisMap G A B (b ⊗ₜ 1) g = b := by simp

/-- *galois_right*: the second tensor factor carries the action. -/
example (b : B) (g : G) : galoisMap G A B (1 ⊗ₜ b) g = g • b := by simp

/-- *galois_identity*: evaluation at the identity is multiplication. -/
example (b c : B) : galoisMap G A B (b ⊗ₜ c) 1 = b * c := by simp

/-- *galois_zero*: the zero-fold group product gives `b₀ ↦ b₀`. -/
example (b : Fin 1 → B) (g : Fin 0 → G) : iterGaloisMap G A B 0 (tprod A b) g = b 0 := by simp

/-- *galois_one*: `b₀ ⊗ b₁` is the function `g ↦ b₀ * g • b₁`. -/
example (b : Fin 2 → B) (g : Fin 1 → G) :
    iterGaloisMap G A B 1 (tprod A b) g = b 0 * g 0 • b 1 := by simp

/-- *galois_two*: `b₀ ⊗ b₁ ⊗ b₂` is the function `(g, h) ↦ b₀ * g • b₁ * h • b₂`; the last factor
is moved by `h`, not by `g * h`. -/
example (b : Fin 3 → B) (g h : G) :
    iterGaloisMap G A B 2 (tprod A b) ![g, h] = b 0 * g • b 1 * h • b 2 := by
  simp [Fin.prod_univ_two, mul_assoc]

/-- *galois_faces_two*: inserting `1` into the three tensor positions of `a ⊗ b` gives, in
order, `g • (a * (g⁻¹ * h) • b)`, `a * h • b` and `a * g • b`. Deleting the zeroth vertex rebases
the remaining ones by `g⁻¹`; deleting another vertex omits its coordinate. -/
example (a b : B) (g h : G) :
    iterGaloisMap G A B 2 (tprod A ![1, a, b]) ![g, h] = g • (a * (g⁻¹ * h) • b) ∧
      iterGaloisMap G A B 2 (tprod A ![a, 1, b]) ![g, h] = a * h • b ∧
      iterGaloisMap G A B 2 (tprod A ![a, b, 1]) ![g, h] = a * g • b := by
  simp [Fin.prod_univ_two, mul_smul]

end TauCeti.Algebra.IsFiniteEtaleTorsor

namespace TauCeti.Algebra

open _root_.TensorProduct

attribute [local instance] rightRegularMulSemiringAction

/-- *galois_convention_three*: on the regular three-cycle torsor, `galoisMap (δ₀ ⊗ δ₁)` is `δ₀`
at group coordinate one and `0` at group coordinate two; the inverse-translation convention would
put the support at coordinate two. -/
example : IsFiniteEtaleTorsor.galoisMap (Multiplicative (ZMod 3)) ℚ (Multiplicative (ZMod 3) → ℚ)
      (Pi.single (Multiplicative.ofAdd 0) 1 ⊗ₜ Pi.single (Multiplicative.ofAdd 1) 1)
      (Multiplicative.ofAdd 1) = Pi.single (Multiplicative.ofAdd 0) 1 ∧
    IsFiniteEtaleTorsor.galoisMap (Multiplicative (ZMod 3)) ℚ (Multiplicative (ZMod 3) → ℚ)
      (Pi.single (Multiplicative.ofAdd 0) 1 ⊗ₜ Pi.single (Multiplicative.ofAdd 1) 1)
      (Multiplicative.ofAdd 2) = 0 := by
  refine ⟨?_, ?_⟩ <;> ext x <;> by_cases hx : x = 1
  · subst x
    simp
  · simp [hx]
  · subst x
    have h : Multiplicative.ofAdd (2 : ZMod 3) ≠ Multiplicative.ofAdd 1 := by decide
    simp [h]
  · simp [Pi.single_apply, hx]

end TauCeti.Algebra
