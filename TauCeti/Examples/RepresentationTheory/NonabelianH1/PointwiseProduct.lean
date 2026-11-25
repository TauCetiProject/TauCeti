/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.ZMod.Basic

/-!
# Pointwise products of homomorphisms to `S₃`

For a group `G` acting trivially on a nonabelian group `A`, the first cohomology `H¹(G, A)` is the
set of continuous homomorphisms `G → A` modulo conjugation
(`TauCeti.NonabelianH1.equivOfTrivial`). It is only a pointed set: pointwise multiplication need
not preserve homomorphisms. For `A = S₃ = Perm (Fin 3)` and two homomorphisms from a quadratic
quotient `G → ℤ/2` sending its generator to the distinct transpositions `(0 1)` and `(1 2)`, the
pointwise product sends the generator to a 3-cycle, which cannot be the image of an element of
order two.
-/

public section

open Equiv

namespace TauCeti.NonabelianPointwiseExample

/-- The homomorphism `ℤ/2 → Perm (Fin 3)` sending the generator to an involution `τ`. -/
def quadraticHom (τ : Perm (Fin 3)) (hτ : τ * τ = 1) :
    Multiplicative (ZMod 2) →* Perm (Fin 3) where
  toFun x := if x.toAdd = 0 then 1 else τ
  map_one' := by simp
  map_mul' x y := by
    induction x using Multiplicative.rec with | ofAdd a => ?_
    induction y using Multiplicative.rec with | ofAdd b => ?_
    fin_cases a <;> fin_cases b <;> simp [hτ] <;> rfl

/-- `quadraticHom τ` sends the generator of `ℤ/2` to `τ`. -/
theorem quadraticHom_ofAdd_one (τ : Perm (Fin 3)) (hτ : τ * τ = 1) :
    quadraticHom τ hτ (Multiplicative.ofAdd 1) = τ := by
  simp [quadraticHom]

/-- **Pointwise products of homomorphisms to `S₃` need not be homomorphisms.** If `φ₁ g` and
`φ₂ g` are the transpositions `(0 1)` and `(1 2)`, no homomorphism agrees with `x ↦ φ₁ x * φ₂ x`:
it would send `g²` to the square of the 3-cycle `(0 1)(1 2)`, which is not `1`, while
`φ₁ (g²) * φ₂ (g²) = 1`. -/
theorem not_exists_monoidHom_eq_mul {Γ : Type*} [Group Γ] (φ₁ φ₂ : Γ →* Perm (Fin 3)) (g : Γ)
    (h₁ : φ₁ g = swap 0 1) (h₂ : φ₂ g = swap 1 2) :
    ¬ ∃ ψ : Γ →* Perm (Fin 3), ∀ x, ψ x = φ₁ x * φ₂ x := by
  rintro ⟨ψ, hψ⟩
  have h := hψ (g * g)
  rw [map_mul, map_mul, map_mul, hψ, h₁, h₂] at h
  exact absurd h (by decide)

/-- The two homomorphisms from a quadratic quotient `χ : Γ →* ℤ/2` to `S₃` sending the generator to
`(0 1)` and to `(1 2)` have a pointwise product that is not a homomorphism. -/
theorem not_exists_monoidHom_eq_mul_quadratic {Γ : Type*} [Group Γ]
    (χ : Γ →* Multiplicative (ZMod 2)) (hχ : Function.Surjective χ) :
    ¬ ∃ ψ : Γ →* Perm (Fin 3), ∀ x,
      ψ x = quadraticHom (swap 0 1) (swap_mul_self 0 1) (χ x) *
        quadraticHom (swap 1 2) (swap_mul_self 1 2) (χ x) := by
  obtain ⟨g, hg⟩ := hχ (Multiplicative.ofAdd 1)
  exact not_exists_monoidHom_eq_mul ((quadraticHom _ (swap_mul_self 0 1)).comp χ)
    ((quadraticHom _ (swap_mul_self 1 2)).comp χ) g
    (by simp [hg, quadraticHom_ofAdd_one]) (by simp [hg, quadraticHom_ofAdd_one])

end TauCeti.NonabelianPointwiseExample
