/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.WeightSpace

/-!
# Weight spaces of the line of a linear character

The line `Representation.ofLinearCharacter χ` of a linear character `χ : G →* kˣ` has a single
weight: `G` acts through `χ` on every vector of it, and, over a commutative ring without zero
divisors, through a different linear character on no nonzero vector of it.

So in a direct sum of lines of linear characters, the vectors of weight `χ` lie in the summands
whose character is `χ`; such a sum has a nonzero vector of weight `χ` exactly when `χ` is one of
its characters. This is how the cancellation of linear characters from semisimple representations
detects which characters occur.

## Main results

* `Representation.weightSpace_ofLinearCharacter_self`: every vector of the line of `χ` has
  weight `χ`.
* `Representation.weightSpace_ofLinearCharacter_eq_bot`: the line of `ψ` has no nonzero vector on
  which `G` acts through a different linear character.
-/

public section

namespace Representation

variable {k G : Type*} [Monoid G]

/-- **The line of `ψ` has no vector of weight `χ ≠ ψ`.** If `ψ` and `χ` are different linear
characters, no nonzero vector of the line of `ψ` is acted on through `χ`. -/
@[simp]
theorem weightSpace_ofLinearCharacter_eq_bot [CommRing k] [NoZeroDivisors k] {ψ χ : G →* kˣ}
    (h : ψ ≠ χ) :
    (ofLinearCharacter ψ).weightSpace ((Units.coeHom k).comp χ) = ⊥ := by
  obtain ⟨g, hg⟩ : ∃ g, (ψ g : k) ≠ χ g := by
    by_contra! H
    exact h (MonoidHom.ext fun g ↦ Units.ext (H g))
  refine eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot k).mpr ?_
  have hx := mem_weightSpace.mp hx g
  rw [ofLinearCharacter_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul,
    mul_comm] at hx
  have hx' : x * ((ψ g : k) - χ g) = 0 := by rw [mul_sub, hx, mul_comm, sub_self]
  exact (mul_eq_zero.mp hx').resolve_right (sub_ne_zero.mpr hg)

/-- Every vector of the line of `χ` is acted on through `χ`. -/
@[simp]
theorem weightSpace_ofLinearCharacter_self [CommSemiring k] (χ : G →* kˣ) :
    (ofLinearCharacter χ).weightSpace ((Units.coeHom k).comp χ) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ mem_weightSpace.mpr fun g ↦ by
    rw [ofLinearCharacter_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul, mul_comm]

end Representation
