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
* `Representation.weightSpace_directSum_ofLinearCharacter_ne_bot`: a direct sum of lines has a
  nonzero vector of weight each of its characters.
* `Representation.weightSpace_directSum_ofLinearCharacter_eq_bot`: a direct sum of lines has no
  nonzero vector of weight a linear character other than its characters.
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
  simp only [ofLinearCharacter_apply, MonoidHom.comp_apply, Units.coeHom_apply,
    smul_eq_mul] at hx
  have hx' : x * ((ψ g : k) - χ g) = 0 := by linear_combination hx
  exact (mul_eq_zero.mp hx').resolve_right (sub_ne_zero.mpr hg)

/-- Every vector of the line of `χ` is acted on through `χ`. -/
@[simp]
theorem weightSpace_ofLinearCharacter_self [CommSemiring k] (χ : G →* kˣ) :
    (ofLinearCharacter χ).weightSpace ((Units.coeHom k).comp χ) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ mem_weightSpace.mpr fun g ↦ by
    simp [ofLinearCharacter_apply, mul_comm]

/-- In the direct sum of the lines of a family `ψ` of linear characters, `G` acts through each
`ψ i` on some nonzero vector: the vector `1` of the summand of `ψ i`. -/
theorem weightSpace_directSum_ofLinearCharacter_ne_bot [CommSemiring k] [Nontrivial k]
    {ι : Type*} (ψ : ι → G →* kˣ) (i : ι) :
    (directSum fun j ↦ ofLinearCharacter (ψ j)).weightSpace ((Units.coeHom k).comp (ψ i)) ≠ ⊥ := by
  classical
  refine Submodule.ne_bot_iff _ |>.mpr ⟨DirectSum.lof k _ _ i 1,
    (mem_weightSpace_directSum _).mpr fun j ↦ ?_, fun h0 ↦ ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [DirectSum.lof_apply, weightSpace_ofLinearCharacter_self]
      exact Submodule.mem_top
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      exact Submodule.zero_mem _
  · have h0i := DFunLike.congr_fun h0 i
    rw [DirectSum.lof_apply, DirectSum.zero_apply] at h0i
    exact one_ne_zero h0i

/-- In the direct sum of the lines of a family `ψ` of linear characters, `G` acts through a linear
character `χ` different from every `ψ j` on no nonzero vector. -/
@[simp]
theorem weightSpace_directSum_ofLinearCharacter_eq_bot [CommRing k] [NoZeroDivisors k]
    {ι : Type*} {ψ : ι → G →* kˣ} {χ : G →* kˣ} (h : ∀ j, ψ j ≠ χ) :
    (directSum fun j ↦ ofLinearCharacter (ψ j)).weightSpace ((Units.coeHom k).comp χ) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot k).mpr <| DirectSum.ext fun j ↦ ?_
  have hxj := (mem_weightSpace_directSum _).mp hx j
  rw [weightSpace_ofLinearCharacter_eq_bot (h j)] at hxj
  rw [DirectSum.zero_apply]
  exact (Submodule.mem_bot k).mp hxj

end Representation
