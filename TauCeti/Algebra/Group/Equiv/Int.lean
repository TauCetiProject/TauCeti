/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion

/-!
# Groups isomorphic to `ℤ`

A group `G` with an isomorphism `Additive G ≃+ ℤ` is infinite cyclic. Transporting along the
isomorphism, it is not a torsion group, and no power map `a ↦ a ^ d` with `d ≠ 1` is surjective on
it, since `1 : ℤ` is not a multiple of such a `d`.

## Main results

* `TauCeti.not_isMulTorsion_of_addEquiv_int`: a group isomorphic to `ℤ` is not a torsion group.
* `TauCeti.not_surjective_pow_of_addEquiv_int`: on a group isomorphic to `ℤ`, the power map
  `a ↦ a ^ d` is not surjective for `d ≠ 1`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **A group isomorphic to `ℤ` is not a torsion group**, since `ℤ` is nontrivial and
torsion-free. -/
theorem not_isMulTorsion_of_addEquiv_int (f : Additive G ≃+ ℤ) : ¬ IsMulTorsion G := fun h ↦
  have e : G ≃* Multiplicative ℤ := AddEquiv.toMultiplicativeRight f
  not_isMulTorsion_of_isMulTorsionFree (h.of_surjective (f := e.toMonoidHom) e.surjective)

/-- **No power map other than the identity is surjective on a group isomorphic to `ℤ`**: under
the isomorphism `a ↦ a ^ d` becomes multiplication by `d`, and `1 : ℤ` is a multiple of the natural
number `d` only for `d = 1`. -/
theorem not_surjective_pow_of_addEquiv_int (f : Additive G ≃+ ℤ) {d : ℕ} (hd : d ≠ 1) :
    ¬ Function.Surjective fun a : G ↦ a ^ d := by
  intro h
  obtain ⟨b, hb⟩ := h (f.symm 1).toMul
  -- Apply `f` to `b ^ d = f⁻¹ 1`: powers become multiples, so `d * f b = 1`.
  have := congrArg (fun a : G ↦ f (Additive.ofMul a)) hb
  simp only [ofMul_pow, map_nsmul, nsmul_eq_mul, ofMul_toMul, f.apply_symm_apply] at this
  exact hd (by exact_mod_cast Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg d) this)

end TauCeti
