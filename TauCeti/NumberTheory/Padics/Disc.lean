/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.ZMod

/-!
# The disc decomposition of `ℤ_p`

For `h : ℕ`, the residue classes `a ∈ ZMod (p ^ h)` cut `ℤ_p` into the discs `a + pʰℤ_p`, where
`a` is represented by its natural representative `a.val < pʰ`. On the disc of `a` the coordinate
`w = (x - a.val) / pʰ` runs through `ℤ_p`.

## Main definitions

* `PadicInt.discHomeomorph p h`: the homeomorphism `ZMod (pʰ) × ℤ_p ≃ₜ ℤ_p`,
  `(a, w) ↦ a.val + pʰ w`.

## Main results

* `PadicInt.toZModPow_natCast_val_add_mul`: the point `a.val + pʰ w` reduces to `a` modulo `pʰ`.
* `PadicInt.fst_discHomeomorph_symm`: the disc of `x` is its residue class modulo `pʰ`.
* `PadicInt.natCast_val_toZModPow_add_mul_snd_discHomeomorph_symm`: `x` is the natural
  representative of its residue class plus `pʰ` times its disc coordinate.
* `PadicInt.discHomeomorph_symm_natCast_val_add_mul`: the inverse decomposition of `a.val + pʰ w`
  is `(a, w)`.
* `PadicInt.discHomeomorph_symm_cast_add_mul`: the same statement in simp normal form.
-/

public section

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The point `a.val + pʰ w` of the disc of `a` reduces to `a` modulo `pʰ`. -/
theorem toZModPow_natCast_val_add_mul (h : ℕ) (a : ZMod (p ^ h)) (w : ℤ_[p]) :
    toZModPow h ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) = a := by
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast, ZMod.natCast_zmod_val, ← Nat.cast_pow,
    ZMod.natCast_self, zero_mul, add_zero]

private theorem bijective_discMap (h : ℕ) :
    Function.Bijective fun y : ZMod (p ^ h) × ℤ_[p] ↦
      (y.1.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * y.2 := by
  refine ⟨fun y z hyz ↦ ?_, fun x ↦ ?_⟩
  · have h1 : y.1 = z.1 := by
      simpa only [toZModPow_natCast_val_add_mul] using
        congrArg (toZModPow h) hyz
    refine Prod.ext h1 (mul_left_cancel₀ (pow_ne_zero h (Nat.cast_ne_zero.mpr hp.out.ne_zero)) ?_)
    simpa [h1] using hyz
  · set a := toZModPow h x
    have hmem : x - (a.val : ℤ_[p]) ∈ RingHom.ker (toZModPow (p := p) h) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [ker_toZModPow, Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨(a, w), by simp [← hw]⟩

variable (p) in
/-- The decomposition of `ℤ_p` into the discs `a + pʰℤ_p`, `a ∈ ZMod (pʰ)`: the homeomorphism
`ZMod (pʰ) × ℤ_p ≃ₜ ℤ_p` sending `(a, w)` to `a.val + pʰ w`, where `a.val < pʰ` is the natural
representative of `a`. Its inverse sends `x` to its residue class modulo `pʰ` and to the disc
coordinate `w = (x - a.val) / pʰ`. -/
noncomputable def discHomeomorph (h : ℕ) : ZMod (p ^ h) × ℤ_[p] ≃ₜ ℤ_[p] :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (bijective_discMap h)) <|
    continuous_prod_of_discrete_left.mpr fun _ ↦ by
      simp only [Equiv.ofBijective_apply]
      fun_prop

@[simp]
theorem discHomeomorph_apply (h : ℕ) (y : ZMod (p ^ h) × ℤ_[p]) :
    discHomeomorph p h y = (y.1.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * y.2 := by
  simp only [discHomeomorph, Continuous.homeoOfEquivCompactToT2, Homeomorph.homeomorph_mk_coe,
    Equiv.ofBijective_apply]

/-- The first component of the inverse disc decomposition is reduction modulo `pʰ`. -/
@[simp]
theorem fst_discHomeomorph_symm (h : ℕ) (x : ℤ_[p]) :
    ((discHomeomorph p h).symm x).1 = toZModPow h x := by
  conv_rhs => rw [← (discHomeomorph p h).apply_symm_apply x, discHomeomorph_apply]
  rw [toZModPow_natCast_val_add_mul]

/-- The second component of the inverse disc decomposition is the disc coordinate: `x` is the
natural representative of its residue class modulo `pʰ` plus `pʰ` times it. -/
theorem natCast_val_toZModPow_add_mul_snd_discHomeomorph_symm (h : ℕ) (x : ℤ_[p]) :
    ((toZModPow h x).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * ((discHomeomorph p h).symm x).2 = x := by
  conv_rhs => rw [← (discHomeomorph p h).apply_symm_apply x]
  rw [discHomeomorph_apply, fst_discHomeomorph_symm]

/-- The inverse disc decomposition of `a.val + pʰ w` is `(a, w)`. -/
theorem discHomeomorph_symm_natCast_val_add_mul (h : ℕ) (a : ZMod (p ^ h)) (w : ℤ_[p]) :
    (discHomeomorph p h).symm ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) = (a, w) :=
  (discHomeomorph p h).symm_apply_eq.mpr (discHomeomorph_apply h (a, w)).symm

/-- The inverse disc decomposition of `a + pʰ w` is `(a, w)`, with `a` cast to `ℤ_p` through its
natural representative. This is the simp normal form of
`discHomeomorph_symm_natCast_val_add_mul`, since `ZMod.natCast_val` rewrites `a.val` to `a.cast`. -/
@[simp]
theorem discHomeomorph_symm_cast_add_mul (h : ℕ) (a : ZMod (p ^ h)) (w : ℤ_[p]) :
    (discHomeomorph p h).symm ((a.cast : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) = (a, w) := by
  rw [← ZMod.natCast_val, discHomeomorph_symm_natCast_val_add_mul]

end PadicInt
