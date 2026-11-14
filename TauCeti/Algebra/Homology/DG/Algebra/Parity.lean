/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.Algebra.Module.GradedModule.Coarsen
import TauCeti.Data.ZMod.IntUnitsPower

/-!
# The parity reduction of a signed derivation

A linear map `d` on an integer-graded algebra that raises degree by one and satisfies the graded
Leibniz rule `d (a * b) = d a * b + (-1) ^ p * (a * d b)` for `a` of degree `p` is, after
reducing degrees modulo two, an odd map for the parity grading `TauCeti.parityGrading 𝒜` that
satisfies the Leibniz rule with the sign `(-1) ^ i` for `a` of parity `i : ZMod 2`.  The sign is
written with Mathlib's power of a unit of `ℤ` by an element of `ZMod 2`.  In particular the
differential of a nonunital differential graded algebra `h : TauCeti.IsNonUnitalDGAlgebra 𝒜 d`
is an odd signed derivation of the underlying super algebra: apply the theorems below to
`h.map_mem` and `h.leibniz`.

Only the forward direction holds in general: a parity datum does not determine an integer lift.

## Main results

* `TauCeti.map_mem_parityGrading_of_map_mem`: a map raising integer degree by one is odd.
* `TauCeti.leibniz_parityGrading_of_leibniz`: the integer Leibniz rule implies the parity Leibniz
  rule.
* `TauCeti.map_mul_of_parity_leibniz_of_map_eq_zero`, `TauCeti.map_one_eq_zero_of_parity_leibniz`,
  and `TauCeti.map_algebraMap_of_parity_leibniz`: consequences of the parity Leibniz rule alone.
* `TauCeti.comp_self_mul_of_parity_leibniz_of_mem` and `TauCeti.comp_self_mul_of_parity_leibniz`:
  the square of an odd parity-Leibniz map is an unsigned derivation.
-/

public section

namespace TauCeti

section Odd

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {f : M →ₗ[R] N}

/-- A linear map raising integer degree by one maps elements of parity `i` to elements of parity
`i + 1`. -/
theorem map_mem_parityGrading_of_map_mem
    (hf : ∀ {p : ℤ} {x : M}, x ∈ ℳ p → f x ∈ 𝒩 (p + 1)) {i : ZMod 2} {x : M}
    (hx : x ∈ parityGrading ℳ i) : f x ∈ parityGrading 𝒩 (i + 1) := by
  have h1 : Int.castAddHom (ZMod 2) 1 = 1 := Int.cast_one
  have := ((LinearMap.isHomogeneous_def.2 fun _ _ hy ↦ hf hy).coarsenGrading
    (Int.castAddHom (ZMod 2))).map_mem hx
  rwa [h1] at this

end Odd

section Leibniz

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}

/-- **The integer Leibniz rule implies the parity Leibniz rule.** If `d` satisfies the graded
Leibniz rule with the sign `(-1) ^ p` on a left factor of degree `p`, it satisfies the graded
Leibniz rule with the sign `(-1) ^ i` on a left factor of parity `i`. -/
theorem leibniz_parityGrading_of_leibniz
    (hl : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A, d (a * b) = d a * b + p.negOnePow • (a * d b))
    {i : ZMod 2} {a : A} (ha : a ∈ parityGrading 𝒜 i) (b : A) :
    d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) := by
  -- Both sides are additive in `a`, so it suffices to treat homogeneous elements.
  refine coarsenGrading_induction
    (motive := fun a ↦ d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) ha
    (fun p hp a ha ↦ ?_) (by simp) fun x y hx hy ↦ ?_
  · rw [hl ha b, ← hp, Int.coe_castAddHom, uzpow_intCast_eq_negOnePow]
  · rw [add_mul, map_add, hx, hy, map_add, add_mul, add_mul, smul_add]
    abel

end Leibniz

section ParityLeibniz

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  {𝒜 : ZMod 2 → Submodule R A} {d : A →ₗ[R] A}

/-- The parity Leibniz rule against a cycle in the right factor holds for an arbitrary left factor,
without a homogeneity hypothesis. -/
theorem map_mul_of_parity_leibniz_of_map_eq_zero [DirectSum.Decomposition 𝒜]
    (hl : ∀ {i : ZMod 2} {a : A}, a ∈ 𝒜 i → ∀ b : A,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (a : A) {b : A} (hb : d b = 0) : d (a * b) = d a * b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a => simp [hl a.property b, hb]
  | add a a' ha ha' => simp [add_mul, ha, ha']

/-- **The square of an odd parity-Leibniz map satisfies the unsigned Leibniz rule** on any
homogeneous left factor: the two middle terms cancel because `d` flips parity. -/
theorem comp_self_mul_of_parity_leibniz_of_mem
    (hd : ∀ {i : ZMod 2} {a : A}, a ∈ 𝒜 i → d a ∈ 𝒜 (i + 1))
    (hl : ∀ {i : ZMod 2} {a : A}, a ∈ 𝒜 i → ∀ b : A,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) (b : A) :
    d (d (a * b)) = d (d a) * b + a * d (d b) := by
  have hda := hd ha
  rw [hl ha, map_add, map_zsmul_unit, hl hda, hl ha, uzpow_add, uzpow_one]
  simp only [Units.smul_def, Units.val_neg, Units.val_one, mul_neg, mul_one,
    neg_zsmul, zsmul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, one_zsmul]
  abel

/-- **The square of an odd parity-Leibniz map is an unsigned derivation** on the whole algebra:
because the unsigned Leibniz rule has no parity sign, it extends additively from homogeneous left
factors to arbitrary elements. -/
theorem comp_self_mul_of_parity_leibniz [DirectSum.Decomposition 𝒜]
    (hd : ∀ {i : ZMod 2} {a : A}, a ∈ 𝒜 i → d a ∈ 𝒜 (i + 1))
    (hl : ∀ {i : ZMod 2} {a : A}, a ∈ 𝒜 i → ∀ b : A,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (a b : A) :
    d (d (a * b)) = d (d a) * b + a * d (d b) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a => exact comp_self_mul_of_parity_leibniz_of_mem hd hl a.2 b
  | add x y hx hy =>
    rw [add_mul, map_add, map_add, hx, hy, map_add, map_add, add_mul, add_mul]
    abel

end ParityLeibniz

section UnitalParityLeibniz

/-- A function satisfying the parity Leibniz rule annihilates the unit: on `1 * 1` the rule reads
`d 1 = d 1 + d 1`. -/
theorem map_one_eq_zero_of_parity_leibniz {A σ : Type*} [NonAssocRing A] [SetLike σ A]
    {𝒜 : ZMod 2 → σ} [SetLike.GradedOne 𝒜] {d : A → A}
    (hl : ∀ {i : ZMod 2} {a : A}, a ∈ 𝒜 i → ∀ b : A,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) :
    d 1 = 0 := by
  have key := hl (SetLike.one_mem_graded 𝒜) 1
  simp only [mul_one, one_mul, uzpow_zero, one_smul] at key
  exact left_eq_add.mp key

/-- A linear map satisfying the parity Leibniz rule annihilates the image of the ground semiring. -/
theorem map_algebraMap_of_parity_leibniz {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    {𝒜 : ZMod 2 → Submodule R A} [SetLike.GradedOne 𝒜] {d : A →ₗ[R] A}
    (hl : ∀ {i : ZMod 2} {a : A}, a ∈ 𝒜 i → ∀ b : A,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (r : R) : d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_eq_zero_of_parity_leibniz hl, smul_zero]

end UnitalParityLeibniz

end TauCeti
