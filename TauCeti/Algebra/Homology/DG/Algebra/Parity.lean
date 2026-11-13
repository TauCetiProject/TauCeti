/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.Algebra.Module.GradedModule.Coarsen

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
* `TauCeti.leibniz_coarsenGrading_of_leibniz` and `TauCeti.leibniz_parityGrading_of_leibniz`:
  the graded Leibniz rule passes to sign-preserving coarsenings, and in particular from integer
  degree to parity.
-/

public section

namespace TauCeti

section Odd

variable {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}

/-- A linear map raising integer degree by one maps elements of parity `i` to elements of parity
`i + 1`. -/
theorem map_mem_parityGrading_of_map_mem
    (hd : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1)) {i : ZMod 2} {a : A}
    (ha : a ∈ parityGrading 𝒜 i) : d a ∈ parityGrading 𝒜 (i + 1) := by
  have h1 : Int.castAddHom (ZMod 2) 1 = 1 := Int.cast_one
  have := ((LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ hd hx).coarsenGrading
    (Int.castAddHom (ZMod 2))).map_mem ha
  rwa [h1] at this

end Odd

section Leibniz

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A] {d : A →ₗ[R] A}

/-- **The graded Leibniz rule passes to any sign-preserving coarsening.** If `d` satisfies the
graded Leibniz rule with the sign `(-1) ^ p` on a left factor of degree `p` and `f : ι → κ`
preserves `(-1) ^ ·`, then `d` satisfies the graded Leibniz rule with the sign `(-1) ^ i` on a
left factor in the coarsened piece of degree `i`. -/
theorem leibniz_coarsenGrading_of_leibniz {ι κ : Type*}
    [CommSemiring ι] [Module ι (Additive ℤˣ)] [CommSemiring κ] [Module κ (Additive ℤˣ)]
    {𝒜 : ι → Submodule R A} {f : ι → κ} (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (hl : ∀ {p : ι} {a : A}, a ∈ 𝒜 p → ∀ b : A,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b))
    {i : κ} {a : A} (ha : a ∈ coarsenGrading 𝒜 f i) (b : A) :
    d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) := by
  -- Both sides are additive in `a`, so it suffices to treat homogeneous elements.
  refine coarsenGrading_induction
    (motive := fun a ↦ d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) ha
    (fun p hp a ha ↦ ?_) (by simp) fun x y hx hy ↦ ?_
  · rw [hl ha b, ← hp, hf]
  · rw [add_mul, map_add, hx, hy, map_add, add_mul, add_mul, smul_add]
    abel

/-- **The integer Leibniz rule implies the parity Leibniz rule.** If `d` satisfies the graded
Leibniz rule with the sign `(-1) ^ p` on a left factor of degree `p`, it satisfies the graded
Leibniz rule with the sign `(-1) ^ i` on a left factor of parity `i`. -/
theorem leibniz_parityGrading_of_leibniz {𝒜 : ℤ → Submodule R A}
    (hl : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A, d (a * b) = d a * b + p.negOnePow • (a * d b))
    {i : ZMod 2} {a : A} (ha : a ∈ parityGrading 𝒜 i) (b : A) :
    d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) :=
  leibniz_coarsenGrading_of_leibniz (fun p ↦ uzpow_intCast (-1) p) hl ha b

end Leibniz

end TauCeti
