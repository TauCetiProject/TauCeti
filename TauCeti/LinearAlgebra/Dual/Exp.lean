/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Transposes of powers and exponentials of endomorphisms

Transposition `f ↦ f.dualMap` reverses composition of linear maps, so it carries the powers of a
single endomorphism `f` to the powers of its transpose. Hence the transpose of a nilpotent
endomorphism is nilpotent, and over a `ℚ`-algebra the transpose of its exponential is the
exponential of its transpose:

`(exp f)ᵀ = exp fᵀ`.

This is the identity by which a unipotent automorphism `exp f` of a module `M` acts on the
polynomial functions `S(M*)` on `M`.

## Main results

* `LinearMap.dualMap_pow`: `(f ^ n)ᵀ = fᵀ ^ n`.
* `IsNilpotent.dualMap`: the transpose of a nilpotent endomorphism is nilpotent.
* `LinearMap.dualMap_exp`: `(exp f)ᵀ = exp fᵀ` for nilpotent `f`.
-/

public section

open Module

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The transpose of a power of an endomorphism is the power of its transpose. -/
theorem LinearMap.dualMap_pow (f : Module.End R M) (n : ℕ) :
    (f ^ n).dualMap = f.dualMap ^ n := by
  induction n with
  | zero => ext; simp
  | succ n ih => rw [pow_succ, pow_succ', Module.End.mul_eq_comp, ← dualMap_comp_dualMap, ih,
      Module.End.mul_eq_comp]

/-- The transpose of a nilpotent endomorphism is nilpotent. -/
theorem IsNilpotent.dualMap {f : Module.End R M} (hf : IsNilpotent f) :
    IsNilpotent f.dualMap := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [← LinearMap.dualMap_pow, hn]; ext; simp⟩

end CommSemiring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The transpose of the exponential of a nilpotent endomorphism** is the exponential of its
transpose. -/
theorem LinearMap.dualMap_exp [Algebra ℚ R] [Module ℚ M] {f : Module.End R M}
    (hf : IsNilpotent f) :
    (IsNilpotent.exp f).dualMap = IsNilpotent.exp f.dualMap := by
  obtain ⟨n, hn⟩ := hf
  rw [IsNilpotent.exp_eq_sum hn, IsNilpotent.exp_eq_sum (k := n) (by
    rw [← dualMap_pow, hn]; ext; simp)]
  ext φ x
  simp [dualMap_apply, ← dualMap_pow, map_rat_smul]
