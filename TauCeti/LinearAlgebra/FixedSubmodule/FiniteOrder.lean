/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.FixedSubmodule.BaseChange

/-!
# Scalar extension of fixed vectors of finite-order maps

If `f ^ n = 1`, summing the first `n` powers of `f` gives a map into its fixed submodule.
On fixed vectors this norm is multiplication by `n`. After extension to an algebra in which
`n` is invertible, its normalized scalar extension is an inverse of the canonical map
`LinearMap.fixedSubmoduleBaseChange`.

Thus fixed vectors commute with this scalar extension without flatness, finite generation,
or freeness assumptions. The order need only be invertible in the *new* coefficient ring,
not in the original ring. In particular, this applies to integral Cartan lattices with a
finite-order action, including actions not given by permutations of a basis.

The norm argument is the cyclic form of the averaging argument for invariants; compare
Mathlib's `Representation.averageMap` for finite group representations. Here division is
performed only after scalar extension.

## Main definitions

* `LinearMap.fixedNorm`: the unnormalized cyclic norm, with codomain the fixed submodule.
* `LinearMap.fixedSubmoduleBaseChangeEquivOfInvertible`: the canonical scalar-extension
  comparison as a linear equivalence when an exponent of the action is invertible.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 1 (averaging).
-/

public section

open TensorProduct

namespace LinearMap

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  (f : M →ₗ[R] M) {n : ℕ}

/-- Sum the first `n` powers of a map satisfying `f ^ n = 1`, with values in its fixed
submodule. No invertibility of `n` is needed. -/
def fixedNorm (hn : f ^ n = 1) : M →ₗ[R] f.fixedSubmodule :=
  (∑ i ∈ Finset.range n, f ^ i).codRestrict _ fun x ↦ by
    rw [mem_fixedSubmodule_iff]
    have h : f * (∑ i ∈ Finset.range n, f ^ i) = ∑ i ∈ Finset.range n, f ^ i := by
      cases n with
      | zero => simp
      | succ n =>
        rw [Finset.mul_sum]
        simp_rw [← pow_succ']
        rw [Finset.sum_range_succ, hn, Finset.sum_range_succ']
        simp
    exact LinearMap.congr_fun h x

/-- On ambient vectors, the norm is the sum of the powers. -/
@[simp]
theorem coe_fixedNorm (hn : f ^ n = 1) (x : M) :
    (f.fixedNorm hn x : M) = ∑ i ∈ Finset.range n, (f ^ i) x := by
  simp [fixedNorm]

/-- On a fixed vector, the cyclic norm is multiplication by the exponent. -/
@[simp]
theorem fixedNorm_coe (hn : f ^ n = 1) (x : f.fixedSubmodule) :
    f.fixedNorm hn x = n • x := by
  apply Subtype.ext
  simp [coe_fixedNorm, pow_apply_of_mem_fixedSubmodule f x.property]

/-- Composing the norm with the fixed-vector inclusion gives the sum of powers. -/
@[simp]
theorem subtype_comp_fixedNorm (hn : f ^ n = 1) :
    f.fixedSubmodule.subtype ∘ₗ f.fixedNorm hn = ∑ i ∈ Finset.range n, f ^ i := by
  ext x
  simp

/-- Composing the inclusion with the norm gives multiplication by the exponent. -/
@[simp]
theorem fixedNorm_comp_subtype (hn : f ^ n = 1) :
    f.fixedNorm hn ∘ₗ f.fixedSubmodule.subtype = n • LinearMap.id := by
  ext x
  simp

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- After scalar extension, composing the inclusion with the norm gives the sum of powers
of the extended endomorphism. -/
@[simp]
theorem subtype_baseChange_comp_fixedNorm_baseChange (hn : f ^ n = 1) :
    f.fixedSubmodule.subtype.baseChange A ∘ₗ (f.fixedNorm hn).baseChange A =
      ∑ i ∈ Finset.range n, (f.baseChange A) ^ i := by
  rw [← baseChange_comp, subtype_comp_fixedNorm]
  simpa only [baseChangeHom_apply, baseChange_pow] using
    map_sum (LinearMap.baseChangeHom R A M M) (fun i ↦ f ^ i) (Finset.range n)

/-- After scalar extension, composing the norm with the inclusion gives multiplication
by the exponent. -/
@[simp]
theorem fixedNorm_baseChange_comp_subtype_baseChange (hn : f ^ n = 1) :
    (f.fixedNorm hn).baseChange A ∘ₗ f.fixedSubmodule.subtype.baseChange A =
      n • LinearMap.id := by
  rw [← baseChange_comp, fixedNorm_comp_subtype]
  simpa only [baseChangeHom_apply, baseChange_id] using
    _root_.map_nsmul (LinearMap.baseChangeHom R A f.fixedSubmodule f.fixedSubmodule) n
      (LinearMap.id : f.fixedSubmodule →ₗ[R] f.fixedSubmodule)

variable [Invertible (n : A)]

/-- Fixed vectors commute with scalar extension whenever an exponent of the original action
is invertible in the target algebra. Neither flatness nor invertibility in the base ring is
required. The forward map is the canonical comparison; its inverse is the scalar-extended
cyclic norm divided by `n`. -/
noncomputable def fixedSubmoduleBaseChangeEquivOfInvertible (hn : f ^ n = 1) :
    A ⊗[R] f.fixedSubmodule ≃ₗ[A] (f.baseChange A).fixedSubmodule := by
  let g := (⅟(n : A)) • (f.fixedNorm hn).baseChange A ∘ₗ
    (f.baseChange A).fixedSubmodule.subtype
  refine LinearEquiv.ofLinearMap (f.fixedSubmoduleBaseChange A) g ?_ ?_
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [g, LinearMap.comp_apply, LinearMap.smul_apply,
      Submodule.coe_subtype, map_smul, Submodule.coe_smul,
      coe_fixedSubmoduleBaseChange, LinearMap.id_apply]
    rw [← LinearMap.comp_apply, subtype_baseChange_comp_fixedNorm_baseChange]
    simp [pow_apply_of_mem_fixedSubmodule _ x.property, ← Nat.cast_smul_eq_nsmul A]
  · apply LinearMap.ext
    intro x
    simp only [g, LinearMap.comp_apply, LinearMap.smul_apply,
      coe_fixedSubmoduleBaseChange, Submodule.coe_subtype, LinearMap.id_apply]
    rw [← LinearMap.comp_apply, fixedNorm_baseChange_comp_subtype_baseChange]
    simp [← Nat.cast_smul_eq_nsmul A]

/-- The forward equivalence is the existing canonical comparison. -/
@[simp]
theorem fixedSubmoduleBaseChangeEquivOfInvertible_apply (hn : f ^ n = 1)
    (x : A ⊗[R] f.fixedSubmodule) :
    f.fixedSubmoduleBaseChangeEquivOfInvertible A hn x = f.fixedSubmoduleBaseChange A x := by
  rfl

/-- The inverse is the normalized scalar extension of the cyclic norm. -/
@[simp]
theorem fixedSubmoduleBaseChangeEquivOfInvertible_symm_apply (hn : f ^ n = 1)
    (x : (f.baseChange A).fixedSubmodule) :
    (f.fixedSubmoduleBaseChangeEquivOfInvertible A hn).symm x =
      ⅟(n : A) • (f.fixedNorm hn).baseChange A (x : A ⊗[R] M) := by
  rfl

end LinearMap
