/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Basic lemmas on alternating maps

This file collects basic constructions and lemmas on `AlternatingMap`:

* **Coefficient extraction:** Putting a linear combination `∑ j ∈ s, e j • v j` in place of the
  `i`-th argument `v i` of an alternating map, for `i ∈ s`, multiplies its value on `v` by `e i`:
  every other term of the sum repeats an argument, so its contribution vanishes. Over a basis, this
  reads off the `i`-th coordinate of a vector put in place of the `i`-th basis vector.
* **Alternating maps in degree one:** For a subsingleton index type `ι` and `i : ι`,
  `AlternatingMap.ofSubsingleton` identifies linear maps `M →ₗ[R] N` with alternating maps
  `M [⋀^ι]→ₗ[R] N`. We upgrade that bijection to an `S`-linear equivalence
  `AlternatingMap.ofSubsingletonₗ` for any commuting scalar action of `S` on `N` (matching
  `MultilinearMap.ofSubsingletonₗ`), record scalar linearity on constant tuples, and show that over
  a nonempty subsingleton index type an alternating map `ω : R [⋀^ι]→ₗ[R] N` vanishes iff
  `ω (fun _ ↦ 1) = 0`.

## Main definitions

* `AlternatingMap.ofSubsingletonₗ`: `AlternatingMap.ofSubsingleton` upgraded to an `S`-linear
  equivalence.

## Main results

* `AlternatingMap.map_update_sum_smul`: putting `∑ j ∈ s, e j • v j` in place of `v i`, for
  `i ∈ s`, multiplies the value of an alternating map by `e i`.
* `AlternatingMap.apply_const_smul`: an alternating map of degree one commutes with scalar
  multiplication on constant tuples.
* `AlternatingMap.apply_const_one_eq_zero`, `AlternatingMap.apply_const_one_ne_zero`: over a
  nonempty subsingleton index type, `ω : R [⋀^ι]→ₗ[R] N` vanishes on `fun _ ↦ 1` iff `ω = 0`.
-/

public section

namespace AlternatingMap

section UpdateSumSmul

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- Putting the linear combination `∑ j ∈ s, e j • v j` in place of `v i`, for `i ∈ s`, multiplies
the value of an alternating map by `e i`: every other term repeats an argument. -/
@[simp]
theorem map_update_sum_smul [DecidableEq ι] (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) {s : Finset ι}
    {i : ι} (hi : i ∈ s) (e : ι → R) :
    f (Function.update v i (∑ j ∈ s, e j • v j)) = e i • f v := by
  rw [f.map_update_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji ↦ by
    rw [f.map_update_smul, f.map_update_self _ hji.symm, smul_zero], f.map_update_smul,
    Function.update_eq_self]

end UpdateSumSmul

section OfSubsingleton

variable (R M N S : Type*) {ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Semiring S] [Module S N] [SMulCommClass R S N] [Subsingleton ι]

/-- `AlternatingMap.ofSubsingleton` upgraded to an `S`-linear equivalence, matching
`MultilinearMap.ofSubsingletonₗ`. -/
def ofSubsingletonₗ (i : ι) : (M →ₗ[R] N) ≃ₗ[S] (M [⋀^ι]→ₗ[R] N) :=
  { AlternatingMap.ofSubsingleton R M N i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem ofSubsingletonₗ_apply (i : ι) (f : M →ₗ[R] N) :
    ofSubsingletonₗ R M N S i f = ofSubsingleton R M N i f := (rfl)

@[simp]
theorem ofSubsingletonₗ_symm_apply (i : ι) (ω : M [⋀^ι]→ₗ[R] N) :
    (ofSubsingletonₗ R M N S i).symm ω = (ofSubsingleton R M N i).symm ω := (rfl)

theorem ofSubsingletonₗ_apply_apply (i : ι) (f : M →ₗ[R] N) (v : ι → M) :
    ofSubsingletonₗ R M N S i f v = f (v i) := (rfl)

theorem ofSubsingletonₗ_symm_apply_apply (i : ι) (ω : M [⋀^ι]→ₗ[R] N) (x : M) :
    (ofSubsingletonₗ R M N S i).symm ω x = ω (fun _ ↦ x) := (rfl)

end OfSubsingleton

section ConstOne

variable {R N ι : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Subsingleton ι] [Nonempty ι]

/-- An alternating map of degree one commutes with scalar multiplication on constant tuples. -/
theorem apply_const_smul {M : Type*} [AddCommMonoid M] [Module R M]
    (ω : M [⋀^ι]→ₗ[R] N) (r : R) (x : M) : ω (fun _ ↦ r • x) = r • ω (fun _ ↦ x) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [← ofSubsingletonₗ_symm_apply_apply R M N ℕ i ω (r • x), map_smul,
    ofSubsingletonₗ_symm_apply_apply]

/-- An alternating map of degree one on `R` vanishes on the constant tuple `1` iff it is zero. -/
@[simp]
theorem apply_const_one_eq_zero {ω : R [⋀^ι]→ₗ[R] N} : ω (fun _ ↦ 1) = 0 ↔ ω = 0 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  let e := (LinearMap.ringLmapEquivSelf R ℕ N).symm.trans (ofSubsingletonₗ R R N ℕ i)
  have he : e.symm ω = ω (fun _ ↦ 1) := by simp [e]
  exact he ▸ map_eq_zero_iff e.symm e.symm.injective

/-- A nonzero alternating map of degree one on `R` is nonzero on the constant tuple `1`. -/
theorem apply_const_one_ne_zero {ω : R [⋀^ι]→ₗ[R] N} (hω : ω ≠ 0) : ω (fun _ ↦ 1) ≠ 0 :=
  apply_const_one_eq_zero.not.2 hω

end ConstOne

end AlternatingMap
