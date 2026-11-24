/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Alternating maps in degree one

For a subsingleton index type `ι` and `i : ι`, `AlternatingMap.ofSubsingleton` identifies linear
maps `M →ₗ[R] N` with alternating maps `M [⋀^ι]→ₗ[R] N`. This file upgrades that bijection to an
`S`-linear equivalence `AlternatingMap.ofSubsingletonₗ` for any commuting scalar action of `S` on
`N`, matching `MultilinearMap.ofSubsingletonₗ`, records scalar linearity on constant tuples
(`AlternatingMap.apply_const_smul`), and shows that over a nonempty subsingleton index
type an alternating map `ω : R [⋀^ι]→ₗ[R] N` vanishes iff `ω (fun _ ↦ 1) = 0`
(`AlternatingMap.apply_const_one_eq_zero`, `AlternatingMap.apply_const_one_ne_zero`).
-/

public section

namespace AlternatingMap

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

end
