/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Elementwise criteria for pure ideals

An ideal is pure exactly when each of its elements is fixed by multiplication by some
other element of the ideal. For a surjective ring map this characterizes flatness in
terms of its kernel, without finite generation hypotheses.

## References

* [Stacks Project, Lemma 10.108.2 (04PS)](https://stacks.math.columbia.edu/tag/04PS).
-/

public section

/-- An ideal is pure if and only if each element is fixed by multiplication by an element
of that ideal. -/
@[stacks 04PS "(1) ⇔ (5)"]
theorem Ideal.pure_iff_forall_exists_eq_mul {R : Type*} [CommRing R] (I : Ideal R) :
    I.Pure ↔ ∀ x ∈ I, ∃ y ∈ I, x = x * y := by
  refine ⟨fun _ _ hx ↦ Ideal.exists_eq_mul_of_pure hx, fun h ↦ ?_⟩
  apply Ideal.Pure.of_inf_eq_mul
  intro J _
  refine le_antisymm (fun x hx ↦ ?_) Ideal.mul_le_inf
  obtain ⟨y, hy, hxy⟩ := h x hx.1
  rw [hxy, mul_comm x y]
  exact Ideal.mul_mem_mul hy hx.2

/-- A surjective ring map is flat exactly when each element of its kernel is fixed by
multiplication by another element of the kernel. -/
theorem RingHom.flat_iff_forall_exists_eq_mul_of_surjective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f) :
    f.Flat ↔ ∀ x, f x = 0 → ∃ y, f y = 0 ∧ x = x * y := by
  let := f.toAlgebra
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hf
  rw [RingHom.Flat, ← Module.Flat.equiv_iff e.toLinearEquiv]
  exact Ideal.pure_iff_forall_exists_eq_mul (RingHom.ker f)
