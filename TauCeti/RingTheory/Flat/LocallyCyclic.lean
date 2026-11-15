/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Data.Finset.Order

/-!
# Flatness of locally cyclic modules

A module `M` over a commutative ring `R` is *locally cyclic* if its cyclic submodules `R ∙ x` form
a directed family, equivalently if every finitely generated submodule of `M` is contained in a
cyclic submodule. For such a module the equational criterion for flatness reduces to relations in
a single element: `M` is flat if and only if every relation `r • x = 0` is trivial in the sense
that `x = d • y` for some `y` and some `d` with `r * d = 0`.

This criterion computes the flatness of tensor squares of idempotent ideals which are directed
unions of principal ideals, the input of the basic setups of almost mathematics.

## Main results

* `Submodule.exists_eq_smul_of_directed`: in a locally cyclic module, every finite family is a
  family of multiples of one element.
* `Ideal.directed_span_singleton_of_exists_dvd`: an ideal in which any two elements have a common
  divisor in the ideal is a locally cyclic module.
* `Module.Flat.iff_forall_smul_eq_zero_of_directed`: a locally cyclic module is flat if and only
  if every relation `r • x = 0` is trivial.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.1,
  Proposition 2.1.7.
-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Submodule

/-- In a locally cyclic module, every finite family is a family of multiples of one element. -/
theorem exists_eq_smul_of_directed (h : Directed (· ≤ ·) fun x : M ↦ R ∙ x)
    {ι : Type*} [Finite ι] (x : ι → M) : ∃ (z : M) (a : ι → R), ∀ i, x i = a i • z := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨z, hz⟩ := h.finset_le (Finset.univ.image x)
  have hmem (i : ι) : x i ∈ R ∙ z :=
    hz (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i)) (Submodule.mem_span_singleton_self _)
  choose a ha using fun i ↦ Submodule.mem_span_singleton.mp (hmem i)
  exact ⟨z, a, fun i ↦ (ha i).symm⟩

end Submodule

namespace Ideal

/-- An ideal in which any two elements have a common divisor in the ideal is locally cyclic: its
cyclic submodules form a directed family. -/
theorem directed_span_singleton_of_exists_dvd {I : Ideal R}
    (hdir : ∀ x ∈ I, ∀ y ∈ I, ∃ z ∈ I, z ∣ x ∧ z ∣ y) : Directed (· ≤ ·) fun y : I ↦ R ∙ y := by
  intro y y'
  obtain ⟨w, hw, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hdir y y.2 y' y'.2
  refine ⟨⟨w, hw⟩, ?_, ?_⟩ <;> dsimp only <;> rw [Submodule.span_singleton_le_iff_mem,
    Submodule.mem_span_singleton]
  · exact ⟨a, Subtype.ext (by simp [ha, mul_comm])⟩
  · exact ⟨b, Subtype.ext (by simp [hb, mul_comm])⟩

end Ideal

namespace Module.Flat

/-- A locally cyclic module is flat if and only if every relation `r • x = 0` is trivial: `x` is
a multiple `d • y` with `r * d = 0` (equational criterion for flatness). -/
theorem iff_forall_smul_eq_zero_of_directed (h : Directed (· ≤ ·) fun x : M ↦ R ∙ x) :
    Module.Flat R M ↔
      ∀ (r : R) (x : M), r • x = 0 → ∃ (d : R) (y : M), x = d • y ∧ r * d = 0 := by
  constructor
  · intro _ r x hrx
    obtain ⟨k, a, y, hxy, hay⟩ :=
      isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Unit ↦ r) (x := fun _ ↦ x) (by simpa)
    obtain ⟨z, b, hb⟩ := Submodule.exists_eq_smul_of_directed h y
    refine ⟨∑ j, a () j * b j, z, ?_, ?_⟩
    · simp [hxy (), hb, Finset.sum_smul, mul_smul]
    · have hay' (j : Fin k) : r * a () j = 0 := by simpa using hay j
      simp [Finset.mul_sum, ← mul_assoc, hay']
  · intro htriv
    refine of_forall_isTrivialRelation fun {l f x} hfx ↦ ?_
    obtain ⟨z, a, ha⟩ := Submodule.exists_eq_smul_of_directed h x
    have hz : (∑ i, f i * a i) • z = 0 := by
      simpa [ha, Finset.sum_smul, mul_smul] using hfx
    obtain ⟨d, y, rfl, hd⟩ := htriv _ z hz
    refine ⟨1, fun i _ ↦ a i * d, fun _ ↦ y, fun i ↦ by simp [ha, mul_smul], fun _ ↦ ?_⟩
    simpa [Finset.sum_mul, mul_assoc] using hd

end Module.Flat
