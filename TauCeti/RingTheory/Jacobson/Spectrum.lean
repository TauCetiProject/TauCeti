/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Jacobson.NonUnital

import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Spectral characterization of the Jacobson radical

For an algebra over a field, an element `a` lies in the Jacobson radical exactly when every
left multiple `b * a` has spectrum contained in `{0}`. In a complex Banach algebra this says
that the radical consists of the elements all of whose left multiples are quasinilpotent.

For a nonunital algebra, with the radical `TauCeti.nonUnitalJacobson` defined through the
external unitization, the same holds with the quasispectrum and with `b` ranging over the
algebra itself rather than over its unitization. The reduction squares a left multiple
`x * a` by an element `x` of the unitization: the square is a left multiple of `a` by an
element of the original algebra.

## Main results

* `TauCeti.Ring.mem_jacobson_iff_forall_spectrum_mul_subset_singleton_zero`: the unital
  characterization.
* `TauCeti.Ring.le_jacobson_of_forall_spectrum_subset_singleton_zero`: the radical contains
  every left ideal consisting of elements with spectrum in `{0}`.
* `TauCeti.mem_nonUnitalJacobson_iff_forall_quasispectrum_mul_subset_singleton_zero`: the
  nonunital characterization.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §1.5.
-/

public section

namespace TauCeti

namespace Ring

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- An element of an algebra over a field lies in the Jacobson radical exactly when every
left multiple of it has spectrum contained in `{0}`. -/
theorem mem_jacobson_iff_forall_spectrum_mul_subset_singleton_zero {a : A} :
    a ∈ Ring.jacobson A ↔ ∀ b : A, spectrum 𝕜 (b * a) ⊆ {0} := by
  rw [mem_jacobson_iff_isUnit_one_add_mul_left]
  refine ⟨fun h b k hk => ?_, fun h b => ?_⟩
  · -- For `k ≠ 0`, `k - b * a = k * (1 + (-(k⁻¹ • b)) * a)` is a unit.
    rw [Set.mem_singleton_iff]
    by_contra hk0
    have e : algebraMap 𝕜 A k - b * a = algebraMap 𝕜 A k * (1 + -(k⁻¹ • b) * a) := by
      simp [mul_add, sub_eq_add_neg, ← Algebra.smul_def, smul_smul, hk0]
    rw [spectrum.mem_iff, e] at hk
    exact hk (((Ne.isUnit hk0).map (algebraMap 𝕜 A)).mul (h _))
  · have h1 : (1 : 𝕜) ∉ spectrum 𝕜 (-b * a) := fun h1 => one_ne_zero (h (-b) h1)
    simpa [spectrum.notMem_iff, sub_eq_add_neg] using h1

/-- Every element of the Jacobson radical of an algebra over a field has spectrum contained
in `{0}`. -/
theorem spectrum_subset_singleton_zero_of_mem_jacobson {a : A} (ha : a ∈ Ring.jacobson A) :
    spectrum 𝕜 a ⊆ {0} := by
  simpa using mem_jacobson_iff_forall_spectrum_mul_subset_singleton_zero.mp ha 1

/-- A left ideal all of whose elements have spectrum contained in `{0}` lies in the Jacobson
radical. Together with `spectrum_subset_singleton_zero_of_mem_jacobson`, the radical is the
largest such left ideal. -/
theorem le_jacobson_of_forall_spectrum_subset_singleton_zero {I : Ideal A}
    (h : ∀ x ∈ I, spectrum 𝕜 x ⊆ {0}) : I ≤ Ring.jacobson A :=
  fun _ ha => mem_jacobson_iff_forall_spectrum_mul_subset_singleton_zero.mpr fun b =>
    h _ (I.mul_mem_left b ha)

end Ring

variable {𝕜 A : Type*} [Field 𝕜] [NonUnitalRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- An element of a nonunital algebra over a field lies in its Jacobson radical exactly when
every left multiple of it by an element of the algebra has quasispectrum contained in `{0}`.
Left multiples by scalars need not be tested separately. -/
theorem mem_nonUnitalJacobson_iff_forall_quasispectrum_mul_subset_singleton_zero {a : A} :
    a ∈ nonUnitalJacobson 𝕜 A ↔ ∀ b : A, quasispectrum 𝕜 (b * a) ⊆ {0} := by
  simp_rw [mem_nonUnitalJacobson,
    Ring.mem_jacobson_iff_forall_spectrum_mul_subset_singleton_zero (𝕜 := 𝕜),
    Unitization.quasispectrum_eq_spectrum_inr 𝕜]
  refine ⟨fun h b => by simpa using h b, fun h x k hk => ?_⟩
  -- `x * a` is the image of `d ∈ A`, and `d * d` is a left multiple of `a` in `A`.
  set d : A := x.fst • a + x.snd * a
  have hd : x * (a : Unitization 𝕜 A) = d := by
    ext <;> simp [d]
  have hsq : (x * (a : Unitization 𝕜 A)) ^ 2 = ((x.fst • d + d * x.snd) * a : A) := by
    rw [hd, sq, ← Unitization.inr_mul]
    congr 1
    simp only [d, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  have hk2 := h _ (hsq ▸ spectrum.pow_mem_pow _ 2 hk)
  simpa using hk2

end TauCeti
