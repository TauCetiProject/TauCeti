/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.PathsInto
public import TauCeti.RepresentationTheory.Quiver.SemisimpleQuotient

/-!
# Vertex augmentation kernels of relation quotients

For a relation ideal contained in the arrow ideal, the trivial-path coefficients descend to
an augmentation onto the product of the coefficient rings at the vertices. In the right vertex
projective `e_v A`, the kernel of this augmentation is exactly the image of the incoming-arrow
map `(z_b) ↦ ∑ b z_b`. This is the augmentation endpoint of vertex projective resolutions.
No admissibility, acyclicity, or field hypothesis is needed.

The last-arrow decomposition reuses the homogeneous path decomposition in
`TauCeti.RepresentationTheory.Quiver.PathAlgebra.PathsInto`. Multiplication is later-factor-first,
so `b z_b` ends at the target of `b`.

## References

* I. Assem, D. Simson, A. Skowronski, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter II, for vertex projectives and their augmentation modules.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver

universe u v w

variable {k : Type w} {Q : Type u} [Quiver.{v} Q]

section Quotient

variable [CommRing k] [Finite Q] {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

/-- In a vertex corner of a relation quotient, vanishing augmentation is equivalent to
being a sum of incoming arrows. This identifies the augmentation kernel, independently
of exactness at the earlier terms of a projective resolution. -/
theorem quotientTrivialCoeff_eq_zero_iff_exists_eq_sum
    [Fintype Q] (hI : I ≤ arrowIdeal k Q) (v : Q) [∀ i : Q, Fintype (i ⟶ v)]
    {x : pathAlgebra k Q ⧸ I}
    (hx : Ideal.Quotient.mk I (vertexIdempotent k v) * x = x) :
    quotientTrivialCoeff hI x = 0 ↔
      ∃ z : (i : Q) → (i ⟶ v) → pathAlgebra k Q ⧸ I,
        (∀ i b, Ideal.Quotient.mk I (vertexIdempotent k i) * z i b = z i b) ∧
          x = ∑ i, ∑ b : i ⟶ v, Ideal.Quotient.mk I (ofArrow b) * z i b := by
  constructor
  · intro h
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hf : f ∈ arrowIdeal k Q := by
      rw [← ker_trivialCoeff k Q, RingHom.mem_ker]
      simpa only [quotientTrivialCoeff_mk] using h
    obtain ⟨z, hz, heq⟩ := exists_eq_sum_ofArrow_mul_of_mem_arrowIdeal v hf
    refine ⟨fun i b => Ideal.Quotient.mk I (z i b), fun i b => ?_, ?_⟩
    · rw [← map_mul, hz]
    · rw [← hx, ← map_mul, heq]
      simp only [map_sum, map_mul]
  · rintro ⟨z, _, rfl⟩
    simp only [map_sum, map_mul, quotientTrivialCoeff_mk, trivialCoeff_ofArrow, zero_mul,
      Finset.sum_const_zero]

/-- Only the coordinate at `v` can be nonzero in the augmentation of `e_v A`. -/
theorem quotientTrivialCoeff_eq_single_of_vertexIdempotent_mul [DecidableEq Q]
    (hI : I ≤ arrowIdeal k Q) (v : Q) {x : pathAlgebra k Q ⧸ I}
    (hx : Ideal.Quotient.mk I (vertexIdempotent k v) * x = x) :
    quotientTrivialCoeff hI x = Pi.single v (quotientTrivialCoeff hI x v) := by
  classical
  have h := congrArg (quotientTrivialCoeff hI) hx
  simp only [map_mul, quotientTrivialCoeff_mk, trivialCoeff_vertexIdempotent] at h
  ext i
  by_cases hi : i = v
  · subst i; simp
  · have hi' := congrFun h i
    simpa [Pi.single_eq_of_ne hi] using hi'.symm

/-- The augmentation kernel in `e_v A` can be tested using its single vertex coordinate. -/
theorem quotientTrivialCoeff_apply_eq_zero_iff_exists_eq_sum
    [Fintype Q] (hI : I ≤ arrowIdeal k Q) (v : Q) [∀ i : Q, Fintype (i ⟶ v)]
    {x : pathAlgebra k Q ⧸ I}
    (hx : Ideal.Quotient.mk I (vertexIdempotent k v) * x = x) :
    quotientTrivialCoeff hI x v = 0 ↔
      ∃ z : (i : Q) → (i ⟶ v) → pathAlgebra k Q ⧸ I,
        (∀ i b, Ideal.Quotient.mk I (vertexIdempotent k i) * z i b = z i b) ∧
          x = ∑ i, ∑ b : i ⟶ v, Ideal.Quotient.mk I (ofArrow b) * z i b := by
  classical
  rw [← quotientTrivialCoeff_eq_zero_iff_exists_eq_sum hI v hx]
  constructor
  · intro h
    rw [quotientTrivialCoeff_eq_single_of_vertexIdempotent_mul hI v hx, h, Pi.single_zero]
  · intro h; exact congrFun h v

/-- Every scalar is the vertex coefficient of an element of the right vertex projective
of a relation quotient whose ideal lies in the arrow ideal. -/
theorem exists_quotientTrivialCoeff_apply_eq (hI : I ≤ arrowIdeal k Q) (v : Q) (c : k) :
    ∃ x : pathAlgebra k Q ⧸ I, Ideal.Quotient.mk I (vertexIdempotent k v) * x = x ∧
      quotientTrivialCoeff hI x v = c := by
  classical
  refine ⟨c • Ideal.Quotient.mk I (vertexIdempotent k v), ?_, ?_⟩
  · rw [mul_smul_comm, ← map_mul, vertexIdempotent_mul_self]
  · simp only [map_smul, quotientTrivialCoeff_mk, trivialCoeff_vertexIdempotent,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]

end Quotient

end TauCeti.PathAlgebra
