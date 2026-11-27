/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Algebra.AlbertAlgebra.Compact
public import TauCeti.Analysis.CayleyDickson.Quaternion

/-!
# The Euclidean structure of the compact Albert algebra

The compact Albert algebra `J = CompactAlbertAlgebra ℝ` of `3 × 3` Hermitian matrices over the real
octonions is a real inner product space for its **trace form**

`⟪A, B⟫ = T(A ∘ B) = ∑ aᵢ bᵢ + 2 ∑ ⟪xᵢ, yᵢ⟫`,

which is positive definite by `TauCeti.CompactAlbertAlgebra.trace_mul_self_pos`. Each octonion entry
occurs twice in the Hermitian matrix, once conjugated, so this is the Frobenius inner product of the
two matrices, and `‖A‖ ^ 2 = T(A ∘ A)` is the sum of the squared norms of all nine entries. By the
associativity of the trace form, every multiplication operator `B ↦ A ∘ B` is self-adjoint. This is
the inner-product half of the axioms of a Euclidean Jordan algebra in the sense of Faraut–Korányi;
the Jordan identity of the compact carrier is not proved here.

As a finite-dimensional real inner product space, `J` carries the topology of its 27 real
coordinates: the coordinate isomorphism with `(Fin 3 → ℝ) × (Fin 3 → DivisionOctonionReal)` is a
continuous linear equivalence. The Jordan product is a continuous bilinear map, hence smooth, and
the trace is a continuous linear functional. An idempotent `A ∘ A = A` has `‖A‖ ^ 2 = T(A)`, so the
idempotents of a given trace lie on a sphere about the origin; in particular the trace-one
idempotents lie on the unit sphere, which bounds the idempotent locus. Since an automorphism
preserves the trace, it preserves the trace form: the automorphisms of `J` are linear isometries.

## Main definitions

* The instances `NormedAddCommGroup (CompactAlbertAlgebra ℝ)` and
  `InnerProductSpace ℝ (CompactAlbertAlgebra ℝ)`: the inner product is the trace form.
* `TauCeti.CompactAlbertAlgebra.continuousLinearEquivProd`: the 27 real coordinates, as a continuous
  linear equivalence.
* `TauCeti.CompactAlbertAlgebra.mulL`: the Jordan product, as a continuous bilinear map.

## Main results

* `TauCeti.CompactAlbertAlgebra.inner_def` and `TauCeti.CompactAlbertAlgebra.inner_eq_sum`: the
  inner product is the trace form, and in coordinates it is `∑ aᵢ bᵢ + 2 ∑ ⟪xᵢ, yᵢ⟫`.
* `TauCeti.CompactAlbertAlgebra.norm_sq_eq_trace_mul_self` and
  `TauCeti.CompactAlbertAlgebra.norm_sq_eq_sum`: `‖A‖ ^ 2 = T(A ∘ A) = ∑ aᵢ ^ 2 + 2 ∑ ‖xᵢ‖ ^ 2`.
* `TauCeti.CompactAlbertAlgebra.inner_mul_left`: **multiplication operators are self-adjoint**,
  `⟪A ∘ B, C⟫ = ⟪B, A ∘ C⟫`.
* `TauCeti.CompactAlbertAlgebra.norm_sq_eq_trace_of_isIdempotentElem`: an idempotent has
  `‖A‖ ^ 2 = T(A)`.
* `TauCeti.CompactAlbertAlgebra.inner_map_map_of_map_mul` and
  `TauCeti.CompactAlbertAlgebra.norm_map_of_map_mul`: **automorphisms are isometries**.
* `TauCeti.CompactAlbertAlgebra.contDiff_mul` and `TauCeti.CompactAlbertAlgebra.contDiff_trace`: the
  Jordan product and the trace are smooth.

## Implementation notes

The `NormedAddCommGroup` and `InnerProductSpace` instances follow the pattern of the corresponding
instances on `Quaternion` in Mathlib's `Mathlib/Analysis/Quaternion.lean`: an `Inner` instance is
promoted to a norm and an inner product space through `InnerProductSpace.Core`.

## References

* J. Faraut and A. Korányi, *Analysis on Symmetric Cones*, Oxford University Press (1994),
  Chapter III, §1: Euclidean Jordan algebras and their trace form.
* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §3.4: the compact
  Albert algebra.
-/

public section

open scoped InnerProductSpace ContDiff

namespace TauCeti

namespace CompactAlbertAlgebra

/-! ### The trace form as an inner product -/

/-- The inner product of the compact Albert algebra is its trace form `⟪A, B⟫ = T(A ∘ B)`. -/
noncomputable instance : Inner ℝ (CompactAlbertAlgebra ℝ) :=
  ⟨fun A B => trace (A * B)⟩

/-- **The inner product of the compact Albert algebra is the trace form**, `⟪A, B⟫ = T(A ∘ B)`. -/
theorem inner_def (A B : CompactAlbertAlgebra ℝ) : ⟪A, B⟫_ℝ = trace (A * B) :=
  (rfl)

/-- The compact Albert algebra is normed by its trace form, `‖A‖ = √(T(A ∘ A))`, which is positive
definite. -/
noncomputable instance : NormedAddCommGroup (CompactAlbertAlgebra ℝ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (CompactAlbertAlgebra ℝ) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun A B => by simp [inner_def, mul_comm]
      re_inner_nonneg := fun A => trace_mul_self_nonneg A
      definite := fun _ => trace_mul_self_eq_zero_iff.mp
      add_left := fun A B C => by simp only [inner_def, add_mul, map_add]
      smul_left := fun A B r => by simp [inner_def, smul_mul_assoc] }

/-- **The compact Albert algebra is a real inner product space** for its trace form. -/
noncomputable instance : InnerProductSpace ℝ (CompactAlbertAlgebra ℝ) :=
  InnerProductSpace.ofCore _

/-- **The inner product in coordinates**: `⟪A, B⟫ = ∑ aᵢ bᵢ + 2 ∑ ⟪xᵢ, yᵢ⟫`, the Frobenius inner
product of the two Hermitian matrices, in which each octonion entry occurs twice. -/
theorem inner_eq_sum (A B : CompactAlbertAlgebra ℝ) :
    ⟪A, B⟫_ℝ = ∑ i, A.diag i * B.diag i + 2 * ∑ i, ⟪A.offDiag i, B.offDiag i⟫_ℝ := by
  simp only [inner_def, trace_mul, CayleyDickson.real_inner_eq_trace_mul_star, Finset.mul_sum,
    mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)]

/-- **The square of the norm is the trace of the Jordan square**, `‖A‖ ^ 2 = T(A ∘ A)`. -/
theorem norm_sq_eq_trace_mul_self (A : CompactAlbertAlgebra ℝ) : ‖A‖ ^ 2 = trace (A * A) := by
  rw [← real_inner_self_eq_norm_sq, inner_def]

/-- **The norm in coordinates**: `‖A‖ ^ 2 = ∑ aᵢ ^ 2 + 2 ∑ ‖xᵢ‖ ^ 2`, the sum of the squared norms
of the nine entries of the Hermitian matrix. -/
theorem norm_sq_eq_sum (A : CompactAlbertAlgebra ℝ) :
    ‖A‖ ^ 2 = ∑ i, A.diag i ^ 2 + 2 * ∑ i, ‖A.offDiag i‖ ^ 2 := by
  simp only [norm_sq_eq_trace_mul_self, trace_mul_self, CayleyDickson.norm_sq_eq_normSq]

/-- A diagonal entry is bounded by the norm, `|aᵢ| ≤ ‖A‖`. -/
theorem abs_diag_le (A : CompactAlbertAlgebra ℝ) (i : Fin 3) : |A.diag i| ≤ ‖A‖ := by
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg A)
  rw [norm_sq_eq_sum]
  have := Finset.single_le_sum (f := fun j => A.diag j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)
  have : 0 ≤ ∑ j, ‖A.offDiag j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- An octonion entry is bounded by the norm, `√2 ‖xᵢ‖ ≤ ‖A‖`, since it occurs twice in the
Hermitian matrix. -/
theorem sqrt_two_mul_norm_offDiag_le (A : CompactAlbertAlgebra ℝ) (i : Fin 3) :
    √2 * ‖A.offDiag i‖ ≤ ‖A‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg A)
  rw [mul_pow, Real.sq_sqrt zero_le_two, norm_sq_eq_sum]
  have := Finset.single_le_sum (f := fun j => ‖A.offDiag j‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)
  have : 0 ≤ ∑ j, A.diag j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **Multiplication operators are self-adjoint for the trace form**, `⟪A ∘ B, C⟫ = ⟪B, A ∘ C⟫`:
the trace form is associative, as the inner product of a Euclidean Jordan algebra must be. -/
theorem inner_mul_left (A B C : CompactAlbertAlgebra ℝ) : ⟪A * B, C⟫_ℝ = ⟪B, A * C⟫_ℝ := by
  rw [inner_def, inner_def, mul_comm A B, trace_mul_assoc]

/-- **An idempotent has squared norm its trace**: if `A ∘ A = A` then `‖A‖ ^ 2 = T(A)`. So the
idempotents of trace `t` lie on the sphere of radius `√t` about the origin. -/
theorem norm_sq_eq_trace_of_isIdempotentElem {A : CompactAlbertAlgebra ℝ}
    (hA : IsIdempotentElem A) : ‖A‖ ^ 2 = trace A := by
  rw [norm_sq_eq_trace_mul_self, hA.eq]

/-- The identity matrix has norm `√3`. -/
@[simp]
protected theorem norm_one : ‖(1 : CompactAlbertAlgebra ℝ)‖ = √3 := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_trace_of_isIdempotentElem IsIdempotentElem.one,
    trace_one]

/-- The diagonal idempotents have norm `1`. -/
@[simp]
theorem norm_diagIdempotent (i : Fin 3) : ‖diagIdempotent ℝ i‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _),
    norm_sq_eq_trace_of_isIdempotentElem (by simp [IsIdempotentElem]), trace_diagIdempotent,
    Real.sqrt_one]

/-- **An automorphism of the compact Albert algebra preserves the trace form**,
`⟪e A, e B⟫ = ⟪A, B⟫`, since it preserves the trace
(`TauCeti.CompactAlbertAlgebra.trace_map_of_map_mul`). So every automorphism is a linear isometry,
`e.isometryOfInner`. -/
theorem inner_map_map_of_map_mul (e : CompactAlbertAlgebra ℝ ≃ₗ[ℝ] CompactAlbertAlgebra ℝ)
    (he : ∀ A B, e (A * B) = e A * e B) (A B : CompactAlbertAlgebra ℝ) :
    ⟪e A, e B⟫_ℝ = ⟪A, B⟫_ℝ := by
  rw [inner_def, inner_def, ← he, trace_map_of_map_mul e he]

/-- An automorphism of the compact Albert algebra preserves the norm. -/
theorem norm_map_of_map_mul (e : CompactAlbertAlgebra ℝ ≃ₗ[ℝ] CompactAlbertAlgebra ℝ)
    (he : ∀ A B, e (A * B) = e A * e B) (A : CompactAlbertAlgebra ℝ) : ‖e A‖ = ‖A‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_map_map_of_map_mul e he]

/-! ### Coordinates and smoothness -/

/-- The 27 real coordinates of the compact Albert algebra, its scalar diagonal and its three
octonion entries, as a continuous linear equivalence: the topology of the trace-form norm is the
topology of these coordinates. -/
noncomputable def continuousLinearEquivProd :
    CompactAlbertAlgebra ℝ ≃L[ℝ] (Fin 3 → ℝ) × (Fin 3 → DivisionOctonionReal) :=
  (linearEquivProd ℝ ℝ).toContinuousLinearEquiv

@[simp]
theorem continuousLinearEquivProd_apply (A : CompactAlbertAlgebra ℝ) :
    continuousLinearEquivProd A = (A.diag, A.offDiag) := by
  simp [continuousLinearEquivProd]

@[simp]
theorem continuousLinearEquivProd_symm_apply (p : (Fin 3 → ℝ) × (Fin 3 → DivisionOctonionReal)) :
    continuousLinearEquivProd.symm p = ⟨p.1, p.2⟩ := by
  simp [continuousLinearEquivProd]

/-- The Jordan product of the compact Albert algebra, as a continuous bilinear map. -/
noncomputable def mulL :
    CompactAlbertAlgebra ℝ →L[ℝ] CompactAlbertAlgebra ℝ →L[ℝ] CompactAlbertAlgebra ℝ :=
  (LinearMap.mul ℝ (CompactAlbertAlgebra ℝ)).toContinuousBilinearMap

@[simp]
theorem mulL_apply (A B : CompactAlbertAlgebra ℝ) : mulL A B = A * B :=
  (rfl)

/-- **The Jordan product of the compact Albert algebra is smooth.** -/
theorem contDiff_mul {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : CompactAlbertAlgebra ℝ × CompactAlbertAlgebra ℝ => p.1 * p.2 :=
  mulL.isBoundedBilinearMap.contDiff

instance : ContinuousMul (CompactAlbertAlgebra ℝ) :=
  ⟨contDiff_mul.continuous (n := 0)⟩

/-- **The trace of the compact Albert algebra is smooth.** -/
theorem contDiff_trace {n : WithTop ℕ∞} : ContDiff ℝ n (trace : CompactAlbertAlgebra ℝ → ℝ) :=
  (trace : CompactAlbertAlgebra ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap.contDiff

end CompactAlbertAlgebra

end TauCeti
