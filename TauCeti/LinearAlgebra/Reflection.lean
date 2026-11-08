/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Module reflections

This file computes the determinant of Mathlib's `Module.reflection` on a finite free module, and
records that a reflection negates the linear form defining it. Consequently a finite free module
of positive rank has a linear automorphism of determinant `-1`.

It also computes the fixed vectors of a product of reflections `y ↦ y - fᵢ(y) • vᵢ` along
linearly independent vectors `vᵢ`, each used at most once: they are exactly the common zeros of the
linear forms `fᵢ` (`Module.list_prod_map_preReflection_apply_eq_self_iff`). Applied to the simple
roots of a base of a root pairing, this computes the fixed vectors of a Coxeter element.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16, for the argument by linear independence in the case of the simple roots.
-/

public section

universe u v

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {x : M} {f : Module.Dual R M} (h : f x = 2)

/-- The determinant of a module reflection is `-1` on a finite free module. -/
@[simp]
theorem det_reflection [Module.Free R M] [Module.Finite R M] :
    LinearEquiv.det (reflection h) = (-1 : Rˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Module.Free.chooseBasis R M)]
  let b := Module.Free.chooseBasis R M
  rw [reflection]
  -- Unfold the reflection into its rank-one perturbation before applying the determinant lemma.
  change Matrix.det (LinearMap.toMatrix b b (LinearMap.id - f.smulRight x)) = -1
  rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight]
  -- The rank-one determinant lemma is stated for a column matrix times a row matrix.
  rw [show Matrix.vecMulVec (b.repr x) (f ∘ b) =
      Matrix.replicateCol Unit (b.repr x) * Matrix.replicateRow Unit (f ∘ b) by
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply]]
  rw [sub_eq_add_neg, ← Matrix.neg_mul]
  -- Put the matrix in the exact Schur-complement rank-one form.
  change Matrix.det
    (1 + Matrix.replicateCol Unit (-b.repr x) * Matrix.replicateRow Unit (f ∘ b)) = -1
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  -- The remaining scalar is `1 - f x = -1`.
  change 1 + ∑ i, f (b i) * -(b.repr x i) = -1
  simp_rw [mul_neg, mul_comm (f (b _))]
  rw [Finset.sum_neg_distrib]
  have hsum : ∑ i, b.repr x i * f (b i) = f x := by
    calc
      _ = ∑ i, f ((b.repr x i) • b i) := by
        simp only [map_smul, smul_eq_mul]
      _ = f (∑ i, (b.repr x i) • b i) := by rw [map_sum]
      _ = f x := congrArg f (b.sum_repr x)
  rw [hsum, h]
  ring

include h in
/-- The reflection `Module.preReflection x f` negates the linear form `f` defining it. -/
@[simp]
theorem apply_preReflection (y : M) : f (preReflection x f y) = -f y := by
  rw [preReflection_apply, map_sub, map_smul, smul_eq_mul, h]
  ring

/-- A finite free module of positive rank has a linear automorphism of determinant `-1`, namely
a reflection in a basis vector. -/
theorem exists_det_eq_neg_one [Module.Free R M] [Module.Finite R M]
    (hM : 0 < finrank R M) : ∃ g : M ≃ₗ[R] M, LinearEquiv.det g = -1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨LinearEquiv.refl R M, Subsingleton.elim _ _⟩
  let b := Module.Free.chooseBasis R M
  have := Module.nontrivial_of_finrank_pos (R := R) hM
  obtain ⟨i⟩ := b.index_nonempty
  have hf : (2 • b.coord i) (b i) = 2 := by simp
  exact ⟨reflection hf, det_reflection hf⟩

section ListProd

variable {ι : Type*} {v : ι → M} {g : ι → Dual R M}

/-- A product of reflections along the vectors `v i`, `i ∈ l`, moves every vector by an element of
the span of those vectors. -/
theorem list_prod_map_preReflection_apply_sub_mem_span (l : List ι) (y : M) :
    (l.map fun i ↦ preReflection (v i) (g i)).prod y - y ∈
      Submodule.span R (v '' {i | i ∈ l}) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, preReflection_apply, sub_right_comm]
    refine sub_mem (Submodule.span_mono (Set.image_mono fun j hj ↦ ?_) ih)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp, rfl⟩))
    exact List.mem_cons_of_mem i hj

/-- **Fixed vectors of a product of reflections in linearly independent vectors.** Let `l` list
distinct indices, and let the vectors `v i` be linearly independent. The product of the
reflections `y ↦ y - g i y • v i` over `i ∈ l`, in the order of `l`, fixes `y` exactly when every
linear form `g i` with `i ∈ l` vanishes on `y`. Thus its fixed space is the intersection of the
kernels of the `g i`. -/
theorem list_prod_map_preReflection_apply_eq_self_iff (hv : LinearIndependent R v) {l : List ι}
    (hl : l.Nodup) {y : M} :
    (l.map fun i ↦ preReflection (v i) (g i)).prod y = y ↔ ∀ i ∈ l, g i y = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, preReflection_apply, List.forall_mem_cons,
      ← ih hl.2]
    set z := (l.map fun i ↦ preReflection (v i) (g i)).prod y
    -- The vectors `g i z • v i` and `z - y` lie in the spans of disjoint sets of the `v j`.
    have hdisj := hv.disjoint_span_image (s := {i}) (t := {j | j ∈ l})
      (Set.disjoint_singleton_left.mpr hl.1)
    refine ⟨fun h ↦ ?_, fun ⟨hi, hz⟩ ↦ by rw [hz, hi, zero_smul, sub_zero]⟩
    have hzero : g i z • v i = 0 := by
      refine Submodule.disjoint_def.mp hdisj _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl, rfl⟩)) ?_
      rw [show g i z • v i = z - y by rw [← h, sub_sub_cancel]]
      exact list_prod_map_preReflection_apply_sub_mem_span l y
    have hgz : g i z = 0 := hv.smul_left_injective i (by simp only [hzero, zero_smul])
    rw [hgz, zero_smul, sub_zero] at h
    exact ⟨h ▸ hgz, h⟩

end ListProd

end Module
