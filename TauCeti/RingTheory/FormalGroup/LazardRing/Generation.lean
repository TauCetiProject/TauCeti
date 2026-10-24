/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import TauCeti.RingTheory.FormalGroup.LazardRing.Indecomposable
-- Proof-only: the graded Nakayama lemma.
import TauCeti.RingTheory.GradedAlgebra.Nakayama

/-!
# The generators `xₙ` generate the Lazard ring

The Lazard ring `L` is graded by homological degree, with `aᵢⱼ` in degree `2 (i + j - 1) ≥ 2`, so
it is connected: its degree-zero part consists of the integers, and its augmentation ideal `I`,
the kernel of the augmentation `L →+* ℤ` classifying `X + Y`, is the irrelevant ideal
`⨁_{n > 0} Lₙ`. The classes of the generators `xₙ ∈ L₂ₙ` form a basis of the indecomposables
`I ⧸ I²` (`TauCeti.LazardRing.cotangentBasis`), so by the graded Nakayama lemma the `xₙ` generate
`L` as a ring. Equivalently, the homomorphism `ℤ[x₁, x₂, …] →ₐ[ℤ] L` sending `xₙ` to the generator
`xₙ` is surjective.

This is the first half of **Lazard's theorem** that `L` is the polynomial ring `ℤ[x₁, x₂, …]`; the
second half is the algebraic independence of the `xₙ`.

## Main results

* `TauCeti.LazardRing.augmentation_eq_zero_of_mem_grading`: the augmentation kills the elements of
  positive degree.
* `TauCeti.LazardRing.eq_intCast_augmentation_of_mem_grading_zero`: an element of degree zero is the
  integer given by its augmentation.
* `TauCeti.LazardRing.augmentationIdeal_eq_irrelevant`: the augmentation ideal is the irrelevant
  ideal of the grading.
* `TauCeti.LazardRing.augmentationIdeal_le_span_range_generator_sup_sq`: `I ≤ (xₙ)ₙ + I²`.
* `TauCeti.LazardRing.adjoin_range_generator`: the `xₙ` generate `L` as a `ℤ`-algebra.
* `TauCeti.LazardRing.aeval_generator_surjective`: `ℤ[x₁, x₂, …] →ₐ[ℤ] L` is surjective.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1
  (the proof of Lazard's theorem A2.1.8).
* J. F. Adams, *Stable Homotopy and Generalised Homology*, Part II, §7.
-/

public section

noncomputable section

open DirectSum HomogeneousIdeal

namespace TauCeti.LazardRing

/-! ### The grading is connected -/

/-- Every coefficient `aᵢⱼ` has nonzero degree `2 (i + j - 1)`. -/
private theorem degree_ne_zero : ∀ ij : ℕ+ × ℕ+, degree ij ≠ 0 := by
  rintro ⟨i, j⟩
  have hi := PNat.pos i
  have hj := PNat.pos j
  rw [degree_apply]
  omega

/-- The augmentation kills the elements of positive degree. -/
theorem augmentation_eq_zero_of_mem_grading {n : ℕ} (hn : n ≠ 0) {x : LazardRing}
    (hx : x ∈ grading n) : augmentation x = 0 := by
  obtain ⟨p, hp, rfl⟩ := mem_grading_iff.1 hx
  rw [augmentation_mk, MvPolynomial.constantCoeff_eq]
  exact hp.coeff_eq_zero 0 (by simpa using hn.symm)

/-- **The Lazard ring is connected**: an element of degree zero is the integer given by its
augmentation. -/
theorem eq_intCast_augmentation_of_mem_grading_zero {x : LazardRing} (hx : x ∈ grading 0) :
    x = augmentation x := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_grading_iff.1 hx
  -- A polynomial of weighted degree zero is constant, since every variable has positive weight.
  have hpC := MvPolynomial.weightedHomogeneousComponent_zero (R := ℤ) (φ := p) degree_ne_zero
  rw [MvPolynomial.weightedHomogeneousComponent_of_mem
    ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 hp)] at hpC
  simp only [↓reduceIte] at hpC
  rw [augmentation_mk, MvPolynomial.constantCoeff_eq, hpC, MvPolynomial.coeff_zero_C]
  exact eq_intCast (mk.comp MvPolynomial.C) _

/-- The augmentation only sees the degree-zero component. -/
@[simp]
theorem augmentation_decompose_zero (x : LazardRing) :
    augmentation (decompose grading x 0 : LazardRing) = augmentation x := by
  classical
  conv_rhs => rw [← sum_support_decompose grading x]
  rw [map_sum, Finset.sum_eq_single 0 (fun n _ hn ↦
    augmentation_eq_zero_of_mem_grading hn (SetLike.coe_mem _))]
  intro h
  rw [DFinsupp.notMem_support_iff.1 h, ZeroMemClass.coe_zero, map_zero]

/-- The augmentation ideal of the Lazard ring is the irrelevant ideal `⨁_{n > 0} Lₙ` of its
grading. -/
theorem augmentationIdeal_eq_irrelevant :
    augmentationIdeal = (irrelevant grading).toIdeal := by
  ext x
  rw [mem_augmentationIdeal, HomogeneousIdeal.mem_iff, mem_irrelevant_iff, GradedRing.proj_apply,
    ← augmentation_decompose_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [eq_intCast_augmentation_of_mem_grading_zero (SetLike.coe_mem _), h, Int.cast_zero]

/-! ### Generation -/

/-- The generators `xₙ` generate the augmentation ideal modulo its square: `I ≤ (xₙ)ₙ + I²`. -/
theorem augmentationIdeal_le_span_range_generator_sup_sq :
    augmentationIdeal ≤ Ideal.span (Set.range generator) ⊔ augmentationIdeal ^ 2 := by
  intro y hy
  let v (n : ℕ+) : augmentationIdeal := ⟨generator n, generator_mem_augmentationIdeal n⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (cotangentBasis.mem_span (augmentationIdeal.toCotangent ⟨y, hy⟩))
  have hcot : augmentationIdeal.toCotangent (c.sum fun n k ↦ k • v n) =
      augmentationIdeal.toCotangent ⟨y, hy⟩ := by
    rw [← hc, map_finsuppSum]
    simp only [map_zsmul, cotangentBasis_apply, v]
  have hcoe : ((c.sum fun n k ↦ k • v n : augmentationIdeal) : LazardRing) =
      c.sum fun n k ↦ k • generator n := by
    simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul_of_tower, v]
  rw [Ideal.toCotangent_eq, hcoe] at hcot
  refine Submodule.mem_sup.2 ⟨c.sum fun n k ↦ k • generator n, ?_,
    y - c.sum fun n k ↦ k • generator n, by simpa using Submodule.neg_mem _ hcot,
    add_sub_cancel _ y⟩
  exact Ideal.sum_mem _ fun n _ ↦ Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨n, rfl⟩)

/-- **The generators `xₙ` generate the Lazard ring** as a `ℤ`-algebra. This is the first half of
Lazard's theorem that `L` is the polynomial ring `ℤ[x₁, x₂, …]`. -/
theorem adjoin_range_generator : Algebra.adjoin ℤ (Set.range generator) = ⊤ := by
  have h := GradedAlgebra.adjoin_eq_top_of_irrelevant_le_span_sup_sq grading
    (s := Set.range generator) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨2 * n, by positivity, generator_mem_grading n⟩)
    (by
      rw [← augmentationIdeal_eq_irrelevant]
      exact augmentationIdeal_le_span_range_generator_sup_sq)
  rw [_root_.eq_top_iff]
  rintro x -
  have hx : x ∈ Algebra.adjoin (grading 0) (Set.range generator) := h ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap r =>
    rw [SetLike.GradeZero.algebraMap_apply, eq_intCast_augmentation_of_mem_grading_zero r.2]
    exact Subalgebra.intCast_mem _ _
  | add y z _ _ hy hz => exact Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => exact Subalgebra.mul_mem _ hy hz

/-- The homomorphism `ℤ[x₁, x₂, …] →ₐ[ℤ] L` sending the variable `xₙ` to the generator `xₙ` is
surjective. -/
theorem aeval_generator_surjective :
    Function.Surjective (MvPolynomial.aeval generator : MvPolynomial ℕ+ ℤ →ₐ[ℤ] LazardRing) := by
  rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range, adjoin_range_generator]

end TauCeti.LazardRing
