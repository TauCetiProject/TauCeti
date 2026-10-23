/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import TauCeti.RingTheory.HahnSeries.Multiplication
-- Proof-only: reindexing double sums over antidiagonals.
import TauCeti.Data.Finset.MulAntidiagonal

/-!
# Lie algebras of Hahn series with Lie algebra coefficients

For a Lie ring `L` and an ordered cancellative monoid `Γ`, the Hahn series `HahnModule Γ R L` with
coefficients in `L` form a Lie ring under the coefficient convolution
`⁅x, y⁆_c = ∑_{a + b = c} ⁅x_a, y_b⁆`.
Each sum is finite, because the supports are partially well-ordered, and the support of the
bracket lies in the sum of the supports. For `Γ = ℤ` and a Lie algebra `L` over a field `K`, this is
the formal loop algebra `L((t))`.

If `L` is a Lie algebra over a commutative ring `R`, the bracket is bilinear for the
coefficientwise action of `R`, and also for the convolution action of the Hahn series
`HahnSeries Γ R`, so `HahnModule Γ R L` is a Lie algebra over both. On monomials,
`⁅single a x, single b y⁆ = single (a + b) ⁅x, y⁆`.

## Main definitions and results

* `HahnModule.instBracket`: the coefficient convolution bracket.
* `HahnModule.coeff_lie`: the coefficient formula for the bracket.
* `HahnModule.support_lie_subset`: the support of a bracket lies in the sum of the supports.
* `HahnModule.orderTop_add_le_lie`: over a linearly ordered `Γ`, the order of a bracket is at
  least the sum of the orders.
* `HahnModule.instLieRing`: the Lie ring of `L`-valued Hahn series.
* `HahnModule.instLieAlgebra`, `HahnModule.instLieAlgebraHahnSeries`: the Lie algebra structures
  over `R` and over `HahnSeries Γ R`.
* `HahnModule.single_lie_single`: the bracket of two monomials.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.

The proof of the Leibniz rule reindexes double sums over antidiagonals, following the proof of
`HahnSeries.mul_assoc` in Mathlib's `Mathlib/RingTheory/HahnSeries/Multiplication.lean`.
-/

public section

open Finset Pointwise

noncomputable section

namespace HahnModule

variable {Γ R L : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section LieRing

variable [SMul R L] [LieRing L]

/-- The coefficient convolution bracket `⁅x, y⁆_c = ∑_{a + b = c} ⁅x_a, y_b⁆` of Hahn series
with coefficients in a Lie ring. -/
instance instBracket : Bracket (HahnModule Γ R L) (HahnModule Γ R L) where
  bracket x y := of R
    { coeff c := ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support
          ((of R).symm y).isPWO_support c,
        ⁅((of R).symm x).coeff ij.1, ((of R).symm y).coeff ij.2⁆
      isPWO_support' := (((of R).symm x).isPWO_support.add
          ((of R).symm y).isPWO_support).mono fun c hc ↦ by
        obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
        rw [mem_antidiagonal] at hij
        exact ⟨ij.1, hij.1, ij.2, hij.2.1, hij.2.2⟩ }

/-- The coefficient formula `⁅x, y⁆_c = ∑_{a + b = c} ⁅x_a, y_b⁆`. -/
theorem coeff_lie (x y : HahnModule Γ R L) (c : Γ) :
    ((of R).symm ⁅x, y⁆).coeff c =
      ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support ((of R).symm y).isPWO_support c,
        ⁅((of R).symm x).coeff ij.1, ((of R).symm y).coeff ij.2⁆ :=
  rfl

/-- The coefficients of a bracket may be computed over any partially well-ordered set containing
the support of the first argument. -/
theorem coeff_lie_left' {x y : HahnModule Γ R L} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hxs : ((of R).symm x).support ⊆ s) :
    ((of R).symm ⁅x, y⁆).coeff c =
      ∑ ij ∈ antidiagonal hs ((of R).symm y).isPWO_support c,
        ⁅((of R).symm x).coeff ij.1, ((of R).symm y).coeff ij.2⁆ := by
  rw [coeff_lie]
  refine sum_subset (antidiagonal_mono_left hxs) fun ij hij hij' ↦ ?_
  rw [mem_antidiagonal] at hij
  by_cases h : ((of R).symm x).coeff ij.1 = 0
  · rw [h, zero_lie]
  · exact (hij' (mem_antidiagonal.2 ⟨h, hij.2⟩)).elim

/-- The coefficients of a bracket may be computed over any partially well-ordered set containing
the support of the second argument. -/
theorem coeff_lie_right' {x y : HahnModule Γ R L} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hys : ((of R).symm y).support ⊆ s) :
    ((of R).symm ⁅x, y⁆).coeff c =
      ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support hs c,
        ⁅((of R).symm x).coeff ij.1, ((of R).symm y).coeff ij.2⁆ := by
  rw [coeff_lie]
  refine sum_subset (antidiagonal_mono_right hys) fun ij hij hij' ↦ ?_
  rw [mem_antidiagonal] at hij
  by_cases h : ((of R).symm y).coeff ij.2 = 0
  · rw [h, lie_zero]
  · exact (hij' (mem_antidiagonal.2 ⟨hij.1, h, hij.2.2⟩)).elim

/-- The support of a bracket lies in the sum of the supports. -/
theorem support_lie_subset (x y : HahnModule Γ R L) :
    ((of R).symm ⁅x, y⁆).support ⊆
      ((of R).symm x).support + ((of R).symm y).support := fun c hc ↦ by
  obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  rw [mem_antidiagonal] at hij
  exact ⟨ij.1, hij.1, ij.2, hij.2.1, hij.2.2⟩

/-- The bracket of two monomials: `⁅x t ^ a, y t ^ b⁆ = ⁅x, y⁆ t ^ (a + b)`. -/
@[simp]
theorem single_lie_single (a b : Γ) (x y : L) :
    ⁅of R (HahnSeries.single a x), of R (HahnSeries.single b y)⁆ =
      of R (HahnSeries.single (a + b) ⁅x, y⁆) := by
  ext c
  simp only [coeff_lie, Equiv.symm_apply_apply]
  by_cases hc : c = a + b
  · subst hc
    rw [HahnSeries.coeff_single_same, sum_eq_single (a, b)]
    · simp only [HahnSeries.coeff_single_same]
    · rintro ⟨i, j⟩ hij hne
      rw [mem_antidiagonal] at hij
      exact (hne (Prod.ext (HahnSeries.eq_of_mem_support_single hij.1)
        (HahnSeries.eq_of_mem_support_single hij.2.1))).elim
    · intro h
      simp only [mem_antidiagonal, HahnSeries.mem_support, HahnSeries.coeff_single_same,
        and_true, not_and_or, not_not] at h
      obtain h | h := h <;> simp [h]
  · rw [HahnSeries.coeff_single_of_ne hc, sum_eq_zero]
    rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj, rfl⟩ := mem_antidiagonal.1 hij
    rw [HahnSeries.eq_of_mem_support_single hi, HahnSeries.eq_of_mem_support_single hj] at hc
    exact (hc rfl).elim

/-- The coefficients of a right-nested bracket, as a sum over pairs of antidiagonals. -/
private theorem coeff_lie_lie (x y z : HahnModule Γ R L) (d : Γ) :
    ((of R).symm ⁅x, ⁅y, z⁆⁆).coeff d =
      ∑ p ∈ (antidiagonal ((of R).symm x).isPWO_support
          (((of R).symm y).isPWO_support.add ((of R).symm z).isPWO_support) d).sigma
          fun p ↦ antidiagonal ((of R).symm y).isPWO_support ((of R).symm z).isPWO_support p.2,
        ⁅((of R).symm x).coeff p.1.1, ⁅((of R).symm y).coeff p.2.1,
          ((of R).symm z).coeff p.2.2⁆⁆ := by
  rw [coeff_lie_right' (((of R).symm y).isPWO_support.add ((of R).symm z).isPWO_support)
    (support_lie_subset y z)]
  simp_rw [coeff_lie, lie_sum]
  rw [sum_sigma']

/-- Hahn series with coefficients in a Lie ring form a Lie ring under the convolution bracket. -/
instance instLieRing : LieRing (HahnModule Γ R L) where
  add_lie x y z := by
    ext c
    have hs := ((of R).symm x).isPWO_support.union ((of R).symm y).isPWO_support
    rw [of_symm_add, HahnSeries.coeff_add,
      coeff_lie_left' hs (by rw [of_symm_add]; exact HahnSeries.support_add_subset _ _),
      coeff_lie_left' hs Set.subset_union_left, coeff_lie_left' hs Set.subset_union_right,
      ← sum_add_distrib]
    simp only [of_symm_add, HahnSeries.coeff_add, add_lie]
  lie_add x y z := by
    ext c
    have hs := ((of R).symm y).isPWO_support.union ((of R).symm z).isPWO_support
    rw [of_symm_add, HahnSeries.coeff_add,
      coeff_lie_right' hs (by rw [of_symm_add]; exact HahnSeries.support_add_subset _ _),
      coeff_lie_right' hs Set.subset_union_left, coeff_lie_right' hs Set.subset_union_right,
      ← sum_add_distrib]
    simp only [of_symm_add, HahnSeries.coeff_add, lie_add]
  lie_self x := by
    ext c
    rw [coeff_lie, of_symm_zero, HahnSeries.coeff_zero]
    refine sum_involution (fun ij _ ↦ ij.swap)
      (fun ij _ ↦ add_eq_zero_iff_eq_neg.2 (lie_skew _ _).symm) (fun ⟨i, j⟩ _ h hij ↦ ?_)
      (fun ij hij ↦ swap_mem_antidiagonal.2 hij) (fun _ _ ↦ rfl)
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hij h
    rw [hij.1] at h
    exact h (lie_self _)
  leibniz_lie x y z := by
    ext d
    have hx := ((of R).symm x).isPWO_support
    have hy := ((of R).symm y).isPWO_support
    have hz := ((of R).symm z).isPWO_support
    rw [of_symm_add, HahnSeries.coeff_add, coeff_lie_lie, coeff_lie_lie,
      coeff_lie_left' (hx.add hy) (support_lie_subset x y)]
    simp_rw [coeff_lie, sum_lie]
    rw [sum_sigma']
    refine (sum_congr rfl fun _ _ ↦ leibniz_lie _ _ _).trans ?_
    rw [sum_add_distrib]
    congr 1
    · exact sum_sigma_antidiagonal_assoc hx hy hz d fun i j k ↦
        ⁅⁅((of R).symm x).coeff i, ((of R).symm y).coeff j⁆, ((of R).symm z).coeff k⁆
    · exact (sum_sigma_antidiagonal_left_comm hy hx hz d fun j i k ↦
        ⁅((of R).symm y).coeff j, ⁅((of R).symm x).coeff i, ((of R).symm z).coeff k⁆⁆).symm

/-- Over a linearly ordered `Γ`, the order of a bracket is at least the sum of the orders. -/
theorem orderTop_add_le_lie {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
    [IsOrderedCancelAddMonoid Γ] (x y : HahnModule Γ R L) :
    ((of R).symm x).orderTop + ((of R).symm y).orderTop ≤ ((of R).symm ⁅x, y⁆).orderTop := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hx' : (of R).symm x ≠ 0 := fun h ↦ hx ((of R).symm.injective (h.trans of_symm_zero.symm))
  have hy' : (of R).symm y ≠ 0 := fun h ↦ hy ((of R).symm.injective (h.trans of_symm_zero.symm))
  rw [HahnSeries.orderTop_of_ne_zero hx', HahnSeries.orderTop_of_ne_zero hy', ← WithTop.coe_add,
    ← Set.IsWF.min_add]
  by_cases hxy : (of R).symm ⁅x, y⁆ = 0
  · rw [hxy, HahnSeries.orderTop_zero]
    exact le_top
  · rw [HahnSeries.orderTop_of_ne_zero hxy, WithTop.coe_le_coe]
    exact Set.IsWF.min_le_min_of_subset (support_lie_subset x y)

end LieRing

section LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The convolution bracket is bilinear for the coefficientwise action of `R`. -/
instance instLieAlgebra : LieAlgebra R (HahnModule Γ R L) where
  lie_smul r x y := by
    ext c
    rw [of_symm_smul', HahnSeries.coeff_smul, coeff_lie_right' ((of R).symm y).isPWO_support
      (by rw [of_symm_smul']; exact HahnSeries.support_smul_subset _ _), coeff_lie, smul_sum]
    simp only [of_symm_smul', HahnSeries.coeff_smul, lie_smul]

/-- The convolution bracket is bilinear for the convolution action of the Hahn series
`HahnSeries Γ R`. For `Γ = ℤ` this makes the formal loop algebra `L((t))` a Lie algebra over the
Laurent series `R((t))`. -/
instance instLieAlgebraHahnSeries : LieAlgebra (HahnSeries Γ R) (HahnModule Γ R L) where
  lie_smul f x y := by
    ext d
    have hx := ((of R).symm x).isPWO_support
    have hy := ((of R).symm y).isPWO_support
    rw [coeff_lie_right' (f.isPWO_support.vadd hy) support_smul_subset_vadd_support,
      coeff_smul_right (hx.add hy) (support_lie_subset x y)]
    simp_rw [coeff_smul, coeff_lie, lie_sum, smul_sum, lie_smul]
    rw [sum_sigma', sum_sigma']
    simp_rw [vaddAntidiagonal_eq_antidiagonal f.isPWO_support hy,
      vaddAntidiagonal_eq_antidiagonal f.isPWO_support (hx.add hy)]
    exact sum_sigma_antidiagonal_left_comm hx f.isPWO_support hy d fun i k j ↦
      f.coeff k • ⁅((of R).symm x).coeff i, ((of R).symm y).coeff j⁆

end LieAlgebra

end HahnModule
