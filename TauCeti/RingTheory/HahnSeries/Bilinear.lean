/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Coefficientwise extension of bilinear maps to Hahn series

An `R`-bilinear map `Φ : V → W → M` extends to Hahn series with coefficients in `V` and `W` by
convolution of coefficients,

`Φ(x, y)_c = ∑_{a + b = c} Φ(x_a, y_b)`,

with values in `M`-valued Hahn series. Each sum is finite, because the supports are partially
well-ordered, and the support of `Φ(x, y)` lies in the sum of the supports. On monomials,
`Φ(v tᵃ, w tᵇ) = Φ(v, w) tᵃ⁺ᵇ`. For `Γ = ℤ` and a bilinear form on a module `V` over a field `K`,
this pairs the `V`-valued Laurent series `V((t))` with themselves to the scalar Laurent series
`K((t))`, and coefficients of the result give residue pairings.

The arguments are module-valued series `HahnModule Γ R V`, the carrier on which scalar series act,
and the value is a Hahn series, so that a bilinear form produces a scalar series.

## Main definitions and results

* `HahnModule.convolution Γ Φ`: the coefficientwise extension of `Φ`, as an `R`-bilinear map.
* `HahnModule.coeff_convolution`: the coefficient formula.
* `HahnModule.support_convolution_subset`: the support lies in the sum of the supports.
* `HahnModule.convolution_single_single`: the extension on monomials.

The construction follows the convolution bracket `HahnModule.instBracket` of Lie-valued series.
-/

public section

open Finset Pointwise

noncomputable section

namespace HahnModule

variable (Γ : Type*) {R V W M : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommSemiring R] [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module R W] [AddCommMonoid M] [Module R M]

/-- The function underlying `HahnModule.convolution`. -/
private def convolutionFun (Φ : V →ₗ[R] W →ₗ[R] M) (x : HahnModule Γ R V)
    (y : HahnModule Γ R W) : HahnSeries Γ M where
  coeff c := ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support ((of R).symm y).isPWO_support c,
    Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2)
  isPWO_support' := (((of R).symm x).isPWO_support.add ((of R).symm y).isPWO_support).mono
    fun c hc ↦ by
      obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
      rw [mem_antidiagonal] at hij
      exact ⟨ij.1, hij.1, ij.2, hij.2.1, hij.2.2⟩

variable {Γ}

/-- The coefficients of `convolutionFun` may be computed over any partially well-ordered set
containing the support of the first argument. -/
private theorem coeff_convolutionFun_left {Φ : V →ₗ[R] W →ₗ[R] M} {x : HahnModule Γ R V}
    {y : HahnModule Γ R W} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hxs : ((of R).symm x).support ⊆ s) :
    (convolutionFun Γ Φ x y).coeff c =
      ∑ ij ∈ antidiagonal hs ((of R).symm y).isPWO_support c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) := by
  refine sum_subset (antidiagonal_mono_left hxs) fun ij hij hij' ↦ ?_
  rw [mem_antidiagonal] at hij
  by_cases h : ((of R).symm x).coeff ij.1 = 0
  · rw [h, map_zero, LinearMap.zero_apply]
  · exact (hij' (mem_antidiagonal.2 ⟨h, hij.2⟩)).elim

/-- The coefficients of `convolutionFun` may be computed over any partially well-ordered set
containing the support of the second argument. -/
private theorem coeff_convolutionFun_right {Φ : V →ₗ[R] W →ₗ[R] M} {x : HahnModule Γ R V}
    {y : HahnModule Γ R W} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hys : ((of R).symm y).support ⊆ s) :
    (convolutionFun Γ Φ x y).coeff c =
      ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support hs c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) := by
  refine sum_subset (antidiagonal_mono_right hys) fun ij hij hij' ↦ ?_
  rw [mem_antidiagonal] at hij
  by_cases h : ((of R).symm y).coeff ij.2 = 0
  · rw [h, map_zero]
  · exact (hij' (mem_antidiagonal.2 ⟨hij.1, h, hij.2.2⟩)).elim

variable (Γ) in
/-- The coefficientwise extension `Φ(x, y)_c = ∑_{a + b = c} Φ(x_a, y_b)` of an `R`-bilinear map
`Φ : V → W → M` to Hahn series with coefficients in `V` and `W`. -/
def convolution (Φ : V →ₗ[R] W →ₗ[R] M) :
    HahnModule Γ R V →ₗ[R] HahnModule Γ R W →ₗ[R] HahnSeries Γ M :=
  LinearMap.mk₂ R (convolutionFun Γ Φ)
    (fun x₁ x₂ y ↦ by
      ext c
      have hs := ((of R).symm x₁).isPWO_support.union ((of R).symm x₂).isPWO_support
      rw [HahnSeries.coeff_add, coeff_convolutionFun_left hs (by
          rw [of_symm_add]; exact HahnSeries.support_add_subset _ _),
        coeff_convolutionFun_left hs Set.subset_union_left,
        coeff_convolutionFun_left hs Set.subset_union_right, ← sum_add_distrib]
      simp only [of_symm_add, HahnSeries.coeff_add, map_add, LinearMap.add_apply])
    (fun r x y ↦ by
      ext c
      rw [HahnSeries.coeff_smul, coeff_convolutionFun_left ((of R).symm x).isPWO_support (by
          rw [of_symm_smul']; exact HahnSeries.support_smul_subset _ _),
        coeff_convolutionFun_left ((of R).symm x).isPWO_support subset_rfl, smul_sum]
      simp only [of_symm_smul', HahnSeries.coeff_smul, map_smul, LinearMap.smul_apply])
    (fun x y₁ y₂ ↦ by
      ext c
      have hs := ((of R).symm y₁).isPWO_support.union ((of R).symm y₂).isPWO_support
      rw [HahnSeries.coeff_add, coeff_convolutionFun_right hs (by
          rw [of_symm_add]; exact HahnSeries.support_add_subset _ _),
        coeff_convolutionFun_right hs Set.subset_union_left,
        coeff_convolutionFun_right hs Set.subset_union_right, ← sum_add_distrib]
      simp only [of_symm_add, HahnSeries.coeff_add, map_add])
    (fun r x y ↦ by
      ext c
      rw [HahnSeries.coeff_smul, coeff_convolutionFun_right ((of R).symm y).isPWO_support (by
          rw [of_symm_smul']; exact HahnSeries.support_smul_subset _ _),
        coeff_convolutionFun_right ((of R).symm y).isPWO_support subset_rfl, smul_sum]
      simp only [of_symm_smul', HahnSeries.coeff_smul, map_smul])

/-- The coefficient formula `Φ(x, y)_c = ∑_{a + b = c} Φ(x_a, y_b)`. -/
theorem coeff_convolution (Φ : V →ₗ[R] W →ₗ[R] M) (x : HahnModule Γ R V) (y : HahnModule Γ R W)
    (c : Γ) :
    (convolution Γ Φ x y).coeff c =
      ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support ((of R).symm y).isPWO_support c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) :=
  (rfl)

/-- The support of `Φ(x, y)` lies in the sum of the supports of `x` and `y`. -/
theorem support_convolution_subset (Φ : V →ₗ[R] W →ₗ[R] M) (x : HahnModule Γ R V)
    (y : HahnModule Γ R W) :
    (convolution Γ Φ x y).support ⊆ ((of R).symm x).support + ((of R).symm y).support :=
  fun c hc ↦ by
    obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    rw [mem_antidiagonal] at hij
    exact ⟨ij.1, hij.1, ij.2, hij.2.1, hij.2.2⟩

/-- The extension on monomials: `Φ(v tᵃ, w tᵇ) = Φ(v, w) tᵃ⁺ᵇ`. -/
@[simp]
theorem convolution_single_single (Φ : V →ₗ[R] W →ₗ[R] M) (a b : Γ) (v : V) (w : W) :
    convolution Γ Φ (of R (HahnSeries.single a v)) (of R (HahnSeries.single b w)) =
      HahnSeries.single (a + b) (Φ v w) := by
  ext c
  simp only [coeff_convolution, Equiv.symm_apply_apply]
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

end HahnModule
