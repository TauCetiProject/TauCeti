/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Coefficientwise extension of bilinear maps to Hahn series

A biadditive map `Φ : V → W → M` extends to Hahn series with coefficients in `V` and `W` by
convolution of coefficients,

`Φ(x, y)_c = ∑_{a + b = c} Φ(x_a, y_b)`,

with values in `M`-valued Hahn series. Each sum is finite, because the supports are partially
well-ordered, and the support of `Φ(x, y)` lies in the sum of the supports. On monomials,
`Φ(v tᵃ, w tᵇ) = Φ(v, w) tᵃ⁺ᵇ`, and if `Φ` is `R`-bilinear then so is its extension. For `Γ = ℤ`
and a bilinear form on a module `V` over a field `K`, this pairs the `V`-valued Laurent series
`V((t))` with themselves to the scalar Laurent series `K((t))`, and coefficients of the result give
residue pairings.

The arguments are module-valued series `HahnModule Γ R V`, the carrier on which scalar series act,
and the value is a Hahn series, so that a bilinear form produces a scalar series.

## Main definitions and results

* `HahnModule.convolutionAddMonoidHom Γ R Φ`: the coefficientwise extension of a biadditive map
  `Φ`, as a biadditive map.
* `HahnModule.convolution Γ Φ`: the coefficientwise extension of an `R`-bilinear map `Φ`, as an
  `R`-bilinear map.
* `HahnModule.convolution_apply`: the extension of a bilinear map is the extension of the
  underlying biadditive map.
* `HahnModule.coeff_convolutionAddMonoidHom`, `HahnModule.coeff_convolution`: the coefficient
  formula.
* `HahnModule.support_convolutionAddMonoidHom_subset`, `HahnModule.support_convolution_subset`:
  the support lies in the sum of the supports.
* `HahnModule.convolutionAddMonoidHom_single_single`, `HahnModule.convolution_single_single`: the
  extension on monomials.

The convolution bracket `HahnModule.instBracket` of Lie-valued series is the extension of the
biadditive Lie bracket.
-/

public section

open Finset Pointwise

noncomputable section

namespace HahnModule

variable {Γ R V W M : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid M]

section AddMonoidHom

variable [SMul R V] [SMul R W]

variable (Γ R) in
/-- The function underlying `HahnModule.convolutionAddMonoidHom`. -/
private def convolutionFun (Φ : V →+ W →+ M) (x : HahnModule Γ R V)
    (y : HahnModule Γ R W) : HahnSeries Γ M where
  coeff c := ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support ((of R).symm y).isPWO_support c,
    Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2)
  isPWO_support' := (((of R).symm x).isPWO_support.add ((of R).symm y).isPWO_support).mono
    fun c hc ↦ by
      obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
      rw [mem_antidiagonal] at hij
      exact ⟨ij.1, hij.1, ij.2, hij.2.1, hij.2.2⟩

/-- The coefficients of `convolutionFun` may be computed over any partially well-ordered set
containing the support of the first argument. -/
private theorem coeff_convolutionFun_left {Φ : V →+ W →+ M} {x : HahnModule Γ R V}
    {y : HahnModule Γ R W} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hxs : ((of R).symm x).support ⊆ s) :
    (convolutionFun Γ R Φ x y).coeff c =
      ∑ ij ∈ antidiagonal hs ((of R).symm y).isPWO_support c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) := by
  refine sum_subset (antidiagonal_mono_left hxs) fun ij hij hij' ↦ ?_
  rw [mem_antidiagonal] at hij
  by_cases h : ((of R).symm x).coeff ij.1 = 0
  · rw [h, map_zero, AddMonoidHom.zero_apply]
  · exact (hij' (mem_antidiagonal.2 ⟨h, hij.2⟩)).elim

/-- The coefficients of `convolutionFun` may be computed over any partially well-ordered set
containing the support of the second argument. -/
private theorem coeff_convolutionFun_right {Φ : V →+ W →+ M} {x : HahnModule Γ R V}
    {y : HahnModule Γ R W} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hys : ((of R).symm y).support ⊆ s) :
    (convolutionFun Γ R Φ x y).coeff c =
      ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support hs c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) := by
  refine sum_subset (antidiagonal_mono_right hys) fun ij hij hij' ↦ ?_
  rw [mem_antidiagonal] at hij
  by_cases h : ((of R).symm y).coeff ij.2 = 0
  · rw [h, map_zero]
  · exact (hij' (mem_antidiagonal.2 ⟨hij.1, h, hij.2.2⟩)).elim

variable (Γ R) in
/-- The coefficientwise extension `Φ(x, y)_c = ∑_{a + b = c} Φ(x_a, y_b)` of a biadditive map
`Φ : V → W → M` to Hahn series with coefficients in `V` and `W`, as a biadditive map. -/
def convolutionAddMonoidHom (Φ : V →+ W →+ M) :
    HahnModule Γ R V →+ HahnModule Γ R W →+ HahnSeries Γ M where
  toFun x :=
    { toFun := convolutionFun Γ R Φ x
      map_zero' := by
        ext c
        simp [convolutionFun]
      map_add' := fun y₁ y₂ ↦ by
        ext c
        have hs := ((of R).symm y₁).isPWO_support.union ((of R).symm y₂).isPWO_support
        rw [HahnSeries.coeff_add, coeff_convolutionFun_right hs (by
            rw [of_symm_add]; exact HahnSeries.support_add_subset _ _),
          coeff_convolutionFun_right hs Set.subset_union_left,
          coeff_convolutionFun_right hs Set.subset_union_right, ← sum_add_distrib]
        simp only [of_symm_add, HahnSeries.coeff_add, map_add] }
  map_zero' := by
    ext y c
    simp [convolutionFun]
  map_add' x₁ x₂ := by
    ext y c
    have hs := ((of R).symm x₁).isPWO_support.union ((of R).symm x₂).isPWO_support
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
    rw [HahnSeries.coeff_add, coeff_convolutionFun_left hs (by
        rw [of_symm_add]; exact HahnSeries.support_add_subset _ _),
      coeff_convolutionFun_left hs Set.subset_union_left,
      coeff_convolutionFun_left hs Set.subset_union_right, ← sum_add_distrib]
    simp only [of_symm_add, HahnSeries.coeff_add, map_add, AddMonoidHom.add_apply]

/-- The coefficient formula `Φ(x, y)_c = ∑_{a + b = c} Φ(x_a, y_b)`. -/
theorem coeff_convolutionAddMonoidHom (Φ : V →+ W →+ M) (x : HahnModule Γ R V)
    (y : HahnModule Γ R W) (c : Γ) :
    (convolutionAddMonoidHom Γ R Φ x y).coeff c =
      ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support ((of R).symm y).isPWO_support c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) :=
  (rfl)

/-- The coefficients of `convolutionAddMonoidHom Γ R Φ x y` may be computed over any partially
well-ordered set containing the support of `x`. -/
theorem coeff_convolutionAddMonoidHom_left' {Φ : V →+ W →+ M} {x : HahnModule Γ R V}
    {y : HahnModule Γ R W} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hxs : ((of R).symm x).support ⊆ s) :
    (convolutionAddMonoidHom Γ R Φ x y).coeff c =
      ∑ ij ∈ antidiagonal hs ((of R).symm y).isPWO_support c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) :=
  coeff_convolutionFun_left hs hxs

/-- The coefficients of `convolutionAddMonoidHom Γ R Φ x y` may be computed over any partially
well-ordered set containing the support of `y`. -/
theorem coeff_convolutionAddMonoidHom_right' {Φ : V →+ W →+ M} {x : HahnModule Γ R V}
    {y : HahnModule Γ R W} {c : Γ} {s : Set Γ} (hs : s.IsPWO)
    (hys : ((of R).symm y).support ⊆ s) :
    (convolutionAddMonoidHom Γ R Φ x y).coeff c =
      ∑ ij ∈ antidiagonal ((of R).symm x).isPWO_support hs c,
        Φ (((of R).symm x).coeff ij.1) (((of R).symm y).coeff ij.2) :=
  coeff_convolutionFun_right hs hys

/-- The support of `Φ(x, y)` lies in the sum of the supports of `x` and `y`. -/
theorem support_convolutionAddMonoidHom_subset (Φ : V →+ W →+ M) (x : HahnModule Γ R V)
    (y : HahnModule Γ R W) :
    (convolutionAddMonoidHom Γ R Φ x y).support ⊆
      ((of R).symm x).support + ((of R).symm y).support :=
  fun c hc ↦ by
    obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    rw [mem_antidiagonal] at hij
    exact ⟨ij.1, hij.1, ij.2, hij.2.1, hij.2.2⟩

/-- The extension on monomials: `Φ(v tᵃ, w tᵇ) = Φ(v, w) tᵃ⁺ᵇ`. -/
@[simp]
theorem convolutionAddMonoidHom_single_single (Φ : V →+ W →+ M) (a b : Γ) (v : V) (w : W) :
    convolutionAddMonoidHom Γ R Φ (of R (HahnSeries.single a v)) (of R (HahnSeries.single b w)) =
      HahnSeries.single (a + b) (Φ v w) := by
  ext c
  simp only [coeff_convolutionAddMonoidHom, Equiv.symm_apply_apply]
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

end AddMonoidHom

section LinearMap

variable [CommSemiring R] [Module R V] [Module R W] [Module R M]

variable (Γ) in
/-- The coefficientwise extension `Φ(x, y)_c = ∑_{a + b = c} Φ(x_a, y_b)` of an `R`-bilinear map
`Φ : V → W → M` to Hahn series with coefficients in `V` and `W`. It is
`HahnModule.convolutionAddMonoidHom` of `Φ`, which is moreover `R`-bilinear. -/
def convolution (Φ : V →ₗ[R] W →ₗ[R] M) :
    HahnModule Γ R V →ₗ[R] HahnModule Γ R W →ₗ[R] HahnSeries Γ M :=
  LinearMap.mk₂ R
    (fun x y ↦ convolutionAddMonoidHom Γ R (LinearMap.toAddMonoidHom'.comp Φ.toAddMonoidHom) x y)
    (fun x₁ x₂ y ↦ by rw [map_add, AddMonoidHom.add_apply])
    (fun r x y ↦ by
      ext c
      rw [HahnSeries.coeff_smul, coeff_convolutionAddMonoidHom_left' ((of R).symm x).isPWO_support
          (by rw [of_symm_smul']; exact HahnSeries.support_smul_subset _ _),
        coeff_convolutionAddMonoidHom, smul_sum]
      simp [of_symm_smul'])
    (fun x y₁ y₂ ↦ map_add _ y₁ y₂)
    (fun r x y ↦ by
      ext c
      rw [HahnSeries.coeff_smul, coeff_convolutionAddMonoidHom_right' ((of R).symm y).isPWO_support
          (by rw [of_symm_smul']; exact HahnSeries.support_smul_subset _ _),
        coeff_convolutionAddMonoidHom, smul_sum]
      simp [of_symm_smul'])

/-- The extension of an `R`-bilinear map is the extension `convolutionAddMonoidHom` of the
underlying biadditive map. -/
theorem convolution_apply (Φ : V →ₗ[R] W →ₗ[R] M) (x : HahnModule Γ R V) (y : HahnModule Γ R W) :
    convolution Γ Φ x y =
      convolutionAddMonoidHom Γ R (LinearMap.toAddMonoidHom'.comp Φ.toAddMonoidHom) x y :=
  (rfl)

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
  support_convolutionAddMonoidHom_subset _ x y

/-- The extension on monomials: `Φ(v tᵃ, w tᵇ) = Φ(v, w) tᵃ⁺ᵇ`. -/
@[simp]
theorem convolution_single_single (Φ : V →ₗ[R] W →ₗ[R] M) (a b : Γ) (v : V) (w : W) :
    convolution Γ Φ (of R (HahnSeries.single a v)) (of R (HahnSeries.single b w)) =
      HahnSeries.single (a + b) (Φ v w) :=
  convolutionAddMonoidHom_single_single _ a b v w

end LinearMap

end HahnModule
