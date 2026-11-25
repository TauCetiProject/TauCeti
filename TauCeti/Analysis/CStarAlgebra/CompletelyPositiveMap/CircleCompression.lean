/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.AsymptoticDomain
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.Fourier.TrigonometricPolynomial

/-!
# Compressions of `C(𝕋)` to trigonometric polynomials of bounded degree

Let `𝕋 = AddCircle 1` with normalized Haar measure, and let `Vₙ : ℂⁿ → L²(𝕋)` be the isometry
onto `span {z⁰, …, z^{n-1}}` sending the `j`-th basis vector to the Fourier monomial `zʲ`
(`TauCeti.fourierEmbedding`). Compressing the multiplication representation
`f ↦ M_f` of `C(𝕋)` on `L²(𝕋)` (`TauCeti.continuousMapMultiplication`) by `Vₙ` gives completely
positive contractions

```text
φₙ : C(𝕋) → Mₙ,   φₙ(f) = Vₙ† M_f Vₙ
```

(`TauCeti.circleCompression`). Their multiplicativity defects at `z⁻¹` separate the 2-norm and
the norm: `d₂(φₙ, z⁻¹) = d₂(φₙ, z) = 1/n`, while `d_∞(φₙ, z⁻¹) = 1` for `n ≠ 0`. So `z` lies in the
asymptotic 2-norm multiplicative domain `D₂` of the sequence `(φₙ)` but not in its asymptotic norm
multiplicative domain `D_∞`. Since `z` generates `C(𝕋)` as a C⋆-algebra, `D₂ = C(𝕋)`, while
`D_∞ ≠ C(𝕋)`.

## Main declarations

* `TauCeti.circleCompression n`: the compression `φₙ` as a completely positive map,
  `TauCeti.circleCompression_apply`: its entries are `⟪zⁱ, M_f zʲ⟫`,
  `TauCeti.circleCompression_one`: it is unital, and
  `TauCeti.norm_circleCompression_le`: it is contractive.
* `TauCeti.twoNormDefect_circleCompression_fourier_neg_one`,
  `TauCeti.twoNormDefect_circleCompression_fourier_one`: `d₂(φₙ, z⁻¹) = d₂(φₙ, z) = 1/n`.
* `TauCeti.normDefect_circleCompression_fourier_neg_one`: `d_∞(φₙ, z⁻¹) = 1`.
* `TauCeti.asymptoticTwoNormDomain_circleCompression_eq_top`: `D₂ = C(𝕋)`.
* `TauCeti.asymptoticNormDomain_circleCompression_ne_top`: `D_∞ ≠ C(𝕋)`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), proof of Theorem 3.1.6, for the asymptotic multiplicative domains.
-/

public section

open MeasureTheory AddCircle Filter Topology
open scoped ENNReal InnerProductSpace ComplexOrder CStarAlgebra

namespace TauCeti

section Circle

open CompletelyPositiveMap CStarMatrix

/-- **The compression of `C(𝕋)` to `span {z⁰, …, z^{n-1}}`**: the completely positive map
`φₙ : C(𝕋) → Mₙ`, `φₙ(f) = V† M_f V`, where `M_f` is multiplication by `f` on `L²(𝕋)` and
`V = fourierEmbedding n`. -/
noncomputable def circleCompression (n : ℕ) :
    C(AddCircle (1 : ℝ), ℂ) →CP CStarMatrix (Fin n) (Fin n) ℂ :=
  (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (toEuclideanCLM (n := Fin n)).symm).comp
    ((fourierEmbedding (T := 1) n).conjAdjoint.comp
      (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
        (continuousMapMultiplication (haarAddCircle (T := 1)))))

/-- The operator of `φₙ(f)` on `ℂⁿ` is `V† M_f V`. -/
@[simp]
theorem toEuclideanCLM_circleCompression (n : ℕ) (f : C(AddCircle (1 : ℝ), ℂ)) :
    toEuclideanCLM (circleCompression n f) =
      (fourierEmbedding (T := 1) n).adjoint ∘L
        (continuousMapMultiplication haarAddCircle f ∘L fourierEmbedding n) := by
  simp [circleCompression]

/-- The entries of `φₙ(f)` are the matrix coefficients `⟪zⁱ, M_f zʲ⟫` of the multiplication
operator `M_f` on the Fourier monomials. -/
theorem circleCompression_apply (n : ℕ) (f : C(AddCircle (1 : ℝ), ℂ)) (i j : Fin n) :
    circleCompression n f i j =
      ⟪fourierLp (T := 1) 2 (i : ℤ),
        continuousMapMultiplication haarAddCircle f (fourierLp (T := 1) 2 (j : ℤ))⟫_ℂ := by
  rw [← inner_single_toEuclideanCLM_single (circleCompression n f) i j]
  simp [ContinuousLinearMap.adjoint_inner_right]

/-- The compressions `φₙ` are unital: `φₙ(1) = 1`, since `V† V = 1`. -/
@[simp]
theorem circleCompression_one (n : ℕ) : circleCompression n 1 = 1 := by
  rw [← (EquivLike.injective toEuclideanCLM).eq_iff]
  simp [ContinuousLinearMap.one_def, LinearIsometry.adjoint_comp_self]

/-- The compressions `φₙ` are contractions. -/
theorem norm_circleCompression_le (n : ℕ) (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖circleCompression n f‖ ≤ ‖f‖ := by
  refine (CompletelyPositiveMapClass.norm_apply_le _ f).trans
    (mul_le_of_le_one_left (norm_nonneg _) ?_)
  rw [← norm_toEuclideanCLM, circleCompression_one, map_one]
  exact ContinuousLinearMap.norm_id_le

/-- The operator of the multiplicativity defect `φₙ(f⋆f) - φₙ(f)⋆φₙ(f)` on `ℂⁿ` is
`V† M_{f⋆f} V - (V† M_f V)† (V† M_f V)`. -/
private theorem toEuclideanCLM_circleCompression_defect (n : ℕ) (f : C(AddCircle (1 : ℝ), ℂ)) :
    toEuclideanCLM (circleCompression n (star f * f) -
        star (circleCompression n f) * circleCompression n f) =
      (fourierEmbedding (T := 1) n).adjoint ∘L
          (continuousMapMultiplication haarAddCircle (star f * f) ∘L fourierEmbedding n) -
        ((fourierEmbedding (T := 1) n).adjoint ∘L
            (continuousMapMultiplication haarAddCircle f ∘L fourierEmbedding n)).adjoint ∘L
          ((fourierEmbedding (T := 1) n).adjoint ∘L
            (continuousMapMultiplication haarAddCircle f ∘L fourierEmbedding n)) := by
  simp [map_star toEuclideanCLM, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def]

/-- The diagonal entries of the defect matrix `φₙ((zᵐ)⋆zᵐ) - φₙ(zᵐ)⋆φₙ(zᵐ)`: the `i`-th one is `1`
when `z^{m+i}` leaves `span {z⁰, …, z^{n-1}}`, and `0` otherwise. -/
theorem circleCompression_defect_fourier_apply_self (n : ℕ) (m : ℤ) (i : Fin n) :
    (circleCompression n (star (fourier m) * fourier m) -
        star (circleCompression n (fourier m)) * circleCompression n (fourier m)) i i =
      ((1 - if 0 ≤ m + i ∧ m + i < n then 1 else 0 : ℝ) : ℂ) := by
  have h : ‖(fourierEmbedding (T := 1) n).adjoint (fourierLp (T := 1) 2 (m + i))‖ ^ 2 =
      if 0 ≤ m + i ∧ m + i < n then 1 else 0 := by
    rw [adjoint_fourierEmbedding_fourierLp]
    split_ifs <;> simp
  have hV : fourierEmbedding (T := 1) n (EuclideanSpace.single i 1) = fourierLp 2 (i : ℤ) := by
    simp
  refine (inner_single_toEuclideanCLM_single _ i i).symm.trans ?_
  rw [toEuclideanCLM_circleCompression_defect, star_fourier_mul_fourier, map_one, ← h]
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right, one_apply_eq_self, hV,
    continuousMapMultiplication_fourier_fourierLp, inner_self_eq_norm_sq_to_K]
  simp [orthonormal_fourier.1]

private theorem twoNormDefect_circleCompression_fourier (n : ℕ) (m : ℤ) :
    (circleCompression n).twoNormDefect (fourier m) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, (1 - if 0 ≤ m + i ∧ m + i < n then 1 else 0 : ℝ) := by
  rw [twoNormDefect_def, normalizedTrace_eq_sum]
  simp_rw [circleCompression_defect_fourier_apply_self]
  simp

/-- `d₂(φₙ, zᵐ) = 1/n` when `z^{m+i}` leaves `span {z⁰, …, z^{n-1}}` for exactly one index
`i = i₀`. -/
private theorem twoNormDefect_circleCompression_fourier_eq_inv {n : ℕ} (m : ℤ) (i₀ : Fin n)
    (h : ∀ i : Fin n, (0 ≤ m + i ∧ m + i < n) ↔ i ≠ i₀) :
    (circleCompression n).twoNormDefect (fourier m) = (n : ℝ)⁻¹ := by
  rw [twoNormDefect_circleCompression_fourier, Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _)
    fun i _ hi ↦ by simp [(h i).2 hi]]
  simp [h]

/-- **The 2-norm defect of `φₙ` at `z⁻¹` is `1/n`**: `d₂(φₙ, z⁻¹) = 1/n`. -/
theorem twoNormDefect_circleCompression_fourier_neg_one (n : ℕ) :
    (circleCompression n).twoNormDefect (fourier (-1)) = (n : ℝ)⁻¹ := by
  rcases n with _ | n
  · simp [twoNormDefect_circleCompression_fourier]
  · refine twoNormDefect_circleCompression_fourier_eq_inv (-1) 0 fun i ↦ ?_
    have := i.isLt
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
    omega

/-- **The 2-norm defect of `φₙ` at `z` is `1/n`**: `d₂(φₙ, z) = 1/n`. -/
theorem twoNormDefect_circleCompression_fourier_one (n : ℕ) :
    (circleCompression n).twoNormDefect (fourier 1) = (n : ℝ)⁻¹ := by
  rcases n with _ | n
  · simp [twoNormDefect_circleCompression_fourier]
  · refine twoNormDefect_circleCompression_fourier_eq_inv 1 (Fin.last n) fun i ↦ ?_
    have := i.isLt
    simp only [ne_eq, Fin.ext_iff, Fin.val_last]
    omega

/-- **The norm defect of `φₙ` at `z⁻¹` is `1`** for `n ≠ 0`: `d_∞(φₙ, z⁻¹) = 1`. -/
theorem normDefect_circleCompression_fourier_neg_one {n : ℕ} (hn : n ≠ 0) :
    (circleCompression n).normDefect (fourier (-1)) = 1 := by
  refine le_antisymm ?_ ?_
  · have h := sqrt_normDefect_le (norm_circleCompression_le n) (fourier (-1))
    rw [fourier_norm, Real.sqrt_le_one] at h
    exact h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [normDefect_def]
    refine le_trans (le_of_eq ?_) (CStarMatrix.norm_entry_le_norm (i := 0) (j := 0))
    rw [circleCompression_defect_fourier_apply_self]
    simp

/-- Every Fourier monomial `zᵐ` lies in the asymptotic 2-norm multiplicative domain of the
compressions `φₙ`. -/
theorem fourier_mem_asymptoticTwoNormDomain_circleCompression (m : ℤ) :
    fourier m ∈ asymptoticTwoNormDomain atTop circleCompression norm_circleCompression_le := by
  set D := asymptoticTwoNormDomain atTop circleCompression norm_circleCompression_le
  have hneg : fourier (T := 1) (-1) ∈ D := by
    rw [mem_asymptoticTwoNormDomain_iff, star_fourier, neg_neg]
    simp only [twoNormDefect_circleCompression_fourier_neg_one,
      twoNormDefect_circleCompression_fourier_one]
    exact ⟨tendsto_inv_atTop_nhds_zero_nat, tendsto_inv_atTop_nhds_zero_nat⟩
  have hone : fourier (T := 1) 1 ∈ D := by
    simpa [star_fourier] using star_mem hneg
  induction m using Int.induction_on with
  | zero => rw [← neg_add_cancel (1 : ℤ), fourier_add_eq_mul]; exact mul_mem hneg hone
  | succ k hk => rw [fourier_add_eq_mul]; exact mul_mem hk hone
  | pred k hk => rw [sub_eq_add_neg, fourier_add_eq_mul]; exact mul_mem hk hneg

/-- **The asymptotic 2-norm multiplicative domain of the compressions `φₙ` is all of `C(𝕋)`**:
`z` lies in it, and `z` generates `C(𝕋)` as a C⋆-algebra. -/
theorem asymptoticTwoNormDomain_circleCompression_eq_top :
    asymptoticTwoNormDomain atTop circleCompression norm_circleCompression_le = ⊤ := by
  set D := asymptoticTwoNormDomain atTop circleCompression norm_circleCompression_le
  have hspan : Submodule.span ℂ (Set.range (fourier (T := 1))) ≤
      D.toNonUnitalSubalgebra.toSubmodule :=
    Submodule.span_le.mpr (by
      rintro _ ⟨m, rfl⟩
      exact fourier_mem_asymptoticTwoNormDomain_circleCompression m)
  have hcl := Submodule.topologicalClosure_minimal _ hspan
    (isClosed_asymptoticTwoNormDomain norm_circleCompression_le)
  rw [span_fourier_closure_eq_top] at hcl
  exact NonUnitalStarAlgebra.eq_top_iff.mpr fun f ↦ hcl Submodule.mem_top

/-- `z⁻¹` does not lie in the asymptotic norm multiplicative domain of the compressions `φₙ`. -/
theorem fourier_neg_one_notMem_asymptoticNormDomain_circleCompression :
    fourier (-1) ∉ asymptoticNormDomain atTop circleCompression norm_circleCompression_le := by
  rw [mem_asymptoticNormDomain_iff]
  rintro ⟨h, -⟩
  have h1 : Tendsto (fun n ↦ (circleCompression n).normDefect (fourier (-1))) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun n hn ↦
      (normDefect_circleCompression_fourier_neg_one hn).symm)
  exact one_ne_zero (tendsto_nhds_unique h1 h)

/-- **The asymptotic norm multiplicative domain of the compressions `φₙ` is not all of `C(𝕋)`**,
although their asymptotic 2-norm multiplicative domain is
(`TauCeti.asymptoticTwoNormDomain_circleCompression_eq_top`). -/
theorem asymptoticNormDomain_circleCompression_ne_top :
    asymptoticNormDomain atTop circleCompression norm_circleCompression_le ≠ ⊤ := fun h ↦
  fourier_neg_one_notMem_asymptoticNormDomain_circleCompression
    (h ▸ NonUnitalStarAlgebra.mem_top)

end Circle

end TauCeti
