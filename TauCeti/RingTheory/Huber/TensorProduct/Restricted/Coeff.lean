/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Restricted.Polydisc
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Rename
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Coefficients of completed tensor products of closed polydiscs

Over a complete Hausdorff nonarchimedean ring `A`, every element of `A⟨T₁, …, Tₖ⟩` is a restricted
power series (`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv`), so it has coefficients.
Under the isomorphism `TauCeti.Huber.CompletedTensor.polydiscEquiv` of
`A⟨T₁, …, Tₘ⟩ ⊗̂_A A⟨S₁, …, Sₙ⟩` with `A⟨T₁, …, Tₘ, S₁, …, Sₙ⟩`, the two factors are renamed into
the two blocks of variables. For one variable on each side, the coefficient of `TⁱSʲ` in the image
of `f ⊗ g` is therefore the product of the coefficient of `Tⁱ` in `f` and that of `Sʲ` in `g`.

Over a field this bounds the rank of the coefficient matrix `(c_{ij})` of the image of an element
of the algebraic tensor product `A⟨T⟩ ⊗_A A⟨S⟩` by the number of its pure tensors. An element
whose coefficient matrix is diagonal with nonzero diagonal, such as `Σₙ πⁿTⁿSⁿ` for a nonzero
topologically nilpotent `π`, is thus not in the image: the completed tensor product of two
one-variable Tate algebras is strictly larger than the algebraic one, so the finiteness hypothesis
in the comparison of completed and algebraic tensor products for finite algebras cannot be
dropped.

## Main definitions

* `TauCeti.Huber.CompletedTensor.toMvPowerSeries A k`: the power series of an element of
  `A⟨T₁, …, Tₖ⟩`.
* `TauCeti.Huber.CompletedTensor.coeffMatrix N y`: the `N × N` matrix of coefficients of `TⁱSʲ` in
  `y ∈ A⟨T, S⟩`.
* `TauCeti.Huber.CompletedTensor.diagonalSeries π`: the element `Σₙ πⁿTⁿSⁿ` of `A⟨T, S⟩`.

## Main results

* `TauCeti.Huber.CompletedTensor.coe_restrictedMvPowerSeriesCompletionEquiv_polydiscEquiv_inl`,
  `…_inr`: the two factors are renamed into the two blocks of variables.
* `TauCeti.Huber.CompletedTensor.coeff_polydiscEquiv_inl_mul_inr`: the coefficient of `TⁱSʲ` in
  the image of `f ⊗ g` is the product of coefficients.
* `TauCeti.Huber.CompletedTensor.exists_rank_coeffMatrix_le`: over a field, the coefficient
  matrices of the image of an element of the algebraic tensor product have bounded rank.
* `TauCeti.Huber.CompletedTensor.diagonalSeries_notMem_range`: `Σₙ πⁿTⁿSⁿ` is not in the image of
  the algebraic tensor product.
-/

public section

open MvPowerSeries Finsupp
open scoped TensorProduct

namespace TauCeti.Huber.CompletedTensor

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]

variable (A) in
/-- The power series of an element of `A⟨T₁, …, Tₖ⟩` over a complete Hausdorff base, as a ring
homomorphism. -/
noncomputable def toMvPowerSeries (k : ℕ) :
    restrictedMvPowerSeriesCompletion k A →+* MvPowerSeries (Fin k) A :=
  (Subring.subtype _).comp (restrictedMvPowerSeriesCompletionEquiv k A).toRingHom

omit [IsHuberRing A] in
theorem toMvPowerSeries_apply {k : ℕ} (f : restrictedMvPowerSeriesCompletion k A) :
    toMvPowerSeries A k f = (restrictedMvPowerSeriesCompletionEquiv k A f : _) :=
  (rfl)

omit [IsHuberRing A] in
private theorem weightedRename_comp_equiv {k l : ℕ} (e : Fin k ↪ Fin l)
    (φ : restrictedMvPowerSeriesCompletion k A →+* restrictedMvPowerSeriesCompletion l A)
    (hφ : Continuous φ) (hC : ∀ a, φ (algebraMap A _ a) = algebraMap A _ a)
    (hX : ∀ i, φ (Pair.polydiscVar k A i) = Pair.polydiscVar l A (e i))
    (f : restrictedMvPowerSeriesCompletion k A) :
    toMvPowerSeries A l (φ f) = rename e (toMvPowerSeries A k f) := by
  have h : (restrictedMvPowerSeriesCompletionEquiv l A).toRingHom.comp φ =
      (weightedRename e _ _ fun _ ↦ subset_rfl).comp
        (restrictedMvPowerSeriesCompletionEquiv k A).toRingHom := by
    refine restrictedMvPowerSeriesCompletion_ringHom_ext
      (uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous.comp hφ)
      ((continuous_weightedRename _ _ _ _).comp
        uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous) (fun a ↦ ?_)
      fun i ↦ ?_
    · simp only [RingHom.comp_apply, hC]
      simp [algebraMap_completion_weightedRestrictedSubring_apply, weightedRename_weightedC]
    · simp [hX, weightedRename_weightedX]
  have h' := congr(($h f : MvPowerSeries (Fin l) A))
  rw [toMvPowerSeries_apply, toMvPowerSeries_apply]
  simpa [coe_weightedRename] using h'

variable (m n : ℕ)

/-- Under `polydiscEquiv`, an element of the left factor is renamed into the first block of
variables. -/
theorem coe_restrictedMvPowerSeriesCompletionEquiv_polydiscEquiv_inl
    (f : restrictedMvPowerSeriesCompletion m A) :
    toMvPowerSeries A (m + n) (polydiscEquiv A m n (inl A _ _ f)) =
      rename (Fin.castAddEmb n) (toMvPowerSeries A m f) :=
  weightedRename_comp_equiv (Fin.castAddEmb n)
    ((polydiscEquiv A m n).toRingEquiv.toRingHom.comp (inl A _ _))
    ((polydiscEquiv A m n).continuous.comp (continuous_inl _ _ _))
    (fun a ↦ by
      rw [RingHom.comp_apply, ← RingHom.comp_apply (inl A _ _), ← algebraMap_eq_inl]
      exact polydiscEquiv_algebraMap A m n a)
    (fun i ↦ polydiscEquiv_inl_polydiscVar A m n i) f

/-- Under `polydiscEquiv`, an element of the right factor is renamed into the second block of
variables. -/
theorem coe_restrictedMvPowerSeriesCompletionEquiv_polydiscEquiv_inr
    (g : restrictedMvPowerSeriesCompletion n A) :
    toMvPowerSeries A (m + n) (polydiscEquiv A m n (inr A _ _ g)) =
      rename (Fin.natAddEmb m) (toMvPowerSeries A n g) :=
  weightedRename_comp_equiv (Fin.natAddEmb m)
    ((polydiscEquiv A m n).toRingEquiv.toRingHom.comp (inr A _ _))
    ((polydiscEquiv A m n).continuous.comp (continuous_inr _ _ _))
    (fun a ↦ by
      rw [RingHom.comp_apply, ← RingHom.comp_apply (inr A _ _), ← inl_comp_algebraMap,
        ← algebraMap_eq_inl]
      exact polydiscEquiv_algebraMap A m n a)
    (fun i ↦ polydiscEquiv_inr_polydiscVar A m n i) g

omit [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A] [T0Space A]
  [IsHuberRing A] in
private theorem coeff_rename_mul_rename (F G : MvPowerSeries (Fin 1) A) (i j : ℕ) :
    coeff (single 0 i + single 1 j : Fin (1 + 1) →₀ ℕ)
        (rename (Fin.castAddEmb 1) F * rename (Fin.natAddEmb 1) G) =
      coeff (single 0 i) F * coeff (single 0 j) G := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (single 0 i, single 1 j)]
  · have e0 : Fin.castAddEmb 1 (0 : Fin 1) = (0 : Fin (1 + 1)) := Fin.ext rfl
    have e1 : Fin.natAddEmb 1 (0 : Fin 1) = (1 : Fin (1 + 1)) := Fin.ext rfl
    have hF := coeff_single_rename (Fin.castAddEmb 1) F 0 i
    have hG := coeff_single_rename (Fin.natAddEmb 1) G 0 j
    rw [e0] at hF
    rw [e1] at hG
    rw [hF, hG]
  · rintro ⟨μ, ν⟩ hμν hne
    rw [Finset.mem_antidiagonal] at hμν
    by_cases h1 : μ 1 = 0
    · by_cases h0 : ν 0 = 0
      · have h0' : μ 0 = i := by simpa [h0] using congr($hμν 0)
        have h1' : ν 1 = j := by simpa [h1] using congr($hμν 1)
        clear hμν
        refine absurd (Prod.ext ?_ ?_) hne <;> ext k <;> fin_cases k <;> simp [h0, h1, h0', h1']
      · rw [coeff_rename_eq_zero_of_apply_ne_zero (Fin.natAddEmb 1) G (j := 0)
          (fun ⟨k, hk⟩ ↦ by fin_cases k; exact absurd hk (by decide)) h0, mul_zero]
    · rw [coeff_rename_eq_zero_of_apply_ne_zero (Fin.castAddEmb 1) F (j := 1)
        (fun ⟨k, hk⟩ ↦ by fin_cases k; exact absurd hk (by decide)) h1, zero_mul]
  · exact fun h ↦ (h (by simp)).elim

/-- **Coefficients of a pure tensor.** Under `polydiscEquiv`, the coefficient of `TⁱSʲ` in the
image of `f ⊗ g` is the coefficient of `Tⁱ` in `f` times the coefficient of `Sʲ` in `g`. -/
theorem coeff_polydiscEquiv_inl_mul_inr (f g : restrictedMvPowerSeriesCompletion 1 A)
    (i j : ℕ) :
    coeff (single 0 i + single 1 j)
        (toMvPowerSeries A (1 + 1) (polydiscEquiv A 1 1 (inl A _ _ f * inr A _ _ g))) =
      coeff (single 0 i) (toMvPowerSeries A 1 f) * coeff (single 0 j) (toMvPowerSeries A 1 g) := by
  rw [map_mul, map_mul, coe_restrictedMvPowerSeriesCompletionEquiv_polydiscEquiv_inl,
    coe_restrictedMvPowerSeriesCompletionEquiv_polydiscEquiv_inr, coeff_rename_mul_rename]

/-- The `N × N` matrix of the coefficients of `TⁱSʲ`, `i, j < N`, of an element of `A⟨T, S⟩`. -/
noncomputable def coeffMatrix (N : ℕ) (y : restrictedMvPowerSeriesCompletion (1 + 1) A) :
    Matrix (Fin N) (Fin N) A :=
  Matrix.of fun i j ↦ coeff (single 0 (i : ℕ) + single 1 (j : ℕ)) (toMvPowerSeries A (1 + 1) y)

section Diagonal

omit [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A] [T0Space A]
  [IsHuberRing A] in
variable (A) in
/-- The power series `Σₙ πⁿTⁿSⁿ` in two variables. -/
def diagonalMvPowerSeries (π : A) : MvPowerSeries (Fin (1 + 1)) A :=
  fun ν ↦ if ν 0 = ν 1 then π ^ ν 0 else 0

omit [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A] [T0Space A]
  [IsHuberRing A] in
theorem coeff_diagonalMvPowerSeries (π : A) (ν : Fin (1 + 1) →₀ ℕ) :
    coeff ν (diagonalMvPowerSeries A π) = if ν 0 = ν 1 then π ^ ν 0 else 0 :=
  (rfl)

omit [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A] [T0Space A]
  [IsHuberRing A] in
/-- For topologically nilpotent `π`, the series `Σₙ πⁿTⁿSⁿ` is restricted: its coefficients `πⁿ`
tend to zero. -/
theorem isWeightedRestricted_diagonalMvPowerSeries {π : A} (hπ : IsTopologicallyNilpotent π) :
    IsWeightedRestricted (fun _ : Fin (1 + 1) ↦ ({1} : Set A)) (diagonalMvPowerSeries A π) := by
  rw [isWeightedRestricted_iff]
  intro U
  simp only [weightMul_one_weight]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hπ (U.isOpen.mem_nhds U.zero_mem))
  refine Filter.eventually_cofinite.mpr (((Set.finite_Iio N).image
    fun n ↦ (single 0 n + single 1 n : Fin (1 + 1) →₀ ℕ)).subset fun ν hν ↦ ?_)
  simp only [Set.mem_ofPred_eq, coeff_diagonalMvPowerSeries] at hν
  by_cases h : ν 0 = ν 1
  · refine ⟨ν 0, Set.mem_Iio.mpr (lt_of_not_ge fun hle ↦ hν ?_), ?_⟩
    · simpa [h] using hN _ hle
    · ext k
      fin_cases k <;> simp [h]
  · exact (hν (by simp [h])).elim

/-- **The series `Σₙ πⁿTⁿSⁿ`** in `A⟨T, S⟩`, for a topologically nilpotent `π`. -/
noncomputable def diagonalSeries {π : A} (hπ : IsTopologicallyNilpotent π) :
    restrictedMvPowerSeriesCompletion (1 + 1) A :=
  (restrictedMvPowerSeriesCompletionEquiv (1 + 1) A).symm
    ⟨diagonalMvPowerSeries A π,
      mem_weightedRestrictedSubring.mpr (isWeightedRestricted_diagonalMvPowerSeries hπ)⟩

omit [IsHuberRing A] in
/-- The coefficient of `TⁱSʲ` in `Σₙ πⁿTⁿSⁿ` is `πⁱ` if `i = j` and `0` otherwise. -/
theorem coeff_diagonalSeries {π : A} (hπ : IsTopologicallyNilpotent π) (i j : ℕ) :
    coeff (single 0 i + single 1 j) (toMvPowerSeries A (1 + 1) (diagonalSeries hπ)) =
      if i = j then π ^ i else 0 := by
  rw [toMvPowerSeries_apply, diagonalSeries, RingEquiv.apply_symm_apply,
    coeff_diagonalMvPowerSeries]
  simp

end Diagonal

section Field

variable {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [NonarchimedeanRing K]
  [CompleteSpace K] [T0Space K] [IsHuberRing K]

/-- **Elements of the algebraic tensor product have coefficient matrices of bounded rank.** For an
element `x = Σₖ fₖ ⊗ gₖ` of `K⟨T⟩ ⊗_K K⟨S⟩`, the coefficient matrix of its image in `K⟨T, S⟩` is
`Σₖ (coefficients of fₖ) (coefficients of gₖ)ᵀ`, of rank at most the number of terms. -/
theorem exists_rank_coeffMatrix_le
    (x : restrictedMvPowerSeriesCompletion 1 K ⊗[K] restrictedMvPowerSeriesCompletion 1 K) :
    ∃ r : ℕ, ∀ N, (coeffMatrix N (polydiscEquiv K 1 1 (toCompletion K _ _ x))).rank ≤ r := by
  obtain ⟨r, f, g, rfl⟩ : ∃ (r : ℕ) (f g : Fin r → restrictedMvPowerSeriesCompletion 1 K),
      x = ∑ k, f k ⊗ₜ[K] g k := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => exact ⟨1, fun _ ↦ a, fun _ ↦ b, by simp⟩
    | add x y hx hy =>
      obtain ⟨r, f, g, rfl⟩ := hx
      obtain ⟨s, f', g', rfl⟩ := hy
      exact ⟨r + s, Fin.append f f', Fin.append g g', by simp [Fin.sum_univ_add]⟩
  refine ⟨r, fun N ↦ ?_⟩
  have h : coeffMatrix N (polydiscEquiv K 1 1 (toCompletion K _ _ (∑ k, f k ⊗ₜ[K] g k))) =
      Matrix.of (fun (a : Fin N) (k : Fin r) ↦
          coeff (single 0 (a : ℕ)) (toMvPowerSeries K 1 (f k))) *
        Matrix.of fun (k : Fin r) (c : Fin N) ↦
          coeff (single 0 (c : ℕ)) (toMvPowerSeries K 1 (g k)) := by
    ext a c
    simp only [coeffMatrix, Matrix.of_apply, Matrix.mul_apply, map_sum, toCompletion_tmul,
      coeff_polydiscEquiv_inl_mul_inr]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- **A diagonal coefficient matrix with nonzero diagonal rules out the algebraic tensor
product.** If the coefficients of `TⁱSʲ` in `y ∈ K⟨T, S⟩` vanish off the diagonal and are nonzero
on it, then `y` is not the image of an element of `K⟨T⟩ ⊗_K K⟨S⟩`. -/
theorem notMem_range_of_coeff_eq_ite (y : restrictedMvPowerSeriesCompletion (1 + 1) K)
    (d : ℕ → K) (hd : ∀ n, d n ≠ 0)
    (hy : ∀ i j, coeff (single 0 i + single 1 j) (toMvPowerSeries K (1 + 1) y) =
      if i = j then d i else 0) :
    y ∉ Set.range fun x ↦ polydiscEquiv K 1 1 (toCompletion K _ _ x) := by
  classical
  rintro ⟨x, rfl⟩
  obtain ⟨r, hr⟩ := exists_rank_coeffMatrix_le x
  have h := hr (r + 1)
  have hdiag : coeffMatrix (r + 1) (polydiscEquiv K 1 1 (toCompletion K _ _ x)) =
      Matrix.diagonal fun i : Fin (r + 1) ↦ d i := by
    ext a b
    simp [coeffMatrix, hy, Matrix.diagonal_apply, Fin.val_inj]
  rw [hdiag, Matrix.rank_diagonal] at h
  simp [hd] at h


/-- **`finite_tensor_infinite_rank`.** For a nonzero topologically nilpotent `π` in a complete
Hausdorff nonarchimedean Huber field `K`, the series `Σₙ πⁿTⁿSⁿ` of
`K⟨T⟩ ⊗̂_K K⟨S⟩ ≃ K⟨T, S⟩` is not the image of an element of the algebraic tensor product
`K⟨T⟩ ⊗_K K⟨S⟩`: its coefficient matrix is diagonal with nonzero entries `πⁿ`, of infinite rank,
while a finite sum of pure tensors has a coefficient matrix of finite rank. -/
theorem diagonalSeries_notMem_range {π : K} (hπ : IsTopologicallyNilpotent π) (hπ0 : π ≠ 0) :
    diagonalSeries hπ ∉ Set.range fun x ↦ polydiscEquiv K 1 1 (toCompletion K _ _ x) :=
  notMem_range_of_coeff_eq_ite _ (π ^ ·) (fun n ↦ pow_ne_zero n hπ0) (coeff_diagonalSeries hπ)

end Field

end TauCeti.Huber.CompletedTensor
