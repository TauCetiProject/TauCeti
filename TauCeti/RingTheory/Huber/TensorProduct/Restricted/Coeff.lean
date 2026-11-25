/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Restricted.Polydisc
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Coefficients of completed tensor products of closed polydiscs

Over a complete Hausdorff nonarchimedean ring `A`, every element of `A⟨T₁, …, Tₖ⟩` has a power
series (`TauCeti.Huber.toMvPowerSeries`), so it has coefficients. Under the isomorphism
`TauCeti.Huber.CompletedTensor.polydiscEquiv` of `A⟨T₁, …, Tₘ⟩ ⊗̂_A A⟨S₁, …, Sₙ⟩` with
`A⟨T₁, …, Tₘ, S₁, …, Sₙ⟩`, the two factors are renamed into the two blocks of variables. The
coefficient of `T^μ S^ν` in the image of `f ⊗ g` is therefore the product of the coefficient of
`T^μ` in `f` and that of `S^ν` in `g`.

Over a field it follows that the coefficient matrices `(c_{ij})_{i,j<N}` of the image of an
element of the algebraic tensor product `A⟨T⟩ ⊗_A A⟨S⟩` have rank bounded uniformly in `N`. An
element whose coefficient matrix is diagonal with nonzero diagonal, such as `Σₙ πⁿTⁿSⁿ` for a
nonzero topologically nilpotent `π`, is thus not in the image: the completed tensor product of two
one-variable Tate algebras is strictly larger than the algebraic one, so the finiteness hypothesis
in the comparison of completed and algebraic tensor products for finite algebras cannot be
dropped.

## Main definitions

* `TauCeti.Huber.CompletedTensor.coeffMatrix N y`: the `N × N` matrix of coefficients of `TⁱSʲ` in
  `y ∈ A⟨T, S⟩`.
* `TauCeti.Huber.CompletedTensor.diagonalSeries π`: the element `Σₙ πⁿTⁿSⁿ` of `A⟨T, S⟩`.

## Main results

* `TauCeti.Huber.CompletedTensor.toMvPowerSeries_polydiscEquiv_inl`, `…_inr`: the two factors
  are renamed into the two blocks of variables.
* `TauCeti.Huber.CompletedTensor.coeff_polydiscEquiv_inl_mul_inr`: the coefficient of `T^μ S^ν` in
  the image of `f ⊗ g` is the product of coefficients; for one variable on each side this is
  `TauCeti.Huber.CompletedTensor.coeff_single_add_single_polydiscEquiv_inl_mul_inr`.
* `TauCeti.Huber.CompletedTensor.toMvPowerSeries_diagonalSeries`: the power series of
  `diagonalSeries π` is `Σₙ πⁿTⁿSⁿ`.
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

section Blocks

variable (m n : ℕ)

/-- Under `polydiscEquiv`, an element of the left factor is renamed into the first block of
variables. -/
@[simp]
theorem toMvPowerSeries_polydiscEquiv_inl (f : restrictedMvPowerSeriesCompletion m A) :
    toMvPowerSeries (m + n) A (polydiscEquiv A m n (inl A _ _ f)) =
      rename (Fin.castAddEmb n) (toMvPowerSeries m A f) :=
  toMvPowerSeries_apply_eq_rename (Fin.castAddEmb n)
    (φ := (polydiscEquiv A m n).toRingEquiv.toRingHom.comp (inl A _ _))
    ((polydiscEquiv A m n).continuous.comp (continuous_inl _ _ _))
    (fun a ↦ by
      rw [RingHom.comp_apply, inl_algebraMap]
      exact polydiscEquiv_algebraMap A m n a)
    (fun i ↦ polydiscEquiv_inl_polydiscVar A m n i) f

/-- Under `polydiscEquiv`, an element of the right factor is renamed into the second block of
variables. -/
@[simp]
theorem toMvPowerSeries_polydiscEquiv_inr (g : restrictedMvPowerSeriesCompletion n A) :
    toMvPowerSeries (m + n) A (polydiscEquiv A m n (inr A _ _ g)) =
      rename (Fin.natAddEmb m) (toMvPowerSeries n A g) :=
  toMvPowerSeries_apply_eq_rename (Fin.natAddEmb m)
    (φ := (polydiscEquiv A m n).toRingEquiv.toRingHom.comp (inr A _ _))
    ((polydiscEquiv A m n).continuous.comp (continuous_inr _ _ _))
    (fun a ↦ by
      rw [RingHom.comp_apply, inr_algebraMap]
      exact polydiscEquiv_algebraMap A m n a)
    (fun i ↦ polydiscEquiv_inr_polydiscVar A m n i) g

end Blocks

/-- **Coefficients of a pure tensor.** Under `polydiscEquiv`, the coefficient of `T^μ S^ν` in the
image of `f ⊗ g` is the coefficient of `T^μ` in `f` times the coefficient of `S^ν` in `g`. -/
theorem coeff_polydiscEquiv_inl_mul_inr {m n : ℕ} (f : restrictedMvPowerSeriesCompletion m A)
    (g : restrictedMvPowerSeriesCompletion n A) (μ : Fin m →₀ ℕ) (ν : Fin n →₀ ℕ) :
    coeff (μ.embDomain (Fin.castAddEmb n) + ν.embDomain (Fin.natAddEmb m))
        (toMvPowerSeries (m + n) A (polydiscEquiv A m n (inl A _ _ f * inr A _ _ g))) =
      coeff μ (toMvPowerSeries m A f) * coeff ν (toMvPowerSeries n A g) := by
  rw [map_mul, map_mul, toMvPowerSeries_polydiscEquiv_inl, toMvPowerSeries_polydiscEquiv_inr,
    coeff_embDomain_add_embDomain_rename_mul_rename _ _ fun i j h ↦ by
      have := congr(Fin.val $h)
      simp at this
      omega]

/-- For one variable on each side, the coefficient of `TⁱSʲ` in the image of `f ⊗ g` under
`polydiscEquiv` is the coefficient of `Tⁱ` in `f` times the coefficient of `Sʲ` in `g`. -/
theorem coeff_single_add_single_polydiscEquiv_inl_mul_inr
    (f g : restrictedMvPowerSeriesCompletion 1 A) (i j : ℕ) :
    coeff (single 0 i + single 1 j)
        (toMvPowerSeries (1 + 1) A (polydiscEquiv A 1 1 (inl A _ _ f * inr A _ _ g))) =
      coeff (single 0 i) (toMvPowerSeries 1 A f) * coeff (single 0 j) (toMvPowerSeries 1 A g) := by
  have h₀ : (single 0 i : Fin 1 →₀ ℕ).embDomain (Fin.castAddEmb 1) = single 0 i := by
    rw [embDomain_single, show Fin.castAddEmb 1 (0 : Fin 1) = 0 from Fin.ext rfl]
  have h₁ : (single 0 j : Fin 1 →₀ ℕ).embDomain (Fin.natAddEmb 1) = single 1 j := by
    rw [embDomain_single, show Fin.natAddEmb 1 (0 : Fin 1) = 1 from Fin.ext rfl]
  rw [← h₀, ← h₁]
  exact coeff_polydiscEquiv_inl_mul_inr f g _ _

/-- The `N × N` matrix of the coefficients of `TⁱSʲ`, `i, j < N`, of an element of `A⟨T, S⟩`. -/
noncomputable def coeffMatrix (N : ℕ) (y : restrictedMvPowerSeriesCompletion (1 + 1) A) :
    Matrix (Fin N) (Fin N) A :=
  Matrix.of fun i j ↦ coeff (single 0 (i : ℕ) + single 1 (j : ℕ)) (toMvPowerSeries (1 + 1) A y)

omit [IsHuberRing A] in
/-- The `(i, j)` entry of `coeffMatrix N y` is the coefficient of `TⁱSʲ` in `y`. -/
@[simp]
theorem coeffMatrix_apply (N : ℕ) (y : restrictedMvPowerSeriesCompletion (1 + 1) A)
    (i j : Fin N) :
    coeffMatrix N y i j =
      coeff (single 0 (i : ℕ) + single 1 (j : ℕ)) (toMvPowerSeries (1 + 1) A y) :=
  (rfl)

section Diagonal

omit [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A] [T0Space A]
  [IsHuberRing A] in
variable (A) in
/-- The power series `Σₙ πⁿTⁿSⁿ` in two variables. -/
def diagonalMvPowerSeries (π : A) : MvPowerSeries (Fin (1 + 1)) A :=
  fun ν ↦ if ν 0 = ν 1 then π ^ ν 0 else 0

omit [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A] [T0Space A]
  [IsHuberRing A] in
@[simp]
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
/-- The power series of `diagonalSeries hπ` is `Σₙ πⁿTⁿSⁿ`. -/
@[simp]
theorem toMvPowerSeries_diagonalSeries {π : A} (hπ : IsTopologicallyNilpotent π) :
    toMvPowerSeries (1 + 1) A (diagonalSeries hπ) = diagonalMvPowerSeries A π := by
  rw [toMvPowerSeries_apply, diagonalSeries, RingEquiv.apply_symm_apply]

omit [IsHuberRing A] in
/-- The coefficient of `TⁱSʲ` in `Σₙ πⁿTⁿSⁿ` is `πⁱ` if `i = j` and `0` otherwise. -/
theorem coeff_diagonalSeries {π : A} (hπ : IsTopologicallyNilpotent π) (i j : ℕ) :
    coeff (single 0 i + single 1 j) (toMvPowerSeries (1 + 1) A (diagonalSeries hπ)) =
      if i = j then π ^ i else 0 := by
  simp

end Diagonal

section Field

variable {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [NonarchimedeanRing K]
  [CompleteSpace K] [T0Space K] [IsHuberRing K]

/-- **Elements of the algebraic tensor product have coefficient matrices of bounded rank.** For an
element `x` of `K⟨T⟩ ⊗_K K⟨S⟩`, the `N × N` coefficient matrices of its image in `K⟨T, S⟩` have
rank bounded independently of `N`: writing `x = Σₖ fₖ ⊗ gₖ`, each is
`Σₖ (coefficients of fₖ) (coefficients of gₖ)ᵀ`. -/
theorem exists_rank_coeffMatrix_le
    (x : restrictedMvPowerSeriesCompletion 1 K ⊗[K] restrictedMvPowerSeriesCompletion 1 K) :
    ∃ r : ℕ, ∀ N, (coeffMatrix N (polydiscEquiv K 1 1 (toCompletion K _ _ x))).rank ≤ r := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  refine ⟨S.card, fun N ↦ ?_⟩
  have h : coeffMatrix N (polydiscEquiv K 1 1 (toCompletion K _ _ x)) =
      Matrix.of (fun (a : Fin N) (k : S) ↦
          coeff (single 0 (a : ℕ)) (toMvPowerSeries 1 K k.val.1)) *
        Matrix.of fun (k : S) (c : Fin N) ↦
          coeff (single 0 (c : ℕ)) (toMvPowerSeries 1 K k.val.2) := by
    ext a c
    rw [hS]
    simp only [coeffMatrix_apply, Matrix.of_apply, Matrix.mul_apply, map_sum, toCompletion_tmul,
      coeff_single_add_single_polydiscEquiv_inl_mul_inr]
    rw [← Finset.sum_coe_sort S]
  rw [h, ← Fintype.card_coe S]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- **A diagonal coefficient matrix with nonzero diagonal rules out the algebraic tensor
product.** If the coefficients of `TⁱSʲ` in `y ∈ K⟨T, S⟩` vanish off the diagonal and are nonzero
on it, then `y` is not the image of an element of `K⟨T⟩ ⊗_K K⟨S⟩`. -/
theorem notMem_range_of_coeff_eq_ite (y : restrictedMvPowerSeriesCompletion (1 + 1) K)
    (d : ℕ → K) (hd : ∀ n, d n ≠ 0)
    (hy : ∀ i j, coeff (single 0 i + single 1 j) (toMvPowerSeries (1 + 1) K y) =
      if i = j then d i else 0) :
    y ∉ Set.range fun x ↦ polydiscEquiv K 1 1 (toCompletion K _ _ x) := by
  classical
  rintro ⟨x, rfl⟩
  obtain ⟨r, hr⟩ := exists_rank_coeffMatrix_le x
  have h := hr (r + 1)
  have hdiag : coeffMatrix (r + 1) (polydiscEquiv K 1 1 (toCompletion K _ _ x)) =
      Matrix.diagonal fun i : Fin (r + 1) ↦ d i := by
    ext a b
    simp [hy, Matrix.diagonal_apply, Fin.val_inj]
  rw [hdiag, Matrix.rank_diagonal] at h
  simp [hd] at h

/-- **`Σₙ πⁿTⁿSⁿ` is not in the image of the algebraic tensor product.** For a nonzero
topologically nilpotent `π` in a complete Hausdorff nonarchimedean Huber field `K`, the series
`Σₙ πⁿTⁿSⁿ` of `K⟨T⟩ ⊗̂_K K⟨S⟩ ≃ K⟨T, S⟩` is not the image of an element of the algebraic
tensor product `K⟨T⟩ ⊗_K K⟨S⟩`: its coefficient matrix is diagonal with nonzero entries `πⁿ`, of
infinite rank, while a finite sum of pure tensors has a coefficient matrix of finite rank. -/
theorem diagonalSeries_notMem_range {π : K} (hπ : IsTopologicallyNilpotent π) (hπ0 : π ≠ 0) :
    diagonalSeries hπ ∉ Set.range fun x ↦ polydiscEquiv K 1 1 (toCompletion K _ _ x) :=
  notMem_range_of_coeff_eq_ite _ (π ^ ·) (fun n ↦ pow_ne_zero n hπ0) (coeff_diagonalSeries hπ)

end Field

end TauCeti.Huber.CompletedTensor
