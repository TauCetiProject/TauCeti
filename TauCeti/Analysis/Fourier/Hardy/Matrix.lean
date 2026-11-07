/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.BrownHalmos
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Matrix

/-!
# Bounded Toeplitz matrices

For a sequence `c : ℤ → ℂ`, the matrix with entries `c (j - i)` represents a bounded
operator on native `ℓ²(ℕ, ℂ)` exactly when `c k = â(-k)` for an essentially bounded
circle symbol `a`. Equivalently, the leading square matrices have uniformly bounded
Euclidean operator norms. Every prescribed nonnegative bound works simultaneously
for the infinite operator, all finite matrices, and the symbol.

The reversed index is essential: the Hardy matrix of `T_a` has entries `â(i - j)`.
Reflecting the symbol gives Fourier coefficients `c k`, and the symbol `e₁` gives the
forward shift. The finite matrices below use genuine Euclidean operator norms.

## References

* A. Brown and P. R. Halmos, *Algebraic properties of Toeplitz operators*, J. Reine
  Angew. Math. 213 (1964), 89–102.
* A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, §2.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace lp

namespace TauCeti

/-- The leading `(n + 1) × (n + 1)` Toeplitz matrix in the convention `c (j - i)`. -/
def toeplitzMatrix (c : ℤ → ℂ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j ↦ c ((j : ℤ) - i)

@[simp]
theorem toeplitzMatrix_apply (c : ℤ → ℂ) (n : ℕ) (i j : Fin (n + 1)) :
    toeplitzMatrix c n i j = c ((j : ℤ) - i) :=
  (rfl)

/-- In the `c (j - i)` convention the coefficient sequence of `T_a` is `c k = â(-k)`. -/
theorem finiteSection_toeplitz (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (n : ℕ) :
    (toeplitz a).finiteSection hardyBasis n =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (toeplitzMatrix (fun k ↦ fourierCoeff a (-k)) n) := by
  rw [ContinuousLinearMap.finiteSection_eq_toEuclideanCLM]
  congr 1
  ext i j
  simp only [Matrix.of_apply, toeplitzMatrix_apply, inner_hardyBasis_toeplitz_hardyBasis]
  congr 1
  omega

/-- A prescribed Toeplitz matrix has an essentially bounded symbol with norm at most `C`
exactly when all its leading square matrices have Euclidean operator norm at most `C`.
No summability assumption on the coefficient sequence is needed. -/
theorem exists_symbol_iff_norm_toeplitzMatrix_le (c : ℤ → ℂ) {C : ℝ} (hC : 0 ≤ C) :
    (∃ a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)),
      ‖a‖ ≤ C ∧ ∀ k : ℤ, fourierCoeff a k = c (-k)) ↔
      ∀ n : ℕ, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (toeplitzMatrix c n)‖ ≤ C := by
  constructor
  · rintro ⟨a, ha, hc⟩ n
    have hm := finiteSection_toeplitz a n
    simp only [hc, neg_neg] at hm
    rw [← hm]
    exact ((toeplitz a).norm_finiteSection_le hardyBasis n).trans ((norm_toeplitz a).le.trans ha)
  · intro h
    obtain ⟨T, hT, hentry⟩ := (hardyBasis.exists_operator_iff_matrix_bound
      (fun i j ↦ c ((j : ℤ) - i)) hC).mpr h
    have hdiag (i j : ℕ) : ⟪hardyBasis (i + 1), T (hardyBasis (j + 1))⟫_ℂ =
        ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ := by
      simp only [hentry]
      congr 1
      omega
    obtain ⟨a, ha⟩ := (exists_toeplitz_eq_iff_inner_hardyBasis_succ T).mpr hdiag
    refine ⟨a, ?_, fun k ↦ ?_⟩
    · simpa only [← norm_toeplitz a, ha] using hT
    · have hij : (k.toNat : ℤ) - (-k).toNat = k := by omega
      have hji : ((-k).toNat : ℤ) - k.toNat = -k := by omega
      have hk := hentry k.toNat (-k).toNat
      simpa only [← ha, inner_hardyBasis_toeplitz_hardyBasis, hij, hji] using hk

/-- The matrix `c (j - i)` extends to a bounded operator on `ℓ²(ℕ, ℂ)` with norm at most
`C` exactly when it is the Fourier matrix of an `L∞` symbol with norm at most `C`.
The formula on unit vectors also specifies the action on every finitely supported vector. -/
theorem exists_operator_iff_exists_toeplitz_symbol (c : ℤ → ℂ) {C : ℝ} (hC : 0 ≤ C) :
    (∃ T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ), ‖T‖ ≤ C ∧
      ∀ i j : ℕ, T (lp.single 2 j 1) i = c ((j : ℤ) - i)) ↔
    ∃ a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)),
      ‖a‖ ≤ C ∧ ∀ k : ℤ, fourierCoeff a k = c (-k) := by
  rw [exists_symbol_iff_norm_toeplitzMatrix_le c hC]
  let b : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ) := .ofRepr (.refl ℂ _)
  have hb (i : ℕ) : b i = lp.single 2 i (1 : ℂ) := by
    apply b.repr.injective
    rw [b.repr_self]
    simp [b]
  have hi (T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) (i j : ℕ) :
      ⟪b i, T (b j)⟫_ℂ = T (lp.single 2 j 1) i := by
    simp [hb, lp.inner_single_left]
  simpa only [hi, toeplitzMatrix] using
    b.exists_operator_iff_matrix_bound (fun i j ↦ c ((j : ℤ) - i)) hC

end TauCeti
