module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure

/-!
# Coordinate API for normalized Chebyshev modes

This file records finite-coordinate consequences of the orthonormality of the normalized
Chebyshev `T` modes in `L²(Polynomial.Chebyshev.measureT)`.  The eventual Chebyshev
Hilbert-basis target in the `OrthogonalL2Bases` roadmap needs to identify coordinates of
finite Chebyshev expansions without unfolding the `Lp` representatives of the modes.

The main object here is `chebyshevModeLinearCombination`, the finitely supported linear
combination of the normalized Chebyshev modes, together with the coefficient-picking inner
product formulas supplied by Mathlib's generic `Orthonormal` API.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Single normalized modes -/

/-- The normalized Chebyshev `T` mode has norm one in `L²(measureT)`. -/
@[simp]
lemma norm_normalizedChebyshevTLp (n : ℕ) :
    ‖normalizedChebyshevTLp 𝕜 n‖ = 1 :=
  orthonormal_normalizedChebyshevTLp.norm_eq_one n

/-- The normalized Chebyshev `T` mode has `ℝ≥0`-norm one in `L²(measureT)`. -/
@[simp]
lemma nnnorm_normalizedChebyshevTLp (n : ℕ) :
    ‖normalizedChebyshevTLp 𝕜 n‖₊ = 1 :=
  orthonormal_normalizedChebyshevTLp.nnnorm_eq_one n

/-- The normalized Chebyshev `T` mode has extended nonnegative norm one in `L²(measureT)`. -/
@[simp]
lemma enorm_normalizedChebyshevTLp (n : ℕ) :
    ‖normalizedChebyshevTLp 𝕜 n‖ₑ = 1 :=
  orthonormal_normalizedChebyshevTLp.enorm_eq_one n

/-- The normalized Chebyshev `T` mode is nonzero in `L²(measureT)`. -/
lemma normalizedChebyshevTLp_ne_zero (n : ℕ) :
    normalizedChebyshevTLp 𝕜 n ≠ 0 :=
  orthonormal_normalizedChebyshevTLp.ne_zero n

/-- The self-inner product of a normalized Chebyshev mode is one. -/
@[simp]
lemma inner_normalizedChebyshevTLp_self (n : ℕ) :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 n) (normalizedChebyshevTLp 𝕜 n) = 1 := by
  simp

/-- Distinct normalized Chebyshev modes are orthogonal. -/
lemma inner_normalizedChebyshevTLp_eq_zero {m n : ℕ} (hmn : m ≠ n) :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 m) (normalizedChebyshevTLp 𝕜 n) = 0 := by
  simp [hmn]

/-! ## Finitely supported Chebyshev expansions -/

/-- A finitely supported linear combination of normalized Chebyshev `T` modes in
`L²(measureT)`. -/
noncomputable def chebyshevModeLinearCombination (a : ℕ →₀ 𝕜) :
    Lp 𝕜 2 Polynomial.Chebyshev.measureT :=
  Finsupp.linearCombination 𝕜 (normalizedChebyshevTLp 𝕜) a

/-- The defining finite sum for `chebyshevModeLinearCombination`. -/
lemma chebyshevModeLinearCombination_eq_sum (a : ℕ →₀ 𝕜) :
    chebyshevModeLinearCombination a =
      a.sum fun n c => c • normalizedChebyshevTLp 𝕜 n := by
  rw [chebyshevModeLinearCombination, Finsupp.linearCombination_apply]

/-- The zero coefficient vector gives the zero Chebyshev expansion. -/
@[simp]
lemma chebyshevModeLinearCombination_zero :
    chebyshevModeLinearCombination (𝕜 := 𝕜) 0 = 0 := by
  simp [chebyshevModeLinearCombination]

/-- Chebyshev expansions add coefficientwise. -/
@[simp]
lemma chebyshevModeLinearCombination_add (a b : ℕ →₀ 𝕜) :
    chebyshevModeLinearCombination (a + b) =
      chebyshevModeLinearCombination a + chebyshevModeLinearCombination b := by
  simp [chebyshevModeLinearCombination]

/-- Chebyshev expansions scale coefficientwise. -/
@[simp]
lemma chebyshevModeLinearCombination_smul (c : 𝕜) (a : ℕ →₀ 𝕜) :
    chebyshevModeLinearCombination (c • a) = c • chebyshevModeLinearCombination a := by
  simp [chebyshevModeLinearCombination]

/-- A single coefficient gives the corresponding scalar multiple of one normalized mode. -/
@[simp]
lemma chebyshevModeLinearCombination_single (n : ℕ) (c : 𝕜) :
    chebyshevModeLinearCombination (Finsupp.single n c) =
      c • normalizedChebyshevTLp 𝕜 n := by
  simp [chebyshevModeLinearCombination]

/-- The coefficient of `n` is recovered by taking the inner product with the `n`th
normalized Chebyshev mode on the left. -/
@[simp]
lemma inner_normalizedChebyshevTLp_chebyshevModeLinearCombination
    (n : ℕ) (a : ℕ →₀ 𝕜) :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 n) (chebyshevModeLinearCombination a) = a n := by
  simpa [chebyshevModeLinearCombination] using
    (orthonormal_normalizedChebyshevTLp (𝕜 := 𝕜)).inner_right_finsupp a n

/-- Taking the inner product of a finite Chebyshev expansion with a normalized mode on the
right gives the conjugate coefficient. -/
@[simp]
lemma inner_chebyshevModeLinearCombination_normalizedChebyshevTLp
    (a : ℕ →₀ 𝕜) (n : ℕ) :
    inner 𝕜 (chebyshevModeLinearCombination a) (normalizedChebyshevTLp 𝕜 n) =
      star (a n) := by
  simpa [chebyshevModeLinearCombination] using
    (orthonormal_normalizedChebyshevTLp (𝕜 := 𝕜)).inner_left_finsupp a n

/-- Inner product of two finite Chebyshev expansions, summed over the first support. -/
lemma inner_chebyshevModeLinearCombination_eq_sum_left (a b : ℕ →₀ 𝕜) :
    inner 𝕜 (chebyshevModeLinearCombination a) (chebyshevModeLinearCombination b) =
      a.sum fun n c => star c * b n := by
  simpa [chebyshevModeLinearCombination] using
    (orthonormal_normalizedChebyshevTLp (𝕜 := 𝕜)).inner_finsupp_eq_sum_left a b

/-- Inner product of two finite Chebyshev expansions, summed over the second support. -/
lemma inner_chebyshevModeLinearCombination_eq_sum_right (a b : ℕ →₀ 𝕜) :
    inner 𝕜 (chebyshevModeLinearCombination a) (chebyshevModeLinearCombination b) =
      b.sum fun n c => star (a n) * c := by
  simpa [chebyshevModeLinearCombination] using
    (orthonormal_normalizedChebyshevTLp (𝕜 := 𝕜)).inner_finsupp_eq_sum_right a b

/-- A finite Chebyshev expansion is orthogonal to a mode outside its support. -/
lemma inner_chebyshevModeLinearCombination_normalizedChebyshevTLp_eq_zero
    {a : ℕ →₀ 𝕜} {n : ℕ} (hn : n ∉ a.support) :
    inner 𝕜 (chebyshevModeLinearCombination a) (normalizedChebyshevTLp 𝕜 n) = 0 := by
  rw [inner_chebyshevModeLinearCombination_normalizedChebyshevTLp]
  simp [Finsupp.notMem_support_iff.mp hn]

/-- If every displayed coefficient is zero, then the finite Chebyshev expansion is zero. -/
lemma chebyshevModeLinearCombination_eq_zero_of_forall_eq_zero
    {a : ℕ →₀ 𝕜} (ha : ∀ n, a n = 0) :
    chebyshevModeLinearCombination a = 0 := by
  have hzero : a = 0 := by
    ext n
    exact ha n
  simp [hzero]

/-- A finite Chebyshev expansion is zero exactly when all its coefficients are zero. -/
lemma chebyshevModeLinearCombination_eq_zero_iff (a : ℕ →₀ 𝕜) :
    chebyshevModeLinearCombination a = 0 ↔ ∀ n, a n = 0 := by
  constructor
  · intro h n
    have hinner :
        inner 𝕜 (normalizedChebyshevTLp 𝕜 n) (chebyshevModeLinearCombination a) = 0 := by
      simp [h]
    simpa using hinner
  · exact chebyshevModeLinearCombination_eq_zero_of_forall_eq_zero

/-- The finite Chebyshev expansion map is injective on coefficient vectors. -/
lemma chebyshevModeLinearCombination_injective :
    Function.Injective (chebyshevModeLinearCombination (𝕜 := 𝕜)) := by
  intro a b h
  ext n
  have hinner :
      inner 𝕜 (normalizedChebyshevTLp 𝕜 n) (chebyshevModeLinearCombination a) =
        inner 𝕜 (normalizedChebyshevTLp 𝕜 n) (chebyshevModeLinearCombination b) := by
    rw [h]
  simpa using hinner

end TauCeti
