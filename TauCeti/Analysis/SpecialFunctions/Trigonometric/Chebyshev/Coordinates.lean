module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure

/-!
# Coordinate API for normalized Chebyshev modes

This file records finite-coordinate consequences of the orthonormality of the normalized
Chebyshev `T` modes in `L²(Polynomial.Chebyshev.measureT)`.  The eventual Chebyshev
Hilbert-basis target in the `OrthogonalL2Bases` roadmap needs to identify coordinates of
finite Chebyshev expansions without unfolding the `Lp` representatives of the modes.

The main object here is `chebyshevModeLinearCombination`, the bundled finitely supported
linear combination map for the normalized Chebyshev modes.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

variable (𝕜 : Type*) [RCLike 𝕜]

/-! ## Finitely supported Chebyshev expansions -/

/-- A finitely supported linear combination of normalized Chebyshev `T` modes in
`L²(measureT)`. -/
noncomputable def chebyshevModeLinearCombination :
    (ℕ →₀ 𝕜) →ₗ[𝕜] Lp 𝕜 2 Polynomial.Chebyshev.measureT :=
  Finsupp.linearCombination 𝕜 (normalizedChebyshevTLp 𝕜)

/-- The defining finite sum for `chebyshevModeLinearCombination`. -/
lemma chebyshevModeLinearCombination_eq_sum (a : ℕ →₀ 𝕜) :
    chebyshevModeLinearCombination 𝕜 a =
      a.sum fun n c => c • normalizedChebyshevTLp 𝕜 n := by
  rw [chebyshevModeLinearCombination, Finsupp.linearCombination_apply]

/-- A single coefficient gives the corresponding scalar multiple of one normalized mode. -/
@[simp]
lemma chebyshevModeLinearCombination_single (n : ℕ) (c : 𝕜) :
    chebyshevModeLinearCombination 𝕜 (Finsupp.single n c) =
      c • normalizedChebyshevTLp 𝕜 n := by
  simp [chebyshevModeLinearCombination]

end TauCeti
