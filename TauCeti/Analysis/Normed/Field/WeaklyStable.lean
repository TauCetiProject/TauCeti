/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Trace
public import Mathlib.FieldTheory.Perfect

/-!
# Weakly stable fields

An ultrametric normed field is weakly stable if every linear functional on each finite
extension is bounded for the spectral norm. This is the bounded-functional formulation of
weak cartesianness. Perfect fields and complete nontrivially normed fields are weakly stable.
The perfect-field result applies to incomplete fields and does not assert that their spectral
norm is multiplicative. The complete-field result includes inseparable finite extensions.

The definitions and proofs adapt William Coram's `IsWeaklyStable`,
`isWeaklyStable_of_perfectField` and `isWeaklyStable_of_completeSpace` in
`PhD/TauCeti/Code/RigidAnalyticGeometry/WeaklyStable.lean` at commit
`eefb3d91f34b27d0bc7822140fa85fecae029884` of <https://github.com/WilliamCoram/PhD>.
The mathematical references are Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*,
§§2.3.1–2.3.2, §3.5.1, Proposition 4 and §3.5.2, Definition 1.
-/

public section

namespace TauCeti

universe u

/-- Every functional on a finite extension is bounded with respect to the spectral norm.
For an ultrametric normed field this is the bounded-functional formulation of **weak stability**. -/
def IsWeaklyStable (K : Type u) [NormedField K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    (φ : Module.Dual K L), ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y

/-- The bounded-functional criterion for weak stability. -/
theorem isWeaklyStable_iff (K : Type u) [NormedField K] :
    IsWeaklyStable K ↔ ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      (φ : Module.Dual K L), ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := Iff.rfl

/-- Every perfect ultrametric normed field is weakly stable, even when incomplete. -/
theorem isWeaklyStable_of_perfectField (K : Type u) [NormedField K] [IsUltrametricDist K]
    [PerfectField K] : IsWeaklyStable K := by
  intro L _ _ _ φ
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact φ.exists_bound_spectralNorm_of_isSeparable

/-- Every complete nontrivially normed ultrametric field is weakly stable, including in
positive characteristic. No separability hypothesis is imposed on finite extensions. -/
theorem isWeaklyStable_of_completeSpace (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : IsWeaklyStable K := by
  intro L _ _ _ φ
  let := spectralNorm.normedField K L
  let := spectralNorm.normedAlgebra K L
  refine ⟨‖LinearMap.toContinuousLinearMap φ‖, fun y ↦ ?_⟩
  rw [← NormedAlgebra.norm_eq_spectralNorm K y]
  exact (LinearMap.toContinuousLinearMap φ).le_opNorm y

end TauCeti
