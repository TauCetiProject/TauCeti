/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic
public import TauCeti.NumberTheory.Padics.Measure.Clopen.Basic

/-!
# Coefficient extension and clopen restriction

Extending the coefficients of a measure along a uniformly bounded homomorphism from a topological
commutative ring to a complete ultrametric normed commutative ring commutes with restriction to
any clopen subset of a profinite space. Both orders give the same integrals on that subset. With
`AbstractMeasure.extendCoefficients_map`, this also compares the ambient extensions by zero.

The coefficient homomorphism need not be continuous: finite projections test only locally constant
functions, and coefficient extension already agrees on these tests. No norm or topology instance
on measures is introduced.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Proposition 3.16,
  Remark 3.28 and §3.5.3, Remark 3.31.
-/

public noncomputable section

open ContinuousMap TopologicalSpace

namespace AbstractMeasure

variable {X O K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K] {B : ℝ}
  (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B)

/-- Extension along a uniformly bounded homomorphism from a topological commutative ring to a
complete ultrametric normed commutative ring commutes with restriction to a clopen subset of a
profinite space.
The homomorphism need not be continuous. -/
@[simp]
theorem extendCoefficients_restrictClopen (s : Clopens X) (μ : D(X, O)) :
    extendCoefficients j hj (restrictClopen s μ) =
      restrictClopen s (extendCoefficients j hj μ) := by
  classical
  apply finiteProjection_ext
  intro q
  ext a
  rw [finiteProjection_extendCoefficients, Finsupp.mapRange_apply,
    finiteProjection_apply, finiteProjection_apply, restrictClopen_apply, restrictClopen_apply]
  -- The extended fibre indicator is an integer-valued locally constant function. Transporting
  -- this test to each coefficient ring avoids any continuity assumption on `j`.
  let f : LocallyConstant X ℤ :=
    ⟨zeroExtendClopen ℤ s (q.fiberIndicator a),
      (IsLocallyConstant.iff_continuous _).mpr (map_continuous _)⟩
  have hO : zeroExtendClopen O s (q.fiberIndicator a) =
      (f.map (Int.castRingHom O) : C(X, O)) := by
    ext x
    by_cases hx : x ∈ s
    · simp [f, hx, fiberIndicator_apply]
    · simp [f, hx]
  have hK : zeroExtendClopen K s (q.fiberIndicator a) =
      ((f.map (Int.castRingHom O)).map j : C(X, K)) := by
    ext x
    by_cases hx : x ∈ s
    · simp [f, hx, fiberIndicator_apply]
    · simp [f, hx]
  rw [hO, hK, extendCoefficients_apply_locallyConstant]

section Examples

-- Empty clopens require neither a chosen point nor a nonempty subtype.
example (μ : D(X, O)) :
    extendCoefficients j hj (restrictClopen (⊥ : Clopens X) μ) = 0 := by
  rw [extendCoefficients_restrictClopen]
  ext f
  have hf : f = 0 := ContinuousMap.ext fun x ↦ (Set.notMem_empty (x : X) x.property).elim
  simp [hf]

end Examples

end AbstractMeasure
