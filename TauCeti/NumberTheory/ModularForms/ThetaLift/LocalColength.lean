/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.ColengthDvd
public import TauCeti.Analysis.AbsoluteValue.IntegralCoordinates

/-!
# Colength after local normalization of a lift

A family of linear coordinates on a vector space, for example the evaluations of all allowed
lifts in integral coordinates, cuts out a submodule over the valuation ring. If the coordinates
of an unnormalized map satisfy a common gain bound on a submodule, scaling the map by a scalar
whose absolute value is bounded by the floored gain makes its image there integral. The same
colength witness works for all the coordinate tests at once, even for infinitely many tests.

The normalization is that of `New.Data.normalizedPoincare_mem_integralVectors` in
`grh/src/New/Reduction/ShortAndEnough.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

namespace Submodule.ColengthDvd

/-- Let `f` be a map whose coordinates on `S` have absolute value at most `p ^ (-g)`. After
scaling by a scalar with absolute value at most `p ^ ⌊g⌋`, the colength of the simultaneous
integral submodule in the scaled image of `M` divides `z`, provided `M ⊸_z S`.
The coordinate index can encode both the allowed twists and their integral coordinates. -/
theorem map_normalized_lifts {K V U : Type*} [Field K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid U] [Module K U] {w : AbsoluteValue K ℝ} {hw : IsNonarchimedean w}
    {M S : Submodule (w.valuationSubring hw) V} {z : w.valuationSubring hw}
    (h : M.ColengthDvd S z) {I : Sort*} (a : I → U →ₗ[K] K) (f : V →ₗ[K] U)
    {c : K} {p g : ℝ} (hp : 1 ≤ p) (hc : w c ≤ p ^ (⌊g⌋ : ℤ))
    (hS : ∀ v ∈ S, ∀ i, w (a i (f v)) ≤ p ^ (-g)) :
    (M.map ((c • f).restrictScalars (w.valuationSubring hw))).ColengthDvd
      (w.integralCoordinates hw a) z := by
  apply h.map _ le_sup_left
  rintro _ ⟨v, hv, rfl⟩
  refine (w.mem_integralCoordinates_iff hw a).2 fun i ↦ ?_
  simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, map_mul]
  calc
    w c * w (a i (f v)) ≤ p ^ (⌊g⌋ : ℤ) * p ^ (-g) :=
      mul_le_mul hc (hS v hv i) (w.nonneg _) (by positivity)
    _ ≤ 1 := by
      rw [← Real.rpow_intCast, ← Real.rpow_add (zero_lt_one.trans_le hp), ← Real.rpow_zero p]
      exact Real.rpow_le_rpow_of_exponent_le hp (sub_nonpos.mpr (Int.floor_le g))

end Submodule.ColengthDvd
