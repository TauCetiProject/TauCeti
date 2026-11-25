/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Rellich

/-!
# Rellich compactness on the closed disc

On the closed unit disc `Complex.UnitClosedDisc` with the trivial bundle of a finite-dimensional
fibre `F`, for every finite bundle atlas, every order `k` and `1 ≤ p ≤ ∞`, the inclusion
`W^{k+1,p} → W^{k,p}` of the bordered Sobolev spaces is a compact operator
(`TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrderL_unitClosedDisc`); at `k = 0` this
is the compactness of `W^{1,p} → Lᵖ`. For a nonzero fibre the identity of `W^{k,p}` is not compact
(`TauCeti.BorderedSobolevSection.not_isCompactOperator_id_unitClosedDisc` in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.InfiniteDimensional.Disc`), so the
loss of one derivative is what makes the inclusion compact.

## Main results

* `TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrderL_unitClosedDisc`: Rellich's theorem
  on the closed disc.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ENNReal Complex.UnitDisc

namespace TauCeti

namespace BorderedSobolevSection

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Rellich's theorem on the closed disc.** For the trivial bundle over the closed unit disc
with a finite-dimensional fibre, every finite bundle atlas, every order `k` and `1 ≤ p ≤ ∞`, the
inclusion `W^{k+1,p} → W^{k,p}` is a compact operator. At `k = 0` it is `W^{1,p} → Lᵖ`. -/
theorem isCompactOperator_lowerOrderL_unitClosedDisc
    (A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F)) :
    IsCompactOperator (A.halfSectionChartData.lowerOrderL volume p k) :=
  isCompactOperator_lowerOrderL (n := k + 1) le_rfl A

end BorderedSobolevSection

end TauCeti
