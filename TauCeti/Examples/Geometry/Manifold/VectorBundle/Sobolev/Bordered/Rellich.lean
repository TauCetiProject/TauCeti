/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.InfiniteDimensional.Disc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Rellich

/-!
# Rellich compactness on the closed disc

The closed-disc check of Rellich's theorem over a base with boundary. On the closed unit disc
`Complex.UnitClosedDisc` with the trivial bundle of a finite-dimensional fibre `F`, for every
finite bundle atlas, every order `k` and `1 ≤ p ≤ ∞`, the inclusion `W^{k+1,p} → W^{k,p}` of the
bordered Sobolev spaces is compact; at `k = 0` this is the compactness of `W^{1,p} → Lᵖ`. This is
`TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrderL`, whose hypotheses the closed disc
and the trivial bundle satisfy through their existing instances. For a nonzero fibre the identity of
`W^{k,p}` is not compact (`TauCeti.BorderedSobolevSection.not_isCompactOperator_id_unitClosedDisc`),
so the loss of one derivative is what makes the inclusion compact.
-/

public noncomputable section

open Bundle MeasureTheory
open scoped Manifold ENNReal Complex.UnitDisc

namespace TauCeti.Examples.BorderedRellichDisc

open BorderedSobolevSection

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

-- `W^{k+1,p} → W^{k,p}` is compact on the closed disc, for every atlas.
example (A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F)) :
    IsCompactOperator (A.halfSectionChartData.lowerOrderL volume p k) :=
  isCompactOperator_lowerOrderL (n := k + 1) le_rfl A

-- `W^{k,p} → W^{k,p}` is not compact on the closed disc, for a nonzero fibre.
example [Nontrivial F] (A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F)) :
    ¬ IsCompactOperator (id : BorderedSobolevSection A p k → BorderedSobolevSection A p k) :=
  not_isCompactOperator_id_unitClosedDisc A

end TauCeti.Examples.BorderedRellichDisc
