/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Applying a continuous linear map to the values of Bessel-potential functions

A continuous linear map `L : F →L[ℂ] G` acts on `F`-valued tempered distributions by
`(L u) φ = L (u φ)`. The Bessel potential acts on the test function, so it commutes with `L`, and
`L` maps `Lᵖ(E, F)` to `Lᵖ(E, G)` with norm at most `‖L‖`. Hence `L` induces a bounded operator
`H^{s,p}(E, F) → H^{s,p}(E, G)` on Mathlib's Bessel-potential spaces, which on Schwartz functions
is `u ↦ L ∘ u`.

For finite-dimensional `F`, an isomorphism `F ≃L[ℂ] F'` with a complex inner product space `F'`
turns these operators into isomorphisms of the Bessel-potential spaces, so results proved for
Hilbert-space values with Plancherel's theorem transfer to any finite-dimensional normed `F`.

## Main declarations

* `BesselPotentialSpace.postcomp`: the operator `H^{s,p}(E, F) →L[ℂ] H^{s,p}(E, G)` induced by
  `L : F →L[ℂ] G`.
* `SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM`: on Schwartz functions it is
  `u ↦ L ∘ u`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

namespace BesselPotentialSpace

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (E s p) in
/-- The bounded operator `H^{s,p}(E, F) → H^{s,p}(E, G)` induced by a continuous linear map
`L : F →L[ℂ] G`. It sends the tempered distribution `u` to `φ ↦ L (u φ)` and its `Lᵖ` part
`J^s u` to `L ∘ J^s u`. -/
def postcomp (L : F →L[ℂ] G) : H^{s, p}(E, F) →L[ℂ] H^{s, p}(E, G) :=
  LinearMap.mkContinuous
    { toFun f :=
        { toDistr := PointwiseConvergenceCLM.postcomp _ L f.toDistr
          toLp := L.compLp f.toLp
          bessel_toDistr_eq_toLp := by
            ext φ
            rw [Lp.toTemperedDistribution_compLp_apply, ← f.bessel_toDistr_eq_toLp]
            -- The Bessel potential acts on the test function, so it commutes with `L` by
            -- definition.
            rfl }
      map_add' f g := ext (map_add (PointwiseConvergenceCLM.postcomp _ L) f.toDistr g.toDistr)
      map_smul' c f := ext (map_smul (PointwiseConvergenceCLM.postcomp _ L) c f.toDistr) }
    ‖L‖ fun f ↦ by
      rw [← norm_toLp_eq, ← norm_toLp_eq]
      exact L.norm_compLp_le f.toLp

@[simp]
theorem toDistr_postcomp_apply (L : F →L[ℂ] G) (f : H^{s, p}(E, F)) (φ : 𝓢(E, ℂ)) :
    (postcomp E s p L f).toDistr φ = L (f.toDistr φ) :=
  (rfl)

@[simp]
theorem toLp_postcomp (L : F →L[ℂ] G) (f : H^{s, p}(E, F)) :
    (postcomp E s p L f).toLp = L.compLp f.toLp :=
  (rfl)

end BesselPotentialSpace

/-- On Schwartz functions, the operator induced by `L` on `H^{s,p}` is `u ↦ L ∘ u`. -/
theorem SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : F →L[ℂ] G) (u : 𝓢(E, F)) :
    toBesselPotentialSpaceCLM s p (u.postcompCLM L) =
      BesselPotentialSpace.postcomp E s p L (toBesselPotentialSpaceCLM s p u) := by
  ext φ
  rw [toDistr_toBesselPotentialSpaceCLM, BesselPotentialSpace.toDistr_postcomp_apply,
    toDistr_toBesselPotentialSpaceCLM, toTemperedDistributionCLM_postcompCLM_apply]
