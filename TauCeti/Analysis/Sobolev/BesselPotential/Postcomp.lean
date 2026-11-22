/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

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
* `BesselPotentialSpace.toDistribution_toDistr_postcomp`: as a distribution on an open set, `L u`
  is `L` applied to the values of `u`.
* `BesselPotentialSpace.sum_postcomp_toSpanSingleton_coord`: for a basis `(e_j)` of a
  finite-dimensional `F` with coordinate functionals `(c_j)`, every `u ∈ H^{s,p}(E, F)` is
  `∑ⱼ e_j (c_j u)`.
* `TemperedDistribution.MemSobolev.postcomp`: applying `L` to the values of a tempered
  distribution in `H^{s,p}(E, F)` gives one in `H^{s,p}(E, G)`.
* `TemperedDistribution.MemSobolev.compLp`: applying `L` to the values of an `Lᵖ` function in
  `H^{s,p}` gives an `Lᵖ` function in `H^{s,p}`.
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

/-- Restricting `L ∘ f` to a distribution on `Ω` applies `L` to the values of the restriction
of `f`. -/
theorem toDistribution_toDistr_postcomp {Ω : TopologicalSpace.Opens E} (L : F →L[ℂ] G)
    (f : H^{s, p}(E, F)) :
    toDistribution Ω (postcomp E s p L f).toDistr =
      Distribution.mapCLM (L.restrictScalars ℝ) (toDistribution Ω f.toDistr) := by
  ext φ
  simp [Distribution.mapCLM_apply]

@[simp]
theorem toLp_postcomp (L : F →L[ℂ] G) (f : H^{s, p}(E, F)) :
    (postcomp E s p L f).toLp = L.compLp f.toLp :=
  (rfl)

/-- **Expansion in a basis of the values.** For a basis `(e_j)` of a finite-dimensional `F` with
coordinate functionals `(c_j)`, every `u ∈ H^{s,p}(E, F)` is the sum `∑ⱼ e_j (c_j u)` of its
scalar coordinates `c_j u ∈ H^{s,p}(E, ℂ)` times the basis vectors. -/
theorem sum_postcomp_toSpanSingleton_coord [FiniteDimensional ℂ F] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ F) (u : H^{s, p}(E, F)) :
    ∑ j, postcomp E s p (ContinuousLinearMap.toSpanSingleton ℂ (b j))
      (postcomp E s p (b.coord j).toContinuousLinearMap u) = u := by
  refine ext ?_
  ext φ
  rw [← toDistrCLM_apply, map_sum, _root_.sum_apply]
  simp only [toDistrCLM_apply, toDistr_postcomp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  exact b.sum_repr _

end BesselPotentialSpace

/-- **Applying a continuous linear map to the values preserves `H^{s,p}`.** If the tempered
distribution `f` lies in `H^{s,p}(E, F)`, then `φ ↦ L (f φ)` lies in `H^{s,p}(E, G)`. -/
theorem TemperedDistribution.MemSobolev.postcomp {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : 𝓢'(E, F)} (hf : MemSobolev s p f) (L : F →L[ℂ] G) :
    MemSobolev s p (PointwiseConvergenceCLM.postcomp _ L f) := by
  have h : (BesselPotentialSpace.postcomp E s p L hf.toBesselPotentialSpace).toDistr =
      PointwiseConvergenceCLM.postcomp _ L f := by
    ext φ
    rw [BesselPotentialSpace.toDistr_postcomp_apply, MemSobolev.toBesselPotentialSpace_toDistr,
      PointwiseConvergenceCLM.postcomp_apply_apply]
  exact h ▸ BesselPotentialSpace.memSobolev_toDistr _

/-- On Schwartz functions, the operator induced by `L` on `H^{s,p}` is `u ↦ L ∘ u`. -/
theorem SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : F →L[ℂ] G) (u : 𝓢(E, F)) :
    toBesselPotentialSpaceCLM s p (u.postcompCLM L) =
      BesselPotentialSpace.postcomp E s p L (toBesselPotentialSpaceCLM s p u) := by
  ext φ
  rw [toDistr_toBesselPotentialSpaceCLM, BesselPotentialSpace.toDistr_postcomp_apply,
    toDistr_toBesselPotentialSpaceCLM, toTemperedDistributionCLM_postcompCLM_apply]

namespace TemperedDistribution

/-- Applying a complex-linear map to the values of an `Lᵖ` function preserves `H^{s,p}`. -/
theorem MemSobolev.compLp {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : Lp F p (volume : Measure E)}
    (hu : MemSobolev s p (u : 𝓢'(E, F))) (L : F →L[ℂ] G) :
    MemSobolev s p ((L.compLp u : Lp G p volume) : 𝓢'(E, G)) := by
  have h := (BesselPotentialSpace.postcomp E s p L hu.toBesselPotentialSpace).memSobolev_toDistr
  convert h using 1
  ext φ
  rw [BesselPotentialSpace.toDistr_postcomp_apply, MemSobolev.toBesselPotentialSpace_toDistr,
    Lp.toTemperedDistribution_compLp_apply]

end TemperedDistribution
