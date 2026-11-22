/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.Pseudodifferential.Microlocality
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Distribution
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Microlocality of properly supported pseudodifferential operators

Let `a` be a scalar symbol on `ℝⁿ` whose quantization has kernel supported within distance `R` of
the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`), acting on all distributions
`T ∈ 𝓓'(ℝⁿ)` by transposition (`TauCeti.Symbol.quantizeDistribution`). No compact spatial support
and no estimate uniform in the position is assumed. This file proves that such an operator does not
enlarge the wave front set,

`WF(Op(a) T) ⊆ WF(T)`

(`TauCeti.Symbol.waveFrontSet_quantizeDistribution_subset`), and hence not the singular support
either (`TauCeti.Symbol.singularSupport_quantizeDistribution_subset`). For symbols with compact
spatial support acting on a Bessel-potential space `H^t` this is
`TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset`; the point here is that `T` is
an arbitrary distribution, with no global Sobolev regularity, and that the symbol is only properly
supported.

## Proof

The reduction to the Sobolev statement is by localization in the input and in the symbol.

* **Localizing the symbol.** For a test function `χ`, the cut-off distribution `χ T` is the
  tempered distribution `Distribution.cutoffTempered T χ`, supported in `tsupport χ ⊆ U` for an
  open set `U`. If `ψ = 1` on the closed `R`-neighbourhood of `U`, then `Op(a)` and the
  quantization of `ψ a`, a symbol with compact spatial support, agree on the test functions
  supported in `U`. By duality their transposes agree on `U`, so `Op(a) (χ T)` is the tempered
  quantization of `ψ a` applied to `χ T`
  (`TauCeti.Symbol.quantizeDistribution_toDistribution_cutoffTempered`).
* **Localizing the input.** Take `χ = 1` on a ball around `x₀` of radius larger than `R`. Then
  `T - χ T` vanishes on that ball, and by proper support `Op(a) (T - χ T)` vanishes near `x₀`
  (`TauCeti.Symbol.dsupport_quantizeDistribution_subset`). Since `χ T` lies in some `H^t`
  (`Distribution.exists_memSobolev_cutoffTempered`), the Sobolev statement applies to
  `Op(a) (χ T)`, and `χ T` agrees with `T` near `x₀`.

## Main results

* `TauCeti.Symbol.quantizeDistribution_toDistribution_cutoffTempered`: on a cut-off distribution,
  `Op(a)` is the tempered quantization of a cut-off symbol with compact spatial support.
* `TauCeti.Symbol.waveFrontSet_quantizeDistribution_subset`: **microlocality**,
  `WF(Op(a) T) ⊆ WF(T)` for every distribution `T`.
* `TauCeti.Symbol.singularSupport_quantizeDistribution_subset`: **pseudolocality**,
  `singsupp (Op(a) T) ⊆ singsupp T`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008, Lecture I,
  Proposition 7.3 (`WF(Pu) ⊆ WF(u)` for properly supported operators).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (properly supported pseudodifferential operators and wave front sets).
-/

public section

noncomputable section

open MeasureTheory Complex Set Metric TopologicalSpace Distribution TemperedDistribution
open scoped SchwartzMap Distributions ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m R : ℝ} {a : Symbol n ℂ ℂ m}

/-- The transpose `Op(a)ᵗ φ = conj (Op(a)* φ)` of a properly supported operator on a real test
function `φ`, as in the definition of `TauCeti.Symbol.quantizeDistribution`. -/
private abbrev transposeTest (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
  TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
    (adjointTestFunctionCLM ha (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ))

/-- The transpose of `Op(a)` pairs with test functions as `Op(a)` does:
`∫ Op(a)ᵗ φ · u = ∫ φ · Op(a) u`. -/
private theorem integral_mul_transposeTest (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) (u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    ∫ x, transposeTest ha φ x * u x = ∫ x, (φ x : ℂ) * quantizeTestFunctionCLM ha u x := by
  have hloc (f : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
      LocallyIntegrableOn f (⊤ : Opens (CoordinateSpace n)) volume :=
    f.continuous.locallyIntegrable.locallyIntegrableOn _
  have h := congr($(quantizeDistribution_ofFun ha u) φ)
  rw [quantizeDistribution_apply, Distribution.complexPairing_ofFun (hloc u),
    Distribution.ofFun_apply (hloc _)] at h
  simpa [Complex.real_smul] using h

/-- The transpose of `Op(ψ a)` pairs with a test function `u` supported in `U` as `Op(a)` does,
when `ψ = 1` on the closed `R`-neighbourhood of `U`: `∫ Op(ψ a)ᵗ φ · u = ∫ φ · Op(a) u`. -/
private theorem integral_mul_transposeUniformCLM_cutoff_comp (ha : a.HasNearDiagonalKernel R)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {U : Set (CoordinateSpace n)} (hψU : EqOn ψ 1 (cthickening R U))
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) {u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (huU : tsupport u ⊆ U) :
    ∫ x, transposeUniformCLM ((cutoff ℂ hψ).comp a)
        ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
        (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ)) x * u x =
      ∫ x, (φ x : ℂ) * quantizeTestFunctionCLM ha u x := by
  set hb := ((hasCompactSpatialSupport_cutoff (V := ℂ) hψ hψc).comp_right a).isUniform
  -- On `u`, `Op(ψ a) u = Op(a) u`, since `Op(a) u` is supported where `ψ = 1`.
  have hu : TestFunction.toSchwartzMapCLM ℝ u = u.hasCompactSupport.toSchwartzMap u.contDiff := by
    ext y
    rw [TestFunction.toSchwartzMapCLM_apply, HasCompactSupport.toSchwartzMap_toFun]
  have hop (x : CoordinateSpace n) :
      quantizeUniformCLM _ hb (TestFunction.toSchwartzMapCLM ℝ u) x =
        quantizeTestFunctionCLM ha u x := by
    rw [quantizeUniformCLM_apply, quantizeTestFunctionCLM_apply, hu,
      ha.quantizeSchwartzValue_cutoff_comp hψ (hψU.mono (cthickening_subset_of_subset R ?_))]
    rwa [← hu, TestFunction.coe_toSchwartzMapCLM]
  calc ∫ x, transposeUniformCLM _ hb
        (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ)) x * u x
      = ∫ x, transposeUniformCLM _ hb
          (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ)) x *
            TestFunction.toSchwartzMapCLM ℝ u x := by
        simp only [TestFunction.toSchwartzMapCLM_apply]
    _ = ∫ x, TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ) x *
          quantizeUniformCLM _ hb (TestFunction.toSchwartzMapCLM ℝ u) x :=
        (integral_mul_quantizeUniformCLM _ hb _ _).symm
    _ = ∫ x, (φ x : ℂ) * quantizeTestFunctionCLM ha u x := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [hop x, TestFunction.toSchwartzMapCLM_apply, TestFunction.postcompCLM_apply,
          Function.comp_apply, Complex.ofRealCLM_apply]

/-- **Transposes are local.** If `ψ = 1` on the closed `R`-neighbourhood of an open set `U`, then
the transposes of `Op(a)` and of `Op(ψ a)` agree on `U`: both operators agree on the test functions
supported in `U`, and the transposes are smooth. -/
private theorem eqOn_transposeTest (ha : a.HasNearDiagonalKernel R) {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {U : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hψU : EqOn ψ 1 (cthickening R U))
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
    EqOn (transposeTest ha φ) (transposeUniformCLM ((cutoff ℂ hψ).comp a)
      ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
      (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ))) U := by
  set b := transposeUniformCLM ((cutoff ℂ hψ).comp a)
    ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
    (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ))
  -- Compare the multiplication operators by the two transposes, tested against every compactly
  -- supported Schwartz function `u` supported in `U`, viewed as a test function.
  have hK {g : CoordinateSpace n → ℂ} (hg : Continuous g) :
      ContinuousOn (fun y ↦ ContinuousLinearMap.mul ℂ ℂ (g y)) U :=
    ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp hg).continuousOn
  intro x hx
  have h := hU.eqOn_of_integral_clm_apply_eq (μ := volume) (hK (transposeTest ha φ).continuous)
    (hK b.continuous) (fun u hu huU ↦ ?_) hx
  · simpa using congr($h 1)
  set v : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) := u.toTestFunction hu (subset_univ _)
  have hv : ⇑v = u := SchwartzMap.coe_toTestFunction u hu _
  have h₁ := integral_mul_transposeTest ha φ v
  have h₂ := integral_mul_transposeUniformCLM_cutoff_comp ha hψ hψc hψU φ (u := v) (hv ▸ huU)
  rw [hv] at h₁ h₂
  simp only [ContinuousLinearMap.mul_apply']
  rw [h₁, h₂]

/-- **Localizing a properly supported operator.** Let `χ` be a test function supported in an open
set `U`, and `ψ` a compactly supported smooth function equal to `1` on the closed `R`-neighbourhood
of `U`. On the cut-off distribution `χ T`, the properly supported operator `Op(a)` is the
quantization on tempered distributions of the symbol `ψ a`, which has compact spatial support. -/
theorem quantizeDistribution_toDistribution_cutoffTempered (ha : a.HasNearDiagonalKernel R)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hψU : EqOn ψ 1 (cthickening R U))
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) {χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (hχU : tsupport χ ⊆ U) :
    quantizeDistribution ha (toDistribution ⊤ (T.cutoffTempered χ)) =
      toDistribution ⊤ (quantizeTempered ℂ ((cutoff ℂ hψ).comp a)
        ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
        (T.cutoffTempered χ)) := by
  ext φ
  rw [quantizeDistribution_apply, complexPairing_toDistribution, toDistribution_apply,
    quantizeTempered_apply_apply]
  refine T.cutoffTempered_apply_congr χ fun x hx ↦ ?_
  rw [TestFunction.toSchwartzMapCLM_apply, eqOn_transposeTest ha hψ hψc hU hψU φ (hχU hx)]

/-- Microlocality on cut-off distributions: if `χ T` is microlocally smooth at `(x₀, ξ₀)`, so is
`Op(a) (χ T)`. Since `χ T` lies in some `H^t` and `Op(a) (χ T) = Op(ψ a) (χ T)` for a cutoff `ψ`,
this is microlocality of operators with compact spatial support on `H^t`. -/
private theorem isMicrolocallySmoothAt_quantizeDistribution_toDistribution_cutoffTempered
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ))
    (χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) {x₀ ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0)
    (h : (toDistribution ⊤ (T.cutoffTempered χ)).IsMicrolocallySmoothAt x₀ ξ₀) :
    (quantizeDistribution ha (toDistribution ⊤ (T.cutoffTempered χ))).IsMicrolocallySmoothAt
      x₀ ξ₀ := by
  -- A cutoff `ψ = 1` on the closed `R`-neighbourhood of the open set `U = thickening 1 (supp χ)`.
  have hK : IsCompact (cthickening R (cthickening 1 (tsupport χ))) :=
    χ.hasCompactSupport.isCompact.cthickening.cthickening
  obtain ⟨ψ, hψ, -, hψ1, hψc, -⟩ := hK.exists_contDiff_cutoff isOpen_univ (subset_univ _)
  have hψU : EqOn ψ 1 (cthickening R (thickening 1 (tsupport χ))) := fun x hx ↦ by
    simpa using interior_subset (hψ1 (cthickening_subset_of_subset R
      (thickening_subset_cthickening _ _) hx))
  have hb := (hasCompactSpatialSupport_cutoff (V := ℂ) hψ hψc).comp_right a
  -- `χ T ∈ H^t` for some `t`, and `Op(a) (χ T) = Op(ψ a) (χ T)` there.
  obtain ⟨t, ht⟩ := T.exists_memSobolev_cutoffTempered χ
  have hD : toDistribution ⊤ (T.cutoffTempered χ) =
      toDistribution ⊤ ht.toBesselPotentialSpace.toDistr := by
    rw [ht.toBesselPotentialSpace_toDistr]
  have hOp : quantizeDistribution ha (toDistribution ⊤ (T.cutoffTempered χ)) =
      toDistribution ⊤ (quantizeSobolev _ hb t ht.toBesselPotentialSpace).toDistr := by
    rw [toDistr_quantizeSobolev, ht.toBesselPotentialSpace_toDistr]
    exact quantizeDistribution_toDistribution_cutoffTempered ha hψ hψc isOpen_thickening hψU T
      (self_subset_thickening one_pos _)
  by_contra hn
  have hmem := waveFrontSet_toDistribution_quantizeSobolev_subset hb t
    ht.toBesselPotentialSpace (hOp ▸ mem_waveFrontSet_iff.2 ⟨trivial, hξ₀, hn⟩)
  exact (mem_waveFrontSet_iff.1 (hD ▸ hmem)).2.2 h

/-- **Microlocality of properly supported pseudodifferential operators.** For a scalar symbol `a`
whose quantization has kernel supported within distance `R` of the diagonal, and every distribution
`T` on `ℝⁿ`, the wave front set of `Op(a) T` is contained in the wave front set of `T`:
`WF(Op(a) T) ⊆ WF(T)`. -/
theorem waveFrontSet_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).waveFrontSet ⊆ T.waveFrontSet := by
  rintro ⟨x₀, ξ₀⟩ hp
  obtain ⟨-, hξ₀, hnot⟩ := mem_waveFrontSet_iff.1 hp
  refine mem_waveFrontSet_iff.2 ⟨trivial, hξ₀, fun hT ↦ hnot ?_⟩
  -- A cutoff `χ = 1` on `ball x₀ r`, where `r > R`.
  set r : ℝ := |R| + 1
  have hr₀ : 0 < r := by positivity
  let ρ : ContDiffBump x₀ := ⟨r, 2 * r, hr₀, by linarith⟩
  let χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
    ⟨fun x ↦ (ρ x : ℂ), ofRealCLM.contDiff.comp ρ.contDiff,
      ρ.hasCompactSupport.comp_left ofReal_zero, subset_univ _⟩
  -- `χ` is the bump function `ρ`, viewed as a complex-valued test function.
  have hχx (x : CoordinateSpace n) : χ x = ρ x := (rfl)
  set D := toDistribution ⊤ (T.cutoffTempered χ)
  -- `T - χ T` vanishes on `ball x₀ r`.
  have hdsupp : dsupport (T - D) ⊆ (ball x₀ r)ᶜ := by
    refine subset_compl_comm.1 fun x hx hx' ↦
      ((T.isVanishingOn_sub_toDistribution_cutoffTempered fun y hy ↦ ?_).disjoint_dsupport
        isOpen_ball).ne_of_mem hx hx' rfl
    rw [hχx, ρ.one_of_mem_closedBall (ball_subset_closedBall hy), ofReal_one]
  -- So `χ T` is microlocally smooth at `(x₀, ξ₀)`, and `Op(a) (T - χ T)` vanishes near `x₀`.
  have hTD : (T - D).IsMicrolocallySmoothAt x₀ ξ₀ :=
    isMicrolocallySmoothAt_of_notMem_dsupport trivial
      (fun h ↦ hdsupp h (mem_ball_self hr₀)) ξ₀
  have hD : D.IsMicrolocallySmoothAt x₀ ξ₀ := by
    convert hT.add (hTD.smul (-1)) using 1
    module
  have hOpTD : (quantizeDistribution ha (T - D)).IsMicrolocallySmoothAt x₀ ξ₀ :=
    isMicrolocallySmoothAt_of_notMem_dsupport trivial (fun h ↦ notMem_cthickening_compl_ball
      (by linarith [le_abs_self R]) hr₀ (cthickening_subset_of_subset R hdsupp
        (dsupport_quantizeDistribution_subset ha _ h))) ξ₀
  have hsplit : quantizeDistribution ha T =
      quantizeDistribution ha D + quantizeDistribution ha (T - D) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit]
  exact (isMicrolocallySmoothAt_quantizeDistribution_toDistribution_cutoffTempered ha T χ hξ₀
    hD).add hOpTD

/-- **Pseudolocality of properly supported pseudodifferential operators.** For a scalar symbol
`a` whose quantization has kernel supported within distance `R` of the diagonal, and every
distribution `T` on `ℝⁿ`, `Op(a) T` is smooth wherever `T` is: the singular support of `Op(a) T` is
contained in that of `T`. -/
theorem singularSupport_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).singularSupport ⊆ T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet]
  exact image_mono (waveFrontSet_quantizeDistribution_subset ha T)

end Symbol

end TauCeti
