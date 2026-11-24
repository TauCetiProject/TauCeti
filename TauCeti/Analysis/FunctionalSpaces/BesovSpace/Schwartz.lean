/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.FourierMultiplier
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.PartialSum
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Postcomp
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Smooth density and Schwartz intertwining in Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and let
`Δⱼ` (`j ≥ 0`) be its inhomogeneous Littlewood–Paley blocks. Every Schwartz function `f ∈ 𝓢(E, F)`
embeds continuously into `B^s_{p,q}(E, F)` via `SchwartzMap.toBesovSpaceCLM` (defined in
`TauCeti.Analysis.Sobolev.BesselPotential.Besov` for all `s ∈ ℝ` and `1 ≤ p, q ≤ ∞`), intertwining
Besov and Bernstein inclusions, change of bump, `postcomp`, Bessel-potential inclusions and the
`B^s_{2,2} ≃ H^{s,2}` equivalence, dyadic partial sums `TauCeti.BesovSpace.partialSumCLM`
(defined in `TauCeti.Analysis.FunctionalSpaces.BesovSpace.PartialSum`), Fourier multipliers,
Bessel-potential lifting, and smooth multiplication.

Because the Fourier transform of each dyadic partial sum `S_N u` has compact support, `S_N u` lies
in `B^{s+1}_{p,1} ⊆ H^{s+1,p}`, so for `1 ≤ p < ∞` it lies in the closure of `𝓢(E, F)` in
`B^s_{p,q}` for *every* `1 ≤ q ≤ ∞` (including `q = ∞`). Combining this with `S_N u → u` for
`q < ∞` (`TauCeti.BesovSpace.tendsto_partialSumCLM`) and the density of compactly supported smooth
functions in `𝓢(E, F)` shows that both `𝓢(E, F)` and `{f ∈ 𝓢(E, F) | HasCompactSupport f}` are
norm-dense in `B^s_{p,q}(E, F)` whenever `1 ≤ p < ∞` and `1 ≤ q < ∞`.

## Main declarations

* `SchwartzMap.inclusion_toBesovSpaceCLM`, `SchwartzMap.inclusionOfLT_toBesovSpaceCLM`,
  `SchwartzMap.inclusionOfExponentLE_toBesovSpaceCLM`, `SchwartzMap.bumpEquiv_toBesovSpaceCLM`,
  `SchwartzMap.toBesovSpaceCLM_postcompCLM`, `SchwartzMap.toBesovSpace_toBesselPotentialSpaceCLM`,
  `SchwartzMap.toBesselPotentialSpace_toBesovSpaceCLM`,
  `SchwartzMap.besselPotentialSpaceEquiv_toBesovSpaceCLM`,
  `SchwartzMap.besselPotentialSpaceEquiv_symm_toBesselPotentialSpaceCLM`,
  `SchwartzMap.partialSumCLM_toBesovSpaceCLM`, `SchwartzMap.fourierMultiplierCLM_toBesovSpaceCLM`,
  `SchwartzMap.besselPotentialEquiv_toBesovSpaceCLM`, and `SchwartzMap.smulLeftCLM_toBesovSpaceCLM`:
  compatibility of `SchwartzMap.toBesovSpaceCLM` with inclusions, change of bump, `postcomp`,
  `BesselPotentialSpace`, dyadic partial sums, Fourier multipliers, Bessel-potential lifting, and
  smooth multiplication.
* `SchwartzMap.denseRange_toBesovSpaceCLM` and
  `SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport`: for `1 ≤ p < ∞` and `1 ≤ q < ∞`,
  Schwartz functions and compactly supported smooth functions are dense in `B^s_{p,q}(E, F)`.
* `TauCeti.BesovSpace.continuousLinearMap_ext` and
  `TauCeti.BesovSpace.continuousLinearMap_ext_hasCompactSupport`: continuous semilinear maps out of
  `B^s_{p,q}(E, F)` (`p, q < ∞`) are determined by their values on (compactly supported) Schwartz
  functions.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2 (Theorem 6.2.3).
* H. Triebel, *Theory of Function Spaces*, Section 2.3.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Proposition 2.74.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

namespace SchwartzMap

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

@[simp]
theorem inclusion_toBesovSpaceCLM {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')] (hs : s' ≤ s)
    (hq : q ≤ q') (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.inclusion F φ p hs hq (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ s' p q' f :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem inclusionOfLT_toBesovSpaceCLM {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')] (hs : s' < s)
    (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.inclusionOfLT F φ p q q' hs (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ s' p q' f :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem inclusionOfExponentLE_toBesovSpaceCLM {r : ℝ≥0∞} [Fact (1 ≤ r)] (hpr : p ≤ r)
    (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.inclusionOfExponentLE F φ q hpr (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r q f :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem bumpEquiv_toBesovSpaceCLM (φ' : ContDiffBump (0 : E)) (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.bumpEquiv F φ φ' s p q (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ' s p q f :=
  TauCeti.BesovSpace.ext (by simp)

/-- On Schwartz functions, `TauCeti.BesovSpace.postcomp` is post-composition of Schwartz maps. -/
theorem toBesovSpaceCLM_postcompCLM (L : F →L[ℂ] G) (f : 𝓢(E, F)) :
    toBesovSpaceCLM G φ s p q (f.postcompCLM L) =
      TauCeti.BesovSpace.postcomp φ s p q L (toBesovSpaceCLM F φ s p q f) := by
  refine TauCeti.BesovSpace.ext ?_
  ext ψ
  rw [toDistr_toBesovSpaceCLM, TauCeti.BesovSpace.toDistr_postcomp_apply,
    toDistr_toBesovSpaceCLM, toTemperedDistributionCLM_postcompCLM_apply]

@[simp]
theorem toBesovSpace_toBesselPotentialSpaceCLM (f : 𝓢(E, F)) :
    BesselPotentialSpace.toBesovSpace φ (f.toBesselPotentialSpaceCLM s p) =
      toBesovSpaceCLM F φ s p ∞ f :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem toBesselPotentialSpace_toBesovSpaceCLM (f : 𝓢(E, F)) :
    (toBesovSpaceCLM F φ s p 1 f).toBesselPotentialSpace = f.toBesselPotentialSpaceCLM s p :=
  BesselPotentialSpace.ext (by simp)

@[simp]
theorem besselPotentialSpaceEquiv_toBesovSpaceCLM {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (f : 𝓢(E, H)) :
    TauCeti.BesovSpace.besselPotentialSpaceEquiv H φ s (toBesovSpaceCLM H φ s 2 2 f) =
      f.toBesselPotentialSpaceCLM s 2 :=
  BesselPotentialSpace.ext (by simp)

@[simp]
theorem besselPotentialSpaceEquiv_symm_toBesselPotentialSpaceCLM {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (f : 𝓢(E, H)) :
    (TauCeti.BesovSpace.besselPotentialSpaceEquiv H φ s).symm
        (f.toBesselPotentialSpaceCLM s 2) =
      toBesovSpaceCLM H φ s 2 2 f :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem partialSumCLM_toBesovSpaceCLM (N : ℕ) (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.partialSumCLM F φ s p q N (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ s p q (∑ j ∈ Finset.range N,
        SchwartzMap.fourierMultiplierCLM F
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f) :=
  TauCeti.BesovSpace.ext <| by
    rw [TauCeti.BesovSpace.toDistr_partialSumCLM, toDistr_toBesovSpaceCLM,
      toDistr_toBesovSpaceCLM, map_sum]
    simp [TemperedDistribution.littlewoodPaleyBlock_toTemperedDistributionCLM_eq]

open scoped ContDiff in
@[simp]
theorem fourierMultiplierCLM_toBesovSpaceCLM {g : E → ℂ} {m s' : ℝ} (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    (hs : s' = s - m) (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.fourierMultiplierCLM F φ p q hg hgm hs (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ s' p q (fourierMultiplierCLM F g f) := by
  have hgt : g.HasTemperateGrowth := .of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hg hgm
  exact TauCeti.BesovSpace.ext (by
    simp [TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq hgt])

@[simp]
theorem besselPotentialEquiv_toBesovSpaceCLM (t : ℝ) {s' : ℝ} (hs : s' = s - t) (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.besselPotentialEquiv F φ p q t hs (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ s' p q
        (fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) f) := by
  have hgt : Function.HasTemperateGrowth (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) :=
    .of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow
      (TauCeti.contDiff_ofReal_one_add_norm_sq_rpow (t / 2))
      (TauCeti.exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le t)
  exact TauCeti.BesovSpace.ext (by
    simp [TemperedDistribution.besselPotential,
      TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq hgt])

@[simp]
theorem smulLeftCLM_toBesovSpaceCLM {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.smulLeftCLM F φ s p q g hg hbd (toBesovSpaceCLM F φ s p q f) =
      toBesovSpaceCLM F φ s p q (smulLeftCLM F g f) :=
  TauCeti.BesovSpace.ext (by simp [TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq])

end SchwartzMap

namespace TauCeti.BesovSpace

open TemperedDistribution

/-- Almost everywhere, the `j`-th block of `f` in `B^s_{p,q}` is the Schwartz function
`𝓕⁻ (ψⱼ • 𝓕 f)`. -/
theorem coeFn_block_toBesovSpaceCLM {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (f : 𝓢(E, F)) (j : ℕ) :
    (SchwartzMap.toBesovSpaceCLM F φ s p q f).block j =ᵐ[volume]
      SchwartzMap.fourierMultiplierCLM F
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f := by
  rw [block_toBesovSpaceCLM]
  exact SchwartzMap.coeFn_toLp _ p volume

section Density

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- For `1 ≤ p < ∞` and *every* `1 ≤ q ≤ ∞` (including `q = ∞`), each dyadic partial sum `S_N u`
lies in the `B^s_{p,q}`-norm closure of `𝓢(E, F)`: it lifts to `H^{s+1,p}(E, F)`, where Schwartz
functions are dense. -/
theorem partialSumCLM_mem_closure_range_toBesovSpaceCLM (hp : p ≠ ∞) (N : ℕ)
    (u : BesovSpace F φ s p q) :
    partialSumCLM F φ s p q N u ∈
      closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p q)) := by
  let v : BesovSpace F φ (s + 1) p 1 :=
    (memBesov_toDistr_partialSumCLM (s + 1) 1 N u).toBesovSpace
  let w : H^{s + 1, p}(E, F) := v.toBesselPotentialSpace
  let T : H^{s + 1, p}(E, F) →L[ℂ] BesovSpace F φ s p q :=
    inclusionOfLT F φ p ∞ q (lt_add_one s) ∘L BesselPotentialSpace.toBesovSpace φ
  have hTw : T w = partialSumCLM F φ s p q N u := ext (by simp [T, w, v])
  have hw : w ∈ closure (Set.range (SchwartzMap.toBesselPotentialSpaceCLM (s + 1) p)) :=
    SchwartzMap.denseRange_toBesselPotentialSpaceCLM (s + 1) hp w
  rw [← hTw]
  have hcomp : ⇑T ∘ ⇑(SchwartzMap.toBesselPotentialSpaceCLM (s + 1) p) =
      ⇑(SchwartzMap.toBesovSpaceCLM F φ s p q) :=
    funext fun f ↦ by simp [T]
  have himg := image_closure_subset_closure_image T.continuous (Set.mem_image_of_mem T hw)
  rwa [← Set.range_comp, hcomp] at himg

/-- Compactly supported smooth functions and Schwartz functions have the same norm closure in every
Besov space `B^s_{p,q}(E, F)` (`1 ≤ p, q ≤ ∞`), because compactly supported functions are dense in
`𝓢(E, F)` and `SchwartzMap.toBesovSpaceCLM` is continuous. -/
theorem closure_image_toBesovSpaceCLM_hasCompactSupport :
    closure (SchwartzMap.toBesovSpaceCLM F φ s p q ''
        {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) =
      closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p q)) := by
  rw [← closure_image_closure (map_continuous _), SchwartzMap.dense_hasCompactSupport.closure_eq,
    Set.image_univ]

/-- **Schwartz functions are dense in `B^s_{p,q}(E, F)`** for `1 ≤ p < ∞` and `1 ≤ q < ∞`
(Bergh–Löfström, Theorem 6.2.3 / Triebel, Section 2.3.2). -/
theorem _root_.SchwartzMap.denseRange_toBesovSpaceCLM (φ : ContDiffBump (0 : E)) (s : ℝ)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    DenseRange (SchwartzMap.toBesovSpaceCLM (E := E) F φ s p q) := fun u ↦
  isClosed_closure.mem_of_tendsto (tendsto_partialSumCLM hq u)
    (Eventually.of_forall fun N ↦ partialSumCLM_mem_closure_range_toBesovSpaceCLM hp N u)

/-- **Compactly supported smooth functions are dense in `B^s_{p,q}(E, F)`** for `1 ≤ p < ∞` and
`1 ≤ q < ∞`. -/
theorem _root_.SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport
    (φ : ContDiffBump (0 : E)) (s : ℝ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Dense (SchwartzMap.toBesovSpaceCLM F φ s p q ''
      {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) :=
  (SchwartzMap.denseRange_toBesovSpaceCLM φ s hp hq).dense_image (map_continuous _)
    SchwartzMap.dense_hasCompactSupport

/-- Explicit norm approximation in `B^s_{p,q}(E, F)` (`p, q < ∞`) by compactly supported Schwartz
functions. -/
theorem exists_hasCompactSupport_norm_sub_lt (hp : p ≠ ∞) (hq : q ≠ ∞)
    (u : BesovSpace F φ s p q) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(E, F), HasCompactSupport (f : E → F) ∧
      ‖u - SchwartzMap.toBesovSpaceCLM F φ s p q f‖ < ε := by
  obtain ⟨_, ⟨f, hf, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1
    ((SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport φ s hp hq) u) ε hε
  exact ⟨f, hf, by rwa [dist_eq_norm] at hdist⟩

/-- Continuous semilinear maps out of `B^s_{p,q}(E, F)` (`p, q < ∞`) into a Hausdorff space are
determined by their values on compactly supported Schwartz functions. -/
theorem continuousLinearMap_ext_hasCompactSupport {R : Type*} [Semiring R] {σ : ℂ →+* R}
    {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    (hp : p ≠ ∞) (hq : q ≠ ∞) {T T' : BesovSpace F φ s p q →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F), HasCompactSupport (f : E → F) →
      T (SchwartzMap.toBesovSpaceCLM F φ s p q f) =
        T' (SchwartzMap.toBesovSpaceCLM F φ s p q f)) :
    T = T' := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  refine (SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport φ s hp hq).induction ?_
    (isClosed_eq T.continuous T'.continuous) u
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

/-- Continuous semilinear maps out of `B^s_{p,q}(E, F)` (`p, q < ∞`) into a Hausdorff space are
determined by their values on Schwartz functions. -/
theorem continuousLinearMap_ext {R : Type*} [Semiring R] {σ : ℂ →+* R}
    {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    (hp : p ≠ ∞) (hq : q ≠ ∞) {T T' : BesovSpace F φ s p q →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F), T (SchwartzMap.toBesovSpaceCLM F φ s p q f) =
      T' (SchwartzMap.toBesovSpaceCLM F φ s p q f)) :
    T = T' :=
  continuousLinearMap_ext_hasCompactSupport hp hq fun f _ ↦ h f

end Density

end TauCeti.BesovSpace
