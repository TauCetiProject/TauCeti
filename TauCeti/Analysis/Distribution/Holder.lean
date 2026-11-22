/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SingularSupport
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local
public import TauCeti.Analysis.Holder.Zygmund
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Holder.JetBounds
import TauCeti.Analysis.Holder.Localization
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributions that are `C^{k,α}` functions near a point

A distribution `T` on an open subset `Ω` of a finite-dimensional real inner product space `E` is
*`C^{k,α}` near `x`* (`Distribution.IsLocallyCkHolderAt k α T x`) when, on an open neighbourhood
`U ⊆ Ω` of `x`, it is a `C^k` function `f` whose `k`-th derivative is `α`-Hölder on `U`: for every
real test function `φ` supported in `U`, `T φ = ∫ φ • f`. This is the regularity in which the
localized Schauder theorem is stated: if `P u` is `C^{k,α}` near `x` for an elliptic operator `P`
of order `m`, then `u` is `C^{k+m,α}` near `x`. The definition follows that of the singular
support (`Distribution.singularSupport`), whose complement consists of the points near which `T`
is a smooth function; a distribution smooth near `x` is `C^{k,α}` near `x` for every `k` and every
`α ≤ 1` (`Distribution.isLocallyCkHolderAt_of_notMem_singularSupport`). Being `C^{k,α}` near `x`
is preserved by sums and scalar multiples (`Distribution.IsLocallyCkHolderAt.add`,
`Distribution.IsLocallyCkHolderAt.smul`) and is monotone in `k` and `α`
(`Distribution.IsLocallyCkHolderAt.mono`).

For `0 < α < 1` this is local membership in the Hölder–Zygmund space `𝒞^{k+α} = B^{k+α}_{∞,∞}`
(`Distribution.isLocallyMemBesovAt_iff_isLocallyCkHolderAt`; the implication from `C^{k,α}` to
`𝒞^{k+α}` holds for every `α ≤ 1`, `Distribution.IsLocallyCkHolderAt.isLocallyMemBesovAt`):

`T ∈ 𝒞^{k+α}` near `x` ↔ `T` is `C^{k,α}` near `x`.

Here `T ∈ 𝒞^{k+α}` near `x` means that the cut-off tempered distributions `ψ T`, for test
functions `ψ` supported near `x`, lie in `𝒞^{k+α}` (`Distribution.IsLocallyMemBesovAt`). This
transfers regularity theorems proved on the Hölder–Zygmund scale, such as local elliptic
regularity, to classical Hölder regularity of distributions.

## The argument

If `χ T ∈ 𝒞^{k+α}` for a test function `χ` equal to one near `x`, then `χ T` is the tempered
distribution of a bounded `C^{k,α}` function `g` (`TauCeti.BesovSpace.toCkHolderSpace`), and `T`
agrees with `χ T`, hence with `g`, where `χ = 1`
(`Distribution.apply_eq_integral_of_cutoffTempered_apply_eq_integral`). Conversely, if `T` is the
function `f` on a ball around `x` on which `f` is `C^{k,α}`, then for a test function `χ` equal to
one near `x` and supported in a smaller ball, the product `χ f` is a bounded `C^{k,α}` function on
all of `E` (`TauCeti.CkHolderSpace.cutoff`), so it lies in `𝒞^{k+α}`
(`TauCeti.BesovSpace.ofCkHolderSpace`), and it is the tempered distribution `χ T`
(`Distribution.cutoffTempered_eq_of_apply_eq_integral`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.32)–(3.34) (the Zygmund spaces and their Hölder identification).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
-/

public section

noncomputable section

open Set TopologicalSpace MeasureTheory TemperedDistribution Metric
open scoped NNReal ENNReal Topology ContDiff Distributions SchwartzMap

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}
  {k : ℕ} {α : ℝ≥0} {x : E}

variable (k α) in
/-- A distribution `T` on `Ω` is **`C^{k,α}` near `x`** if `x` has an open neighbourhood `U ⊆ Ω`
on which `T` is a `C^k` function whose `k`-th derivative is `α`-Hölder: there is a function `f`,
`C^k` on `U` with `iteratedFDeriv ℝ k f` `α`-Hölder on `U`, such that `T φ = ∫ φ • f` for every
real test function `φ` supported in `U`. -/
def IsLocallyCkHolderAt (T : 𝓓'(Ω, F)) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ∃ f : E → F, ContDiffOn ℝ k f U ∧
    (∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ k f) U) ∧
      ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y

/-- Unfolds `IsLocallyCkHolderAt` into its neighbourhood and its local representative. -/
theorem isLocallyCkHolderAt_iff {T : 𝓓'(Ω, F)} :
    T.IsLocallyCkHolderAt k α x ↔ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ∃ f : E → F,
      ContDiffOn ℝ k f U ∧ (∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ k f) U) ∧
        ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- A distribution can only be `C^{k,α}` near points of its domain. -/
theorem IsLocallyCkHolderAt.mem {T : 𝓓'(Ω, F)} (h : T.IsLocallyCkHolderAt k α x) : x ∈ Ω :=
  let ⟨_, _, hxU, hUΩ, _⟩ := h
  hUΩ hxU

variable (k α) in
/-- The set of points near which a distribution is `C^{k,α}` is open. -/
theorem isOpen_setOf_isLocallyCkHolderAt (T : 𝓓'(Ω, F)) :
    IsOpen {x : E | T.IsLocallyCkHolderAt k α x} :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨U, hU, hxU, hUΩ, hf⟩ ↦
    ⟨U, fun _ hy ↦ ⟨U, hU, hy, hUΩ, hf⟩, hU, hxU⟩

/-- The zero distribution is `C^{k,α}` near every point of its domain. -/
@[simp]
theorem isLocallyCkHolderAt_zero_iff : (0 : 𝓓'(Ω, F)).IsLocallyCkHolderAt k α x ↔ x ∈ Ω :=
  ⟨IsLocallyCkHolderAt.mem, fun hx ↦ ⟨Ω, Ω.isOpen, hx, subset_rfl, 0, contDiffOn_const,
    ⟨0, (TauCeti.holderWith_iteratedFDeriv_const k α (0 : F)).holderOnWith _⟩, fun _ _ ↦ by simp⟩⟩

section SMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- A scalar multiple of a distribution `C^{k,α}` near `x` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.smul {T : 𝓓'(Ω, F)} (h : T.IsLocallyCkHolderAt k α x) (c : 𝕜) :
    (c • T).IsLocallyCkHolderAt k α x := by
  obtain ⟨U, hU, hxU, hUΩ, f, hf, ⟨C, hC⟩, hT⟩ := h
  refine ⟨U, hU, hxU, hUΩ, c • f, hf.const_smul c,
    ⟨C * ‖c‖₊, (hC.smul c).congr fun y hy ↦ ?_⟩, fun φ hφ ↦ ?_⟩
  · exact (iteratedFDeriv_const_smul_apply (hf.contDiffAt (hU.mem_nhds hy))).symm
  · rw [smul_apply, hT φ hφ, ← integral_smul]
    congr 1 with y
    exact (smul_comm (φ y) c (f y)).symm

/-- A nonzero scalar multiple of `T` is `C^{k,α}` near `x` exactly when `T` is. -/
theorem isLocallyCkHolderAt_smul_iff {T : 𝓓'(Ω, F)} {c : 𝕜} (hc : c ≠ 0) :
    (c • T).IsLocallyCkHolderAt k α x ↔ T.IsLocallyCkHolderAt k α x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul c⁻¹, fun h ↦ h.smul c⟩

end SMul

/-- The negative of `T` is `C^{k,α}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyCkHolderAt_neg_iff {T : 𝓓'(Ω, F)} :
    (-T).IsLocallyCkHolderAt k α x ↔ T.IsLocallyCkHolderAt k α x := by
  rw [← neg_one_smul ℝ T, isLocallyCkHolderAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

/-- The sum of two distributions `C^{k,α}` near `x` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.add {S T : 𝓓'(Ω, F)} (hS : S.IsLocallyCkHolderAt k α x)
    (hT : T.IsLocallyCkHolderAt k α x) : (S + T).IsLocallyCkHolderAt k α x := by
  obtain ⟨U, hU, hxU, hUΩ, f, hf, ⟨C, hC⟩, hSf⟩ := hS
  obtain ⟨V, hV, hxV, -, g, hg, ⟨D, hD⟩, hTg⟩ := hT
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, inter_subset_left.trans hUΩ, f + g,
    (hf.mono inter_subset_left).add (hg.mono inter_subset_right),
    ⟨C + D, ((hC.mono inter_subset_left).add (hD.mono inter_subset_right)).congr fun y hy ↦ ?_⟩,
    fun φ hφ ↦ ?_⟩
  · exact (iteratedFDeriv_add_apply (hf.contDiffAt (hU.mem_nhds hy.1))
      (hg.contDiffAt (hV.mem_nhds hy.2))).symm
  have hφU := hφ.trans inter_subset_left
  have hφV := hφ.trans inter_subset_right
  have hfU := hf.continuousOn.locallyIntegrableOn (μ := volume) hU.measurableSet
  have hgV := hg.continuousOn.locallyIntegrableOn (μ := volume) hV.measurableSet
  rw [add_apply, hSf φ hφU, hTg φ hφV, ← integral_add
    (hfU.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport hφU)
    (hgV.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport hφV)]
  simp [smul_add]

/-- The difference of two distributions `C^{k,α}` near `x` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.sub {S T : 𝓓'(Ω, F)} (hS : S.IsLocallyCkHolderAt k α x)
    (hT : T.IsLocallyCkHolderAt k α x) : (S - T).IsLocallyCkHolderAt k α x := by
  rw [sub_eq_add_neg]
  exact hS.add (isLocallyCkHolderAt_neg_iff.2 hT)

/-- **Monotonicity in the exponent.** A distribution `C^{k,α}` near `x` is `C^{k,α'}` near `x`
for `α' ≤ α`. -/
theorem IsLocallyCkHolderAt.mono_exponent {T : 𝓓'(Ω, F)} (h : T.IsLocallyCkHolderAt k α x)
    {α' : ℝ≥0} (hα : α' ≤ α) : T.IsLocallyCkHolderAt k α' x := by
  obtain ⟨U, hU, hxU, hUΩ, f, hf, ⟨C, hC⟩, hT⟩ := h
  refine ⟨U ∩ ball x 1, hU.inter isOpen_ball, ⟨hxU, mem_ball_self one_pos⟩,
    inter_subset_left.trans hUΩ, f, hf.mono inter_subset_left,
    HolderOnWith.exists_holderOnWith_of_le ⟨C, hC.mono inter_subset_left⟩ hα
      (isBounded_ball.subset inter_subset_right), fun φ hφ ↦ hT φ (hφ.trans inter_subset_left)⟩

/-- A distribution that is `C^{k + 1}` on a neighbourhood `U` of `x` is `C^{k,α}` near `x` for
every `α ≤ 1`. -/
theorem isLocallyCkHolderAt_of_contDiffOn {T : 𝓓'(Ω, F)} {U : Set E} (hU : IsOpen U)
    (hxU : x ∈ U) (hUΩ : U ⊆ Ω) {f : E → F} (hf : ContDiffOn ℝ (k + 1 : ℕ) f U)
    (hT : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y) (hα : α ≤ 1) :
    T.IsLocallyCkHolderAt k α x := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hxU
  have hsub : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hball : ball x (r / 2) ⊆ U := ball_subset_closedBall.trans hsub
  obtain ⟨C, hC⟩ := hf.exists_holderOnWith_iteratedFDeriv hU hα (isCompact_closedBall x (r / 2))
    hsub
  exact ⟨ball x (r / 2), isOpen_ball, mem_ball_self (by positivity), hball.trans hUΩ, f,
    (hf.mono hball).of_le (by exact_mod_cast k.le_succ), ⟨C, hC.mono ball_subset_closedBall⟩,
    fun φ hφ ↦ hT φ (hφ.trans hball)⟩

/-- A distribution `C^{k,α}` near `x` is `C^{k',α'}` near `x` for `k' < k` and every `α' ≤ 1`. -/
theorem IsLocallyCkHolderAt.of_lt {T : 𝓓'(Ω, F)} (h : T.IsLocallyCkHolderAt k α x) {k' : ℕ}
    (hk : k' < k) {α' : ℝ≥0} (hα' : α' ≤ 1) : T.IsLocallyCkHolderAt k' α' x :=
  let ⟨_, hU, hxU, hUΩ, _, hf, _, hT⟩ := h
  isLocallyCkHolderAt_of_contDiffOn hU hxU hUΩ (hf.of_le (by exact_mod_cast hk)) hT hα'

/-- **Monotonicity.** A distribution `C^{k,α}` near `x` is `C^{k',α'}` near `x` for `k' ≤ k`,
`α' ≤ α` and `α' ≤ 1`. -/
theorem IsLocallyCkHolderAt.mono {T : 𝓓'(Ω, F)} (h : T.IsLocallyCkHolderAt k α x) {k' : ℕ}
    (hk : k' ≤ k) {α' : ℝ≥0} (hα : α' ≤ α) (hα' : α' ≤ 1) : T.IsLocallyCkHolderAt k' α' x := by
  rcases hk.eq_or_lt with rfl | hk
  exacts [h.mono_exponent hα, h.of_lt hk hα']

/-- **A distribution smooth near `x` is `C^{k,α}` near `x`**, for every `k` and every
`α ≤ 1`. -/
theorem isLocallyCkHolderAt_of_notMem_singularSupport {T : 𝓓'(Ω, F)} (hx : x ∈ Ω)
    (hT : x ∉ T.singularSupport) (k : ℕ) (hα : α ≤ 1) : T.IsLocallyCkHolderAt k α x := by
  obtain ⟨U, hU, hxU, f, hf, hTf⟩ := (notMem_singularSupport_iff hx).1 hT
  exact isLocallyCkHolderAt_of_contDiffOn (hU.inter Ω.isOpen) ⟨hxU, hx⟩ inter_subset_right
    ((hf.of_le (by exact_mod_cast le_top)).mono inter_subset_left)
    (fun φ hφ ↦ hTf φ (hφ.trans inter_subset_left)) hα

/-! ### Comparison with the Hölder–Zygmund scale -/

section Besov

open TauCeti BoundedContinuousFunction

variable {T : 𝓓'(Ω, ℂ)} (φ : ContDiffBump (0 : E))

/-- **A distribution in `𝒞^{k+α}` near `x` is `C^{k,α}` near `x`**, for `k : ℕ` and
`0 < α < 1`. -/
theorem IsLocallyMemBesovAt.isLocallyCkHolderAt (hα0 : 0 < α) (hα1 : α < 1)
    (h : T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x) : T.IsLocallyCkHolderAt k α x := by
  obtain ⟨χ, hχ, hB⟩ := isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.1 h
  -- `χ T` is the tempered distribution of a bounded `C^{k,α}` function `g`.
  set g := BesovSpace.toCkHolderSpace ℂ φ k hα0 hα1 hB.toBesovSpace
  have hg (ψ : 𝓢(E, ℂ)) : T.cutoffTempered χ ψ = ∫ y, ψ y • g y := by
    rw [← MemBesov.toDistr_toBesovSpace hB, ← BesovSpace.toLpTop_toCkHolderSpace φ k hα0 hα1,
      toTemperedDistribution_toLpTop_apply, CkHolderSpace.coe_toBoundedContinuousFunction]
  have hxΩ : x ∈ Ω := χ.tsupport_subset (subset_tsupport _ (by simp [hχ.self_of_nhds]))
  exact ⟨interior {y | χ y = 1} ∩ Ω, isOpen_interior.inter Ω.isOpen,
    ⟨mem_interior_iff_mem_nhds.2 hχ, hxΩ⟩, inter_subset_right, g, g.contDiff.contDiffOn,
    ⟨_, g.memHolder_iteratedFDeriv.holderWith.holderOnWith _⟩, fun ψ hψ ↦
      T.apply_eq_integral_of_cutoffTempered_apply_eq_integral hg
        (V := interior {y | χ y = 1} ∩ Ω) (fun y hy ↦ interior_subset hy.1) hψ⟩

/-- **A distribution `C^{k,α}` near `x` is in `𝒞^{k+α}` near `x`**, for `k : ℕ` and
`α ≤ 1`. -/
theorem IsLocallyCkHolderAt.isLocallyMemBesovAt (hα : α ≤ 1) (h : T.IsLocallyCkHolderAt k α x) :
    T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x := by
  obtain ⟨U, hU, hxU, hUΩ, f, hf, ⟨C, hC⟩, hT⟩ := h
  -- A ball `s` around `x` whose closure lies in `U`, and a cutoff `χ` equal to one near `x`.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hxU
  set s := ball x (r / 2)
  have hsub : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hsU : s ⊆ U := ball_subset_closedBall.trans hsub
  obtain ⟨M, hM0, hM⟩ := hf.exists_nonneg_bound_iteratedFDeriv_of_isOpen hU
    (isCompact_closedBall x (r / 2)) hsub
  obtain ⟨χ, -, hχ1, hχs⟩ := TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    isCompact_singleton isOpen_ball (singleton_subset_iff.2 (mem_ball_self (by positivity)))
    (hsU.trans hUΩ)
  obtain ⟨N, hN0, hN⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv_of_contDiff (n := k + 1)
    (χ.contDiff.of_le (by exact_mod_cast le_top))
  -- `χ f` is a bounded `C^{k,α}` function on `E`, and it is the tempered distribution `χ T`.
  set g := CkHolderSpace.cutoff (M := ⟨M, hM0⟩) (N := ⟨N, hN0⟩) (hf.mono hsU)
    (χ.contDiff.of_le (by exact_mod_cast le_top)) isOpen_ball (convex_ball x (r / 2)) hχs hα
    (fun i hi y hy ↦ hM i hi y (ball_subset_closedBall hy)) (fun i hi y ↦ hN i hi y)
    (hC.mono hsU)
  have hχT : T.cutoffTempered (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM χ) =
      (toLpTop volume ℂ g.toBoundedContinuousFunction : 𝓢'(E, ℂ)) :=
    cutoffTempered_eq_of_apply_eq_integral hT (hχs.trans hsU) fun ψ ↦ by
      rw [toTemperedDistribution_toLpTop_apply]
      congr 1 with y
      rw [CkHolderSpace.coe_toBoundedContinuousFunction]
      exact congrArg (ψ y • ·) (CkHolderSpace.cutoff_apply ..)
  refine isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.2
    ⟨TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM χ, ?_, ?_⟩
  · rw [nhdsSet_singleton] at hχ1
    filter_upwards [hχ1] with y hy
    simp [hy]
  · rw [hχT, ← BesovSpace.toDistr_ofCkHolderSpace φ k g]
    exact (BesovSpace.ofCkHolderSpace ℂ φ k α g).memBesov_toDistr

/-- **Local Hölder–Zygmund regularity is local Hölder regularity.** For `k : ℕ` and
`0 < α < 1`, a complex distribution `T` lies in the Hölder–Zygmund space `𝒞^{k+α} = B^{k+α}_{∞,∞}`
near `x` exactly when it is a `C^{k,α}` function near `x`. -/
theorem isLocallyMemBesovAt_iff_isLocallyCkHolderAt (hα0 : 0 < α) (hα1 : α < 1) :
    T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x ↔ T.IsLocallyCkHolderAt k α x :=
  ⟨IsLocallyMemBesovAt.isLocallyCkHolderAt φ hα0 hα1,
    IsLocallyCkHolderAt.isLocallyMemBesovAt φ hα1.le⟩

end Besov

end Distribution
