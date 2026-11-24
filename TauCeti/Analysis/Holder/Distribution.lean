/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local
public import TauCeti.Analysis.Holder.Zygmund
import TauCeti.Analysis.Distribution.ComplexPairing
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
import TauCeti.Analysis.Holder.CompLinear
import TauCeti.Analysis.Holder.Inclusion
import TauCeti.Analysis.Holder.Localization

/-!
# Distributions that are `C^{k,α}` near a point

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. This file says when `T` is a `C^{k,α}` function near a point `x`
(`Distribution.IsLocallyCkHolderAt k α T x`): on a neighbourhood `U ⊆ Ω` of `x`, `T` is
integration against a bounded `C^k` function `f` whose derivatives through order `k` are bounded
and whose `k`-th derivative is globally `α`-Hölder (an element of `TauCeti.CkHolderSpace k α E ℂ`),
that is `T ψ = ∫ ψ • f` for every real test function `ψ` supported in `U`. Only the values of `f`
on `U` enter, and for `α ≤ 1` the global bounds on `f` are no restriction: a function that is `C^k`
on an open convex neighbourhood `s ⊆ Ω` of `x`, with bounded derivatives and `α`-Hölder `k`-th
derivative there, agrees near `x` with such an `f`
(`Distribution.IsLocallyCkHolderAt.of_contDiffOn`, by a cutoff). This is the form of regularity
in which the Schauder estimates conclude: an elliptic operator of order `m` whose image `P T` is
`C^{k,α}` near `x` forces `T` to be `C^{k + m,α}` near `x`.

For `0 < α < 1` the notion is local membership in the Hölder–Zygmund space
`𝒞^{k+α} = B^{k+α}_{∞,∞}`: `T` is `C^{k,α}` near `x` exactly when it is `B^{k+α}_{∞,∞}` near `x`
(`Distribution.isLocallyMemBesovAt_iff_isLocallyCkHolderAt`). This is the local form of the
identification `𝒞^{k+α} ≃ C_b^{k,α}` (`TauCeti.BesovSpace.ckHolderSpaceEquiv`), and it turns local
regularity theorems on the Besov scale into local Schauder theorems.

The argument for the identification:

* if `χ T ∈ 𝒞^{k+α}` for a test function `χ` equal to one near `x`, then `χ T` is the tempered
  distribution of some `f ∈ C_b^{k,α}` (`TauCeti.BesovSpace.toCkHolderSpace`), and `T` agrees with
  `χ T`, hence with `f`, where `χ = 1`;
* conversely, if `T` agrees with `f ∈ C_b^{k,α}` on `U`, then for a test function `χ` supported in
  `U` and equal to one near `x`, `χ T = χ f` lies in `𝒞^{k+α}`, since `f` does
  (`TauCeti.BesovSpace.ofCkHolderSpace`) and smooth multipliers preserve the Besov spaces
  (`TemperedDistribution.MemBesov.smulLeftCLM`).

## Main declarations

* `Distribution.IsLocallyCkHolderAt`: `T` is a `C^{k,α}` function near `x`, with
  `Distribution.isLocallyCkHolderAt_iff`, `Distribution.IsLocallyCkHolderAt.mem` and
  `Distribution.isOpen_setOf_isLocallyCkHolderAt`; every bounded `C^{k,α}` function is one
  (`Distribution.isLocallyCkHolderAt_ofFun`), and for `α ≤ 1` it suffices that `T` is a `C^{k,α}`
  function on an open convex neighbourhood `s ⊆ Ω` of `x`
  (`Distribution.IsLocallyCkHolderAt.of_contDiffOn`). The notion is
  stable under the linear operations (`Distribution.isLocallyCkHolderAt_zero_iff`,
  `Distribution.IsLocallyCkHolderAt.smul`, `Distribution.IsLocallyCkHolderAt.add`,
  `Distribution.IsLocallyCkHolderAt.sub`), smooth multipliers for `α ≤ 1`
  (`Distribution.IsLocallyCkHolderAt.smulLeftCLM`) and lowering the regularity
  (`Distribution.IsLocallyCkHolderAt.mono_exponent`, and `Distribution.IsLocallyCkHolderAt.mono`
  for a target exponent `β ≤ 1`).
* `Distribution.isLocallyMemBesovAt_iff_isLocallyCkHolderAt`: for `0 < α < 1`, being `C^{k,α}`
  near `x` is being `B^{k+α}_{∞,∞}` near `x`. The direction
  `Distribution.IsLocallyCkHolderAt.isLocallyMemBesovAt` holds for every `α`, and
  `Distribution.IsLocallyMemBesovAt.isLocallyCkHolderAt` is the converse.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.32)–(3.34) (the Zygmund spaces and the Hölder spaces).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.5.7.
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace TemperedDistribution BoundedContinuousFunction
open TauCeti Complex
open scoped ENNReal NNReal Topology SchwartzMap Distributions ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- A complex distribution `T` on `Ω` is **`C^{k,α}` near `x`** if `x` has a neighbourhood
`U ⊆ Ω` on which `T` is integration against a bounded `C^k` function `f` with bounded derivatives
through order `k` and `α`-Hölder `k`-th derivative: `T ψ = ∫ ψ • f` for every real test function
`ψ` supported in `U`. Only the values of `f` on `U` enter. -/
def IsLocallyCkHolderAt (k : ℕ) (α : ℝ≥0) (T : 𝓓'(Ω, ℂ)) (x : E) : Prop :=
  ∃ U ∈ 𝓝 x, U ⊆ Ω ∧ ∃ f : CkHolderSpace k α E ℂ,
    ∀ ψ : 𝓓(Ω, ℝ), tsupport ψ ⊆ U → T ψ = ∫ y, ψ y • f y

variable {k : ℕ} {α : ℝ≥0} {T : 𝓓'(Ω, ℂ)} {x : E}

/-- Unfolds `IsLocallyCkHolderAt` into its neighbourhood and the function representing `T`
there. -/
theorem isLocallyCkHolderAt_iff : T.IsLocallyCkHolderAt k α x ↔
    ∃ U ∈ 𝓝 x, U ⊆ Ω ∧ ∃ f : CkHolderSpace k α E ℂ,
      ∀ ψ : 𝓓(Ω, ℝ), tsupport ψ ⊆ U → T ψ = ∫ y, ψ y • f y :=
  Iff.rfl

/-- A distribution can only be `C^{k,α}` near points of its domain. -/
theorem IsLocallyCkHolderAt.mem (h : T.IsLocallyCkHolderAt k α x) : x ∈ Ω :=
  let ⟨_, hU, hUΩ, _⟩ := h
  hUΩ (mem_of_mem_nhds hU)

variable (k α) in
/-- The set of points near which a distribution is `C^{k,α}` is open. -/
theorem isOpen_setOf_isLocallyCkHolderAt (T : 𝓓'(Ω, ℂ)) :
    IsOpen {x : E | T.IsLocallyCkHolderAt k α x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨U, hU, hUΩ, hT⟩ ↦ ?_
  filter_upwards [eventually_mem_nhds_iff.2 hU] with y hy using ⟨U, hy, hUΩ, hT⟩

/-- A bounded `C^{k,α}` function, as a distribution on `Ω`, is `C^{k,α}` near every point of
`Ω`. -/
theorem isLocallyCkHolderAt_ofFun (f : CkHolderSpace k α E ℂ) (hx : x ∈ Ω) :
    (ofFun Ω f volume ⊤).IsLocallyCkHolderAt k α x :=
  ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, f, fun _ _ ↦
    ofFun_apply (f.contDiff.continuous.locallyIntegrable.locallyIntegrableOn _)⟩

/-- The zero distribution is `C^{k,α}` near every point of its domain. -/
@[simp]
theorem isLocallyCkHolderAt_zero_iff : (0 : 𝓓'(Ω, ℂ)).IsLocallyCkHolderAt k α x ↔ x ∈ Ω :=
  ⟨IsLocallyCkHolderAt.mem, fun hx ↦ ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, 0, fun ψ _ ↦ by simp⟩⟩

/-- A scalar multiple of a distribution `C^{k,α}` near `x` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.smul (h : T.IsLocallyCkHolderAt k α x) (c : ℂ) :
    (c • T).IsLocallyCkHolderAt k α x :=
  let ⟨U, hU, hUΩ, f, hT⟩ := h
  ⟨U, hU, hUΩ, CkHolderSpace.compLeftL (ContinuousLinearMap.mul ℝ ℂ c) f, fun ψ hψ ↦ by
    rw [smul_apply, hT ψ hψ, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp [Complex.real_smul, mul_left_comm]⟩

/-- A nonzero scalar multiple of `T` is `C^{k,α}` near `x` exactly when `T` is. -/
theorem isLocallyCkHolderAt_smul_iff {c : ℂ} (hc : c ≠ 0) :
    (c • T).IsLocallyCkHolderAt k α x ↔ T.IsLocallyCkHolderAt k α x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul c⁻¹, fun h ↦ h.smul c⟩

/-- The negative of `T` is `C^{k,α}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyCkHolderAt_neg_iff :
    (-T).IsLocallyCkHolderAt k α x ↔ T.IsLocallyCkHolderAt k α x := by
  rw [← neg_one_smul ℂ T, isLocallyCkHolderAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

/-- The sum of two distributions `C^{k,α}` near `x` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.add {S : 𝓓'(Ω, ℂ)} (hS : S.IsLocallyCkHolderAt k α x)
    (hT : T.IsLocallyCkHolderAt k α x) : (S + T).IsLocallyCkHolderAt k α x :=
  let ⟨U, hU, hUΩ, f, hSU⟩ := hS
  let ⟨V, hV, _, g, hTV⟩ := hT
  ⟨U ∩ V, inter_mem hU hV, inter_subset_left.trans hUΩ, f + g, fun ψ hψ ↦ by
    have hi (f : CkHolderSpace k α E ℂ) : Integrable fun y ↦ ψ y • f y :=
      (ψ.contDiff.continuous.smul f.contDiff.continuous).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.smul_right
    rw [add_apply, hSU ψ (hψ.trans inter_subset_left),
      hTV ψ (hψ.trans inter_subset_right), ← integral_add (hi f) (hi g)]
    simp [smul_add]⟩

/-- The difference of two distributions `C^{k,α}` near `x` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.sub {S : 𝓓'(Ω, ℂ)} (hS : S.IsLocallyCkHolderAt k α x)
    (hT : T.IsLocallyCkHolderAt k α x) : (S - T).IsLocallyCkHolderAt k α x := by
  rw [sub_eq_add_neg]
  exact hS.add (isLocallyCkHolderAt_neg_iff.2 hT)

/-- **Monotonicity in the exponent.** Being `C^{k,α}` near a point implies being `C^{k,β}` there
for `β ≤ α`. -/
theorem IsLocallyCkHolderAt.mono_exponent (h : T.IsLocallyCkHolderAt k α x) {β : ℝ≥0}
    (hβ : β ≤ α) : T.IsLocallyCkHolderAt k β x :=
  let ⟨U, hU, hUΩ, f, hT⟩ := h
  ⟨U, hU, hUΩ, CkHolderSpace.inclusionL hβ f, fun ψ hψ ↦ by simpa using hT ψ hψ⟩

/-- **Monotonicity.** Being `C^{k,α}` near a point implies being `C^{j,β}` there for `j ≤ k`,
`β ≤ α` and `β ≤ 1`. -/
theorem IsLocallyCkHolderAt.mono (h : T.IsLocallyCkHolderAt k α x) {j : ℕ} {β : ℝ≥0}
    (hj : j ≤ k) (hβ : β ≤ α) (hβ1 : β ≤ 1) : T.IsLocallyCkHolderAt j β x :=
  let ⟨U, hU, hUΩ, f, hT⟩ := h.mono_exponent hβ
  ⟨U, hU, hUΩ, CkHolderSpace.ofContDiff f (f.contDiff.of_le (by exact_mod_cast hj))
    (fun i hi ↦ ⟨‖f‖, f.norm_iteratedFDeriv_apply_le (hi.trans hj)⟩)
    (f.holderWith_iteratedFDeriv_of_le hβ1 hj).memHolder, fun ψ hψ ↦ by simpa using hT ψ hψ⟩

/-- **Local data suffice.** Let `s ⊆ Ω` be an open convex neighbourhood of `x` and `α ≤ 1`. If `T`
is integration on `s` against a function `f` that is `C^k` on `s`, with derivatives through order
`k` bounded on `s` and `α`-Hölder `k`-th derivative on `s`, then `T` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.of_contDiffOn {s : Set E} {f : E → ℂ} {M H : ℝ≥0} (hs : IsOpen s)
    (hc : Convex ℝ s) (hxs : x ∈ s) (hsΩ : s ⊆ Ω) (hα : α ≤ 1) (hf : ContDiffOn ℝ k f s)
    (hfb : ∀ i ≤ k, ∀ y ∈ s, ‖iteratedFDeriv ℝ i f y‖ ≤ M)
    (hfH : HolderOnWith H α (iteratedFDeriv ℝ k f) s)
    (hT : ∀ ψ : 𝓓(Ω, ℝ), tsupport ψ ⊆ s → T ψ = ∫ y, ψ y • f y) :
    T.IsLocallyCkHolderAt k α x := by
  -- A bump `χ` equal to one on `ball x (r / 4)` and supported in `s` turns `f` into
  -- `χ f ∈ C_b^{k,α}`, which agrees with `f` on `ball x (r / 4)`.
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.1 hs x hxs
  let χ : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχs : tsupport χ ⊆ s := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show r / 2 < r by linarith)).trans hrs
  obtain ⟨N, hN0, hN⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff (k + 1)
  have hχb (i : ℕ) (hi : i ≤ k + 1) (y : E) : ‖iteratedFDeriv ℝ i χ y‖ ≤ (⟨N, hN0⟩ : ℝ≥0) :=
    hN i hi y
  let g := CkHolderSpace.cutoff hf χ.contDiff hs hc hχs hα hfb hχb hfH
  have hg (y : E) : g y = χ y • f y :=
    CkHolderSpace.cutoff_apply hf χ.contDiff hs hc hχs hα hfb hχb hfH y
  refine ⟨Metric.ball x (r / 4), Metric.ball_mem_nhds x (by positivity),
    (Metric.ball_subset_ball (by linarith)).trans (hrs.trans hsΩ), g, fun ψ hψ ↦ ?_⟩
  rw [hT ψ (hψ.trans ((Metric.ball_subset_ball (by linarith)).trans hrs))]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [hg]
  by_cases hy : y ∈ tsupport ψ
  · simp [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hψ hy))]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- A smooth multiple `g T` of a distribution `C^{k,α}` near `x` is `C^{k,α}` near `x`, for
`α ≤ 1`. -/
theorem IsLocallyCkHolderAt.smulLeftCLM (h : T.IsLocallyCkHolderAt k α x) (hα : α ≤ 1)
    {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    (Distribution.smulLeftCLM hg T).IsLocallyCkHolderAt k α x := by
  obtain ⟨U, hU, hUΩ, f, hT⟩ := h
  -- For a bump `χ` equal to one on `ball x 1`, the compactly supported `χ g` agrees with `g`
  -- there, and `χ g • f ∈ C_b^{k,α}`.
  let χ : ContDiffBump x := ⟨1, 2, one_pos, one_lt_two⟩
  have hχg : ContDiff ℝ ∞ fun y ↦ χ y * g y := χ.contDiff.mul hg
  obtain ⟨N, hN0, hN⟩ := χ.hasCompactSupport.mul_right.exists_bound_iteratedFDeriv hχg (k + 1)
  let fg := CkHolderSpace.cutoff f.contDiff.contDiffOn (hχg.of_le (mod_cast le_top)) isOpen_univ
    convex_univ (subset_univ _) hα (M := ‖f‖₊) (fun i hi y _ ↦ f.norm_iteratedFDeriv_apply_le hi y)
    (N := ⟨N, hN0⟩) hN
    ((f.holderWith_iteratedFDeriv_of_le hα le_rfl).holderOnWith univ)
  refine ⟨U ∩ Metric.ball x 1, inter_mem hU (Metric.ball_mem_nhds x one_pos),
    inter_subset_left.trans hUΩ, fg, fun ψ hψ ↦ ?_⟩
  rw [smulLeftCLM_apply, hT _ ((TestFunction.tsupport_smulLeftCLM_subset_right hg ψ).trans
    (hψ.trans inter_subset_left))]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [show fg y = (χ y * g y) • f y from CkHolderSpace.cutoff_apply ..]
  by_cases hy : y ∈ tsupport ψ
  · simp only [TestFunction.smulLeftCLM_apply, smul_eq_mul, real_smul, ofReal_mul,
      χ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hψ hy).2), one_mul]
    ring
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Local Hölder–Zygmund regularity gives local Hölder regularity.** For `0 < α < 1`, a complex
distribution that is `B^{k+α}_{∞,∞}` near `x`, that is locally in the Hölder–Zygmund space
`𝒞^{k+α}`, is a `C^{k,α}` function near `x`. -/
theorem IsLocallyMemBesovAt.isLocallyCkHolderAt {φ : ContDiffBump (0 : E)} (hα0 : 0 < α)
    (hα1 : α < 1) (h : T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x) : T.IsLocallyCkHolderAt k α x := by
  -- `χ T ∈ 𝒞^{k+α}` is a `C^{k,α}` function `f`, and `T = χ T` where `χ = 1`.
  obtain ⟨χ, hχ, hχT⟩ := isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.1 h
  set f := BesovSpace.toCkHolderSpace ℂ φ k hα0 hα1 hχT.toBesovSpace
  have hf : (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, ℂ)) =
      T.cutoffTempered χ := by
    rw [BesovSpace.toLpTop_toCkHolderSpace, hχT.toDistr_toBesovSpace]
  refine ⟨{y | χ y = 1} ∩ Ω, inter_mem hχ (Ω.isOpen.mem_nhds h.mem), inter_subset_right, f,
    fun ψ hψ ↦ ?_⟩
  let ψS : 𝓢(E, ℂ) := HasCompactSupport.toSchwartzMap (f := fun y ↦ (ψ y : ℂ))
    (ψ.hasCompactSupport.comp_left ofReal_zero) (ofRealCLM.contDiff.comp ψ.contDiff)
  have hψS (y : E) : ψS y = ψ y := HasCompactSupport.toSchwartzMap_toFun _ _ y
  have hψχ (y : E) : TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM ψ y = χ y * ψS y := by
    by_cases hy : y ∈ tsupport ψ
    · simp [hψS, (hψ hy).1.out]
    · simp [hψS, image_eq_zero_of_notMem_tsupport hy]
  rw [← complexPairing_postcompCLM_ofRealCLM, ← cutoffTempered_apply T χ hψχ, ← hf,
    toTemperedDistribution_toLpTop_apply]
  simp [hψS, Complex.real_smul]

/-- **Local Hölder regularity gives local Hölder–Zygmund regularity.** A complex distribution that
is a `C^{k,α}` function near `x` is `B^{k+α}_{∞,∞}` near `x`, that is locally in the
Hölder–Zygmund space `𝒞^{k+α}`. -/
theorem IsLocallyCkHolderAt.isLocallyMemBesovAt (φ : ContDiffBump (0 : E))
    (h : T.IsLocallyCkHolderAt k α x) : T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x := by
  obtain ⟨U, hU, hUΩ, f, hT⟩ := h
  -- For `χ` supported in `U` and equal to one near `x`, `χ T = χ f ∈ 𝒞^{k+α}`.
  obtain ⟨χ, hχ1, hχU⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    isCompact_singleton isOpen_interior
    (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU)) (interior_subset.trans hUΩ)
  rw [nhdsSet_singleton] at hχ1
  set χS := TestFunction.toSchwartzMapCLM ℂ χ
  have hχS : (χS : E → ℂ) = χ := TestFunction.coe_toSchwartzMapCLM χ
  have heq : T.cutoffTempered χ = TemperedDistribution.smulLeftCLM ℂ (χS : E → ℂ)
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, ℂ)) := by
    ext g
    have hsupp : tsupport (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
        (g.smooth ⊤) χ) ⊆ U := by
      simp only [TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
      exact tsupport_mul_subset_left.trans (hχU.trans interior_subset)
    rw [smulLeftCLM_apply_apply, toTemperedDistribution_toLpTop_apply, cutoffTempered_def,
      complexPairing_eq_integral (f.contDiff.continuous.locallyIntegrable.locallyIntegrableOn U)
        hT hsupp]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth χS), hχS]
    simp only [TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', smul_eq_mul,
      CkHolderSpace.coe_toBoundedContinuousFunction]
  refine isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.2 ⟨χ, hχ1, heq ▸ ?_⟩
  exact (BesovSpace.toDistr_ofCkHolderSpace φ k f ▸
    (BesovSpace.ofCkHolderSpace ℂ φ k α f).memBesov_toDistr).smulLeftCLM
      (SchwartzMap.hasTemperateGrowth χS)
      fun n _ ↦ ⟨_, SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ _ n⟩

/-- **Local Hölder–Zygmund regularity is local Hölder regularity.** For `0 < α < 1`, a complex
distribution is `B^{k+α}_{∞,∞}` near `x`, that is locally in the Hölder–Zygmund space
`𝒞^{k+α}`, exactly when it is a `C^{k,α}` function near `x`. -/
theorem isLocallyMemBesovAt_iff_isLocallyCkHolderAt (φ : ContDiffBump (0 : E)) (hα0 : 0 < α)
    (hα1 : α < 1) : T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x ↔ T.IsLocallyCkHolderAt k α x :=
  ⟨IsLocallyMemBesovAt.isLocallyCkHolderAt hα0 hα1, IsLocallyCkHolderAt.isLocallyMemBesovAt φ⟩

end Distribution
