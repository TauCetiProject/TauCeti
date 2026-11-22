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
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Holder.JetBounds
import TauCeti.Analysis.Holder.Localization

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
`α ≤ 1` (`Distribution.isLocallyCkHolderAt_of_notMem_singularSupport`).

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
(`Distribution.isVanishingOn_sub_toDistribution_cutoffTempered`). Conversely, if `T` is the
function `f` on a ball around `x` on which `f` is `C^{k,α}`, then for a test function `χ` equal to
one near `x` and supported in a smaller ball, the product `χ f` is a bounded `C^{k,α}` function on
all of `E` (`TauCeti.CkHolderSpace.cutoff`), so it lies in `𝒞^{k+α}`
(`TauCeti.BesovSpace.ofCkHolderSpace`), and it is the tempered distribution `χ T`.

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

/-- **A distribution smooth near `x` is `C^{k,α}` near `x`**, for every `k` and every `α ≤ 1`:
on a ball whose closure lies where `T` is a smooth function `f`, the derivatives of `f` of orders
`k` and `k + 1` are bounded, so the `k`-th derivative is Lipschitz, hence `α`-Hölder. -/
theorem isLocallyCkHolderAt_of_notMem_singularSupport {T : 𝓓'(Ω, F)} (hx : x ∈ Ω)
    (hT : x ∉ T.singularSupport) (k : ℕ) (hα : α ≤ 1) : T.IsLocallyCkHolderAt k α x := by
  obtain ⟨U, hU, hxU, f, hf, hTf⟩ := (notMem_singularSupport_iff hx).1 hT
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 (hU.inter Ω.isOpen) x ⟨hxU, hx⟩
  have hsub : closedBall x (r / 2) ⊆ U ∩ Ω :=
    (closedBall_subset_ball (by linarith)).trans hrU
  have hball : ball x (r / 2) ⊆ U ∩ Ω := ball_subset_closedBall.trans hsub
  have hf' : ContDiffOn ℝ (k + 1 : ℕ) f U := hf.of_le (by exact_mod_cast le_top)
  obtain ⟨M, hM0, hM⟩ := hf'.exists_nonneg_bound_iteratedFDeriv_of_isOpen hU
    (isCompact_closedBall x (r / 2)) (hsub.trans inter_subset_left)
  have hfb : ContDiffOn ℝ (k + 1 : ℕ) f (ball x (r / 2)) := hf'.mono (hball.trans inter_subset_left)
  refine ⟨ball x (r / 2), isOpen_ball, mem_ball_self (by positivity),
    hball.trans inter_subset_right, f, hfb.of_le (by exact_mod_cast k.le_succ),
    ⟨⟨M, hM0⟩ + 2 * ⟨M, hM0⟩, ?_⟩, fun φ hφ ↦ hTf φ (hφ.trans (hball.trans inter_subset_left))⟩
  exact hfb.holderOnWith_iteratedFDeriv_of_lt isOpen_ball (convex_ball x (r / 2)) k.lt_succ_self
    hα (fun y hy ↦ hM k k.le_succ y (ball_subset_closedBall hy))
    (fun y hy ↦ hM (k + 1) le_rfl y (ball_subset_closedBall hy))

/-! ### Comparison with the Hölder–Zygmund scale -/

section Besov

open TauCeti BoundedContinuousFunction

variable {T : 𝓓'(Ω, ℂ)} (φ : ContDiffBump (0 : E))

/-- If `χ T` is the tempered distribution of a bounded continuous function `g` and `χ = 1` on
`V`, then `T` is the function `g` on the test functions supported in `V`. -/
private theorem apply_eq_integral_of_cutoffTempered_eq {χ : 𝓓(Ω, ℂ)} {g : E →ᵇ ℂ}
    (hg : (toLpTop volume ℂ g : 𝓢'(E, ℂ)) = T.cutoffTempered χ) {V : Set E}
    (hχ : ∀ y ∈ V, χ y = 1) {ψ : 𝓓(Ω, ℝ)} (hψ : tsupport ψ ⊆ V) :
    T ψ = ∫ y, ψ y • g y := by
  have h := isVanishingOn_sub_toDistribution_cutoffTempered T hχ ψ hψ
  rw [sub_apply, sub_eq_zero, toDistribution_apply, ← hg, Lp.toTemperedDistribution_apply] at h
  rw [h]
  refine integral_congr_ae ((coeFn_toLpTop volume (𝕜 := ℂ) g).mono fun y hy ↦ ?_)
  simp [hy, TestFunction.toSchwartzMapCLM_apply, Complex.real_smul]

/-- If `T` is the function `f` on the test functions supported in `U`, and `χ` is a real test
function supported in `U`, then `χ T` is the tempered distribution of the function `χ f`, given
as a bounded continuous function `g`. -/
private theorem cutoffTempered_eq_of_apply_eq_integral {U : Set E} {f : E → ℂ}
    (hT : ∀ ψ : 𝓓(Ω, ℝ), tsupport ψ ⊆ U → T ψ = ∫ y, ψ y • f y) {χ : 𝓓(Ω, ℝ)}
    (hχU : tsupport χ ⊆ U) {g : E →ᵇ ℂ} (hg : ∀ y, g y = χ y • f y) :
    T.cutoffTempered (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM χ) =
      (toLpTop volume ℂ g : 𝓢'(E, ℂ)) := by
  refine (eq_cutoffTempered_of_forall T _ fun ψ ρ _ hρ ↦ ?_).symm
  -- The complex test function `ρ = χ ψ` is real, so `T` pairs with it through its real part.
  have hre : TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM ρ) = ρ := by
    ext y
    simp [hρ]
  have hρU : tsupport (TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM ρ) ⊆ U := by
    have h : ⇑(TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM ρ) = fun y ↦ χ y * ψ y := by
      ext y
      simp [hρ]
    rw [h]
    exact (tsupport_mul_subset_left).trans hχU
  rw [← hre, complexPairing_postcompCLM_ofRealCLM,
    hT _ hρU, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ((coeFn_toLpTop volume (𝕜 := ℂ) g).mono fun y hy ↦ ?_)
  simp only [hy, hg, SchwartzMap.postcompCLM_apply, Function.comp_apply, Complex.ofRealCLM_apply,
    TestFunction.postcompCLM_apply, Complex.reCLM_apply, hρ, Complex.real_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  push_cast
  ring

/-- **A distribution in `𝒞^{k+α}` near `x` is `C^{k,α}` near `x`**, for `k : ℕ` and `0 < α < 1`:
where a cutoff `χ` equals one, `T` is the bounded `C^{k,α}` function representing `χ T`. -/
theorem IsLocallyMemBesovAt.isLocallyCkHolderAt (hα0 : 0 < α) (hα1 : α < 1)
    (h : T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x) : T.IsLocallyCkHolderAt k α x := by
  obtain ⟨χ, hχ, hB⟩ := isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.1 h
  -- `χ T` is the tempered distribution of a bounded `C^{k,α}` function `g`.
  set g := BesovSpace.toCkHolderSpace ℂ φ k hα0 hα1 hB.toBesovSpace
  have hg : (toLpTop volume ℂ g.toBoundedContinuousFunction : 𝓢'(E, ℂ)) =
      T.cutoffTempered χ := by
    rw [BesovSpace.toLpTop_toCkHolderSpace, MemBesov.toDistr_toBesovSpace]
  have hxΩ : x ∈ Ω := χ.tsupport_subset (subset_tsupport _ (by simp [hχ.self_of_nhds]))
  refine ⟨interior {y | χ y = 1} ∩ Ω, isOpen_interior.inter Ω.isOpen,
    ⟨mem_interior_iff_mem_nhds.2 hχ, hxΩ⟩, inter_subset_right, g, g.contDiff.contDiffOn,
    ⟨_, g.memHolder_iteratedFDeriv.holderWith.holderOnWith _⟩, fun ψ hψ ↦ ?_⟩
  rw [apply_eq_integral_of_cutoffTempered_eq hg (V := interior {y | χ y = 1} ∩ Ω)
    (fun y hy ↦ interior_subset hy.1) hψ]
  simp

/-- **A distribution `C^{k,α}` near `x` is in `𝒞^{k+α}` near `x`**, for `k : ℕ` and `α ≤ 1`: for
a cutoff `χ` equal to one near `x` and supported in a ball on which `T` is a `C^{k,α}` function
`f`, the tempered distribution `χ T` is the bounded `C^{k,α}` function `χ f`. -/
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
  -- The derivatives of `χ` through order `k + 1` are bounded by its Schwartz seminorms.
  set N : ℝ := ∑ i ∈ Finset.range (k + 2),
    SchwartzMap.seminorm ℝ 0 i (TestFunction.toSchwartzMapCLM ℝ χ)
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
  have hN (i : ℕ) (hi : i ≤ k + 1) (y : E) : ‖iteratedFDeriv ℝ i χ y‖ ≤ N := by
    have h := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
      (TestFunction.toSchwartzMapCLM ℝ χ) i y
    rw [TestFunction.coe_toSchwartzMapCLM] at h
    exact h.trans (Finset.single_le_sum (f := fun j ↦
      SchwartzMap.seminorm ℝ 0 j (TestFunction.toSchwartzMapCLM ℝ χ))
      (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_range.2 (by omega)))
  -- `χ f` is a bounded `C^{k,α}` function on `E`, and it is the tempered distribution `χ T`.
  set g := CkHolderSpace.cutoff (M := ⟨M, hM0⟩) (N := ⟨N, hN0⟩) (hf.mono hsU)
    (χ.contDiff.of_le (by exact_mod_cast le_top)) isOpen_ball (convex_ball x (r / 2)) hχs hα
    (fun i hi y hy ↦ hM i hi y (ball_subset_closedBall hy)) hN (hC.mono hsU)
  have hχT : T.cutoffTempered (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM χ) =
      (toLpTop volume ℂ g.toBoundedContinuousFunction : 𝓢'(E, ℂ)) :=
    cutoffTempered_eq_of_apply_eq_integral hT (hχs.trans hsU) fun y ↦ by
      rw [CkHolderSpace.coe_toBoundedContinuousFunction]
      exact CkHolderSpace.cutoff_apply ..
  refine isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.2
    ⟨_, ?_, hχT ▸ BesovSpace.toDistr_ofCkHolderSpace φ k g ▸
      (BesovSpace.ofCkHolderSpace ℂ φ k α g).memBesov_toDistr⟩
  rw [nhdsSet_singleton] at hχ1
  filter_upwards [hχ1] with y hy
  simp [hy]

/-- **Local Hölder–Zygmund regularity is local Hölder regularity.** For `k : ℕ` and
`0 < α < 1`, a complex distribution `T` lies in the Hölder–Zygmund space `𝒞^{k+α} = B^{k+α}_{∞,∞}`
near `x` exactly when it is a `C^{k,α}` function near `x`. -/
theorem isLocallyMemBesovAt_iff_isLocallyCkHolderAt (hα0 : 0 < α) (hα1 : α < 1) :
    T.IsLocallyMemBesovAt φ (k + α) ∞ ∞ x ↔ T.IsLocallyCkHolderAt k α x :=
  ⟨IsLocallyMemBesovAt.isLocallyCkHolderAt φ hα0 hα1,
    IsLocallyCkHolderAt.isLocallyMemBesovAt φ hα1.le⟩

end Besov

end Distribution
