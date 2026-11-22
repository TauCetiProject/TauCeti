/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Distribution.Convolution
public import TauCeti.Analysis.PDE.FundamentalSolution.CutoffPotential
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
import TauCeti.Analysis.Distribution.LineDeriv
import TauCeti.Analysis.Distribution.LinearEquiv
import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.Convergence
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.InnerProductSpace.Harmonic.Real
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Multipole
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Multipole
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential

/-!
# Lax–Malgrange harmonic orthogonality

Let `E` be a finite-dimensional real inner product space, `Ω ⊆ E` an open set, `K ⊆ Ω` a compact
set that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`), `F` a real normed space, and `T : 𝓓'(Ω, F)` a
distribution with `dsupport T ⊆ K` that annihilates every test function agreeing near `K` with a
function harmonic on `Ω`.

For any symmetric locally integrable kernel `G : E → ℝ` that solves `-Δ (G ⋆ φ) = φ`, is harmonic
on `{0}ᶜ`, and admits exterior multipole approximation by globally harmonic functions, scalarizing
`T` with continuous linear functionals `ℓ : StrongDual ℝ F` reduces to `F = ℝ`:

* at every `x₀ ∉ Ω`, all iterated derivatives of `T.kernelPotentialOfSupport hG` vanish;
* outside a large ball, `T.kernelPotentialOfSupport hG` vanishes by exterior multipole
  approximation;
* unique continuation forces `T.kernelPotentialOfSupport hG` to vanish on `Kᶜ`, confining
  `dsupport (G ⋆ (χ T))` to `K`;
* testing `-Δ (G ⋆ (χ T)) = χ T` against a cutoff of any `h` harmonic near `K` shows that `T` also
  annihilates every test agreeing near `K` with `h`.

Combining this fundamental-solution argument in dimension `2` (via `TauCeti.planarNewtonianKernel`)
and dimensions `d ≥ 3` (via `TauCeti.newtonianKernel d`) with direct arguments in dimensions `0`
and `1` (`InnerProductSpace.exists_harmonicOnNhd_real_of_isFilledIn`) yields the dimension-free
Lax–Malgrange harmonic orthogonality theorem
`Distribution.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd`.

## Main declarations

* `Distribution.kernelPotentialOfSupport_eq_zero_of_isFilledIn`,
  `Distribution.dsupport_cutoffConvolutionCLM_subset_of_isFilledIn`,
  `Distribution.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_fundamentalSolution`: unique
  continuation, support confinement, and harmonic orthogonality for any real normed space `F`
  given a fundamental solution with exterior multipole approximation.
* `Distribution.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd`: dimension-free Lax–Malgrange
  harmonic orthogonality for every finite-dimensional real inner product space `E` and every real
  normed space `F`.

## References

* P. D. Lax, *A stability theorem for solutions of abstract differential equations, and its
  application to the study of the local behavior of solutions of elliptic equations*, Comm. Pure
  Appl. Math. **9** (1956), 747–766.
* B. Malgrange, *Existence et approximation des solutions des équations aux dérivées partielles et
  des équations de convolution*, Ann. Inst. Fourier **6** (1955–1956), 271–355.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, 2nd ed., §4.4.
-/

public section

noncomputable section

open Bornology ContinuousLinearMap Filter Function InnerProductSpace Laplacian
open LineDeriv MeasureTheory Metric Set TauCeti TopologicalSpace
open scoped ContDiff Convolution Distributions Pointwise Topology

namespace Distribution

section FilledIn

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- At any point `x₀ ∉ Ω`, if a scalar distribution `T` vanishes on tests agreeing near `K` with
functions harmonic on `Ω`, then `T.kernelPotentialOfSupport hG` vanishes on a neighbourhood of
`x₀`. -/
private theorem eventuallyEq_zero_kernelPotentialOfSupport_of_notMem
    {T : 𝓓'(Ω, ℝ)} {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hTK : dsupport T ⊆ K)
    {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x))
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {x₀ : E} (hx₀ : x₀ ∉ (Ω : Set E)) :
    T.kernelPotentialOfSupport hG =ᶠ[𝓝 x₀] 0 := by
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK hKΩ
  have hχT : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1 := hχ1.filter_mono (nhdsSet_mono hTK)
  have hx₀χ : x₀ ∉ tsupport (χ : E → ℝ) := fun h ↦ hx₀ (χ.tsupport_subset h)
  have hx₀T : x₀ ∉ dsupport T := fun h ↦ hx₀ (hKΩ (hTK h))
  have hcT : IsCompact (dsupport T) := hK.of_isClosed_subset isClosed_dsupport hTK
  have han : AnalyticAt ℝ (T.kernelPotentialOfSupport hG) x₀ :=
    (harmonicOnNhd_kernelPotentialOfSupport hcT (hTK.trans hKΩ) hG hG_symm x₀ hx₀T).analyticAt
  rw [han.eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero]
  intro k
  ext m
  have hcx : ContDiffAt ℝ k (T.kernelPotentialOfSupport hG) x₀ :=
    ((contDiffOn_kernelPotentialOfSupport hcT (hTK.trans hKΩ) hG hG_symm).contDiffAt
      (isClosed_dsupport.isOpen_compl.mem_nhds hx₀T)).of_le (by simp)
  rw [← hcx.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv le_rfl m]
  let H : E → ℝ := fun y ↦ iteratedFDerivAlong ℝ (List.ofFn m) G (x₀ - y)
  have hH : HarmonicOnNhd H {x₀}ᶜ := hG.iteratedFDerivAlong_sub_right (List.ofFn m) x₀
  let ψ : 𝓓(Ω, ℝ) := χ.smulOfContDiffOn isOpen_compl_singleton
    (subset_compl_singleton_iff.2 hx₀χ)
    (hH.analyticOnNhd.contDiffOn isOpen_compl_singleton.uniqueDiffOn)
  rw [iteratedFDerivAlong_kernelPotentialOfSupport T hχT hG hG_symm hx₀χ (List.ofFn m)
      (φ := ψ) (fun y ↦ by simp [ψ, H]), zero_apply]
  refine hT H ψ (hH.mono (subset_compl_singleton_iff.2 hx₀)) ?_
  filter_upwards [hχ1] with y hy
  simp [ψ, hy]

/-- Outside a sufficiently large ball, if `T` vanishes on tests agreeing near `K` with harmonic
functions on `Ω` and `G` admits exterior multipole approximation by globally harmonic functions,
then `T.kernelPotentialOfSupport hG` vanishes identically. -/
private theorem exists_radius_kernelPotentialOfSupport_eq_zero {T : 𝓓'(Ω, ℝ)} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hTK : dsupport T ⊆ K) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ)
    (hmp : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : E, x ≠ 0 →
      ∃ P : ℕ → E → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
        ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
          (iteratedFDeriv ℝ k fun y ↦ G (x - y)) atTop (closedBall 0 (c * ‖x‖)))
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0) :
    ∃ R > 0, ∀ x : E, R < ‖x‖ → T.kernelPotentialOfSupport hG x = 0 := by
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK hKΩ
  have hχT : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1 := hχ1.filter_mono (nhdsSet_mono hTK)
  obtain ⟨R₀, hR₀⟩ := χ.hasCompactSupport.isBounded.subset_closedBall 0
  set R₁ : ℝ := max R₀ 1
  have hR₁_pos : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hχR₁ : tsupport (χ : E → ℝ) ⊆ closedBall 0 R₁ :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨c, hc0, hc1, hmp⟩ := hmp
  refine ⟨(R₁ + 1) / c, div_pos (by linarith) hc0, fun x hx ↦ ?_⟩
  have hcx : R₁ + 1 < c * ‖x‖ := by
    rw [mul_comm]
    exact (div_lt_iff₀ hc0).1 hx
  have hnorm_pos : 0 < ‖x‖ := lt_trans (div_pos (by linarith) hc0) hx
  have hx0 : x ≠ 0 := norm_pos_iff.1 hnorm_pos
  have hx_gt : R₁ < ‖x‖ := by linarith [mul_lt_of_lt_one_left hnorm_pos hc1]
  have hxχ : x ∉ tsupport (χ : E → ℝ) :=
    fun h ↦ hx_gt.not_ge (mem_closedBall_zero_iff.1 (hχR₁ h))
  have hχx : tsupport (χ : E → ℝ) ⊆ {x}ᶜ := subset_compl_singleton_iff.2 hxχ
  obtain ⟨P, hPharm, hPlim⟩ := hmp x hx0
  have hPsmooth (N : ℕ) : ContDiffOn ℝ ∞ (P N) {x}ᶜ :=
    (((HarmonicOnNhd.analyticOnNhd (fun z _ ↦ hPharm N z : HarmonicOnNhd (P N) univ)).contDiffOn
      uniqueDiffOn_univ).mono (subset_univ _))
  have hχ_sub : tsupport (χ : E → ℝ) ⊆ closedBall 0 (c * ‖x‖) :=
    hχR₁.trans (closedBall_subset_closedBall (by linarith))
  have htend := TestFunction.tendsto_smulOfContDiffOn χ isOpen_compl_singleton hχx hPsmooth
    (hG.contDiffOn_sub_right x) fun k _ ↦ (hPlim k).mono hχ_sub
  have hT_lim := (T.continuous.tendsto _).comp htend
  have hzero (N : ℕ) :
      T (χ.smulOfContDiffOn isOpen_compl_singleton hχx (hPsmooth N)) = 0 := by
    refine hT (P N) _ (fun z _ ↦ hPharm N z) ?_
    filter_upwards [hχ1] with y hy
    simp [hy]
  rw [kernelPotentialOfSupport_eq_kernelPotentialPairing T hχT hG hxχ,
    kernelPotentialPairing_eq T hG hxχ
      (φ := χ.smulOfContDiffOn isOpen_compl_singleton hχx (hG.contDiffOn_sub_right x))
      (fun y ↦ by simp)]
  exact tendsto_nhds_unique (hT_lim.congr hzero) tendsto_const_nhds

private theorem kernelPotentialOfSupport_eq_zero_of_isFilledIn_real {T : 𝓓'(Ω, ℝ)} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x))
    (hmp : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : E, x ≠ 0 →
      ∃ P : ℕ → E → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
        ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
          (iteratedFDeriv ℝ k fun y ↦ G (x - y)) atTop (closedBall 0 (c * ‖x‖)))
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {x : E} (hx : x ∈ Kᶜ) :
    T.kernelPotentialOfSupport hG x = 0 := by
  have hcT : IsCompact (dsupport T) := hK.of_isClosed_subset isClosed_dsupport hTK
  have han : AnalyticOnNhd ℝ (T.kernelPotentialOfSupport hG) (connectedComponentIn Kᶜ x) :=
    ((harmonicOnNhd_kernelPotentialOfSupport hcT (hTK.trans hKΩ) hG hG_symm).analyticOnNhd).mono
      ((connectedComponentIn_subset Kᶜ x).trans (compl_subset_compl.2 hTK))
  by_cases hxH : x ∈ filledHull K
  · -- A bounded component of `Kᶜ` cannot stay inside `Ω` since `K` is filled in `Ω`.
    have hnot := (isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
      hK.isClosed Ω.isOpen hKΩ).1 hfill x ⟨hxH, hx⟩
    obtain ⟨x₀, hx₀C, hx₀Ω⟩ := not_subset.1 hnot
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
      hx₀C (eventuallyEq_zero_kernelPotentialOfSupport_of_notMem hK hKΩ hTK hG hG_symm hT hx₀Ω)
      (mem_connectedComponentIn hx)
  · -- An unbounded component of `Kᶜ` escapes every closed ball, reaching the multipole region.
    obtain ⟨R, _, hRzero⟩ := exists_radius_kernelPotentialOfSupport_eq_zero hK hKΩ hTK hG hmp hT
    have hunb : ¬IsBounded (connectedComponentIn Kᶜ x) := mt mem_filledHull_iff.2 hxH
    have hnot : ¬connectedComponentIn Kᶜ x ⊆ closedBall 0 R :=
      fun hsub ↦ hunb (isBounded_closedBall.subset hsub)
    obtain ⟨x₀, hx₀C, hx₀R⟩ := not_subset.1 hnot
    have hx₀_gt : R < ‖x₀‖ := not_le.1 (mt mem_closedBall_zero_iff.2 hx₀R)
    have hev : T.kernelPotentialOfSupport hG =ᶠ[𝓝 x₀] 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx₀_gt] with z hz
      exact hRzero z hz
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
      hx₀C hev (mem_connectedComponentIn hx)

/-- **Unique continuation for off-support kernel potentials on filled compact sets.** For any real
normed space `F`, if `T : 𝓓'(Ω, F)` has `dsupport T ⊆ K` for a compact set `K ⊆ Ω` filled in `Ω`,
`T` vanishes on every test agreeing near `K` with a function harmonic on `Ω`, and `G` is a
symmetric kernel harmonic on `{0}ᶜ` with exterior multipole approximation by globally harmonic
functions, then `T.kernelPotentialOfSupport hG` vanishes throughout `Kᶜ`. -/
theorem kernelPotentialOfSupport_eq_zero_of_isFilledIn {T : 𝓓'(Ω, F)} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x))
    (hmp : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : E, x ≠ 0 →
      ∃ P : ℕ → E → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
        ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
          (iteratedFDeriv ℝ k fun y ↦ G (x - y)) atTop (closedBall 0 (c * ‖x‖)))
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {x : E} (hx : x ∈ Kᶜ) :
    T.kernelPotentialOfSupport hG x = 0 := by
  have hcT : IsCompact (dsupport T) := hK.of_isClosed_subset isClosed_dsupport hTK
  have hxT : x ∉ dsupport T := fun hx' ↦ hx (hTK hx')
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  rw [← kernelPotentialOfSupport_mapCLM ℓ hcT (hTK.trans hKΩ) hG hxT]
  exact kernelPotentialOfSupport_eq_zero_of_isFilledIn_real hK hKΩ hfill
    ((dsupport_comp_subset T (map_zero ℓ)).trans hTK) hG hG_symm hmp
    (fun H ψ hH hψ ↦ by simp [hT H ψ hH hψ]) hx

/-- **Support confinement of the distributional kernel potential.** Under the hypotheses of
`kernelPotentialOfSupport_eq_zero_of_isFilledIn`, for any real normed space `F` and any cutoff `χ`
equal to `1` near `K`, `dsupport (G ⋆ (χ T)) ⊆ K`. -/
theorem dsupport_cutoffConvolutionCLM_subset_of_isFilledIn [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsLocallyFiniteMeasure μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {T : 𝓓'(Ω, F)} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ y in 𝓝ˢ K, χ y = 1) {G : E → ℝ}
    (hG_loc : LocallyIntegrable G μ) (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x))
    (hmp : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : E, x ≠ 0 →
      ∃ P : ℕ → E → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
        ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
          (iteratedFDeriv ℝ k fun y ↦ G (x - y)) atTop (closedBall 0 (c * ‖x‖)))
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0) :
    dsupport (cutoffConvolutionCLM (Ω' := ⊤) χ hG_loc T) ⊆ K := by
  rw [← disjoint_compl_left_iff_subset]
  refine IsVanishingOn.disjoint_dsupport (fun φ hφ ↦ ?_) hK.isClosed.isOpen_compl
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  have hsuppℓ : dsupport (mapCLM ℓ T) ⊆ K := (dsupport_comp_subset T (map_zero ℓ)).trans hTK
  have hχℓ : ∀ᶠ y in 𝓝ˢ (dsupport (mapCLM ℓ T)), χ y = 1 :=
    hχ.filter_mono (nhdsSet_mono hsuppℓ)
  have hdisj : Disjoint (tsupport (φ : E → ℝ)) (dsupport (mapCLM ℓ T)) :=
    Set.disjoint_left.2 fun z hz hzT ↦ hφ hz (hsuppℓ hzT)
  rw [← mapCLM_apply, mapCLM_cutoffConvolutionCLM,
    cutoffConvolutionCLM_apply_eq_integral_smul_kernelPotentialOfSupport hχℓ hG_loc hG hG_symm
      hdisj]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ tsupport (φ : E → ℝ)
  · simp [kernelPotentialOfSupport_eq_zero_of_isFilledIn_real hK hKΩ hfill hsuppℓ hG hG_symm hmp
      (fun H ψ hH hψ ↦ by simp [hT H ψ hH hψ]) (hφ hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Lax–Malgrange harmonic orthogonality from a fundamental solution.** For any real normed space
`F`, if `E` admits a symmetric locally integrable fundamental solution `G` of `-Δ` that is harmonic
away from `0` and has exterior multipole approximation by globally harmonic functions, then any
distribution `T : 𝓓'(Ω, F)` supported in a filled-in compact set `K ⊆ Ω` that annihilates tests
agreeing near `K` with global harmonic functions on `Ω` also annihilates every test agreeing near
`K` with a function harmonic near `K`. -/
theorem apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_fundamentalSolution [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ] [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] {T : 𝓓'(Ω, F)} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    {G : E → ℝ} (hG_loc : LocallyIntegrable G μ) (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x))
    (hG_lap : ∀ φ : 𝓓((⊤ : Opens E), ℝ), Δ (G ⋆[lsmul ℝ ℝ, μ] (φ : E → ℝ)) = -(φ : E → ℝ))
    (hmp : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : E, x ≠ 0 →
      ∃ P : ℕ → E → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
        ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
          (iteratedFDeriv ℝ k fun y ↦ G (x - y)) atTop (closedBall 0 (c * ‖x‖)))
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {h : E → ℝ} (hh : HarmonicOnNhd h K) {ψ : 𝓓(Ω, ℝ)} (hψ : (ψ : E → ℝ) =ᶠ[𝓝ˢ K] h) :
    T ψ = 0 := by
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK hKΩ
  let W := cutoffConvolutionCLM (Ω' := ⊤) χ hG_loc T
  have hWK : dsupport W ⊆ K :=
    dsupport_cutoffConvolutionCLM_subset_of_isFilledIn hK hKΩ hfill hTK hχ1 hG_loc hG hG_symm
      hmp hT
  -- Cut `h` off inside its open harmonic locus `{y | HarmonicAt h y}`.
  let U : Set E := {y | HarmonicAt h y}
  have hUo : IsOpen U := isOpen_setOfPred_harmonicAt (f := h)
  obtain ⟨η, -, hη1, hηU⟩ := TestFunction.exists_cutoff_tsupport_subset
    (Ω := (⊤ : Opens E)) (n := ⊤) hK hUo hh (subset_univ _)
  have hU_harm : HarmonicOnNhd h U := fun _ hy ↦ hy
  let θ : 𝓓((⊤ : Opens E), ℝ) :=
    η.smulOfContDiffOn hUo hηU (hU_harm.analyticOnNhd.contDiffOn hUo.uniqueDiffOn)
  have hθh : (θ : E → ℝ) =ᶠ[𝓝ˢ K] h := by
    filter_upwards [hη1] with y hy
    simp [θ, hy]
  -- Near `K ⊇ dsupport W`, `Δθ = Δh = 0`, so `W (Δθ) = 0`.
  let Δθ : 𝓓((⊤ : Opens E), ℝ) := laplacianCLM ℝ E _ θ
  have hΔ0 : (Δθ : E → ℝ) =ᶠ[𝓝ˢ (dsupport W)] (0 : 𝓓((⊤ : Opens E), ℝ)) := by
    refine Filter.EventuallyEq.filter_mono ?_ (nhdsSet_mono hWK)
    obtain ⟨V, hVo, hKV, hθV⟩ := mem_nhdsSet_iff_exists.1 hθh
    filter_upwards [(hVo.inter hUo).mem_nhdsSet.2 (subset_inter hKV hh)] with y ⟨hyV, hyU⟩
    have hev_y : (θ : E → ℝ) =ᶠ[𝓝 y] h :=
      Filter.eventuallyEq_iff_exists_mem.2 ⟨V, hVo.mem_nhds hyV, hθV⟩
    rw [TestFunction.laplacianCLM_apply, ((harmonicAt_congr_nhds hev_y.symm).1 hyU).2.self_of_nhds,
      FunLike.coe_zero, Pi.zero_apply]
  have hW0 : laplacianCLM ℝ E _ W θ = 0 := by
    rw [Distribution.laplacianCLM_apply_apply, Distribution.map_eq_map_of_eventuallyEq W hΔ0,
      map_zero]
  have hχθ0 : T (TestFunction.cutoffCLM χ.contDiff
      (inter_subset_left.trans χ.tsupport_subset) θ) = 0 := by
    have hpois := congrArg (fun D : 𝓓'((⊤ : Opens E), F) ↦ D θ)
      (laplacianCLM_cutoffConvolutionCLM χ hG_loc hG_lap T)
    rw [hW0, neg_apply, cutoffCLM_apply] at hpois
    exact neg_eq_zero.1 hpois.symm
  have hψ_eq : (ψ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)]
      TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) θ := by
    refine Filter.EventuallyEq.filter_mono ?_ (nhdsSet_mono hTK)
    filter_upwards [hψ, hχ1, hθh] with y hy₁ hy₂ hy₃
    simp [hy₁, hy₂, hy₃]
  rw [Distribution.map_eq_map_of_eventuallyEq T hψ_eq, hχθ0]

end FilledIn

section DimensionFree

/-- Transport scalar Lax–Malgrange orthogonality along a linear isometry equivalence. -/
private theorem apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_linearIsometryEquiv
    {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    (e : E ≃ₗᵢ[ℝ] E') {Ω : Opens E} {T : 𝓓'(Ω, ℝ)} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {h : E → ℝ} (hh : HarmonicOnNhd h K) {ψ : 𝓓(Ω, ℝ)} (hψ : (ψ : E → ℝ) =ᶠ[𝓝ˢ K] h)
    (hE' : ∀ {Ω' : Opens E'} {T' : 𝓓'(Ω', ℝ)} {K' : Set E'},
      IsCompact K' → K' ⊆ Ω' → IsFilledIn K' Ω' → dsupport T' ⊆ K' →
      (∀ (H' : E' → ℝ) (ψ' : 𝓓(Ω', ℝ)),
        HarmonicOnNhd H' Ω' → ((ψ' : E' → ℝ) =ᶠ[𝓝ˢ K'] H') → T' ψ' = 0) →
      ∀ {h' : E' → ℝ}, HarmonicOnNhd h' K' → ∀ {ψ' : 𝓓(Ω', ℝ)},
        ((ψ' : E' → ℝ) =ᶠ[𝓝ˢ K'] h') → T' ψ' = 0) :
    T ψ = 0 := by
  let Ω' : Opens E' := ⟨e '' (Ω : Set E), e.toHomeomorph.isOpenMap _ Ω.isOpen⟩
  let K' : Set E' := e '' K
  let e_cle : E' ≃L[ℝ] E := e.symm.toContinuousLinearEquiv
  have hmaps : MapsTo e_cle Ω' Ω := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [e_cle] using hx
  have hmaps_symm : MapsTo e_cle.symm Ω Ω' := fun x hx ↦ ⟨x, hx, rfl⟩
  let T' : 𝓓'(Ω', ℝ) := transportCLM e_cle hmaps T
  have hT'K' : dsupport T' ⊆ K' := by
    refine (dsupport_transportCLM_subset e_cle hmaps T).trans fun y hy ↦ ?_
    exact ⟨e.symm y, hTK hy, e.apply_symm_apply y⟩
  have hT' : ∀ (H' : E' → ℝ) (ψ' : 𝓓(Ω', ℝ)),
      HarmonicOnNhd H' Ω' → ((ψ' : E' → ℝ) =ᶠ[𝓝ˢ K'] H') → T' ψ' = 0 := by
    intro H' ψ' hH' hψ'
    rw [transportCLM_apply]
    refine hT (H' ∘ e) (e_cle.transportTestFunction hmaps ψ') ?_ ?_
    · intro x hx
      exact (harmonicAt_comp_linearIsometryEquiv_right_iff e).2 (hH' (e x) ⟨x, hx, rfl⟩)
    · have hcoe : ((e_cle.transportTestFunction hmaps ψ' : 𝓓(Ω, ℝ)) : E → ℝ) = ψ' ∘ e :=
        funext fun y ↦ by simp [e_cle]
      rw [hcoe]
      exact hψ'.comp_tendsto (e.continuous.tendsto_nhdsSet (mapsTo_image e K))
  have hh' : HarmonicOnNhd (h ∘ e.symm) K' := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using (harmonicAt_comp_linearIsometryEquiv_right_iff e.symm).2 (by simpa using hh x hx)
  let ψ' : 𝓓(Ω', ℝ) := e_cle.symm.transportTestFunction hmaps_symm ψ
  have hψ' : (ψ' : E' → ℝ) =ᶠ[𝓝ˢ K'] (h ∘ e.symm) := by
    have hcoe : (ψ' : E' → ℝ) = ψ ∘ e.symm := funext fun y ↦ by simp [ψ', e_cle]
    have hmaps_K : MapsTo e.symm K' K := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using hx
    rw [hcoe]
    exact hψ.comp_tendsto (e.symm.continuous.tendsto_nhdsSet hmaps_K)
  have hfill' : IsFilledIn K' Ω' := by
    convert e.toHomeomorph.isFilledIn_image.2 hfill
    · simp
    · exact Set.image_congr fun _ _ ↦ by simp
  have hzero : T' ψ' = 0 := hE' (hK.image e.continuous) (image_mono hKΩ)
    hfill' hT'K' hT' hh' hψ'
  rwa [transportCLM_apply, e_cle.transportTestFunction_transportTestFunction_symm] at hzero

/-- Scalar Lax–Malgrange harmonic orthogonality in every finite dimension. -/
private theorem apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_real
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Ω : Opens E} {T : 𝓓'(Ω, ℝ)} {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {h : E → ℝ} (hh : HarmonicOnNhd h K) {ψ : 𝓓(Ω, ℝ)} (hψ : (ψ : E → ℝ) =ᶠ[𝓝ˢ K] h) :
    T ψ = 0 := by
  match hd : Module.finrank ℝ E with
  | 0 =>
    have : Subsingleton E := Module.finrank_zero_iff.1 hd
    rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · rw [Distribution.eq_zero_of_dsupport_subset_empty hTK, zero_apply]
    · have hKu : K = univ := eq_univ_of_forall fun x ↦ Subsingleton.elim x x₀ ▸ hx₀
      have hΩu : (Ω : Set E) = univ := univ_subset_iff.1 (hKu ▸ hKΩ)
      exact hT h ψ (by rwa [hΩu, ← hKu]) hψ
  | 1 =>
    let e : E ≃ₗᵢ[ℝ] ℝ :=
      ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr.trans
        (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    exact apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_linearIsometryEquiv e hK hKΩ hfill hTK
      hT hh hψ fun {Ω' T' K'} _ hK'Ω' hfill' _ hT' {h'} hh' {ψ'} hψ' ↦ by
        obtain ⟨H', hH', hH'eq⟩ :=
          exists_harmonicOnNhd_real_of_isFilledIn Ω'.isOpen hK'Ω' hfill' hh'
        exact hT' H' ψ' hH' (hψ'.trans hH'eq.symm)
  | 2 =>
    let e : E ≃ₗᵢ[ℝ] ℂ :=
      ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr.trans
        Complex.orthonormalBasisOneI.repr.symm
    exact apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_linearIsometryEquiv e hK hKΩ hfill hTK
      hT hh hψ fun {Ω' T' K'} hK' hK'Ω' hfill' hT'K' hT' {h'} hh' {ψ'} hψ' ↦
        apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_fundamentalSolution hK' hK'Ω' hfill'
          hT'K' locallyIntegrable_planarNewtonianKernel harmonicOnNhd_planarNewtonianKernel
          planarNewtonianKernel_sub_comm
          (fun φ ↦ laplacian_planarNewtonianKernel_convolution (φ.contDiff.of_le (by simp))
            φ.hasCompactSupport)
          ⟨1 / 2, by norm_num, by norm_num, fun x hx ↦
            ⟨(planarMultipoleSeries x).partialSum,
              fun N z ↦ harmonicAt_planarMultipoleSeries_partialSum x N z,
              fun k ↦ tendstoUniformlyOn_iteratedFDeriv_planarMultipoleSeries_partialSum
                (by linarith [norm_pos_iff.2 hx]) k⟩⟩
          hT' hh' hψ'
  | d + 3 =>
    let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 3)) :=
      ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr
    have hmp : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : EuclideanSpace ℝ (Fin (d + 3)), x ≠ 0 →
        ∃ P : ℕ → EuclideanSpace ℝ (Fin (d + 3)) → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
          ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
            (iteratedFDeriv ℝ k fun y ↦ newtonianKernel (d + 3) (x - y)) atTop
            (closedBall 0 (c * ‖x‖)) := by
      obtain ⟨c, hc0, hc1, h⟩ :=
        exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_newtonianKernel_sub
          (d + 3)
      exact ⟨c, hc0, hc1, fun x hx ↦ let ⟨P, hP, _, hlim⟩ := h x hx; ⟨P, hP, hlim⟩⟩
    exact apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_linearIsometryEquiv e hK hKΩ hfill hTK
      hT hh hψ fun {Ω' T' K'} hK' hK'Ω' hfill' hT'K' hT' {h'} hh' {ψ'} hψ' ↦
        apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_of_fundamentalSolution hK' hK'Ω' hfill'
          hT'K' (locallyIntegrable_newtonianKernel (d + 3))
          (harmonicOnNhd_newtonianKernel (d + 3)) (newtonianKernel_sub_comm (d + 3))
          (fun φ ↦ laplacian_newtonianKernel_convolution (by omega) (by omega)
            (φ.contDiff.of_le (by simp)) φ.hasCompactSupport)
          hmp hT' hh' hψ'

/-- **Lax–Malgrange harmonic orthogonality.** Let `E` be any finite-dimensional real inner product
space, `F` any real normed space, and `T : 𝓓'(Ω, F)` a distribution supported in a compact set
`K ⊆ Ω` that is filled in `Ω`. If `T` vanishes on every test function agreeing near `K` with a
function harmonic on `Ω`, then `T` also vanishes on every test function agreeing near `K` with a
function harmonic near `K`. -/
theorem apply_eq_zero_of_isFilledIn_of_harmonicOnNhd
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens E} {T : 𝓓'(Ω, F)} {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    (hT : ∀ (H : E → ℝ) (ψ : 𝓓(Ω, ℝ)), HarmonicOnNhd H Ω → ((ψ : E → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {h : E → ℝ} (hh : HarmonicOnNhd h K) {ψ : 𝓓(Ω, ℝ)} (hψ : (ψ : E → ℝ) =ᶠ[𝓝ˢ K] h) :
    T ψ = 0 := by
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  rw [← mapCLM_apply]
  exact apply_eq_zero_of_isFilledIn_of_harmonicOnNhd_real hK hKΩ hfill
    ((dsupport_comp_subset T (map_zero ℓ)).trans hTK)
    (fun H φ hH hφ ↦ by simp [hT H φ hH hφ]) hh hψ

end DimensionFree

end Distribution
