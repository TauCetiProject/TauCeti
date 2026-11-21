/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Distribution.Convolution
public import TauCeti.Analysis.Distribution.LineDeriv
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Distribution.LinearEquiv
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.Convergence
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Multipole
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Multipole
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential

/-!
# Distributional kernel potentials and Lax–Malgrange harmonic orthogonality

Let `E` be a finite-dimensional real inner product space, `Ω ⊆ E` an open set, `F` a real normed
space (or a topological real vector space for the distributional Poisson equation), and
`T : 𝓓'(Ω, F)` a distribution. For a symmetric locally integrable kernel `G : E → ℝ` that is
harmonic on `{0}ᶜ` and a smooth cutoff `χ : 𝓓(Ω, ℝ)`, `Distribution.cutoffConvolutionCLM χ hG_loc T`
is the global distributional potential `G ⋆ (χ T)` on `E`. Whenever `-Δ (G ⋆ φ) = φ` for all global
test functions `φ`, this distribution solves Poisson's equation `-Δ (G ⋆ (χ T)) = χ T` on `E`
(`Distribution.laplacianCLM_cutoffConvolutionCLM`).

Away from `tsupport χ`, the reflected translated kernel `y ↦ G (x - y)` is smooth on a neighbourhood
of `tsupport χ`, yielding the pointwise off-support potential

`T.kernelPotentialPairing χ hG x = T (y ↦ χ y • G (x - y))`.

Cutting `G` off away from the origin identifies this function locally with the regularization
`Distribution.translatePairing` of `Distribution.cutoffCLM ... T`, from which smoothness, the jet
formula for `TauCeti.iteratedFDerivAlong`, harmonicity off `tsupport χ`, and (when `F` is complete)
the Bochner-integral representation `G ⋆ (χ T) = ∫ φ(x) • T.kernelPotentialPairing χ hG x dμ` on
tests disjoint from `tsupport χ` all follow.

When `dsupport T` is a compact subset of `Ω`, choosing cutoffs equal to `1` near `dsupport T` glues
these pairings into the cutoff-free potential `T.kernelPotentialOfSupport hG`, smooth and harmonic
on `(dsupport T)ᶜ`. If `dsupport T ⊆ K` for a compact set `K ⊆ Ω` filled in `Ω`
(`TauCeti.IsFilledIn K Ω`), `T` annihilates every test function agreeing near `K` with a function
harmonic on `Ω`, and `G` admits exterior multipole approximation by globally harmonic functions,
then scalarizing `T` with continuous linear functionals `ℓ : StrongDual ℝ F` reduces to `F = ℝ`:

* at every `x₀ ∉ Ω`, all iterated derivatives of the potential vanish;
* outside a large ball, the potential vanishes by the exterior multipole approximation;
* unique continuation forces `T.kernelPotentialOfSupport hG` to vanish on `Kᶜ`, confining
  `dsupport (G ⋆ (χ T))` to `K`;
* testing `-Δ (G ⋆ (χ T)) = χ T` against a cutoff of any `h` harmonic near `K` shows that `T` also
  annihilates every test agreeing near `K` with `h`.

Combining this fundamental-solution argument in dimension `2` (via `TauCeti.planarNewtonianKernel`)
and dimensions `d ≥ 3` (via `TauCeti.newtonianKernel d`) with direct arguments in dimensions `0`
and `1` (where locally harmonic functions on a filled-in compact set extend to affine functions on
each connected component of `Ω`) yields the dimension-free Lax–Malgrange harmonic orthogonality
theorem `Distribution.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd` for every finite-dimensional
real inner product space `E` and every real normed space `F`.

## Main declarations

* `Distribution.laplacianCLM_cutoffConvolutionCLM`: `-Δ (G ⋆ (χ T)) = χ T` in `𝓓'(⊤, F)` for any
  topological `ℝ`-module `F`.
* `Distribution.kernelPotentialPairing`: the pointwise pairing `x ↦ T (y ↦ χ y • G (x - y))` off
  `tsupport χ`, with smoothness, iterated directional derivative formula, harmonicity, and
  (for `[CompleteSpace F]`) integral representation
  `Distribution.cutoffConvolutionCLM_apply_eq_integral`.
* `Distribution.kernelPotentialOfSupport`: the cutoff-free potential on `(dsupport T)ᶜ` for
  compactly supported `T`, with smoothness, iterated directional derivative formula, harmonicity,
  and (for `[CompleteSpace F]`) integral representation
  `Distribution.cutoffConvolutionCLM_apply_eq_integral_smul_kernelPotentialOfSupport`.
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

section Poisson

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]
  {Ω : Opens E}

/-- **Poisson's equation for distributional kernel convolution.** If `G : E → ℝ` is locally
integrable with respect to an `SFinite` left-invariant measure `μ` and solves `-Δ (G ⋆ φ) = φ` for
every global test function `φ : 𝓓(⊤, ℝ)`, then `-Δ (G ⋆ (χ T)) = χ T` in `𝓓'(⊤, F)`. -/
theorem laplacianCLM_cutoffConvolutionCLM (χ : 𝓓(Ω, ℝ)) {G : E → ℝ} {μ : Measure E} [SFinite μ]
    [μ.IsAddLeftInvariant] (hG_loc : LocallyIntegrable G μ)
    (hG_lap : ∀ φ : 𝓓((⊤ : Opens E), ℝ),
      Δ (G ⋆[lsmul ℝ ℝ, μ] (φ : E → ℝ)) = -(φ : E → ℝ))
    (T : 𝓓'(Ω, F)) :
    laplacianCLM ℝ E _ (cutoffConvolutionCLM (Ω' := ⊤) χ hG_loc T) =
      -cutoffCLM (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T := by
  ext φ
  rw [Distribution.laplacianCLM_apply_apply, cutoffConvolutionCLM_apply, neg_apply,
    cutoffCLM_apply, ← map_neg]
  congr 1
  ext y
  let Δφ : 𝓓((⊤ : Opens E), ℝ) := laplacianCLM ℝ E _ φ
  have hconv : (G ⋆[lsmul ℝ ℝ, μ] (Δφ : E → ℝ)) y = -φ y := by
    have hΔ : (Δφ : E → ℝ) = Δ (φ : E → ℝ) := funext (TestFunction.laplacianCLM_apply φ)
    rw [hΔ, ← φ.hasCompactSupport.laplacian_convolution_right (lsmul ℝ ℝ) hG_loc
      (φ.contDiff.of_le (by simp)), hG_lap φ, Pi.neg_apply]
  simp [Δφ, hconv]

end Poisson

section KernelPotential

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

private theorem contDiffOn_kernel_sub_right {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) (x : E) :
    ContDiffOn ℝ ∞ (fun y ↦ G (x - y)) {x}ᶜ := by
  simpa using (hG.iteratedFDerivAlong_sub_right [] x).analyticOnNhd.contDiffOn
    isOpen_compl_singleton.uniqueDiffOn

/-- The pointwise off-support kernel potential `x ↦ T (y ↦ χ y • G (x - y))` for `x ∉ tsupport χ`,
extended by `0` on `tsupport χ`. -/
def kernelPotentialPairing (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) (x : E) : F :=
  open Classical in
  if hx : x ∉ tsupport (χ : E → ℝ) then
    T (χ.smulOfContDiffOn isOpen_compl_singleton (subset_compl_singleton_iff.2 hx)
      (contDiffOn_kernel_sub_right hG x))
  else 0

/-- At `x ∉ tsupport χ`, `kernelPotentialPairing` is `T` applied to any test function equal to
`y ↦ χ y * G (x - y)`. -/
theorem kernelPotentialPairing_eq (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)} {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) {x : E} (hx : x ∉ tsupport (χ : E → ℝ)) {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = χ y * G (x - y)) :
    T.kernelPotentialPairing χ hG x = T φ := by
  unfold kernelPotentialPairing
  rw [dite_eq_left_of_eq_true (eq_true hx)]
  congr 1
  ext y
  rw [TestFunction.smulOfContDiffOn_apply, smul_eq_mul, hφ]

/-- On `tsupport χ`, `kernelPotentialPairing` takes the junk value `0`. -/
theorem kernelPotentialPairing_eq_zero_of_mem_tsupport (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)} {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) {x : E} (hx : x ∈ tsupport (χ : E → ℝ)) :
    T.kernelPotentialPairing χ hG x = 0 := by
  simp [kernelPotentialPairing, hx]

/-- The kernel potential pairing of the zero distribution vanishes. -/
@[simp]
theorem kernelPotentialPairing_zero (χ : 𝓓(Ω, ℝ)) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) :
    (0 : 𝓓'(Ω, F)).kernelPotentialPairing χ hG = 0 := by
  ext x
  simp [kernelPotentialPairing]

/-- The kernel potential pairing with the zero cutoff vanishes. -/
@[simp]
theorem kernelPotentialPairing_zero_cutoff (T : 𝓓'(Ω, F)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) :
    T.kernelPotentialPairing (0 : 𝓓(Ω, ℝ)) hG = 0 := by
  ext x
  have hx : x ∉ tsupport ((0 : 𝓓(Ω, ℝ)) : E → ℝ) := by simp
  rw [kernelPotentialPairing_eq T hG hx (φ := 0) fun y ↦ by simp]
  simp

/-- The kernel potential pairing is additive in the distribution. -/
@[simp]
theorem kernelPotentialPairing_add (T S : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) :
    (T + S).kernelPotentialPairing χ hG =
      T.kernelPotentialPairing χ hG + S.kernelPotentialPairing χ hG := by
  ext x
  by_cases hx : x ∉ tsupport (χ : E → ℝ) <;> simp [kernelPotentialPairing, hx]

/-- The kernel potential pairing commutes with negation of the distribution. -/
@[simp]
theorem kernelPotentialPairing_neg (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) :
    (-T).kernelPotentialPairing χ hG = -T.kernelPotentialPairing χ hG := by
  ext x
  by_cases hx : x ∉ tsupport (χ : E → ℝ) <;> simp [kernelPotentialPairing, hx]

/-- The kernel potential pairing commutes with subtraction of distributions. -/
@[simp]
theorem kernelPotentialPairing_sub (T S : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) :
    (T - S).kernelPotentialPairing χ hG =
      T.kernelPotentialPairing χ hG - S.kernelPotentialPairing χ hG := by
  ext x
  by_cases hx : x ∉ tsupport (χ : E → ℝ) <;> simp [kernelPotentialPairing, hx]

/-- The kernel potential pairing commutes with scalar multiplication of the distribution. -/
@[simp]
theorem kernelPotentialPairing_smul {M : Type*} [Monoid M] [DistribMulAction M F]
    [SMulCommClass ℝ M F] [ContinuousConstSMul M F] (c : M) (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ))
    {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) :
    (c • T).kernelPotentialPairing χ hG = c • T.kernelPotentialPairing χ hG := by
  ext x
  by_cases hx : x ∉ tsupport (χ : E → ℝ) <;> simp [kernelPotentialPairing, hx]

/-- Postcomposing a distribution with a continuous linear map commutes with
`kernelPotentialPairing`. -/
theorem kernelPotentialPairing_mapCLM {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (A : F →L[ℝ] F') (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ)
    (x : E) :
    (mapCLM A T).kernelPotentialPairing χ hG x = A (T.kernelPotentialPairing χ hG x) := by
  by_cases hx : x ∉ tsupport (χ : E → ℝ)
  · simp [kernelPotentialPairing, hx]
  · simp [kernelPotentialPairing, hx]

/-- Given a compact set `K` disjoint from `tsupport χ`, cut off `G` away from `0` to obtain a test
function `ρ` on `E` with `ρ (y - z) = G (z - y)` for all `y ∈ tsupport χ` and `z` near `K`. -/
private theorem exists_kernelTestFunction_of_disjoint (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x))
    {K : Set E} (hK : IsCompact K) (hdisj : Disjoint K (tsupport (χ : E → ℝ))) :
    ∃ ρ : 𝓓((⊤ : Opens E), ℝ),
      ∀ y ∈ tsupport (χ : E → ℝ), ∀ x ∈ K,
        (fun z ↦ ρ (y - z)) =ᶠ[𝓝 x] fun z ↦ G (z - y) := by
  let S : Set E := tsupport (χ : E → ℝ) - K
  have hS : IsCompact S := by
    simpa only [S, sub_eq_add_neg] using IsCompact.add χ.hasCompactSupport hK.neg
  have hS0 : S ⊆ {0}ᶜ := by
    rintro _ ⟨y, hy, x, hx, hyx⟩ h0
    rw [mem_singleton_iff] at h0
    exact hdisj.le_bot ⟨hx, (sub_eq_zero.1 (hyx.trans h0)) ▸ hy⟩
  obtain ⟨η, -, hη1, hη0⟩ := TestFunction.exists_cutoff_tsupport_subset
    (Ω := (⊤ : Opens E)) (n := ⊤) hS isOpen_compl_singleton hS0 (subset_univ _)
  let ρ : 𝓓((⊤ : Opens E), ℝ) := η.smulOfContDiffOn isOpen_compl_singleton hη0
    (hG.analyticOnNhd.contDiffOn isOpen_compl_singleton.uniqueDiffOn)
  obtain ⟨W, hWo, hSW, hηW⟩ := mem_nhdsSet_iff_exists.1 hη1
  refine ⟨ρ, fun y hy x hx ↦ ?_⟩
  have hyx : y - x ∈ W := hSW ⟨y, hy, x, hx, rfl⟩
  filter_upwards [(hWo.preimage (continuous_const.sub continuous_id)).mem_nhds hyx] with z hz
  have hηz : η (y - z) = 1 := hηW hz
  simp [ρ, hηz, hG_symm]

/-- On any compact set `K` disjoint from `tsupport χ`, `kernelPotentialPairing` agrees with the
global regularization of `cutoffCLM ... T`. -/
private theorem exists_translatePairing_eqOn_of_disjoint (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x))
    {K : Set E} (hK : IsCompact K) (hdisj : Disjoint K (tsupport (χ : E → ℝ))) :
    ∃ ρ : 𝓓((⊤ : Opens E), ℝ),
      (∀ y ∈ tsupport (χ : E → ℝ), ∀ x ∈ K,
        (fun z ↦ ρ (y - z)) =ᶠ[𝓝 x] fun z ↦ G (z - y)) ∧
      EqOn ((cutoffCLM (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T
        ).translatePairing ρ) (T.kernelPotentialPairing χ hG) K := by
  obtain ⟨ρ, hρ⟩ := exists_kernelTestFunction_of_disjoint χ hG hG_symm hK hdisj
  refine ⟨ρ, hρ, fun x hx ↦ ?_⟩
  have hxχ : x ∉ tsupport (χ : E → ℝ) := Disjoint.notMem_of_mem_left hdisj hx
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ρ.translateOfMapsTo (mapsTo_univ (· + x) _)
  rw [Distribution.translatePairing_eq _ (ρ.translateOfMapsTo_apply (mapsTo_univ (· + x) _)),
    cutoffCLM_apply, kernelPotentialPairing_eq T hG hxχ
      (φ := TestFunction.cutoffCLM χ.contDiff
        (inter_subset_left.trans χ.tsupport_subset) ψ) fun y ↦ by
      rw [TestFunction.cutoffCLM_apply, smul_eq_mul]
      by_cases hy : y ∈ tsupport (χ : E → ℝ)
      · have hψy : ψ y = ρ (y - x) := ρ.translateOfMapsTo_apply (mapsTo_univ (· + x) _) y
        have hρx : ρ (y - x) = G (x - y) := (hρ y hy x hx).self_of_nhds
        rw [hψy, hρx]
      · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]]

/-- Around any point `x₀ ∉ tsupport χ`, `kernelPotentialPairing` locally agrees with a
regularization of `cutoffCLM ... T` by a smooth cutoff of `G`. -/
private theorem exists_translatePairing_eventuallyEq_kernelPotentialPairing (T : 𝓓'(Ω, F))
    (χ : 𝓓(Ω, ℝ)) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x)) {x₀ : E} (hx₀ : x₀ ∉ tsupport (χ : E → ℝ)) :
    ∃ ρ : 𝓓((⊤ : Opens E), ℝ),
      (∀ y ∈ tsupport (χ : E → ℝ), (fun z ↦ ρ (y - z)) =ᶠ[𝓝 x₀] fun z ↦ G (z - y)) ∧
      T.kernelPotentialPairing χ hG =ᶠ[𝓝 x₀]
        (cutoffCLM (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T
          ).translatePairing ρ := by
  have hopen := (isClosed_tsupport (χ : E → ℝ)).isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x₀ hx₀
  have hcb : closedBall x₀ (r / 2) ⊆ (tsupport (χ : E → ℝ))ᶜ :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨ρ, hρ, hEq⟩ := exists_translatePairing_eqOn_of_disjoint T χ hG hG_symm
    (isCompact_closedBall x₀ (r / 2)) (Set.disjoint_left.2 fun _ h₁ h₂ ↦ hcb h₁ h₂)
  refine ⟨ρ, fun y hy ↦ hρ y hy x₀ (mem_closedBall_self (half_pos hr).le), ?_⟩
  filter_upwards [ball_mem_nhds x₀ (half_pos hr)] with x hx
  exact (hEq (ball_subset_closedBall hx)).symm

/-- **Smoothness of the off-support kernel potential.** `T.kernelPotentialPairing χ hG` is smooth
on `(tsupport χ)ᶜ`. -/
theorem contDiffOn_kernelPotentialPairing (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x)) :
    ContDiffOn ℝ ∞ (T.kernelPotentialPairing χ hG) (tsupport (χ : E → ℝ))ᶜ := by
  intro x₀ hx₀
  obtain ⟨ρ, -, hev⟩ :=
    exists_translatePairing_eventuallyEq_kernelPotentialPairing T χ hG hG_symm hx₀
  have hc : ContDiffAt ℝ ∞
      ((cutoffCLM (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T
        ).translatePairing ρ) x₀ :=
    (((cutoffCLM (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T
      ).contDiffOn_translatePairing ρ).mono fun _ _ ↦ mapsTo_univ _ _).contDiffAt
        (isOpen_univ.mem_nhds (mem_univ x₀))
  exact (hc.congr_of_eventuallyEq hev).contDiffWithinAt

/-- **Jet formula for the off-support kernel potential.** At `x₀ ∉ tsupport χ`, the iterated
directional derivative of `T.kernelPotentialPairing χ hG` along `vs` pairs `T` with
`y ↦ χ y * (∂_{vs} G)(x₀ - y)`. -/
theorem iteratedFDerivAlong_kernelPotentialPairing (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)} {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x))
    {x₀ : E} (hx₀ : x₀ ∉ tsupport (χ : E → ℝ)) (vs : List E) {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = χ y * iteratedFDerivAlong ℝ vs G (x₀ - y)) :
    iteratedFDerivAlong ℝ vs (T.kernelPotentialPairing χ hG) x₀ = T φ := by
  obtain ⟨ρ, hρ, hev⟩ :=
    exists_translatePairing_eventuallyEq_kernelPotentialPairing T χ hG hG_symm hx₀
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ρ.translateIteratedFDerivAlong (mapsTo_univ (· + x₀) _) vs
  rw [(hev.iteratedFDerivAlong vs).eq_of_nhds,
    (cutoffCLM (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T
      ).iteratedFDerivAlong_translatePairing_eq (mapsTo_univ (· + x₀) _) vs (φ := ψ)
      (ρ.translateIteratedFDerivAlong_apply (mapsTo_univ (· + x₀) _) vs),
    cutoffCLM_apply]
  congr 1
  ext y
  rw [TestFunction.cutoffCLM_apply, hφ]
  by_cases hy : y ∈ tsupport (χ : E → ℝ)
  · simp only [ψ, TestFunction.translateIteratedFDerivAlong_apply, smul_eq_mul,
      ((hρ y hy).iteratedFDerivAlong vs).eq_of_nhds, iteratedFDerivAlong_comp_sub]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Harmonicity of the off-support kernel potential.** `T.kernelPotentialPairing χ hG` is
harmonic on `(tsupport χ)ᶜ`. -/
theorem harmonicOnNhd_kernelPotentialPairing (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) (hG_symm : ∀ x y, G (x - y) = G (y - x)) :
    HarmonicOnNhd (T.kernelPotentialPairing χ hG) (tsupport (χ : E → ℝ))ᶜ := by
  have hopen := (isClosed_tsupport (χ : E → ℝ)).isOpen_compl
  have hsmooth := contDiffOn_kernelPotentialPairing T χ hG hG_symm
  intro x₀ hx₀
  refine ⟨(hsmooth.contDiffAt (hopen.mem_nhds hx₀)).of_le (by simp), ?_⟩
  filter_upwards [hopen.mem_nhds hx₀] with x hx
  set b := stdOrthonormalBasis ℝ E
  have hcx : ContDiffAt ℝ ∞ (T.kernelPotentialPairing χ hG) x :=
    hsmooth.contDiffAt (hopen.mem_nhds hx)
  let φ (i : Fin (Module.finrank ℝ E)) : 𝓓(Ω, ℝ) :=
    χ.smulOfContDiffOn isOpen_compl_singleton (subset_compl_singleton_iff.2 hx)
      ((hG.iteratedFDerivAlong_sub_right [b i, b i] x).analyticOnNhd.contDiffOn
        isOpen_compl_singleton.uniqueDiffOn)
  have hsum : ∑ i, φ i = 0 := by
    ext y
    rw [_root_.sum_apply, FunLike.coe_zero, Pi.zero_apply]
    simp only [φ, TestFunction.smulOfContDiffOn_apply, smul_eq_mul, ← Finset.mul_sum]
    by_cases hy : y ∈ tsupport (χ : E → ℝ)
    · have hxy : x - y ∈ ({0}ᶜ : Set E) := sub_ne_zero.2 fun h ↦ hx (h ▸ hy)
      have hGx : ContDiffAt ℝ 2 G (x - y) := (hG (x - y) hxy).1
      have hΔ : ∑ i, iteratedFDerivAlong ℝ [b i, b i] G (x - y) = Δ G (x - y) := by
        rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simpa using hGx.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv le_rfl ![b i, b i]
      rw [hΔ, (hG (x - y) hxy).2.self_of_nhds, Pi.zero_apply, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  calc ∑ i, iteratedFDeriv ℝ 2 (T.kernelPotentialPairing χ hG) x ![b i, b i]
      = ∑ i, iteratedFDerivAlong ℝ [b i, b i] (T.kernelPotentialPairing χ hG) x := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simpa using ((hcx.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
          ).iteratedFDerivAlong_ofFn_eq_iteratedFDeriv le_rfl ![b i, b i]).symm
    _ = ∑ i, T (φ i) := Finset.sum_congr rfl fun i _ ↦
        iteratedFDerivAlong_kernelPotentialPairing T hG hG_symm hx [b i, b i] (fun y ↦ by
          simp [φ])
    _ = 0 := by rw [← map_sum, hsum, map_zero]

/-- **Integral representation of the distributional kernel potential.** On test functions `φ`
whose support is disjoint from `tsupport χ`, `G ⋆ (χ T)` is represented by integrating against
`T.kernelPotentialPairing χ hG`. -/
theorem cutoffConvolutionCLM_apply_eq_integral [CompleteSpace F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsLocallyFiniteMeasure μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG_loc : LocallyIntegrable G μ) (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x))
    {φ : 𝓓((⊤ : Opens E), ℝ)} (hdisj : Disjoint (tsupport (φ : E → ℝ)) (tsupport (χ : E → ℝ))) :
    cutoffConvolutionCLM (Ω' := ⊤) χ hG_loc T φ =
      ∫ x, φ x • T.kernelPotentialPairing χ hG x ∂μ := by
  obtain ⟨ρ, hρ, hEq⟩ :=
    exists_translatePairing_eqOn_of_disjoint T χ hG hG_symm φ.hasCompactSupport hdisj
  let ψ : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨(φ : E → ℝ) ⋆[lsmul ℝ ℝ, μ] (ρ : E → ℝ),
      ρ.hasCompactSupport.contDiff_convolution_right (lsmul ℝ ℝ)
        φ.contDiff.continuous.locallyIntegrable ρ.contDiff,
      φ.hasCompactSupport.convolution (lsmul ℝ ℝ) ρ.hasCompactSupport, subset_univ _⟩
  have hφint : Integrable (φ : E → ℝ) μ :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hmatch : χ.cutoffConvolutionCLM hG_loc φ =
      TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) ψ := by
    ext y
    simp only [TestFunction.cutoffConvolutionCLM_apply, TestFunction.cutoffCLM_apply, ψ,
      TestFunction.coe_mk]
    by_cases hy : y ∈ tsupport (χ : E → ℝ)
    · congr 1
      rw [convolution_def, convolution_def, ← integral_sub_left_eq_self _ μ y]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      dsimp only
      rw [sub_sub_cancel]
      by_cases hx : x ∈ tsupport (φ : E → ℝ)
      · simp [(hρ y hy x hx).self_of_nhds, hG_symm, mul_comm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [cutoffConvolutionCLM_apply, hmatch,
    ← cutoffCLM_apply (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T ψ,
    (cutoffCLM (Ω' := ⊤) χ.contDiff (inter_subset_left.trans χ.tsupport_subset) T
      ).apply_eq_integral_smul_translatePairing ρ hφint φ.hasCompactSupport
      (fun _ _ ↦ mapsTo_univ _ _) (ψ := ψ) rfl]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  by_cases hx : x ∈ tsupport (φ : E → ℝ)
  · rw [hEq hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end KernelPotential

section SupportPotential

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The cutoff-free off-support kernel potential of `T` at `x`: defined by choosing any cutoff
`χ : 𝓓(Ω, ℝ)` equal to `1` near `dsupport T` with `x ∉ tsupport χ`, and `0` when none exists. -/
def kernelPotentialOfSupport (T : 𝓓'(Ω, F)) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) (x : E) : F :=
  open Classical in
  if h : ∃ χ : 𝓓(Ω, ℝ), (∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) ∧ x ∉ tsupport (χ : E → ℝ) then
    T.kernelPotentialPairing h.choose hG x
  else 0

/-- For any cutoff `χ : 𝓓(Ω, ℝ)` equal to `1` near `dsupport T` and any `x ∉ tsupport χ`,
`T.kernelPotentialOfSupport hG x` agrees with `T.kernelPotentialPairing χ hG x`. -/
theorem kernelPotentialOfSupport_eq_kernelPotentialPairing (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) {x : E}
    (hx : x ∉ tsupport (χ : E → ℝ)) :
    T.kernelPotentialOfSupport hG x = T.kernelPotentialPairing χ hG x := by
  have hex : ∃ χ' : 𝓓(Ω, ℝ),
      (∀ᶠ y in 𝓝ˢ (dsupport T), χ' y = 1) ∧ x ∉ tsupport (χ' : E → ℝ) :=
    ⟨χ, hχ, hx⟩
  simp only [kernelPotentialOfSupport, hex, ↓reduceDIte]
  obtain ⟨hχ', hx'⟩ := hex.choose_spec
  rw [kernelPotentialPairing_eq T hG hx'
      (φ := hex.choose.smulOfContDiffOn isOpen_compl_singleton
        (subset_compl_singleton_iff.2 hx') (contDiffOn_kernel_sub_right hG x))
      (fun y ↦ by simp),
    kernelPotentialPairing_eq T hG hx
      (φ := χ.smulOfContDiffOn isOpen_compl_singleton (subset_compl_singleton_iff.2 hx)
        (contDiffOn_kernel_sub_right hG x))
      (fun y ↦ by simp)]
  refine Distribution.map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ', hχ] with y h₁ h₂
  simp [h₁, h₂]

/-- When no cutoff equal to `1` near `dsupport T` avoids `x`, `kernelPotentialOfSupport` takes the
junk value `0`. -/
theorem kernelPotentialOfSupport_eq_zero_of_not_exists (T : 𝓓'(Ω, F)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) {x : E}
    (h : ¬∃ χ : 𝓓(Ω, ℝ), (∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) ∧ x ∉ tsupport (χ : E → ℝ)) :
    T.kernelPotentialOfSupport hG x = 0 := by
  simp [kernelPotentialOfSupport, h]

/-- On `dsupport T`, `kernelPotentialOfSupport` takes the junk value `0`. -/
theorem kernelPotentialOfSupport_eq_zero_of_mem_dsupport (T : 𝓓'(Ω, F)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) {x : E} (hx : x ∈ dsupport T) :
    T.kernelPotentialOfSupport hG x = 0 := by
  refine kernelPotentialOfSupport_eq_zero_of_not_exists T hG ?_
  rintro ⟨χ, hχ1, hxχ⟩
  have hχx : χ x = 1 := (hχ1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
  exact hxχ (subset_tsupport (χ : E → ℝ) (by simp [hχx]))

/-- The cutoff-free potential of the zero distribution vanishes. -/
@[simp]
theorem kernelPotentialOfSupport_zero {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) :
    (0 : 𝓓'(Ω, F)).kernelPotentialOfSupport hG = 0 := by
  ext x
  simp [kernelPotentialOfSupport]

/-- The cutoff-free potential commutes with negation of the distribution. -/
@[simp]
theorem kernelPotentialOfSupport_neg (T : 𝓓'(Ω, F)) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) :
    (-T).kernelPotentialOfSupport hG = -T.kernelPotentialOfSupport hG := by
  ext x
  have hsupp : dsupport (-T) = dsupport T := by
    rw [FunLike.coe_neg]
    exact dsupport_neg ⇑T
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), (∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) ∧ x ∉ tsupport (χ : E → ℝ)
  · obtain ⟨χ, hχ, hx⟩ := h
    rw [Pi.neg_apply,
      kernelPotentialOfSupport_eq_kernelPotentialPairing (-T) (by rwa [hsupp]) hG hx,
      kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ hG hx,
      kernelPotentialPairing_neg, Pi.neg_apply]
  · rw [Pi.neg_apply,
      kernelPotentialOfSupport_eq_zero_of_not_exists (-T) hG (by rwa [hsupp]),
      kernelPotentialOfSupport_eq_zero_of_not_exists T hG h, neg_zero]

/-- The cutoff-free potential commutes with scalar multiplication of the distribution. -/
@[simp]
theorem kernelPotentialOfSupport_smul (c : ℝ) (T : 𝓓'(Ω, F)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) :
    (c • T).kernelPotentialOfSupport hG = c • T.kernelPotentialOfSupport hG := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  ext x
  have hsupp : dsupport (c • T) = dsupport T := by
    rw [FunLike.coe_smul]
    exact dsupport_smul_of_ne_zero hc ⇑T
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), (∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) ∧ x ∉ tsupport (χ : E → ℝ)
  · obtain ⟨χ, hχ, hx⟩ := h
    rw [Pi.smul_apply,
      kernelPotentialOfSupport_eq_kernelPotentialPairing (c • T) (by rwa [hsupp]) hG hx,
      kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ hG hx,
      kernelPotentialPairing_smul, Pi.smul_apply]
  · rw [Pi.smul_apply,
      kernelPotentialOfSupport_eq_zero_of_not_exists (c • T) hG (by rwa [hsupp]),
      kernelPotentialOfSupport_eq_zero_of_not_exists T hG h, smul_zero]

/-- If `dsupport T` is a compact subset of `Ω`, every `x ∉ dsupport T` admits a cutoff equal to `1`
near `dsupport T` whose support misses `x`. -/
private theorem exists_cutoff_notMem_tsupport_of_notMem_dsupport {T : 𝓓'(Ω, F)}
    (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω) {x : E} (hx : x ∉ dsupport T) :
    ∃ χ : 𝓓(Ω, ℝ), (∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) ∧ x ∉ tsupport (χ : E → ℝ) := by
  obtain ⟨χ, -, hχ1, hχs⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤) hc
    (Ω.isOpen.inter isOpen_compl_singleton)
    (subset_inter hΩ (subset_compl_singleton_iff.2 hx)) inter_subset_left
  exact ⟨χ, hχ1, fun hxχ ↦ (hχs hxχ).2 rfl⟩

/-- On distributions with compact support inside `Ω`, `kernelPotentialOfSupport` is additive away
from the union of their supports. -/
theorem kernelPotentialOfSupport_add {T S : 𝓓'(Ω, F)} (hcT : IsCompact (dsupport T))
    (hΩT : dsupport T ⊆ Ω) (hcS : IsCompact (dsupport S)) (hΩS : dsupport S ⊆ Ω) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) {x : E} (hxT : x ∉ dsupport T) (hxS : x ∉ dsupport S) :
    (T + S).kernelPotentialOfSupport hG x =
      T.kernelPotentialOfSupport hG x + S.kernelPotentialOfSupport hG x := by
  have hxU : x ∉ dsupport T ∪ dsupport S := fun h ↦ h.elim hxT hxS
  obtain ⟨χ, -, hχ1, hχs⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤)
    (hcT.union hcS) (Ω.isOpen.inter isOpen_compl_singleton)
    (subset_inter (union_subset hΩT hΩS) (subset_compl_singleton_iff.2 hxU)) inter_subset_left
  have hxχ : x ∉ tsupport (χ : E → ℝ) := fun hx' ↦ (hχs hx').2 rfl
  have hsupp : dsupport (T + S) ⊆ dsupport T ∪ dsupport S := by
    rw [FunLike.coe_add]
    exact dsupport_add_subset ⇑T ⇑S
  rw [kernelPotentialOfSupport_eq_kernelPotentialPairing (T + S)
      (hχ1.filter_mono (nhdsSet_mono hsupp)) hG hxχ,
    kernelPotentialOfSupport_eq_kernelPotentialPairing T
      (hχ1.filter_mono (nhdsSet_mono subset_union_left)) hG hxχ,
    kernelPotentialOfSupport_eq_kernelPotentialPairing S
      (hχ1.filter_mono (nhdsSet_mono subset_union_right)) hG hxχ,
    kernelPotentialPairing_add, Pi.add_apply]

/-- On a compactly supported distribution `T`, postcomposition with a continuous linear map
commutes with `kernelPotentialOfSupport` off `dsupport T`. -/
theorem kernelPotentialOfSupport_mapCLM {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (A : F →L[ℝ] F') {T : 𝓓'(Ω, F)} (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω)
    {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ) {x : E} (hx : x ∉ dsupport T) :
    (mapCLM A T).kernelPotentialOfSupport hG x = A (T.kernelPotentialOfSupport hG x) := by
  obtain ⟨χ, hχ1, hxχ⟩ := exists_cutoff_notMem_tsupport_of_notMem_dsupport hc hΩ hx
  have hsupp : dsupport (mapCLM A T) ⊆ dsupport T := dsupport_comp_subset T (map_zero A)
  rw [kernelPotentialOfSupport_eq_kernelPotentialPairing (mapCLM A T)
      (hχ1.filter_mono (nhdsSet_mono hsupp)) hG hxχ,
    kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ1 hG hxχ,
    kernelPotentialPairing_mapCLM]

/-- **Smoothness of the cutoff-free potential off `dsupport T`.** When `dsupport T` is a compact
subset of `Ω`, `T.kernelPotentialOfSupport hG` is smooth on `(dsupport T)ᶜ`. -/
theorem contDiffOn_kernelPotentialOfSupport {T : 𝓓'(Ω, F)} (hc : IsCompact (dsupport T))
    (hΩ : dsupport T ⊆ Ω) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x)) :
    ContDiffOn ℝ ∞ (T.kernelPotentialOfSupport hG) (dsupport T)ᶜ := by
  intro x hx
  obtain ⟨χ, hχ1, hxχ⟩ := exists_cutoff_notMem_tsupport_of_notMem_dsupport hc hΩ hx
  have hev : T.kernelPotentialOfSupport hG =ᶠ[𝓝 x] T.kernelPotentialPairing χ hG := by
    filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hxχ] with z hz
    exact kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ1 hG hz
  exact (((contDiffOn_kernelPotentialPairing T χ hG hG_symm).contDiffAt
    ((isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hxχ)).congr_of_eventuallyEq
      hev).contDiffWithinAt

/-- **Jet formula for the cutoff-free potential.** For a cutoff `χ` equal to `1` near `dsupport T`
and `x₀ ∉ tsupport χ`, the iterated directional derivative of `T.kernelPotentialOfSupport hG`
along `vs` pairs `T` with `y ↦ χ y * (∂_{vs} G)(x₀ - y)`. -/
theorem iteratedFDerivAlong_kernelPotentialOfSupport (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x)) {x₀ : E} (hx₀ : x₀ ∉ tsupport (χ : E → ℝ))
    (vs : List E) {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = χ y * iteratedFDerivAlong ℝ vs G (x₀ - y)) :
    iteratedFDerivAlong ℝ vs (T.kernelPotentialOfSupport hG) x₀ = T φ := by
  have hev : T.kernelPotentialOfSupport hG =ᶠ[𝓝 x₀] T.kernelPotentialPairing χ hG := by
    filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hx₀] with z hz
    exact kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ hG hz
  rw [(hev.iteratedFDerivAlong vs).eq_of_nhds]
  exact iteratedFDerivAlong_kernelPotentialPairing T hG hG_symm hx₀ vs hφ

/-- **Harmonicity of the cutoff-free potential off `dsupport T`.** When `dsupport T` is a compact
subset of `Ω`, `T.kernelPotentialOfSupport hG` is harmonic on `(dsupport T)ᶜ`. -/
theorem harmonicOnNhd_kernelPotentialOfSupport {T : 𝓓'(Ω, F)} (hc : IsCompact (dsupport T))
    (hΩ : dsupport T ⊆ Ω) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x)) :
    HarmonicOnNhd (T.kernelPotentialOfSupport hG) (dsupport T)ᶜ := by
  intro x hx
  obtain ⟨χ, hχ1, hxχ⟩ := exists_cutoff_notMem_tsupport_of_notMem_dsupport hc hΩ hx
  have hev : T.kernelPotentialOfSupport hG =ᶠ[𝓝 x] T.kernelPotentialPairing χ hG := by
    filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hxχ] with z hz
    exact kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ1 hG hz
  exact (harmonicAt_congr_nhds hev).2
    (harmonicOnNhd_kernelPotentialPairing T χ hG hG_symm x hxχ)

/-- On tests disjoint from `dsupport T`, `cutoffConvolutionCLM` is represented by integrating
against the cutoff-free potential `T.kernelPotentialOfSupport hG`. -/
theorem cutoffConvolutionCLM_apply_eq_integral_smul_kernelPotentialOfSupport [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {T : 𝓓'(Ω, F)} {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) {G : E → ℝ}
    (hG_loc : LocallyIntegrable G μ) (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x)) {φ : 𝓓((⊤ : Opens E), ℝ)}
    (hdisj : Disjoint (tsupport (φ : E → ℝ)) (dsupport T)) :
    cutoffConvolutionCLM (Ω' := ⊤) χ hG_loc T φ =
      ∫ x, φ x • T.kernelPotentialOfSupport hG x ∂μ := by
  obtain ⟨hc, hΩ⟩ := Distribution.isCompact_dsupport_and_subset_of_eventually_eq_one hχ
  obtain ⟨χ', -, hχ'1, hχ's⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤) hc
    (Ω.isOpen.inter (isClosed_tsupport (φ : E → ℝ)).isOpen_compl)
    (subset_inter hΩ hdisj.symm.subset_compl_right) inter_subset_left
  have hdisj' : Disjoint (tsupport (φ : E → ℝ)) (tsupport (χ' : E → ℝ)) :=
    Disjoint.symm (Set.disjoint_left.2 fun _ hy hyφ ↦ (hχ's hy).2 hyφ)
  have hcongr : (χ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ' := by
    filter_upwards [hχ, hχ'1] with y h₁ h₂
    rw [h₁, h₂]
  rw [cutoffConvolutionCLM_congr hG_loc hcongr,
    cutoffConvolutionCLM_apply_eq_integral T χ' hG_loc hG hG_symm hdisj']
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  by_cases hx : x ∈ tsupport (φ : E → ℝ)
  · rw [kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ'1 hG
      (Disjoint.notMem_of_mem_left hdisj' hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end SupportPotential

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
    (contDiffOn_kernel_sub_right hG x) fun k _ ↦ (hPlim k).mono hχ_sub
  have hT_lim := (T.continuous.tendsto _).comp htend
  have hzero (N : ℕ) :
      T (χ.smulOfContDiffOn isOpen_compl_singleton hχx (hPsmooth N)) = 0 := by
    refine hT (P N) _ (fun z _ ↦ hPharm N z) ?_
    filter_upwards [hχ1] with y hy
    simp [hy]
  rw [kernelPotentialOfSupport_eq_kernelPotentialPairing T hχT hG hxχ,
    kernelPotentialPairing_eq T hG hxχ
      (φ := χ.smulOfContDiffOn isOpen_compl_singleton hχx (contDiffOn_kernel_sub_right hG x))
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
    · obtain ⟨W, hWo, hK'W, hW⟩ := mem_nhdsSet_iff_exists.1 hψ'
      filter_upwards [(hWo.preimage e.continuous).mem_nhdsSet.2 fun x hx ↦ hK'W ⟨x, hx, rfl⟩]
        with x hx
      simpa [e_cle] using hW hx
  have hh' : HarmonicOnNhd (h ∘ e.symm) K' := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using (harmonicAt_comp_linearIsometryEquiv_right_iff e.symm).2 (by simpa using hh x hx)
  let ψ' : 𝓓(Ω', ℝ) := e_cle.symm.transportTestFunction hmaps_symm ψ
  have hψ' : (ψ' : E' → ℝ) =ᶠ[𝓝ˢ K'] (h ∘ e.symm) := by
    obtain ⟨W, hWo, hKW, hW⟩ := mem_nhdsSet_iff_exists.1 hψ
    filter_upwards [(hWo.preimage e.symm.continuous).mem_nhdsSet.2 fun y hy ↦ by
      rcases hy with ⟨x, hx, rfl⟩; simpa using hKW hx] with y hy
    simpa [ψ', e_cle] using hW hy
  have hfill' : IsFilledIn K' Ω' := by
    convert e.toHomeomorph.isFilledIn_image.2 hfill
    · simp
    · exact Set.image_congr fun _ _ ↦ by simp
  have hzero : T' ψ' = 0 := hE' (hK.image e.continuous) (image_mono hKΩ)
    hfill' hT'K' hT' hh' hψ'
  have hroundtrip : e_cle.transportTestFunction hmaps ψ' = ψ := by
    ext x
    simp [ψ', e_cle]
  rwa [transportCLM_apply, hroundtrip] at hzero

/-- On an open connected subset of `ℝ`, every real-valued harmonic function is affine. -/
private theorem exists_affine_eqOn_of_harmonicOnNhd_real {V : Set ℝ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) {h : ℝ → ℝ} (hh : HarmonicOnNhd h V) :
    ∃ a b : ℝ, ∀ y ∈ V, h y = a * y + b := by
  have hc2 : ContDiffOn ℝ 2 h V := hh.contDiffOn
  have hderiv_diff : DifferentiableOn ℝ (deriv h) V :=
    (hc2.deriv_of_isOpen hVo (by norm_num)).differentiableOn one_ne_zero
  have hderiv2 : ∀ y ∈ V, deriv (deriv h) y = 0 := fun y hy ↦ by
    have hΔ := (hh y hy).2.self_of_nhds
    simpa [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one] using hΔ
  obtain ⟨a, ha⟩ := hVo.exists_is_const_of_deriv_eq_zero hVc hderiv_diff hderiv2
  have hg_diff : DifferentiableOn ℝ (fun y ↦ h y - a * y) V :=
    (hc2.differentiableOn (by norm_num)).sub (differentiableOn_const a |>.mul differentiableOn_id)
  have hg_deriv : ∀ y ∈ V, deriv (fun z ↦ h z - a * z) y = 0 := fun y hy ↦ by
    have hhd : DifferentiableAt ℝ h y :=
      ((hc2.differentiableOn (by norm_num)).differentiableAt (hVo.mem_nhds hy))
    have hlin : HasDerivAt (fun z : ℝ ↦ a * z) a y := by
      simpa using (hasDerivAt_id y).const_mul a
    rw [deriv_fun_sub hhd hlin.differentiableAt, hlin.deriv, ha y hy, sub_self]
  obtain ⟨b, hb⟩ := hVo.exists_is_const_of_deriv_eq_zero hVc hg_diff hg_deriv
  exact ⟨a, b, fun y hy ↦ by linarith [hb y hy]⟩

/-- Every affine function on `ℝ` is harmonic everywhere. -/
private theorem harmonicOnNhd_affine_real (a b : ℝ) :
    HarmonicOnNhd (fun y : ℝ ↦ a * y + b) univ := fun x _ ↦ by
  refine ⟨(contDiff_const.mul contDiff_id |>.add contDiff_const).contDiffAt,
    Eventually.of_forall fun y ↦ ?_⟩
  have hd : deriv (fun z : ℝ ↦ a * z + b) = fun _ ↦ a := by
    ext z
    simp
  simp [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, hd]

/-- In dimension `1`, every function harmonic near a filled-in set `K ⊆ Ω` extends to a
function harmonic on all of `Ω` that agrees with `h` on a neighbourhood of `K`. -/
private theorem exists_harmonicOnNhd_real_of_isFilledIn {Ω K : Set ℝ} (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) {h : ℝ → ℝ} (hh : HarmonicOnNhd h K) :
    ∃ H : ℝ → ℝ, HarmonicOnNhd H Ω ∧ H =ᶠ[𝓝ˢ K] h := by
  classical
  let U : Set ℝ := {y | HarmonicAt h y}
  have hUo : IsOpen U := isOpen_setOfPred_harmonicAt (f := h)
  -- For each `x ∈ Ω`, `K ∩ connectedComponentIn Ω x` is order-connected (hence preconnected).
  have hK_preconn : ∀ x ∈ Ω, IsPreconnected (K ∩ connectedComponentIn Ω x) := by
    intro x _
    rw [isPreconnected_iff_ordConnected]
    refine ⟨fun a ha b hb z hz ↦ ?_⟩
    have hC_ord : (connectedComponentIn Ω x).OrdConnected :=
      isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn
    have hzC : z ∈ connectedComponentIn Ω x := hC_ord.out ha.2 hb.2 hz
    refine ⟨?_, hzC⟩
    by_contra hzK
    have hzΩK : z ∈ Ω \ K := ⟨connectedComponentIn_subset Ω x hzC, hzK⟩
    have hD_sub : connectedComponentIn (Ω \ K) z ⊆ Icc a b := by
      intro w hw
      have hD_ord : (connectedComponentIn (Ω \ K) z).OrdConnected :=
        isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn
      refine ⟨?_, ?_⟩
      · by_contra hwa
        have haD : a ∈ connectedComponentIn (Ω \ K) z :=
          hD_ord.out hw (mem_connectedComponentIn hzΩK) ⟨(not_le.1 hwa).le, hz.1⟩
        exact (connectedComponentIn_subset (Ω \ K) z haD).2 ha.1
      · by_contra hbw
        have hbD : b ∈ connectedComponentIn (Ω \ K) z :=
          hD_ord.out (mem_connectedComponentIn hzΩK) hw ⟨hz.2, (not_le.1 hbw).le⟩
        exact (connectedComponentIn_subset (Ω \ K) z hbD).2 hb.1
    have hcl_sub : closure (connectedComponentIn (Ω \ K) z) ⊆ Icc a b :=
      closure_minimal hD_sub isClosed_Icc
    exact isFilledIn_iff.1 hfill z hzΩK ⟨isCompact_Icc.of_isClosed_subset isClosed_closure hcl_sub,
      hcl_sub.trans ((hC_ord.out ha.2 hb.2).trans (connectedComponentIn_subset Ω x))⟩
  -- For each `x ∈ K`, pick an affine function agreeing with `h` on `connectedComponentIn U x`.
  have haff : ∀ x ∈ K, ∃ a b : ℝ, ∀ y ∈ connectedComponentIn U x, h y = a * y + b := fun x _ ↦
    exists_affine_eqOn_of_harmonicOnNhd_real (hUo.connectedComponentIn)
      isPreconnected_connectedComponentIn fun y hy ↦ connectedComponentIn_subset U x hy
  -- Define `H` on each connected component `C = connectedComponentIn Ω y` using a chosen point
  -- of `K ∩ C` (depending only on `C`) when `K ∩ C` is nonempty, and `0` otherwise.
  let H (y : ℝ) : ℝ :=
    if hne : (K ∩ connectedComponentIn Ω y).Nonempty then
      let x₀ := hne.choose
      have hx₀ : x₀ ∈ K := hne.choose_spec.1
      (haff x₀ hx₀).choose * y + (haff x₀ hx₀).choose_spec.choose
    else 0
  have hH_harm : HarmonicOnNhd H Ω := by
    intro y hy
    let C := connectedComponentIn Ω y
    have hCo : IsOpen C := hΩ.connectedComponentIn
    have hCeq : ∀ z ∈ C, connectedComponentIn Ω z = C := fun z hz ↦
      (connectedComponentIn_eq hz).symm
    by_cases hne : (K ∩ C).Nonempty
    · let x₀ := hne.choose
      have hx₀ : x₀ ∈ K := hne.choose_spec.1
      let a := (haff x₀ hx₀).choose
      let b := (haff x₀ hx₀).choose_spec.choose
      have hev : H =ᶠ[𝓝 y] fun z ↦ a * z + b := by
        filter_upwards [hCo.mem_nhds (mem_connectedComponentIn hy)] with z hz
        simp only [H, hCeq z hz, hne, ↓reduceDIte, x₀, a, b]
      exact (harmonicAt_congr_nhds hev).2 (harmonicOnNhd_affine_real a b y (mem_univ y))
    · have hev : H =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hCo.mem_nhds (mem_connectedComponentIn hy)] with z hz
        simp only [H, hCeq z hz, hne, ↓reduceDIte]
      exact (harmonicAt_congr_nhds hev).2 (harmonicOnNhd_const (0 : ℝ) y (mem_univ y))
  refine ⟨H, hH_harm, ?_⟩
  rw [EventuallyEq, eventually_nhdsSet_iff_forall]
  intro x hx
  let C := connectedComponentIn Ω x
  have hCo : IsOpen C := hΩ.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn (hKΩ hx)
  have hne : (K ∩ C).Nonempty := ⟨x, hx, hxC⟩
  let x₀ := hne.choose
  have hx₀K : x₀ ∈ K := hne.choose_spec.1
  have hx₀C : x₀ ∈ C := hne.choose_spec.2
  have hKC_sub : K ∩ C ⊆ connectedComponentIn U x₀ :=
    (hK_preconn x (hKΩ hx)).subset_connectedComponentIn ⟨hx₀K, hx₀C⟩ (inter_subset_left.trans hh)
  have hxU₀ : x ∈ connectedComponentIn U x₀ := hKC_sub ⟨hx, hxC⟩
  have hVo : IsOpen (connectedComponentIn U x₀) := hUo.connectedComponentIn
  filter_upwards [(hCo.inter hVo).mem_nhds ⟨hxC, hxU₀⟩] with y ⟨hyC, hyV⟩
  have hCeq : connectedComponentIn Ω y = C := (connectedComponentIn_eq hyC).symm
  simp only [H, hCeq, hne, ↓reduceDIte]
  exact ((haff x₀ hx₀K).choose_spec.choose_spec y hyV).symm

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
