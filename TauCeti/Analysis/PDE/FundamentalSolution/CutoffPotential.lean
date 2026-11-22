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
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution

/-!
# Distributional kernel potentials of compactly supported cutoffs

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
on `(dsupport T)ᶜ`.

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

/-- The pointwise off-support kernel potential `x ↦ T (y ↦ χ y • G (x - y))` for `x ∉ tsupport χ`,
extended by `0` on `tsupport χ`. -/
def kernelPotentialPairing (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) {G : E → ℝ}
    (hG : HarmonicOnNhd G {0}ᶜ) (x : E) : F :=
  open Classical in
  if hx : x ∉ tsupport (χ : E → ℝ) then
    T (χ.smulOfContDiffOn isOpen_compl_singleton (subset_compl_singleton_iff.2 hx)
      (hG.contDiffOn_sub_right x))
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
      rw [convolution_lsmul_swap, convolution_def]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
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
        (subset_compl_singleton_iff.2 hx') (hG.contDiffOn_sub_right x))
      (fun y ↦ by simp),
    kernelPotentialPairing_eq T hG hx
      (φ := χ.smulOfContDiffOn isOpen_compl_singleton (subset_compl_singleton_iff.2 hx)
        (hG.contDiffOn_sub_right x))
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
  obtain ⟨χ, hχ1, hxχ⟩ := exists_cutoff_notMem_tsupport_of_notMem_dsupport T hc hΩ hx
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
  obtain ⟨χ, hχ1, hxχ⟩ := exists_cutoff_notMem_tsupport_of_notMem_dsupport T hc hΩ hx
  have hx_mem : (tsupport (χ : E → ℝ))ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hxχ
  have hev : T.kernelPotentialOfSupport hG =ᶠ[𝓝 x] T.kernelPotentialPairing χ hG :=
    Set.EqOn.eventuallyEq_of_mem
      (fun _ hx' ↦ kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ1 hG hx') hx_mem
  exact (((contDiffOn_kernelPotentialPairing T χ hG hG_symm).contDiffAt
    hx_mem).congr_of_eventuallyEq hev).contDiffWithinAt

/-- **Jet formula for the cutoff-free potential.** For a cutoff `χ` equal to `1` near `dsupport T`
and `x₀ ∉ tsupport χ`, the iterated directional derivative of `T.kernelPotentialOfSupport hG`
along `vs` pairs `T` with `y ↦ χ y * (∂_{vs} G)(x₀ - y)`. -/
theorem iteratedFDerivAlong_kernelPotentialOfSupport (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x)) {x₀ : E} (hx₀ : x₀ ∉ tsupport (χ : E → ℝ))
    (vs : List E) {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = χ y * iteratedFDerivAlong ℝ vs G (x₀ - y)) :
    iteratedFDerivAlong ℝ vs (T.kernelPotentialOfSupport hG) x₀ = T φ := by
  have hev : T.kernelPotentialOfSupport hG =ᶠ[𝓝 x₀] T.kernelPotentialPairing χ hG :=
    Set.EqOn.eventuallyEq_of_mem
      (fun _ hx' ↦ kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ hG hx')
      ((isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hx₀)
  rw [(hev.iteratedFDerivAlong vs).eq_of_nhds]
  exact iteratedFDerivAlong_kernelPotentialPairing T hG hG_symm hx₀ vs hφ

/-- **Harmonicity of the cutoff-free potential off `dsupport T`.** When `dsupport T` is a compact
subset of `Ω`, `T.kernelPotentialOfSupport hG` is harmonic on `(dsupport T)ᶜ`. -/
theorem harmonicOnNhd_kernelPotentialOfSupport {T : 𝓓'(Ω, F)} (hc : IsCompact (dsupport T))
    (hΩ : dsupport T ⊆ Ω) {G : E → ℝ} (hG : HarmonicOnNhd G {0}ᶜ)
    (hG_symm : ∀ x y, G (x - y) = G (y - x)) :
    HarmonicOnNhd (T.kernelPotentialOfSupport hG) (dsupport T)ᶜ := by
  intro x hx
  obtain ⟨χ, hχ1, hxχ⟩ := exists_cutoff_notMem_tsupport_of_notMem_dsupport T hc hΩ hx
  have hev : T.kernelPotentialOfSupport hG =ᶠ[𝓝 x] T.kernelPotentialPairing χ hG :=
    Set.EqOn.eventuallyEq_of_mem
      (fun _ hx' ↦ kernelPotentialOfSupport_eq_kernelPotentialPairing T hχ1 hG hx')
      ((isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hxχ)
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

end Distribution
