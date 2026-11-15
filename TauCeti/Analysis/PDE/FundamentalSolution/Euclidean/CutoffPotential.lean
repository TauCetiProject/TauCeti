/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Distribution.LineDeriv
public import TauCeti.Analysis.Distribution.TestFunction.Convolution
public import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Convergence
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Multipole
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential

/-!
# Distributional Newtonian potentials and Lax–Malgrange harmonic orthogonality

For a distribution `T : 𝓓'(Ω, F)` on an open subset `Ω ⊆ ℝⁿ` and a smooth cutoff `χ : 𝓓(Ω, ℝ)`,
the **distributional Newtonian potential** `Gₙ ⋆ (χ T)` is defined globally on `ℝⁿ` as the
transpose `T ∘L TestFunction.cutoffConvolutionCLM χ (locallyIntegrable_newtonianKernel n)`, pairing
a test function `φ` on `ℝⁿ` with `T (χ • (Gₙ ⋆ φ))`. In dimensions `n ≥ 3`, where `-Δ Gₙ = δ₀`,
this distribution solves Poisson's equation `-Δ (Gₙ ⋆ (χ T)) = χ T` on `ℝⁿ`: the distributional
Laplacian passes to `φ`, commutes with convolution against `Gₙ`, and evaluates `-Δ (Gₙ ⋆ φ) = φ`.

Away from `tsupport χ`, the translated kernel `y ↦ Gₙ(x - y)` is smooth on a neighbourhood of
`tsupport χ`, giving the pointwise off-support potential

`newtonianPotentialPairing T χ x = T (y ↦ χ y * Gₙ(x - y))`.

Cutting `Gₙ` off away from the origin identifies this function locally with the regularization
`Distribution.translatePairing` of `χ T`, from which smoothness, the jet formula for
`TauCeti.iteratedFDerivAlong`, harmonicity off `tsupport χ`, and the integral representation
`Gₙ ⋆ (χ T) = ∫ φ(x) • newtonianPotentialPairing T χ x dx` on tests disjoint from `tsupport χ`
all follow without manual difference-quotient estimates.

When `dsupport T` is a compact subset of `Ω`, choosing cutoffs equal to `1` near `dsupport T`
glues these pairings into the cutoff-free potential `TauCeti.newtonianPotentialOfSupport T`,
harmonic (hence real analytic for finite-dimensional `F`) on `(dsupport T)ᶜ`. If `dsupport T ⊆ K`
for a compact set `K ⊆ Ω` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`) and `T` annihilates
every test function agreeing near `K` with a function harmonic on `Ω`, then:

* at every `x₀ ∉ Ω`, all iterated derivatives of the potential vanish because the partial
  derivatives of `y ↦ Gₙ(x₀ - y)` are harmonic on `{x₀}ᶜ ⊇ Ω`;
* outside a large ball, the potential vanishes by the exterior multipole expansion
  (`exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_newtonianKernel_sub`);
* every connected component of `Kᶜ` meets either `Ωᶜ` or the exterior of every ball, so unique
  continuation forces the potential to vanish on `Kᶜ`, confining `dsupport (Gₙ ⋆ (χ T))` to `K`;
* in dimensions `n ≥ 3`, testing `-Δ (Gₙ ⋆ (χ T)) = χ T` against a cutoff of any function `h`
  harmonic near `K` shows that `T` also annihilates every test agreeing near `K` with `h`.

This is the PDE duality core of the Lax–Malgrange harmonic Runge approximation theorem.

## Main declarations

* `TauCeti.newtonianPotentialDistribution`: the global distribution `Gₙ ⋆ (χ T)` on `ℝⁿ`.
* `TauCeti.laplacianCLM_newtonianPotentialDistribution`: for `n ≥ 3`, `-Δ (Gₙ ⋆ (χ T)) = χ T`.
* `TauCeti.newtonianPotentialPairing`: the pointwise pairing `x ↦ T (y ↦ χ y * Gₙ(x - y))` off
  `tsupport χ`.
* `TauCeti.harmonicOnNhd_newtonianPotentialPairing`,
  `TauCeti.newtonianPotentialDistribution_apply_eq_integral`: off-support harmonicity and integral
  representation of `Gₙ ⋆ (χ T)`.
* `TauCeti.newtonianPotentialOfSupport`, `TauCeti.harmonicOnNhd_newtonianPotentialOfSupport`:
  the cutoff-free potential on `(dsupport T)ᶜ` for compactly supported `T`.
* `TauCeti.newtonianPotentialOfSupport_eq_zero_of_isFilledIn`,
  `TauCeti.dsupport_newtonianPotentialDistribution_subset_of_isFilledIn`: vanishing of the
  potential on `Kᶜ` and confinement of the distributional support to `K`.
* `TauCeti.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd`: Lax–Malgrange harmonic orthogonality in
  dimensions `n ≥ 3`.

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

open Bornology ContinuousLinearMap Distribution Filter Function InnerProductSpace Laplacian
open LineDeriv MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions Pointwise Topology

namespace TauCeti

section CutoffTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-- Multiply a test function `χ : 𝓓(Ω, ℝ)` by a scalar function `g` smooth on an open
neighbourhood `U` of `tsupport χ`, packaged as a test function in `𝓓(Ω, ℝ)`. -/
private def cutoffMulTestFunction (χ : 𝓓(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) : 𝓓(Ω, ℝ) where
  toFun y := χ y * g y
  contDiff' := contDiff_of_contDiffOn_union_of_isOpen (χ.contDiff.contDiffOn.mul hg)
    ((contDiffOn_const (c := (0 : ℝ))).congr fun _ hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport (f := (χ : E → ℝ)) hy])
    (eq_univ_of_forall fun y ↦ (em (y ∈ tsupport (χ : E → ℝ))).imp (hχU ·) id)
    hU (isClosed_tsupport (χ : E → ℝ)).isOpen_compl
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := tsupport_mul_subset_left.trans χ.tsupport_subset

@[simp]
private theorem cutoffMulTestFunction_apply (χ : 𝓓(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (y : E) :
    cutoffMulTestFunction χ hU hχU hg y = χ y * g y :=
  rfl

private theorem tsupport_cutoffMulTestFunction_subset (χ : 𝓓(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    tsupport (cutoffMulTestFunction χ hU hχU hg : E → ℝ) ⊆ tsupport (χ : E → ℝ) :=
  tsupport_mul_subset_left

omit [NormedSpace ℝ E] in
private theorem tsupport_subset_compl_singleton {α : Type*} [Zero α] {f : E → α} {x : E}
    (hx : x ∉ tsupport f) : tsupport f ⊆ {x}ᶜ :=
  fun _ hy (hxy : _ = x) ↦ hx (hxy ▸ hy)

/-- Pointwise Leibniz bound for the `k`-th derivative of `cutoffMulTestFunction χ g₁ -
cutoffMulTestFunction χ g₂`. -/
private theorem norm_iteratedFDeriv_cutoffMulTestFunction_sub_le (χ : 𝓓(Ω, ℝ)) {U : Set E}
    (hU : IsOpen U) (hχU : tsupport (χ : E → ℝ) ⊆ U) {g₁ g₂ : E → ℝ}
    (hg₁ : ContDiffOn ℝ ∞ g₁ U) (hg₂ : ContDiffOn ℝ ∞ g₂ U) {M : ℕ → ℝ}
    (hM0 : ∀ j, 0 ≤ M j) (hM : ∀ j y, ‖iteratedFDeriv ℝ j (χ : E → ℝ) y‖ ≤ M j)
    {k : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hg_le : ∀ j ∈ Finset.range (k + 1), ∀ y ∈ tsupport (χ : E → ℝ),
      ‖iteratedFDeriv ℝ (k - j) g₁ y - iteratedFDeriv ℝ (k - j) g₂ y‖ ≤ δ)
    (y : E) :
    ‖iteratedFDeriv ℝ k (cutoffMulTestFunction χ hU hχU hg₁ : E → ℝ) y -
        iteratedFDeriv ℝ k (cutoffMulTestFunction χ hU hχU hg₂ : E → ℝ) y‖ ≤
      (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M j) * δ := by
  let ψ₁ := cutoffMulTestFunction χ hU hχU hg₁
  let ψ₂ := cutoffMulTestFunction χ hU hχU hg₂
  rw [← iteratedFDeriv_sub_apply (ψ₁.contDiff.contDiffAt.of_le (by simp))
    (ψ₂.contDiff.contDiffAt.of_le (by simp))]
  by_cases hy : y ∈ tsupport (χ : E → ℝ)
  · have hsub_eq : ((ψ₁ : E → ℝ) - (ψ₂ : E → ℝ)) = fun z ↦ χ z * ((g₁ - g₂) z) := by
      ext z
      simp [ψ₁, ψ₂, mul_sub]
    have hyU : y ∈ U := hχU hy
    have hle := norm_iteratedFDerivWithin_mul_le χ.contDiff.contDiffOn (hg₁.sub hg₂)
      hU.uniqueDiffOn hyU (n := k) (mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen k hU hyU] at hle
    rw [hsub_eq]
    refine hle.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    rw [iteratedFDerivWithin_of_isOpen j hU hyU, iteratedFDerivWithin_of_isOpen (k - j) hU hyU,
      show (fun x ↦ g₁ x - g₂ x) = g₁ - g₂ from rfl,
      iteratedFDeriv_sub_apply ((hg₁.contDiffAt (hU.mem_nhds hyU)).of_le (by simp))
        ((hg₂.contDiffAt (hU.mem_nhds hyU)).of_le (by simp)), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hM j y) (hg_le j hj y hy) (norm_nonneg _) (hM0 j))
      (Nat.cast_nonneg _)
  · have h0 : ((ψ₁ : E → ℝ) - (ψ₂ : E → ℝ)) =ᶠ[𝓝 y] 0 := by
      filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hy] with z hz
      simp [ψ₁, ψ₂, image_eq_zero_of_notMem_tsupport hz]
    rw [(h0.iteratedFDeriv ℝ k).eq_of_nhds]
    simpa using mul_nonneg (Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hM0 j)) hδ0

/-- Uniform convergence of all derivatives of `g i` to `g₀` on `tsupport χ` implies convergence of
`χ • g i` to `χ • g₀` in the LF topology of `𝓓(Ω, ℝ)`. -/
private theorem tendsto_cutoffMulTestFunction {ι : Type*} {l : Filter ι} (χ : 𝓓(Ω, ℝ))
    {U : Set E} (hU : IsOpen U) (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : ι → E → ℝ} {g₀ : E → ℝ}
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    (hlim : ∀ k : ℕ, TendstoUniformlyOn (fun i ↦ iteratedFDeriv ℝ k (g i))
      (iteratedFDeriv ℝ k g₀) l (tsupport (χ : E → ℝ))) :
    Tendsto (fun i ↦ cutoffMulTestFunction χ hU hχU (hg i)) l
      (𝓝 (cutoffMulTestFunction χ hU hχU hg₀)) := by
  refine TestFunction.tendsto_of_tendstoUniformly_iteratedFDeriv χ.hasCompactSupport
    χ.tsupport_subset (fun i ↦ tsupport_cutoffMulTestFunction_subset χ hU hχU (hg i)) fun k _ ↦ ?_
  have hχb (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖iteratedFDeriv ℝ j (χ : E → ℝ) y‖ ≤ M := by
    obtain ⟨M, hM⟩ := (χ.hasCompactSupport.iteratedFDeriv j).exists_bound_of_continuous
      (χ.contDiff.continuous_iteratedFDeriv (by simp))
    exact ⟨max M 0, le_max_right _ _, fun y ↦ (hM y).trans (le_max_left _ _)⟩
  choose M hM0 hM using hχb
  set C : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M j + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hM0 j)) zero_lt_one
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hev : ∀ᶠ i in l, ∀ j ∈ Finset.range (k + 1), ∀ y ∈ tsupport (χ : E → ℝ),
      ‖iteratedFDeriv ℝ (k - j) (g i) y - iteratedFDeriv ℝ (k - j) g₀ y‖ < ε / C := by
    rw [Filter.eventually_all_finset]
    intro j _
    simpa [dist_eq_norm, norm_sub_rev] using
      Metric.tendstoUniformlyOn_iff.1 (hlim (k - j)) (ε / C) (div_pos hε hC)
  filter_upwards [hev] with i hi y
  rw [dist_eq_norm, norm_sub_rev]
  refine (norm_iteratedFDeriv_cutoffMulTestFunction_sub_le χ hU hχU (hg i) hg₀ hM0 hM
    (div_pos hε hC).le (fun j hj z hz ↦ (hi j hj z hz).le) y).trans_lt ?_
  exact (mul_lt_mul_of_pos_right (lt_add_one _) (div_pos hε hC)).trans_eq
    (mul_div_cancel₀ ε hC.ne')

end CutoffTestFunction

section Potential

variable {n : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The global distributional Newtonian potential `Gₙ ⋆ (χ T)` on `ℝⁿ`, pairing a test function
`φ` with `T (χ • (Gₙ ⋆ φ))`. -/
def newtonianPotentialDistribution (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) :
    𝓓'((⊤ : Opens (EuclideanSpace ℝ (Fin n))), F) :=
  (T : 𝓓(Ω, ℝ) →L[ℝ] F) ∘L
    χ.cutoffConvolutionCLM (Ω' := ⊤) (F := ℝ) (locallyIntegrable_newtonianKernel n)

@[simp]
theorem newtonianPotentialDistribution_apply (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    newtonianPotentialDistribution T χ φ =
      T (χ.cutoffConvolutionCLM (locallyIntegrable_newtonianKernel n) φ) := by
  rfl

/-- Cutoffs equal to `1` near `dsupport T` define the same distributional Newtonian potential. -/
theorem newtonianPotentialDistribution_congr (T : 𝓓'(Ω, F)) {χ₁ χ₂ : 𝓓(Ω, ℝ)}
    (hχ₁ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ₁ y = 1) (hχ₂ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ₂ y = 1) :
    newtonianPotentialDistribution T χ₁ = newtonianPotentialDistribution T χ₂ := by
  ext φ
  rw [newtonianPotentialDistribution_apply, newtonianPotentialDistribution_apply]
  refine Distribution.map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ₁, hχ₂] with y h₁ h₂
  simp [h₁, h₂]

/-- **Poisson's equation for the distributional Newtonian potential.** In dimensions `n ≥ 3`,
`-Δ (Gₙ ⋆ (χ T)) = χ T` on `ℝⁿ`. -/
theorem laplacianCLM_newtonianPotentialDistribution (hn : 3 ≤ n) (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    laplacianCLM ℝ (EuclideanSpace ℝ (Fin n)) _ (newtonianPotentialDistribution T χ) φ =
      -T (TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) φ) := by
  rw [Distribution.laplacianCLM_apply_apply, newtonianPotentialDistribution_apply, ← map_neg]
  congr 1
  ext y
  let Δφ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
    laplacianCLM ℝ (EuclideanSpace ℝ (Fin n)) _ φ
  have hconv : (newtonianKernel n ⋆ (Δφ : _ → ℝ)) y = -φ y := by
    have hΔ : (Δφ : EuclideanSpace ℝ (Fin n) → ℝ) = Δ (φ : _ → ℝ) :=
      funext (TestFunction.laplacianCLM_apply φ)
    rw [hΔ, ← φ.hasCompactSupport.laplacian_convolution_right (lsmul ℝ ℝ)
      (locallyIntegrable_newtonianKernel n) (φ.contDiff.of_le (by simp)),
      laplacian_newtonianKernel_convolution hn (φ.contDiff.of_le (by simp)) φ.hasCompactSupport,
      Pi.neg_apply]
  simp [Δφ, hconv]

/-- For fixed `x`, any iterated directional derivative `y ↦ (∂_{vs} Gₙ)(x - y)` of the Newtonian
kernel is harmonic away from `x`. -/
private theorem harmonicOnNhd_iteratedFDerivAlong_newtonianKernel_sub_right
    (vs : List (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    HarmonicOnNhd (fun y ↦ iteratedFDerivAlong ℝ vs (newtonianKernel n) (x - y)) {x}ᶜ := by
  intro y hy
  have hxy : -(y - x) ≠ 0 := neg_ne_zero.2 (sub_ne_zero.2 (mem_compl_singleton_iff.1 hy))
  have h₀ : HarmonicAt (iteratedFDerivAlong ℝ vs (newtonianKernel n)) (-(y - x)) :=
    (harmonicAt_newtonianKernel n hxy).iteratedFDerivAlong vs
  have h₁ : HarmonicAt
      ((iteratedFDerivAlong ℝ vs (newtonianKernel n)) ∘ LinearIsometryEquiv.neg ℝ) (y - x) :=
    (harmonicAt_comp_linearIsometryEquiv_right_iff (LinearIsometryEquiv.neg ℝ)).2 h₀
  have h₂ : HarmonicAt
      (fun z ↦ iteratedFDerivAlong ℝ vs (newtonianKernel n) (-(z + -x))) y :=
    (harmonicAt_comp_add_right_iff (x := y) (a := -x)).2 h₁
  simpa [sub_eq_add_neg] using h₂

private theorem contDiffOn_newtonianKernel_sub_right (x : EuclideanSpace ℝ (Fin n)) :
    ContDiffOn ℝ ∞ (fun y ↦ newtonianKernel n (x - y)) {x}ᶜ := by
  simpa using (harmonicOnNhd_iteratedFDerivAlong_newtonianKernel_sub_right [] x
    ).analyticOnNhd.contDiffOn isOpen_compl_singleton.uniqueDiffOn

/-- The pointwise off-support Newtonian potential `x ↦ T (y ↦ χ y * Gₙ(x - y))` for
`x ∉ tsupport χ`, extended by `0` on `tsupport χ`. -/
def newtonianPotentialPairing (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) (x : EuclideanSpace ℝ (Fin n)) : F :=
  open Classical in
  if hx : x ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) then
    T (cutoffMulTestFunction χ isOpen_compl_singleton (tsupport_subset_compl_singleton hx)
      (contDiffOn_newtonianKernel_sub_right x))
  else 0

/-- At `x ∉ tsupport χ`, `newtonianPotentialPairing` is `T` applied to any test function equal to
`y ↦ χ y * Gₙ(x - y)`. -/
theorem newtonianPotentialPairing_eq (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)) {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = χ y * newtonianKernel n (x - y)) :
    newtonianPotentialPairing T χ x = T φ := by
  unfold newtonianPotentialPairing
  rw [dite_eq_left_of_eq_true (eq_true hx)]
  congr 1
  ext y
  rw [cutoffMulTestFunction_apply, hφ]

/-- Extend `χ T` by zero to a distribution on `ℝⁿ`. -/
private def cutoffGlobalDistribution (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) :
    𝓓'((⊤ : Opens (EuclideanSpace ℝ (Fin n))), F) :=
  (T : 𝓓(Ω, ℝ) →L[ℝ] F) ∘L
    TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset)

@[simp]
private theorem cutoffGlobalDistribution_apply (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ))
    (ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    cutoffGlobalDistribution T χ ψ =
      T (TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) ψ) :=
  rfl

/-- Given a compact set `K` disjoint from `tsupport χ`, cut off `Gₙ` away from `0` to obtain a test
function `ρ` on `ℝⁿ` with `ρ (y - z) = Gₙ(z - y)` for all `y ∈ tsupport χ` and `z` near `K`. -/
private theorem exists_kernelTestFunction_of_disjoint (χ : 𝓓(Ω, ℝ))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hdisj : Disjoint K (tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))) :
    ∃ ρ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      ∀ y ∈ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ), ∀ x ∈ K,
        (fun z ↦ ρ (y - z)) =ᶠ[𝓝 x] fun z ↦ newtonianKernel n (z - y) := by
  let S : Set (EuclideanSpace ℝ (Fin n)) := tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) - K
  have hS : IsCompact S := by
    simpa only [S, sub_eq_add_neg] using IsCompact.add χ.hasCompactSupport hK.neg
  have hS0 : S ⊆ {0}ᶜ := by
    rintro _ ⟨y, hy, x, hx, hyx⟩ h0
    rw [mem_singleton_iff] at h0
    exact hdisj.le_bot ⟨hx, (sub_eq_zero.1 (hyx.trans h0)) ▸ hy⟩
  obtain ⟨η, -, hη1, hη0⟩ := TestFunction.exists_cutoff_tsupport_subset
    (Ω := (⊤ : Opens (EuclideanSpace ℝ (Fin n)))) (n := ⊤) hS isOpen_compl_singleton hS0
    (subset_univ _)
  let ρ := cutoffMulTestFunction η isOpen_compl_singleton hη0
    ((harmonicOnNhd_newtonianKernel n).analyticOnNhd.contDiffOn
      isOpen_compl_singleton.uniqueDiffOn)
  obtain ⟨W, hWo, hSW, hηW⟩ := mem_nhdsSet_iff_exists.1 hη1
  refine ⟨ρ, fun y hy x hx ↦ ?_⟩
  have hyx : y - x ∈ W := hSW ⟨y, hy, x, hx, rfl⟩
  filter_upwards [(hWo.preimage (continuous_const.sub continuous_id)).mem_nhds hyx] with z hz
  have hηz : η (y - z) = 1 := hηW hz
  simp [ρ, hηz, newtonianKernel_sub_comm]

/-- On any compact set `K` disjoint from `tsupport χ`, `newtonianPotentialPairing` agrees with the
global regularization `(cutoffGlobalDistribution T χ).translatePairing ρ`. -/
private theorem exists_translatePairing_eqOn_of_disjoint (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hdisj : Disjoint K (tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))) :
    ∃ ρ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∀ y ∈ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ), ∀ x ∈ K,
        (fun z ↦ ρ (y - z)) =ᶠ[𝓝 x] fun z ↦ newtonianKernel n (z - y)) ∧
      EqOn ((cutoffGlobalDistribution T χ).translatePairing ρ)
        (newtonianPotentialPairing T χ) K := by
  obtain ⟨ρ, hρ⟩ := exists_kernelTestFunction_of_disjoint χ hK hdisj
  refine ⟨ρ, hρ, fun x hx ↦ ?_⟩
  have hxχ : x ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    Disjoint.notMem_of_mem_left hdisj hx
  let ψ := translateTestFunction (Omega := (⊤ : Opens (EuclideanSpace ℝ (Fin n)))) (h := x)
    (fun _ _ ↦ trivial) ρ
  rw [Distribution.translatePairing_eq _ (φ := ψ) (translateTestFunction_apply _ ρ),
    cutoffGlobalDistribution_apply, newtonianPotentialPairing_eq T hxχ
      (φ := TestFunction.cutoffCLM χ.contDiff
        (inter_subset_left.trans χ.tsupport_subset) ψ) fun y ↦ by
      rw [TestFunction.cutoffCLM_apply, smul_eq_mul]
      by_cases hy : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)
      · have hψy : ψ y = ρ (y - x) := translateTestFunction_apply _ ρ y
        have hρx : ρ (y - x) = newtonianKernel n (x - y) := (hρ y hy x hx).self_of_nhds
        rw [hψy, hρx]
      · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]]

/-- **Smoothness of the off-support Newtonian potential.** `newtonianPotentialPairing T χ` is
smooth on `(tsupport χ)ᶜ`. -/
theorem contDiffOn_newtonianPotentialPairing (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) :
    ContDiffOn ℝ ∞ (newtonianPotentialPairing T χ)
      (tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))ᶜ := by
  have hopen := (isClosed_tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)).isOpen_compl
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ ↦ ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x₀ hx₀
  have hcb : closedBall x₀ (r / 2) ⊆ (tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))ᶜ :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨ρ, -, hEq⟩ := exists_translatePairing_eqOn_of_disjoint T χ
    (isCompact_closedBall x₀ (r / 2)) (Set.disjoint_left.2 fun _ h₁ h₂ ↦ hcb h₁ h₂)
  refine ⟨ball x₀ (r / 2), isOpen_ball, mem_ball_self (half_pos hr), ?_⟩
  refine (((cutoffGlobalDistribution T χ).contDiffOn_translatePairing ρ).mono
    fun _ _ ↦ mapsTo_univ _ _).congr fun x hx ↦ ?_
  exact (hEq (ball_subset_closedBall hx.2)).symm

/-- Package `y ↦ iteratedFDerivAlong ℝ vs (fun z ↦ ρ (y - z)) x₀` as a global test function on
`ℝⁿ`. -/
private def translateIteratedFDerivAlongTestFunction
    (ρ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (vs : List (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) where
  toFun y := iteratedFDerivAlong ℝ vs (fun z ↦ ρ (y - z)) x₀
  contDiff' := by
    let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      0 - ContinuousLinearMap.id ℝ _
    have h : (fun y ↦ iteratedFDerivAlong ℝ vs (fun z ↦ ρ (y - z)) x₀) =
        fun y ↦ iteratedFDerivAlong ℝ (vs.map L) (ρ : _ → ℝ) (y - x₀) := by
      ext y
      exact iteratedFDerivAlong_comp_of_hasFDerivAt
        (fun z ↦ (hasFDerivAt_const y z).sub (hasFDerivAt_id z))
        ρ.contDiff vs (by simp) x₀
    rw [h]
    exact (ρ.contDiff.iteratedFDerivAlong _ (by simp)).comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := by
    let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      0 - ContinuousLinearMap.id ℝ _
    have hg : HasCompactSupport (iteratedFDerivAlong ℝ (vs.map L) (ρ : _ → ℝ)) := by
      refine HasCompactSupport.of_support_subset_isCompact ρ.hasCompactSupport fun w hw ↦ ?_
      contrapose hw
      rw [Function.mem_support, not_not]
      have h0 : (ρ : _ → ℝ) =ᶠ[𝓝 w] 0 := by
        filter_upwards [(isClosed_tsupport (ρ : _ → ℝ)).isOpen_compl.mem_nhds hw] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      exact iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero h0 _
    have h : (fun y ↦ iteratedFDerivAlong ℝ vs (fun z ↦ ρ (y - z)) x₀) =
        (iteratedFDerivAlong ℝ (vs.map L) (ρ : _ → ℝ)) ∘ Homeomorph.addRight (-x₀) := by
      ext y
      change iteratedFDerivAlong ℝ vs (fun z ↦ ρ (y - z)) x₀ =
        iteratedFDerivAlong ℝ (vs.map L) (ρ : _ → ℝ) (y + -x₀)
      rw [← sub_eq_add_neg]
      exact iteratedFDerivAlong_comp_of_hasFDerivAt
        (fun z ↦ (hasFDerivAt_const y z).sub (hasFDerivAt_id z))
        ρ.contDiff vs (by simp) x₀
    rw [h]
    exact hg.comp_homeomorph (Homeomorph.addRight (-x₀))
  tsupport_subset' := subset_univ _

/-- **Jet formula for the off-support Newtonian potential.** At `x₀ ∉ tsupport χ`, the iterated
directional derivative of `newtonianPotentialPairing T χ` along `vs` pairs `T` with
`y ↦ χ y * (∂_{vs} Gₙ)(x₀ - y)`. -/
theorem iteratedFDerivAlong_newtonianPotentialPairing (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))
    (vs : List (EuclideanSpace ℝ (Fin n))) {φ : 𝓓(Ω, ℝ)}
    (hφ : ∀ y, φ y = χ y * iteratedFDerivAlong ℝ vs (newtonianKernel n) (x₀ - y)) :
    iteratedFDerivAlong ℝ vs (newtonianPotentialPairing T χ) x₀ = T φ := by
  have hopen := (isClosed_tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)).isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x₀ hx₀
  have hcb : closedBall x₀ (r / 2) ⊆ (tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))ᶜ :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨ρ, hρ, hEq⟩ := exists_translatePairing_eqOn_of_disjoint T χ
    (isCompact_closedBall x₀ (r / 2)) (Set.disjoint_left.2 fun _ h₁ h₂ ↦ hcb h₁ h₂)
  have hev : newtonianPotentialPairing T χ =ᶠ[𝓝 x₀]
      (cutoffGlobalDistribution T χ).translatePairing ρ := by
    filter_upwards [ball_mem_nhds x₀ (half_pos hr)] with x hx
    exact (hEq (ball_subset_closedBall hx)).symm
  let ψ := translateIteratedFDerivAlongTestFunction ρ vs x₀
  rw [(hev.iteratedFDerivAlong vs).eq_of_nhds,
    (cutoffGlobalDistribution T χ).iteratedFDerivAlong_translatePairing_eq
      (mapsTo_univ _ _) vs (φ := ψ) (fun _ ↦ rfl),
    cutoffGlobalDistribution_apply]
  congr 1
  ext y
  rw [TestFunction.cutoffCLM_apply, hφ]
  by_cases hy : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)
  · have hev_y := hρ y hy x₀ (mem_closedBall_self (half_pos hr).le)
    simp only [ψ, translateIteratedFDerivAlongTestFunction, TestFunction.coe_mk, smul_eq_mul,
      (hev_y.iteratedFDerivAlong vs).eq_of_nhds, iteratedFDerivAlong_comp_sub]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Harmonicity of the off-support Newtonian potential.** `newtonianPotentialPairing T χ` is
harmonic on `(tsupport χ)ᶜ` in every dimension. -/
theorem harmonicOnNhd_newtonianPotentialPairing (T : 𝓓'(Ω, F)) (χ : 𝓓(Ω, ℝ)) :
    HarmonicOnNhd (newtonianPotentialPairing T χ)
      (tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))ᶜ := by
  have hopen := (isClosed_tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)).isOpen_compl
  have hsmooth := contDiffOn_newtonianPotentialPairing T χ
  intro x₀ hx₀
  refine ⟨(hsmooth.contDiffAt (hopen.mem_nhds hx₀)).of_le (by simp), ?_⟩
  filter_upwards [hopen.mem_nhds hx₀] with x hx
  set b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  have hcx : ContDiffAt ℝ ∞ (newtonianPotentialPairing T χ) x :=
    hsmooth.contDiffAt (hopen.mem_nhds hx)
  let φ (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) : 𝓓(Ω, ℝ) :=
    cutoffMulTestFunction χ isOpen_compl_singleton (tsupport_subset_compl_singleton hx)
      ((harmonicOnNhd_iteratedFDerivAlong_newtonianKernel_sub_right [b i, b i] x
        ).analyticOnNhd.contDiffOn isOpen_compl_singleton.uniqueDiffOn)
  have hsum : ∑ i, φ i = 0 := by
    ext y
    rw [_root_.sum_apply, FunLike.coe_zero, Pi.zero_apply]
    simp only [φ, cutoffMulTestFunction_apply, ← Finset.mul_sum]
    by_cases hy : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    · have hxy : x - y ≠ 0 := sub_ne_zero.2 fun h ↦ hx (h ▸ hy)
      have hG : ContDiffAt ℝ 2 (newtonianKernel n) (x - y) :=
        (contDiffAt_newtonianKernel n hxy).of_le (by simp)
      have hΔ : ∑ i, iteratedFDerivAlong ℝ [b i, b i] (newtonianKernel n) (x - y) =
          Δ (newtonianKernel n) (x - y) := by
        rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simpa using hG.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv ![b i, b i]
      rw [hΔ, laplacian_newtonianKernel n hxy, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  calc ∑ i, iteratedFDeriv ℝ 2 (newtonianPotentialPairing T χ) x ![b i, b i]
      = ∑ i, iteratedFDerivAlong ℝ [b i, b i] (newtonianPotentialPairing T χ) x := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simpa using ((hcx.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
          ).iteratedFDerivAlong_ofFn_eq_iteratedFDeriv ![b i, b i]).symm
    _ = ∑ i, T (φ i) := Finset.sum_congr rfl fun i _ ↦
        iteratedFDerivAlong_newtonianPotentialPairing T hx [b i, b i] (fun _ ↦ rfl)
    _ = 0 := by rw [← map_sum, hsum, map_zero]

/-- **Integral representation of the distributional Newtonian potential.** On test functions `φ`
whose support is disjoint from `tsupport χ`, `Gₙ ⋆ (χ T)` is represented by integrating against
`newtonianPotentialPairing T χ`. -/
theorem newtonianPotentialDistribution_apply_eq_integral [CompleteSpace F] (T : 𝓓'(Ω, F))
    (χ : 𝓓(Ω, ℝ)) {φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)}
    (hdisj : Disjoint (tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ))
      (tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ))) :
    newtonianPotentialDistribution T χ φ =
      ∫ x, φ x • newtonianPotentialPairing T χ x := by
  obtain ⟨ρ, hρ, hEq⟩ := exists_translatePairing_eqOn_of_disjoint T χ φ.hasCompactSupport hdisj
  let ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
    ⟨(φ : _ → ℝ) ⋆[lsmul ℝ ℝ, volume] (ρ : _ → ℝ),
      ρ.hasCompactSupport.contDiff_convolution_right (lsmul ℝ ℝ)
        φ.contDiff.continuous.locallyIntegrable ρ.contDiff,
      φ.hasCompactSupport.convolution (lsmul ℝ ℝ) ρ.hasCompactSupport, subset_univ _⟩
  have hφint : Integrable (φ : EuclideanSpace ℝ (Fin n) → ℝ) volume :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hmatch : χ.cutoffConvolutionCLM (locallyIntegrable_newtonianKernel n) φ =
      TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) ψ := by
    ext y
    simp only [TestFunction.cutoffConvolutionCLM_apply, TestFunction.cutoffCLM_apply, ψ,
      TestFunction.coe_mk]
    by_cases hy : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    · congr 1
      rw [convolution_def, convolution_def, ← integral_sub_left_eq_self _ volume y]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      dsimp only
      rw [sub_sub_cancel]
      by_cases hx : x ∈ tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      · simp [(hρ y hy x hx).self_of_nhds, newtonianKernel_sub_comm, mul_comm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have happ : T (TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) ψ) =
      cutoffGlobalDistribution T χ ψ := rfl
  rw [newtonianPotentialDistribution_apply, hmatch, happ,
    (cutoffGlobalDistribution T χ).apply_eq_integral_smul_translatePairing ρ hφint
      φ.hasCompactSupport (fun _ _ ↦ mapsTo_univ _ _) (ψ := ψ) rfl]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  by_cases hx : x ∈ tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ)
  · rw [hEq hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-! ### Cutoff-free potential on `(dsupport T)ᶜ` and unique continuation -/

/-- The cutoff-free off-support Newtonian potential of `T` at `x`: defined by choosing any cutoff
`χ : 𝓓(Ω, ℝ)` equal to `1` near `dsupport T` with `x ∉ tsupport χ`, and `0` when none exists. -/
def newtonianPotentialOfSupport (T : 𝓓'(Ω, F)) (x : EuclideanSpace ℝ (Fin n)) : F :=
  open Classical in
  if h : ∃ χ : 𝓓(Ω, ℝ),
      (∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) ∧ x ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) then
    newtonianPotentialPairing T h.choose x
  else 0

/-- For any cutoff `χ : 𝓓(Ω, ℝ)` equal to `1` near `dsupport T` and any `x ∉ tsupport χ`,
`newtonianPotentialOfSupport T x` agrees with `newtonianPotentialPairing T χ x`. -/
theorem newtonianPotentialOfSupport_eq_pairing (T : 𝓓'(Ω, F)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)) :
    newtonianPotentialOfSupport T x = newtonianPotentialPairing T χ x := by
  have hex : ∃ χ' : 𝓓(Ω, ℝ),
      (∀ᶠ y in 𝓝ˢ (dsupport T), χ' y = 1) ∧
        x ∉ tsupport (χ' : EuclideanSpace ℝ (Fin n) → ℝ) :=
    ⟨χ, hχ, hx⟩
  simp only [newtonianPotentialOfSupport, hex, ↓reduceDIte]
  obtain ⟨hχ', hx'⟩ := hex.choose_spec
  rw [newtonianPotentialPairing_eq T hx'
      (φ := cutoffMulTestFunction hex.choose isOpen_compl_singleton
        (tsupport_subset_compl_singleton hx') (contDiffOn_newtonianKernel_sub_right x))
      (fun _ ↦ rfl),
    newtonianPotentialPairing_eq T hx
      (φ := cutoffMulTestFunction χ isOpen_compl_singleton (tsupport_subset_compl_singleton hx)
        (contDiffOn_newtonianKernel_sub_right x)) (fun _ ↦ rfl)]
  refine Distribution.map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ', hχ] with y h₁ h₂
  simp [h₁, h₂]

/-- If `dsupport T` is a compact subset of `Ω`, every `x ∉ dsupport T` admits a cutoff equal to `1`
near `dsupport T` whose support misses `x`. -/
private theorem exists_cutoff_notMem_tsupport_of_notMem_dsupport {T : 𝓓'(Ω, F)}
    (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ dsupport T) :
    ∃ χ : 𝓓(Ω, ℝ),
      (∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1) ∧ x ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) := by
  obtain ⟨χ, -, hχ1, hχs⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤) hc
    (Ω.isOpen.inter isOpen_compl_singleton)
    (subset_inter hΩ fun _ hy (hxy : _ = x) ↦ hx (hxy ▸ hy)) inter_subset_left
  exact ⟨χ, hχ1, fun hxχ ↦ (hχs hxχ).2 rfl⟩

/-- **Harmonicity of the cutoff-free potential off `dsupport T`.** When `dsupport T` is a compact
subset of `Ω`, `newtonianPotentialOfSupport T` is harmonic on `(dsupport T)ᶜ`. -/
theorem harmonicOnNhd_newtonianPotentialOfSupport {T : 𝓓'(Ω, F)}
    (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω) :
    HarmonicOnNhd (newtonianPotentialOfSupport T) (dsupport T)ᶜ := by
  intro x hx
  obtain ⟨χ, hχ1, hxχ⟩ := exists_cutoff_notMem_tsupport_of_notMem_dsupport hc hΩ hx
  have hev : newtonianPotentialOfSupport T =ᶠ[𝓝 x] newtonianPotentialPairing T χ := by
    filter_upwards [(isClosed_tsupport (χ : _ → ℝ)).isOpen_compl.mem_nhds hxχ] with z hz
    exact newtonianPotentialOfSupport_eq_pairing T hχ1 hz
  exact (harmonicAt_congr_nhds hev).2 (harmonicOnNhd_newtonianPotentialPairing T χ x hxχ)

/-- On tests disjoint from `dsupport T`, `newtonianPotentialDistribution` is the integral against
the cutoff-free potential `newtonianPotentialOfSupport`. -/
theorem newtonianPotentialDistribution_apply_eq_integral_ofSupport [CompleteSpace F]
    {T : 𝓓'(Ω, F)} {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1)
    {φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)}
    (hdisj : Disjoint (tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ)) (dsupport T)) :
    newtonianPotentialDistribution T χ φ =
      ∫ x, φ x • newtonianPotentialOfSupport T x := by
  obtain ⟨hc, hΩ⟩ := Distribution.isCompact_dsupport_and_subset_of_eventually_eq_one hχ
  obtain ⟨χ', -, hχ'1, hχ's⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤) hc
    (Ω.isOpen.inter (isClosed_tsupport (φ : _ → ℝ)).isOpen_compl)
    (subset_inter hΩ hdisj.symm.subset_compl_right) inter_subset_left
  have hdisj' : Disjoint (tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ))
      (tsupport (χ' : EuclideanSpace ℝ (Fin n) → ℝ)) :=
    Disjoint.symm (Set.disjoint_left.2 fun _ hy hyφ ↦ (hχ's hy).2 hyφ)
  rw [newtonianPotentialDistribution_congr T hχ hχ'1,
    newtonianPotentialDistribution_apply_eq_integral T χ' hdisj']
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  by_cases hx : x ∈ tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ)
  · rw [newtonianPotentialOfSupport_eq_pairing T hχ'1
      (Disjoint.notMem_of_mem_left hdisj' hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- At any point `x₀ ∉ Ω`, if `T` vanishes on tests agreeing near `K` with functions harmonic on
`Ω`, then `newtonianPotentialOfSupport T` vanishes on a neighbourhood of `x₀`. -/
private theorem eventuallyEq_zero_newtonianPotentialOfSupport_of_notMem [FiniteDimensional ℝ F]
    {T : 𝓓'(Ω, F)} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hTK : dsupport T ⊆ K)
    (hT : ∀ (H : EuclideanSpace ℝ (Fin n) → ℝ) (ψ : 𝓓(Ω, ℝ)),
      HarmonicOnNhd H Ω → ((ψ : _ → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∉ (Ω : Set (EuclideanSpace ℝ (Fin n)))) :
    newtonianPotentialOfSupport T =ᶠ[𝓝 x₀] 0 := by
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK hKΩ
  have hχT : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1 := hχ1.filter_mono (nhdsSet_mono hTK)
  have hx₀χ : x₀ ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    fun h ↦ hx₀ (χ.tsupport_subset h)
  have hx₀T : x₀ ∉ dsupport T := fun h ↦ hx₀ (hKΩ (hTK h))
  have hcT : IsCompact (dsupport T) := hK.of_isClosed_subset isClosed_dsupport hTK
  have han : AnalyticAt ℝ (newtonianPotentialOfSupport T) x₀ :=
    (harmonicOnNhd_newtonianPotentialOfSupport hcT (hTK.trans hKΩ) x₀ hx₀T).analyticAt
  have hev : newtonianPotentialOfSupport T =ᶠ[𝓝 x₀] newtonianPotentialPairing T χ := by
    filter_upwards [(isClosed_tsupport (χ : _ → ℝ)).isOpen_compl.mem_nhds hx₀χ] with z hz
    exact newtonianPotentialOfSupport_eq_pairing T hχT hz
  rw [han.eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero]
  intro k
  ext m
  have hcx : ContDiffAt ℝ k (newtonianPotentialPairing T χ) x₀ :=
    ((contDiffOn_newtonianPotentialPairing T χ).contDiffAt
      ((isClosed_tsupport (χ : _ → ℝ)).isOpen_compl.mem_nhds hx₀χ)).of_le (by simp)
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds,
    ← hcx.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv m]
  let H : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y ↦ iteratedFDerivAlong ℝ (List.ofFn m) (newtonianKernel n) (x₀ - y)
  have hH : HarmonicOnNhd H {x₀}ᶜ :=
    harmonicOnNhd_iteratedFDerivAlong_newtonianKernel_sub_right (List.ofFn m) x₀
  have hχx₀ : tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ {x₀}ᶜ := by
    rintro _ hy (rfl : _ = x₀)
    exact hx₀χ hy
  let ψ : 𝓓(Ω, ℝ) := cutoffMulTestFunction χ isOpen_compl_singleton hχx₀
    (hH.analyticOnNhd.contDiffOn isOpen_compl_singleton.uniqueDiffOn)
  rw [iteratedFDerivAlong_newtonianPotentialPairing T hx₀χ (List.ofFn m) (φ := ψ) (fun _ ↦ rfl),
    zero_apply]
  refine hT H ψ (hH.mono fun _ hy (hxy : _ = x₀) ↦ hx₀ (hxy ▸ hy)) ?_
  filter_upwards [hχ1] with y hy
  simp [ψ, hy]

/-- Outside a sufficiently large ball, if `T` vanishes on tests agreeing near `K` with harmonic
functions on `Ω`, then `newtonianPotentialOfSupport T` vanishes identically, by the exterior
multipole expansion. -/
private theorem exists_radius_newtonianPotentialOfSupport_eq_zero {T : 𝓓'(Ω, F)}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hTK : dsupport T ⊆ K)
    (hT : ∀ (H : EuclideanSpace ℝ (Fin n) → ℝ) (ψ : 𝓓(Ω, ℝ)),
      HarmonicOnNhd H Ω → ((ψ : _ → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0) :
    ∃ R > 0, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ →
      newtonianPotentialOfSupport T x = 0 := by
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK hKΩ
  have hχT : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1 := hχ1.filter_mono (nhdsSet_mono hTK)
  obtain ⟨R₀, hR₀⟩ := χ.hasCompactSupport.isBounded.subset_closedBall 0
  set R₁ : ℝ := max R₀ 1
  have hR₁_pos : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hχR₁ : tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ closedBall 0 R₁ :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨c, hc0, hc1, hmp⟩ :=
    exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_newtonianKernel_sub n
  refine ⟨(R₁ + 1) / c, div_pos (by linarith) hc0, fun x hx ↦ ?_⟩
  have hcx : R₁ + 1 < c * ‖x‖ := by
    rw [mul_comm]
    exact (div_lt_iff₀ hc0).1 hx
  have hnorm_pos : 0 < ‖x‖ := lt_trans (div_pos (by linarith) hc0) hx
  have hx0 : x ≠ 0 := norm_pos_iff.1 hnorm_pos
  have hx_gt : R₁ < ‖x‖ := by linarith [mul_lt_of_lt_one_left hnorm_pos hc1]
  have hxχ : x ∉ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    fun h ↦ hx_gt.not_ge (mem_closedBall_zero_iff.1 (hχR₁ h))
  have hχx : tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ {x}ᶜ := by
    rintro _ hy (rfl : _ = x)
    exact hxχ hy
  obtain ⟨P, hPharm, -, hPlim⟩ := hmp x hx0
  have hPsmooth (N : ℕ) : ContDiffOn ℝ ∞ (P N) {x}ᶜ :=
    (((HarmonicOnNhd.analyticOnNhd (fun z _ ↦ hPharm N z : HarmonicOnNhd (P N) univ)).contDiffOn
      uniqueDiffOn_univ).mono (subset_univ _))
  have hχ_sub : tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ closedBall 0 (c * ‖x‖) :=
    hχR₁.trans (closedBall_subset_closedBall (by linarith))
  have htend := tendsto_cutoffMulTestFunction χ isOpen_compl_singleton hχx hPsmooth
    (contDiffOn_newtonianKernel_sub_right x) fun k ↦ (hPlim k).mono hχ_sub
  have hT_lim := (T.continuous.tendsto _).comp htend
  have hzero (N : ℕ) :
      T (cutoffMulTestFunction χ isOpen_compl_singleton hχx (hPsmooth N)) = 0 := by
    refine hT (P N) _ (fun z _ ↦ hPharm N z) ?_
    filter_upwards [hχ1] with y hy
    simp [hy]
  rw [newtonianPotentialOfSupport_eq_pairing T hχT hxχ,
    newtonianPotentialPairing_eq T hxχ
      (φ := cutoffMulTestFunction χ isOpen_compl_singleton hχx
        (contDiffOn_newtonianKernel_sub_right x)) (fun _ ↦ rfl)]
  exact tendsto_nhds_unique (hT_lim.congr hzero) tendsto_const_nhds

/-- **Unique continuation for off-support Newtonian potentials on filled compact sets.** If
`dsupport T ⊆ K` for a compact set `K ⊆ Ω` that is filled in `Ω`, and `T` vanishes on every test
agreeing near `K` with a function harmonic on `Ω`, then `newtonianPotentialOfSupport T` vanishes
throughout `Kᶜ`. -/
theorem newtonianPotentialOfSupport_eq_zero_of_isFilledIn [FiniteDimensional ℝ F]
    {T : 𝓓'(Ω, F)} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    (hT : ∀ (H : EuclideanSpace ℝ (Fin n) → ℝ) (ψ : 𝓓(Ω, ℝ)),
      HarmonicOnNhd H Ω → ((ψ : _ → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Kᶜ) :
    newtonianPotentialOfSupport T x = 0 := by
  have hcT : IsCompact (dsupport T) := hK.of_isClosed_subset isClosed_dsupport hTK
  have han : AnalyticOnNhd ℝ (newtonianPotentialOfSupport T) (connectedComponentIn Kᶜ x) :=
    ((harmonicOnNhd_newtonianPotentialOfSupport hcT (hTK.trans hKΩ)).analyticOnNhd).mono
      ((connectedComponentIn_subset Kᶜ x).trans (compl_subset_compl.2 hTK))
  by_cases hxH : x ∈ filledHull K
  · -- A bounded component of `Kᶜ` cannot stay inside `Ω` since `K` is filled in `Ω`.
    have hnot := (isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
      hK.isClosed Ω.isOpen hKΩ).1 hfill x ⟨hxH, hx⟩
    obtain ⟨x₀, hx₀C, hx₀Ω⟩ := not_subset.1 hnot
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
      hx₀C (eventuallyEq_zero_newtonianPotentialOfSupport_of_notMem hK hKΩ hTK hT hx₀Ω)
      (mem_connectedComponentIn hx)
  · -- An unbounded component of `Kᶜ` escapes every closed ball, reaching the multipole region.
    obtain ⟨R, _, hRzero⟩ := exists_radius_newtonianPotentialOfSupport_eq_zero hK hKΩ hTK hT
    have hunb : ¬IsBounded (connectedComponentIn Kᶜ x) := mt mem_filledHull_iff.2 hxH
    have hnot : ¬connectedComponentIn Kᶜ x ⊆ closedBall 0 R :=
      fun hsub ↦ hunb (isBounded_closedBall.subset hsub)
    obtain ⟨x₀, hx₀C, hx₀R⟩ := not_subset.1 hnot
    have hx₀_gt : R < ‖x₀‖ := not_le.1 (mt mem_closedBall_zero_iff.2 hx₀R)
    have hev : newtonianPotentialOfSupport T =ᶠ[𝓝 x₀] 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx₀_gt] with z hz
      exact hRzero z hz
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
      hx₀C hev (mem_connectedComponentIn hx)

/-- **Support confinement of the distributional Newtonian potential.** Under the hypotheses of
`newtonianPotentialOfSupport_eq_zero_of_isFilledIn`, for any cutoff `χ` equal to `1` near `K`,
`dsupport (Gₙ ⋆ (χ T)) ⊆ K`. -/
theorem dsupport_newtonianPotentialDistribution_subset_of_isFilledIn [FiniteDimensional ℝ F]
    {T : 𝓓'(Ω, F)} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ y in 𝓝ˢ K, χ y = 1)
    (hT : ∀ (H : EuclideanSpace ℝ (Fin n) → ℝ) (ψ : 𝓓(Ω, ℝ)),
      HarmonicOnNhd H Ω → ((ψ : _ → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0) :
    dsupport (newtonianPotentialDistribution T χ) ⊆ K := by
  rw [← disjoint_compl_left_iff_subset]
  refine IsVanishingOn.disjoint_dsupport (fun φ hφ ↦ ?_) hK.isClosed.isOpen_compl
  have hχT : ∀ᶠ y in 𝓝ˢ (dsupport T), χ y = 1 := hχ.filter_mono (nhdsSet_mono hTK)
  have hdisj : Disjoint (tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ)) (dsupport T) :=
    Set.disjoint_left.2 fun z hz hzT ↦ hφ hz (hTK hzT)
  rw [newtonianPotentialDistribution_apply_eq_integral_ofSupport hχT hdisj]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ)
  · simp [newtonianPotentialOfSupport_eq_zero_of_isFilledIn hK hKΩ hfill hTK hT (hφ hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Lax–Malgrange harmonic orthogonality.** In dimensions `n ≥ 3`, let `T : 𝓓'(Ω, F)` be a
distribution with values in a finite-dimensional space `F` supported in a compact set `K ⊆ Ω`
that is filled in `Ω`. If `T` vanishes on every test function agreeing near `K` with a function
harmonic on `Ω`, then `T` also vanishes on every test function agreeing near `K` with a function
harmonic near `K`. -/
theorem apply_eq_zero_of_isFilledIn_of_harmonicOnNhd [FiniteDimensional ℝ F] (hn : 3 ≤ n)
    {T : 𝓓'(Ω, F)} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) (hTK : dsupport T ⊆ K)
    (hT : ∀ (H : EuclideanSpace ℝ (Fin n) → ℝ) (ψ : 𝓓(Ω, ℝ)),
      HarmonicOnNhd H Ω → ((ψ : _ → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : HarmonicOnNhd h K) {ψ : 𝓓(Ω, ℝ)}
    (hψ : (ψ : _ → ℝ) =ᶠ[𝓝ˢ K] h) :
    T ψ = 0 := by
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK hKΩ
  let W := newtonianPotentialDistribution T χ
  have hWK : dsupport W ⊆ K :=
    dsupport_newtonianPotentialDistribution_subset_of_isFilledIn hK hKΩ hfill hTK hχ1 hT
  -- Cut `h` off inside its open harmonic locus `{y | HarmonicAt h y}`.
  let U : Set (EuclideanSpace ℝ (Fin n)) := {y | HarmonicAt h y}
  have hUo : IsOpen U := isOpen_setOfPred_harmonicAt (f := h)
  obtain ⟨η, -, hη1, hηU⟩ := TestFunction.exists_cutoff_tsupport_subset
    (Ω := (⊤ : Opens (EuclideanSpace ℝ (Fin n)))) (n := ⊤) hK hUo hh (subset_univ _)
  have hU_harm : HarmonicOnNhd h U := fun _ hy ↦ hy
  let θ := cutoffMulTestFunction η hUo hηU (hU_harm.analyticOnNhd.contDiffOn hUo.uniqueDiffOn)
  have hθh : (θ : _ → ℝ) =ᶠ[𝓝ˢ K] h := by
    filter_upwards [hη1] with y hy
    simp [θ, hy]
  -- Near `K ⊇ dsupport W`, `Δθ = Δh = 0`, so `W (Δθ) = 0`.
  let Δθ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
    laplacianCLM ℝ (EuclideanSpace ℝ (Fin n)) _ θ
  have hΔ0 : (Δθ : _ → ℝ) =ᶠ[𝓝ˢ (dsupport W)]
      (0 : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) := by
    refine Filter.EventuallyEq.filter_mono ?_ (nhdsSet_mono hWK)
    obtain ⟨V, hVo, hKV, hθV⟩ := mem_nhdsSet_iff_exists.1 hθh
    filter_upwards [(hVo.inter hUo).mem_nhdsSet.2 (subset_inter hKV hh)] with y ⟨hyV, hyU⟩
    have hev_y : (θ : _ → ℝ) =ᶠ[𝓝 y] h :=
      Filter.eventuallyEq_iff_exists_mem.2 ⟨V, hVo.mem_nhds hyV, hθV⟩
    rw [TestFunction.laplacianCLM_apply, ((harmonicAt_congr_nhds hev_y.symm).1 hyU).2.self_of_nhds,
      FunLike.coe_zero, Pi.zero_apply]
  have hW0 : laplacianCLM ℝ (EuclideanSpace ℝ (Fin n)) _ W θ = 0 := by
    rw [Distribution.laplacianCLM_apply_apply, Distribution.map_eq_map_of_eventuallyEq W hΔ0,
      map_zero]
  have hχθ0 : T (TestFunction.cutoffCLM χ.contDiff
      (inter_subset_left.trans χ.tsupport_subset) θ) = 0 :=
    neg_eq_zero.1 ((laplacianCLM_newtonianPotentialDistribution hn T χ θ).symm.trans hW0)
  have hψ_eq : (ψ : _ → ℝ) =ᶠ[𝓝ˢ (dsupport T)]
      TestFunction.cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) θ := by
    refine Filter.EventuallyEq.filter_mono ?_ (nhdsSet_mono hTK)
    filter_upwards [hψ, hχ1, hθh] with y hy₁ hy₂ hy₃
    simp [hy₁, hy₂, hy₃]
  rw [Distribution.map_eq_map_of_eventuallyEq T hψ_eq, hχθ0]

end Potential

end TauCeti
