/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Complex.MixedDeriv
import TauCeti.Analysis.Complex.Runge.FiniteRank
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential
import TauCeti.Analysis.Normed.Module.Exhaustion

/-!
# Global solutions of `bar∂ u = f` on arbitrary open plane domains with parameters

Let `Ω ⊆ ℂ` be an arbitrary open set, let `P` be a proper real normed space, let `Q` be a proper
complex normed space, let `s ⊆ P × Q` be open, and let `f : P × Q → ℂ → F` be a smooth map into a
complex Banach space `F` on `s ×ˢ Ω` that is holomorphic in the complex parameter `q ∈ Q`. This file
constructs a smooth map `u : P × Q → ℂ → F` on `s ×ˢ Ω`, holomorphic in `q`, satisfying
`bar∂_z u = f` on all of `s ×ˢ Ω`, without shrinking either `s` or `Ω` and without assuming `Ω` is
a disc or `s` is a product.

This flat-space non-shrinking parameter solver is the local input glued via partitions of unity to
solve `bar∂` with smooth manifold parameters
(`TauCeti/Geometry/Manifold/Complex/DolbeaultParameter.lean`) and to eliminate one complex variable
at a time on whole product domains.

The construction follows the Mittag–Leffler / Runge exhaustion scheme:

1. Exhaust `s` by compact sets `D j` and `Ω` by filled compact sets `C j`
   (`IsOpen.exists_isFilledIn_compact_exhaustion`). Apply `TauCeti.exists_contDiff_shell_cutoffs`
   to the shifted exhaustion `j ↦ C (j + 1)` to obtain smooth compactly supported shell cutoffs
   `χ j` supported in `interior (C (j + 2))`, vanishing near `C j` for `j ≥ 1`, and summing to `1`
   on `C (m + 1)`.
2. For each shell `j`, solve `bar∂_z (v j x) = (χ j : ℂ) • f x` via
   `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_smul_with_holomorphic_param`. Then
   `v j` is jointly smooth on `s ×ˢ univ`, holomorphic in `q`, and for `j ≥ 1` holomorphic in `w`
   off `tsupport (χ j)` (in particular near `C j`).
3. For `j ≥ 1`, apply the finite-rank Runge approximation operator
   (`TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`) on `C j ⊆ Ω` to approximate `v j` by a
   finite linear combination `a j x w = ∑ i, (c i * g i w) • v j x (ζ i)` with `g i` holomorphic on
   `Ω`. Because the nodes `ζ i`, weights `c i`, and functions `g i` are independent of `(x, F)`,
   applying the same finite-rank operator simultaneously shrinks all parameter derivatives
   `iteratedFDeriv ℝ k (fun x' ↦ (v j - a j) x' w) x` for `k ≤ j` to at most `2⁻ʲ` on `D j ×ˢ C j`,
   while preserving `q`-holomorphy and leaving `bar∂_z` unchanged on `Ω`.
4. Put `u 0 = v 0` (i.e. `a 0 = 0`) and `u j = v j - a j` for `j ≥ 1`, and set
   `U x w = ∑' j, u j x w`. On any local box `ball x₀ ρ ×ˢ ball z₀ r` inside
   `D (m + 1) ×ˢ interior (C (m + 1))`, the Cauchy bound
   `TauCeti.norm_iteratedFDeriv_le_of_differentiableOn_of_norm_iteratedFDeriv_prod_left_le`
   converts the parameter-only bounds on the tail `j ≥ max (m + 1) k` into total `C^k` bounds
   `(1 + 2^k / r)^k * 2⁻ʲ`, so `TauCeti.contDiffOn_tsum_of_eventually` gives joint smoothness on
   `s ×ˢ Ω`. Splitting at `m + 1` shows both `bar∂_z U = f` and holomorphy in `q`.

In the parameter-free case, a direct Mittag–Leffler exhaustion using `C^n` cut-off Cauchy
transforms and Runge's theorem (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`) yields a
`C^n` solution for every `n : ℕ∞` with `1 ≤ n`.

## Main results

* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param`: global smooth
  solution of `bar∂_z u = f` on `s ×ˢ Ω`, preserving holomorphy in `q`.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_param`: specialization to purely
  smooth parameters `s ⊆ P`.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`: parameter-free global `C^n`
  (`1 ≤ n`) solution of `bar∂ u = f` on an arbitrary open set `Ω ⊆ ℂ`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter I, §3.
-/

public noncomputable section

open Complex Filter Metric Set Topology
open scoped ContDiff

universe uP uQ uF

namespace TauCeti

/-! ### Finite-rank Runge correction of a single shell -/

section RungeCorrection

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {Q : Type uQ} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Uniform bound on all parameter derivatives of `v` up to order `j` over a compact product
`D ×ˢ L ⊆ s ×ˢ univ`. -/
private theorem exists_pos_bound_iteratedFDeriv_prod_left {v : P × Q → ℂ → F} {s : Set (P × Q)}
    {D : Set (P × Q)} {L : Set ℂ} (hs : IsOpen s) (hD : IsCompact D) (hDs : D ⊆ s)
    (hL : IsCompact L) (hv : ContDiffOn ℝ ∞ ↿v (s ×ˢ univ)) (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ k ≤ j, ∀ x ∈ D, ∀ w ∈ L,
      ‖iteratedFDeriv ℝ k (fun x' ↦ v x' w) x‖ ≤ M := by
  have hcont (k : Fin (j + 1)) : ∃ B : ℝ, ∀ p ∈ D ×ˢ L,
      ‖iteratedFDeriv ℝ k.val (fun x' ↦ v x' p.2) p.1‖ ≤ B :=
    (hD.prod hL).exists_bound_of_continuousOn
      ((hv.continuousOn_iteratedFDeriv_partial (hs.prod isOpen_univ) (by simp)).mono
        (prod_mono hDs (subset_univ L)))
  choose B hB using hcont
  refine ⟨1 + ∑ i : Fin (j + 1), max 0 (B i), by positivity, fun k hk x hx w hw ↦ ?_⟩
  let idx : Fin (j + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  calc
    ‖iteratedFDeriv ℝ k (fun x' ↦ v x' w) x‖ ≤ B idx := hB idx (x, w) ⟨hx, hw⟩
    _ ≤ max 0 (B idx) := le_max_right _ _
    _ ≤ ∑ i : Fin (j + 1), max 0 (B i) :=
      Finset.single_le_sum (fun i _ ↦ le_max_left 0 (B i)) (Finset.mem_univ idx)
    _ ≤ 1 + ∑ i : Fin (j + 1), max 0 (B i) := le_add_of_nonneg_left zero_le_one

/-- Applying a fixed finite-rank Runge operator commutes with parameter differentiation, shrinking
the `k`-th parameter derivative of `v - a` uniformly on `D ×ˢ K`. -/
private theorem norm_iteratedFDeriv_sub_rungeSum_le {N : ℕ} {ζ c : Fin N → ℂ} {g : Fin N → ℂ → ℂ}
    {s D : Set (P × Q)} {K L : Set ℂ} {v : P × Q → ℂ → F} {M ε : ℝ}
    (hs : IsOpen s) (hDs : D ⊆ s) (hv_cd : ContDiffOn ℝ ∞ ↿v (s ×ˢ univ))
    (hv_hol : ∀ x ∈ s, DifferentiableOn ℂ (v x) (interior L)) (hM0 : 0 < M)
    (happrox : ∀ {G : Type max uP uQ uF} [NormedAddCommGroup G] [NormedSpace ℂ G]
      (φ : ℂ → G) (B : ℝ), DifferentiableOn ℂ φ (interior L) → (∀ z ∈ interior L, ‖φ z‖ ≤ B) →
      ∀ w ∈ K, ‖φ w - ∑ i, (c i * g i w) • φ (ζ i)‖ ≤ (ε / M) * B)
    {k : ℕ} {x : P × Q} (hx : x ∈ D) (hM : ∀ z ∈ L, ‖iteratedFDeriv ℝ k (fun x' ↦ v x' z) x‖ ≤ M)
    {w : ℂ} (hw : w ∈ K) :
    ‖iteratedFDeriv ℝ k (fun x' ↦ v x' w - ∑ i : Fin N, (c i * g i w) • v x' (ζ i)) x‖ ≤ ε := by
  let φ : ℂ → (P × Q) [×k]→L[ℝ] F := fun z ↦ iteratedFDeriv ℝ k (fun x' ↦ v x' z) x
  have hφ_hol : DifferentiableOn ℂ φ (interior L) :=
    differentiableOn_iteratedFDeriv_prod_left k hs isOpen_interior
      ((hv_cd.mono (prod_mono Subset.rfl (subset_univ _))).of_le (by simp)) hv_hol (hDs hx)
  have hslice (z : ℂ) : ContDiffAt ℝ k (fun x' ↦ v x' z) x :=
    ((hv_cd.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hDs hx, mem_univ z⟩)).of_le
      (by simp)).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hcomm : iteratedFDeriv ℝ k
      (fun x' ↦ v x' w - ∑ i : Fin N, (c i * g i w) • v x' (ζ i)) x =
      φ w - ∑ i : Fin N, (c i * g i w) • φ (ζ i) := by
    have ha_cd : ContDiffAt ℝ k (fun x' ↦ ∑ i : Fin N, (c i * g i w) • v x' (ζ i)) x :=
      ContDiffAt.sum fun i _ ↦ (hslice (ζ i)).const_smul (c i * g i w)
    have hsub_eq : (fun x' ↦ v x' w - ∑ i : Fin N, (c i * g i w) • v x' (ζ i)) =
        (fun x' ↦ v x' w) - (fun x' ↦ ∑ i : Fin N, (c i * g i w) • v x' (ζ i)) := rfl
    rw [hsub_eq, iteratedFDeriv_sub_apply (hslice w) ha_cd,
      iteratedFDeriv_fun_sum_apply fun i _ ↦ (hslice (ζ i)).const_smul (c i * g i w)]
    simp only [φ, iteratedFDeriv_const_smul_apply' (hslice _)]
  rw [hcomm]
  have hle := happrox φ M hφ_hol (fun z hz ↦ hM z (interior_subset hz)) w hw
  rwa [div_mul_cancel₀ _ hM0.ne'] at hle

variable [CompleteSpace F]

/-- For any shell cutoff `χ` supported in `Ω` and vanishing near a filled compact `K ⊆ Ω`,
subtracting a finite-rank Runge approximant from the cut-off Cauchy transform yields a smooth
`q`-holomorphic solution of `bar∂_z u = χ f` on `s ×ˢ Ω` which is holomorphic in `z` on
`(tsupport χ)ᶜ ∩ Ω` and has all parameter derivatives up to order `j` bounded by `ε` on `D ×ˢ K`. -/
private theorem exists_runge_corrected_shell {s : Set (P × Q)} {Ω K : Set ℂ} {D : Set (P × Q)}
    {f : P × Q → ℂ → F} {χ : ℂ → ℝ} (hs : IsOpen s) (hΩ : IsOpen Ω)
    (hD : IsCompact D) (hDs : D ⊆ s) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hKχ : K ⊆ (tsupport χ)ᶜ) (hf : ContDiffOn ℝ ∞ ↿f (s ×ˢ Ω))
    (hfq : ∀ x ∈ s, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ f (x.1, q) z) x.2)
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : P × Q → ℂ → F,
      ContDiffOn ℝ ∞ ↿u (s ×ˢ Ω) ∧
      (∀ x ∈ s, ∀ w ∈ Ω, DifferentiableAt ℂ (fun q ↦ u (x.1, q) w) x.2) ∧
      (∀ x ∈ s, ∀ w ∈ Ω, conjWirtingerDeriv (u x) w 1 = (χ w : ℂ) • f x w) ∧
      (∀ x ∈ s, DifferentiableOn ℂ (u x) ((tsupport χ)ᶜ ∩ Ω)) ∧
      ∀ k ≤ j, ∀ x ∈ D, ∀ w ∈ K, ‖iteratedFDeriv ℝ k (fun x' ↦ u x' w) x‖ ≤ ε := by
  obtain ⟨v, hv_cd, hv_dbar, hv_hol, hv_q⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_smul_with_holomorphic_param
      (by simp) hs hΩ hχ hχc hχΩ hf hfq
  obtain ⟨L, hL, hKL, hLχ⟩ := exists_compact_between hK (isClosed_tsupport χ).isOpen_compl hKχ
  obtain ⟨M, hM0, hM⟩ := exists_pos_bound_iteratedFDeriv_prod_left hs hD hDs hL hv_cd j
  obtain ⟨N, ζ, c, g, -, hg, happrox⟩ :=
    hfill.exists_norm_sub_sum_mul_smul_le.{max uP uQ uF} hΩ hK hKΩ isOpen_interior hKL
      (div_pos hε hM0)
  let a : P × Q → ℂ → F := fun x w ↦ ∑ i : Fin N, (c i * g i w) • v x (ζ i)
  let u : P × Q → ℂ → F := fun x w ↦ v x w - a x w
  have ha_hol (x : P × Q) : DifferentiableOn ℂ (a x) Ω :=
    DifferentiableOn.fun_sum fun i _ ↦ ((hg i).const_mul (c i)).smul_const (v x (ζ i))
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · have ha_cd : ContDiffOn ℝ ∞ ↿a (s ×ˢ Ω) := by
      have ha_eq : ↿a = fun p : (P × Q) × ℂ ↦ ∑ i : Fin N, (c i * g i p.2) • v p.1 (ζ i) := rfl
      rw [ha_eq]
      refine ContDiffOn.sum fun i _ ↦ ?_
      have hg_cd : ContDiffOn ℝ ∞ (fun p : (P × Q) × ℂ ↦ c i * g i p.2) (s ×ˢ Ω) :=
        ((((hg i).const_mul (c i)).contDiffOn hΩ).restrict_scalars ℝ).comp contDiffOn_snd
          fun _ hp ↦ hp.2
      have hv_ζ : ContDiffOn ℝ ∞ (fun p : (P × Q) × ℂ ↦ v p.1 (ζ i)) (s ×ˢ Ω) :=
        hv_cd.comp (contDiffOn_fst.prodMk contDiffOn_const) fun _ hp ↦ ⟨hp.1, mem_univ _⟩
      exact hg_cd.smul hv_ζ
    exact (hv_cd.mono (prod_mono Subset.rfl (subset_univ Ω))).sub ha_cd
  · intro x hx w _
    exact (hv_q x hx w).sub (DifferentiableAt.fun_sum fun i _ ↦ (hv_q x hx (ζ i)).const_smul _)
  · intro x hx w hw
    have hvd : DifferentiableAt ℝ (v x) w :=
      ((hv_cd.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hx, mem_univ w⟩)).comp w
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have had : DifferentiableAt ℂ (a x) w := (ha_hol x).differentiableAt (hΩ.mem_nhds hw)
    have hsub := congrArg (fun L ↦ L 1) (conjWirtingerDeriv_sub hvd (had.restrictScalars ℝ))
    have hu_eq : u x = v x - a x := rfl
    rw [hu_eq]
    simpa only [had.conjWirtingerDeriv_eq_zero, sub_apply, zero_apply, sub_zero,
      hv_dbar x hx w] using hsub
  · exact fun x hx ↦ ((hv_hol x hx).mono inter_subset_left).sub ((ha_hol x).mono inter_subset_right)
  · exact fun k hk x hx w hw ↦ norm_iteratedFDeriv_sub_rungeSum_le hs hDs hv_cd
      (fun x' hx' ↦ (hv_hol x' hx').mono (interior_subset.trans hLχ)) hM0 happrox hx
      (fun z hz ↦ hM k hk x hx z hz) hw

/-- Assemble the full sequence `u j` of shell solutions along compact exhaustions `D` of `s` and
filled `C` of `Ω`: `u 0` is the raw cut-off Cauchy transform, while `u (n + 1)` is Runge-corrected
so that all parameter derivatives through order `n + 1` are bounded by `(1 / 2) ^ (n + 1)` on
`D (n + 1) ×ˢ C (n + 1)`. -/
private theorem exists_shell_sequence {s : Set (P × Q)} {Ω : Set ℂ} {D : ℕ → Set (P × Q)}
    {C : ℕ → Set ℂ} {χ : ℕ → ℂ → ℝ} {f : P × Q → ℂ → F} (hs : IsOpen s) (hΩ : IsOpen Ω)
    (hD_cpt : ∀ j, IsCompact (D j)) (hD_sub : ∀ j, D j ⊆ s)
    (hC_cpt : ∀ j, IsCompact (C j)) (hC_sub : ∀ j, C j ⊆ Ω) (hC_fill : ∀ j, IsFilledIn (C j) Ω)
    (hχ_cd : ∀ j, ContDiff ℝ ∞ (χ j)) (hχ_cpt : ∀ j, HasCompactSupport (χ j))
    (hχ_Ω : ∀ j, tsupport (χ j) ⊆ Ω) (hχ_disj : ∀ j, 1 ≤ j → C j ⊆ (tsupport (χ j))ᶜ)
    (hf : ContDiffOn ℝ ∞ ↿f (s ×ˢ Ω))
    (hfq : ∀ x ∈ s, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ f (x.1, q) z) x.2) :
    ∃ u : ℕ → P × Q → ℂ → F,
      (∀ j, ContDiffOn ℝ ∞ ↿(u j) (s ×ˢ Ω)) ∧
      (∀ j, ∀ x ∈ s, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ u j (x.1, q) z) x.2) ∧
      (∀ j, ∀ x ∈ s, ∀ z ∈ Ω, conjWirtingerDeriv (u j x) z 1 = (χ j z : ℂ) • f x z) ∧
      (∀ j, 1 ≤ j → ∀ x ∈ s, DifferentiableOn ℂ (u j x) (interior (C j))) ∧
      ∀ j, 1 ≤ j → ∀ k ≤ j, ∀ x ∈ D j, ∀ w ∈ C j,
        ‖iteratedFDeriv ℝ k (fun x' ↦ u j x' w) x‖ ≤ (1 / 2 : ℝ) ^ j := by
  obtain ⟨u₀, hu₀_cd, hu₀_dbar, -, hu₀_q⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_smul_with_holomorphic_param
      (by simp) hs hΩ (hχ_cd 0) (hχ_cpt 0) (hχ_Ω 0) hf hfq
  have hstep (n : ℕ) := exists_runge_corrected_shell hs hΩ (hD_cpt (n + 1)) (hD_sub (n + 1))
    (hC_cpt (n + 1)) (hC_sub (n + 1)) (hC_fill (n + 1)) (hχ_cd (n + 1)) (hχ_cpt (n + 1))
    (hχ_Ω (n + 1)) (hχ_disj (n + 1) (Nat.succ_pos n)) hf hfq (n + 1)
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1))
  choose uS huS_cd huS_q huS_dbar huS_hol huS_bd using hstep
  refine ⟨fun j ↦ match j with | 0 => u₀ | n + 1 => uS n,
    fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · cases j with
    | zero => exact hu₀_cd.mono (prod_mono Subset.rfl (subset_univ Ω))
    | succ n => exact huS_cd n
  · cases j with
    | zero => exact fun _ hx z _ ↦ hu₀_q _ hx z
    | succ n => exact huS_q n
  · cases j with
    | zero => exact fun _ hx z _ ↦ hu₀_dbar _ hx z
    | succ n => exact huS_dbar n
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact fun x hx ↦ (huS_hol n x hx).mono
      (subset_inter (interior_subset.trans (hχ_disj (n + 1) hj))
        (interior_subset.trans (hC_sub (n + 1))))
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact huS_bd n

end RungeCorrection

/-! ### Local convergence lemmas for the shell series -/

section SeriesConvergence

/-- Given exhaustions `D` of `s` and `C` of `Ω` with `D j ⊆ interior (D (j + 1))` and
`C j ⊆ interior (C (j + 1))`, every `(x₀, z₀) ∈ s ×ˢ Ω` lies inside a product box
`ball x₀ ρ ×ˢ closedBall z₀ (2 * r)` contained in `D (m + 1) ×ˢ interior (C (m + 1))`. -/
private theorem exists_local_exhaustion_box {X : Type*} [PseudoMetricSpace X]
    {s : Set X} {Ω : Set ℂ} {D : ℕ → Set X} {C : ℕ → Set ℂ}
    (hD_step : ∀ j, D j ⊆ interior (D (j + 1))) (hD_uni : ⋃ j, D j = s)
    (hC_step : ∀ j, C j ⊆ interior (C (j + 1))) (hC_uni : ⋃ j, C j = Ω)
    {x₀ : X} (hx₀ : x₀ ∈ s) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ (m : ℕ) (ρ r : ℝ), 0 < ρ ∧ 0 < r ∧
      ball x₀ ρ ⊆ D (m + 1) ∧ closedBall z₀ (2 * r) ⊆ interior (C (m + 1)) := by
  have hD_mono : Monotone D := monotone_nat_of_le_succ fun j ↦ (hD_step j).trans interior_subset
  have hC_mono : Monotone C := monotone_nat_of_le_succ fun j ↦ (hC_step j).trans interior_subset
  obtain ⟨m₁, hm₁⟩ := mem_iUnion.1 (hD_uni.symm ▸ hx₀)
  obtain ⟨m₂, hm₂⟩ := mem_iUnion.1 (hC_uni.symm ▸ hz₀)
  let m := max m₁ m₂
  have hx' : x₀ ∈ interior (D (m + 1)) := hD_step m (hD_mono (le_max_left m₁ m₂) hm₁)
  have hz' : z₀ ∈ interior (C (m + 1)) := hC_step m (hC_mono (le_max_right m₁ m₂) hm₂)
  obtain ⟨ρ, hρ, hball_x⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx'
  obtain ⟨R, hR, hball_z⟩ := Metric.isOpen_iff.1 isOpen_interior z₀ hz'
  refine ⟨m, ρ, R / 4, hρ, by positivity, hball_x.trans interior_subset, ?_⟩
  exact (closedBall_subset_ball (by linarith)).trans hball_z

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {Q : Type uQ} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Local smoothness of the shell series `U x w = ∑' j, u j x w` on a box
`ball x₀ ρ ×ˢ ball z₀ r ⊆ D (m + 1) ×ˢ interior (C (m + 1))`. -/
private theorem contDiffOn_shell_series_box {s : Set (P × Q)} {Ω : Set ℂ}
    {D : ℕ → Set (P × Q)} {C : ℕ → Set ℂ} {u : ℕ → P × Q → ℂ → F}
    (hD_mono : Monotone D) (hC_mono : Monotone C)
    (hD_sub : ∀ j, D j ⊆ s) (hC_sub : ∀ j, C j ⊆ Ω)
    (hu_cd : ∀ j, ContDiffOn ℝ ∞ ↿(u j) (s ×ˢ Ω))
    (hu_hol : ∀ j, 1 ≤ j → ∀ x ∈ s, DifferentiableOn ℂ (u j x) (interior (C j)))
    (hu_bd : ∀ j, 1 ≤ j → ∀ k ≤ j, ∀ x ∈ D j, ∀ w ∈ C j,
      ‖iteratedFDeriv ℝ k (fun x' ↦ u j x' w) x‖ ≤ (1 / 2 : ℝ) ^ j)
    {m : ℕ} {x₀ : P × Q} {z₀ : ℂ} {ρ r : ℝ} (hr : 0 < r)
    (hball_x : ball x₀ ρ ⊆ D (m + 1)) (hball_z : closedBall z₀ (2 * r) ⊆ interior (C (m + 1))) :
    ContDiffOn ℝ ∞ (fun p : (P × Q) × ℂ ↦ ∑' j, u j p.1 p.2) (ball x₀ ρ ×ˢ ball z₀ r) := by
  have hbox_sub : ball x₀ ρ ×ˢ ball z₀ r ⊆ s ×ˢ Ω :=
    prod_mono (hball_x.trans (hD_sub (m + 1)))
      ((ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans
        (hball_z.trans interior_subset))).trans (hC_sub (m + 1)))
  refine contDiffOn_tsum_of_eventually (isOpen_ball.prod isOpen_ball)
    (fun j ↦ (hu_cd j).mono hbox_sub)
    (fun k _ ↦ summable_geometric_two.mul_left ((1 + (2 : ℝ) ^ k / r) ^ k))
    fun k _ ↦ ?_
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max (m + 1) k, fun j hj p hp ↦ ?_⟩
  have hjm : m + 1 ≤ j := (le_max_left _ _).trans hj
  have hjk : k ≤ j := (le_max_right _ _).trans hj
  have hj1 : 1 ≤ j := le_trans (Nat.succ_le_succ (Nat.zero_le m)) hjm
  have hsub_z : closedBall p.2 r ⊆ interior (C (m + 1)) :=
    (closedBall_subset_closedBall' (by linarith [mem_ball.1 hp.2])).trans hball_z
  have hCD : ball x₀ ρ ×ˢ interior (C (m + 1)) ⊆ s ×ˢ Ω :=
    prod_mono (hball_x.trans (hD_sub (m + 1))) (interior_subset.trans (hC_sub (m + 1)))
  have hhol_j : ∀ x' ∈ ball x₀ ρ, DifferentiableOn ℂ (u j x') (interior (C (m + 1))) :=
    fun x' hx' ↦ (hu_hol j hj1 x' (hD_sub (m + 1) (hball_x hx'))).mono
      (interior_mono (hC_mono hjm))
  exact norm_iteratedFDeriv_le_of_differentiableOn_of_norm_iteratedFDeriv_prod_left_le k
    isOpen_ball isOpen_interior (((hu_cd j).mono hCD).of_le (by simp)) hhol_j hp.1 hr hsub_z
    fun l hl w hw ↦ hu_bd j hj1 l (hl.trans hjk) p.1 (hD_mono hjm (hball_x hp.1)) w
      (hC_mono hjm (interior_subset (hsub_z hw)))

/-- Pointwise `bar∂_z` identity for the shell series `U x w = ∑' j, u j x w`: splitting at
`m + 1` yields a finite sum whose `bar∂_z` is `f` plus a uniformly convergent holomorphic tail. -/
private theorem conjWirtingerDeriv_shell_series {s : Set (P × Q)} {Ω : Set ℂ}
    {D : ℕ → Set (P × Q)} {C : ℕ → Set ℂ} {χ : ℕ → ℂ → ℝ} {f : P × Q → ℂ → F}
    {u : ℕ → P × Q → ℂ → F} (hs : IsOpen s) (hΩ : IsOpen Ω)
    (hD_mono : Monotone D) (hC_mono : Monotone C)
    (hχ_sum : ∀ m, ∀ z ∈ C (m + 1), ∑ j ∈ Finset.range (m + 1), χ j z = 1)
    (hu_cd : ∀ j, ContDiffOn ℝ ∞ ↿(u j) (s ×ˢ Ω))
    (hu_dbar : ∀ j, ∀ x ∈ s, ∀ z ∈ Ω, conjWirtingerDeriv (u j x) z 1 = (χ j z : ℂ) • f x z)
    (hu_hol : ∀ j, 1 ≤ j → ∀ x ∈ s, DifferentiableOn ℂ (u j x) (interior (C j)))
    (hu_bd : ∀ j, 1 ≤ j → ∀ k ≤ j, ∀ x ∈ D j, ∀ w ∈ C j,
      ‖iteratedFDeriv ℝ k (fun x' ↦ u j x' w) x‖ ≤ (1 / 2 : ℝ) ^ j)
    {m : ℕ} {x₀ : P × Q} (hx₀ : x₀ ∈ s) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hxD : x₀ ∈ D (m + 1)) (hball_C : ball z₀ r ⊆ interior (C (m + 1))) :
    conjWirtingerDeriv (fun w ↦ ∑' j, u j x₀ w) z₀ 1 = f x₀ z₀ := by
  have hsumm : Summable fun j ↦ (1 / 2 : ℝ) ^ (j + (m + 1)) :=
    (summable_nat_add_iff (m + 1)).2 summable_geometric_two
  have hbd0 (j : ℕ) {w : ℂ} (hw : w ∈ ball z₀ r) :
      ‖u (j + (m + 1)) x₀ w‖ ≤ (1 / 2 : ℝ) ^ (j + (m + 1)) := by
    simpa only [norm_iteratedFDeriv_zero] using hu_bd (j + (m + 1)) (by omega) 0 (Nat.zero_le _)
      x₀ (hD_mono (Nat.le_add_left _ _) hxD) w
      (hC_mono (Nat.le_add_left _ _) (interior_subset (hball_C hw)))
  have hsplit : (fun w ↦ ∑' j, u j x₀ w) =ᶠ[𝓝 z₀]
      (fun w ↦ ∑ j ∈ Finset.range (m + 1), u j x₀ w) +
        (fun w ↦ ∑' j, u (j + (m + 1)) x₀ w) := by
    filter_upwards [ball_mem_nhds z₀ hr] with w hw
    have hs_w : Summable fun j ↦ u j x₀ w := (summable_nat_add_iff (m + 1)).1 <|
      .of_norm_bounded hsumm fun j ↦ hbd0 j hw
    exact (hs_w.sum_add_tsum_nat_add (m + 1)).symm
  have htail_hol : DifferentiableOn ℂ (fun w ↦ ∑' j, u (j + (m + 1)) x₀ w) (ball z₀ r) :=
    (tendstoUniformlyOn_tsum hsumm fun j w hw ↦ hbd0 j hw).differentiableOn
      (.of_forall fun _ ↦ DifferentiableOn.fun_sum fun j _ ↦
        (hu_hol (j + (m + 1)) (by omega) x₀ hx₀).mono
          (hball_C.trans (interior_mono (hC_mono (Nat.le_add_left _ _))))) isOpen_ball
  have hfin_diff (j : ℕ) : DifferentiableAt ℝ (u j x₀) z₀ :=
    (((hu_cd j).contDiffAt ((hs.prod hΩ).mem_nhds ⟨hx₀, hz₀⟩)).comp z₀
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hfin_dbar : conjWirtingerDeriv (fun w ↦ ∑ j ∈ Finset.range (m + 1), u j x₀ w) z₀ 1 =
      f x₀ z₀ := by
    rw [conjWirtingerDeriv_fun_sum fun j _ ↦ hfin_diff j, sum_apply]
    simp_rw [hu_dbar _ x₀ hx₀ z₀ hz₀, ← Finset.sum_smul, ← Complex.ofReal_sum,
      hχ_sum m z₀ (interior_subset (hball_C (mem_ball_self hr))), Complex.ofReal_one, one_smul]
  have htail_at : DifferentiableAt ℂ (fun w ↦ ∑' j, u (j + (m + 1)) x₀ w) z₀ :=
    htail_hol.differentiableAt (ball_mem_nhds z₀ hr)
  have hadd := congrArg (fun L ↦ L 1) (conjWirtingerDeriv_add
    (DifferentiableAt.fun_sum (u := Finset.range (m + 1)) fun j _ ↦ hfin_diff j)
    (htail_at.restrictScalars ℝ))
  rw [hsplit.conjWirtingerDeriv_eq]
  simpa [hfin_dbar, htail_at.conjWirtingerDeriv_eq_zero] using hadd

/-- Holomorphy in `q ∈ Q` for the shell series `U x w = ∑' j, u j x w`: splitting at `m + 1` yields
a finite sum of `q`-holomorphic terms plus a uniformly convergent `q`-holomorphic tail. -/
private theorem differentiableAt_shell_series_param {s : Set (P × Q)} {Ω : Set ℂ}
    {D : ℕ → Set (P × Q)} {C : ℕ → Set ℂ} {u : ℕ → P × Q → ℂ → F}
    (hD_mono : Monotone D) (hC_mono : Monotone C) (hD_sub : ∀ j, D j ⊆ s)
    (hu_q : ∀ j, ∀ x ∈ s, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ u j (x.1, q) z) x.2)
    (hu_bd : ∀ j, 1 ≤ j → ∀ k ≤ j, ∀ x ∈ D j, ∀ w ∈ C j,
      ‖iteratedFDeriv ℝ k (fun x' ↦ u j x' w) x‖ ≤ (1 / 2 : ℝ) ^ j)
    {m : ℕ} {x₀ : P × Q} (hx₀ : x₀ ∈ s) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {ρ : ℝ} (hρ : 0 < ρ)
    (hball_x : ball x₀ ρ ⊆ D (m + 1)) (hz_C : z₀ ∈ C (m + 1)) :
    DifferentiableAt ℂ (fun q ↦ ∑' j, u j (x₀.1, q) z₀) x₀.2 := by
  have hq_mem {q : Q} (hq : q ∈ ball x₀.2 ρ) : (x₀.1, q) ∈ D (m + 1) := by
    apply hball_x
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hq
  have hsumm : Summable fun j ↦ (1 / 2 : ℝ) ^ (j + (m + 1)) :=
    (summable_nat_add_iff (m + 1)).2 summable_geometric_two
  have hbd0 (j : ℕ) {q : Q} (hq : q ∈ ball x₀.2 ρ) :
      ‖u (j + (m + 1)) (x₀.1, q) z₀‖ ≤ (1 / 2 : ℝ) ^ (j + (m + 1)) := by
    simpa only [norm_iteratedFDeriv_zero] using hu_bd (j + (m + 1)) (by omega) 0 (Nat.zero_le _)
      (x₀.1, q) (hD_mono (Nat.le_add_left _ _) (hq_mem hq))
      z₀ (hC_mono (Nat.le_add_left _ _) hz_C)
  have htail_hol : DifferentiableOn ℂ (fun q ↦ ∑' j, u (j + (m + 1)) (x₀.1, q) z₀)
      (ball x₀.2 ρ) :=
    (tendstoUniformlyOn_tsum hsumm fun j q hq ↦ hbd0 j hq).differentiableOn
      (.of_forall fun _ ↦ DifferentiableOn.fun_sum fun j _ q hq ↦
        (hu_q (j + (m + 1)) (x₀.1, q) (hD_sub (m + 1) (hq_mem hq)) z₀ hz₀).differentiableWithinAt)
      isOpen_ball
  have hfin_hol : DifferentiableAt ℂ (fun q ↦ ∑ j ∈ Finset.range (m + 1), u j (x₀.1, q) z₀)
      x₀.2 :=
    DifferentiableAt.fun_sum fun j _ ↦ hu_q j x₀ hx₀ z₀ hz₀
  have hsplit : (fun q ↦ ∑' j, u j (x₀.1, q) z₀) =ᶠ[𝓝 x₀.2]
      fun q ↦ ∑ j ∈ Finset.range (m + 1), u j (x₀.1, q) z₀ +
        ∑' j, u (j + (m + 1)) (x₀.1, q) z₀ := by
    filter_upwards [ball_mem_nhds x₀.2 hρ] with q hq
    have hs_q : Summable fun j ↦ u j (x₀.1, q) z₀ := (summable_nat_add_iff (m + 1)).1 <|
      .of_norm_bounded hsumm fun j ↦ hbd0 j hq
    exact (hs_q.sum_add_tsum_nat_add (m + 1)).symm
  exact (hfin_hol.add (htail_hol.differentiableAt (ball_mem_nhds x₀.2 hρ))).congr_of_eventuallyEq
    hsplit

end SeriesConvergence

/-! ### Global mixed-parameter solver on arbitrary open domains -/

section GlobalSolver

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  {Q : Type uQ} [NormedAddCommGroup Q] [NormedSpace ℂ Q] [ProperSpace Q]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Global `bar∂` solver on arbitrary open plane domains with smooth and holomorphic
parameters.** Let `s ⊆ P × Q` be an open subset of the product of a proper real normed space `P`
and a proper complex normed space `Q`, let `Ω ⊆ ℂ` be open, and let `f : P × Q → ℂ → F` be smooth
on `s ×ˢ Ω` with values in a complex Banach space `F` and holomorphic in `q ∈ Q`. Then there exists
`u : P × Q → ℂ → F`, smooth on `s ×ˢ Ω` and holomorphic in `q ∈ Q`, such that
`conjWirtingerDeriv (u x) z 1 = f x z` for all `x ∈ s` and `z ∈ Ω`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param
    {s : Set (P × Q)} {Ω : Set ℂ} {f : P × Q → ℂ → F} (hs : IsOpen s) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ ↿f (s ×ˢ Ω))
    (hfq : ∀ x ∈ s, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ f (x.1, q) z) x.2) :
    ∃ u : P × Q → ℂ → F,
      ContDiffOn ℝ ∞ ↿u (s ×ˢ Ω) ∧
      (∀ x ∈ s, ∀ z ∈ Ω, conjWirtingerDeriv (u x) z 1 = f x z) ∧
      ∀ x ∈ s, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ u (x.1, q) z) x.2 := by
  obtain ⟨D, hD_cpt, hD_step, hD_uni, -⟩ := hs.exists_isFilledIn_compact_exhaustion
  obtain ⟨C, hC_cpt, hC_step, hC_uni, hC_fill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hD_mono : Monotone D := monotone_nat_of_le_succ fun j ↦ (hD_step j).trans interior_subset
  have hC_mono : Monotone C := monotone_nat_of_le_succ fun j ↦ (hC_step j).trans interior_subset
  have hD_sub (j : ℕ) : D j ⊆ s := hD_uni ▸ subset_iUnion D j
  have hC_sub (j : ℕ) : C j ⊆ Ω := hC_uni ▸ subset_iUnion C j
  obtain ⟨χ, hχ_cd, hχ_cpt, -, hχ_ts, hχ_disj', hχ_sum⟩ :=
    exists_contDiff_shell_cutoffs (C := fun j ↦ C (j + 1)) (fun j ↦ hC_cpt (j + 1))
      (fun j ↦ hC_step (j + 1))
  have hχ_Ω (j : ℕ) : tsupport (χ j) ⊆ Ω := (hχ_ts j).trans (interior_subset.trans (hC_sub (j + 2)))
  have hχ_disj (j : ℕ) (hj : 1 ≤ j) : C j ⊆ (tsupport (χ j))ᶜ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact hχ_disj' k
  obtain ⟨u, hu_cd, hu_q, hu_dbar, hu_hol, hu_bd⟩ :=
    exists_shell_sequence hs hΩ hD_cpt hD_sub hC_cpt hC_sub hC_fill hχ_cd hχ_cpt hχ_Ω hχ_disj hf hfq
  refine ⟨fun x w ↦ ∑' j, u j x w, ?_, ?_, ?_⟩
  · rintro ⟨x₀, z₀⟩ ⟨hx₀, hz₀⟩
    obtain ⟨m, ρ, r, hρ, hr, hball_x, hball_z⟩ :=
      exists_local_exhaustion_box hD_step hD_uni hC_step hC_uni hx₀ hz₀
    exact (contDiffOn_shell_series_box hD_mono hC_mono hD_sub hC_sub hu_cd hu_hol hu_bd hr
      hball_x hball_z).contDiffAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hρ, mem_ball_self hr⟩)
      |>.contDiffWithinAt
  · intro x₀ hx₀ z₀ hz₀
    obtain ⟨m, ρ, r, hρ, hr, hball_x, hball_z⟩ :=
      exists_local_exhaustion_box hD_step hD_uni hC_step hC_uni hx₀ hz₀
    have hball_C : ball z₀ r ⊆ interior (C (m + 1)) :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hball_z
    exact conjWirtingerDeriv_shell_series hs hΩ hD_mono hC_mono hχ_sum hu_cd hu_dbar hu_hol hu_bd
      hx₀ hz₀ hr (hball_x (mem_ball_self hρ)) hball_C
  · intro x₀ hx₀ z₀ hz₀
    obtain ⟨m, ρ, r, hρ, hr, hball_x, hball_z⟩ :=
      exists_local_exhaustion_box hD_step hD_uni hC_step hC_uni hx₀ hz₀
    have hz_C : z₀ ∈ C (m + 1) :=
      interior_subset (hball_z (mem_closedBall_self (by positivity)))
    exact differentiableAt_shell_series_param hD_mono hC_mono hD_sub hu_q hu_bd hx₀ hz₀ hρ
      hball_x hz_C

/-- **Global `bar∂` solver on arbitrary open plane domains with smooth parameters.** Let `s ⊆ P`
be an open subset of a proper real normed space, let `Ω ⊆ ℂ` be open, and let `f : P → ℂ → F` be
smooth on `s ×ˢ Ω` with values in a complex Banach space `F`. Then some smooth `u : P → ℂ → F` on
`s ×ˢ Ω` satisfies `conjWirtingerDeriv (u p) z 1 = f p z` for all `p ∈ s` and `z ∈ Ω`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_param
    {s : Set P} {Ω : Set ℂ} {f : P → ℂ → F} (hs : IsOpen s) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ ↿f (s ×ˢ Ω)) :
    ∃ u : P → ℂ → F,
      ContDiffOn ℝ ∞ ↿u (s ×ˢ Ω) ∧
      ∀ p ∈ s, ∀ z ∈ Ω, conjWirtingerDeriv (u p) z 1 = f p z := by
  let f' : P × (Fin 0 → ℂ) → ℂ → F := fun x z ↦ f x.1 z
  have hf' : ContDiffOn ℝ ∞ ↿f' ((s ×ˢ (univ : Set (Fin 0 → ℂ))) ×ˢ Ω) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      fun _ hp ↦ ⟨hp.1.1, hp.2⟩
  obtain ⟨u', hu'_cd, hu'_dbar, -⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param
      (hs.prod isOpen_univ) hΩ hf' fun _ _ _ _ ↦ by simp [f']
  refine ⟨fun p z ↦ u' (p, 0) z, ?_, fun p hp z hz ↦ hu'_dbar (p, 0) ⟨hp, mem_univ _⟩ z hz⟩
  exact hu'_cd.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd).contDiffOn
    fun _ hp ↦ ⟨⟨hp.1, mem_univ _⟩, hp.2⟩

end GlobalSolver

section ParameterFree

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Telescoping step along an exhaustion `C` of `Ω ⊆ ℂ`: if consecutive differences
`h (k + 1) - h k` are holomorphic on `interior (C (k + 1))` and approximated within `2⁻ᵏ` on `C k`
by functions `g k` holomorphic on `Ω`, then on `interior (C m)` the corrected series
`h 0 + ∑' k, (h (k + 1) - h k - g k)` equals `h m` plus a holomorphic function. -/
private theorem exists_differentiableOn_eqOn_add_tsum_exhaustion {Ω : Set ℂ} {C : ℕ → Set ℂ}
    {h g : ℕ → ℂ → F} (hC_mono : Monotone C) (hC_sub : ∀ j, C j ⊆ Ω)
    (hg : ∀ k, DifferentiableOn ℂ (g k) Ω)
    (hdiff : ∀ k, DifferentiableOn ℂ (h (k + 1) - h k) (interior (C (k + 1))))
    (hg_lt : ∀ k, ∀ z ∈ C k, ‖(h (k + 1) - h k) z - g k z‖ < (1 / 2 : ℝ) ^ k) (m : ℕ) :
    ∃ K : ℂ → F, DifferentiableOn ℂ K (interior (C m)) ∧
      EqOn (fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - g k) z) (h m + K) (interior (C m)) := by
  set e : ℕ → ℂ → F := fun k ↦ h (k + 1) - h k - g k
  have he_le {k : ℕ} (hmk : m ≤ k) {z : ℂ} (hz : z ∈ interior (C m)) :
      ‖e k z‖ ≤ (1 / 2 : ℝ) ^ k :=
    (hg_lt k z (hC_mono hmk (interior_subset hz))).le
  have hsumm : Summable fun k ↦ (1 / 2 : ℝ) ^ (k + m) :=
    (summable_nat_add_iff m).2 summable_geometric_two
  refine ⟨fun z ↦ ∑' k, e (k + m) z - ∑ k ∈ Finset.range m, g k z, ?_, fun z hz ↦ ?_⟩
  · refine DifferentiableOn.sub ?_ (DifferentiableOn.fun_sum fun k _ ↦
      (hg k).mono (interior_subset.trans (hC_sub m)))
    refine (tendstoUniformlyOn_tsum hsumm fun k z hz ↦ he_le (Nat.le_add_left m k) hz)
      |>.differentiableOn (.of_forall fun _ ↦ DifferentiableOn.fun_sum fun k _ ↦ ?_)
      isOpen_interior
    exact ((hdiff (k + m)).mono (interior_mono (hC_mono (by omega)))).sub
      ((hg (k + m)).mono (interior_subset.trans (hC_sub m)))
  · have hs : Summable fun k ↦ e k z := (summable_nat_add_iff m).1 <|
      .of_norm_bounded hsumm fun k ↦ he_le (Nat.le_add_left m k) hz
    have htel : ∑ k ∈ Finset.range m, e k z = h m z - h 0 z - ∑ k ∈ Finset.range m, g k z := by
      simp only [e, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_range_sub fun k ↦ h k z]
    simp only [Pi.add_apply]
    rw [← hs.sum_add_tsum_nat_add m, htel]
    abel

/-- **Global `bar∂` solver on an arbitrary open set in `ℂ`.** Every `C^n` function `f : ℂ → F`
(`1 ≤ n`) on an open set `Ω ⊆ ℂ` with values in a complex Banach space `F` satisfies `bar∂ u = f`
on `Ω` for some `C^n` function `u : ℂ → F` on `Ω`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq
    {n : ℕ∞} {Ω : Set ℂ} {f : ℂ → F} (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ n f Ω) :
    ∃ u : ℂ → F,
      ContDiffOn ℝ n u Ω ∧ ∀ z ∈ Ω, conjWirtingerDeriv u z 1 = f z := by
  obtain ⟨C, hC_cpt, hC_step, hC_uni, hC_fill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hC_mono : Monotone C := monotone_nat_of_le_succ fun j ↦ (hC_step j).trans interior_subset
  have hC_sub (j : ℕ) : C j ⊆ Ω := hC_uni ▸ subset_iUnion C j
  -- Local `C^n` solutions `h k` with `bar∂ (h k) = f` on `C (k + 1)`.
  have hloc (k : ℕ) : ∃ h : ℂ → F, ContDiff ℝ n h ∧
      ∀ z ∈ C (k + 1), conjWirtingerDeriv h z 1 = f z := by
    obtain ⟨ψ, hψ_cd, -, hψ_one, hψ_cpt, hψ_ts⟩ :=
      (hC_cpt (k + 1)).exists_contDiff_cutoff hΩ (hC_sub (k + 1))
    obtain ⟨h, hh, hheq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport
      hn (hf.contDiff_smul_of_tsupport_subset hΩ
        (hψ_cd.of_le (by exact_mod_cast le_top)).contDiffOn hψ_ts) hψ_cpt.smul_right
    refine ⟨h, hh, fun z hz ↦ ?_⟩
    have hψz : ψ z = 1 := by simpa using interior_subset (hψ_one hz)
    simpa [hψz] using hheq z
  choose h hh hh_eq using hloc
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  have hd (k : ℕ) : Differentiable ℝ (h k) := (hh k).differentiable hn0
  -- Consecutive differences `h (k + 1) - h k` are holomorphic on `interior (C (k + 1))`.
  have hdiff (k : ℕ) : DifferentiableOn ℂ (h (k + 1) - h k) (interior (C (k + 1))) := fun z hz ↦ by
    refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
      ((hd (k + 1)).sub (hd k) z)).2 ?_).differentiableWithinAt
    rw [conjWirtingerDeriv_sub (hd (k + 1) z) (hd k z), sub_apply,
      hh_eq (k + 1) z (hC_mono (k + 1).le_succ (interior_subset hz)),
      hh_eq k z (interior_subset hz), sub_self]
  -- Runge corrections `g k` holomorphic on `Ω`, approximating `h (k + 1) - h k` within `2⁻ᵏ`.
  have happrox (k : ℕ) : ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ C k, ‖(h (k + 1) - h k) z - g z‖ < (1 / 2 : ℝ) ^ k :=
    (hC_fill k).exists_differentiableOn_norm_sub_lt hΩ (hC_cpt k) (hC_sub k) isOpen_interior
      (hC_step k) (hdiff k) (by positivity)
  choose g hg hg_lt using happrox
  set u : ℂ → F := fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - g k) z
  have hglue := contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add (G := u) (n := n) (U := Ω)
    (v := fun _ : Unit ↦ (1 : ℂ)) (f := fun _ ↦ f) (by exact_mod_cast hn) fun z hz ↦ by
      obtain ⟨m, hm⟩ := mem_iUnion.1 (hC_uni.symm ▸ hz)
      obtain ⟨K, hK, huK⟩ :=
        exists_differentiableOn_eqOn_add_tsum_exhaustion hC_mono hC_sub hg hdiff hg_lt (m + 1)
      exact ⟨interior (C (m + 1)), isOpen_interior, hC_step m hm, h (m + 1), K,
        (hh (m + 1)).contDiffOn,
        fun w hw _ ↦ hh_eq (m + 1) w (hC_mono (m + 1).le_succ (interior_subset hw)),
        hK.contDiffOn isOpen_interior, huK⟩
  exact ⟨u, hglue.1, fun z hz ↦ hglue.2 z hz ()⟩

end ParameterFree

end TauCeti
