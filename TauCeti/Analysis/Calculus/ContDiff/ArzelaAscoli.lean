/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Arzelà–Ascoli for smooth functions on a ball

Let `f_i` be smooth functions on a ball `B_R(p)` of a finite-dimensional normed space, with values
in a finite-dimensional normed space, such that for every order `k` and every `r < R` the `k`-th
derivatives `D^k f_i` are bounded on `closed ball B_r(p)` uniformly in `i`. Then a subsequence converges
smoothly on compact subsets of the ball: there is a smooth `g` on `B_R(p)` such that, for every
`k` and every `r < R`, `D^k f_(φ i) → D^k g` uniformly on `closed ball B_r(p)`.

On each closed ball `closed ball B_r(p)` the bound on `D^(k+1) f_i` makes the `D^k f_i` uniformly Lipschitz,
so by the Arzelà–Ascoli theorem they lie in a compact set of bounded continuous functions. The
countable product over orders `k` and radii `r_m ↑ R` of these compact sets is compact and first
countable, which gives one subsequence converging in every factor. The limits of the derivatives
form a Taylor series of the limit of the functions, by the theorem on uniform limits of
derivatives.

## Main declarations

* `TauCeti.exists_subseq_tendstoUniformlyOn_iteratedFDeriv`: the subsequence and its smooth
  limit.
-/

public noncomputable section

open Filter Function Metric Set
open scoped BoundedContinuousFunction ContDiff Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function smooth on a ball has differentiable derivatives of every order there. -/
private theorem differentiableAt_iteratedFDeriv_of_contDiffOn_ball {f : E → F} {p : E} {R : ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball p R)) (k : ℕ) {x : E} (hx : x ∈ ball p R) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x := by
  have h := hf.differentiableOn_iteratedFDerivWithin (m := k)
    (mod_cast ENat.natCast_lt_top k) isOpen_ball.uniqueDiffOn
  exact (h.congr fun y hy ↦ (iteratedFDerivWithin_of_isOpen k isOpen_ball hy).symm).differentiableAt
    (isOpen_ball.mem_nhds hx)

/-- A uniform bound on `D^(k+1) f` on a closed ball makes `D^k f` Lipschitz there. -/
private theorem norm_iteratedFDeriv_sub_le {f : E → F} {p : E} {R r C : ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball p R)) (hr : r < R) (k : ℕ)
    (hC : ∀ x ∈ closedBall p r, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ C) {x y : E}
    (hx : x ∈ closedBall p r) (hy : y ∈ closedBall p r) :
    ‖iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k f x‖ ≤ C * ‖y - x‖ :=
  (convex_closedBall p r).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ differentiableAt_iteratedFDeriv_of_contDiffOn_ball hf k
      (closedBall_subset_ball hr hz))
    (fun z hz ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hC z hz) hx hy

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Arzelà–Ascoli for smooth functions on a ball.** If smooth functions `f_i` on `B_R(p)` have,
for every order `k` and every `r < R`, `k`-th derivatives bounded on `closed ball B_r(p)` uniformly in `i`,
then a subsequence converges smoothly on compact subsets of the ball to a smooth function `g`:
`D^k f_(φ i) → D^k g` uniformly on every `closed ball B_r(p)` with `r < R`, for every `k`. -/
theorem exists_subseq_tendstoUniformlyOn_iteratedFDeriv {f : ℕ → E → F} {p : E} {R : ℝ}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (ball p R))
    (hbd : ∀ k : ℕ, ∀ r < R, ∃ C, ∀ i, ∀ x ∈ closedBall p r,
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : E → F, ContDiffOn ℝ ∞ g (ball p R) ∧
      ∀ k : ℕ, ∀ r < R, TendstoUniformlyOn (fun i ↦ iteratedFDeriv ℝ k (f (φ i)))
        (iteratedFDeriv ℝ k g) atTop (closedBall p r) := by
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨id, strictMono_id, 0, ?_, fun k r hr ↦ ?_⟩
    · rw [ball_eq_empty.2 hR]
      exact contDiffOn_empty
    · rw [closedBall_eq_empty.2 (by linarith)]
      exact tendstoUniformlyOn_empty
  set rad : ℕ → ℝ := fun m ↦ R - R / (m + 2) with hrad
  have hrad_lt (m : ℕ) : rad m < R := by
    have : 0 < R / (m + 2) := by positivity
    simp only [hrad]
    linarith
  have hrad_ex {r : ℝ} (hr : r < R) : ∃ m, r ≤ rad m := by
    obtain ⟨m, hm⟩ := exists_nat_gt (R / (R - r))
    refine ⟨m, ?_⟩
    have h1 : R / (m + 2) ≤ R - r := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by linarith)] at hm
      nlinarith
    simp only [hrad]
    linarith
  have hmem {x : E} (hx : x ∈ ball p R) : ∃ m, x ∈ ball p (rad m) := by
    rw [mem_ball] at hx
    obtain ⟨m, hm⟩ := hrad_ex (show (dist x p + R) / 2 < R by linarith)
    exact ⟨m, mem_ball.2 (by linarith)⟩
  choose C hC using fun q : ℕ × ℕ ↦ hbd q.1 (rad q.2) (hrad_lt q.2)
  have hcpt (m : ℕ) : CompactSpace (closedBall p (rad m)) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall p (rad m))
  have hcont (i k : ℕ) : ContinuousOn (iteratedFDeriv ℝ k (f i)) (ball p R) := fun x hx ↦
    (differentiableAt_iteratedFDeriv_of_contDiffOn_ball (hf i) k hx).continuousAt.continuousWithinAt
  let Φ : ℕ → ∀ q : ℕ × ℕ,
      closedBall p (rad q.2) →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin q.1 ↦ E) F :=
    fun i q ↦ have := hcpt q.2
      BoundedContinuousFunction.mkOfCompact ⟨fun x ↦ iteratedFDeriv ℝ q.1 (f i) x,
        (hcont i q.1).comp_continuous continuous_subtype_val
          fun x ↦ closedBall_subset_ball (hrad_lt q.2) x.2⟩
  have hΦ (i : ℕ) (q : ℕ × ℕ) (x : closedBall p (rad q.2)) :
      Φ i q x = iteratedFDeriv ℝ q.1 (f i) x := rfl
  have hS (q : ℕ × ℕ) : IsCompact (closure (range fun i ↦ Φ i q)) := by
    have := hcpt q.2
    have : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin q.1 ↦ E) F) :=
      FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ)
        (A := ℝ) (M₁ := fun _ : Fin q.1 ↦ E) (M₂ := F))
        ContinuousMultilinearMap.toMultilinearMap_injective
    refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 (C q))
      (isCompact_closedBall 0 (C q)) _ ?_ ?_
    · rintro _ x ⟨i, rfl⟩
      rw [mem_closedBall_zero_iff, hΦ]
      exact hC q i x x.2
    · refine Metric.equicontinuous_of_continuity_modulus (fun t ↦ C (q.1 + 1, q.2) * t)
        (by
          have h : Continuous fun t : ℝ ↦ C (q.1 + 1, q.2) * t := continuous_const.mul continuous_id
          simpa using h.tendsto 0) _ ?_
      rintro x y ⟨_, i, rfl⟩
      rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
      exact norm_iteratedFDeriv_sub_le (hf i) (hrad_lt q.2) q.1 (hC (q.1 + 1, q.2) i) y.2 x.2
  obtain ⟨Ψ, -, φ, hφ, hlim⟩ := (isCompact_univ_pi hS).tendsto_subseq (x := Φ)
    fun i q _ ↦ subset_closure ⟨i, rfl⟩
  have hlimq (q : ℕ × ℕ) : TendstoUniformly
      (fun n (x : closedBall p (rad q.2)) ↦ iteratedFDeriv ℝ q.1 (f (φ n)) x) (Ψ q) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 (tendsto_pi_nhds.1 hlim q)
  let P : ∀ k : ℕ, E → ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F :=
    fun k x ↦ limUnder atTop fun n ↦ iteratedFDeriv ℝ k (f (φ n)) x
  have hunif (k m : ℕ) : TendstoUniformlyOn (fun n ↦ iteratedFDeriv ℝ k (f (φ n))) (P k) atTop
      (closedBall p (rad m)) := by
    have hPΨ : (P k ∘ (↑) : closedBall p (rad m) → _) = Ψ (k, m) :=
      funext fun x ↦ ((hlimq (k, m)).tendsto_at x).limUnder_eq
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, hPΨ]
    exact hlimq (k, m)
  set g : E → F := fun x ↦ (P 0 x).curry0
  have hT : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) g (fun x k ↦ P k x) (ball p R) := by
    refine ⟨fun x _ ↦ rfl, fun k _ x hx ↦ ?_, fun k _ ↦ ?_⟩
    · obtain ⟨m, hm⟩ := hmem hx
      have hiso := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E)
        F).isometry.uniformContinuous
      refine (hasFDerivAt_of_tendstoUniformlyOn (l := atTop) isOpen_ball
        (f := fun n ↦ iteratedFDeriv ℝ k (f (φ n)))
        (f' := fun n y ↦ continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
          (iteratedFDeriv ℝ (k + 1) (f (φ n)) y))
        (g' := fun y ↦ continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
          (P (k + 1) y))
        (hiso.comp_tendstoUniformlyOn ((hunif (k + 1) m).mono ball_subset_closedBall))
        (fun n y hy ↦ ?_) (fun y hy ↦ (hunif k m).tendsto_at (ball_subset_closedBall hy))
        hm).hasFDerivWithinAt
      have h := (differentiableAt_iteratedFDeriv_of_contDiffOn_ball (hf (φ n)) k
        (ball_subset_ball (hrad_lt m).le hy)).hasFDerivAt
      rwa [fderiv_iteratedFDeriv, comp_apply] at h
    · intro x hx
      obtain ⟨m, hm⟩ := hmem hx
      exact (((hunif k m).mono ball_subset_closedBall).continuousOn
        (Frequently.of_forall fun n ↦ (hcont (φ n) k).mono (ball_subset_ball (hrad_lt m).le))
        |>.continuousAt (isOpen_ball.mem_nhds hm)).continuousWithinAt
  have hDg (k : ℕ) {x : E} (hx : x ∈ ball p R) : iteratedFDeriv ℝ k g x = P k x :=
    ((hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast le_top) isOpen_ball.uniqueDiffOn
      hx).trans (iteratedFDerivWithin_of_isOpen k isOpen_ball hx)).symm
  refine ⟨φ, hφ, g, hT.contDiffOn, fun k r hr ↦ ?_⟩
  obtain ⟨m, hm⟩ := hrad_ex hr
  exact ((hunif k m).mono (closedBall_subset_closedBall hm)).congr_right
    fun x hx ↦ (hDg k (closedBall_subset_ball hr hx)).symm

end TauCeti
