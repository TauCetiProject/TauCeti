/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import TauCeti.Analysis.Calculus.CoordinateDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Termwise differentiation of series in coordinates

Let `f j` be smooth functions of a position and a frequency `p ∈ ℝⁿ × ℝⁿ`, indexed by a type `ι`.
Suppose that every mixed derivative `∂_x^α ∂_ξ^β f j` is bounded near each point by a summable
family of constants (`TauCeti.LocallySummableMixedDeriv`). Then the series `∑' j, f j` is smooth
(`TauCeti.contDiff_tsum_of_locallySummableMixedDeriv`) and its mixed derivatives are the series of
the mixed derivatives (`TauCeti.mixedDeriv_tsum_of_locallySummableMixedDeriv`). The bounds only
need to hold locally, so this applies to series such as `∑ j, g (x - j, ξ)` over a lattice, whose
terms decay away from the lattice point `j` but are not summable uniformly in the position.

This is the series counterpart of differentiation under the integral sign in coordinates,
`TauCeti.differentiableAt_integral_and_fderiv_apply_eq_sum`; it rests on Mathlib's
`hasFDerivAt_tsum_of_isPreconnected`.
-/

public section

open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}

/-- A family of smooth functions on `ℝⁿ × ℝⁿ` whose mixed derivatives `∂_x^α ∂_ξ^β f j` are
bounded, on the unit ball around each point, by a summable family of constants. -/
structure LocallySummableMixedDeriv (f : ι → CoordinateSpace n × CoordinateSpace n → F) :
    Prop where
  /-- Every term is smooth. -/
  contDiff (j : ι) : ContDiff ℝ ∞ (f j)
  /-- Near each point, the mixed derivatives of the terms are bounded by a summable family. -/
  exists_summable_bound (α β : List (Fin n)) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ u : ι → ℝ, Summable u ∧
      ∀ j, ∀ p ∈ Metric.ball p₀ 1, ‖mixedDeriv α β (f j) p.1 p.2‖ ≤ u j

namespace LocallySummableMixedDeriv

variable {f : ι → CoordinateSpace n × CoordinateSpace n → F}

/-- The family of position derivatives `∂_{x_i} f j` again has locally summable mixed
derivatives. -/
theorem coordinateDeriv_fst (hf : LocallySummableMixedDeriv f) (i : Fin n) :
    LocallySummableMixedDeriv fun j p ↦ coordinateDeriv [i] (fun y ↦ f j (y, p.2)) p.1 := by
  refine ⟨fun j ↦ (hf.contDiff j).coordinateDeriv_fst [i], fun α β p₀ ↦ ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.exists_summable_bound (α ++ [i]) β p₀
  exact ⟨u, hu, fun j p hp ↦ by
    rw [mixedDeriv_coordinateDeriv_fst (hf.contDiff j)]
    exact hb j p hp⟩

/-- The family of frequency derivatives `∂_{ξ_i} f j` again has locally summable mixed
derivatives. -/
theorem coordinateDeriv_snd (hf : LocallySummableMixedDeriv f) (i : Fin n) :
    LocallySummableMixedDeriv fun j p ↦ coordinateDeriv [i] (fun η ↦ f j (p.1, η)) p.2 := by
  refine ⟨fun j ↦ (hf.contDiff j).coordinateDeriv_snd [i], fun α β p₀ ↦ ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.exists_summable_bound α (β ++ [i]) p₀
  exact ⟨u, hu, fun j p hp ↦ by rw [mixedDeriv_coordinateDeriv_snd]; exact hb j p hp⟩

/-- At each point the values of the family are summable. -/
theorem summable [CompleteSpace F] (hf : LocallySummableMixedDeriv f)
    (p : CoordinateSpace n × CoordinateSpace n) : Summable fun j ↦ f j p := by
  obtain ⟨u, hu, hb⟩ := hf.exists_summable_bound [] [] p
  exact hu.of_norm_bounded fun j ↦ by
    simpa [mixedDeriv_nil_nil] using hb j p (Metric.mem_ball_self one_pos)

variable [CompleteSpace F]

/-- The derivatives of the terms are summable, and the series is differentiable with derivative
the series of the derivatives. -/
private theorem hasFDerivAt_tsum_and_summable (hf : LocallySummableMixedDeriv f)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (fun p ↦ ∑' j, f j p) (∑' j, fderiv ℝ (f j) p₀) p₀ ∧
      Summable fun j ↦ fderiv ℝ (f j) p₀ := by
  choose u hu hb using fun i ↦ hf.exists_summable_bound [i] [] p₀
  choose w hw hc using fun i ↦ hf.exists_summable_bound [] [i] p₀
  have hd (j : ι) (p : CoordinateSpace n × CoordinateSpace n) : DifferentiableAt ℝ (f j) p :=
    ((hf.contDiff j).differentiable (by simp)) p
  have hnorm (j : ι) (p : CoordinateSpace n × CoordinateSpace n) (hp : p ∈ Metric.ball p₀ 1) :
      ‖fderiv ℝ (f j) p‖ ≤ ∑ i, u i j + ∑ i, w i j := by
    refine ((fderiv ℝ (f j) p).opNorm_le_of_apply_eq_sum _ _
      (fderiv_apply_eq_sum_coordinateDeriv (hd j p))).trans (add_le_add
        (Finset.sum_le_sum fun i _ ↦ ?_) (Finset.sum_le_sum fun i _ ↦ ?_))
    · simpa [mixedDeriv_def] using hb i j p hp
    · simpa [mixedDeriv_def] using hc i j p hp
  have hU : Summable fun j ↦ ∑ i, u i j + ∑ i, w i j :=
    (summable_sum fun i _ ↦ hu i).add (summable_sum fun i _ ↦ hw i)
  have hmem := Metric.mem_ball_self (x := p₀) one_pos
  exact ⟨hasFDerivAt_tsum_of_isPreconnected hU Metric.isOpen_ball
    (convex_ball p₀ 1).isPreconnected (fun j p _ ↦ (hd j p).hasFDerivAt) hnorm hmem
    (hf.summable p₀) hmem, hU.of_norm_bounded fun j ↦ hnorm j p₀ hmem⟩

/-- At each point the derivatives of the terms are summable. -/
theorem summable_fderiv (hf : LocallySummableMixedDeriv f)
    (p : CoordinateSpace n × CoordinateSpace n) : Summable fun j ↦ fderiv ℝ (f j) p :=
  (hf.hasFDerivAt_tsum_and_summable p).2

/-- The series is differentiable, with derivative the series of the derivatives. -/
theorem hasFDerivAt_tsum (hf : LocallySummableMixedDeriv f)
    (p : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (fun p ↦ ∑' j, f j p) (∑' j, fderiv ℝ (f j) p) p :=
  (hf.hasFDerivAt_tsum_and_summable p).1

/-- The derivative of the series in the direction `v` is the series of the coordinate derivatives
weighted by the coordinates of `v`. -/
theorem fderiv_tsum_apply (hf : LocallySummableMixedDeriv f)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p ↦ ∑' j, f j p) p v =
      ∑ i, v.1 i • ∑' j, coordinateDeriv [i] (fun y ↦ f j (y, p.2)) p.1 +
        ∑ i, v.2 i • ∑' j, coordinateDeriv [i] (fun η ↦ f j (p.1, η)) p.2 := by
  have h := hf.hasFDerivAt_tsum p
  have hs := hf.summable_fderiv p
  have hd (j : ι) : DifferentiableAt ℝ (f j) p := ((hf.contDiff j).differentiable (by simp)) p
  have hx (i : Fin n) := (hf.coordinateDeriv_fst i).summable p
  have hξ (i : Fin n) := (hf.coordinateDeriv_snd i).summable p
  rw [h.fderiv, ← ContinuousLinearMap.apply_apply (𝕜 := ℝ) v,
    ContinuousLinearMap.map_tsum _ hs]
  simp only [ContinuousLinearMap.apply_apply, fderiv_apply_eq_sum_coordinateDeriv (hd _)]
  rw [Summable.tsum_add (summable_sum fun i _ ↦ (hx i).const_smul _)
    (summable_sum fun i _ ↦ (hξ i).const_smul _), Summable.tsum_finsetSum fun i _ ↦
      (hx i).const_smul _, Summable.tsum_finsetSum fun i _ ↦ (hξ i).const_smul _]
  simp only [Summable.tsum_const_smul _ (hx _), Summable.tsum_const_smul _ (hξ _)]

/-- The position derivative of the series is the series of the position derivatives. -/
theorem coordinateDeriv_fst_tsum (hf : LocallySummableMixedDeriv f) (i : Fin n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    coordinateDeriv [i] (fun y ↦ ∑' j, f j (y, p.2)) p.1 =
      ∑' j, coordinateDeriv [i] (fun y ↦ f j (y, p.2)) p.1 := by
  rw [coordinateDeriv_fst_eq_fderiv (f := fun p ↦ ∑' j, f j p)
    (hf.hasFDerivAt_tsum p).differentiableAt, fderiv_tsum_apply hf]
  simp [PiLp.single_apply]

/-- The frequency derivative of the series is the series of the frequency derivatives. -/
theorem coordinateDeriv_snd_tsum (hf : LocallySummableMixedDeriv f) (i : Fin n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    coordinateDeriv [i] (fun η ↦ ∑' j, f j (p.1, η)) p.2 =
      ∑' j, coordinateDeriv [i] (fun η ↦ f j (p.1, η)) p.2 := by
  rw [coordinateDeriv_snd_eq_fderiv (f := fun p ↦ ∑' j, f j p)
    (hf.hasFDerivAt_tsum p).differentiableAt, fderiv_tsum_apply hf]
  simp [PiLp.single_apply]

/-- The series is `C^k` for every `k`. -/
private theorem contDiff_nat (k : ℕ) :
    ∀ {f : ι → CoordinateSpace n × CoordinateSpace n → F}, LocallySummableMixedDeriv f →
      ContDiff ℝ k fun p ↦ ∑' j, f j p := by
  induction k with
  | zero =>
    intro f hf
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p ↦
      (hf.hasFDerivAt_tsum p).continuousAt)
  | succ k ih =>
    intro f hf
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv_apply.2 ⟨fun p ↦ (hf.hasFDerivAt_tsum p).differentiableAt,
      by simp, fun v ↦ ?_⟩
    simp_rw [hf.fderiv_tsum_apply]
    exact (ContDiff.sum fun i _ ↦ (contDiff_const.smul (ih (hf.coordinateDeriv_fst i)))).add
      (ContDiff.sum fun i _ ↦ (contDiff_const.smul (ih (hf.coordinateDeriv_snd i))))

end LocallySummableMixedDeriv

variable [CompleteSpace F] {f : ι → CoordinateSpace n × CoordinateSpace n → F}

/-- **Smoothness of a series.** A series of smooth functions on `ℝⁿ × ℝⁿ` whose mixed derivatives
are locally bounded by summable families is smooth. -/
theorem contDiff_tsum_of_locallySummableMixedDeriv (hf : LocallySummableMixedDeriv f) :
    ContDiff ℝ ∞ fun p ↦ ∑' j, f j p :=
  contDiff_infty.2 fun k ↦ LocallySummableMixedDeriv.contDiff_nat k hf

/-- **Termwise differentiation.** The mixed derivatives of a series of smooth functions on
`ℝⁿ × ℝⁿ` whose mixed derivatives are locally bounded by summable families are the series of the
mixed derivatives. -/
theorem mixedDeriv_tsum_of_locallySummableMixedDeriv (hf : LocallySummableMixedDeriv f)
    (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p ↦ ∑' j, f j p) x ξ = ∑' j, mixedDeriv α β (f j) x ξ := by
  induction β using List.reverseRecOn generalizing f α x ξ with
  | nil =>
    induction α using List.reverseRecOn generalizing f x ξ with
    | nil => simp [mixedDeriv_nil_nil]
    | append_singleton α i ih =>
      rw [← mixedDeriv_coordinateDeriv_fst (contDiff_tsum_of_locallySummableMixedDeriv hf)]
      simp_rw [hf.coordinateDeriv_fst_tsum i]
      rw [ih (hf.coordinateDeriv_fst i)]
      exact tsum_congr fun j ↦ mixedDeriv_coordinateDeriv_fst (hf.contDiff j) α [] i x ξ
  | append_singleton β i ih =>
    rw [← mixedDeriv_coordinateDeriv_snd]
    simp_rw [hf.coordinateDeriv_snd_tsum i]
    rw [ih (hf.coordinateDeriv_snd i)]
    exact tsum_congr fun j ↦ mixedDeriv_coordinateDeriv_snd α β i (f j) x ξ

end TauCeti
