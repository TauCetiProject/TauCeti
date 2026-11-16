/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Distance to subspaces and orthogonal projections

For subspaces `P` and `Q` of an inner product space over `𝕜` admitting orthogonal projections,
this file relates `Metric.infDist` to a subspace with its orthogonal projection:

* `Submodule.antilipschitzWith_orthogonalProjectionOnto_of_forall_infDist_le`: on a set `s` whose
  secants satisfy the strict cone bound `infDist (y - x) P ≤ α * dist y x` (`α < 1`), restricting
  `P.orthogonalProjectionOnto` to `s` is antilipschitz with constant
  `(Real.toNNReal (1 - max α 0))⁻¹`.
* `Submodule.infDist_le_infDist_add_norm_starProjection_sub_mul`: replacing `P` by `Q` changes
  `infDist v ·` by at most `‖P.starProjection - Q.starProjection‖ * ‖v‖`.
* `TauCeti.exists_countable_finrank_eq_and_norm_starProjection_sub_lt`: in a second-countable
  inner product space, the `k`-dimensional subspaces admit a countable subfamily whose orthogonal
  projections are dense in operator norm among those of all `k`-dimensional subspaces.
-/

public section

namespace Submodule

open Metric Set
open scoped NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- On a set `s` whose secants lie in the strict cone `infDist (y - x) P ≤ α * dist y x` (`α < 1`)
around a subspace `P` admitting an orthogonal projection, restricting `P.orthogonalProjectionOnto`
to `s` is antilipschitz with constant `(Real.toNNReal (1 - max α 0))⁻¹`. -/
theorem antilipschitzWith_orthogonalProjectionOnto_of_forall_infDist_le
    (P : Submodule 𝕜 E) [P.HasOrthogonalProjection] {s : Set E} {α : ℝ} (hα : α < 1)
    (h : ∀ x ∈ s, ∀ y ∈ s, infDist (y - x) (P : Set E) ≤ α * dist y x) :
    AntilipschitzWith (Real.toNNReal (1 - max α 0))⁻¹
      (s.domRestrict P.orthogonalProjectionOnto) := by
  set β := max α 0
  have hβ1 : 0 < 1 - β := sub_pos.2 (max_lt hα zero_lt_one)
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have htri : dist (y : E) x ≤
      dist (P.orthogonalProjectionOnto y) (P.orthogonalProjectionOnto x) +
        infDist ((y : E) - x) (P : Set E) := by
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, ← Submodule.coe_sub, ← map_sub,
      ← P.starProjection_apply, ← P.dist_starProjection_eq_infDist, dist_eq_norm]
    simpa only [add_sub_cancel] using norm_add_le (P.starProjection ((y : E) - x))
      ((y : E) - x - P.starProjection ((y : E) - x))
  have hle : (1 - β) * dist (x : E) y ≤
      dist (s.domRestrict P.orthogonalProjectionOnto x)
        (s.domRestrict P.orthogonalProjectionOnto y) := by
    have hinf : infDist ((y : E) - x) (P : Set E) ≤ β * dist (y : E) x :=
      (h x.1 x.2 y.1 y.2).trans (mul_le_mul_of_nonneg_right (le_max_left α 0) dist_nonneg)
    rw [dist_comm (x : E), domRestrict_apply, domRestrict_apply,
      dist_comm (P.orthogonalProjectionOnto x)]
    linarith
  rw [NNReal.coe_inv, Real.coe_toNNReal _ hβ1.le, inv_mul_eq_div, le_div_iff₀ hβ1, mul_comm]
  exact hle

/-- Replacing a subspace `P` by `Q` increases `infDist v ·` by at most
`‖P.starProjection - Q.starProjection‖ * ‖v‖`. -/
theorem infDist_le_infDist_add_norm_starProjection_sub_mul (P Q : Submodule 𝕜 E)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] (v : E) :
    infDist v (Q : Set E) ≤
      infDist v (P : Set E) + ‖P.starProjection - Q.starProjection‖ * ‖v‖ := by
  rw [← Q.dist_starProjection_eq_infDist, ← P.dist_starProjection_eq_infDist,
    dist_eq_norm, dist_eq_norm]
  have hsplit : v - Q.starProjection v =
      (v - P.starProjection v) + (P.starProjection - Q.starProjection) v := by
    simp
  calc ‖v - Q.starProjection v‖
      ≤ ‖v - P.starProjection v‖ + ‖(P.starProjection - Q.starProjection) v‖ :=
        hsplit ▸ norm_add_le _ _
    _ ≤ ‖v - P.starProjection v‖ + ‖P.starProjection - Q.starProjection‖ * ‖v‖ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _

end Submodule

namespace TauCeti

open Metric Module Set TopologicalSpace

/-- In a second-countable inner product space over `𝕜`, there exists a countable family of
`k`-dimensional subspaces whose orthogonal projections are dense in operator norm among those of
all `k`-dimensional subspaces. -/
theorem exists_countable_finrank_eq_and_norm_starProjection_sub_lt (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [SecondCountableTopology E] (k : ℕ) :
    ∃ (S : Set (Submodule 𝕜 E)) (_ : ∀ Q : S, FiniteDimensional 𝕜 Q.1),
      S.Countable ∧ (∀ Q : S, finrank 𝕜 Q.1 = k) ∧
      ∀ (P : Submodule 𝕜 E) [FiniteDimensional 𝕜 P], finrank 𝕜 P = k →
        ∀ ε > (0 : ℝ), ∃ Q : S, ‖P.starProjection - Q.1.starProjection‖ < ε := by
  let O : Set (Fin k → E) := {u | Orthonormal 𝕜 u}
  rcases O.eq_empty_or_nonempty with hO | hk
  · refine ⟨∅, fun Q => Q.2.elim, countable_empty, fun Q => Q.2.elim, fun P _ hP => ?_⟩
    let b := (stdOrthonormalBasis 𝕜 P).reindex (finCongr hP)
    have hbO : (fun i => (b i : E)) ∈ O := P.subtypeₗᵢ.orthonormal_comp_iff.mpr b.orthonormal
    exact False.elim ((hO ▸ hbO : (fun i => (b i : E)) ∈ (∅ : Set (Fin k → E))))
  have := hk.to_subtype
  let u : ℕ → O := denseSeq O
  let Q : ℕ → Submodule 𝕜 E := fun j => Submodule.span 𝕜 (range (u j : Fin k → E))
  have hQfin (j : ℕ) : FiniteDimensional 𝕜 (Q j) :=
    FiniteDimensional.span_of_finite 𝕜 (finite_range _)
  have hQrk (j : ℕ) : finrank 𝕜 (Q j) = k :=
    (finrank_span_eq_card (u j).2.linearIndependent).trans (Fintype.card_fin k)
  let Φ : (Fin k → E) → (E →L[𝕜] E) :=
    fun w => ∑ i : Fin k, InnerProductSpace.rankOne 𝕜 (w i) (w i)
  have hΦ : Continuous Φ := by
    have hterm (i : Fin k) : Continuous fun w : Fin k → E =>
        InnerProductSpace.rankOne 𝕜 (w i) (w i) :=
      (((ContinuousLinearMap.smulRightL 𝕜 E E).continuous.comp
        ((innerSL 𝕜).continuous.comp (continuous_apply i))).clm_apply (continuous_apply i))
    fun_prop
  have hQproj (j : ℕ) : (Q j).starProjection = Φ (u j) := by
    let v : Fin k → Q j := fun i => ⟨(u j : Fin k → E) i, Submodule.subset_span (mem_range_self i)⟩
    have hv : Orthonormal 𝕜 v := (Q j).subtypeₗᵢ.orthonormal_comp_iff.mp (u j).2
    have hsp : ⊤ ≤ Submodule.span 𝕜 (range v) := (Submodule.eq_top_of_finrank_eq
      ((finrank_span_eq_card hv.linearIndependent).trans
        ((Fintype.card_fin k).trans (hQrk j).symm))).ge
    let b : OrthonormalBasis (Fin k) 𝕜 (Q j) := OrthonormalBasis.mk hv hsp
    simpa only [Φ, b, v, OrthonormalBasis.coe_mk] using b.starProjection_eq_sum_rankOne
  refine ⟨range Q, ?_, countable_range Q, ?_, fun P _ hP ε hε => ?_⟩
  · rintro ⟨_, j, rfl⟩
    exact hQfin j
  · rintro ⟨_, j, rfl⟩
    exact hQrk j
  let b := (stdOrthonormalBasis 𝕜 P).reindex (finCongr hP)
  let w : O := ⟨fun i => (b i : E), P.subtypeₗᵢ.orthonormal_comp_iff.mpr b.orthonormal⟩
  have hPproj : P.starProjection = Φ w := b.starProjection_eq_sum_rankOne
  obtain ⟨δ, hδ, hδball⟩ := Metric.continuousAt_iff.1
    ((hΦ.comp continuous_subtype_val).continuousAt (x := w)) ε hε
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq O) w δ hδ
  refine ⟨⟨Q j, mem_range_self j⟩, ?_⟩
  rw [hPproj, hQproj j, ← dist_eq_norm, dist_comm]
  exact hδball (by simpa only [dist_comm] using hj)

end TauCeti
