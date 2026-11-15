/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.MeasureTheory.Rectifiable.Subspace

/-!
# Geometric cone criteria for countable rectifiability

A subset `s` of a real inner product space is countably `k`-rectifiable whenever, at every point
`x ∈ s`, `s` lies locally inside a strict cone `infDist (y - x) P ≤ α * dist y x` (`α < 1`) around
some `k`-dimensional subspace `P`. For the converse approximate tangent-cone containment almost
everywhere on bi-Lipschitz patches, see `TauCeti.Geometry.MeasureTheory.Rectifiable.TangentCone`.

When a single finite-dimensional subspace `P` and aperture `α < 1` serve globally on `s`, the
orthogonal projection of `s` into `P` has `(1 - max α 0)⁻¹`-Lipschitz inverse, so `s` is a
Lipschitz image of a subset of `P` (`TauCeti.CountablyRectifiable.of_forall_infDist_le`). In any
second-countable real inner product space, the orthogonal projections onto `k`-dimensional
subspaces form a separable family in the operator norm, as continuous images of `k`-tuples of
orthonormal vectors. Perturbing the local plane at `x ∈ s` to a countable dense subfamily of
`k`-planes and intersecting with small balls from a countable dense set of centers decomposes `s`
into countably many pieces satisfying the global cone condition
(`TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_le`).

For a finite-dimensional ambient space `V`, specializing to hyperplanes `(ℝ ∙ ν)ᗮ` orthogonal to
unit vectors `ν` yields the codimension-one normal-cone criterion
(`TauCeti.CountablyRectifiable.of_forall_exists_inner_le`), which is the geometric step in
De Giorgi's structure theorem for the reduced boundary.

## Main results

* `TauCeti.CountablyRectifiable.of_forall_infDist_le`: global cone containment around a
  finite-dimensional subspace `P` implies countable `(dim P)`-rectifiability.
* `TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_le`: local cone containment
  around `k`-dimensional subspaces at every point of `s` implies countable `k`-rectifiability.
* `TauCeti.CountablyRectifiable.of_forall_exists_inner_le`: local containment away from unit
  normal directions `ν` implies countable `(dim V - 1)`-rectifiability.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11, Lemma 11.4.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 15.13.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Lemma 15.13.
-/

public section

open Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped NNReal RealInnerProductSpace

namespace TauCeti

namespace CountablyRectifiable

section GlobalCone

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- On a set `s` whose secants lie in the strict cone `infDist (y - x) P ≤ α * dist y x` (`α < 1`)
around a subspace `P` with orthogonal projection, the restriction of `P.orthogonalProjectionOnto`
to `s` is antilipschitz. -/
private theorem antilipschitzWith_orthogonalProjectionOnto_of_forall_infDist_le
    (P : Submodule ℝ V) [P.HasOrthogonalProjection] {s : Set V} {α : ℝ} (hα : α < 1)
    (h : ∀ x ∈ s, ∀ y ∈ s, infDist (y - x) (P : Set V) ≤ α * dist y x) :
    AntilipschitzWith (Real.toNNReal (1 - max α 0))⁻¹
      (s.domRestrict P.orthogonalProjectionOnto) := by
  set β := max α 0
  have hβ1 : 0 < 1 - β := sub_pos.2 (max_lt hα zero_lt_one)
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have htri : dist (y : V) x ≤
      dist (P.orthogonalProjectionOnto y) (P.orthogonalProjectionOnto x) +
        infDist ((y : V) - x) (P : Set V) := by
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, ← Submodule.coe_sub, ← map_sub,
      ← P.starProjection_apply, ← P.dist_starProjection_eq_infDist, dist_eq_norm]
    simpa only [add_sub_cancel] using norm_add_le (P.starProjection ((y : V) - x))
      ((y : V) - x - P.starProjection ((y : V) - x))
  have hle : (1 - β) * dist (x : V) y ≤
      dist (s.domRestrict P.orthogonalProjectionOnto x)
        (s.domRestrict P.orthogonalProjectionOnto y) := by
    have hinf : infDist ((y : V) - x) (P : Set V) ≤ β * dist (y : V) x :=
      (h x.1 x.2 y.1 y.2).trans (mul_le_mul_of_nonneg_right (le_max_left α 0) dist_nonneg)
    rw [dist_comm (x : V), domRestrict_apply, domRestrict_apply,
      dist_comm (P.orthogonalProjectionOnto x)]
    linarith
  rw [NNReal.coe_inv, Real.coe_toNNReal _ hβ1.le, inv_mul_eq_div, le_div_iff₀ hβ1, mul_comm]
  exact hle

/-- **Global cone criterion for countable rectifiability.** If all secants of `s` lie in a strict
cone `infDist (y - x) P ≤ α * dist y x` (`α < 1`) around a finite-dimensional subspace `P`, then
`s` is countably `(dim P)`-rectifiable, without finite dimensionality or separability of the
ambient space. -/
theorem of_forall_infDist_le [MeasurableSpace V] [BorelSpace V] (P : Submodule ℝ V)
    [FiniteDimensional ℝ P] {s : Set V} {α : ℝ} (hα : α < 1)
    (h : ∀ x ∈ s, ∀ y ∈ s, infDist (y - x) (P : Set V) ≤ α * dist y x) :
    CountablyRectifiable (finrank ℝ P) s := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact .empty
  have := hs.to_subtype
  let f : s → P := s.domRestrict P.orthogonalProjectionOnto
  have hanti := antilipschitzWith_orthogonalProjectionOnto_of_forall_infDist_le P hα h
  have hinv : RightInvOn (invFun f) f (range f) := fun _ hy => invFun_eq hy
  have hlip : LipschitzOnWith (Real.toNNReal (1 - max α 0))⁻¹
      ((Subtype.val : s → V) ∘ invFun f) (range f) := by
    simpa only [one_mul] using (LipschitzWith.subtype_val s).comp_lipschitzOnWith
      (lipschitzOnWith_iff_restrict.2 (hanti.to_rightInvOn hinv))
  have himg : ((Subtype.val : s → V) ∘ invFun f) '' range f = s := by
    rw [← range_comp, comp_assoc, invFun_comp hanti.injective, comp_id, Subtype.range_coe]
  rw [← himg]
  exact (of_finiteDimensional (range f)).image hlip

end GlobalCone

section LocalCone

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Perturbing a subspace `P` to `Q` shifts `infDist (y - x) ·` by at most
`‖P.starProjection - Q.starProjection‖ * dist y x`. -/
private theorem infDist_sub_le_add_norm_starProjection_sub_mul (P Q : Submodule ℝ V)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] (x y : V) :
    infDist (y - x) (Q : Set V) ≤
      infDist (y - x) (P : Set V) + ‖P.starProjection - Q.starProjection‖ * dist y x := by
  rw [← Q.dist_starProjection_eq_infDist, ← P.dist_starProjection_eq_infDist,
    dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have hsplit : (y - x) - Q.starProjection (y - x) =
      ((y - x) - P.starProjection (y - x)) + (P.starProjection - Q.starProjection) (y - x) := by
    simp
  calc ‖(y - x) - Q.starProjection (y - x)‖
      ≤ ‖(y - x) - P.starProjection (y - x)‖ +
          ‖(P.starProjection - Q.starProjection) (y - x)‖ := hsplit ▸ norm_add_le _ _
    _ ≤ ‖(y - x) - P.starProjection (y - x)‖ +
          ‖P.starProjection - Q.starProjection‖ * ‖y - x‖ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _

/-- In a second-countable real inner product space containing at least one `k`-dimensional
subspace, the orthogonal projections onto `k`-dimensional subspaces admit a countable subfamily
dense in operator norm. -/
private theorem exists_countable_submodule_starProjection_approx [SecondCountableTopology V]
    {k : ℕ} (hk : ({u : Fin k → V | Orthonormal ℝ u}).Nonempty) :
    ∃ (Q : ℕ → Submodule ℝ V) (_ : ∀ j, FiniteDimensional ℝ (Q j)),
      (∀ j, finrank ℝ (Q j) = k) ∧
      ∀ (P : Submodule ℝ V) [FiniteDimensional ℝ P], finrank ℝ P = k →
        ∀ ε > (0 : ℝ), ∃ j, ‖P.starProjection - (Q j).starProjection‖ < ε := by
  let O : Set (Fin k → V) := {u | Orthonormal ℝ u}
  have := hk.to_subtype
  let u : ℕ → O := denseSeq O
  let Q : ℕ → Submodule ℝ V := fun j => Submodule.span ℝ (range (u j : Fin k → V))
  have hQfin (j : ℕ) : FiniteDimensional ℝ (Q j) :=
    FiniteDimensional.span_of_finite ℝ (finite_range _)
  have hQrk (j : ℕ) : finrank ℝ (Q j) = k :=
    (finrank_span_eq_card (u j).2.linearIndependent).trans (Fintype.card_fin k)
  let Φ : (Fin k → V) → (V →L[ℝ] V) :=
    fun w => ∑ i : Fin k, InnerProductSpace.rankOne ℝ (w i) (w i)
  have hΦ : Continuous Φ := by
    have hterm (i : Fin k) : Continuous fun w : Fin k → V =>
        InnerProductSpace.rankOne ℝ (w i) (w i) :=
      ((InnerProductSpace.rankOne ℝ).continuous.comp (continuous_apply i)).clm_apply
        (continuous_apply i)
    fun_prop
  have hQproj (j : ℕ) : (Q j).starProjection = Φ (u j) := by
    let v : Fin k → Q j := fun i => ⟨(u j : Fin k → V) i, Submodule.subset_span (mem_range_self i)⟩
    have hv : Orthonormal ℝ v := (Q j).subtypeₗᵢ.orthonormal_comp_iff.mp (u j).2
    have hsp : ⊤ ≤ Submodule.span ℝ (range v) := (Submodule.eq_top_of_finrank_eq
      ((finrank_span_eq_card hv.linearIndependent).trans
        ((Fintype.card_fin k).trans (hQrk j).symm))).ge
    let b : OrthonormalBasis (Fin k) ℝ (Q j) := OrthonormalBasis.mk hv hsp
    simpa only [Φ, b, v, OrthonormalBasis.coe_mk] using b.starProjection_eq_sum_rankOne
  refine ⟨Q, hQfin, hQrk, fun P _ hP ε hε => ?_⟩
  let b := (stdOrthonormalBasis ℝ P).reindex (finCongr hP)
  let w : O := ⟨fun i => (b i : V), P.subtypeₗᵢ.orthonormal_comp_iff.mpr b.orthonormal⟩
  have hPproj : P.starProjection = Φ w := b.starProjection_eq_sum_rankOne
  obtain ⟨δ, hδ, hδball⟩ := Metric.continuousAt_iff.1
    ((hΦ.comp continuous_subtype_val).continuousAt (x := w)) ε hε
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq O) w δ hδ
  refine ⟨j, ?_⟩
  rw [hPproj, hQproj j, ← dist_eq_norm, dist_comm]
  exact hδball (by simpa only [dist_comm] using hj)

/-- **Local cone criterion for countable rectifiability.** If at every `x ∈ s` there exist a
`k`-dimensional subspace `P`, an aperture `α < 1`, and a radius `r > 0` such that every `y ∈ s`
within `r` of `x` satisfies `infDist (y - x) P ≤ α * dist y x`, then `s` is countably
`k`-rectifiable. -/
theorem of_forall_exists_submodule_infDist_le [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {s : Set V}
    (h : ∀ x ∈ s, ∃ (P : Submodule ℝ V) (_ : FiniteDimensional ℝ P), finrank ℝ P = k ∧
      ∃ α < 1, ∃ r > 0, ∀ y ∈ s, dist y x < r → infDist (y - x) (P : Set V) ≤ α * dist y x) :
    CountablyRectifiable k s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact .empty
  have : Nonempty V := ⟨x₀⟩
  have hk : ({u : Fin k → V | Orthonormal ℝ u}).Nonempty := by
    obtain ⟨P₀, hP₀fin, hP₀k, -⟩ := h x₀ hx₀
    let b₀ := (stdOrthonormalBasis ℝ P₀).reindex (finCongr hP₀k)
    exact ⟨fun i => (b₀ i : V), P₀.subtypeₗᵢ.orthonormal_comp_iff.mpr b₀.orthonormal⟩
  obtain ⟨Q, hQfin, hQrk, hQapp⟩ := exists_countable_submodule_starProjection_approx hk
  let c : ℕ → V := denseSeq V
  let piece (p : ℕ × ℕ × ℕ) : Set V :=
    {x ∈ s | x ∈ ball (c p.2.2) (1 / (2 * ((p.2.1 : ℝ) + 1))) ∧
      ∀ y ∈ s, dist y x < 1 / ((p.2.1 : ℝ) + 1) →
        infDist (y - x) (Q p.1 : Set V) ≤ (1 - 1 / (2 * ((p.2.1 : ℝ) + 1))) * dist y x}
  have hrect (p : ℕ × ℕ × ℕ) : CountablyRectifiable k (piece p) := by
    rw [← hQrk p.1]
    refine of_forall_infDist_le (Q p.1) (α := 1 - 1 / (2 * ((p.2.1 : ℝ) + 1)))
      (sub_lt_self 1 (by positivity)) fun x hx y hy => hx.2.2 y hy.1 ?_
    calc dist y x ≤ dist y (c p.2.2) + dist x (c p.2.2) := dist_triangle_right y x (c p.2.2)
      _ < 1 / (2 * ((p.2.1 : ℝ) + 1)) + 1 / (2 * ((p.2.1 : ℝ) + 1)) := add_lt_add hy.2.1 hx.2.1
      _ = 1 / ((p.2.1 : ℝ) + 1) := by field_simp; ring
  refine (CountablyRectifiable.iUnion hrect).mono fun x hx => mem_iUnion.2 ?_
  obtain ⟨P, hPfin, hPk, α, hα, r, hr, hcone⟩ := h x hx
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((1 - α)⁻¹) r⁻¹)
  have hrm : 1 / ((m : ℝ) + 1) < r := by
    simpa using inv_lt_of_inv_lt₀ hr ((le_max_right _ _).trans_lt (hm.trans (lt_add_one _)))
  have hαm : α + 1 / (2 * ((m : ℝ) + 1)) ≤ 1 - 1 / (2 * ((m : ℝ) + 1)) := by
    have h1 : 1 / ((m : ℝ) + 1) < 1 - α := by
      simpa using inv_lt_of_inv_lt₀ (sub_pos.2 hα)
        ((le_max_left _ _).trans_lt (hm.trans (lt_add_one _)))
    have h2 : 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) = 1 / ((m : ℝ) + 1) := by
      field_simp; ring
    linarith
  obtain ⟨j, hj⟩ := @hQapp P hPfin hPk (1 / (2 * ((m : ℝ) + 1))) (by positivity)
  obtain ⟨l, hl⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq V) x
    (1 / (2 * ((m : ℝ) + 1))) (by positivity)
  refine ⟨(j, m, l), hx, by simpa [mem_ball, dist_comm] using hl, fun y hys hyx => ?_⟩
  calc infDist (y - x) (Q j : Set V)
      ≤ α * dist y x + 1 / (2 * ((m : ℝ) + 1)) * dist y x :=
        (infDist_sub_le_add_norm_starProjection_sub_mul P (Q j) x y).trans
          (add_le_add (hcone y hys (hyx.trans hrm))
            (mul_le_mul_of_nonneg_right hj.le dist_nonneg))
    _ ≤ (1 - 1 / (2 * ((m : ℝ) + 1))) * dist y x := by
        simpa only [← add_mul] using mul_le_mul_of_nonneg_right hαm dist_nonneg

/-- **Hyperplane normal-cone criterion for countable rectifiability.** In a finite-dimensional real
inner product space `V`, if at every `x ∈ s` there exist a unit vector `ν`, `α < 1`, and `r > 0`
such that `|⟪y - x, ν⟫| ≤ α * dist y x` whenever `y ∈ s` and `dist y x < r`, then `s` is countably
`(dim V - 1)`-rectifiable. -/
theorem of_forall_exists_inner_le [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {s : Set V}
    (h : ∀ x ∈ s, ∃ ν : V, ‖ν‖ = 1 ∧ ∃ α < 1, ∃ r > 0,
      ∀ y ∈ s, dist y x < r → |⟪y - x, ν⟫| ≤ α * dist y x) :
    CountablyRectifiable (finrank ℝ V - 1) s := by
  refine of_forall_exists_submodule_infDist_le fun x hx => ?_
  obtain ⟨ν, hν, α, hα, r, hr, hcone⟩ := h x hx
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν ▸ one_ne_zero)
  have : Nontrivial V := ⟨⟨ν, 0, hν0⟩⟩
  have : Fact (finrank ℝ V = finrank ℝ V - 1 + 1) := ⟨(Nat.sub_add_cancel finrank_pos).symm⟩
  refine ⟨(ℝ ∙ ν)ᗮ, inferInstance, Submodule.finrank_orthogonal_span_singleton hν0,
    α, hα, r, hr, fun y hy hyx => ?_⟩
  rw [← (ℝ ∙ ν).norm_starProjection_eq_infDist, Submodule.starProjection_unit_singleton ℝ hν,
    norm_smul, hν, mul_one, Real.norm_eq_abs, real_inner_comm]
  exact hcone y hy hyx

end LocalCone

end CountablyRectifiable

end TauCeti
