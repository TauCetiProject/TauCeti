/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.InfDist
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import TauCeti.Geometry.MeasureTheory.Rectifiable.Subspace

/-!
# Geometric cone criteria for countable rectifiability

In a second-countable real inner product space `V`, a subset `s` is countably `k`-rectifiable
whenever, at every point `x ∈ s`, `s` lies locally inside a strict cone
`infDist (y - x) P ≤ α * dist y x` (`α < 1`) around some `k`-dimensional subspace `P`
(`TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_le`). For the converse
approximate tangent-cone containment almost everywhere on bi-Lipschitz patches, see
`TauCeti.Geometry.MeasureTheory.Rectifiable.TangentCone`.

When a single finite-dimensional subspace `P` and aperture `α < 1` serve globally on `s`, `s` is
countably `(dim P)`-rectifiable without any finite-dimensionality or separability hypothesis on `V`
(`TauCeti.CountablyRectifiable.of_forall_infDist_le`). In a finite-dimensional real inner product
space `V`, specializing the local criterion to hyperplanes `(ℝ ∙ ν)ᗮ` orthogonal to unit vectors `ν`
yields the codimension-one normal-cone criterion
(`TauCeti.CountablyRectifiable.of_forall_exists_inner_le`), which supplies the rectifiability step
in De Giorgi's structure theorem for the reduced boundary.

## Main results

* `TauCeti.CountablyRectifiable.of_forall_infDist_le`: global cone containment around a
  finite-dimensional subspace `P` implies countable `(dim P)`-rectifiability, without separability
  or finite dimensionality of `V`.
* `TauCeti.CountablyRectifiable.of_forall_exists_submodule_infDist_le`: in a second-countable real
  inner product space `V`, local cone containment around `k`-dimensional subspaces at every point of
  `s` implies countable `k`-rectifiability.
* `TauCeti.CountablyRectifiable.of_forall_exists_inner_le`: in a finite-dimensional real inner
  product space `V`, local containment away from unit normal directions `ν` implies countable
  `(dim V - 1)`-rectifiability.

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
  have hanti := P.antilipschitzWith_orthogonalProjectionOnto_of_forall_infDist_le hα h
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

/-- **Local cone criterion for countable rectifiability.** If at every `x ∈ s` there exist a
`k`-dimensional subspace `P`, an aperture `α < 1`, and a radius `r > 0` such that every `y ∈ s`
within `r` of `x` satisfies `infDist (y - x) P ≤ α * dist y x`, then `s` is countably
`k`-rectifiable. -/
theorem of_forall_exists_submodule_infDist_le [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {s : Set V}
    (h : ∀ x ∈ s, ∃ (P : Submodule ℝ V) (_ : FiniteDimensional ℝ P), finrank ℝ P = k ∧
      ∃ α < 1, ∃ r > 0, ∀ y ∈ s, dist y x < r → infDist (y - x) (P : Set V) ≤ α * dist y x) :
    CountablyRectifiable k s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, _⟩
  · exact .empty
  have : Nonempty V := ⟨x₀⟩
  obtain ⟨S, hSfin, hSc, hSrk, hSapp⟩ :=
    exists_countable_finrank_eq_and_norm_starProjection_sub_lt ℝ V k
  have : Countable S := hSc.to_subtype
  let c : ℕ → V := denseSeq V
  let piece (p : S × ℕ × ℕ) : Set V :=
    {x ∈ s | x ∈ ball (c p.2.2) (1 / (2 * ((p.2.1 : ℝ) + 1))) ∧
      ∀ y ∈ s, dist y x < 1 / ((p.2.1 : ℝ) + 1) →
        infDist (y - x) (p.1.1 : Set V) ≤ (1 - 1 / (2 * ((p.2.1 : ℝ) + 1))) * dist y x}
  have hrect (p : S × ℕ × ℕ) : CountablyRectifiable k (piece p) := by
    rw [← hSrk p.1]
    refine of_forall_infDist_le p.1.1 (α := 1 - 1 / (2 * ((p.2.1 : ℝ) + 1)))
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
  obtain ⟨Q, hQ⟩ := @hSapp P hPfin hPk (1 / (2 * ((m : ℝ) + 1))) (by positivity)
  obtain ⟨l, hl⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq V) x
    (1 / (2 * ((m : ℝ) + 1))) (by positivity)
  refine ⟨(Q, m, l), hx, by simpa [mem_ball, dist_comm] using hl, fun y hys hyx => ?_⟩
  have hpert : infDist (y - x) (Q.1 : Set V) ≤
      infDist (y - x) (P : Set V) + ‖P.starProjection - Q.1.starProjection‖ * dist y x := by
    simpa only [dist_eq_norm] using P.infDist_le_infDist_add_norm_starProjection_sub_mul Q.1 (y - x)
  calc infDist (y - x) (Q.1 : Set V)
      ≤ α * dist y x + 1 / (2 * ((m : ℝ) + 1)) * dist y x :=
        hpert.trans (add_le_add (hcone y hys (hyx.trans hrm))
          (mul_le_mul_of_nonneg_right hQ.le dist_nonneg))
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
