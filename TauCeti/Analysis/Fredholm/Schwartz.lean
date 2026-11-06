/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Fredholm.ClosedRange
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Compact perturbations of surjections

The functional-analytic Schwartz lemma used in the finite-dimensionality proof for cohomology
on compact Riemann surfaces: a compact perturbation of a surjective map between Banach spaces
has closed range of finite codimension. The kernel of the surjection need not be finite
or complemented.

The first step makes a compact operator arbitrarily small after quotienting its target by a
finite-dimensional subspace. It uses total boundedness of the image of the unit ball, without
assuming the approximation property or a finite-rank operator-norm approximation.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
-/

public noncomputable section

open ContinuousLinearMap Metric Set
open scoped NNReal Topology

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A compact operator becomes arbitrarily small after quotienting its target by a
finite-dimensional subspace. No finite-rank approximation hypothesis is required. -/
theorem exists_finiteDimensional_quotient_norm_le (K : E →L[𝕜] F)
    (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Submodule 𝕜 F, FiniteDimensional 𝕜 W ∧ ‖W.mkQL.comp K‖ ≤ ε := by
  classical
  obtain ⟨s, -, hs, hcover⟩ :=
    (hK.isCompact_closure_image_closedBall (f := K.toLinearMap) 1).finite_cover_balls hε
  let W : Submodule 𝕜 F := Submodule.span 𝕜 s
  refine ⟨W, FiniteDimensional.span_of_finite 𝕜 hs, ?_⟩
  apply opNorm_le_of_unit_norm hε.le
  intro x hx
  have hxin : K x ∈ closure (K '' closedBall 0 1) :=
    subset_closure ⟨x, by simpa [mem_closedBall, dist_zero_right] using hx.le, rfl⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hxin)
  have hyW : y ∈ W := Submodule.subset_span hy
  have hqy : (Submodule.Quotient.mk y : F ⧸ W) = 0 := by simpa using hyW
  calc
    ‖(W.mkQL.comp K) x‖ = ‖W.mkQL (K x - y)‖ := by simp [hqy]
    _ ≤ ‖K x - y‖ := Submodule.Quotient.norm_mk_le W _
    _ ≤ ε := (by simpa [mem_ball, dist_eq_norm] using hxy : ‖K x - y‖ < ε).le

/-- A perturbation smaller than the reciprocal bound of a nonlinear right inverse stays onto.
No complement to the kernel is needed. -/
theorem surjective_of_norm_sub_lt_inv_rightInverse [CompleteSpace E]
    (T S : E →L[𝕜] F) (R : T.NonlinearRightInverse)
    (h : ‖S - T‖ < (R.nnnorm : ℝ)⁻¹) : Function.Surjective S := by
  have ha : ApproximatesLinearOn (S : E → F) T univ ‖S - T‖₊ := by
    intro x _ y _
    have he : S x - S y - T (x - y) = (S - T) (x - y) := by
      simp only [map_sub, sub_apply]
      abel
    rw [he]
    exact (S - T).le_opNorm _
  have hnn : ‖S - T‖₊ < R.nnnorm⁻¹ := by exact_mod_cast h
  have hopen : IsOpen (Set.range S) := by
    simpa only [image_univ] using ha.open_image R isOpen_univ (Or.inr hnn)
  apply LinearMap.range_eq_top.1
  apply Submodule.eq_top_of_nonempty_interior'
  change (interior (Set.range S)).Nonempty
  rw [hopen.interior_eq]
  exact ⟨0, 0, map_zero S⟩

/-- The quotient norm gives a right inverse of bound `2` for a closed-subspace quotient. -/
private def quotientRightInverse (W : Submodule 𝕜 F) [IsClosed (W : Set F)] :
    W.mkQL.NonlinearRightInverse := by
  classical
  have h (z : F ⧸ W) : ∃ x : F, W.mkQL x = z ∧ ‖x‖ ≤ 2 * ‖z‖ := by
    by_cases hz : z = 0
    · exact ⟨0, by simp [hz]⟩
    · obtain ⟨x, hx, hxn⟩ := Submodule.Quotient.norm_mk_lt z (norm_pos_iff.2 hz)
      exact ⟨x, hx, by linarith⟩
  choose lift hlift using h
  exact ⟨lift, 2, fun z ↦ (hlift z).2, fun z ↦ (hlift z).1⟩

/-- Compose a bounded right inverse with the uniformly bounded quotient lift. -/
private def quotientCompRightInverse (T : E →L[𝕜] F) (R : T.NonlinearRightInverse)
    (W : Submodule 𝕜 F) [IsClosed (W : Set F)] :
    (W.mkQL.comp T).NonlinearRightInverse where
  toFun z := R (quotientRightInverse W z)
  nnnorm := R.nnnorm * 2
  bound' z := by
    calc
      ‖R (quotientRightInverse W z)‖ ≤ R.nnnorm * ‖quotientRightInverse W z‖ := R.bound _
      _ ≤ R.nnnorm * (2 * ‖z‖) := mul_le_mul_of_nonneg_left
        ((quotientRightInverse W).bound z) R.nnnorm.coe_nonneg
      _ = (R.nnnorm * 2 : ℝ≥0) * ‖z‖ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  right_inv' z := by
    change W.mkQL (T (R (quotientRightInverse W z))) = z
    rw [R.right_inv, (quotientRightInverse W).right_inv]

/-- **Schwartz's lemma.** A compact perturbation of a surjection between real or complex
Banach spaces has finite-dimensional cokernel, without any hypothesis on its kernel. -/
theorem cofg_range_add_of_surjective_of_isCompactOperator [CompleteSpace E] [CompleteSpace F]
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    (T + K).range.CoFG := by
  let R := T.nonlinearRightInverseOfSurjective (LinearMap.range_eq_top.2 hT)
  have hR : 0 < (R.nnnorm : ℝ) := by
    exact_mod_cast T.nonlinearRightInverseOfSurjective_nnnorm_pos
      (LinearMap.range_eq_top.2 hT)
  let a : ℝ := ((R.nnnorm : ℝ) * 2)⁻¹
  have ha : 0 < a := inv_pos.2 (mul_pos hR (by norm_num))
  obtain ⟨W, hW, hsmall⟩ := exists_finiteDimensional_quotient_norm_le K hK (half_pos ha)
  have : FiniteDimensional 𝕜 W := hW
  have : IsClosed (W : Set F) := W.closed_of_finiteDimensional
  let A := W.mkQL.comp T
  let B := W.mkQL.comp (T + K)
  let Q : A.NonlinearRightInverse := quotientCompRightInverse T R W
  have hd : B - A = W.mkQL.comp K := by
    ext x
    simp [A, B]
  have hp : ‖B - A‖ < (Q.nnnorm : ℝ)⁻¹ := by
    rw [hd]
    simpa only [Q, quotientCompRightInverse, NNReal.coe_mul, NNReal.coe_ofNat, a] using
      hsmall.trans_lt (half_lt_self ha)
  have hs : Function.Surjective B := surjective_of_norm_sub_lt_inv_rightInverse A B Q hp
  have hm : Submodule.map W.mkQ (T + K).range = ⊤ := by
    have hr : LinearMap.range (B : E →ₗ[𝕜] F ⧸ W) = ⊤ := LinearMap.range_eq_top.2 hs
    simpa only [B, toLinearMap_comp, Submodule.toLinearMap_mkQL, LinearMap.range_comp] using hr
  have hsup : W ⊔ (T + K).range = ⊤ := (Submodule.map_mkQ_eq_top _ _).1 hm
  have hm' : Submodule.map (T + K).range.mkQ W = ⊤ :=
    (Submodule.map_mkQ_eq_top _ _).2 (by simpa only [sup_comm] using hsup)
  let L : W →ₗ[𝕜] F ⧸ (T + K).range := (T + K).range.mkQ.comp W.subtype
  have hL : Function.Surjective L := by
    apply LinearMap.range_eq_top.1
    change LinearMap.range ((T + K).range.mkQ.comp W.subtype) = ⊤
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact hm'
  exact Module.Finite.of_surjective L hL

/-- A compact perturbation of a surjection between real or complex Banach spaces has closed
range. The finite-dimensional cokernel, rather than a kernel complement, supplies closedness. -/
theorem isClosed_range_add_of_surjective_of_isCompactOperator [CompleteSpace E] [CompleteSpace F]
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    IsClosed ((T + K).range : Set F) := by
  have := cofg_range_add_of_surjective_of_isCompactOperator T K hT hK
  exact (T + K).isClosed_range_of_finite_coker

end TauCeti
