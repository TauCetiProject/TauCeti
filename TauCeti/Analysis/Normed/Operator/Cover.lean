/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import TauCeti.Analysis.Normed.Group.Cover

/-!
# Covering estimates for bounded linear operators

Given a bounded operator `T` whose unit-ball image `T(B_E)` is covered at radius `ε` by a set of
centres `C`, there are two dual ways to turn the metric cover into an operator-norm bound:

* **Quotienting the target by the span of the centres.** Over any nontrivially normed fields linked
  by an isometric ring homomorphism `σ : 𝕜 →+* 𝕜₂`, every centre `y ∈ C` maps to `0` in
  `F ⧸ Submodule.span 𝕜₂ C`, so `(Submodule.span 𝕜₂ C).mkQL.comp T` has norm at most `ε` on `B_E`
  and hence operator norm at most `ε * ‖c‖₊` for every scalar `c : 𝕜` with `1 < ‖c‖` via shell
  rescaling (`ContinuousLinearMap.nnnorm_mkQL_span_comp_le_mul_of_isCover`). This is the geometric
  core shared by `ContinuousLinearMap.exists_finiteDimensional_quotient_norm_le` and the covering
  upper bound for Kolmogorov numbers.
* **Restricting the domain to the joint kernel of norming functionals.** Over an `RCLike` scalar
  field, when `C` is finite, choosing Hahn–Banach norming functionals `φ_y` for the centres `y ∈ C`
  and intersecting `ker (φ_y ∘ T)` produces a closed submodule `K ≤ E` of codimension at most
  `C.ncard` on which `‖T ∘L K.subtypeL‖₊ ≤ 2 * ε`
  (`ContinuousLinearMap.exists_rank_quotient_le_nnnorm_comp_subtypeL_le_of_isCover`). For `x ∈ K`
  on the unit sphere and a centre `y ∈ C` within `ε` of `T x`, `φ_y (T x) = 0` gives
  `‖y‖ = ‖φ_y (y - T x)‖ ≤ ‖T x - y‖ ≤ ε` and hence `‖T x‖ ≤ 2 * ε`. This is the geometric core
  shared by `IsCompactOperator.exists_finiteDimensional_quotient_norm_comp_subtype_le` and the
  covering upper bound for Gelfand numbers.

## Main declarations

* `ContinuousLinearMap.nnnorm_mkQL_span_comp_le_mul_of_isCover`: quotienting the target by
  `Submodule.span 𝕜₂ C` for an `ε`-cover `C` of `T(B_E)` bounds the operator norm by `ε * ‖c‖₊`
  whenever `1 < ‖c‖`.
* `ContinuousLinearMap.exists_rank_quotient_le_nnnorm_comp_subtypeL_le_of_isCover`: over `RCLike`,
  a finite `ε`-cover `C` of `T(B_E)` yields a closed submodule `K ≤ E` with
  `Module.rank 𝕜 (E ⧸ K) ≤ C.ncard` and `‖T ∘L K.subtypeL‖₊ ≤ 2 * ε`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §§2.4–2.5.
* B. Carl, I. Stephani, *Entropy, Compactness and the Approximation of Operators*, Cambridge Tracts
  in Mathematics 98, Cambridge University Press (1990), Chapters 1–2.
* J. B. Conway, *A Course in Functional Analysis*, Graduate Texts in Mathematics 96, Springer
  (1990), Chapter VI.
-/

public section

open Metric Set
open scoped NNReal

namespace ContinuousLinearMap

section NontriviallyNormedField

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- If `C` is an `ε`-cover of the image `T(B_E)` of the closed unit ball, then quotienting the
target by `Submodule.span 𝕜₂ C` bounds the operator norm of `(Submodule.span 𝕜₂ C).mkQL.comp T` by
`ε * ‖c‖₊` for every scalar `c : 𝕜` with `1 < ‖c‖`. -/
theorem nnnorm_mkQL_span_comp_le_mul_of_isCover {T : E →SL[σ] F} {ε : ℝ≥0}
    {C : Set F} (hcover : Metric.IsCover ε (T '' Metric.closedBall 0 1) C) {c : 𝕜}
    (hc : 1 < ‖c‖) :
    ‖(Submodule.span 𝕜₂ C).mkQL.comp T‖₊ ≤ ε * ‖c‖₊ := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have _ : 0 < ‖c‖ := one_pos.trans hc
  refine opNorm_le_of_shell one_pos (by positivity) hc fun x hx₁ hx₂ ↦ ?_
  obtain ⟨y, hyC, hxy⟩ :=
    hcover.exists_norm_sub_le ⟨x, mem_closedBall_zero_iff.mpr hx₂.le, rfl⟩
  have hy0 : (Submodule.Quotient.mk y : F ⧸ Submodule.span 𝕜₂ C) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span hyC)
  calc ‖((Submodule.span 𝕜₂ C).mkQL.comp T) x‖
      = ‖(Submodule.span 𝕜₂ C).mkQL (T x - y)‖ := by simp [hy0]
    _ ≤ ‖T x - y‖ := Submodule.Quotient.norm_mk_le _ _
    _ ≤ ε := hxy
    _ = ((ε : ℝ) * ‖c‖) * (1 / ‖c‖) := by field_simp
    _ ≤ ((ε : ℝ) * ‖c‖) * ‖x‖ := by gcongr

end NontriviallyNormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over an `RCLike` scalar field, if `C` is a finite `ε`-cover of the image `T(B_E)` of the closed
unit ball, intersecting the kernels `ker (φ_y ∘ T)` of Hahn–Banach norming functionals `φ_y` for
`y ∈ C` yields a closed submodule `K ≤ E` of codimension at most `C.ncard` on which
`‖T ∘L K.subtypeL‖₊ ≤ 2 * ε`. -/
theorem exists_rank_quotient_le_nnnorm_comp_subtypeL_le_of_isCover {T : E →L[𝕜] F} {ε : ℝ≥0}
    {C : Set F} (hC : C.Finite) (hcover : Metric.IsCover ε (T '' Metric.closedBall 0 1) C) :
    ∃ K : Submodule 𝕜 E, IsClosed (K : Set E) ∧ Module.rank 𝕜 (E ⧸ K) ≤ C.ncard ∧
      ‖T ∘L K.subtypeL‖₊ ≤ 2 * ε := by
  let : Fintype C := hC.fintype
  choose φ hφ hφ_apply using fun y : C ↦ exists_dual_vector'' 𝕜 (y : F)
  let A : E →L[𝕜] (C → 𝕜) := ContinuousLinearMap.pi fun y ↦ (φ y).comp T
  have hrank : Module.rank 𝕜 (E ⧸ A.ker) ≤ C.ncard := by
    have h1 := A.toLinearMap.quotKerEquivRange.lift_rank_eq
    have h2 : Module.rank 𝕜 (LinearMap.range A.toLinearMap) ≤ C.ncard := by
      refine (Submodule.rank_le _).trans ?_
      rw [rank_fun', Nat.cast_le]
      exact (Nat.card_eq_fintype_card.symm.trans (Nat.card_coe_set_eq C)).le
    exact Cardinal.lift_le_nat_iff.mp (h1.trans_le (Cardinal.lift_le_nat_iff.mpr h2))
  refine ⟨A.ker, A.isClosed_ker, hrank, ?_⟩
  rw [← NNReal.coe_le_coe]
  push_cast
  refine opNorm_le_of_unit_norm (by positivity) fun x hx ↦ ?_
  have hTx : T x ∈ T '' Metric.closedBall 0 1 :=
    ⟨x, mem_closedBall_zero_iff.mpr (by simpa using hx.le), rfl⟩
  obtain ⟨y, hyC, hdist⟩ := hcover.exists_norm_sub_le hTx
  let j : C := ⟨y, hyC⟩
  have hzero : φ j (T x) = 0 := congrFun (A.mem_ker.mp x.2) j
  have hy_le : ‖y‖ ≤ ‖T x - y‖ := by
    calc ‖y‖ = ‖φ j (y - T x)‖ := by rw [map_sub, hzero, sub_zero, hφ_apply]; simp [j]
      _ ≤ ‖φ j‖ * ‖y - T x‖ := (φ j).le_opNorm _
      _ ≤ ‖y - T x‖ := mul_le_of_le_one_left (norm_nonneg _) (hφ j)
      _ = ‖T x - y‖ := norm_sub_rev _ _
  calc ‖(T ∘L A.ker.subtypeL) x‖ = ‖T x‖ := rfl
    _ ≤ ‖T x - y‖ + ‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (T x - y) y
    _ ≤ 2 * (ε : ℝ) := by linarith

end RCLike

end ContinuousLinearMap
