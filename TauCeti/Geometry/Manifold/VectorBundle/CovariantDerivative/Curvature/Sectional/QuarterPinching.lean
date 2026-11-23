/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.QuarterPinching
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.FourTensor
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Pointwise quarter-pinched sectional curvature and the PIC2 cone on Riemannian manifolds

`IsQuarterPinchedAt` and `IsPointwiseQuarterPinched` express pointwise strict quarter pinching of
sectional curvature. For a metric-compatible torsion-free connection, strict quarter pinching places
`hcov.algebraicCurvature cov ht x` in `interior {q | IsPIC2FourFrame q.1}` (geometric
`interior PIC2` when `4 ≤ finrank ℝ E`, vacuous otherwise); on compact `M`, this upgrades to
uniform pinching, a uniform `pic2Expression` margin, and a compact convex `O(n)`-invariant subset
of `interior PIC2`.

## Main definitions & statements

* `IsQuarterPinchedAt`, `IsPointwiseQuarterPinched`, `IsQuarterPinchedAt.sectionalMin_pos`,
  `IsQuarterPinchedAt.sectionalMax_lt_four_mul_sectionalMin`,
  `IsQuarterPinchedAt.mem_interior_isPIC2FourFrame`,
  `IsPointwiseQuarterPinched.exists_pos_and_lt_four_sectionalCurvature`,
  `IsPointwiseQuarterPinched.exists_pos_le_pic2Expression`,
  `IsPointwiseQuarterPinched.exists_isCompact_convex_subset_interior`.

## References

* S. Brendle and R. Schoen, J. Amer. Math. Soc. 22 (2009), 287–307.
-/

public section

open Bundle Set TauCeti TauCeti.FourTensor
open scoped ContDiff InnerProductSpace Manifold Matrix

noncomputable section

namespace CovariantDerivative

section QuarterPinching

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

section Pointwise

variable (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)

/-- Strict quarter pinching at `x`: every tangent two-plane has positive sectional curvature
strictly less than four times every other tangent two-plane at `x`. -/
def IsQuarterPinchedAt (x : M) : Prop :=
  ∀ u v u' v' : TangentSpace I x, LinearIndependent ℝ ![u, v] →
    LinearIndependent ℝ ![u', v'] → 0 < cov.sectionalCurvature hcov x u v ∧
      cov.sectionalCurvature hcov x u v < 4 * cov.sectionalCurvature hcov x u' v'

/-- Pointwise unfolding of `IsQuarterPinchedAt`. -/
theorem isQuarterPinchedAt_iff (x : M) :
    cov.IsQuarterPinchedAt hcov x ↔
      ∀ u v u' v' : TangentSpace I x, LinearIndependent ℝ ![u, v] →
        LinearIndependent ℝ ![u', v'] → 0 < cov.sectionalCurvature hcov x u v ∧
          cov.sectionalCurvature hcov x u v < 4 * cov.sectionalCurvature hcov x u' v' := Iff.rfl

/-- Strict sectional curvature bounds `0 < a`, `b < 4 * a` at `x` imply `IsQuarterPinchedAt`. -/
theorem isQuarterPinchedAt_of_sectionalCurvature_mem_Icc (x : M) {a b : ℝ} (ha : 0 < a)
    (hab : b < 4 * a)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov x u v ∈ Icc a b) : cov.IsQuarterPinchedAt hcov x :=
  fun u v u' v' huv huv' ↦ ⟨ha.trans_le (hsec u v huv).1,
    (hsec u v huv).2.trans_lt (hab.trans_le (by linarith [(hsec u' v' huv').1]))⟩

/-- Pointwise strict quarter pinching on `M`. -/
def IsPointwiseQuarterPinched : Prop := ∀ x : M, cov.IsQuarterPinchedAt hcov x

/-- Pointwise characterization of `IsPointwiseQuarterPinched`. -/
theorem isPointwiseQuarterPinched_iff :
    cov.IsPointwiseQuarterPinched hcov ↔ ∀ x : M, cov.IsQuarterPinchedAt hcov x := Iff.rfl

end Pointwise

variable {cov}

/-- Weak quarter pinching at `x` implies `IsPIC2FourFrame (cov.curvatureFourTensor x)`. -/
theorem IsMetricCompatible.isPIC2FourFrame_curvatureFourTensor_of_sectionalCurvature_mem_Icc
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) {a b : ℝ} (ha : 0 ≤ a) (hab : b ≤ 4 * a)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov x u v ∈ Icc a b) : IsPIC2FourFrame (cov.curvatureFourTensor x) :=
  (hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x).isPIC2FourFrame_of_weak_quarterPinching
    ha hab fun u v huv ↦ by
      rw [← cov.sectionalCurvature_eq_curvatureFourTensor_of_orthonormal hcov x huv]
      exact mem_Icc.1 (hsec u v huv.linearIndependent)

variable {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}

/-- Specialize `IsPointwiseQuarterPinched` to a point `x : M`. -/
theorem IsPointwiseQuarterPinched.isQuarterPinchedAt (h : cov.IsPointwiseQuarterPinched hcov)
    (x : M) : cov.IsQuarterPinchedAt hcov x := h x

/-- In dimension `≥ 2`, `IsQuarterPinchedAt` implies `0 < sectionalMin`. -/
theorem IsQuarterPinchedAt.sectionalMin_pos {x : M} (hp : cov.IsQuarterPinchedAt hcov x)
    (hn : 2 ≤ Module.finrank ℝ E) : 0 < sectionalMin (cov.curvatureFourTensor x) :=
  sectionalMin_pos_of_quarterPinched (by simpa using hn) (cov.curvatureFourTensor x) fun u v huv ↦
    by simpa only [← cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x] using
      (hp u v u v huv huv).1

/-- In dimension `≥ 2`, `IsQuarterPinchedAt` implies `sectionalMax < 4 * sectionalMin`. -/
theorem IsQuarterPinchedAt.sectionalMax_lt_four_mul_sectionalMin {x : M}
    (hp : cov.IsQuarterPinchedAt hcov x) (hn : 2 ≤ Module.finrank ℝ E) :
    sectionalMax (cov.curvatureFourTensor x) < 4 * sectionalMin (cov.curvatureFourTensor x) :=
  sectionalMax_lt_four_mul_sectionalMin_of_quarterPinched (by simpa using hn)
    (cov.curvatureFourTensor x) fun u v u' v' huv huv' ↦ by
      simpa only [← cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x] using
        (hp u v u' v' huv huv').2

/-- Strict quarter pinching at `x` places `hcov.algebraicCurvature cov ht x` in `interior PIC2`. -/
theorem IsQuarterPinchedAt.mem_interior_isPIC2FourFrame {x : M}
    (hp : cov.IsQuarterPinchedAt hcov x) (ht : cov.torsion = 0) :
    hcov.algebraicCurvature cov ht x ∈ interior {q | IsPIC2FourFrame q.val} :=
  mem_interior_isPIC2FourFrame_of_quarterPinched (hcov.algebraicCurvature cov ht x)
    fun u v u' v' huv huv' ↦ by
      simpa only [IsMetricCompatible.coe_algebraicCurvature,
        ← cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x] using hp u v u' v' huv huv'

section Compact

variable [CompactSpace M]

/-- On a compact manifold of dimension `≥ 2`, pointwise strict quarter pinching yields a uniform
lower bound `a > 0` and uniform pinching factor `θ < 4`. -/
theorem IsPointwiseQuarterPinched.exists_pos_and_lt_four_sectionalCurvature
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0)
    (hn : 2 ≤ Module.finrank ℝ E) :
    ∃ a > 0, ∃ θ < (4 : ℝ), ∀ (x : M) (u v u' v' : TangentSpace I x),
      LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
        a ≤ cov.sectionalCurvature hcov x u v ∧
          cov.sectionalCurvature hcov x u v ≤ θ * cov.sectionalCurvature hcov x u' v' := by
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨1, one_pos, 1, by norm_num, fun x ↦ hE.elim x⟩
  · let smin (x : M) := sectionalMin (cov.curvatureFourTensor x)
    let smax (x : M) := sectionalMax (cov.curvatureFourTensor x)
    have hpos (x : M) : 0 < smin x := (hp x).sectionalMin_pos hn
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      cov.continuous_sectionalMin_curvatureFourTensor.continuousOn
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      (cov.continuous_sectionalMax_curvatureFourTensor.div
        cov.continuous_sectionalMin_curvatureFourTensor fun x ↦ (hpos x).ne').continuousOn
    refine ⟨smin x₀, hpos x₀, smax x₁ / smin x₁,
      (div_lt_iff₀ (hpos x₁)).2 ((hp x₁).sectionalMax_lt_four_mul_sectionalMin hn),
      fun x u v u' v' huv huv' ↦ ?_⟩
    have hr := hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x
    have hmin_le {w z : TangentSpace I x} (hwz : LinearIndependent ℝ ![w, z]) :
        smin x ≤ cov.sectionalCurvature hcov x w z := by
      rw [cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x]
      exact (le_div_iff₀ (Matrix.posDef_gram_of_linearIndependent hwz).det_pos).2
        (hr.sectionalMin_mul_det_gram_le_and_le_sectionalMax w z).1
    have hle_max : cov.sectionalCurvature hcov x u v ≤ smax x := by
      rw [cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x]
      exact (div_le_iff₀ (Matrix.posDef_gram_of_linearIndependent huv).det_pos).2
        (hr.sectionalMin_mul_det_gram_le_and_le_sectionalMax u v).2
    have hθ : 0 ≤ smax x₁ / smin x₁ := div_nonneg
      ((hpos x₁).le.trans (sectionalMin_le_sectionalMax _)) (hpos x₁).le
    refine ⟨(isMinOn_iff.1 hx₀ x (mem_univ x)).trans (hmin_le huv), hle_max.trans ?_⟩
    calc smax x = (smax x / smin x) * smin x := (div_mul_cancel₀ _ (hpos x).ne').symm
      _ ≤ (smax x₁ / smin x₁) * smin x :=
          mul_le_mul_of_nonneg_right (isMaxOn_iff.1 hx₁ x (mem_univ x)) (hpos x).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmin_le huv') hθ

/-- On a compact manifold, pointwise strict quarter pinching yields a uniform positive margin
`ε > 0` below `pic2Expression`. -/
theorem IsPointwiseQuarterPinched.exists_pos_le_pic2Expression
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0) :
    ∃ ε > 0, ∀ (x : M) (f : Fin 4 → TangentSpace I x), Orthonormal ℝ f →
      ∀ l ∈ Icc (-1 : ℝ) 1, ∀ m ∈ Icc (-1 : ℝ) 1,
        ε ≤ pic2Expression (cov.curvatureFourTensor x) f l m := by
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨1, one_pos, fun x ↦ hE.elim x⟩
  · by_cases hn4 : 4 ≤ Module.finrank ℝ E
    · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
        cov.continuous_pic2Min_curvatureFourTensor.continuousOn
      have hpos : 0 < pic2Min (cov.curvatureFourTensor x₀) := by
        simpa only [IsMetricCompatible.coe_algebraicCurvature] using
          (mem_interior_isPIC2FourFrame_iff_pic2Min_pos (by simpa using hn4)).1
            ((hp x₀).mem_interior_isPIC2FourFrame ht)
      exact ⟨pic2Min (cov.curvatureFourTensor x₀), hpos, fun x _ hf _ hl _ hm ↦
        (isMinOn_iff.1 hx₀ x (mem_univ x)).trans (pic2Min_le_pic2Expression _ hf hl hm)⟩
    · refine ⟨1, one_pos, fun x f hf ↦ ?_⟩
      have := hf.linearIndependent.fintype_card_le_finrank
      rw [Fintype.card_fin, TauCeti.finrank_tangentSpace] at this; omega

/-- On a compact pointwise strictly quarter-pinched manifold, all isometric pullbacks of curvature
tensors to `EuclideanSpace ℝ (Fin n)` lie in a compact convex `O(n)`-invariant subset of
`interior {q | IsPIC2FourFrame q.1}`. -/
theorem IsPointwiseQuarterPinched.exists_isCompact_convex_subset_interior
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0) :
    let V₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    ∃ K : Set (algebraicCurvatureSubmodule V₀),
      IsCompact K ∧ Convex ℝ K ∧
      (∀ (e : V₀ ≃ₗᵢ[ℝ] V₀) (q : algebraicCurvatureSubmodule V₀),
        q ∈ K → algebraicCurvatureLinearIsometryEquiv e q ∈ K) ∧
      K ⊆ interior {q | IsPIC2FourFrame q.val} ∧
      ∀ (x : M) (e : V₀ ≃ₗᵢ[ℝ] TangentSpace I x),
        algebraicCurvatureLinearIsometryEquiv e (hcov.algebraicCurvature cov ht x) ∈ K := by
  intro V₀
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨∅, isCompact_empty, convex_empty, fun _ _ h ↦ h.elim, empty_subset _,
      fun x ↦ hE.elim x⟩
  · obtain ⟨ε, hε, hpic⟩ := hp.exists_pos_le_pic2Expression ht
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      cov.continuous_norm_curvatureFourTensor.continuousOn
    set R := ‖cov.curvatureFourTensor x₁‖
    let B : Set (algebraicCurvatureSubmodule V₀) :=
      Subtype.val ⁻¹' Metric.closedBall (0 : FourTensor V₀) R
    have hB_conv : Convex ℝ B := fun _ h₁ _ h₂ _ _ ha hb hab ↦ by
      simpa only [B, mem_preimage, Submodule.coe_add, Submodule.coe_smul_of_tower] using
        (convex_closedBall (0 : FourTensor V₀) R) h₁ h₂ ha hb hab
    let P : Set (algebraicCurvatureSubmodule V₀) :=
      Subtype.val ⁻¹' {r : FourTensor V₀ | ∀ f : Fin 4 → V₀, Orthonormal ℝ f →
        ∀ l ∈ Icc (-1 : ℝ) 1, ∀ m ∈ Icc (-1 : ℝ) 1, ε ≤ pic2Expression r f l m}
    have hP_conv : Convex ℝ P := fun _ h₁ _ h₂ _ _ ha hb hab ↦ by
      simpa only [P, mem_preimage, Submodule.coe_add, Submodule.coe_smul_of_tower] using
        (convex_setOf_le_pic2Expression ε) h₁ h₂ ha hb hab
    refine ⟨B ∩ P,
      (isClosed_algebraicCurvatureSubmodule.isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_closedBall (0 : FourTensor V₀) R)).inter_right
        ((isClosed_setOf_le_pic2Expression ε).preimage continuous_subtypeVal),
      hB_conv.inter hP_conv,
      fun e q ⟨hqB, hqP⟩ ↦ ⟨by
          simpa [B, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv] using hqB,
        fun f hf l hl m hm ↦ by
          simpa using hqP (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf) l hl m hm⟩,
      fun q ⟨_, hqP⟩ ↦ mem_interior_isPIC2FourFrame_of_exists_pos_le hε hqP,
      fun x e ↦ ⟨by
          simpa [B, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv] using
            isMaxOn_iff.1 hx₁ x (mem_univ x),
        fun f hf l hl m hm ↦ by
          simpa using hpic x (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf) l hl m hm⟩⟩

end Compact

end QuarterPinching

end CovariantDerivative
