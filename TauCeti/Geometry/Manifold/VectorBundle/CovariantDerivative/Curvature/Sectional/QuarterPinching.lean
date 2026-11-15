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

A metric-compatible connection on a Riemannian manifold is strictly quarter-pinched at `x`
(`CovariantDerivative.IsQuarterPinchedAt`) when every tangent two-plane at `x` has positive
sectional curvature strictly less than four times that of every other tangent two-plane at `x`, and
pointwise strictly quarter-pinched (`CovariantDerivative.IsPointwiseQuarterPinched`) when this holds
at every point of `M`.

In dimension at least two (`2 ≤ Module.finrank ℝ E`), `IsQuarterPinchedAt` yields
`0 < sectionalMin (cov.curvatureFourTensor x)` and
`sectionalMax (cov.curvatureFourTensor x) < 4 * sectionalMin (cov.curvatureFourTensor x)`. For a
metric-compatible torsion-free connection in any dimension, `IsQuarterPinchedAt` places
`hcov.algebraicCurvature cov ht x` in `interior {q | IsPIC2FourFrame q.1}` (which coincides with the
interior of the `PIC2` cone when `4 ≤ Module.finrank ℝ E`, and equals the full submodule vacuously
when `Module.finrank ℝ E < 4` because no orthonormal four-frame exists).

On a compact manifold `M`, continuity of `‖curvatureFourTensor ·‖`, `sectionalMin`, `sectionalMax`,
and `pic2Min` upgrades `IsPointwiseQuarterPinched` to:
* a uniform positive sectional lower bound `a > 0` and uniform pinching factor `θ < 4` when
  `2 ≤ Module.finrank ℝ E`,
* a uniform margin `ε > 0` below `pic2Expression` across all points and orthonormal four-frames, and
* a compact convex `O(n)`-invariant subset of `interior {q | IsPIC2FourFrame q.1}` on the Euclidean
  model space containing all isometric frame pullbacks of the manifold's curvature tensors.

## Main definitions

* `CovariantDerivative.IsQuarterPinchedAt`, `CovariantDerivative.IsPointwiseQuarterPinched`.

## Main statements

* `CovariantDerivative.IsQuarterPinchedAt.sectionalMin_pos`,
  `CovariantDerivative.IsQuarterPinchedAt.sectionalMax_lt_four_mul_sectionalMin`, and
  `CovariantDerivative.IsQuarterPinchedAt.mem_interior_isPIC2FourFrame`.
* `CovariantDerivative.IsPointwiseQuarterPinched.exists_pos_and_lt_four_sectionalCurvature`,
  `CovariantDerivative.IsPointwiseQuarterPinched.exists_pos_le_pic2Expression`, and
  `CovariantDerivative.IsPointwiseQuarterPinched.exists_isCompact_convex_subset_interior`.

## References

* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307.
* S. Brendle, *Ricci Flow and the Sphere Theorem*, GSM 111, AMS (2010).
-/

public section

open Bundle Set
open scoped ContDiff InnerProductSpace Manifold Matrix

noncomputable section

namespace CovariantDerivative

section QuarterPinching

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

/-- A metric-compatible connection is strictly quarter-pinched at `x` if every tangent two-plane at
`x` has positive sectional curvature strictly less than four times that of every other tangent
two-plane at `x`. -/
def IsQuarterPinchedAt
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) : Prop :=
  ∀ u v u' v' : TangentSpace I x, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
    0 < cov.sectionalCurvature hcov x u v ∧
      cov.sectionalCurvature hcov x u v < 4 * cov.sectionalCurvature hcov x u' v'

/-- Pointwise unfolding of `IsQuarterPinchedAt`. -/
theorem isQuarterPinchedAt_iff
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) : cov.IsQuarterPinchedAt hcov x ↔
      ∀ u v u' v' : TangentSpace I x,
        LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
          0 < cov.sectionalCurvature hcov x u v ∧
            cov.sectionalCurvature hcov x u v < 4 * cov.sectionalCurvature hcov x u' v' := Iff.rfl

/-- Strict sectional curvature bounds `0 < a`, `b < 4 * a` at `x` imply `IsQuarterPinchedAt`. -/
theorem isQuarterPinchedAt_of_sectionalCurvature_mem_Icc
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) {a b : ℝ} (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov x u v ∈ Icc a b) :
    cov.IsQuarterPinchedAt hcov x := fun u v u' v' huv huv' ↦
  ⟨ha.trans_le (hsec u v huv).1,
    (hsec u v huv).2.trans_lt (hab.trans_le (by linarith [(hsec u' v' huv').1]))⟩

/-- A connection is pointwise strictly quarter-pinched when `IsQuarterPinchedAt` holds at every
point of `M`. -/
def IsPointwiseQuarterPinched
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov) :
    Prop :=
  ∀ x : M, cov.IsQuarterPinchedAt hcov x

/-- Pointwise characterization of `IsPointwiseQuarterPinched`. -/
theorem isPointwiseQuarterPinched_iff
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov) :
    cov.IsPointwiseQuarterPinched hcov ↔ ∀ x : M, cov.IsQuarterPinchedAt hcov x := Iff.rfl

variable {cov} in
/-- Specialize `IsPointwiseQuarterPinched` to a point `x : M`. -/
theorem IsPointwiseQuarterPinched.isQuarterPinchedAt
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (h : cov.IsPointwiseQuarterPinched hcov) (x : M) : cov.IsQuarterPinchedAt hcov x := h x

variable {cov} in
/-- Weak quarter pinching at `x` implies `IsPIC2FourFrame (cov.curvatureFourTensor x)` (which is the
`PIC2` condition when `4 ≤ Module.finrank ℝ E` and holds vacuously below dimension four). -/
theorem IsMetricCompatible.isPIC2FourFrame_curvatureFourTensor_of_sectionalCurvature_mem_Icc
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) {a b : ℝ} (ha : 0 ≤ a) (hab : b ≤ 4 * a)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov x u v ∈ Icc a b) :
    TauCeti.FourTensor.IsPIC2FourFrame (cov.curvatureFourTensor x) :=
  (hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x).isPIC2FourFrame_of_weak_quarterPinching
    ha hab fun u v huv ↦ by
      rw [← cov.sectionalCurvature_eq_curvatureFourTensor_of_orthonormal hcov x huv]
      exact mem_Icc.1 (hsec u v huv.linearIndependent)

variable {cov} in
/-- In dimension at least two, strict quarter pinching at `x` implies
`0 < sectionalMin (cov.curvatureFourTensor x)`. -/
theorem IsQuarterPinchedAt.sectionalMin_pos
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    {x : M} (hp : cov.IsQuarterPinchedAt hcov x) (hn : 2 ≤ Module.finrank ℝ E) :
    0 < TauCeti.FourTensor.sectionalMin (cov.curvatureFourTensor x) :=
  TauCeti.FourTensor.sectionalMin_pos_of_quarterPinched (by simpa using hn)
    (cov.curvatureFourTensor x) fun u v huv ↦ by
      simpa only [← cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x] using
        (hp u v u v huv huv).1

variable {cov} in
/-- In dimension at least two, strict quarter pinching at `x` implies
`sectionalMax (cov.curvatureFourTensor x) < 4 * sectionalMin (cov.curvatureFourTensor x)`. -/
theorem IsQuarterPinchedAt.sectionalMax_lt_four_mul_sectionalMin
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    {x : M} (hp : cov.IsQuarterPinchedAt hcov x) (hn : 2 ≤ Module.finrank ℝ E) :
    TauCeti.FourTensor.sectionalMax (cov.curvatureFourTensor x) <
      4 * TauCeti.FourTensor.sectionalMin (cov.curvatureFourTensor x) :=
  TauCeti.FourTensor.sectionalMax_lt_four_mul_sectionalMin_of_quarterPinched (by simpa using hn)
    (cov.curvatureFourTensor x) fun u v u' v' huv huv' ↦ by
      simpa only [← cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x] using
        (hp u v u' v' huv huv').2

variable {cov} in
/-- Strict quarter pinching at `x` for a metric-compatible torsion-free connection places
`hcov.algebraicCurvature cov ht x` in `interior {q | IsPIC2FourFrame q.1}` (which coincides with the
interior of the `PIC2` cone when `4 ≤ Module.finrank ℝ E`, and equals the full submodule vacuously
when `Module.finrank ℝ E < 4`). -/
theorem IsQuarterPinchedAt.mem_interior_isPIC2FourFrame
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    {x : M} (hp : cov.IsQuarterPinchedAt hcov x) (ht : cov.torsion = 0) :
    hcov.algebraicCurvature cov ht x ∈
      interior {q | TauCeti.FourTensor.IsPIC2FourFrame q.1} :=
  TauCeti.FourTensor.mem_interior_isPIC2FourFrame_of_quarterPinched
    (hcov.algebraicCurvature cov ht x) fun u v u' v' huv huv' ↦ by
      simpa only [IsMetricCompatible.coe_algebraicCurvature,
        ← cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x] using hp u v u' v' huv huv'

section Compact

variable {cov} [CompactSpace M]

/-- On a compact manifold of dimension at least two, pointwise strict quarter pinching yields a
uniform positive sectional lower bound `a > 0` and a uniform pinching factor `θ < 4`. -/
theorem IsPointwiseQuarterPinched.exists_pos_and_lt_four_sectionalCurvature
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0)
    (hn : 2 ≤ Module.finrank ℝ E) :
    ∃ a > 0, ∃ θ < (4 : ℝ), ∀ (x : M) (u v u' v' : TangentSpace I x),
      LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
        a ≤ cov.sectionalCurvature hcov x u v ∧
          cov.sectionalCurvature hcov x u v ≤ θ * cov.sectionalCurvature hcov x u' v' := by
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨1, one_pos, 1, by norm_num, fun x ↦ hE.elim x⟩
  · let smin (x : M) := TauCeti.FourTensor.sectionalMin (cov.curvatureFourTensor x)
    let smax (x : M) := TauCeti.FourTensor.sectionalMax (cov.curvatureFourTensor x)
    have hpos (x : M) : 0 < smin x := (hp x).sectionalMin_pos hn
    have hlt (x : M) : smax x / smin x < 4 :=
      (div_lt_iff₀ (hpos x)).2 ((hp x).sectionalMax_lt_four_mul_sectionalMin hn)
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      cov.continuous_sectionalMin_curvatureFourTensor.continuousOn
    have hcont_div : Continuous fun x : M ↦ smax x / smin x :=
      cov.continuous_sectionalMax_curvatureFourTensor.div
        cov.continuous_sectionalMin_curvatureFourTensor fun x ↦ (hpos x).ne'
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont_div.continuousOn
    refine ⟨smin x₀, hpos x₀, smax x₁ / smin x₁, hlt x₁, fun x u v u' v' huv huv' ↦ ?_⟩
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
    have hθ_ge : 0 ≤ smax x₁ / smin x₁ := div_nonneg
      ((hpos x₁).le.trans (TauCeti.FourTensor.sectionalMin_le_sectionalMax (by simpa using hn) _))
      (hpos x₁).le
    refine ⟨(isMinOn_iff.1 hx₀ x (mem_univ x)).trans (hmin_le huv), hle_max.trans ?_⟩
    calc smax x = (smax x / smin x) * smin x := (div_mul_cancel₀ _ (hpos x).ne').symm
      _ ≤ (smax x₁ / smin x₁) * smin x :=
          mul_le_mul_of_nonneg_right (isMaxOn_iff.1 hx₁ x (mem_univ x)) (hpos x).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmin_le huv') hθ_ge

/-- On a compact manifold, pointwise strict quarter pinching yields a uniform positive margin
`ε > 0` below `pic2Expression` across all points and orthonormal four-frames (when
`Module.finrank ℝ E < 4`, no orthonormal four-frame exists so any `ε > 0` works vacuously). -/
theorem IsPointwiseQuarterPinched.exists_pos_le_pic2Expression
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0) :
    ∃ ε > 0, ∀ (x : M) (f : Fin 4 → TangentSpace I x), Orthonormal ℝ f →
      ∀ l ∈ Icc (-1 : ℝ) 1, ∀ m ∈ Icc (-1 : ℝ) 1,
        ε ≤ TauCeti.FourTensor.pic2Expression (cov.curvatureFourTensor x) f l m := by
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨1, one_pos, fun x ↦ hE.elim x⟩
  · by_cases hn4 : 4 ≤ Module.finrank ℝ E
    · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
        cov.continuous_pic2Min_curvatureFourTensor.continuousOn
      have hpos : 0 < TauCeti.FourTensor.pic2Min (cov.curvatureFourTensor x₀) := by
        simpa only [IsMetricCompatible.coe_algebraicCurvature] using
          (TauCeti.FourTensor.mem_interior_isPIC2FourFrame_iff_pic2Min_pos (by simpa using hn4)).1
            ((hp x₀).mem_interior_isPIC2FourFrame ht)
      exact ⟨TauCeti.FourTensor.pic2Min (cov.curvatureFourTensor x₀), hpos,
        fun x _ hf _ hl _ hm ↦ (isMinOn_iff.1 hx₀ x (mem_univ x)).trans
          (TauCeti.FourTensor.pic2Min_le_pic2Expression _ hf hl hm)⟩
    · refine ⟨1, one_pos, fun x f hf ↦ ?_⟩
      have hcard := hf.linearIndependent.fintype_card_le_finrank
      rw [Fintype.card_fin, TauCeti.finrank_tangentSpace] at hcard; omega

/-- On a compact pointwise strictly quarter-pinched manifold, all isometric pullbacks of the
manifold's curvature tensors to the Euclidean model space lie inside a single compact convex
`O(n)`-invariant subset of `interior {q | IsPIC2FourFrame q.1}` (which coincides with the interior
of the `PIC2` cone when `4 ≤ Module.finrank ℝ E`, and equals the full submodule vacuously when
`Module.finrank ℝ E < 4`). -/
theorem IsPointwiseQuarterPinched.exists_isCompact_convex_subset_interior
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0) :
    let V₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    ∃ K : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V₀),
      IsCompact K ∧ Convex ℝ K ∧
      (∀ (e : V₀ ≃ₗᵢ[ℝ] V₀) (q : TauCeti.FourTensor.algebraicCurvatureSubmodule V₀),
        q ∈ K → TauCeti.FourTensor.algebraicCurvatureLinearIsometryEquiv e q ∈ K) ∧
      K ⊆ interior {q | TauCeti.FourTensor.IsPIC2FourFrame q.1} ∧
      ∀ (x : M) (e : V₀ ≃ₗᵢ[ℝ] TangentSpace I x),
        TauCeti.FourTensor.algebraicCurvatureLinearIsometryEquiv e
          (hcov.algebraicCurvature cov ht x) ∈ K := by
  intro V₀
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨∅, isCompact_empty, convex_empty, fun _ _ h ↦ h.elim, empty_subset _,
      fun x ↦ hE.elim x⟩
  · -- Take `K = B ∩ P`, intersecting the closed operator-norm ball `B` of radius
    -- `R = max_M ‖curvatureFourTensor‖` (compact in finite dimension) with the closed convex
    -- `ε`-superlevel `PIC2` set `P` supplied by `exists_pos_le_pic2Expression`.
    obtain ⟨ε, hε, hpic⟩ := hp.exists_pos_le_pic2Expression ht
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      cov.continuous_norm_curvatureFourTensor.continuousOn
    set R := ‖cov.curvatureFourTensor x₁‖
    let B : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V₀) :=
      Subtype.val ⁻¹' Metric.closedBall (0 : TauCeti.FourTensor V₀) R
    have hB_cpt : IsCompact B :=
      TauCeti.FourTensor.isClosed_algebraicCurvatureSubmodule.isClosedEmbedding_subtypeVal
        |>.isCompact_preimage (isCompact_closedBall (0 : TauCeti.FourTensor V₀) R)
    have hB_conv : Convex ℝ B := fun q₁ h₁ q₂ h₂ a b ha hb hab ↦ by
      simpa only [B, mem_preimage, Submodule.coe_add, Submodule.coe_smul_of_tower] using
        (convex_closedBall (0 : TauCeti.FourTensor V₀) R) h₁ h₂ ha hb hab
    let P : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V₀) :=
      Subtype.val ⁻¹' {r : TauCeti.FourTensor V₀ | ∀ f : Fin 4 → V₀, Orthonormal ℝ f →
        ∀ l ∈ Icc (-1 : ℝ) 1, ∀ m ∈ Icc (-1 : ℝ) 1,
          ε ≤ TauCeti.FourTensor.pic2Expression r f l m}
    have hP_closed : IsClosed P :=
      (TauCeti.FourTensor.isClosed_setOf_le_pic2Expression ε).preimage continuous_subtype_val
    have hP_conv : Convex ℝ P := fun q₁ h₁ q₂ h₂ a b ha hb hab ↦ by
      simpa only [P, mem_preimage, Submodule.coe_add, Submodule.coe_smul_of_tower] using
        (TauCeti.FourTensor.convex_setOf_le_pic2Expression ε) h₁ h₂ ha hb hab
    -- Both `B` and `P` are `O(V₀)`-invariant, `P` sits inside `interior PIC2` by the `ε` margin,
    -- and every frame pullback of `hcov.algebraicCurvature cov ht x` lies in `B ∩ P`.
    refine ⟨B ∩ P, hB_cpt.inter_right hP_closed, hB_conv.inter hP_conv,
      fun e q ⟨hqB, hqP⟩ ↦ ⟨?_, ?_⟩,
      fun q ⟨_, hqP⟩ ↦ TauCeti.FourTensor.mem_interior_isPIC2FourFrame_of_exists_pos_le hε hqP,
      fun x e ↦ ⟨?_, ?_⟩⟩
    · simp only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right,
        TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv] at hqB ⊢
      exact hqB
    · intro f hf l hl m hm
      rw [TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        TauCeti.FourTensor.pic2Expression_compContinuousLinearMap]
      exact hqP (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf) l hl m hm
    · simp only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right,
        TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        IsMetricCompatible.coe_algebraicCurvature,
        ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
      exact isMaxOn_iff.1 hx₁ x (mem_univ x)
    · intro f hf l hl m hm
      rw [TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        IsMetricCompatible.coe_algebraicCurvature,
        TauCeti.FourTensor.pic2Expression_compContinuousLinearMap]
      exact hpic x (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf) l hl m hm

end Compact

end QuarterPinching

end CovariantDerivative
