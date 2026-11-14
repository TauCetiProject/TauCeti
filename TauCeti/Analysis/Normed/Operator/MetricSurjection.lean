/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import TauCeti.Analysis.Normed.Group.BallSphere
import TauCeti.Analysis.Normed.Module.Quotient
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Metric surjections between seminormed spaces

A bounded linear operator `q : E →L[𝕜] F` between seminormed spaces is a **metric surjection**
(also called a metric quotient map) if `‖q‖ ≤ 1` and every `y : F` lifts for every `ε > 0` to
some `x : E` with `q x = y` and `‖x‖ < ‖y‖ + ε` (`ContinuousLinearMap.IsMetricSurjection`).

Metric surjections are characterized in two equivalent ways:
* geometrically, `q` maps every open ball centered at `0` onto the open ball of the same radius
  (`ContinuousLinearMap.isMetricSurjection_iff_image_ball`);
* metrically, `q` is contractive, surjective, and expresses the seminorm on `F` as the quotient
  infimum `‖y‖ = ⨅ x : {x // q x = y}, ‖x.1‖` (`ContinuousLinearMap.isMetricSurjection_iff_iInf`).

Canonical examples include identity maps, linear isometric equivalences, quotient projections
`S.mkQL : E →L[𝕜] E ⧸ S` by arbitrary submodules, and compositions of metric surjections.
Precomposition with any metric surjection preserves operator norms
(`IsMetricSurjection.opNorm_comp`, `IsMetricSurjection.opNNNorm_comp`).

## Main definitions and results

* `ContinuousLinearMap.IsMetricSurjection`: predicate that `q : E →L[𝕜] F` is a metric surjection.
* `ContinuousLinearMap.isMetricSurjection_iff_image_ball`: open-ball characterization
  `∀ r, q '' Metric.ball 0 r = Metric.ball 0 r`.
* `ContinuousLinearMap.isMetricSurjection_iff_iInf`: infimum characterization
  `‖q‖ ≤ 1 ∧ Function.Surjective q ∧ ∀ y, ‖y‖ = ⨅ x : {x // q x = y}, ‖x.1‖`.
* `Submodule.isMetricSurjection_mkQL`: every quotient projection `S.mkQL` is a metric surjection.
* `ContinuousLinearMap.IsMetricSurjection.opNorm_comp` and `opNNNorm_comp`: precomposition with a
  metric surjection preserves operator norms.

## References

* A. Pietsch, *Operator Ideals*, North-Holland (1980), §B.3.2 and §C.3.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.2.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

section Basic

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A bounded linear operator `q : E →L[𝕜] F` is a **metric surjection** if `‖q‖ ≤ 1` and every
target vector `y` lifts to vectors of norm arbitrarily close to `‖y‖`. -/
structure IsMetricSurjection (q : E →L[𝕜] F) : Prop where
  /-- A metric surjection has operator norm at most one. -/
  norm_le_one : ‖q‖ ≤ 1
  /-- Every vector `y` lifts to a preimage of norm strictly below `‖y‖ + ε` for each `ε > 0`. -/
  exists_apply_eq_norm_lt : ∀ y : F, ∀ {ε : ℝ}, 0 < ε → ∃ x : E, q x = y ∧ ‖x‖ < ‖y‖ + ε

/-- Unfold `ContinuousLinearMap.IsMetricSurjection` into contractivity and norm-lifting. -/
theorem isMetricSurjection_def {q : E →L[𝕜] F} :
    q.IsMetricSurjection ↔
      ‖q‖ ≤ 1 ∧ ∀ y : F, ∀ {ε : ℝ}, 0 < ε → ∃ x : E, q x = y ∧ ‖x‖ < ‖y‖ + ε :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- A metric surjection has nonnegative operator norm at most one. -/
theorem IsMetricSurjection.nnnorm_le_one {q : E →L[𝕜] F} (hq : q.IsMetricSurjection) :
    ‖q‖₊ ≤ 1 := by
  exact_mod_cast hq.norm_le_one

/-- A metric surjection does not increase norms. -/
theorem IsMetricSurjection.norm_apply_le {q : E →L[𝕜] F} (hq : q.IsMetricSurjection) (x : E) :
    ‖q x‖ ≤ ‖x‖ := by
  simpa using q.le_of_opNorm_le hq.norm_le_one x

/-- Every metric surjection is surjective. -/
theorem IsMetricSurjection.surjective {q : E →L[𝕜] F} (hq : q.IsMetricSurjection) :
    Function.Surjective q := fun y ↦ by
  obtain ⟨x, hx, -⟩ := hq.exists_apply_eq_norm_lt y zero_lt_one
  exact ⟨x, hx⟩

/-- Every open ball centered at `0` in the codomain is contained in the image of the open ball of
the same radius under a metric surjection. -/
theorem IsMetricSurjection.ball_subset_image_ball {q : E →L[𝕜] F} (hq : q.IsMetricSurjection)
    (r : ℝ) : Metric.ball (0 : F) r ⊆ q '' Metric.ball 0 r := fun y hy ↦ by
  have hy' : ‖y‖ < r := mem_ball_zero_iff.mp hy
  obtain ⟨x, hx, hlt⟩ := hq.exists_apply_eq_norm_lt y (sub_pos.mpr hy')
  exact ⟨x, mem_ball_zero_iff.mpr (hlt.trans_eq (add_sub_cancel ‖y‖ r)), hx⟩

/-- A metric surjection maps each open ball centered at `0` onto the open ball of the same
radius. -/
theorem IsMetricSurjection.image_ball {q : E →L[𝕜] F} (hq : q.IsMetricSurjection) (r : ℝ) :
    q '' Metric.ball 0 r = Metric.ball 0 r :=
  q.image_ball_eq_ball hq.norm_le_one hq.ball_subset_image_ball r

/-- Construct a metric surjection from contractivity and open-ball lifting. -/
theorem IsMetricSurjection.of_ball_subset_image_ball {q : E →L[𝕜] F} (h₁ : ‖q‖ ≤ 1)
    (h₂ : ∀ r : ℝ, Metric.ball (0 : F) r ⊆ q '' Metric.ball 0 r) :
    q.IsMetricSurjection :=
  ⟨h₁, fun y _ hε ↦ TauCeti.exists_apply_eq_norm_lt_add h₂ y hε⟩

/-- **Open-ball characterization.** A bounded linear operator is a metric surjection if and only if
it maps each open ball centered at `0` onto the open ball of the same radius. -/
theorem isMetricSurjection_iff_image_ball {q : E →L[𝕜] F} :
    q.IsMetricSurjection ↔ ∀ r : ℝ, q '' Metric.ball 0 r = Metric.ball 0 r := by
  refine ⟨fun hq ↦ hq.image_ball, fun h ↦ .of_ball_subset_image_ball ?_ fun r ↦ (h r).ge⟩
  refine q.opNorm_le_bound zero_le_one fun x ↦ ?_
  rw [one_mul]
  refine le_of_forall_pos_lt_add fun ε hε ↦ mem_ball_zero_iff.mp ?_
  rw [← h (‖x‖ + ε)]
  exact ⟨x, mem_ball_zero_iff.mpr (lt_add_of_pos_right ‖x‖ hε), rfl⟩

/-- A metric surjection expresses the seminorm of every `y` as the infimum of the seminorms of its
preimages. -/
theorem IsMetricSurjection.norm_eq_iInf {q : E →L[𝕜] F} (hq : q.IsMetricSurjection) (y : F) :
    ‖y‖ = ⨅ x : {x : E // q x = y}, ‖x.1‖ := by
  have : Nonempty {x : E // q x = y} := nonempty_subtype.mpr (hq.surjective y)
  have hbdd : BddBelow (Set.range fun x : {x : E // q x = y} ↦ ‖x.1‖) :=
    ⟨0, Set.forall_mem_range.mpr fun x ↦ norm_nonneg x.1⟩
  refine le_antisymm (le_ciInf fun x ↦ by simpa [x.2] using hq.norm_apply_le x.1) ?_
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨x, hx, hlt⟩ := hq.exists_apply_eq_norm_lt y hε
  exact (ciInf_le hbdd ⟨x, hx⟩).trans_lt hlt

/-- **Quotient-norm characterization.** A bounded linear operator is a metric surjection if and
only if it has norm at most one, is surjective, and expresses every target seminorm as the infimum
over preimages. -/
theorem isMetricSurjection_iff_iInf {q : E →L[𝕜] F} :
    q.IsMetricSurjection ↔
      ‖q‖ ≤ 1 ∧ Function.Surjective q ∧ ∀ y : F, ‖y‖ = ⨅ x : {x : E // q x = y}, ‖x.1‖ := by
  refine ⟨fun hq ↦ ⟨hq.norm_le_one, hq.surjective, hq.norm_eq_iInf⟩, ?_⟩
  rintro ⟨h₁, hsurj, hiInf⟩
  refine ⟨h₁, fun y ε hε ↦ ?_⟩
  have : Nonempty {x : E // q x = y} := nonempty_subtype.mpr (hsurj y)
  have hlt : (⨅ x : {x : E // q x = y}, ‖x.1‖) < ‖y‖ + ε := by
    rw [← hiInf y]
    exact lt_add_of_pos_right ‖y‖ hε
  obtain ⟨⟨x, hx⟩, hxlt⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨x, hx, hxlt⟩

end Basic

section Examples

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The identity operator on any seminormed space is a metric surjection. -/
@[simp]
theorem IsMetricSurjection.id : (ContinuousLinearMap.id 𝕜 E).IsMetricSurjection :=
  ⟨norm_id_le, fun y _ hε ↦ ⟨y, rfl, lt_add_of_pos_right ‖y‖ hε⟩⟩

/-- Linear isometric equivalences are metric surjections. -/
theorem _root_.LinearIsometryEquiv.isMetricSurjection [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃ₗᵢ[𝕜] F) : (e : E →L[𝕜] F).IsMetricSurjection :=
  ⟨e.toLinearIsometry.norm_toContinuousLinearMap_le, fun y _ hε ↦
    ⟨e.symm y, e.apply_symm_apply y,
      by simpa only [e.symm.norm_map] using lt_add_of_pos_right ‖y‖ hε⟩⟩

/-- The quotient projection by any submodule of a seminormed space is a metric surjection. -/
@[simp]
theorem _root_.Submodule.isMetricSurjection_mkQL (S : Submodule 𝕜 E) :
    S.mkQL.IsMetricSurjection :=
  .of_ball_subset_image_ball S.norm_mkQL_le S.ball_subset_image_mkQL_ball

end Examples

section Composition

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Metric surjections are closed under composition. -/
theorem IsMetricSurjection.comp {q₂ : F →L[𝕜] G} {q₁ : E →L[𝕜] F}
    (hq₂ : q₂.IsMetricSurjection) (hq₁ : q₁.IsMetricSurjection) :
    (q₂ ∘L q₁).IsMetricSurjection where
  norm_le_one := ((q₂.opNorm_comp_le q₁).trans
    (mul_le_of_le_one_right (norm_nonneg q₂) hq₁.norm_le_one)).trans hq₂.norm_le_one
  exists_apply_eq_norm_lt z {ε} hε := by
    obtain ⟨y, rfl, hy⟩ := hq₂.exists_apply_eq_norm_lt z (half_pos hε)
    obtain ⟨x, rfl, hx⟩ := hq₁.exists_apply_eq_norm_lt y (half_pos hε)
    exact ⟨x, rfl, by linarith⟩

/-- If `q` lifts every vector `y` to preimages of norm arbitrarily close to `‖y‖`, then
precomposition with `q` cannot decrease operator norms. -/
theorem le_opNorm_comp_of_forall_exists_lt {q : E →L[𝕜] F}
    (hq : ∀ y : F, ∀ {ε : ℝ}, 0 < ε → ∃ x : E, q x = y ∧ ‖x‖ < ‖y‖ + ε)
    (T : F →L[𝕜] G) : ‖T‖ ≤ ‖T ∘L q‖ := by
  refine T.opNorm_le_bound (norm_nonneg (T ∘L q)) fun y ↦ le_of_forall_pos_lt_add fun δ hδ ↦ ?_
  obtain ⟨x, hx, hlt⟩ := hq y (div_pos hδ (add_pos_of_nonneg_of_pos (norm_nonneg (T ∘L q)) one_pos))
  calc ‖T y‖ = ‖(T ∘L q) x‖ := by rw [comp_apply, hx]
    _ ≤ ‖T ∘L q‖ * ‖x‖ := (T ∘L q).le_opNorm x
    _ ≤ ‖T ∘L q‖ * (‖y‖ + δ / (‖T ∘L q‖ + 1)) := by gcongr
    _ = ‖T ∘L q‖ * ‖y‖ + ‖T ∘L q‖ * (δ / (‖T ∘L q‖ + 1)) := mul_add ..
    _ < ‖T ∘L q‖ * ‖y‖ + δ := by
      gcongr
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      linarith

/-- Precomposition with a metric surjection preserves the operator norm. -/
theorem IsMetricSurjection.opNorm_comp {q : E →L[𝕜] F} (hq : q.IsMetricSurjection)
    (T : F →L[𝕜] G) : ‖T ∘L q‖ = ‖T‖ :=
  le_antisymm ((T.opNorm_comp_le q).trans (mul_le_of_le_one_right (norm_nonneg T) hq.norm_le_one))
    (le_opNorm_comp_of_forall_exists_lt hq.exists_apply_eq_norm_lt T)

/-- Precomposition with a metric surjection preserves the nonnegative operator norm. -/
theorem IsMetricSurjection.opNNNorm_comp {q : E →L[𝕜] F} (hq : q.IsMetricSurjection)
    (T : F →L[𝕜] G) : ‖T ∘L q‖₊ = ‖T‖₊ :=
  NNReal.eq (hq.opNorm_comp T)

end Composition

section NormEqOne

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Nontrivial F]

/-- A metric surjection onto a nontrivial normed space has operator norm one. -/
theorem IsMetricSurjection.norm_eq_one {q : E →L[𝕜] F} (hq : q.IsMetricSurjection) :
    ‖q‖ = 1 := by
  simpa using hq.opNorm_comp (ContinuousLinearMap.id 𝕜 F)

/-- A metric surjection onto a nontrivial normed space has nonnegative operator norm one. -/
theorem IsMetricSurjection.nnnorm_eq_one {q : E →L[𝕜] F} (hq : q.IsMetricSurjection) :
    ‖q‖₊ = 1 :=
  NNReal.eq hq.norm_eq_one

end NormEqOne

end ContinuousLinearMap
