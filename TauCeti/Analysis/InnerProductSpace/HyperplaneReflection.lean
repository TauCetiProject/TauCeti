/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.InnerProductSpace.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import TauCeti.Data.Set.Function
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Reflection in an affine hyperplane

For a vector `ν` and a real number `c`, `TauCeti.hyperplaneReflection ν c` is the affine isometry

`x ↦ x - (2 (⟪x, ν⟫ - c) / ‖ν‖²) ν`

of a real inner product space, the reflection in the hyperplane `{x | ⟪x, ν⟫ = c}` when `ν ≠ 0`
(for `ν = 0` it is the identity). Its linear part is the reflection `(ℝ ∙ ν)ᗮ.reflection` in the
parallel hyperplane through the origin, so its derivative at every point is this linear
reflection. It is an involution, fixes the hyperplane pointwise and exchanges the two open
half-spaces `{x | c < ⟪x, ν⟫}` and `{x | ⟪x, ν⟫ < c}`, since `⟪ρ x, ν⟫ = 2c - ⟪x, ν⟫`.

This is the reflection used to extend functions defined on one side of a flat boundary to the
other side, by odd or even reflection. It is Mathlib's `EuclideanGeometry.reflection` in the
affine hyperplane `{x | ⟪x, ν⟫ = c}`, written out for the parametrisation of half-spaces by a
normal vector and an offset.

## Main declarations

* `TauCeti.hyperplaneReflection`: the reflection in the hyperplane `{x | ⟪x, ν⟫ = c}`.
* `TauCeti.hyperplaneReflection_apply`: the explicit formula.
* `TauCeti.hyperplaneReflection_hyperplaneReflection`: it is an involution.
* `TauCeti.inner_hyperplaneReflection`: it reverses the signed height `⟪x, ν⟫ - c`.
* `TauCeti.hyperplaneReflection_eq_self_iff`: its fixed points are the points of the hyperplane.
* `TauCeti.mapsTo_hyperplaneReflection_ball`: it maps every ball centred on the hyperplane into
  itself.
* `TauCeti.hyperplaneReflection_mem_ball_iff` and
  `TauCeti.hyperplaneReflection_mem_closedBall_iff`: open and closed balls centred on the
  hyperplane are invariant.
* `TauCeti.closure_setOf_lt_inner_subset`: the closure of the open half-space `{x | c < ⟪x, ν⟫}`
  lies in the closed half-space `{x | c ≤ ⟪x, ν⟫}`, and
  (`TauCeti.closure_thickening_inter_setOf_lt_inner_subset`) the closure of the part of an open
  `R`-thickening in it lies in the part of the closed `R`-thickening in the closed half-space.
* `TauCeti.mem_closure_setOf_lt_inner_inter`: conversely, a point of the closed half-space in an
  open set `V` lies in the closure of the part of `V` in the open half-space.
* `TauCeti.hyperplaneReflection_eq_self_of_mem_closure`: it fixes the points of the closure of the
  open half-space `{x | c < ⟪x, ν⟫}` outside it.
* `TauCeti.dist_le_dist_hyperplaneReflection`: a point of the closed half-space
  `{y | c ≤ ⟪y, ν⟫}` is at least as close to another such point as to its mirror image, and so
  (`TauCeti.mem_thickening_of_hyperplaneReflection_mem_thickening`) a point of that half-space
  whose mirror image lies in a thickening of a set in the half-space lies in it too.
* `TauCeti.lipschitzWith_one_ite_hyperplaneReflection`: folding across the hyperplane, the map
  that fixes the closed half-space `{y | c ≤ ⟪y, ν⟫}` and reflects the other side onto it, is
  `1`-Lipschitz. It lands in that half-space (`TauCeti.le_inner_ite_hyperplaneReflection`) and maps
  every ball centred on the hyperplane into itself
  (`TauCeti.mapsTo_ite_hyperplaneReflection_ball`).
* `TauCeti.exists_opens_mapsTo_hyperplaneReflection`: a bounded reflection-invariant open set
  around a thickening of a bounded set of the closed half-space, whose points in the open
  half-space lie in that thickening.
* `TauCeti.fderiv_hyperplaneReflection` and `TauCeti.abs_det_fderiv_hyperplaneReflection`: its
  derivative is the linear reflection, of determinant `±1`.
* `TauCeti.measurePreserving_hyperplaneReflection`: it preserves every additive Haar measure, and
  its restriction to every measurable set it maps into itself
  (`TauCeti.measurePreserving_restrict_hyperplaneReflection`).
* `TauCeti.aestronglyMeasurable_piecewise_comp_hyperplaneReflection`: a field equal to `f` above
  the hyperplane and to `G ∘ f ∘ ρ` below it is measurable when `f` is measurable above it.
* `TauCeti.memLp_indicator_sub_indicator_comp_hyperplaneReflection` and
  `TauCeti.eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le`: the function
  `x ↦ 1_H f x - 1_H g (ρ x)` built from two functions `f`, `g` given on one side `H` of the
  hyperplane lies in `Lᵖ` with norm at most `‖f‖_p + ‖g‖_p`. For `g = f` this is the odd
  reflection of `f`, of norm at most twice that of `f`.
* `TauCeti.memLp_indicator_sub_indicator_linearIsometryEquiv_comp_hyperplaneReflection`: for a
  linear isometric equivalence `T`, the field `1_H G - 1_H (T ∘ G) ∘ ρ` lies in `Lᵖ` with norm at
  most twice that of `G`; for `T` the linear part of `ρ` this is the odd reflection of a field.
* `TauCeti.sub_comp_hyperplaneReflection_ae_eq_indicator`: for `f` vanishing off `H`, the odd
  reflection `f - T (f ∘ ρ)` is `1_H f - 1_H (T ∘ f) ∘ ρ`.
* `TauCeti.setIntegral_inner_reflection_comp_hyperplaneReflection`: the reflection moves across a
  pairing, `∫_U ⟪G, R (v ∘ ρ)⟫ = ∫_U ⟪R (G ∘ ρ), v⟫`.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The height above a hyperplane through the origin -/

/-- The height `⟪x, v⟫` above the hyperplane `⟪·, v⟫ = 0` is `1`-Lipschitz. -/
theorem abs_inner_sub_inner_le {v : F} (hv : ‖v‖ = 1) (x y : F) :
    |⟪x, v⟫_ℝ - ⟪y, v⟫_ℝ| ≤ dist x y := by
  rw [← inner_sub_left, dist_eq_norm]
  simpa [hv] using abs_real_inner_le_norm (x - y) v

/-! ### The reflection -/

/-- The **reflection in the affine hyperplane** `{x | ⟪x, ν⟫ = c}`: the affine isometry
`x ↦ x - (2 (⟪x, ν⟫ - c) / ‖ν‖²) ν`, whose linear part is the reflection `(ℝ ∙ ν)ᗮ.reflection` in
the parallel hyperplane through the origin. For `ν = 0` it is the identity. -/
def hyperplaneReflection (ν : F) (c : ℝ) : F ≃ᵃⁱ[ℝ] F :=
  (ℝ ∙ ν)ᗮ.reflection.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ F ((2 * (c / ‖ν‖ ^ 2)) • ν))

/-- The hyperplane reflection is the linear reflection `(ℝ ∙ ν)ᗮ.reflection` followed by the
translation by `(2 c / ‖ν‖²) ν`. -/
theorem hyperplaneReflection_eq_reflection_add (ν : F) (c : ℝ) (x : F) :
    hyperplaneReflection ν c x = (ℝ ∙ ν)ᗮ.reflection x + (2 * (c / ‖ν‖ ^ 2)) • ν := by
  simp [hyperplaneReflection, add_comm]

theorem hyperplaneReflection_apply (ν : F) (c : ℝ) (x : F) :
    hyperplaneReflection ν c x = x - (2 * ((⟪x, ν⟫_ℝ - c) / ‖ν‖ ^ 2)) • ν := by
  simp only [hyperplaneReflection, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv, AffineIsometryEquiv.coe_constVAdd, vadd_eq_add,
    reflection_orthogonal_singleton_apply_div_norm_sq, real_inner_comm ν x]
  rw [sub_div, mul_sub, sub_smul]
  abel

/-- The hyperplane reflection reverses the signed height `⟪x, ν⟫ - c` above the hyperplane. -/
theorem inner_hyperplaneReflection {ν : F} (hν : ν ≠ 0) (c : ℝ) (x : F) :
    ⟪hyperplaneReflection ν c x, ν⟫_ℝ = 2 * c - ⟪x, ν⟫_ℝ := by
  rw [hyperplaneReflection_apply, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
    RCLike.conj_to_real]
  field_simp
  ring

/-- The hyperplane reflection is an involution. -/
@[simp]
theorem hyperplaneReflection_hyperplaneReflection (ν : F) (c : ℝ) (x : F) :
    hyperplaneReflection ν c (hyperplaneReflection ν c x) = x := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp [hyperplaneReflection_apply]
  rw [hyperplaneReflection_apply (x := hyperplaneReflection ν c x), inner_hyperplaneReflection hν,
    hyperplaneReflection_apply, sub_sub, ← add_smul, sub_eq_self, smul_eq_zero]
  left
  ring

/-- The hyperplane reflection is an involution. -/
theorem hyperplaneReflection_involutive (ν : F) (c : ℝ) :
    Function.Involutive (hyperplaneReflection ν c) :=
  hyperplaneReflection_hyperplaneReflection ν c

/-- The inverse of the hyperplane reflection is itself. -/
@[simp]
theorem hyperplaneReflection_symm (ν : F) (c : ℝ) :
    (hyperplaneReflection ν c).symm = hyperplaneReflection ν c := by
  ext x
  rw [AffineIsometryEquiv.symm_apply_eq, hyperplaneReflection_hyperplaneReflection]

/-- The hyperplane reflection fixes every point of the hyperplane `{x | ⟪x, ν⟫ = c}`. -/
theorem hyperplaneReflection_eq_self_of_inner_eq {ν : F} {c : ℝ} {x : F} (hx : ⟪x, ν⟫_ℝ = c) :
    hyperplaneReflection ν c x = x := by
  rw [hyperplaneReflection_apply, hx, sub_self, zero_div, mul_zero, zero_smul, sub_zero]

/-- For `ν ≠ 0` the fixed points of the hyperplane reflection are the points of the hyperplane
`{x | ⟪x, ν⟫ = c}`. -/
theorem hyperplaneReflection_eq_self_iff {ν : F} (hν : ν ≠ 0) (c : ℝ) {x : F} :
    hyperplaneReflection ν c x = x ↔ ⟪x, ν⟫_ℝ = c := by
  have hν2 : ‖ν‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hν)
  rw [hyperplaneReflection_apply, sub_eq_self, smul_eq_zero, or_iff_left hν, mul_eq_zero,
    or_iff_right two_ne_zero, div_eq_zero_iff, or_iff_left hν2, sub_eq_zero]

/-- A ball centred on the hyperplane `{x | ⟪x, ν⟫ = c}` is mapped into itself by the reflection. -/
theorem mapsTo_hyperplaneReflection_ball {ν z : F} {c : ℝ} (hz : ⟪z, ν⟫_ℝ = c) (r : ℝ) :
    Set.MapsTo (hyperplaneReflection ν c) (Metric.ball z r) (Metric.ball z r) := fun y hy => by
  rw [Metric.mem_ball] at hy ⊢
  rwa [← hyperplaneReflection_eq_self_of_inner_eq hz, AffineIsometryEquiv.dist_map]

/-- The closure of the open half-space `{x | c < ⟪x, ν⟫}` lies in the closed half-space
`{x | c ≤ ⟪x, ν⟫}`. -/
theorem closure_setOf_lt_inner_subset (ν : F) (c : ℝ) :
    closure {x : F | c < ⟪x, ν⟫_ℝ} ⊆ {x | c ≤ ⟪x, ν⟫_ℝ} :=
  closure_lt_subset_le continuous_const (continuous_id.inner continuous_const)

/-- A point of the closed half-space `{x | c ≤ ⟪x, ν⟫}` lying in an open set `V` is a limit of
points of the open half-space `{x | c < ⟪x, ν⟫}` in `V`. -/
theorem mem_closure_setOf_lt_inner_inter {ν y : F} (hν : ν ≠ 0) {c : ℝ} (hy : c ≤ ⟪y, ν⟫_ℝ)
    {V : Set F} (hV : IsOpen V) (hyV : y ∈ V) : y ∈ closure ({x | c < ⟪x, ν⟫_ℝ} ∩ V) := by
  have hT : Filter.Tendsto (fun t : ℝ => y + t • ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds y) := by
    have hc : Continuous fun t : ℝ => y + t • ν := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin, hT.eventually (hV.mem_nhds hyV)] with t (ht : 0 < t) htV
  refine ⟨?_, htV⟩
  have hν2 : 0 < ‖ν‖ ^ 2 := by positivity
  simp only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith

/-- The closure of the part in the open half-space `{x | c < ⟪x, ν⟫}` of the open `R`-thickening of
a set `S` lies in the part in the closed half-space `{x | c ≤ ⟪x, ν⟫}` of the closed
`R`-thickening. -/
theorem closure_thickening_inter_setOf_lt_inner_subset (R : ℝ) (S : Set F) (ν : F) (c : ℝ) :
    closure (Metric.thickening R S ∩ {x | c < ⟪x, ν⟫_ℝ}) ⊆
      Metric.cthickening R S ∩ {x | c ≤ ⟪x, ν⟫_ℝ} :=
  (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter
    (Metric.closure_thickening_subset_cthickening R S) (closure_setOf_lt_inner_subset ν c))

/-- Points of the closure of an open half-space `H = {x | c < ⟪x, ν⟫}` outside `H` lie on the
hyperplane, where the reflection is the identity. -/
theorem hyperplaneReflection_eq_self_of_mem_closure {ν : F} {c : ℝ} {H : Set F}
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) {x : F} (hxc : x ∈ closure H) (hxH : x ∉ H) :
    hyperplaneReflection ν c x = x := by
  have hset : H = {x | c < ⟪x, ν⟫_ℝ} := Set.ext hH
  have hle : c ≤ ⟪x, ν⟫_ℝ := by
    rw [hset] at hxc
    exact closure_setOf_lt_inner_subset ν c hxc
  exact hyperplaneReflection_eq_self_of_inner_eq
    (le_antisymm (not_lt.1 fun h => hxH ((hH x).2 h)) hle)

/-- A ball centred on the hyperplane `{x | ⟪x, ν⟫ = c}` is invariant under the reflection. -/
theorem hyperplaneReflection_mem_ball_iff {ν : F} {c : ℝ} {x : F} (hx : ⟪x, ν⟫_ℝ = c) {y : F}
    {r : ℝ} : hyperplaneReflection ν c y ∈ Metric.ball x r ↔ y ∈ Metric.ball x r := by
  rw [Metric.mem_ball, Metric.mem_ball, ← hyperplaneReflection_eq_self_of_inner_eq hx,
    (hyperplaneReflection ν c).dist_map, hyperplaneReflection_eq_self_of_inner_eq hx]

/-- A closed ball centred on the hyperplane `{x | ⟪x, ν⟫ = c}` is invariant under the
reflection. -/
theorem hyperplaneReflection_mem_closedBall_iff {ν : F} {c : ℝ} {x : F} (hx : ⟪x, ν⟫_ℝ = c)
    {y : F} {r : ℝ} :
    hyperplaneReflection ν c y ∈ Metric.closedBall x r ↔ y ∈ Metric.closedBall x r := by
  rw [Metric.mem_closedBall, Metric.mem_closedBall, ← hyperplaneReflection_eq_self_of_inner_eq hx,
    (hyperplaneReflection ν c).dist_map, hyperplaneReflection_eq_self_of_inner_eq hx]

/-- The hyperplane reflection maps the open half-space `{x | c < ⟪x, ν⟫}` onto the opposite
open half-space `{x | ⟪x, ν⟫ < c}`, and conversely. -/
theorem inner_hyperplaneReflection_lt_iff {ν : F} (hν : ν ≠ 0) (c : ℝ) {x : F} :
    ⟪hyperplaneReflection ν c x, ν⟫_ℝ < c ↔ c < ⟪x, ν⟫_ℝ := by
  rw [inner_hyperplaneReflection hν]
  constructor <;> intro h <;> linarith

/-- **Points on one side are closer than their mirror images.** If `x` and `z` both lie in the
closed half-space `{y | c ≤ ⟪y, ν⟫}`, then `x` is at least as close to `z` as to the reflection of
`z` in the hyperplane `{y | ⟪y, ν⟫ = c}`: indeed
`‖x - ρ z‖² = ‖x - z‖² + 4 (⟪z, ν⟫ - c) (⟪x, ν⟫ - c) / ‖ν‖²`. -/
theorem dist_le_dist_hyperplaneReflection {ν : F} {c : ℝ} {x z : F} (hx : c ≤ ⟪x, ν⟫_ℝ)
    (hz : c ≤ ⟪z, ν⟫_ℝ) : dist x z ≤ dist x (hyperplaneReflection ν c z) := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp [hyperplaneReflection_apply]
  have hid : ‖x - hyperplaneReflection ν c z‖ ^ 2 =
      ‖x - z‖ ^ 2 + 4 * (⟪z, ν⟫_ℝ - c) * (⟪x, ν⟫_ℝ - c) / ‖ν‖ ^ 2 := by
    -- Expand both squares.
    simp only [hyperplaneReflection_apply, norm_sub_sq_real, inner_sub_right, inner_smul_right,
      norm_smul, real_inner_comm ν, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
    ring
  have h0 : 0 ≤ 4 * (⟪z, ν⟫_ℝ - c) * (⟪x, ν⟫_ℝ - c) / ‖ν‖ ^ 2 := by
    have := sub_nonneg.2 hx
    have := sub_nonneg.2 hz
    positivity
  rw [dist_eq_norm, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), hid]
  linarith

/-- **Folding across a hyperplane is `1`-Lipschitz.** The map that fixes the closed half-space
`{y | c ≤ ⟪y, ν⟫}` and reflects the other side onto it in the hyperplane `{y | ⟪y, ν⟫ = c}` does
not increase distances. Composing with it extends a function given on the closed half-space to
the whole space, keeping Hölder and Lipschitz constants. -/
theorem lipschitzWith_one_ite_hyperplaneReflection (ν : F) (c : ℝ) :
    LipschitzWith 1 fun x => if c ≤ ⟪x, ν⟫_ℝ then x else hyperplaneReflection ν c x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  rcases eq_or_ne ν 0 with rfl | hν
  · by_cases hc : c ≤ 0 <;> simp [hc]
  -- A point and the mirror image of a point on the other side.
  have hmix {x y : F} (hx : c ≤ ⟪x, ν⟫_ℝ) (hy : ¬c ≤ ⟪y, ν⟫_ℝ) :
      dist x (hyperplaneReflection ν c y) ≤ dist x y := by
    have hρy : c ≤ ⟪hyperplaneReflection ν c y, ν⟫_ℝ := by
      rw [inner_hyperplaneReflection hν]
      linarith [not_le.1 hy]
    simpa [hyperplaneReflection_hyperplaneReflection] using
      dist_le_dist_hyperplaneReflection hx hρy
  split_ifs with hx hy hy
  · exact le_rfl
  · exact hmix hx hy
  · rw [dist_comm, dist_comm x]
    exact hmix hy hx
  · exact ((hyperplaneReflection ν c).dist_map x y).le

/-- Folding across the hyperplane `{y | ⟪y, ν⟫ = c}` lands in the closed half-space
`{y | c ≤ ⟪y, ν⟫}`. -/
theorem le_inner_ite_hyperplaneReflection {ν : F} (hν : ν ≠ 0) (c : ℝ) (x : F) :
    c ≤ ⟪if c ≤ ⟪x, ν⟫_ℝ then x else hyperplaneReflection ν c x, ν⟫_ℝ := by
  split_ifs with hx
  · exact hx
  · rw [inner_hyperplaneReflection hν]
    linarith [not_le.1 hx]

/-- Folding across the hyperplane `{y | ⟪y, ν⟫ = c}` maps every ball centred on the hyperplane
into itself. -/
theorem mapsTo_ite_hyperplaneReflection_ball {ν z : F} {c : ℝ} (hz : ⟪z, ν⟫_ℝ = c) (r : ℝ) :
    Set.MapsTo (fun x => if c ≤ ⟪x, ν⟫_ℝ then x else hyperplaneReflection ν c x)
      (Metric.ball z r) (Metric.ball z r) := fun x hx => by
  dsimp only
  split_ifs
  · exact hx
  · exact mapsTo_hyperplaneReflection_ball hz r hx

/-- **Reflection does not bring a point closer to a set on its side.** If `S` lies in the closed
half-space `{y | c ≤ ⟪y, ν⟫}` and `x` lies in that half-space with its mirror image in the open
`r`-thickening of `S`, then `x` lies in the `r`-thickening of `S` too. -/
theorem mem_thickening_of_hyperplaneReflection_mem_thickening {ν x : F} {c r : ℝ} {S : Set F}
    (hS : ∀ y ∈ S, c ≤ ⟪y, ν⟫_ℝ) (hx : c ≤ ⟪x, ν⟫_ℝ)
    (hρx : hyperplaneReflection ν c x ∈ Metric.thickening r S) : x ∈ Metric.thickening r S := by
  obtain ⟨s, hs, hxs⟩ := Metric.mem_thickening_iff.1 hρx
  refine Metric.mem_thickening_iff.2 ⟨s, hs, ?_⟩
  calc dist x s = dist s x := dist_comm _ _
    _ ≤ dist s (hyperplaneReflection ν c x) := dist_le_dist_hyperplaneReflection (hS s hs) hx
    _ = dist (hyperplaneReflection ν c x) s := dist_comm _ _
    _ < r := hxs

/-- **A reflection-invariant open set around a thickening.** Let `S` be a bounded set of the
closed half-space `{x | c ≤ ⟪x, ν⟫}`, let `ρ` be the reflection in its boundary hyperplane and `T`
the open `r`-thickening of `S`. The open set `T ∪ ρ⁻¹ T` is mapped into itself by `ρ`, contains
`T`, is bounded, and its points in the open half-space `{x | c < ⟪x, ν⟫}` lie in `T`. -/
theorem exists_opens_mapsTo_hyperplaneReflection {ν : F} {c r : ℝ} {S : Set F}
    (hS : Bornology.IsBounded S) (hSc : ∀ x ∈ S, c ≤ ⟪x, ν⟫_ℝ) :
    ∃ U : TopologicalSpace.Opens F, Set.MapsTo (hyperplaneReflection ν c) U U ∧
      Metric.thickening r S ⊆ U ∧ (U : Set F) ∩ {x | c < ⟪x, ν⟫_ℝ} ⊆ Metric.thickening r S ∧
      Bornology.IsBounded (U : Set F) := by
  set ρ := hyperplaneReflection ν c
  refine ⟨⟨Metric.thickening r S ∪ ρ ⁻¹' Metric.thickening r S,
    Metric.isOpen_thickening.union (Metric.isOpen_thickening.preimage ρ.continuous)⟩, ?_,
    fun x hx => Or.inl hx, ?_,
    hS.thickening.union (ρ.isometry.antilipschitzWith.isBounded_preimage hS.thickening)⟩
  · rintro x (hx | hx)
    · exact Or.inr (by simpa [ρ, hyperplaneReflection_hyperplaneReflection] using hx)
    · exact Or.inl hx
  · rintro x ⟨hx | hx, hxH⟩
    · exact hx
    · exact mem_thickening_of_hyperplaneReflection_mem_thickening hSc (le_of_lt hxH) hx

/-- The derivative of the hyperplane reflection at every point is its linear part
`(ℝ ∙ ν)ᗮ.reflection`. -/
theorem hasFDerivAt_hyperplaneReflection (ν : F) (c : ℝ) (x : F) :
    HasFDerivAt (hyperplaneReflection ν c) ((ℝ ∙ ν)ᗮ.reflection : F →L[ℝ] F) x := by
  rw [funext (hyperplaneReflection_eq_reflection_add ν c)]
  exact ((ℝ ∙ ν)ᗮ.reflection : F →L[ℝ] F).hasFDerivAt.add_const _

theorem differentiable_hyperplaneReflection (ν : F) (c : ℝ) :
    Differentiable ℝ (hyperplaneReflection ν c) :=
  fun x => (hasFDerivAt_hyperplaneReflection ν c x).differentiableAt

@[simp]
theorem fderiv_hyperplaneReflection (ν : F) (c : ℝ) (x : F) :
    fderiv ℝ (hyperplaneReflection ν c) x = ((ℝ ∙ ν)ᗮ.reflection : F →L[ℝ] F) :=
  (hasFDerivAt_hyperplaneReflection ν c x).fderiv

/-- The derivative of the hyperplane reflection has determinant of absolute value one. -/
theorem abs_det_fderiv_hyperplaneReflection [FiniteDimensional ℝ F] (ν : F) (c : ℝ) (x : F) :
    |(fderiv ℝ (hyperplaneReflection ν c) x).det| = 1 := by
  rw [fderiv_hyperplaneReflection, ContinuousLinearMap.det]
  exact (congrArg abs ((ℝ ∙ ν)ᗮ.det_reflection (𝕜 := ℝ))).trans (by simp)

/-- The hyperplane reflection preserves every additive Haar measure: it is a linear reflection,
of determinant `±1`, followed by a translation. -/
theorem measurePreserving_hyperplaneReflection [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] (ν : F) (c : ℝ) :
    MeasurePreserving (hyperplaneReflection ν c) μ μ := by
  have hdet := (ℝ ∙ ν)ᗮ.det_reflection (𝕜 := ℝ)
  have hS : MeasurePreserving (ℝ ∙ ν)ᗮ.reflection μ μ := by
    refine ⟨(ℝ ∙ ν)ᗮ.reflection.continuous.measurable, ?_⟩
    simpa [hdet] using Measure.map_linearMap_addHaar_eq_smul_addHaar μ
      (f := (ℝ ∙ ν)ᗮ.reflection.toLinearMap) (by simp [hdet])
  rw [funext (hyperplaneReflection_eq_reflection_add ν c)]
  exact (measurePreserving_add_right μ _).comp hS

/-- The hyperplane reflection preserves the restriction of an additive Haar measure to a
measurable set that it maps into itself. -/
theorem measurePreserving_restrict_hyperplaneReflection [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure] {ν : F} {c : ℝ}
    {V : Set F} (hV : Set.MapsTo (hyperplaneReflection ν c) V V) (hVm : MeasurableSet V) :
    MeasurePreserving (hyperplaneReflection ν c) (μ.restrict V) (μ.restrict V) := by
  have hpre : hyperplaneReflection ν c ⁻¹' V = V :=
    (congrFun (hyperplaneReflection_involutive ν c).image_eq_preimage_symm V).symm.trans
      (hV.image_eq_of_involutive (hyperplaneReflection_involutive ν c))
  simpa only [hpre] using
    (measurePreserving_hyperplaneReflection μ ν c).restrict_preimage hVm

/-- A field equal to `f` on the closed half-space `{x | c ≤ ⟪x, ν⟫}` and to `G ∘ f ∘ ρ` below
it, for a continuous `G`, is a.e. strongly measurable on a measurable set `U` that `ρ` maps into
itself, as soon as `f` is a.e. strongly measurable on the part `U ∩ H` of `U` above the
hyperplane, where `H = {x | c < ⟪x, ν⟫}`. -/
theorem aestronglyMeasurable_piecewise_comp_hyperplaneReflection [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure] {β : Type*}
    [TopologicalSpace β] {ν : F} (hν : ν ≠ 0) {c : ℝ} {H U : Set F}
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) (hUm : MeasurableSet U)
    (hU : Set.MapsTo (hyperplaneReflection ν c) U U) {f : F → β} {G : β → β}
    (hG : Continuous G) (hf : AEStronglyMeasurable f (μ.restrict (U ∩ H))) :
    AEStronglyMeasurable
      ({x | ⟪x, ν⟫_ℝ < c}.piecewise (fun x => G (f (hyperplaneReflection ν c x))) f)
      (μ.restrict U) := by
  have hS : MeasurableSet {x : F | ⟪x, ν⟫_ℝ < c} :=
    measurableSet_lt (continuous_id.inner continuous_const).measurable measurable_const
  have hHm : MeasurableSet H := by
    rw [show H = {x | c < ⟪x, ν⟫_ℝ} from Set.ext hH]
    exact measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable
  refine AEStronglyMeasurable.piecewise hS.nullMeasurableSet ?_ ?_
  · -- Below the hyperplane, `ρ` carries the measure onto the part of `U` above it.
    have hpre : hyperplaneReflection ν c ⁻¹' (U ∩ H) = {x | ⟪x, ν⟫_ℝ < c} ∩ U := by
      have hlt (x : F) : c < ⟪hyperplaneReflection ν c x, ν⟫_ℝ ↔ ⟪x, ν⟫_ℝ < c := by
        simpa only [hyperplaneReflection_hyperplaneReflection] using
          (inner_hyperplaneReflection_lt_iff hν c (x := hyperplaneReflection ν c x)).symm
      ext x
      refine ⟨fun hx => ⟨(hlt x).1 ((hH _).1 hx.2), ?_⟩,
        fun hx => ⟨hU hx.2, (hH _).2 ((hlt x).2 hx.1)⟩⟩
      simpa only [hyperplaneReflection_hyperplaneReflection] using hU hx.1
    have hmp := (measurePreserving_hyperplaneReflection μ ν c).restrict_preimage
      (hUm.inter hHm)
    rw [hpre] at hmp
    rw [Measure.restrict_restrict hS]
    exact hG.comp_aestronglyMeasurable (hf.comp_measurePreserving hmp)
  · -- Above the hyperplane the field is `f`; the hyperplane itself is null.
    rw [Measure.restrict_restrict hS.compl]
    refine hf.mono_measure (Measure.restrict_congr_set ?_).le
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (Measure.addHaar_setOf_inner_eq μ hν c)] with x hx
    have hx' : ⟪x, ν⟫_ℝ ≠ c := hx
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, hH]
    constructor
    · exact fun h => ⟨h.2, lt_of_le_of_ne h.1 (Ne.symm hx')⟩
    · exact fun h => ⟨h.2.le, h.1⟩

/-! ### Odd reflection of a function -/

section OddReflection

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {μ : Measure F}
  [μ.IsAddHaarMeasure] {ν : F} {c : ℝ} {H U : Set F} {E : Type*} [NormedAddCommGroup E]
  {f g : F → E} {p : ENNReal}

/-- **The odd reflection of an `Lᵖ` function.** Let `U` be a measurable set mapped into itself by
the hyperplane reflection `ρ` and let `H` be measurable. If `f, g ∈ Lᵖ(U ∩ H)`, then
`x ↦ 1_H f x - 1_H g (ρ x)` lies in `Lᵖ(U)`. When `H` and `ρ H` are disjoint, for instance when
`H` is an open half-space bounded by the hyperplane, it equals `f` on `H` and `-g ∘ ρ` on `ρ H`.
For `g = f` it is the odd reflection of `f`. -/
theorem memLp_indicator_sub_indicator_comp_hyperplaneReflection (hHm : MeasurableSet H)
    (hUm : MeasurableSet U) (hU : Set.MapsTo (hyperplaneReflection ν c) U U)
    (hf : MemLp f p (μ.restrict (U ∩ H))) (hg : MemLp g p (μ.restrict (U ∩ H))) :
    MemLp (fun x => H.indicator f x - H.indicator g (hyperplaneReflection ν c x)) p
      (μ.restrict U) := by
  exact (memLp_indicator_of_memLp_restrict_inter hHm hf).sub
    ((memLp_indicator_of_memLp_restrict_inter hHm hg).comp_measurePreserving
      (measurePreserving_restrict_hyperplaneReflection hU hUm))

/-- **The norm of the odd reflection.** Let `U` be a measurable set mapped into itself by the
hyperplane reflection `ρ`, let `H` be measurable and let `1 ≤ p`. The function
`x ↦ 1_H f x - 1_H g (ρ x)` has `Lᵖ(U)` norm at most `‖f‖_{Lᵖ(U ∩ H)} + ‖g‖_{Lᵖ(U ∩ H)}`. For
`g = f`, the odd reflection of `f` has norm at most `2 ‖f‖_{Lᵖ(U ∩ H)}`. -/
theorem eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le (hp : 1 ≤ p)
    (hHm : MeasurableSet H) (hUm : MeasurableSet U)
    (hU : Set.MapsTo (hyperplaneReflection ν c) U U) :
    eLpNorm (fun x => H.indicator f x - H.indicator g (hyperplaneReflection ν c x)) p
      (μ.restrict U) ≤ eLpNorm f p (μ.restrict (U ∩ H)) + eLpNorm g p (μ.restrict (U ∩ H)) := by
  have hnorm (k : F → E) :
      eLpNorm (H.indicator k) p (μ.restrict U) = eLpNorm k p (μ.restrict (U ∩ H)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hHm.nullMeasurableSet,
      Measure.restrict_restrict hHm, Set.inter_comm]
  by_cases hg : AEStronglyMeasurable g (μ.restrict (U ∩ H))
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hg]
  have hρ := measurePreserving_restrict_hyperplaneReflection (μ := μ) hU hUm
  have hg' : AEStronglyMeasurable (H.indicator g) (μ.restrict U) := by
    rw [aestronglyMeasurable_indicator_iff hHm, Measure.restrict_restrict hHm, Set.inter_comm]
    exact hg
  calc eLpNorm (fun x => H.indicator f x - H.indicator g (hyperplaneReflection ν c x)) p
        (μ.restrict U)
      ≤ eLpNorm (H.indicator f) p (μ.restrict U) +
          eLpNorm (H.indicator g ∘ hyperplaneReflection ν c) p (μ.restrict U) :=
        eLpNorm_sub_le hp
    _ = eLpNorm f p (μ.restrict (U ∩ H)) + eLpNorm g p (μ.restrict (U ∩ H)) := by
        rw [eLpNorm_comp_measurePreserving hg' hρ, hnorm, hnorm]

/-- **The odd reflection of a vector field.** Let `U` be a measurable set mapped into itself by
the hyperplane reflection `ρ`, let `H` be measurable, let `1 ≤ p` and let `T` be a linear isometric
equivalence of `E`, such as the linear part of `ρ`. If `G ∈ Lᵖ(U ∩ H)`, then
`x ↦ 1_H G x - 1_H (T ∘ G) (ρ x)` lies in `Lᵖ(U)`, with norm at most `2 ‖G‖_{Lᵖ(U ∩ H)}`. -/
theorem memLp_indicator_sub_indicator_linearIsometryEquiv_comp_hyperplaneReflection
    [NormedSpace ℝ E] (hp : 1 ≤ p) (hHm : MeasurableSet H) (hUm : MeasurableSet U)
    (hU : Set.MapsTo (hyperplaneReflection ν c) U U) (T : E ≃ₗᵢ[ℝ] E)
    (hf : MemLp f p (μ.restrict (U ∩ H))) :
    MemLp (fun x => H.indicator f x - H.indicator (fun y => T (f y)) (hyperplaneReflection ν c x))
        p (μ.restrict U) ∧
      eLpNorm (fun x => H.indicator f x -
        H.indicator (fun y => T (f y)) (hyperplaneReflection ν c x)) p (μ.restrict U) ≤
          2 * eLpNorm f p (μ.restrict (U ∩ H)) := by
  refine ⟨memLp_indicator_sub_indicator_comp_hyperplaneReflection hHm hUm hU hf
    (T.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hf), ?_⟩
  refine (eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le hp hHm hUm hU).trans_eq ?_
  rw [LinearIsometryEquiv.eLpNorm_comp, two_mul]

/-- **The odd reflection in indicator form.** Let `U` be a measurable set mapped into itself by
the hyperplane reflection `ρ`, and let `f` vanish almost everywhere on `U ∖ H`. For a map `T` with
`T 0 = 0`, the function `x ↦ f x - T (f (ρ x))` is almost everywhere on `U` the function
`x ↦ 1_H f x - 1_H (T ∘ f) (ρ x)`. -/
theorem sub_comp_hyperplaneReflection_ae_eq_indicator (hUm : MeasurableSet U)
    (hU : Set.MapsTo (hyperplaneReflection ν c) U U) {T : E → E} (hT : T 0 = 0)
    (hf : ∀ᵐ x ∂μ.restrict U, x ∉ H → f x = 0) :
    (fun x => f x - T (f (hyperplaneReflection ν c x))) =ᵐ[μ.restrict U]
      fun x => H.indicator f x - H.indicator (fun y => T (f y)) (hyperplaneReflection ν c x) := by
  filter_upwards [hf,
    (measurePreserving_restrict_hyperplaneReflection hU hUm).quasiMeasurePreserving.ae hf]
    with x h1 h2
  congr 1
  · by_cases hx : x ∈ H
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, h1 hx]
  · by_cases hx : hyperplaneReflection ν c x ∈ H
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, h2 hx, hT]

/-- **Moving the reflection across a pairing.** Let `U` be a measurable set mapped into itself by
the hyperplane reflection `ρ`, with linear part `R = (ℝ ∙ ν)ᗮ.reflection`. For vector fields `G`
and `v` on `F`, pairing `G` with `R (v ∘ ρ)` over `U` is pairing `R (G ∘ ρ)` with `v`:

`∫_U ⟪G, R (v ∘ ρ)⟫ = ∫_U ⟪R (G ∘ ρ), v⟫`,

since `R` is self-adjoint and `ρ` is a measure-preserving involution of `U`. -/
theorem setIntegral_inner_reflection_comp_hyperplaneReflection (hUm : MeasurableSet U)
    (hU : Set.MapsTo (hyperplaneReflection ν c) U U) (G v : F → F) :
    ∫ x in U, ⟪G x, (ℝ ∙ ν)ᗮ.reflection (v (hyperplaneReflection ν c x))⟫_ℝ ∂μ =
      ∫ x in U, ⟪(ℝ ∙ ν)ᗮ.reflection (G (hyperplaneReflection ν c x)), v x⟫_ℝ ∂μ := by
  have h := (measurePreserving_restrict_hyperplaneReflection (μ := μ) hU hUm).integral_comp
    (hyperplaneReflection ν c).toHomeomorph.measurableEmbedding
      fun x => ⟪(ℝ ∙ ν)ᗮ.reflection (G (hyperplaneReflection ν c x)), v x⟫_ℝ
  simp only [hyperplaneReflection_hyperplaneReflection] at h
  rw [← h]
  simp only [LinearIsometryEquiv.inner_map_eq_flip, Submodule.reflection_symm]

/-- **Averages of fields odd under the reflection are normal.** Let `ρ` be the reflection in the
hyperplane `{x | ⟪x, ν⟫ = c}` and `R` its linear part, and let `V` be a measurable set mapped into
itself by `ρ`. If a field `G` satisfies `G ∘ ρ = -R ∘ G` almost everywhere on `V`, as the gradient
of a function odd under `ρ` does, then its average over `V` is a multiple of `ν`. -/
theorem setAverage_eq_inner_div_smul_of_ae_comp_hyperplaneReflection [CompleteSpace F]
    {V : Set F} (hV : Set.MapsTo (hyperplaneReflection ν c) V V) (hVm : MeasurableSet V) {G : F → F}
    (hG : ∀ᵐ x ∂μ.restrict V, G (hyperplaneReflection ν c x) = -(ℝ ∙ ν)ᗮ.reflection (G x)) :
    ⨍ x in V, G x ∂μ = (⟪⨍ x in V, G x ∂μ, ν⟫_ℝ / ‖ν‖ ^ 2) • ν := by
  set m := ⨍ x in V, G x ∂μ
  -- Changing variables by `ρ`, which preserves `μ` on `V`, gives `R m = -m`.
  have hcv := (measurePreserving_restrict_hyperplaneReflection (μ := μ) hV hVm).integral_comp
    (hyperplaneReflection ν c).toHomeomorph.measurableEmbedding G
  have hR := (ℝ ∙ ν)ᗮ.reflection.toLinearIsometry.integral_comp_comm (μ := μ.restrict V) G
  simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hR
  rw [integral_congr_ae hG, integral_neg, hR] at hcv
  have hRm : (ℝ ∙ ν)ᗮ.reflection m = -m := by
    simp only [m, setAverage_eq, map_smul, neg_eq_iff_eq_neg.1 hcv, smul_neg]
  -- Writing `R m = m - 2 p` with `p` the projection of `m` onto `ν`, this says `2 m = 2 p`.
  have h2 : (2 : ℝ) • m = (2 : ℝ) • ((⟪m, ν⟫_ℝ / ‖ν‖ ^ 2) • ν) := by
    rw [reflection_orthogonal_singleton_apply_div_norm_sq, real_inner_comm m ν] at hRm
    linear_combination (norm := module) hRm
  exact smul_right_injective F (two_ne_zero' ℝ) h2

end OddReflection

end TauCeti
