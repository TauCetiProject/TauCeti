/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.PolygonalDomain
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Vertex
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.LocalFrontier

/-!
# The Schwarz--Christoffel theorem for polygonal Jordan domains

Let `U` be a bounded, simply connected domain whose frontier is a Jordan curve, and which is
polygonal: near each boundary point that is not one of the finitely many vertices `v i` it
coincides with an open half-plane, and near `v i` with the open sector of opening `(e i + 1) * π`
at `v i`, where `e i ∈ (-1, 1)`.  Then there are distinct real prevertices `a i` and complex
constants `A ≠ 0` and `B` such that `A * F + B` maps the upper half-plane bijectively onto `U`,
where `F` is the normalized Schwarz--Christoffel primitive for `a` and `e`, and sends each
prevertex to its vertex: `A * vertex i + B = v i`, where `vertex i` is the limit of `F` at `a i`.

The same holds for an unbounded polygonal domain `U` with a vertex at infinity, whose frontier is
homeomorphic to the real line and which far from some point `c` coincides with an open sector at
`c` of opening `β * π`, where `0 < β < 2`.  The point at infinity of the half-plane then
corresponds to the vertex at infinity, and the turning exponents of the finite vertices sum to
`β - 1` instead of `-2`.

## Main results

* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier` --
  a bounded polygonal Jordan domain is the image of the upper half-plane under an affine image of
  a Schwarz--Christoffel primitive, with the prevertices sent to the vertices.
* `TauCeti.exponent_sum_eq_neg_two_of_isJordanCurve_frontier` -- the turning exponents of a bounded
  polygonal Jordan domain sum to `-2`, so its interior angles sum to `(n - 2) * π`.
* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_frontier_homeomorph_real` --
  an unbounded polygonal domain with a vertex at infinity is likewise the image of the upper
  half-plane under an affine image of a Schwarz--Christoffel primitive.
* `TauCeti.exponent_sum_eq_sub_one_of_frontier_homeomorph_real` -- the turning exponents of the
  finite vertices of such a domain, of opening `β * π` at infinity, sum to `β - 1`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- A local corner sector of angle strictly between zero and `2π` places its vertex on the
frontier of the domain. -/
private theorem vertex_mem_frontier_of_corner {ι : Type*} (e : ι → ℝ)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) {U : Set ℂ} {v : ι → ℂ}
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (i : ι) : v i ∈ frontier U := by
  obtain ⟨ρ, hρ, b, hb, hU⟩ := hcorner i
  have he₁ := he i
  refine mem_frontier_of_forall_mem_iff_abs_arg_lt hρ hb ?_ ?_ hU
  · nlinarith [Real.pi_pos, he₁.1]
  · nlinarith [Real.pi_pos, he₁.2]

/-- A conformal map `f` of the upper half-plane onto `U`, continuous up to the real axis with
`f (a i) = v i`, which is an affine image of the Schwarz--Christoffel primitive, supplies the
affine data of the Schwarz--Christoffel theorem: that affine image of the primitive maps the upper
half-plane bijectively onto `U` and sends the Schwarz--Christoffel vertex at `a i` to `v i`. -/
private theorem exists_bijOn_of_eqOn_const_mul_schwarzChristoffelPrimitive_add
    {ι : Type*} [Fintype ι] {a e : ι → ℝ} (ha : Injective a) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    (z₀ : UpperHalfPlane) {U : Set ℂ} {v : ι → ℂ} {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfH : BijOn f upperHalfPlaneSet U) (hfa : ∀ i, f (a i) = v i)
    (hform : EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand a e z₀ *
      schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet) :
    ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U ∧
      ∀ i, A * schwarzChristoffelVertex a e z₀ i + B = v i := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  refine ⟨_, div_ne_zero ?_ (schwarzChristoffelIntegrand_ne_zero a e z₀.im_pos), _,
    hfH.congr hform, fun i => ?_⟩
  · exact deriv_ne_zero_of_injOn hfd isOpen_upperHalfPlaneSet hfH.injOn z₀.im_pos
  -- both sides are limits at the prevertex `a i` from the upper half-plane
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot (a i)
  have hsum : -1 < ∑ l with a l = a i, e l := by
    rw [Finset.sum_eq_single_of_mem i (by simp) fun l hl hli =>
      absurd (ha (Finset.mem_filter.mp hl).2) hli]
    exact (he i).1
  refine tendsto_nhds_unique
    ((((tendsto_schwarzChristoffelPrimitive a e z₀ i hsum).const_mul _).add_const _)) ?_
  rw [← hfa i]
  exact ((hfc _ (by simp)).tendsto.mono_left (nhdsWithin_mono _ hH0)).congr'
    (eventually_nhdsWithin_of_forall hform)

/-- **The Schwarz--Christoffel theorem for a bounded polygonal Jordan domain.**  Let `U` be a
bounded, simply connected open set whose frontier is a Jordan curve.  Suppose that `U` coincides
near each frontier point other than the distinct vertices `v i` with an open half-plane, and near
the vertex `v i` with the open sector of opening `(e i + 1) * π` at `v i`, where `e i ∈ (-1, 1)`.
Then there are distinct real prevertices `a i` and constants `A ≠ 0` and `B` such that
`z ↦ A * F z + B` maps the upper half-plane bijectively onto `U`, where `F` is the normalized
Schwarz--Christoffel primitive for the prevertices `a` and the turning exponents `e`, and such that
the Schwarz--Christoffel vertex at `a i`, the limit of `F` at `a i`, is sent to `v i`. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {v : ι → ℂ} (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2)) :
    ∃ a : ι → ℝ, Injective a ∧ ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U ∧
      ∀ i, A * schwarzChristoffelVertex a e z₀ i + B = v i := by
  obtain ⟨f, a, p, ha, hfd, hfc, hfi, hfH, hfa, hfp, hpf⟩ :=
    exists_prevertices_of_isJordanCurve_frontier hUo hUc hUb hUJ hv
      (vertex_mem_frontier_of_corner e he hcorner)
  exact ⟨a, ha, exists_bijOn_of_eqOn_const_mul_schwarzChristoffelPrimitive_add ha he z₀ hfd hfc
    hfH hfa (eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain a e ha he z₀ hfd
      hfc hfi hfH.image_eq hfa hfp hpf hside hcorner)⟩

/-- **The angle sum of a bounded polygonal Jordan domain.**  Under the hypotheses of
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier`, the
turning exponents sum to `-2`: the interior angles `(e i + 1) * π` at the `n` vertices sum to
`(n - 2) * π`.  So the Schwarz--Christoffel data of a polygonal Jordan domain always satisfy the
closing condition `∑ i, e i = -2`. -/
theorem exponent_sum_eq_neg_two_of_isJordanCurve_frontier
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {v : ι → ℂ} (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2)) :
    ∑ i, e i = -2 := by
  obtain ⟨f, a, p, ha, hfd, hfc, hfi, hfH, hfa, hfp, hpf⟩ :=
    exists_prevertices_of_isJordanCurve_frontier hUo hUc hUb hUJ hv
      (vertex_mem_frontier_of_corner e he hcorner)
  exact exponent_sum_eq_neg_two_of_polygonal_domain a e ha he hfd hfc hfi hfH.image_eq hfa hfp
    hpf hside hcorner

/-- A set which far from `c` coincides with the open sector `{|arg ((z - c) / b)| < β * π / 2}` of
opening less than `2π` misses the far part of the opposite sector, an open set, so its closure is
not the whole plane. -/
private theorem closure_ne_univ_of_forall_mem_iff_abs_arg_lt {U : Set ℂ} {β ρ : ℝ}
    (hβ : β ∈ Ioo (0 : ℝ) 2) {c b : ℂ} (hb : b ≠ 0)
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ → (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    closure U ≠ univ := by
  have hβπ : 0 ≤ β * Real.pi / 2 := by have := hβ.1; positivity
  have hβπ' : β * Real.pi / 2 < Real.pi := by nlinarith [Real.pi_pos, hβ.2]
  -- points far out in the opposite direction, where `arg` is close to `π`
  set W : Set ℂ :=
    {z | ρ < ‖z - c‖ ∧ ((z - c) / b).re < Real.cos (β * Real.pi / 2) * ‖(z - c) / b‖}
  have hWo : IsOpen W :=
    (isOpen_lt (g := fun z : ℂ => ‖z - c‖) continuous_const (by fun_prop)).inter
      (isOpen_lt (f := fun z : ℂ => ((z - c) / b).re) (by fun_prop) (by fun_prop))
  have hWU : Disjoint W U := by
    refine disjoint_left.2 fun z ⟨hz, hzW⟩ hzU => ?_
    have hx : (z - c) / b ≠ 0 := fun h => by simp [h] at hzW
    -- in the sector, `cos (arg x) > cos (β * π / 2)`
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hβπ'.le ((hU z hz).1 hzU)
    rw [Real.cos_abs, cos_arg hx, lt_div_iff₀ (norm_pos_iff.2 hx)] at hcos
    exact hcos.not_gt hzW
  set t : ℝ := (|ρ| + 1) / ‖b‖
  have ht : 0 < t := by have := norm_pos_iff.2 hb; positivity
  have hpW : c - b * t ∈ W := by
    have hdiv : (c - b * t - c) / b = ((-t : ℝ) : ℂ) := by field_simp; push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le,
        mul_div_cancel₀ _ (norm_ne_zero_iff.2 hb)]
      linarith [le_abs_self ρ]
    · rw [hdiv, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hβπ le_rfl hβπ'
      rw [Real.cos_pi] at this
      nlinarith
  exact fun h => (hWU.closure_right hWo).notMem_of_mem_left hpW (h ▸ mem_univ _)

/-- **The Schwarz--Christoffel theorem for an unbounded polygonal domain.**  Let `U` be a simply
connected open set whose frontier is homeomorphic to the real line.  Suppose that `U` coincides
near each frontier point other than the distinct vertices `v i` with an open half-plane, near the
vertex `v i` with the open sector of opening `(e i + 1) * π` at `v i`, where `e i ∈ (-1, 1)`, and
far from a point `c` with the open sector `{|arg ((z - c) / b)| < β * π / 2}` of opening `β * π`,
where `0 < β < 2`.  Then there are distinct real prevertices `a i` and constants `A ≠ 0` and `B`
such that `z ↦ A * F z + B` maps the upper half-plane bijectively onto `U`, where `F` is the
normalized Schwarz--Christoffel primitive for the prevertices `a` and the turning exponents `e`,
and such that the Schwarz--Christoffel vertex at `a i`, the limit of `F` at `a i`, is sent to
`v i`.  The vertex at infinity of `U` corresponds to the point at infinity of the half-plane. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_frontier_homeomorph_real
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUJ : Nonempty (frontier U ≃ₜ ℝ))
    {v : ι → ℂ} (hv : Injective v) {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    ∃ a : ι → ℝ, Injective a ∧ ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U ∧
      ∀ i, A * schwarzChristoffelVertex a e z₀ i + B = v i := by
  obtain ⟨ρ, c, b, hb, hU⟩ := hinfty
  obtain ⟨f, a, ha, hfd, hfc, hfi, hfH, hfa, hf⟩ :=
    exists_prevertices_of_frontier_homeomorph_real hUo hUc
      (closure_ne_univ_of_forall_mem_iff_abs_arg_lt hβ hb hU) hUJ hv
      (vertex_mem_frontier_of_corner e he hcorner)
  exact ⟨a, ha, exists_bijOn_of_eqOn_const_mul_schwarzChristoffelPrimitive_add ha he z₀ hfd hfc
    hfH hfa (eqOn_const_mul_schwarzChristoffelPrimitive_add_of_unbounded_polygonal_domain a e ha
      he z₀ hβ hfd hfc hfi hfH.image_eq hfa hf hside hcorner ⟨ρ, c, b, hb, hU⟩)⟩

/-- **The angle sum of an unbounded polygonal domain.**  Under the hypotheses of
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_frontier_homeomorph_real`, the
turning exponents of the finite vertices sum to `β - 1`, where `β * π` is the opening of `U` at
infinity.  So the Schwarz--Christoffel data of such a domain satisfy `∑ i, e i = β - 1`. -/
theorem exponent_sum_eq_sub_one_of_frontier_homeomorph_real
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUJ : Nonempty (frontier U ≃ₜ ℝ))
    {v : ι → ℂ} (hv : Injective v) {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    ∑ i, e i = β - 1 := by
  obtain ⟨ρ, c, b, hb, hU⟩ := hinfty
  obtain ⟨f, a, ha, hfd, hfc, hfi, hfH, hfa, hf⟩ :=
    exists_prevertices_of_frontier_homeomorph_real hUo hUc
      (closure_ne_univ_of_forall_mem_iff_abs_arg_lt hβ hb hU) hUJ hv
      (vertex_mem_frontier_of_corner e he hcorner)
  exact exponent_sum_eq_sub_one_of_unbounded_polygonal_domain a e ha he hβ hfd hfc hfi
    hfH.image_eq hfa hf hside hcorner ⟨ρ, c, b, hb, hU⟩

end TauCeti

end
