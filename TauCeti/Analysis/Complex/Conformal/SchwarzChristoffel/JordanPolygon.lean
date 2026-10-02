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

Let `U` be a bounded domain whose frontier is a Jordan curve, and which is
polygonal: near each boundary point that is not one of the finitely many vertices `v i` it
coincides with an open half-plane, and near `v i` with the open sector of opening `(e i + 1) * π`
at `v i`, where `e i ∈ (-1, 1)`.  Then there are distinct real prevertices `a i` and complex
constants `A ≠ 0` and `B` such that `A * F + B` maps the upper half-plane bijectively onto `U`,
where `F` is the normalized Schwarz--Christoffel primitive for `a` and `e`, and sends each
prevertex to its vertex: `A * vertex i + B = v i`, where `vertex i` is the limit of `F` at `a i`.

The same holds for an unbounded polygonal domain with a vertex at infinity, one which far out
coincides with an open sector of opening `β * π`, `0 < β < 2`, and whose frontier together with the
point at infinity is a Jordan curve of the Riemann sphere.  The point at infinity of the half-plane
is then the prevertex of the vertex at infinity.

## Main results

* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier` --
  a bounded polygonal Jordan domain is the image of the upper half-plane under an affine image of
  a Schwarz--Christoffel primitive, with the prevertices sent to the vertices.
* `TauCeti.exponent_sum_eq_neg_two_of_isJordanCurve_frontier` -- the turning exponents of a bounded
  polygonal Jordan domain sum to `-2`, so its interior angles sum to `(n - 2) * π`.
* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_insert_infty`
  -- the same representation for an unbounded polygonal Jordan domain with a vertex at infinity.
* `TauCeti.exponent_sum_eq_sub_one_of_isJordanCurve_insert_infty` -- the turning exponents of the
  finite vertices of such a domain sum to `β - 1`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane
open scoped OnePoint

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

/-- A conformal map `f` of the upper half-plane onto `U` which is an affine image of the
Schwarz--Christoffel primitive, and continuous up to the real axis with `f (a i) = v i`, exhibits
`U` as the image of an affine image `A * F + B` of the primitive, with `A ≠ 0`, sending the
Schwarz--Christoffel vertices to the `v i`. -/
private theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_eqOn {ι : Type*}
    [Fintype ι] {e : ι → ℝ} (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane) {U : Set ℂ}
    {v : ι → ℂ} {f : ℂ → ℂ} {a : ι → ℝ} (ha : Injective a)
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
bounded, connected open set whose frontier is a Jordan curve.  Suppose that `U` coincides
near each frontier point other than the distinct vertices `v i` with an open half-plane, and near
the vertex `v i` with the open sector of opening `(e i + 1) * π` at `v i`, where `e i ∈ (-1, 1)`.
Then there are distinct real prevertices `a i` and constants `A ≠ 0` and `B` such that
`z ↦ A * F z + B` maps the upper half-plane bijectively onto `U`, where `F` is the normalized
Schwarz--Christoffel primitive for the prevertices `a` and the turning exponents `e`, and such that
the Schwarz--Christoffel vertex at `a i`, the limit of `F` at `a i`, is sent to `v i`. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hUb : IsBounded U)
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
  exact ⟨a, ha, exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_eqOn he z₀ ha hfd hfc hfH
    hfa (eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain a e ha he z₀ hfd hfc
      hfi hfH.image_eq hfa hfp hpf hside hcorner)⟩

/-- **The angle sum of a bounded polygonal Jordan domain.**  Under the hypotheses of
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier`, the
turning exponents sum to `-2`: the interior angles `(e i + 1) * π` at the `n` vertices sum to
`(n - 2) * π`.  So the Schwarz--Christoffel data of a polygonal Jordan domain always satisfy the
closing condition `∑ i, e i = -2`. -/
theorem exponent_sum_eq_neg_two_of_isJordanCurve_frontier
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hUb : IsBounded U)
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

/-- A Carathéodory map of the upper half-plane onto an unbounded polygonal Jordan domain, sending
infinity to infinity, with real prevertices of the vertices.  The exterior point that
`TauCeti.exists_prevertices_of_isJordanCurve_insert_infty` asks for comes from the sector at
infinity. -/
private theorem exists_prevertices_of_unbounded_polygon {ι : Type*} (e : ι → ℝ)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2) {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) {v : ι → ℂ}
    (hv : Injective v)
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    ∃ f : ℂ → ℂ, ∃ a : ι → ℝ, Injective a ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧ ContinuousOn f {z : ℂ | 0 ≤ z.im} ∧
      InjOn f {z : ℂ | 0 ≤ z.im} ∧ BijOn f upperHalfPlaneSet U ∧ (∀ i, f (a i) = v i) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ) := by
  obtain ⟨ρ, c, b, hb, hU⟩ := hinfty
  obtain ⟨q, hq⟩ := exists_notMem_closure_of_forall_mem_iff_abs_arg_lt hb
    (by nlinarith [Real.pi_pos, hβ.2]) hU
  exact exists_prevertices_of_isJordanCurve_insert_infty hUo hUc hq hUJ hv
    (vertex_mem_frontier_of_corner e he hcorner)

/-- **The Schwarz--Christoffel theorem for an unbounded polygonal Jordan domain.**  Let `U` be a
connected open set whose frontier, together with the point at infinity, is a Jordan curve
of the Riemann sphere.  Suppose that `U` coincides near each frontier point other than the
distinct vertices `v i` with an open half-plane, near the vertex `v i` with the open sector of
opening `(e i + 1) * π` at `v i`, where `e i ∈ (-1, 1)`, and far from a point `c` with the open
sector `{|arg ((z - c) / b)| < β * π / 2}` of opening `β * π`, where `0 < β < 2`: so `U` has a
further vertex at infinity.  Then there are distinct real prevertices `a i` and constants `A ≠ 0`
and `B` such that `z ↦ A * F z + B` maps the upper half-plane bijectively onto `U`, where `F` is
the normalized Schwarz--Christoffel primitive for the prevertices `a` and the turning exponents
`e`, and such that the Schwarz--Christoffel vertex at `a i`, the limit of `F` at `a i`, is sent to
`v i`.  The prevertex of the vertex at infinity is the point at infinity of the half-plane. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_insert_infty
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane)
    {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2) {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) {v : ι → ℂ}
    (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    ∃ a : ι → ℝ, Injective a ∧ ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U ∧
      ∀ i, A * schwarzChristoffelVertex a e z₀ i + B = v i := by
  obtain ⟨f, a, ha, hfd, hfc, hfi, hfH, hfa, hfinf⟩ :=
    exists_prevertices_of_unbounded_polygon e he hβ hUo hUc hUJ hv hcorner hinfty
  exact ⟨a, ha, exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_eqOn he z₀ ha hfd hfc hfH
    hfa (eqOn_const_mul_schwarzChristoffelPrimitive_add_of_unbounded_polygonal_domain a e ha he z₀
      hβ hfd hfc hfi hfH.image_eq hfa hfinf hside hcorner hinfty)⟩

/-- **The angle sum of an unbounded polygonal Jordan domain.**  Under the hypotheses of
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_insert_infty`,
the turning exponents of the finite vertices sum to `β - 1`, where `β * π` is the opening of the
sector at infinity. -/
theorem exponent_sum_eq_sub_one_of_isJordanCurve_insert_infty
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2) {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) {v : ι → ℂ}
    (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    ∑ i, e i = β - 1 := by
  obtain ⟨f, a, ha, hfd, hfc, hfi, hfH, hfa, hfinf⟩ :=
    exists_prevertices_of_unbounded_polygon e he hβ hUo hUc hUJ hv hcorner hinfty
  exact exponent_sum_eq_sub_one_of_unbounded_polygonal_domain a e ha he hβ hfd hfc hfi
    hfH.image_eq hfa hfinf hside hcorner hinfty

end TauCeti

end
