/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.FiniteBoundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Ray
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Ray
import TauCeti.Data.Fin.Basic

/-!
# Finite boundary chains with logarithmic Schwarz--Christoffel ends

The finite trace of a Schwarz--Christoffel boundary is a finite union of segments, closed
rays, and affine lines. Between consecutive real cut points, an integrable endpoint is
included and a logarithmic endpoint is excluded. Two finite endpoints give a segment,
one finite endpoint gives a ray, and two logarithmic endpoints give a line.

`schwarzChristoffelFiniteBoundary_eq_union_edges` assembles these pieces. The ordered cuts
must include all prevertices with nonzero exponent; the first and last cuts must be
integrable. They may be chosen outside all prevertices, so logarithmic extreme prevertices
are allowed. The two outer pieces are segments meeting at the finite vertex at parameter
infinity, or rays when that vertex is infinite. This description does not assume boundary
simplicity or interior univalence. It provides the geometric exceptional set for covering
and separation arguments with several ends.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The geometric finite side between two real parameters. Integrable endpoints contribute
boundary values; logarithmic endpoints contribute ends at infinity. With no nonzero
prevertex between the parameters and endpoint exponent sums at least `-1`, the four cases
are a segment, a positive ray, a negative ray, and an affine line. In the last case the
midpoint supplies a finite origin. -/
def schwarzChristoffelFiniteEdge (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p q : ℝ) : Set ℂ :=
  if -1 < ∑ i with a i = p, e i then
    if -1 < ∑ i with a i = q, e i then
      segment ℝ (schwarzChristoffelBoundary a e z₀ p) (schwarzChristoffelBoundary a e z₀ q)
    else
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ p +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' Ici 0
  else
    if -1 < ∑ i with a i = q, e i then
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ q -
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' Ici 0
    else
      range (fun t : ℝ => schwarzChristoffelBoundary a e z₀ ((p + q) / 2) +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e ((p + q) / 2) * Complex.I))

/-- With two integrable endpoints, the finite side is their closed segment. -/
@[simp]
theorem schwarzChristoffelFiniteEdge_of_integrable_integrable (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ}
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelFiniteEdge a e z₀ p q =
      segment ℝ (schwarzChristoffelBoundary a e z₀ p) (schwarzChristoffelBoundary a e z₀ q) := by
  simp [schwarzChristoffelFiniteEdge, hp, hq]

/-- An integrable left endpoint and a logarithmic right endpoint give the positive ray. -/
@[simp]
theorem schwarzChristoffelFiniteEdge_of_integrable_logarithmic (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ}
    (hp : -1 < ∑ i with a i = p, e i) (hq : ∑ i with a i = q, e i = -1) :
    schwarzChristoffelFiniteEdge a e z₀ p q =
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ p +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' Ici 0 := by
  simp [schwarzChristoffelFiniteEdge, hp, hq]

/-- A logarithmic left endpoint and an integrable right endpoint give the negative ray. -/
@[simp]
theorem schwarzChristoffelFiniteEdge_of_logarithmic_integrable (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ}
    (hp : ∑ i with a i = p, e i = -1) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelFiniteEdge a e z₀ p q =
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ q -
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' Ici 0 := by
  simp [schwarzChristoffelFiniteEdge, hp, hq]

/-- Two logarithmic endpoints give the full affine line through the midpoint value. -/
@[simp]
theorem schwarzChristoffelFiniteEdge_of_logarithmic_logarithmic (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ}
    (hp : ∑ i with a i = p, e i = -1) (hq : ∑ i with a i = q, e i = -1) :
    schwarzChristoffelFiniteEdge a e z₀ p q =
      range (fun t : ℝ => schwarzChristoffelBoundary a e z₀ ((p + q) / 2) +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e ((p + q) / 2) * Complex.I)) := by
  simp [schwarzChristoffelFiniteEdge, hp, hq]

/-- **Exact geometric side image.** On a prevertex-free interval whose endpoint exponent
sums are at least `-1`, the finite side is exactly the image of the integrable parameters.
In particular, the arbitrary ordinary value assigned at a logarithmic endpoint is excluded. -/
theorem schwarzChristoffelFiniteEdge_eq_image (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (hpq : p < q) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 ≤ ∑ i with a i = p, e i) (hq : -1 ≤ ∑ i with a i = q, e i) :
    schwarzChristoffelFiniteEdge a e z₀ p q =
      schwarzChristoffelBoundary a e z₀ ''
        (Icc p q ∩ {x | -1 < ∑ i with a i = x, e i}) := by
  classical
  have hzero {x : ℝ} (hx : x ∈ Ioo p q) : ∑ i with a i = x, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hei
    exact ha i hei ((Finset.mem_filter.mp hi).2 ▸ hx)
  have hinterior {x : ℝ} (hx : x ∈ Ioo p q) : -1 < ∑ i with a i = x, e i := by
    rw [hzero hx]
    norm_num
  have hmem (x : ℝ) :
      x ∈ Icc p q ∩ {x | -1 < ∑ i with a i = x, e i} ↔
        p ≤ x ∧ x ≤ q ∧ (x = p → -1 < ∑ i with a i = p, e i) ∧
          (x = q → -1 < ∑ i with a i = q, e i) := by
    constructor
    · rintro ⟨⟨hpx, hxq⟩, hx⟩
      exact ⟨hpx, hxq, fun h => h ▸ hx, fun h => h ▸ hx⟩
    · rintro ⟨hpx, hxq, hxp, hxq'⟩
      refine ⟨⟨hpx, hxq⟩, ?_⟩
      rcases hpx.eq_or_lt with rfl | hpx
      · exact hxp rfl
      rcases hxq.eq_or_lt with rfl | hxq
      · exact hxq' rfl
      exact hinterior ⟨hpx, hxq⟩
  -- The endpoint tests select precisely the closed, half-open, or open source interval.
  rcases hp.eq_or_lt with hp | hp <;> rcases hq.eq_or_lt with hq | hq
  · have hdom : Icc p q ∩ {x | -1 < ∑ i with a i = x, e i} = Ioo p q := by
      ext x
      simp only [hmem, mem_Ioo]
      grind
    rw [hdom, schwarzChristoffelFiniteEdge_of_logarithmic_logarithmic a e z₀ hp.symm hq.symm]
    exact (schwarzChristoffelBoundary_image_Ioo_eq_range_of_endpoint_sums_eq_neg_one
      a e z₀ (by constructor <;> linarith : (p + q) / 2 ∈ Ioo p q)
      ha hp.symm hq.symm).symm
  · have hdom : Icc p q ∩ {x | -1 < ∑ i with a i = x, e i} = Ioc p q := by
      ext x
      simp only [hmem, mem_Ioc]
      grind
    rw [hdom, schwarzChristoffelFiniteEdge_of_logarithmic_integrable a e z₀ hp.symm hq]
    exact (schwarzChristoffelBoundary_image_Ioc_eq_ray_of_left_sum_eq_neg_one
      a e z₀ hpq ha hp.symm hq).symm
  · have hdom : Icc p q ∩ {x | -1 < ∑ i with a i = x, e i} = Ico p q := by
      ext x
      simp only [hmem, mem_Ico]
      grind
    rw [hdom, schwarzChristoffelFiniteEdge_of_integrable_logarithmic a e z₀ hp hq.symm]
    exact (schwarzChristoffelBoundary_image_Ico_eq_ray_of_right_sum_eq_neg_one
      a e z₀ hpq ha hp hq.symm).symm
  · have hdom : Icc p q ∩ {x | -1 < ∑ i with a i = x, e i} = Icc p q := by
      ext x
      simp only [hmem, mem_Icc]
      grind
    rw [hdom, schwarzChristoffelFiniteEdge_of_integrable_integrable a e z₀ hp hq]
    exact (schwarzChristoffelBoundary_image_Icc a e z₀ hpq.le ha hp hq).symm

/-- **Finite boundary assembly with several logarithmic ends.** Choose strictly increasing
cuts containing every nonzero prevertex and with integrable extreme cuts. The complete finite
trace is the union of the consecutive finite sides and two outer pieces. When parameter
infinity has a finite image, the outer pieces are closed segments including that vertex;
otherwise they are closed rays. The cuts need not themselves be prevertices. -/
theorem schwarzChristoffelFiniteBoundary_eq_union_edges {n : ℕ}
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (b : Fin (n + 1) → ℝ) (hb : StrictMono b)
    (hab : ∀ j, e j ≠ 0 → a j ∈ range b)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = b j, e i)
    (hleft : -1 < ∑ i with a i = b 0, e i)
    (hright : -1 < ∑ i with a i = b (Fin.last n), e i) :
    schwarzChristoffelFiniteBoundary a e z₀ =
      (if ∑ i, e i < -1 then
        segment ℝ (schwarzChristoffelBoundary a e z₀ (b 0))
          (schwarzChristoffelVertexAtInfinity a e z₀) ∪
        segment ℝ (schwarzChristoffelBoundary a e z₀ (b (Fin.last n)))
          (schwarzChristoffelVertexAtInfinity a e z₀)
      else
        ((fun t : ℝ => schwarzChristoffelBoundary a e z₀ (b 0) -
          (t : ℂ) * exp ((Real.pi * ∑ i, e i) * Complex.I)) '' Ici 0) ∪
        ((fun t : ℝ => schwarzChristoffelBoundary a e z₀ (b (Fin.last n)) +
          (t : ℂ)) '' Ici 0)) ∪
      ⋃ j : Fin n, schwarzChristoffelFiniteEdge a e z₀ (b j.castSucc) (b j.succ) := by
  classical
  let B := schwarzChristoffelBoundary a e z₀
  let D : Set ℝ := {x | -1 < ∑ i with a i = x, e i}
  have hamin : ∀ i, e i ≠ 0 → b 0 ≤ a i := by
    intro i hi
    obtain ⟨j, hj⟩ := hab i hi
    rw [← hj]
    exact hb.monotone j.zero_le
  have hamax : ∀ i, e i ≠ 0 → a i ≤ b (Fin.last n) := by
    intro i hi
    obtain ⟨j, hj⟩ := hab i hi
    rw [← hj]
    exact hb.monotone j.le_last
  -- Split the real line at the cuts, keeping logarithmic parameters out of the trace.
  have hcover : (univ : Set ℝ) =
      (Iic (b 0) ∪ Ici (b (Fin.last n))) ∪
        ⋃ j : Fin n, Icc (b j.castSucc) (b j.succ) := by
    ext x
    simp only [mem_univ, mem_union, mem_iUnion, mem_Iic, mem_Ici, true_iff]
    by_cases hl : x ≤ b 0
    · exact Or.inl (Or.inl hl)
    by_cases hr : b (Fin.last n) ≤ x
    · exact Or.inl (Or.inr hr)
    have hn : n ≠ 0 := by
      rintro rfl
      simp only [Fin.last_zero] at hr
      exact hr (le_of_not_ge hl)
    exact Or.inr (exists_mem_Icc_castSucc_succ b hb.monotone hn
      ⟨(le_of_not_ge hl), (le_of_not_ge hr)⟩)
  have hDl : Iic (b 0) ⊆ D := fun x hx =>
    Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (γ := OrderDual ℝ)
      Finset.univ (by norm_num) hleft (fun i _ hi => hamin i hi) hx
  have hDr : Ici (b (Fin.last n)) ⊆ D := fun x hx =>
    Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le
      Finset.univ (by norm_num) hright (fun i _ hi => hamax i hi) hx
  have hfree (j : Fin n) : ∀ i, e i ≠ 0 → a i ∉ Ioo (b j.castSucc) (b j.succ) := by
    intro i hi
    obtain ⟨k, hk⟩ := hab i hi
    rw [← hk]
    exact not_mem_Ioo_castSucc_succ b hb.monotone j k
  -- Each consecutive interval has exactly the geometric image identified above.
  have hdecomp : B '' D = (B '' Iic (b 0) ∪ B '' Ici (b (Fin.last n))) ∪
      ⋃ j : Fin n, schwarzChristoffelFiniteEdge a e z₀ (b j.castSucc) (b j.succ) := by
    have hD : D = (Iic (b 0) ∪ Ici (b (Fin.last n))) ∪
        ⋃ j : Fin n, (Icc (b j.castSucc) (b j.succ) ∩ D) := by
      calc
        D = univ ∩ D := (univ_inter D).symm
        _ = _ := by
          rw [hcover, union_inter_distrib_right, union_inter_distrib_right,
            inter_eq_left.mpr hDl, inter_eq_left.mpr hDr, iUnion_inter]
    rw [hD, image_union, image_union, image_iUnion]
    congr 1
    apply iUnion_congr
    intro j
    exact (schwarzChristoffelFiniteEdge_eq_image a e z₀
      (hb j.castSucc_lt_succ) (hfree j) (hfinite j.castSucc) (hfinite j.succ)).symm
  have htrace : schwarzChristoffelFiniteBoundary a e z₀ = B '' D ∪
      if ∑ i, e i < -1 then {schwarzChristoffelVertexAtInfinity a e z₀} else ∅ := by
    ext w
    simp [mem_schwarzChristoffelFiniteBoundary, B, D]
  rw [htrace, hdecomp]
  -- Add the finite value at parameter infinity, or use the two divergent outer rays.
  by_cases hS : ∑ i, e i < -1
  · rw [ite_eq_left hS, ite_eq_left hS,
      schwarzChristoffelBoundary_image_Iic a e z₀ hleft hamin hS,
      schwarzChristoffelBoundary_image_Ici a e z₀ hright hamax hS]
    have hVl : schwarzChristoffelVertexAtInfinity a e z₀ ∈
        segment ℝ (B (b 0)) (schwarzChristoffelVertexAtInfinity a e z₀) := right_mem_segment ..
    have hVr : schwarzChristoffelVertexAtInfinity a e z₀ ∈
        segment ℝ (B (b (Fin.last n))) (schwarzChristoffelVertexAtInfinity a e z₀) :=
      right_mem_segment ..
    ext w
    simp only [mem_union, mem_sdiff, mem_singleton_iff]
    grind
  · rw [ite_eq_right hS, ite_eq_right hS, union_empty,
      schwarzChristoffelBoundary_image_Iic_eq_ray a e z₀ hleft hamin (le_of_not_gt hS),
      schwarzChristoffelBoundary_image_Ici_eq_ray a e z₀ hright hamax (le_of_not_gt hS)]

end TauCeti
