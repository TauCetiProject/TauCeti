/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Divergence
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge
import TauCeti.Data.Fin.Basic

/-!
# The infinite rays of a Schwarz--Christoffel boundary

When the total turning exponent is at least `-1`, the two outer boundary edges have infinite
length. Each traces an entire closed ray from its finite endpoint: the right ray points in the
positive real direction, and the left ray points in direction `-exp (π * (∑ i, e i) * I)`.
The local exponent sum at the finite endpoint must exceed `-1`, so that the endpoint is attained.

For ordered prevertices, these two rays and the segments between consecutive finite vertices
give the complete range of the boundary map. This identifies the polygonal chain parametrized
by that map; it does not assert simplicity, interior injectivity, or equality with the frontier
of the interior image.

## Main results

* `TauCeti.schwarzChristoffelBoundary_image_Ici_eq_ray` and
  `TauCeti.schwarzChristoffelBoundary_image_Iic_eq_ray` identify the two outer edge images.
* `TauCeti.range_schwarzChristoffelBoundary_of_neg_one_le_sum` identifies the entire boundary
  range as the union of the finite sides and the two infinite rays.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The right outer Schwarz--Christoffel edge is an infinite ray.** If the total exponent
is at least `-1`, all prevertices with nonzero exponent lie at or to the left of `p`, and the
exponent sum at `p` is greater than `-1`, the boundary map on `Ici p` traces the full positive
horizontal ray starting at its value at `p`. -/
theorem schwarzChristoffelBoundary_image_Ici_eq_ray (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p : ℝ} (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hS : -1 ≤ ∑ i, e i) :
    schwarzChristoffelBoundary a e z₀ '' Ici p =
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ p + (t : ℂ)) '' Ici 0 := by
  let B := schwarzChristoffelBoundary a e z₀
  let d : ℝ → ℝ := fun x => ‖B x - B p‖
  have hcont : ContinuousOn B (Ici p) :=
    continuousOn_schwarzChristoffelBoundary_Ici a e z₀ hp ha
  have hdir {x : ℝ} (hx : p ≤ x) : B x = B p + (d x : ℂ) := by
    have h := schwarzChristoffelBoundary_sub_eq_norm_mul_of_forall_le a e z₀ hp ha hx
    have hangle : schwarzChristoffelEdgeAngle a e p = 0 := by
      rw [schwarzChristoffelEdgeAngle_eq_sum_filter]
      have hzero : ∑ i ∈ Finset.univ.filter (fun i => p < a i), e i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          by_contra hei
          exact (not_lt_of_ge (ha i hei)) (Finset.mem_filter.mp hi).2
      rw [hzero, mul_zero]
    simp only [hangle, ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h
    exact sub_eq_iff_eq_add'.mp h
  have hdt : Tendsto d atTop atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact (tendsto_sub_const_cobounded (B p)).comp
      (tendsto_schwarzChristoffelBoundary_atTop_cobounded a e z₀ hS)
  have hdimage : d '' Ici p = Ici 0 := by
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨x, _, rfl⟩
      exact norm_nonneg _
    · have hdcont : ContinuousOn d (Ici p) := (hcont.sub continuousOn_const).norm
      simpa only [d, sub_self, norm_zero] using intermediate_value_Ici hdcont hdt
  calc
    B '' Ici p = (fun t : ℝ => B p + (t : ℂ)) '' (d '' Ici p) := by
      rw [← image_comp]
      exact image_congr fun x hx => hdir hx
    _ = _ := by rw [hdimage]

/-- The right outer ray based at a prevertex starts at its corresponding Schwarz--Christoffel
vertex. -/
theorem schwarzChristoffelBoundary_image_Ici_eq_ray_prevertex (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j : ι) (hj : -1 < ∑ i with a i = a j, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ a j) (hS : -1 ≤ ∑ i, e i) :
    schwarzChristoffelBoundary a e z₀ '' Ici (a j) =
      (fun t : ℝ => schwarzChristoffelVertex a e z₀ j + (t : ℂ)) '' Ici 0 := by
  rw [schwarzChristoffelBoundary_image_Ici_eq_ray a e z₀ hj ha hS,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj]

/-- **The left outer Schwarz--Christoffel edge is an infinite ray.** If the total exponent
is at least `-1`, all prevertices with nonzero exponent lie at or to the right of `p`, and the
exponent sum at `p` is greater than `-1`, the boundary map on `Iic p` traces the full ray from
its value at `p` in direction `-exp (π * (∑ i, e i) * I)`. -/
theorem schwarzChristoffelBoundary_image_Iic_eq_ray (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p : ℝ} (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) (hS : -1 ≤ ∑ i, e i) :
    schwarzChristoffelBoundary a e z₀ '' Iic p =
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ p -
        (t : ℂ) * Complex.exp ((Real.pi * ∑ i, e i) * Complex.I)) '' Ici 0 := by
  let B := schwarzChristoffelBoundary a e z₀
  let d : ℝ → ℝ := fun x => ‖B p - B x‖
  let u : ℂ := Complex.exp ((Real.pi * ∑ i, e i) * Complex.I)
  have hcont : ContinuousOn B (Iic p) :=
    continuousOn_schwarzChristoffelBoundary_Iic a e z₀ hp ha
  have hdir {x : ℝ} (hx : x ≤ p) : B x = B p - (d x : ℂ) * u := by
    have h' : B p - B x = (d x : ℂ) * u :=
      schwarzChristoffelBoundary_sub_eq_norm_mul_of_forall_ge a e z₀ hp ha hx
    linear_combination -h'
  have hdt : Tendsto d atBot atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact (tendsto_const_sub_cobounded (B p)).comp
      (tendsto_schwarzChristoffelBoundary_atBot_cobounded a e z₀ hS)
  have hdimage : d '' Iic p = Ici 0 := by
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨x, _, rfl⟩
      exact norm_nonneg _
    · have hdcont : ContinuousOn d (Iic p) := (continuousOn_const.sub hcont).norm
      simpa only [d, sub_self, norm_zero] using intermediate_value_Iic' hdcont hdt
  calc
    B '' Iic p = (fun t : ℝ => B p - (t : ℂ) * u) '' (d '' Iic p) := by
      rw [← image_comp]
      exact image_congr fun x hx => hdir hx
    _ = _ := by simp only [hdimage, B, u]

/-- The left outer ray based at a prevertex starts at its corresponding Schwarz--Christoffel
vertex. -/
theorem schwarzChristoffelBoundary_image_Iic_eq_ray_prevertex (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j : ι) (hj : -1 < ∑ i with a i = a j, e i)
    (ha : ∀ i, e i ≠ 0 → a j ≤ a i) (hS : -1 ≤ ∑ i, e i) :
    schwarzChristoffelBoundary a e z₀ '' Iic (a j) =
      (fun t : ℝ => schwarzChristoffelVertex a e z₀ j -
        (t : ℂ) * Complex.exp ((Real.pi * ∑ i, e i) * Complex.I)) '' Ici 0 := by
  rw [schwarzChristoffelBoundary_image_Iic_eq_ray a e z₀ hj ha hS,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj]

/-- **An unbounded Schwarz--Christoffel boundary is a chain of finite sides and two rays.**
For ordered prevertices with integrable finite exponent sums and total exponent at least `-1`,
the complete boundary range consists of the consecutive vertex segments, a horizontal ray
from the last vertex, and a ray from the first vertex in direction `-exp (π * (∑ i, e i) * I)`.
The formula does not require the chain to be simple. -/
theorem range_schwarzChristoffelBoundary_of_neg_one_le_sum {n : ℕ}
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hS : -1 ≤ ∑ i, e i) :
    range (schwarzChristoffelBoundary a e z₀) =
      ((fun t : ℝ => schwarzChristoffelVertex a e z₀ 0 -
        (t : ℂ) * Complex.exp ((Real.pi * ∑ i, e i) * Complex.I)) '' Ici 0 ∪
      ⋃ i : Fin n, segment ℝ (schwarzChristoffelVertex a e z₀ i.castSucc)
        (schwarzChristoffelVertex a e z₀ i.succ)) ∪
      (fun t : ℝ => schwarzChristoffelVertex a e z₀ (Fin.last n) + (t : ℂ)) '' Ici 0 := by
  classical
  have hcover : (univ : Set ℝ) =
      (Iic (a 0) ∪ ⋃ i : Fin n, Icc (a i.castSucc) (a i.succ)) ∪ Ici (a (Fin.last n)) := by
    ext x
    simp only [mem_univ, mem_union, mem_iUnion, mem_Iic, mem_Ici, true_iff]
    by_cases hleft : x ≤ a 0
    · exact Or.inl (Or.inl hleft)
    by_cases hright : a (Fin.last n) ≤ x
    · exact Or.inr hright
    have hn : n ≠ 0 := by
      rintro rfl
      simp only [Fin.last_zero] at hright
      exact hright (le_of_not_ge hleft)
    exact Or.inl (Or.inr (exists_mem_Icc_castSucc_succ a ha hn
      ⟨(le_of_not_ge hleft), (le_of_not_ge hright)⟩))
  have hbounded (i : Fin n) := schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
    (ha i.castSucc_le_succ) (fun j _ => not_mem_Ioo_castSucc_succ a ha i j)
    (hfinite i.castSucc) (hfinite i.succ)
  have hleft := schwarzChristoffelBoundary_image_Iic_eq_ray_prevertex a e z₀ 0 (hfinite 0)
    (fun i _ => ha i.zero_le) hS
  have hright := schwarzChristoffelBoundary_image_Ici_eq_ray_prevertex a e z₀ (Fin.last n)
    (hfinite (Fin.last n)) (fun i _ => ha i.le_last) hS
  rw [← image_univ, hcover, image_union, image_union, image_iUnion, hleft, hright]
  simp_rw [hbounded]

end TauCeti
