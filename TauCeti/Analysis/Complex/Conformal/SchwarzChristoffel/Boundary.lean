/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ExtendFrom
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Edge
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Vertex

/-!
# Boundary values of the Schwarz--Christoffel map

The Schwarz--Christoffel primitive has two kinds of boundary point on the real axis.  Away from
the prevertices it continues holomorphically across a neighbourhood, while at a prevertex it still
has a finite limit when the total exponent there is greater than `-1`.  This file packages both
cases in a single boundary map.

The canonical value `schwarzChristoffelBoundary a e z₀ x` is Mathlib's `extendFrom` extension of
the primitive from the upper half-plane.  That extension is a genuine limit of the primitive
wherever such a limit exists, which is the case whenever the total exponent at `x` is greater
than `-1`; this includes every point which is not a prevertex.  On a prevertex whose total
exponent is greater than `-1` it agrees with `schwarzChristoffelVertex`, and on an interval free
of nonzero prevertices it is continuous,
injective, and has the explicit straight-edge increment formula from the boundary continuation.
Thus the boundary map is the common object in which the vertices and the open edges of the
eventual polygon meet.

## Main definitions

* `TauCeti.schwarzChristoffelBoundary` -- the boundary value of the Schwarz--Christoffel
  primitive at a real point.

## Main results

* `TauCeti.tendsto_schwarzChristoffelPrimitive_boundary` -- the primitive tends to the boundary
  value wherever the total exponent is greater than `-1`.
* `TauCeti.schwarzChristoffelBoundary_apply_prevertex` -- at a prevertex whose total exponent is
  greater than `-1`, the boundary value is the previously constructed Schwarz--Christoffel
  vertex.
* `TauCeti.schwarzChristoffelBoundary_change_base` -- changing the normalization point of the
  primitive subtracts a constant from the boundary map.
* `TauCeti.schwarzChristoffelBoundary_sub_eq` -- an increment of the boundary map along an open
  edge is a real integral times the fixed edge direction.
* `TauCeti.schwarzChristoffelBoundary_injOn` and
  `TauCeti.collinear_schwarzChristoffelBoundary_image` -- an open edge is embedded in a line.
* `TauCeti.schwarzChristoffelBoundary_image_Icc_eq_closure_image_Ioo` -- the closed boundary arc
  is the closure of its open edge.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The **boundary value of the Schwarz--Christoffel map** at a real point: the value at that
point of Mathlib's `extendFrom` extension of the normalized primitive from the upper half-plane.
The extension is total, so this is a limit of the primitive only where such a limit exists; that
happens whenever the total exponent at the point is greater than `-1`, by
`tendsto_schwarzChristoffelPrimitive_boundary`, and the value is unspecified elsewhere. -/
def schwarzChristoffelBoundary (a e : ι → ℝ) (z₀ : UpperHalfPlane) (x : ℝ) : ℂ :=
  extendFrom upperHalfPlaneSet (schwarzChristoffelPrimitive a e z₀) (x : ℂ)

/-- The Schwarz--Christoffel boundary map is Mathlib's canonical extension-by-limits of the
primitive from the upper half-plane, restricted to the real axis. -/
theorem schwarzChristoffelBoundary_def (a e : ι → ℝ) (z₀ : UpperHalfPlane) (x : ℝ) :
    schwarzChristoffelBoundary a e z₀ x =
      extendFrom upperHalfPlaneSet (schwarzChristoffelPrimitive a e z₀) (x : ℂ) := by
  rfl

/-- A limit of the Schwarz--Christoffel primitive from the upper half-plane is its canonical
boundary value. -/
theorem schwarzChristoffelBoundary_eq_of_tendsto (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (x : ℝ) {v : ℂ} (h : Tendsto (schwarzChristoffelPrimitive a e z₀)
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 v)) :
    schwarzChristoffelBoundary a e z₀ x = v := by
  rw [schwarzChristoffelBoundary]
  exact extendFrom_eq (by rw [Complex.closure_setOfPred_lt_im]; simp) h

/-- At a prevertex whose total exponent is greater than `-1`, the canonical
Schwarz--Christoffel boundary value is the Schwarz--Christoffel vertex. -/
@[simp]
theorem schwarzChristoffelBoundary_apply_prevertex (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (j : ι) (he : -1 < ∑ i with a i = a j, e i) :
    schwarzChristoffelBoundary a e z₀ (a j) = schwarzChristoffelVertex a e z₀ j := by
  exact schwarzChristoffelBoundary_eq_of_tendsto a e z₀ (a j)
    (tendsto_schwarzChristoffelPrimitive a e z₀ j he)

private theorem exists_tendsto_schwarzChristoffelPrimitive_boundary (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (x : ℝ) (he : -1 < ∑ i with a i = x, e i) :
    ∃ v, Tendsto (schwarzChristoffelPrimitive a e z₀)
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 v) := by
  classical
  by_cases hx : x ∈ Set.range a
  · obtain ⟨j, hj⟩ := hx
    subst x
    exact ⟨_, tendsto_schwarzChristoffelPrimitive a e z₀ j he⟩
  · have hopen : IsOpen ((Set.range a)ᶜ : Set ℝ) :=
      Set.Finite.isClosed (Set.finite_range a) |>.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
    have hxIoo : x ∈ Ioo (x - ε) (x + ε) := by constructor <;> linarith
    have ha : ∀ i, e i ≠ 0 → a i ∉ Ioo (x - ε) (x + ε) := by
      intro i _ hi
      have hai : a i ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hi.1, hi.2]
      exact (hball hai) ⟨i, rfl⟩
    obtain ⟨L, hL, -, -⟩ :=
      exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀ ha
    exact ⟨L x, hL x hxIoo⟩

/-- The Schwarz--Christoffel primitive tends to its canonical boundary value at every real point
where the total exponent is greater than `-1`.  At a prevertex this is the integrable-singularity
estimate; away from all prevertices the integrand continues holomorphically across a real
neighbourhood. -/
theorem tendsto_schwarzChristoffelPrimitive_boundary (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (x : ℝ) (he : -1 < ∑ i with a i = x, e i) :
    Tendsto (schwarzChristoffelPrimitive a e z₀)
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (schwarzChristoffelBoundary a e z₀ x)) := by
  rw [schwarzChristoffelBoundary]
  exact tendsto_extendFrom (exists_tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x he)

/-- Changing the base point of the normalized primitive subtracts, from the canonical
Schwarz--Christoffel boundary map, the value of the primitive at the old base point.  This is the
boundary counterpart of `schwarzChristoffelPrimitive_change_base`, and holds wherever the total
exponent is greater than `-1`. -/
theorem schwarzChristoffelBoundary_change_base (a e : ι → ℝ) (b c : UpperHalfPlane) (x : ℝ)
    (he : -1 < ∑ i with a i = x, e i) :
    schwarzChristoffelBoundary a e b x =
      schwarzChristoffelBoundary a e c x - schwarzChristoffelPrimitive a e c b := by
  refine schwarzChristoffelBoundary_eq_of_tendsto a e b x (Tendsto.congr' ?_
    ((tendsto_schwarzChristoffelPrimitive_boundary a e c x he).sub tendsto_const_nhds))
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (schwarzChristoffelPrimitive_change_base a e b c hz).symm

/-- The canonical Schwarz--Christoffel boundary map is continuous on any set of real points at
which the total exponent is greater than `-1`.  This simultaneously gives continuity along open
edges and attachment of those edges to every integrable prevertex. -/
theorem continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {s : Set ℝ} (he : ∀ x ∈ s, -1 < ∑ i with a i = x, e i) :
    ContinuousOn (schwarzChristoffelBoundary a e z₀) s := by
  let F : ℂ → ℂ := schwarzChristoffelPrimitive a e z₀
  have hcont : ContinuousOn (extendFrom upperHalfPlaneSet F) (Complex.ofReal '' s) := by
    apply continuousOn_extendFrom
    · intro z hz
      rw [Complex.closure_setOfPred_lt_im]
      obtain ⟨x, -, rfl⟩ := hz
      simp
    · rintro z ⟨x, hx, rfl⟩
      exact exists_tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (he x hx)
  exact hcont.comp Complex.continuous_ofReal.continuousOn fun x hx => ⟨x, hx, rfl⟩

/-- On a real interval free of prevertices with nonzero exponent, the canonical boundary map is
continuous. -/
theorem continuousOn_schwarzChristoffelBoundary (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) :
    ContinuousOn (schwarzChristoffelBoundary a e z₀) (Ioo p q) := by
  obtain ⟨L, hL, hLcont, -⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀ ha
  refine hLcont.congr fun x hx => ?_
  exact schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx)

/-- Along a real interval free of prevertices with nonzero exponent, the increment of the
canonical Schwarz--Christoffel boundary map between two points is the real integral of
`∏ i, |t - a i| ^ e i` between them, times the fixed unimodular direction with argument
`schwarzChristoffelEdgeAngle a e p`. -/
theorem schwarzChristoffelBoundary_sub_eq (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) {x y : ℝ}
    (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) :
    schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y =
      ((∫ t in y..x, ∏ i, |t - a i| ^ e i : ℝ) : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
  obtain ⟨L, hL, -, hsub⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀ ha
  rw [schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx),
    schwarzChristoffelBoundary_eq_of_tendsto a e z₀ y (hL y hy)]
  exact hsub x hx y hy

/-- The canonical Schwarz--Christoffel boundary map is injective on every real interval free of
prevertices with nonzero exponent. -/
theorem schwarzChristoffelBoundary_injOn (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Ioo p q) := by
  obtain ⟨L, hL, -, hLinj, -⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear a e z₀ ha
  intro x hx y hy hxy
  apply hLinj hx hy
  rwa [schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx),
    schwarzChristoffelBoundary_eq_of_tendsto a e z₀ y (hL y hy)] at hxy

/-- The image of a prevertex-free real interval under the canonical Schwarz--Christoffel boundary
map is collinear. -/
theorem collinear_schwarzChristoffelBoundary_image (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) :
    Collinear ℝ (schwarzChristoffelBoundary a e z₀ '' Ioo p q) := by
  obtain ⟨L, hL, -, -, hLcol⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear a e z₀ ha
  convert hLcol using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx)).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx)⟩

/-- Between two real endpoints whose total exponents are greater than `-1`, with no prevertex of
nonzero exponent strictly between them, the canonical Schwarz--Christoffel boundary map is
continuous on the closed interval.  When the endpoints are prevertices, this says that the open
straight edge supplied by `schwarzChristoffelBoundary_sub_eq` attaches continuously to its two
vertices. -/
theorem continuousOn_schwarzChristoffelBoundary_Icc (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    ContinuousOn (schwarzChristoffelBoundary a e z₀) (Icc p q) := by
  classical
  apply continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hpx
  · exact hp
  rcases eq_or_lt_of_le hx.2 with rfl | hxq
  · exact hq
  have hzero : ∑ i with a i = x, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hei
    exact ha i hei ⟨hi ▸ hpx, hi ▸ hxq⟩
  rw [hzero]
  norm_num

/-- The closed boundary arc between two real endpoints whose total exponents are greater than
`-1`, with no prevertex of nonzero exponent strictly between them, is exactly the closure of its
open straight edge.  When the endpoints are prevertices, this places both endpoint vertices --
rewriting with `schwarzChristoffelBoundary_apply_prevertex` -- in the closure of that edge, which
is the local gluing statement needed to assemble the Schwarz--Christoffel polygon. -/
theorem schwarzChristoffelBoundary_image_Icc_eq_closure_image_Ioo (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (hpq : p < q)
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelBoundary a e z₀ '' Icc p q =
      closure (schwarzChristoffelBoundary a e z₀ '' Ioo p q) := by
  rw [← closure_Ioo hpq.ne]
  refine image_closure_of_isCompact ?_ ?_ <;> rw [closure_Ioo hpq.ne]
  · exact isCompact_Icc
  · exact continuousOn_schwarzChristoffelBoundary_Icc a e z₀ ha hp hq

end TauCeti
