/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Polynomial hulls and polynomially convex sets in `ℂⁿ`

The *polynomial hull* of a set `K ⊆ ℂⁿ` is the set of points `z` at which every polynomial is
bounded in modulus by any bound it satisfies on `K`; for compact `K` this is the set of `z` with
`|p(z)| ≤ max_K |p|` for every polynomial `p`. A set is *polynomially convex* if it contains its
polynomial hull. Polynomially convex compact sets are the natural domains of polynomial
approximation in several complex variables (the Oka–Weil theorem), and the interiors of their
polynomial polyhedron neighbourhoods form cofinal systems of Stein neighbourhoods, along which
germs of holomorphic functions on compact sets are studied.

Points are modelled as functions `ι → ℂ` for a finite index type `ι`, polynomials as
`MvPolynomial ι ℂ` and evaluation as `MvPolynomial.eval`; the norm on `ι → ℂ` is the sup norm, so
its closed balls are closed polydiscs.

The two main results are the following.

* Every compact subset of the real locus `ℝⁿ ⊆ ℂⁿ` is polynomially convex. For `z` outside such a
  set `K`, the polynomial `p(w) = 1 - ε ∑ᵢ (wᵢ - Re zᵢ)²` is real on `K` with values in `(0, 1]`
  for small `ε > 0`, while `p(z) = 1 + ε ∑ᵢ (Im zᵢ)²`; one of the two inequalities
  `|p| ≤ 1 ≤ |p(z)|` is strict at every point of `K` because `z ∉ K`, and compactness makes the
  separation uniform.
* A compact polynomially convex set `K` has arbitrarily small polynomially convex compact
  neighbourhoods of the form `P = closedBall 0 R ∩ ⋂ᵢ {|pᵢ| ≤ 1}` for finitely many polynomials
  `pᵢ`, with `K` contained in the open set `ball 0 R ∩ ⋂ᵢ {|pᵢ| < 1} ⊆ P`. The points of the
  compact set `closedBall 0 R \ U` are separated from `K` by polynomials, and finitely many of
  these separators suffice.

## Main declarations

* `TauCeti.polynomialHull K`: the polynomial hull of `K`; it contains `K`
  (`TauCeti.subset_polynomialHull`), is closed (`TauCeti.isClosed_polynomialHull`) and is
  idempotent (`TauCeti.polynomialHull_polynomialHull`).
* `TauCeti.IsPolynomiallyConvex K`: `K` contains its polynomial hull. Polynomial convexity is
  preserved by arbitrary intersections (`TauCeti.isPolynomiallyConvex_iInter`) and holds for the
  sublevel sets `{|p| ≤ c}` (`TauCeti.isPolynomiallyConvex_setOf_norm_eval_le`) and for closed
  balls (`TauCeti.isPolynomiallyConvex_closedBall`).
* `TauCeti.polynomialPolyhedron R s`: the polynomial polyhedron
  `closedBall 0 R ∩ ⋂_{p ∈ s} {|p| ≤ 1}`; it is compact
  (`TauCeti.isCompact_polynomialPolyhedron`) and polynomially convex
  (`TauCeti.isPolynomiallyConvex_polynomialPolyhedron`), and its interior contains
  `ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}`
  (`TauCeti.ball_inter_biInter_subset_interior_polynomialPolyhedron`).

## Main results

* `TauCeti.exists_norm_eval_lt_one_lt_of_notMem_polynomialHull`: a point outside the hull of `K`
  is separated from `K` by a polynomial of modulus `< 1` on `K` and `> 1` at the point.
* `TauCeti.isPolynomiallyConvex_iff_forall_notMem_exists_norm_eval_lt_one_lt`: `K` is
  polynomially convex if and only if every point outside `K` is separated from `K` in this way.
* `IsCompact.notMem_polynomialHull_of_forall_norm_eval_lt`: if `|p| < |p(z)|` at every point of a
  compact `K`, then `z` is not in the hull of `K`.
* `IsCompact.isPolynomiallyConvex_of_forall_im_eq_zero`: compact subsets of `ℝⁿ` are polynomially
  convex.
* `TauCeti.IsPolynomiallyConvex.exists_polynomialPolyhedron_subset`: the polynomial polyhedron
  neighbourhoods of a compact polynomially convex set, and
  `TauCeti.IsPolynomiallyConvex.exists_subset_interior_polynomialPolyhedron`: such a set lies in
  the interior of a polynomial polyhedron inside any given open neighbourhood.

## References

* L. Hörmander, *An introduction to complex analysis in several variables*, 3rd ed.,
  North-Holland, 1990, §2.7.
* E. L. Stout, *Polynomial convexity*, Progress in Mathematics 261, Birkhäuser, 2007, Chapter 1.
-/

public section

open MvPolynomial Metric Set

namespace TauCeti

variable {ι : Type*}

/-- The polynomial hull of a set `K ⊆ ℂⁿ`: the points `z` such that `|p(z)| ≤ c` for every
polynomial `p` and every bound `c` with `|p| ≤ c` on `K`. For compact `K` these are the points
with `|p(z)| ≤ max_K |p|` for every polynomial `p`. -/
def polynomialHull (K : Set (ι → ℂ)) : Set (ι → ℂ) :=
  {z | ∀ (p : MvPolynomial ι ℂ) (c : ℝ), (∀ w ∈ K, ‖eval w p‖ ≤ c) → ‖eval z p‖ ≤ c}

/-- A set `K ⊆ ℂⁿ` is polynomially convex if it contains its polynomial hull. For compact `K`
this is the standard notion; for unbounded `K` it is stricter than the convention that the hull
of every compact subset of `K` stays in `K` (for instance, `ℝⁿ` with `n ≥ 1` is not polynomially
convex in this sense, since only constant polynomials are bounded on it). -/
def IsPolynomiallyConvex (K : Set (ι → ℂ)) : Prop :=
  polynomialHull K ⊆ K

variable {K L : Set (ι → ℂ)} {z : ι → ℂ}

theorem isPolynomiallyConvex_iff : IsPolynomiallyConvex K ↔ polynomialHull K ⊆ K :=
  Iff.rfl

theorem mem_polynomialHull_iff :
    z ∈ polynomialHull K ↔
      ∀ (p : MvPolynomial ι ℂ) (c : ℝ), (∀ w ∈ K, ‖eval w p‖ ≤ c) → ‖eval z p‖ ≤ c :=
  Iff.rfl

theorem subset_polynomialHull (K : Set (ι → ℂ)) : K ⊆ polynomialHull K :=
  fun _ hz _ _ hc ↦ hc _ hz

theorem polynomialHull_mono (h : K ⊆ L) : polynomialHull K ⊆ polynomialHull L :=
  fun _ hz p c hc ↦ hz p c fun w hw ↦ hc w (h hw)

@[simp]
theorem polynomialHull_empty : polynomialHull (∅ : Set (ι → ℂ)) = ∅ :=
  eq_empty_of_forall_notMem fun z hz ↦ (hz 1 0 (by simp)).not_gt (by simp)

/-- Taking the polynomial hull is idempotent. -/
@[simp]
theorem polynomialHull_polynomialHull (K : Set (ι → ℂ)) :
    polynomialHull (polynomialHull K) = polynomialHull K :=
  (subset_polynomialHull _).antisymm' fun _ hz p c hc ↦ hz p c fun _ hw ↦ hw p c hc

/-- The polynomial hull of any set is closed. -/
theorem isClosed_polynomialHull (K : Set (ι → ℂ)) : IsClosed (polynomialHull K) := by
  have : polynomialHull K = ⋂ (p : MvPolynomial ι ℂ) (c : ℝ) (_ : ∀ w ∈ K, ‖eval w p‖ ≤ c),
      {z | ‖eval z p‖ ≤ c} := by
    ext z
    simp [mem_polynomialHull_iff]
  rw [this]
  exact isClosed_iInter fun p ↦ isClosed_iInter fun c ↦ isClosed_iInter fun _ ↦
    isClosed_le (continuous_eval p).norm continuous_const

/-- A point outside the polynomial hull of `K` is separated from `K` by a polynomial: there is
`p` with `|p| < 1` on `K` and `|p(z)| > 1`. -/
theorem exists_norm_eval_lt_one_lt_of_notMem_polynomialHull (hz : z ∉ polynomialHull K) :
    ∃ p : MvPolynomial ι ℂ, (∀ w ∈ K, ‖eval w p‖ < 1) ∧ 1 < ‖eval z p‖ := by
  simp only [mem_polynomialHull_iff, not_forall, not_le, exists_prop] at hz
  obtain ⟨p, c, hpK, hcz⟩ := hz
  set s := ‖eval z p‖
  rcases (norm_nonneg (eval z p)).eq_or_lt with hs | hs
  · -- `|p(z)| = 0 > c`, so `K` is empty and a constant polynomial separates.
    have hK : ∀ w ∈ K, False := fun w hw ↦
      ((norm_nonneg _).trans (hpK w hw)).not_gt (hs ▸ hcz)
    exact ⟨C 2, fun w hw ↦ (hK w hw).elim, by norm_num⟩
  -- Rescale `p` by `2 / (a + s)`, where `a = max c (s / 2)` satisfies `0 < a < s`.
  set a := max c (s / 2)
  have ha : 0 < a := (half_pos hs).trans_le (le_max_right _ _)
  have has : a < s := max_lt hcz (half_lt_self hs)
  have hr : 0 < 2 / (a + s) := by positivity
  have hnorm (w : ι → ℂ) :
      ‖eval w (C ((2 / (a + s) : ℝ) : ℂ) * p)‖ = 2 * ‖eval w p‖ / (a + s) := by
    rw [map_mul, eval_C, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_mul_eq_mul_div]
  refine ⟨C ((2 / (a + s) : ℝ) : ℂ) * p, fun w hw ↦ ?_, ?_⟩
  · rw [hnorm, div_lt_one (by positivity)]
    linarith [(hpK w hw).trans (le_max_left c (s / 2))]
  · rw [hnorm, one_lt_div (by positivity)]
    linarith

/-- If a polynomial is strictly smaller in modulus at every point of a compact set `K` than at `z`,
then `z` is not in the polynomial hull of `K`. -/
theorem _root_.IsCompact.notMem_polynomialHull_of_forall_norm_eval_lt (hK : IsCompact K)
    {p : MvPolynomial ι ℂ} (hp : ∀ w ∈ K, ‖eval w p‖ < ‖eval z p‖) :
    z ∉ polynomialHull K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hne (continuous_eval p).norm.continuousOn
  exact fun hz ↦ (hz p _ fun w hw ↦ hmax hw).not_gt (hp w₀ hw₀)

theorem isPolynomiallyConvex_iff_polynomialHull_eq :
    IsPolynomiallyConvex K ↔ polynomialHull K = K :=
  ⟨fun h ↦ h.antisymm (subset_polynomialHull K), fun h ↦ h.subset⟩

theorem isPolynomiallyConvex_polynomialHull (K : Set (ι → ℂ)) :
    IsPolynomiallyConvex (polynomialHull K) :=
  (polynomialHull_polynomialHull K).subset

/-- A point outside a polynomially convex set `K` is separated from `K` by a polynomial of
modulus `< 1` on `K` and `> 1` at the point. -/
theorem IsPolynomiallyConvex.exists_norm_eval_lt_one_lt (hK : IsPolynomiallyConvex K)
    (hz : z ∉ K) : ∃ p : MvPolynomial ι ℂ, (∀ w ∈ K, ‖eval w p‖ < 1) ∧ 1 < ‖eval z p‖ :=
  exists_norm_eval_lt_one_lt_of_notMem_polynomialHull fun h ↦
    hz (isPolynomiallyConvex_iff.1 hK h)

/-- A set `K` is polynomially convex if and only if every point outside `K` is separated from `K`
by a polynomial of modulus `< 1` on `K` and `> 1` at the point. -/
theorem isPolynomiallyConvex_iff_forall_notMem_exists_norm_eval_lt_one_lt :
    IsPolynomiallyConvex K ↔
      ∀ z ∉ K, ∃ p : MvPolynomial ι ℂ, (∀ w ∈ K, ‖eval w p‖ < 1) ∧ 1 < ‖eval z p‖ := by
  refine ⟨fun hK _ hz ↦ hK.exists_norm_eval_lt_one_lt hz, fun h ↦ ?_⟩
  refine isPolynomiallyConvex_iff.2 fun z hz ↦ by_contra fun hzK ↦ ?_
  obtain ⟨p, hpK, hpz⟩ := h z hzK
  exact (mem_polynomialHull_iff.1 hz p 1 fun w hw ↦ (hpK w hw).le).not_gt hpz

theorem isPolynomiallyConvex_empty : IsPolynomiallyConvex (∅ : Set (ι → ℂ)) := by
  simp [isPolynomiallyConvex_iff]

/-- An intersection of polynomially convex sets is polynomially convex. -/
theorem isPolynomiallyConvex_iInter {κ : Sort*} {K : κ → Set (ι → ℂ)}
    (hK : ∀ k, IsPolynomiallyConvex (K k)) : IsPolynomiallyConvex (⋂ k, K k) :=
  isPolynomiallyConvex_iff.2 fun _ hz ↦ mem_iInter.2 fun k ↦
    isPolynomiallyConvex_iff.1 (hK k) (polynomialHull_mono (iInter_subset K k) hz)

/-- The intersection of two polynomially convex sets is polynomially convex. -/
theorem IsPolynomiallyConvex.inter (hK : IsPolynomiallyConvex K) (hL : IsPolynomiallyConvex L) :
    IsPolynomiallyConvex (K ∩ L) :=
  isPolynomiallyConvex_iff.2 fun _ hz ↦
    ⟨isPolynomiallyConvex_iff.1 hK (polynomialHull_mono inter_subset_left hz),
      isPolynomiallyConvex_iff.1 hL (polynomialHull_mono inter_subset_right hz)⟩

/-- A sublevel set `{w | |p(w)| ≤ c}` of the modulus of a polynomial is polynomially convex. -/
theorem isPolynomiallyConvex_setOf_norm_eval_le (p : MvPolynomial ι ℂ) (c : ℝ) :
    IsPolynomiallyConvex {w | ‖eval w p‖ ≤ c} :=
  isPolynomiallyConvex_iff.2 fun _ hz ↦ hz p c fun _ hw ↦ hw

/-- Closed balls of `ℂⁿ` for the sup norm, that is, closed polydiscs, are polynomially convex. -/
theorem isPolynomiallyConvex_closedBall [Fintype ι] (x : ι → ℂ) (r : ℝ) :
    IsPolynomiallyConvex (closedBall x r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [closedBall_eq_empty.2 hr]
    exact isPolynomiallyConvex_empty
  have : closedBall x r = ⋂ i, {w | ‖eval w (X i - C (x i))‖ ≤ r} := by
    ext w
    simp [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hr]
  rw [this]
  exact isPolynomiallyConvex_iInter fun i ↦ isPolynomiallyConvex_setOf_norm_eval_le _ r

/-- The value of `∑ᵢ (Xᵢ - Re zᵢ)²` at a real point `w` is the real number
`∑ᵢ (Re wᵢ - Re zᵢ)²`. -/
private theorem eval_sum_sq_sub_re_of_forall_im_eq_zero [Fintype ι] (z : ι → ℂ) {w : ι → ℂ}
    (hw : ∀ i, (w i).im = 0) :
    eval w (∑ i, (X i - C ((z i).re : ℂ)) ^ 2) = ((∑ i, ((w i).re - (z i).re) ^ 2 : ℝ) : ℂ) := by
  simp only [map_sum, map_pow, map_sub, eval_X, eval_C, Complex.ofReal_sum, Complex.ofReal_pow,
    Complex.ofReal_sub]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Complex.re_add_im (w i), hw i]
  simp

/-- The value of `∑ᵢ (Xᵢ - Re zᵢ)²` at `z` itself is the real number `-∑ᵢ (Im zᵢ)²`. -/
private theorem eval_sum_sq_sub_re_self [Fintype ι] (z : ι → ℂ) :
    eval z (∑ i, (X i - C ((z i).re : ℂ)) ^ 2) = ((-∑ i, (z i).im ^ 2 : ℝ) : ℂ) := by
  simp only [map_sum, map_pow, map_sub, eval_X, eval_C, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_pow, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply Complex.ext <;> simp [sq]

/-- Every compact subset of the real locus `ℝⁿ ⊆ ℂⁿ` is polynomially convex. -/
theorem _root_.IsCompact.isPolynomiallyConvex_of_forall_im_eq_zero [Finite ι]
    (hK : IsCompact K) (hreal : ∀ w ∈ K, ∀ i, (w i).im = 0) : IsPolynomiallyConvex K := by
  have := Fintype.ofFinite ι
  refine isPolynomiallyConvex_iff.2 fun z hz ↦ ?_
  by_contra hzK
  -- `f w = ∑ᵢ (Re wᵢ - Re zᵢ)²` is bounded on `K`; choose `ε > 0` with `ε f < 1` on `K`.
  set f : (ι → ℂ) → ℝ := fun w ↦ ∑ i, ((w i).re - (z i).re) ^ 2
  have hf : Continuous f := by fun_prop
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
  set ε : ℝ := (|M| + 1)⁻¹
  have hε : 0 < ε := by positivity
  have hεf : ∀ w ∈ K, ε * f w < 1 := fun w hw ↦ by
    have : f w ≤ |M| := (hM (mem_image_of_mem f hw)).trans (le_abs_self M)
    calc ε * f w ≤ ε * |M| := mul_le_mul_of_nonneg_left this hε.le
      _ < ε * (|M| + 1) := by gcongr; linarith
      _ = 1 := inv_mul_cancel₀ (by positivity)
  set g : ℝ := ∑ i, (z i).im ^ 2
  have hg : 0 ≤ g := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  set p : MvPolynomial ι ℂ := 1 - C (ε : ℂ) * ∑ i, (X i - C ((z i).re : ℂ)) ^ 2
  refine hK.notMem_polynomialHull_of_forall_norm_eval_lt (p := p) (fun w hw ↦ ?_) hz
  have hfw : 0 ≤ f w := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hpz : eval z p = ((1 + ε * g : ℝ) : ℂ) := by
    simp only [p, map_sub, map_one, map_mul, eval_C, eval_sum_sq_sub_re_self]
    push_cast [g]
    ring
  have hpw : eval w p = ((1 - ε * f w : ℝ) : ℂ) := by
    simp only [p, map_sub, map_one, map_mul, eval_C,
      eval_sum_sq_sub_re_of_forall_im_eq_zero z (hreal w hw)]
    push_cast [f]
    ring
  rw [hpz, hpw, Complex.norm_of_nonneg (by linarith [hεf w hw]),
    Complex.norm_of_nonneg (by positivity)]
  -- `1 - ε f w ≤ 1 ≤ 1 + ε g`, and equality throughout would force `w = z`.
  by_contra hle
  have hfw0 : f w = 0 := by nlinarith
  have hg0 : g = 0 := by nlinarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _] at hfw0 hg0
  refine hzK ((funext fun i ↦ Complex.ext ?_ ?_ : w = z) ▸ hw)
  · simpa [sub_eq_zero] using hfw0 i (Finset.mem_univ i)
  · simpa [hreal w hw i, eq_comm] using hg0 i (Finset.mem_univ i)

section polynomialPolyhedron

variable [Fintype ι]

/-- The polynomial polyhedron `closedBall 0 R ∩ ⋂_{p ∈ s} {|p| ≤ 1}` cut out of the closed
polydisc of radius `R` by a finite set `s` of polynomials. -/
noncomputable def polynomialPolyhedron (R : ℝ) (s : Finset (MvPolynomial ι ℂ)) : Set (ι → ℂ) :=
  closedBall 0 R ∩ ⋂ p ∈ s, {w | ‖eval w p‖ ≤ 1}

variable {R : ℝ} {s : Finset (MvPolynomial ι ℂ)} {w : ι → ℂ}

@[simp]
theorem mem_polynomialPolyhedron_iff :
    w ∈ polynomialPolyhedron R s ↔ ‖w‖ ≤ R ∧ ∀ p ∈ s, ‖eval w p‖ ≤ 1 := by
  simp [polynomialPolyhedron]

theorem isClosed_polynomialPolyhedron (R : ℝ) (s : Finset (MvPolynomial ι ℂ)) :
    IsClosed (polynomialPolyhedron R s) :=
  isClosed_closedBall.inter <| isClosed_biInter fun p _ ↦
    isClosed_le (continuous_eval p).norm continuous_const

theorem isCompact_polynomialPolyhedron (R : ℝ) (s : Finset (MvPolynomial ι ℂ)) :
    IsCompact (polynomialPolyhedron R s) :=
  (isCompact_closedBall 0 R).inter_right <| isClosed_biInter fun p _ ↦
    isClosed_le (continuous_eval p).norm continuous_const

/-- The open set `ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}` lies in the interior of the polynomial
polyhedron `polynomialPolyhedron R s`. -/
theorem ball_inter_biInter_subset_interior_polynomialPolyhedron (R : ℝ)
    (s : Finset (MvPolynomial ι ℂ)) :
    ball 0 R ∩ ⋂ p ∈ s, {w | ‖eval w p‖ < 1} ⊆ interior (polynomialPolyhedron R s) :=
  interior_maximal
    (inter_subset_inter ball_subset_closedBall <| biInter_mono subset_rfl fun _ _ ↦
      ofPred_subset_ofPred.2 fun _ hw ↦ hw.le)
    (isOpen_ball.inter <| isOpen_biInter_finset fun p _ ↦
      isOpen_lt (continuous_eval p).norm continuous_const)

/-- Polynomial polyhedra are polynomially convex. -/
theorem isPolynomiallyConvex_polynomialPolyhedron (R : ℝ) (s : Finset (MvPolynomial ι ℂ)) :
    IsPolynomiallyConvex (polynomialPolyhedron R s) :=
  (isPolynomiallyConvex_closedBall 0 R).inter <| isPolynomiallyConvex_iInter fun p ↦
    isPolynomiallyConvex_iInter fun _ ↦ isPolynomiallyConvex_setOf_norm_eval_le p 1

end polynomialPolyhedron

/-- **Polynomial polyhedron neighbourhoods.** A compact polynomially convex set `K ⊆ ℂⁿ` with an
open neighbourhood `U` has a polynomial polyhedron neighbourhood
`P = closedBall 0 R ∩ ⋂_{p ∈ s} {|p| ≤ 1}` inside `U`, for a radius `R > 0` and a finite set `s`
of polynomials, such that `K` lies in the open subset `ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}` of `P`.
The set `P` is compact (`TauCeti.isCompact_polynomialPolyhedron`) and polynomially convex
(`TauCeti.isPolynomiallyConvex_polynomialPolyhedron`). -/
theorem IsPolynomiallyConvex.exists_polynomialPolyhedron_subset [Fintype ι]
    (hKc : IsPolynomiallyConvex K) (hK : IsCompact K) {U : Set (ι → ℂ)} (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (R : ℝ) (s : Finset (MvPolynomial ι ℂ)), 0 < R ∧
      K ⊆ ball 0 R ∩ ⋂ p ∈ s, {w | ‖eval w p‖ < 1} ∧ polynomialPolyhedron R s ⊆ U := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball 0
  set R := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  -- The points of the compact set `closedBall 0 R \ U` are separated from `K` by polynomials
  -- of modulus `< 1` on `K`; finitely many of these separators cover it.
  set S := {p : MvPolynomial ι ℂ // ∀ w ∈ K, ‖eval w p‖ < 1}
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ι → ℂ) R).diff hU |>.elim_finite_subcover
    (fun p : S ↦ {w | 1 < ‖eval w p.1‖})
    (fun p ↦ isOpen_lt continuous_const (continuous_eval p.1).norm)
    (fun ζ hζ ↦ by
      obtain ⟨p, hpK, hpζ⟩ := hKc.exists_norm_eval_lt_one_lt fun h ↦ hζ.2 (hKU h)
      exact mem_iUnion.2 ⟨⟨p, hpK⟩, hpζ⟩)
  refine ⟨R, t.map (Function.Embedding.subtype _), hR, fun w hw ↦ ⟨?_, ?_⟩, ?_⟩
  · exact ball_subset_ball (le_max_left _ _) (hR₀ hw)
  · simp only [Finset.mem_map, Function.Embedding.coe_subtype, mem_iInter]
    rintro _ ⟨p, -, rfl⟩
    exact p.2 w hw
  · rintro w ⟨hwR, hws⟩
    by_contra hwU
    obtain ⟨p, hpt, hpw⟩ := mem_iUnion₂.1 (ht ⟨hwR, hwU⟩)
    have hpw' := mem_iInter₂.1 hws p.1 (Finset.mem_map_of_mem _ hpt)
    simp only [mem_ofPred_eq] at hpw hpw'
    linarith

/-- A compact polynomially convex set `K ⊆ ℂⁿ` lies in the interior of a polynomial polyhedron
contained in any given open neighbourhood `U` of `K`. -/
theorem IsPolynomiallyConvex.exists_subset_interior_polynomialPolyhedron [Fintype ι]
    (hKc : IsPolynomiallyConvex K) (hK : IsCompact K) {U : Set (ι → ℂ)} (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (R : ℝ) (s : Finset (MvPolynomial ι ℂ)), 0 < R ∧
      K ⊆ interior (polynomialPolyhedron R s) ∧ polynomialPolyhedron R s ⊆ U := by
  obtain ⟨R, s, hR, hKs, hsU⟩ := hKc.exists_polynomialPolyhedron_subset hK hU hKU
  exact ⟨R, s, hR, hKs.trans (ball_inter_biInter_subset_interior_polynomialPolyhedron R s), hsU⟩

end TauCeti
