/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.GlobalTurning
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ShortTurn
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge

/-!
# Separation of bounded Schwarz--Christoffel sides

Two nonadjacent bounded sides of a Schwarz--Christoffel polygon can be separated by following
either of the two boundary arcs between them.  `Polygon.ShortTurn` treats the direct arc when its
directions turn through less than `π`.  This file treats the complementary arc through the vertex
at infinity when the direct turn is at least `π`.  The closing condition makes its two unbounded
pieces point in the same direction, and the complementary turn is at most `π`.

Combining the two cases shows that every pair of nonadjacent bounded sides is disjoint under the
classical convex-polygon hypotheses: strictly ordered prevertices, exponents in `(-1, 0)`, and
total exponent `-2`.  These lemmas supply the bounded-side part of the global
boundary-simplicity argument.

## Main results

* `TauCeti.im_exp_neg_mul_schwarzChristoffelVertex_sub_pos_of_long_turn` puts the chord along the
  complementary boundary arc strictly to one side of the later bounded edge.
* `TauCeti.disjoint_schwarzChristoffelPolygon_edgeSet_of_long_turn` separates nonadjacent bounded
  sides when their direct turn is at least `π`.
* `TauCeti.disjoint_schwarzChristoffelPolygon_bounded_edgeSet` separates every pair of
  nonadjacent bounded sides.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

private lemma exponent_sum_at_eq (a e : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (k : Fin (n + 1)) :
    ∑ l with a l = a k, e l = e k := by
  classical
  have hfilter : Finset.univ.filter (fun l ↦ a l = a k) = {k} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ha.injective.eq_iff
  rw [hfilter, Finset.sum_singleton]

/-- After rotating by `-θ`, the height of a bounded Schwarz--Christoffel side vector is its length
times the sine of its edge angle measured from `θ`. -/
theorem im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (θ : ℝ) (k : Fin n)
    (hfinite_left : -1 < ∑ l with a l = a k.castSucc, e l)
    (hfinite_right : -1 < ∑ l with a l = a k.succ, e l) :
    (Complex.exp (-θ * Complex.I) *
      (schwarzChristoffelVertex a e z₀ k.succ -
        schwarzChristoffelVertex a e z₀ k.castSucc)).im =
      ‖schwarzChristoffelVertex a e z₀ k.succ -
        schwarzChristoffelVertex a e z₀ k.castSucc‖ *
        Real.sin (schwarzChristoffelEdgeAngle a e (a k.castSucc) - θ) := by
  let d := ‖schwarzChristoffelVertex a e z₀ k.succ -
    schwarzChristoffelVertex a e z₀ k.castSucc‖
  let φ := schwarzChristoffelEdgeAngle a e (a k.castSucc)
  have hedge := schwarzChristoffelVertex_succ_sub_eq_norm_mul a e z₀ ha k
    hfinite_left hfinite_right
  have hexp : Complex.exp (-θ * Complex.I) *
      ((d : ℂ) * Complex.exp (φ * Complex.I)) =
      (d : ℂ) * Complex.exp (((φ - θ : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = (d : ℂ) * (Complex.exp (-θ * Complex.I) *
          Complex.exp (φ * Complex.I)) := by ring
      _ = (d : ℂ) * Complex.exp (-θ * Complex.I + φ * Complex.I) := by
        rw [Complex.exp_add]
      _ = _ := by
        congr 2
        push_cast
        ring
  conv_lhs => rw [hedge]
  -- Re-express the two opaque analytic values through the local names used in `hexp`.
  change (Complex.exp (-θ * Complex.I) *
    ((d : ℂ) * Complex.exp (φ * Complex.I))).im = _
  rw [hexp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im]

/-- If the direct turn from bounded side `i` to bounded side `j` is at least `π`, the chord from
the end of side `j` to the start of side `i`, following the complementary boundary arc through
infinity, lies strictly to the left of side `j`.

The index condition leaves at least one complete bounded side on the direct arc.  The exponent
conditions make all edge directions strictly ordered through one full turn, while the total
exponent `-2` identifies the two unbounded pieces as a single positive-direction closing side. -/
theorem im_exp_neg_mul_schwarzChristoffelVertex_sub_pos_of_long_turn
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2)
    (i j : Fin n) (hij : i.val + 1 < j.val)
    (hlong : schwarzChristoffelEdgeAngle a e (a i.castSucc) + Real.pi ≤
      schwarzChristoffelEdgeAngle a e (a j.castSucc)) :
    0 < (Complex.exp
        (-schwarzChristoffelEdgeAngle a e (a j.castSucc) * Complex.I) *
      (schwarzChristoffelVertex a e z₀ i.castSucc -
        schwarzChristoffelVertex a e z₀ j.succ)).im := by
  classical
  let θj := schwarzChristoffelEdgeAngle a e (a j.castSucc)
  let u := Complex.exp (-θj * Complex.I)
  let V : ℕ → ℂ := fun k ↦ if hk : k < n + 1 then
    schwarzChristoffelVertex a e z₀ ⟨k, hk⟩ else 0
  let Vinf := schwarzChristoffelVertexAtInfinity a e z₀
  have hangle := schwarzChristoffelEdgeAngle_comp_strictMono a e ha fun k ↦ (he k).2
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    rw [exponent_sum_at_eq a e ha]
    exact (he k).1
  have hsumlt : ∑ k, e k < -1 := by rw [hsum]; norm_num
  have hjlast : j.castSucc < Fin.last n := by
    apply Fin.mk_lt_mk.mpr
    exact j.isLt
  have hθjneg : θj < 0 := by
    have hlast := hangle hjlast
    -- Beta-reduce the ordered angle family before rewriting its value at the last prevertex.
    change schwarzChristoffelEdgeAngle a e (a j.castSucc) <
      schwarzChristoffelEdgeAngle a e (a (Fin.last n)) at hlast
    rw [schwarzChristoffelEdgeAngle_eq_zero_of_last_le a e ha.monotone le_rfl] at hlast
    exact hlast
  have hθilower := (schwarzChristoffelEdgeAngle_mem_Ioc a e
    (fun k ↦ (he k).2) hsum i.castSucc).1
  have hθjlower : -Real.pi < θj := by
    dsimp only [θj]
    linarith
  -- Both pieces incident to infinity point along the positive real axis when the total
  -- exponent is `-2`; their sum is the strictly positive part of the complementary chord.
  have hcloseDir :
      Vinf - schwarzChristoffelVertex a e z₀ (Fin.last n) =
        (‖Vinf - schwarzChristoffelVertex a e z₀ (Fin.last n)‖ : ℂ) := by
    have h := schwarzChristoffelVertexAtInfinity_sub_boundary_eq_norm_mul
      a e z₀ (hfinite (Fin.last n)) (fun k _ ↦ ha.monotone k.le_last) hsumlt
    rw [schwarzChristoffelBoundary_apply_prevertex a e z₀ (Fin.last n)
      (hfinite (Fin.last n))] at h
    have hzero := schwarzChristoffelEdgeAngle_eq_zero_of_last_le
      a e ha.monotone (c := a (Fin.last n)) le_rfl
    rw [hzero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h
    exact h
  have hfirstDir :
      schwarzChristoffelVertex a e z₀ 0 - Vinf =
        (‖schwarzChristoffelVertex a e z₀ 0 - Vinf‖ : ℂ) := by
    have h := schwarzChristoffelBoundary_sub_vertexAtInfinity_eq_norm_mul
      a e z₀ (hfinite 0) (fun k _ ↦ ha.monotone k.zero_le) hsumlt
    rw [schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)] at h
    have hexp : Complex.exp (((Real.pi * (-2 : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (-1) using 1
      push_cast
      ring_nf
    have harg : (Real.pi : ℂ) * ((-2 : ℝ) : ℂ) * Complex.I =
        (((Real.pi * (-2 : ℝ) : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hsum, harg, hexp, mul_one] at h
    exact h
  have hclose : 0 < (u *
      ((schwarzChristoffelVertex a e z₀ 0 - Vinf) +
        (Vinf - schwarzChristoffelVertex a e z₀ (Fin.last n)))).im := by
    rw [hfirstDir, hcloseDir, mul_add, Complex.add_im]
    have hrot (d : ℝ) :
        (u * (d : ℂ)).im = d * Real.sin (-θj) := by
      dsimp only [u]
      have hexp : -((θj : ℂ)) * Complex.I = ((-θj : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hexp, mul_comm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, Complex.exp_ofReal_mul_I_im]
    rw [hrot, hrot, ← add_mul]
    apply mul_pos
    · have hfirstNe := schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_ge
        a e z₀ (hfinite 0) (fun k _ ↦ ha.monotone k.zero_le) hsumlt
      rw [schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)] at hfirstNe
      have hlastNe := schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_le
        a e z₀ (hfinite (Fin.last n)) (fun k _ ↦ ha.monotone k.le_last) hsumlt
      rw [schwarzChristoffelBoundary_apply_prevertex a e z₀ (Fin.last n)
        (hfinite (Fin.last n))] at hlastNe
      exact add_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr hfirstNe))
        (norm_pos_iff.mpr (sub_ne_zero.mpr hlastNe.symm))
    · exact Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hθjneg) (by linarith)
  have hVzero : V 0 = schwarzChristoffelVertex a e z₀ 0 := by
    dsimp only [V]
    split
    · congr
    · omega
  have hVi : V i.val = schwarzChristoffelVertex a e z₀ i.castSucc := by
    dsimp only [V]
    split
    · congr
    · omega
  have hVj : V (j.val + 1) = schwarzChristoffelVertex a e z₀ j.succ := by
    dsimp only [V]
    split
    · congr
    · omega
  have hVlast : V n = schwarzChristoffelVertex a e z₀ (Fin.last n) := by
    dsimp only [V]
    split
    · congr
    · omega
  have hleftTel := Finset.sum_Ico_sub V (Nat.zero_le i.val)
  have hrightTel := Finset.sum_Ico_sub V (Nat.succ_le_iff.mpr j.isLt)
  rw [hVzero, hVi] at hleftTel
  rw [hVj, hVlast] at hrightTel
  -- The early bounded edges are read one full turn later, so their adjusted angles lie in
  -- `(0, π)` relative to side `j`.
  have hleft : 0 ≤ (u *
      (schwarzChristoffelVertex a e z₀ i.castSucc -
        schwarzChristoffelVertex a e z₀ 0)).im := by
    rw [← hleftTel, Finset.mul_sum]
    -- Use the bundled imaginary-part map so that it distributes over the telescoping sum.
    change 0 ≤ Complex.imCLM (∑ k ∈ Finset.Ico 0 i.val, u * (V (k + 1) - V k))
    rw [map_sum]
    apply Finset.sum_nonneg
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hkn : k < n := lt_of_lt_of_le hk.2 i.isLt.le
    let k' : Fin n := ⟨k, hkn⟩
    have hki : k' < i := Fin.mk_lt_mk.mpr hk.2
    have hkj : k'.castSucc < j.castSucc := by
      apply Fin.mk_lt_mk.mpr
      dsimp only [k']
      omega
    have hdiff := schwarzChristoffelEdgeAngle_sub_mem_Ioo_two_pi
      a e ha (fun l ↦ (he l).2) hsum hkj
    have hδ : schwarzChristoffelEdgeAngle a e (a k'.castSucc) - θj + 2 * Real.pi ∈
        Ioo (0 : ℝ) Real.pi := by
      constructor
      · dsimp only [θj]
        linarith [hdiff.2]
      · have hkiangle := hangle (Fin.castSucc_lt_castSucc_iff.mpr hki)
        dsimp only [θj]
        linarith
    have him := im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
      a e z₀ ha θj k' (hfinite k'.castSucc) (hfinite k'.succ)
    have hsin : 0 < Real.sin
        (schwarzChristoffelEdgeAngle a e (a k'.castSucc) - θj) := by
      rw [← Real.sin_add_two_pi]
      exact Real.sin_pos_of_pos_of_lt_pi hδ.1 hδ.2
    have hV : V (k + 1) - V k =
        schwarzChristoffelVertex a e z₀ k'.succ -
          schwarzChristoffelVertex a e z₀ k'.castSucc := by
      dsimp only [V]
      split <;> split
      · congr
      · omega
      · omega
      · omega
    simp only [Complex.imCLM_apply, hV]
    rw [him]
    exact mul_nonneg (norm_nonneg _) hsin.le
  -- The late bounded edges have their actual angles in `(θj, θj + π)`.
  have hright : 0 ≤ (u *
      (schwarzChristoffelVertex a e z₀ (Fin.last n) -
        schwarzChristoffelVertex a e z₀ j.succ)).im := by
    rw [← hrightTel, Finset.mul_sum]
    -- Use the bundled imaginary-part map so that it distributes over the telescoping sum.
    change 0 ≤ Complex.imCLM
      (∑ k ∈ Finset.Ico (j.val + 1) n, u * (V (k + 1) - V k))
    rw [map_sum]
    apply Finset.sum_nonneg
    intro k hk
    simp only [Finset.mem_Ico] at hk
    let k' : Fin n := ⟨k, hk.2⟩
    have hjk : j < k' := Fin.mk_lt_mk.mpr hk.1
    have hδ : schwarzChristoffelEdgeAngle a e (a k'.castSucc) - θj ∈
        Ioo (0 : ℝ) Real.pi := by
      constructor
      · exact sub_pos.mpr (hangle (Fin.castSucc_lt_castSucc_iff.mpr hjk))
      · have hkangle := (schwarzChristoffelEdgeAngle_mem_Ioc a e
          (fun l ↦ (he l).2) hsum k'.castSucc).2
        linarith
    have him := im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
      a e z₀ ha θj k' (hfinite k'.castSucc) (hfinite k'.succ)
    have hV : V (k + 1) - V k =
        schwarzChristoffelVertex a e z₀ k'.succ -
          schwarzChristoffelVertex a e z₀ k'.castSucc := by
      dsimp only [V]
      split <;> split
      · congr
      · omega
      · omega
      · omega
    simp only [Complex.imCLM_apply, hV]
    rw [him]
    exact mul_nonneg (norm_nonneg _)
      (Real.sin_pos_of_pos_of_lt_pi hδ.1 hδ.2).le
  have hdecomp :
      schwarzChristoffelVertex a e z₀ i.castSucc -
          schwarzChristoffelVertex a e z₀ j.succ =
        (schwarzChristoffelVertex a e z₀ i.castSucc -
          schwarzChristoffelVertex a e z₀ 0) +
        ((schwarzChristoffelVertex a e z₀ 0 - Vinf) +
          (Vinf - schwarzChristoffelVertex a e z₀ (Fin.last n))) +
        (schwarzChristoffelVertex a e z₀ (Fin.last n) -
          schwarzChristoffelVertex a e z₀ j.succ) := by
    abel
  rw [hdecomp, mul_add, mul_add, Complex.add_im, Complex.add_im]
  exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hleft hclose) hright

/-- Two nonadjacent bounded Schwarz--Christoffel sides are disjoint when their direct edge-angle
turn is at least `π`.  The separating chord follows the complementary boundary arc through the
vertex at infinity, whose turn is at most `π`. -/
theorem disjoint_schwarzChristoffelPolygon_edgeSet_of_long_turn
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2)
    (i j : Fin n) (hij : i.val + 1 < j.val)
    (hlong : schwarzChristoffelEdgeAngle a e (a i.castSucc) + Real.pi ≤
      schwarzChristoffelEdgeAngle a e (a j.castSucc)) :
    Disjoint ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc) := by
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
    schwarzChristoffelPolygon_edgeSet_castSucc_castSucc, Set.disjoint_left]
  intro x hxi hxj
  rw [segment_eq_image'] at hxi hxj
  obtain ⟨s, hs, rfl⟩ := hxi
  obtain ⟨t, ht, heq⟩ := hxj
  let Vi := schwarzChristoffelVertex a e z₀ i.castSucc
  let Vi' := schwarzChristoffelVertex a e z₀ i.succ
  let Vj := schwarzChristoffelVertex a e z₀ j.castSucc
  let Vj' := schwarzChristoffelVertex a e z₀ j.succ
  let θj := schwarzChristoffelEdgeAngle a e (a j.castSucc)
  let u := Complex.exp (-θj * Complex.I)
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    rw [exponent_sum_at_eq a e ha]
    exact (he k).1
  have hmiddle : 0 < (u * (Vi - Vj')).im :=
    im_exp_neg_mul_schwarzChristoffelVertex_sub_pos_of_long_turn
      a e z₀ ha he hsum i j hij hlong
  have hjzero : (u * (Vj' - Vj)).im = 0 := by
    have him := im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
      a e z₀ ha θj j (hfinite j.castSucc) (hfinite j.succ)
    simpa only [u, θj, sub_self, Real.sin_zero, mul_zero, Vi, Vi', Vj, Vj'] using him
  have hi_nonneg : 0 ≤ (u * (Vi' - Vi)).im := by
    have hangle := schwarzChristoffelEdgeAngle_comp_strictMono a e ha fun k ↦ (he k).2
    have hij' : i.castSucc < j.castSucc := Fin.mk_lt_mk.mpr (by omega)
    have hdiff := schwarzChristoffelEdgeAngle_sub_mem_Ioo_two_pi
      a e ha (fun k ↦ (he k).2) hsum hij'
    have hδ : schwarzChristoffelEdgeAngle a e (a i.castSucc) - θj +
        2 * Real.pi ∈ Ioc (0 : ℝ) Real.pi := by
      dsimp only [θj] at hdiff ⊢
      constructor
      · linarith [hdiff.2]
      · linarith
    have him := im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
      a e z₀ ha θj i (hfinite i.castSucc) (hfinite i.succ)
    rw [him, ← Real.sin_add_two_pi]
    exact mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_mem_Icc ⟨hδ.1.le, hδ.2⟩)
  have hfirst : 0 ≤ (u * ((1 - t) • (Vj' - Vj))).im := by
    have hmul : u * ((1 - t) • (Vj' - Vj)) =
        ((1 - t : ℝ) : ℂ) * (u * (Vj' - Vj)) := by
      rw [Complex.real_smul]
      ring
    rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, hjzero, mul_zero]
  have hlast : 0 ≤ (u * (s • (Vi' - Vi))).im := by
    have hmul : u * (s • (Vi' - Vi)) = (s : ℂ) * (u * (Vi' - Vi)) := by
      rw [Complex.real_smul]
      ring
    rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg hs.1 hi_nonneg
  have hdecomp :
      AffineMap.lineMap Vi Vi' s - AffineMap.lineMap Vj Vj' t =
        (1 - t) • (Vj' - Vj) + (Vi - Vj') + s • (Vi' - Vi) := by
    simp only [AffineMap.lineMap_apply_module']
    module
  have hpos : 0 <
      (u * (AffineMap.lineMap Vi Vi' s - AffineMap.lineMap Vj Vj' t)).im := by
    rw [hdecomp, mul_add, mul_add, Complex.add_im, Complex.add_im]
    exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hfirst hmiddle) hlast
  have heq' : AffineMap.lineMap Vi Vi' s = AffineMap.lineMap Vj Vj' t := by
    simpa only [AffineMap.lineMap_apply_module', add_comm, Vi, Vi', Vj, Vj'] using heq.symm
  rw [heq', sub_self, mul_zero, Complex.zero_im] at hpos
  exact hpos.false

/-- Under the classical convex Schwarz--Christoffel hypotheses, every two nonadjacent bounded
sides are disjoint.  The proof uses the direct boundary arc when its turn is less than `π` and
the complementary arc through infinity otherwise. -/
theorem disjoint_schwarzChristoffelPolygon_bounded_edgeSet
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2)
    (i j : Fin n) (hij : i.val + 1 < j.val) :
    Disjoint ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc) := by
  by_cases hshort : schwarzChristoffelEdgeAngle a e (a j.castSucc) <
      schwarzChristoffelEdgeAngle a e (a i.castSucc) + Real.pi
  · apply disjoint_schwarzChristoffelPolygon_edgeSet_of_short_turn
      a e z₀ ha i j
    · exact fun _ _ _ _ hkl ↦
        schwarzChristoffelEdgeAngle_comp_strictMono a e ha (fun k ↦ (he k).2) hkl
    · intro k _
      rw [exponent_sum_at_eq a e ha]
      exact (he k).1
    · exact hij
    · exact hshort
  · exact disjoint_schwarzChristoffelPolygon_edgeSet_of_long_turn
      a e z₀ ha he hsum i j hij (le_of_not_gt hshort)

end TauCeti
