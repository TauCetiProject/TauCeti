/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Basic
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.ClosedEdge

/-!
# Short-turn separation of Schwarz--Christoffel sides

The bounded sides of a Schwarz--Christoffel polygon are positive multiples of unit vectors whose
arguments are the Schwarz--Christoffel edge angles.  If `i + 1 < j` and the edge angles from `i`
through `j` are strictly increasing by less than `π`, then the intermediate chord from vertex
`i + 1` to vertex `j` lies strictly on one side of the supporting line of side `i`.  Consequently
the first and last sides cannot meet when at least one complete side lies between them.

This file records that geometric part of the global boundary-simplicity argument.  It is stated in
terms of strict monotonicity and a short-turn bound on the edge angles, so that the analytic angle
calculation and the planar separation argument remain independent.  The complementary case, where
the direct boundary arc turns by at least `π`, can use the same idea on the other arc
through the closing side.

## Main results

* `TauCeti.schwarzChristoffelVertex_succ_sub_eq_norm_mul` identifies each bounded side vector.
* `TauCeti.im_exp_neg_mul_schwarzChristoffelVertex_sub_pos_of_short_turn` puts the intermediate
  chord from vertex `i + 1` to vertex `j` strictly to the left of side `i` when `i + 1 < j` and
  the edge angles are strictly ordered with total turn less than `π`.
* `TauCeti.disjoint_schwarzChristoffelPolygon_edgeSet_of_short_turn` separates two nonadjacent
  bounded polygon sides whenever the intervening turn is less than `π`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- The vector of a bounded Schwarz--Christoffel side is its length times the unit vector whose
argument is the edge angle at the side's left prevertex.

The prevertices are strictly ordered, and integrability is required only at the two endpoints of
the side.  These are exactly the hypotheses needed to apply the closed-edge direction formula to
consecutive indexed prevertices. -/
theorem schwarzChristoffelVertex_succ_sub_eq_norm_mul (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (i : Fin n)
    (hfinite_left : -1 < ∑ k with a k = a i.castSucc, e k)
    (hfinite_right : -1 < ∑ k with a k = a i.succ, e k) :
    schwarzChristoffelVertex a e z₀ i.succ -
        schwarzChristoffelVertex a e z₀ i.castSucc =
      (‖schwarzChristoffelVertex a e z₀ i.succ -
          schwarzChristoffelVertex a e z₀ i.castSucc‖ : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) := by
  have hai : a i.castSucc < a i.succ := ha i.castSucc_lt_succ
  have hfree : ∀ k, e k ≠ 0 → a k ∉ Ioo (a i.castSucc) (a i.succ) := by
    intro k _ hk
    have hik : i.castSucc < k := (ha.lt_iff_lt).mp hk.1
    have hki : k < i.succ := (ha.lt_iff_lt).mp hk.2
    have hik' := Fin.lt_def.mp hik
    have hki' := Fin.lt_def.mp hki
    simp only [Fin.val_castSucc, Fin.val_succ] at hik' hki'
    omega
  simpa only [schwarzChristoffelBoundary_apply_prevertex a e z₀ i.castSucc hfinite_left,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ i.succ hfinite_right] using
    schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ hfree hfinite_left hfinite_right
      (x := a i.succ) (y := a i.castSucc) ⟨hai.le, le_rfl⟩ ⟨le_rfl, hai.le⟩ hai.le

private lemma norm_schwarzChristoffelVertex_succ_sub_pos (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (i : Fin n)
    (hfinite_left : -1 < ∑ k with a k = a i.castSucc, e k)
    (hfinite_right : -1 < ∑ k with a k = a i.succ, e k) :
    0 < ‖schwarzChristoffelVertex a e z₀ i.succ -
      schwarzChristoffelVertex a e z₀ i.castSucc‖ := by
  rw [norm_pos_iff, sub_ne_zero]
  apply (schwarzChristoffelVertex_ne a e z₀ (ha i.castSucc_lt_succ) ?_
    hfinite_left hfinite_right).symm
  intro k _ hk
  have hik : i.castSucc < k := (ha.lt_iff_lt).mp hk.1
  have hki : k < i.succ := (ha.lt_iff_lt).mp hk.2
  have hik' := Fin.lt_def.mp hik
  have hki' := Fin.lt_def.mp hki
  simp only [Fin.val_castSucc, Fin.val_succ] at hik' hki'
  omega

private lemma im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_pos
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hangle : StrictMono (fun j ↦ schwarzChristoffelEdgeAngle a e (a j)))
    (i k : Fin n)
    (hfinite_left : -1 < ∑ j with a j = a k.castSucc, e j)
    (hfinite_right : -1 < ∑ j with a j = a k.succ, e j) (hik : i < k)
    (hshort : schwarzChristoffelEdgeAngle a e (a k.castSucc) <
      schwarzChristoffelEdgeAngle a e (a i.castSucc) + Real.pi) :
    0 < (Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
      (schwarzChristoffelVertex a e z₀ k.succ -
        schwarzChristoffelVertex a e z₀ k.castSucc)).im := by
  let θi := schwarzChristoffelEdgeAngle a e (a i.castSucc)
  let θk := schwarzChristoffelEdgeAngle a e (a k.castSucc)
  let d := ‖schwarzChristoffelVertex a e z₀ k.succ -
    schwarzChristoffelVertex a e z₀ k.castSucc‖
  have hθ : θi < θk := hangle (Fin.castSucc_lt_castSucc_iff.mpr hik)
  have hθdiff : θk - θi ∈ Ioo (0 : ℝ) Real.pi := by
    constructor
    · exact sub_pos.mpr hθ
    · dsimp only [θi, θk]
      linarith
  have hd : 0 < d := norm_schwarzChristoffelVertex_succ_sub_pos a e z₀ ha k
    hfinite_left hfinite_right
  have hexp : -θi * Complex.I + θk * Complex.I = ((θk - θi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [schwarzChristoffelVertex_succ_sub_eq_norm_mul a e z₀ ha k
    hfinite_left hfinite_right]
  -- Expose the local names through the real-to-complex coercions before combining exponentials.
  change 0 < (Complex.exp (-θi * Complex.I) *
    ((d : ℂ) * Complex.exp (θk * Complex.I))).im
  have hmul : Complex.exp (-θi * Complex.I) *
      ((d : ℂ) * Complex.exp (θk * Complex.I)) =
      (d : ℂ) * Complex.exp (((θk - θi : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = (d : ℂ) * (Complex.exp (-θi * Complex.I) *
          Complex.exp (θk * Complex.I)) := by ring
      _ = (d : ℂ) * Complex.exp (-θi * Complex.I + θk * Complex.I) := by
        rw [Complex.exp_add]
      _ = _ := by rw [hexp]
  rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im]
  exact mul_pos hd (Real.sin_pos_of_pos_of_lt_pi hθdiff.1 hθdiff.2)

/-- A chord across a nonempty part of a short-turn Schwarz--Christoffel side chain lies strictly
to the left of the first side.

Here `i + 1 < j`, so the chord from vertex `i + 1` to vertex `j` contains at least one complete
side.  After rotating the direction of side `i` to the positive real axis, every side in that
chord has positive imaginary part: strict angle monotonicity gives the lower bound and `hshort`
keeps the final angle below the opposite direction. -/
theorem im_exp_neg_mul_schwarzChristoffelVertex_sub_pos_of_short_turn
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hangle : StrictMono (fun j ↦ schwarzChristoffelEdgeAngle a e (a j)))
    (i j : Fin n)
    (hfinite : ∀ k ∈ Icc i.succ j.castSucc, -1 < ∑ l with a l = a k, e l)
    (hij : i.val + 1 < j.val)
    (hshort : schwarzChristoffelEdgeAngle a e (a j.castSucc) <
      schwarzChristoffelEdgeAngle a e (a i.castSucc) + Real.pi) :
    0 < (Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
      (schwarzChristoffelVertex a e z₀ j.castSucc -
        schwarzChristoffelVertex a e z₀ i.succ)).im := by
  let V : ℕ → ℂ := fun k ↦ if hk : k < n + 1 then
    schwarzChristoffelVertex a e z₀ ⟨k, hk⟩ else 0
  let u := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
  have hle : i.val + 1 ≤ j.val := hij.le
  have htel := Finset.sum_Ico_sub V hle
  have hVi : V (i.val + 1) = schwarzChristoffelVertex a e z₀ i.succ := by
    dsimp only [V]
    split
    · congr 1
    · omega
  have hVj : V j.val = schwarzChristoffelVertex a e z₀ j.castSucc := by
    dsimp only [V]
    split
    · congr 1
    · omega
  rw [hVi, hVj] at htel
  rw [← htel, Finset.mul_sum]
  -- Regard imaginary part as its bundled real-linear map so it distributes over the finite sum.
  change 0 < Complex.imCLM (∑ k ∈ Finset.Ico (i.val + 1) j.val,
    u * (V (k + 1) - V k))
  rw [map_sum]
  simp only [Complex.imCLM_apply]
  apply Finset.sum_pos
  · intro k hk
    simp only [Finset.mem_Ico] at hk
    have hkn : k < n := hk.2.trans j.isLt
    let k' : Fin n := ⟨k, hkn⟩
    have hik' : i < k' := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hkj : k' ≤ j := Fin.mk_le_mk.mpr hk.2.le
    have hshort' : schwarzChristoffelEdgeAngle a e (a k'.castSucc) <
        schwarzChristoffelEdgeAngle a e (a i.castSucc) + Real.pi :=
      (hangle.monotone (Fin.castSucc_le_castSucc_iff.mpr hkj)).trans_lt hshort
    have hkleft : k'.castSucc ∈ Icc i.succ j.castSucc := by
      constructor <;> apply Fin.mk_le_mk.mpr <;> omega
    have hkright : k'.succ ∈ Icc i.succ j.castSucc := by
      constructor <;> apply Fin.mk_le_mk.mpr <;> omega
    have hkpos := im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_pos
      a e z₀ ha hangle i k' (hfinite _ hkleft) (hfinite _ hkright) hik' hshort'
    have hVk : V k = schwarzChristoffelVertex a e z₀ k'.castSucc := by
      dsimp only [V]
      split
      · congr 1
      · omega
    have hVksucc : V (k + 1) = schwarzChristoffelVertex a e z₀ k'.succ := by
      dsimp only [V]
      split
      · congr 1
      · omega
    simpa only [u, hVk, hVksucc] using hkpos
  · exact Finset.nonempty_Ico.mpr hij

/-- Two nonadjacent bounded sides of a Schwarz--Christoffel polygon are disjoint when their edge
angles are strictly ordered and the directions from the first through the last side turn through
less than `π`.  The index condition excludes adjacent sides and the closing side. -/
theorem disjoint_schwarzChristoffelPolygon_edgeSet_of_short_turn
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hangle : StrictMono (fun j ↦ schwarzChristoffelEdgeAngle a e (a j)))
    (i j : Fin n)
    (hfinite : ∀ k ∈ Icc i.castSucc j.succ, -1 < ∑ l with a l = a k, e l)
    (hij : i.val + 1 < j.val)
    (hshort : schwarzChristoffelEdgeAngle a e (a j.castSucc) <
      schwarzChristoffelEdgeAngle a e (a i.castSucc) + Real.pi) :
    Disjoint ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc) := by
  -- If the sides met, the first-side remainder, the intermediate chord, and the final-side
  -- segment would sum to zero.  After rotating side `i` to the real axis, their imaginary parts
  -- are respectively zero, positive, and nonnegative.
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
  let u := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
  have hfinite_middle : ∀ k ∈ Icc i.succ j.castSucc,
      -1 < ∑ l with a l = a k, e l := by
    intro k hk
    exact hfinite k ⟨(Fin.mk_le_mk.mpr (by simp)).trans hk.1,
      hk.2.trans (Fin.mk_le_mk.mpr (by simp))⟩
  have hmiddle : 0 < (u * (Vj - Vi')).im := by
    exact im_exp_neg_mul_schwarzChristoffelVertex_sub_pos_of_short_turn
      a e z₀ ha hangle i j hfinite_middle hij hshort
  have hfirst : (u * (Vi' - Vi)).im = 0 := by
    rw [schwarzChristoffelVertex_succ_sub_eq_norm_mul a e z₀ ha i
      (hfinite _ ⟨le_rfl, Fin.mk_le_mk.mpr (by omega)⟩)
      (hfinite _ ⟨Fin.mk_le_mk.mpr (by omega), Fin.mk_le_mk.mpr (by omega)⟩)]
    dsimp only [u, Vi, Vi']
    have hmul : Complex.exp
          (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
          ((‖schwarzChristoffelVertex a e z₀ i.succ -
              schwarzChristoffelVertex a e z₀ i.castSucc‖ : ℂ) *
            Complex.exp (schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)) =
        (‖schwarzChristoffelVertex a e z₀ i.succ -
            schwarzChristoffelVertex a e z₀ i.castSucc‖ : ℂ) *
          Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I +
            schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) := by
      rw [Complex.exp_add]
      ring
    rw [hmul]
    have hz : -schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I +
        schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I = 0 := by ring
    rw [hz, Complex.exp_zero, mul_one, Complex.ofReal_im]
  have hlast : 0 ≤ (u * (t • (Vj' - Vj))).im := by
    have hij' : i < j := Fin.mk_lt_mk.mpr (by omega)
    have hjpos := im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_pos
      a e z₀ ha hangle i j
        (hfinite _ ⟨Fin.mk_le_mk.mpr (by omega), Fin.mk_le_mk.mpr (by omega)⟩)
        (hfinite _ ⟨Fin.mk_le_mk.mpr (by omega), le_rfl⟩) hij' hshort
    have hmul : u * (t • (Vj' - Vj)) = (t : ℂ) * (u * (Vj' - Vj)) := by
      rw [Complex.real_smul]
      ring
    rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg ht.1 hjpos.le
  have hdecomp :
      AffineMap.lineMap Vj Vj' t - AffineMap.lineMap Vi Vi' s =
        (1 - s) • (Vi' - Vi) + (Vj - Vi') + t • (Vj' - Vj) := by
    simp only [AffineMap.lineMap_apply_module']
    module
  have hpos : 0 <
      (u * (AffineMap.lineMap Vj Vj' t - AffineMap.lineMap Vi Vi' s)).im := by
    rw [hdecomp, mul_add, mul_add, Complex.add_im, Complex.add_im]
    have hs0 : (u * ((1 - s) • (Vi' - Vi))).im = 0 := by
      have hmul : u * ((1 - s) • (Vi' - Vi)) =
          ((1 - s : ℝ) : ℂ) * (u * (Vi' - Vi)) := by
        rw [Complex.real_smul]
        ring
      rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, hfirst, mul_zero]
    rw [hs0, zero_add]
    exact add_pos_of_pos_of_nonneg hmiddle hlast
  have heq' : AffineMap.lineMap Vj Vj' t = AffineMap.lineMap Vi Vi' s := by
    simpa only [AffineMap.lineMap_apply_module', add_comm, Vi, Vi', Vj, Vj'] using heq
  rw [heq', sub_self, mul_zero, Complex.zero_im] at hpos
  exact hpos.false

end TauCeti
