/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image

/-!
# Balls, closures and interiors of real semialgebraic sets

This file shows that the basic metric and topological constructions on the real coordinate space
`σ → ℝ`, for a finite index type `σ`, preserve semialgebraicity.

* Open and closed balls are semialgebraic, both for the sup norm, which is the norm Mathlib puts
  on `σ → ℝ`, and for the Euclidean norm of `EuclideanSpace ℝ σ`. In particular every point has
  arbitrarily small open semialgebraic neighbourhoods of either kind.
* The closure, interior and frontier of a semialgebraic set are semialgebraic.

The ball statements only use the polynomial description of the two norms. The closure statement
uses the Tarski–Seidenberg theorem in the form of projection closure
(`TauCeti.HasSemialgebraicProjections ℝ`): a point `x` lies in `closure s` exactly when for every
`ε > 0` there is `y ∈ s` with `dist x y < ε`, and the two quantifiers are eliminated by two
projections and a complement. Interiors and frontiers then follow from closures by complements
and differences.

## Main results

* `TauCeti.isSemialgebraic_setOf_dist_eval_lt`, `TauCeti.isSemialgebraic_setOf_dist_eval_le`:
  the locus where the sup distance between two polynomial maps is bounded by a polynomial is
  semialgebraic.
* `TauCeti.isSemialgebraic_ball`, `TauCeti.isSemialgebraic_closedBall`: sup-norm balls.
* `TauCeti.isSemialgebraic_preimage_toLp_ball`, `TauCeti.isSemialgebraic_preimage_toLp_closedBall`:
  Euclidean balls, read in the coordinates `σ → ℝ`.
* `TauCeti.IsSemialgebraic.closure`, `TauCeti.IsSemialgebraic.interior`,
  `TauCeti.IsSemialgebraic.frontier`.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Proposition 2.2.2.
* S. Basu, R. Pollack, and M.-F. Roy,
  [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
  second edition, Section 3.1.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {σ τ : Type*}

/-! ### Balls -/

/-- The locus where the sup distance between two polynomial maps is less than the value of a
polynomial is semialgebraic. -/
theorem isSemialgebraic_setOf_dist_eval_lt [Fintype σ] (p q : σ → MvPolynomial τ ℝ)
    (r : MvPolynomial τ ℝ) :
    IsSemialgebraic
      {z : τ → ℝ | dist (fun i => eval z (p i)) (fun i => eval z (q i)) < eval z r} := by
  convert (isSemialgebraic_eval_pos r).inter (IsSemialgebraic.iInter fun i =>
    (isSemialgebraic_eval_lt (-r) (p i - q i)).inter
      (isSemialgebraic_eval_lt (p i - q i) r)) using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, map_neg, map_sub]
  refine ⟨fun h => ?_, fun ⟨hr, h⟩ => ?_⟩
  · have hr : 0 < eval z r := dist_nonneg.trans_lt h
    exact ⟨hr, fun i => abs_lt.1 (by simpa [Real.dist_eq] using (dist_pi_lt_iff hr).1 h i)⟩
  · exact (dist_pi_lt_iff hr).2 fun i => by simpa [Real.dist_eq] using abs_lt.2 (h i)

/-- The locus where the sup distance between two polynomial maps is at most the value of a
polynomial is semialgebraic. -/
theorem isSemialgebraic_setOf_dist_eval_le [Fintype σ] (p q : σ → MvPolynomial τ ℝ)
    (r : MvPolynomial τ ℝ) :
    IsSemialgebraic
      {z : τ → ℝ | dist (fun i => eval z (p i)) (fun i => eval z (q i)) ≤ eval z r} := by
  convert (isSemialgebraic_eval_nonneg r).inter (IsSemialgebraic.iInter fun i =>
    (isSemialgebraic_eval_le (-r) (p i - q i)).inter
      (isSemialgebraic_eval_le (p i - q i) r)) using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, map_neg, map_sub]
  refine ⟨fun h => ?_, fun ⟨hr, h⟩ => ?_⟩
  · have hr : 0 ≤ eval z r := dist_nonneg.trans h
    exact ⟨hr, fun i => abs_le.1 (by simpa [Real.dist_eq] using (dist_pi_le_iff hr).1 h i)⟩
  · exact (dist_pi_le_iff hr).2 fun i => by simpa [Real.dist_eq] using abs_le.2 (h i)

/-- An open ball for the sup norm on `σ → ℝ` is semialgebraic. -/
theorem isSemialgebraic_ball [Fintype σ] (x : σ → ℝ) (r : ℝ) :
    IsSemialgebraic (Metric.ball x r) := by
  simpa [Metric.ball] using
    isSemialgebraic_setOf_dist_eval_lt (fun i => X i) (fun i => C (x i)) (C r)

/-- A closed ball for the sup norm on `σ → ℝ` is semialgebraic. -/
theorem isSemialgebraic_closedBall [Fintype σ] (x : σ → ℝ) (r : ℝ) :
    IsSemialgebraic (Metric.closedBall x r) := by
  simpa [Metric.closedBall] using
    isSemialgebraic_setOf_dist_eval_le (fun i => X i) (fun i => C (x i)) (C r)

/-- An open ball of the Euclidean space `EuclideanSpace ℝ σ`, read in the coordinates `σ → ℝ`, is
semialgebraic. -/
theorem isSemialgebraic_preimage_toLp_ball [Fintype σ] (x : EuclideanSpace ℝ σ) (r : ℝ) :
    IsSemialgebraic (WithLp.toLp 2 ⁻¹' Metric.ball x r : Set (σ → ℝ)) := by
  convert (isSemialgebraic_eval_pos (C r)).inter
    (isSemialgebraic_eval_lt (∑ i, (X i - C (x i)) ^ 2) (C r ^ 2)) using 1
  ext y
  have hS : 0 ≤ ∑ i, (y i - x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [mem_preimage, Metric.mem_ball, EuclideanSpace.dist_eq,
    Real.dist_eq, sq_abs, mem_inter_iff, mem_ofPred_eq, eval_C, map_sum, map_pow, map_sub, eval_X]
  refine ⟨fun h => ?_, fun ⟨hr, h⟩ => (Real.sqrt_lt' hr).2 h⟩
  have hr : 0 < r := (Real.sqrt_nonneg _).trans_lt h
  exact ⟨hr, (Real.sqrt_lt' hr).1 h⟩

/-- A closed ball of the Euclidean space `EuclideanSpace ℝ σ`, read in the coordinates `σ → ℝ`,
is semialgebraic. -/
theorem isSemialgebraic_preimage_toLp_closedBall [Fintype σ] (x : EuclideanSpace ℝ σ) (r : ℝ) :
    IsSemialgebraic (WithLp.toLp 2 ⁻¹' Metric.closedBall x r : Set (σ → ℝ)) := by
  convert (isSemialgebraic_eval_nonneg (C r)).inter
    (isSemialgebraic_eval_le (∑ i, (X i - C (x i)) ^ 2) (C r ^ 2)) using 1
  ext y
  simp only [mem_preimage, Metric.mem_closedBall, EuclideanSpace.dist_eq,
    Real.dist_eq, sq_abs, mem_inter_iff, mem_ofPred_eq, eval_C, map_sum, map_pow, map_sub, eval_X,
    Real.sqrt_le_iff]

/-! ### Closures, interiors and frontiers -/

/-- The closure of a semialgebraic subset of `σ → ℝ` is semialgebraic. -/
theorem IsSemialgebraic.closure [Finite σ] {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (closure s) := by
  cases nonempty_fintype σ
  -- In the coordinates `(σ ⊕ Unit) ⊕ σ`, a point `z` encodes a centre `x = z ∘ inl ∘ inl`, a
  -- radius `ε = z (inl (inr ()))` and a point `y = z ∘ inr`; `T` says `y ∈ s` and `dist x y < ε`.
  let T : Set ((σ ⊕ Unit) ⊕ σ → ℝ) := (fun z => z ∘ Sum.inr) ⁻¹' s ∩
    {z | dist (fun i => eval z (X (.inl (.inl i)))) (fun i => eval z (X (.inr i))) <
      eval z (X (.inl (.inr ())))}
  have hT : IsSemialgebraic T :=
    (hs.preimage_comp _).inter (isSemialgebraic_setOf_dist_eval_lt _ _ _)
  -- Projecting away `y`, then the radius among the `ε > 0` for which no such `y` exists, gives
  -- the complement of the closure.
  let A : Set (σ ⊕ Unit → ℝ) := (fun z => z ∘ Sum.inl) '' T
  have hB : IsSemialgebraic ((fun w : σ ⊕ Unit → ℝ => w ∘ Sum.inl) ''
      ({w | 0 < eval w (X (.inr ()))} ∩ Aᶜ)) :=
    ((isSemialgebraic_eval_pos _).inter hT.image_comp_inl.compl).image_comp_inl
  convert hB.compl using 1
  ext x
  have hA (ε : ℝ) : Sum.elim x (fun _ => ε) ∈ A ↔ ∃ y ∈ s, dist x y < ε := by
    constructor
    · rintro ⟨z, ⟨hzs, hzd⟩, hz⟩
      refine ⟨z ∘ Sum.inr, hzs, ?_⟩
      have hx : (fun i => z (.inl (.inl i))) = x := funext fun i => congrFun hz (.inl i)
      have hε : z (.inl (.inr ())) = ε := congrFun hz (.inr ())
      simpa [hx, hε, Function.comp_def] using hzd
    · rintro ⟨y, hys, hy⟩
      exact ⟨Sum.elim (Sum.elim x fun _ => ε) y, ⟨hys, by simpa using hy⟩, rfl⟩
  simp only [Metric.mem_closure_iff, mem_compl_iff, mem_image, mem_inter_iff, mem_ofPred_eq,
    eval_X, not_exists, not_and]
  refine ⟨fun h w ⟨hw, hwA⟩ hwx => hwA ?_, fun h ε hε => ?_⟩
  · have hw' : w = Sum.elim x fun _ => w (.inr ()) := by
      ext (i | ⟨⟩)
      · exact congrFun hwx i
      · rfl
    rw [hw', hA]
    exact h _ hw
  · by_contra hne
    exact h (Sum.elim x fun _ => ε) ⟨hε, fun hA' => hne ((hA ε).1 hA')⟩ rfl

/-- The interior of a semialgebraic subset of `σ → ℝ` is semialgebraic. -/
theorem IsSemialgebraic.interior [Finite σ] {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (interior s) := by
  rw [interior_eq_compl_closure_compl]
  exact hs.compl.closure.compl

/-- The frontier of a semialgebraic subset of `σ → ℝ` is semialgebraic. -/
theorem IsSemialgebraic.frontier [Finite σ] {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (frontier s) :=
  hs.closure.sdiff hs.interior

end TauCeti
