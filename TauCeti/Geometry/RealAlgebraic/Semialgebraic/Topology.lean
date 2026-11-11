/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
import TauCeti.Topology.LocallyClosed

/-!
# Balls, closures and interiors of real semialgebraic sets

This file shows that the basic metric and topological constructions on the real coordinate space
`σ → ℝ`, for a finite index type `σ`, preserve semialgebraicity.

* Open and closed balls are semialgebraic, both for the sup norm, which is the norm Mathlib puts
  on `σ → ℝ`, and for the Euclidean norm of `EuclideanSpace ℝ σ`. In particular every point has
  arbitrarily small open semialgebraic neighbourhoods of either kind.
* The closure, interior and frontier of a semialgebraic set are semialgebraic.
* A semialgebraic subset of `ℝ ^ n` with empty interior is nowhere dense. It is the union of the
  cells of an adapted cylindrical algebraic decomposition that it contains, and these are locally
  closed with empty interior, hence nowhere dense. This fails for arbitrary sets, as the rationals
  in `ℝ` show.

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
* `TauCeti.IsSemialgebraic.setOf_mem_interior_fiber`,
  `TauCeti.IsSemialgebraic.setOf_fiber_interior_nonempty`: interiors taken separately in the
  fibers of a semialgebraic family, and the parameters where these interiors are nonempty.
* `TauCeti.IsSemialgebraic.isNowhereDense_iff`: a semialgebraic set is nowhere dense exactly when
  its interior is empty.

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

/-! ### Interiors in families -/

/-- Taking the interior separately in each fiber of a semialgebraic family preserves
semialgebraicity. The parameters need not have finitely many coordinates. -/
theorem IsSemialgebraic.setOf_mem_interior_fiber [Finite τ]
    {s : Set (σ ⊕ τ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic {z : σ ⊕ τ → ℝ |
      z ∘ Sum.inr ∈ _root_.interior {y : τ → ℝ | Sum.elim (z ∘ Sum.inl) y ∈ s}} := by
  cases nonempty_fintype τ
  -- Encode a parameter, a center, a radius and a test point, in that order.
  let p : σ ⊕ τ → ((σ ⊕ τ) ⊕ Unit) ⊕ τ :=
    Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  let B : Set (((σ ⊕ τ) ⊕ Unit) ⊕ τ → ℝ) :=
    {z | dist (fun i ↦ eval z (X (.inr i)))
      (fun i ↦ eval z (X (.inl (.inl (.inr i))))) < eval z (X (.inl (.inr ())))}
  have hB : IsSemialgebraic B := isSemialgebraic_setOf_dist_eval_lt _ _ _
  have h := ((isSemialgebraic_eval_pos (X (.inr ()))).inter
    (hB.compl.union (hs.preimage_comp p)).setOf_forall_sumElim).setOf_exists_sumElim
  convert h using 1
  ext z
  simp only [mem_ofPred_eq, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff,
    subset_def, Metric.mem_ball, mem_inter_iff, mem_compl_iff, mem_union, mem_preimage,
    B, p, eval_X, Sum.comp_elim, Sum.elim_comp_inr, ← imp_iff_not_or]
  exact ⟨fun ⟨r, hr, h⟩ ↦ ⟨fun _ ↦ r, hr, h⟩, fun ⟨r, hr, h⟩ ↦ ⟨r (), hr, h⟩⟩

/-- The parameters whose fiber has nonempty interior form a semialgebraic set. -/
theorem IsSemialgebraic.setOf_fiber_interior_nonempty [Finite τ]
    {s : Set (σ ⊕ τ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic {x : σ → ℝ | (_root_.interior {y : τ → ℝ | Sum.elim x y ∈ s}).Nonempty} := by
  simpa only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr, ← nonempty_def] using
    hs.setOf_mem_interior_fiber.setOf_exists_sumElim

/-! ### Nowhere dense semialgebraic sets -/

/-- A semialgebraic set is nowhere dense exactly when its interior is empty. -/
theorem IsSemialgebraic.isNowhereDense_iff {n : ℕ} {s : Set (Fin n → ℝ)} (hs : IsSemialgebraic s) :
    IsNowhereDense s ↔ _root_.interior s = ∅ := by
  refine ⟨fun h ↦ subset_empty_iff.1 (h ▸ interior_mono subset_closure), fun h ↦ ?_⟩
  -- `s` is the finite union of the cells of an adapted CAD that it contains, which are locally
  -- closed with empty interior.
  obtain ⟨𝒞, h𝒞, hsub⟩ := hs.exists_isCAD_subset_or_disjoint
  rw [← h𝒞.sUnion_sep_subset hsub] at h ⊢
  have := (h𝒞.finite.subset (sep_subset 𝒞 (· ⊆ s))).to_subtype
  rw [sUnion_eq_iUnion]
  exact IsNowhereDense.iUnion fun E ↦ (h𝒞.isLocallyClosed E.2.1).isNowhereDense_iff.2 <|
    subset_empty_iff.1 (h ▸ interior_mono (subset_sUnion_of_mem E.2))

end TauCeti
