/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ginzburg.Completion.Basic
import TauCeti.Combinatorics.Quiver.LoopPower

/-!
# When the Ginzburg completion adds elements

The comparison from the ordinary two-dimensional Ginzburg algebra to its Adams completion is
surjective precisely when the original quiver has no arrows, over a nonzero coefficient ring.
Indeed, an arrow and its formal reverse give a backtrack of cohomological degree zero. The
series of all powers of this backtrack is a homogeneous element of the completion with
infinitely many nonzero Adams components, so it cannot come from the ordinary algebra.

When there are no arrows, only the adjoined loops remain. Their Adams degree is twice the
negative of their cohomological degree. The finite cohomological support required in the
completion therefore forces finite Adams support as well. Thus completion adds no elements in
this case, even though powers of the adjoined loops still have unbounded Adams degree.

These statements concern the underlying differential graded algebras, not whether their
comparison is a quasi-isomorphism.

## References

* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, Section 4, for the
  distinction between ordinary and completed two-dimensional Ginzburg algebras.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra _root_.DirectSum PowerSeries

universe u v w

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

omit [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)] in
private theorem adamsWeight_eq_neg_two_mul_degree_of_no_arrows
    (hQ : ∀ i j : Q, IsEmpty (i ⟶ j)) {i j : GinzburgQuiver Q} (p : Path i j) :
    ((p.addWeight (ginzburgTwoAdamsDegree (Q := Q)) : ℕ) : ℤ) =
      -2 * p.addWeight (ginzburgTwoDegree (Q := Q)) := by
  have harrow {i j : GinzburgQuiver Q} (a : i ⟶ j) :
      (ginzburgTwoAdamsDegree a : ℤ) = -2 * ginzburgTwoDegree a := by
    induction a using GinzburgQuiver.hom_induction with
    | double a =>
      rcases a with a | a <;> exact ((hQ _ _).false a).elim
    | loop i =>
      rw [ginzburgTwoAdamsDegree_loop (Q := Q), ginzburgTwoDegree_loop (Q := Q)]
      norm_num
  induction p with
  | nil => simp
  | cons p a ih =>
    rw [Path.addWeight_cons, Path.addWeight_cons, Nat.cast_add, harrow, ih]
    ring

/-- If the original quiver has no arrows, completion adds no elements: finite cohomological
support already forces finite Adams support. No nontriviality assumption on the ring is needed. -/
theorem ginzburgTwoToCompleted_surjective_of_no_arrows
    (hQ : ∀ i j : Q, IsEmpty (i ⟶ j)) :
    Function.Surjective (ginzburgTwoToCompleted k Q) := by
  classical
  intro f
  apply (mem_range_ginzburgTwoToCompleted_iff k Q).mpr
  obtain ⟨hf, s, hs⟩ := (mem_completedGinzburgTwo_iff k Q).mp f.2
  apply (s.finite_toSet.image (fun p : ℤ => (-2 * p).toNat)).subset
  intro n hn
  have hn' := Function.mem_support.mp hn
  rw [← sum_support_decompose (gradeBy k (ginzburgTwoDegree (Q := Q)))
    (coeff n (f : PowerSeries (pathAlgebra k (GinzburgQuiver Q))))] at hn'
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
  let z := decompose (gradeBy k (ginzburgTwoDegree (Q := Q)))
    (coeff n (f : PowerSeries (pathAlgebra k (GinzburgQuiver Q)))) p
  have hp' : p ∈ s := by
    by_contra hp'
    exact hp (hs n p hp')
  obtain ⟨x, hxA, hxC⟩ := exists_path_of_ne_zero_mem_gradeBy_inf hp
    ⟨isHomogeneous_gradeBy_ginzburgTwoDegree k n p (hf n), z.2⟩
  refine ⟨p, hp', ?_⟩
  have hw := adamsWeight_eq_neg_two_mul_degree_of_no_arrows Q hQ x.2.2
  rw [hxA, hxC] at hw
  simpa only [Int.toNat_natCast] using (congrArg Int.toNat hw).symm

/-- An arrow gives a degree-zero element of the completed Ginzburg algebra outside the image of
its ordinary algebra: the formal sum of all powers of the corresponding doubled backtrack. -/
theorem exists_completedGinzburgTwo_notMem_range [Nontrivial k] {i j : Q} (a : i ⟶ j) :
    ∃ f : completedGinzburgTwo k Q, f ∈ completedGinzburgTwoGrading k Q 0 ∧
      f ∉ Set.range (ginzburgTwoToCompleted k Q) := by
  classical
  let e := Symmetrify.of.map a
  let b := ginzburgOf.mapPath ((Path.nil.cons e).cons (_root_.Quiver.reverse e))
  have hbA : b.addWeight (ginzburgTwoAdamsDegree (Q := Q)) = 2 := by
    rw [Prefunctor.addWeight_mapPath]
    simp only [ginzburgTwoAdamsDegree_ginzburgOf_map, Path.addWeight_cons, Path.addWeight_nil]
  have hbC : b.addWeight (ginzburgTwoDegree (Q := Q)) = 0 := by
    rw [Prefunctor.addWeight_mapPath]
    simp only [ginzburgTwoDegree_ginzburgOf_map, Path.addWeight_cons, Path.addWeight_nil,
      add_zero]
  have hb (m : ℕ) :
      (b.loopPow m).addWeight (ginzburgTwoAdamsDegree (Q := Q)) = 2 * m ∧
        (b.loopPow m).addWeight (ginzburgTwoDegree (Q := Q)) = 0 := by
    rw [Path.addWeight_loopPow, Path.addWeight_loopPow, hbA, hbC]
    simp [mul_comm]
  let f : PowerSeries (pathAlgebra k (GinzburgQuiver Q)) := mk fun n =>
    if n % 2 = 0 then
      ofPath ⟨ginzburgOf.obj (Symmetrify.of.obj i), ginzburgOf.obj (Symmetrify.of.obj i),
        b.loopPow (n / 2)⟩ else 0
  have hf : f ∈ adamsCompletionPiece (gradeBy k (ginzburgTwoAdamsDegree (Q := Q)))
      (gradeBy k (ginzburgTwoDegree (Q := Q))) 0 := by
    apply (mem_adamsCompletionPiece_iff _ _).mpr
    intro n
    simp only [f, coeff_mk]
    split_ifs with hn
    · exact ⟨ofPath_mem_gradeBy_of_addWeight (by rw [(hb _).1]; omega),
        ofPath_mem_gradeBy_of_addWeight (hb _).2⟩
    · exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  let g : completedGinzburgTwo k Q :=
    ⟨f, adamsCompletionPiece_le_adamsCompletion _ _ 0 hf⟩
  refine ⟨g, (mem_adamsCompletionGrading_iff _ _).mpr hf, ?_⟩
  intro hg
  have hfin := (mem_range_ginzburgTwoToCompleted_iff k Q).mp hg
  have heven : Set.range (fun m : ℕ => 2 * m) ⊆
      Function.support (fun n => coeff n (g : PowerSeries (pathAlgebra k (GinzburgQuiver Q)))) := by
    rintro _ ⟨m, rfl⟩
    simp only [Function.mem_support, g, f, coeff_mk, Nat.mul_mod_right, ite_true]
    exact (linearIndependent_ofPath k (GinzburgQuiver Q)).ne_zero _
  exact (Set.infinite_range_of_injective (fun m n h => by omega)) (hfin.subset heven)

/-- Over a nonzero commutative ring, the ordinary-to-completed comparison is surjective exactly
when the original quiver has no arrows. This does not assert a criterion for quasi-isomorphism. -/
@[simp]
theorem ginzburgTwoToCompleted_surjective_iff [Nontrivial k] :
    Function.Surjective (ginzburgTwoToCompleted k Q) ↔ ∀ i j : Q, IsEmpty (i ⟶ j) := by
  constructor
  · intro h i j
    refine ⟨fun a => ?_⟩
    obtain ⟨f, -, hf⟩ := exists_completedGinzburgTwo_notMem_range k Q a
    exact hf (h f)
  · exact ginzburgTwoToCompleted_surjective_of_no_arrows k Q

end TauCeti
