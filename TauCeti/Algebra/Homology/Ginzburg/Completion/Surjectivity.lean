/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ginzburg.Completion
-- Arrow induction identifies the vertices of the Ginzburg quiver with those of the original.
import all TauCeti.Algebra.Homology.Ginzburg.Basic
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
  induction p with
  | nil => simp
  | cons p a ih =>
    rcases a with (a | a) | i
    · exact ((hQ _ _).false a).elim
    · exact ((hQ _ _).false a).elim
    · -- The constructors use original vertices; the weight API uses the Ginzburg vertex wrapper.
      erw [Path.addWeight_cons, Path.addWeight_cons, ginzburgTwoAdamsDegree_loop,
        ginzburgTwoDegree_loop, Nat.cast_add]
      omega

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
  have hn' : coeff n (f : PowerSeries (pathAlgebra k (GinzburgQuiver Q))) ≠ 0 := hn
  obtain ⟨p, hp⟩ : ∃ p : ℤ,
      decompose (gradeBy k (ginzburgTwoDegree (Q := Q)))
        (coeff n (f : PowerSeries (pathAlgebra k (GinzburgQuiver Q)))) p ≠ 0 := by
    by_contra h
    push Not at h
    apply hn'
    have hz : decompose (gradeBy k (ginzburgTwoDegree (Q := Q)))
        (coeff n (f : PowerSeries (pathAlgebra k (GinzburgQuiver Q)))) = 0 := by
      exact DFinsupp.ext h
    exact (decompose _).injective (hz.trans (decompose_zero _).symm)
  let z := decompose (gradeBy k (ginzburgTwoDegree (Q := Q)))
    (coeff n (f : PowerSeries (pathAlgebra k (GinzburgQuiver Q)))) p
  have hz : (z : pathAlgebra k (GinzburgQuiver Q)) ≠ 0 := by
    intro hz
    exact hp (Subtype.ext hz)
  have hp' : p ∈ s := by
    by_contra hp'
    exact hz (hs n p hp')
  have hzA := isHomogeneous_gradeBy_ginzburgTwoDegree k n p (hf n)
  have hzC := z.2
  obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.mpr
    (fun h => hz ((pathAlgebraBasis k (GinzburgQuiver Q)).repr.map_eq_zero_iff.mp h))
  have hxA := mem_gradeBy_iff.mp hzA x hx
  have hxC := mem_gradeBy_iff.mp hzC x hx
  refine ⟨p, hp', ?_⟩
  have hw := adamsWeight_eq_neg_two_mul_degree_of_no_arrows Q hQ x.2.2
  rw [hxA, hxC] at hw
  exact (congrArg Int.toNat hw).symm

/-- An arrow gives a degree-zero element of the completed Ginzburg algebra outside the image of
its ordinary algebra: the formal sum of all powers of the corresponding doubled backtrack. -/
theorem exists_completedGinzburgTwo_not_mem_range [Nontrivial k] {i j : Q} (a : i ⟶ j) :
    ∃ f : completedGinzburgTwo k Q, f ∈ completedGinzburgTwoGrading k Q 0 ∧
      f ∉ Set.range (ginzburgTwoToCompleted k Q) := by
  classical
  let b : Path (V := GinzburgQuiver Q) i i :=
    (Path.nil.cons (GinzburgHom.double (Sum.inl a))).cons
      (GinzburgHom.double (Sum.inr a))
  have hb (m : ℕ) :
      (b.loopPow m).addWeight (ginzburgTwoAdamsDegree (Q := Q)) = 2 * m ∧
        (b.loopPow m).addWeight (ginzburgTwoDegree (Q := Q)) = 0 := by
    induction m with
    | zero =>
      -- The path is based at an original vertex, viewed through the Ginzburg vertex wrapper.
      erw [Path.loopPow_zero, Path.addWeight_nil, Path.addWeight_nil]
      simp
    | succ m ih =>
      have hbA : b.addWeight (ginzburgTwoAdamsDegree (Q := Q)) = 2 := by
        erw [Path.addWeight_cons, Path.addWeight_cons, Path.addWeight_nil,
          ginzburgTwoAdamsDegree_double]
      have hbC : b.addWeight (ginzburgTwoDegree (Q := Q)) = 0 := by
        erw [Path.addWeight_cons, Path.addWeight_cons, Path.addWeight_nil,
          ginzburgTwoDegree_double]
        omega
      erw [Path.loopPow_succ, Path.addWeight_comp, Path.addWeight_comp, ih.1, ih.2, hbA, hbC]
      constructor <;> omega
  let f : PowerSeries (pathAlgebra k (GinzburgQuiver Q)) := mk fun n =>
    if n % 2 = 0 then ofPath ⟨i, i, b.loopPow (n / 2)⟩ else 0
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
    obtain ⟨f, -, hf⟩ := exists_completedGinzburgTwo_not_mem_range k Q a
    exact hf (h f)
  · exact ginzburgTwoToCompleted_surjective_of_no_arrows k Q

end TauCeti
