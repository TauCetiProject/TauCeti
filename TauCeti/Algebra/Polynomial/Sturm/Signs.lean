/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.RealClosed.Sign
public import TauCeti.Data.List.SignVariations

/-! # Sign bookkeeping for abstract Sturm chains

Zero-skipping variations are unchanged when an interior zero has neighbors of
opposite signs. This bookkeeping works over a strictly ordered ring. The closing
constancy lemma uses the intermediate value property of a real closed field.
-/

public section

namespace TauCeti.Sturm

open List

section Signs

variable {R : Type*} [Zero R] [LinearOrder R]

/-- A local sign-pattern relation between two lists: they agree entry by
entry except that a nonzero entry flanked by two opposite-sign neighbours may
collapse to `0`. Such a collapse is variation-neutral, so `List.signVariations` and
the leading sign are preserved (`SignRelation.signVariations_eq`). -/
private inductive SignRelation : List R → List R → Prop
  | nil : SignRelation [] []
  | same {x y : R} {l m : List R} (hx : x ≠ 0) (hy : y ≠ 0)
      (hs : SignType.sign x = SignType.sign y) (h : SignRelation l m) :
      SignRelation (x :: l) (y :: m)
  | collapse {x X x' : R} {l m : List R} {y y' : R}
      (hx : x ≠ 0) (hX : X ≠ 0) (hy' : y' ≠ 0)
      (hsx : SignType.sign x = SignType.sign x')
      (hsy : SignType.sign y = SignType.sign y')
      (hopp : SignType.sign x * SignType.sign y = -1)
      (h : SignRelation (y :: l) (y' :: m)) :
      SignRelation (x :: X :: y :: l) (x' :: 0 :: y' :: m)

private theorem sign_changes_of_opposite (u v w : SignType) (huw : u * w = -1) (hv : v ≠ 0) :
    (if u * v = -1 then (1 : ℕ) else 0) + (if v * w = -1 then 1 else 0) = 1 := by
  revert huw hv; revert u v w; decide

/-- Lists related by `SignRelation` have equal sign variations and equal leading signs. -/
private theorem SignRelation.signVariations_eq {L M : List R} (h : SignRelation L M) :
    List.signVariations L = List.signVariations M ∧ firstSign L = firstSign M := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @same x y l m hx hy hs h ih =>
    refine ⟨?_, ?_⟩
    · rw [signVariations_cons l, signVariations_cons m, ih.1, ih.2, hs]
    · rw [firstSign_cons_of_ne_zero l hx, firstSign_cons_of_ne_zero m hy, hs]
  | @collapse x X x' l m y y' hx hX hy' hsx hsy hopp h ih =>
    have hy : y ≠ 0 := by
      intro hy0; rw [hy0, sign_zero, mul_zero] at hopp; exact absurd hopp (by decide)
    have hx' : x' ≠ 0 := by
      intro hx0; rw [hx0, sign_zero] at hsx; exact hx (sign_eq_zero_iff.mp hsx)
    refine ⟨?_, ?_⟩
    · rw [signVariations_cons (X :: y :: l),
        firstSign_cons_of_ne_zero (y :: l) hX, signVariations_cons (y :: l),
        firstSign_cons_of_ne_zero l hy]
      rw [signVariations_cons (0 :: y' :: m),
        firstSign_zero_cons (y' :: m), firstSign_cons_of_ne_zero m hy',
        List.signVariations_zero_cons]
      rw [← add_assoc, ih.1]
      congr 1
      rw [← hsx, ← hsy, ite_eq_left hopp]
      exact sign_changes_of_opposite _ _ _ hopp (fun h => hX (sign_eq_zero_iff.mp h))
    · rw [firstSign_cons_of_ne_zero (X :: y :: l) hx,
        firstSign_cons_of_ne_zero (0 :: y' :: m) hx', hsx]

end Signs

section Polynomials

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The zero-skipping variations of a polynomial list at a point. -/
noncomputable def signVariationsAt (cs : List (Polynomial R)) (x : R) : ℕ :=
  List.signVariations (cs.map (Polynomial.eval x))

/-- Variations are computed on the list of evaluations. -/
theorem signVariationsAt_def (cs : List (Polynomial R)) (x : R) :
    signVariationsAt cs x = List.signVariations (cs.map (Polynomial.eval x)) := (rfl)

@[simp, grind =]
theorem signVariationsAt_nil (x : R) : signVariationsAt [] x = 0 := by simp [signVariationsAt_def]

@[simp, grind =]
theorem signVariationsAt_singleton (p : Polynomial R) (x : R) : signVariationsAt [p] x = 0 := by
  simp [signVariationsAt_def]

/-- Prepending an evaluation contributes one variation exactly when its
sign is opposite to the first nonzero sign of the remaining evaluations. -/
theorem signVariationsAt_cons (cs : List (Polynomial R)) {p : Polynomial R} {x : R}
    : signVariationsAt (p :: cs) x =
      (if SignType.sign (p.eval x) * List.firstSign (cs.map (Polynomial.eval x)) = -1
        then 1 else 0) + signVariationsAt cs x := by
  rw [signVariationsAt_def, List.map_cons, List.signVariations_cons,
    signVariationsAt_def]

end Basic

section OrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying every entry by a polynomial that does not vanish at the point
preserves the sign variations at that point. -/
theorem signVariationsAt_map_mul (cs : List (Polynomial R)) {d : Polynomial R} {x : R}
    (hd : d.eval x ≠ 0) : signVariationsAt (cs.map (d * ·)) x = signVariationsAt cs x := by
  simp only [signVariationsAt_def]
  have heq : (cs.map (d * ·)).map (Polynomial.eval x) =
      (cs.map (Polynomial.eval x)).map (d.eval x * ·) := by simp [List.map_map, Function.comp_def]
  rw [heq]
  rcases lt_or_gt_of_ne hd with hd | hd
  · exact List.signVariations_map_of_sign_eq_neg
      (fun y => by rw [sign_mul, sign_neg hd, neg_one_mul]) _
  · exact List.signVariations_map
      (fun y => by rw [sign_mul, sign_pos hd, one_mul]) _

end OrderedCommRing

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Evaluation hypotheses that persist when entries are removed from the front.
Nonvanishing of the first entry at `r` is supplied separately to the induction. -/
private structure EvalSigns (a r : R) (cs : List (Polynomial R)) : Prop where
  nonzero : ∀ q ∈ cs, q.eval a ≠ 0
  last : ∀ q, cs.getLast? = some q → q.eval r ≠ 0
  alternate : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
    cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → q1.eval r = 0 →
    q0.eval r * q2.eval r < 0
  same : ∀ q ∈ cs, q.eval r ≠ 0 → SignType.sign (q.eval a) = SignType.sign (q.eval r)

omit [IsStrictOrderedRing R] in
private theorem EvalSigns.tail {a r : R} {p : Polynomial R} {cs : List (Polynomial R)}
    (h : EvalSigns a r (p :: cs)) : EvalSigns a r cs where
  nonzero q hq := h.nonzero q (List.mem_cons_of_mem _ hq)
  last q hq := by
    cases cs with
    | nil => simp at hq
    | cons q0 rest => exact h.last q (by simpa using hq)
  alternate i q0 q1 q2 h0 h1 h2 :=
    h.alternate (i + 1) q0 q1 q2 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  same q hq := h.same q (List.mem_cons_of_mem _ hq)

-- Induct along the list: a zero second entry collapses between opposite signs;
-- otherwise the first entries match and the induction continues on the tail.
private theorem signRelation_eval (a r : R) :
    ∀ (cs : List (Polynomial R)), EvalSigns a r cs →
      (∀ q, cs.head? = some q → q.eval r ≠ 0) →
      SignRelation (cs.map (Polynomial.eval a)) (cs.map (Polynomial.eval r))
  | [], _, _ => SignRelation.nil
  | [q0], h, hfront => by
      have hr : q0.eval r ≠ 0 := hfront q0 rfl
      exact SignRelation.same (h.nonzero q0 (by simp)) hr (h.same q0 (by simp) hr) SignRelation.nil
  | q0 :: q1 :: rest, h, hfront => by
      have hr0 : q0.eval r ≠ 0 := hfront q0 rfl
      have ha0 : q0.eval a ≠ 0 := h.nonzero q0 (by simp)
      by_cases hq1 : q1.eval r = 0
      · cases rest with
        | nil => exact absurd hq1 (h.last q1 (by simp))
        | cons q2 rest' =>
            have hoppR := h.alternate 0 q0 q1 q2 rfl rfl rfl hq1
            have hn0 := left_ne_zero_of_mul hoppR.ne
            have hn2 := right_ne_zero_of_mul hoppR.ne
            have hsx := h.same q0 (by simp) hn0
            have hsy := h.same q2 (by simp) hn2
            have hoppA : SignType.sign (q0.eval a) * SignType.sign (q2.eval a) = -1 := by
              rw [hsx, hsy, ← sign_mul, sign_eq_neg_one_iff]
              exact hoppR
            have hfront' : ∀ q, (q2 :: rest').head? = some q → q.eval r ≠ 0 := by
              intro q hq
              cases hq
              exact hn2
            have ih := signRelation_eval a r (q2 :: rest') h.tail.tail hfront'
            simp only [List.map_cons] at ih ⊢
            rw [hq1]
            exact SignRelation.collapse ha0 (h.nonzero q1 (by simp)) hn2 hsx hsy hoppA ih
      · have hfront' : ∀ q, (q1 :: rest).head? = some q → q.eval r ≠ 0 := by
          intro q hq
          cases hq
          exact hq1
        have ih := signRelation_eval a r (q1 :: rest) h.tail hfront'
        simp only [List.map_cons] at ih ⊢
        exact SignRelation.same ha0 hr0 (h.same q0 (by simp) hr0) ih

/-- Evaluations at `a` and `r` have the same variation count if no entry
vanishes at `a`, the first and last entries do not vanish at `r`, zeros at `r`
have nonvanishing opposite-sign neighbours, and the surviving signs agree. -/
theorem signVariationsAt_eq_of_alternate (cs : List (Polynomial R)) (a r : R)
    (hne : ∀ q ∈ cs, q.eval a ≠ 0)
    (hfront : ∀ q, cs.head? = some q → q.eval r ≠ 0)
    (hlast : ∀ q, cs.getLast? = some q → q.eval r ≠ 0)
    (halt : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
      cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → q1.eval r = 0 →
      q0.eval r * q2.eval r < 0)
    (hsame : ∀ q ∈ cs, q.eval r ≠ 0 →
      SignType.sign (q.eval a) = SignType.sign (q.eval r)) :
    signVariationsAt cs a = signVariationsAt cs r :=
  (signRelation_eval a r cs ⟨hne, hlast, halt, hsame⟩ hfront).signVariations_eq.1

end OrderedRing

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Variations are constant if no chain entry vanishes on the interval. -/
theorem signVariationsAt_const (cs : List (Polynomial R)) {a b : R} (hab : a ≤ b)
    (hz : ∀ q ∈ cs, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    signVariationsAt cs a = signVariationsAt cs b := by
  apply List.signVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left fun q hq => Polynomial.sign_eval_const q hab (hz q hq)

end Polynomials

end TauCeti.Sturm
