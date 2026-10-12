/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Clifford
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister.Basic

/-!
# Clifford invariants of Pfister generators

The Clifford invariant of the two-fold Pfister form `⟨⟨a,b⟩⟩ = ⟨1,-a,-b,ab⟩` is the
quaternion class `[(a,b)]`, and scaling this form by a nonzero scalar preserves that invariant.
The Clifford invariant of a three-fold Pfister form is trivial. These computations supply the
values on the additive generators of the square and cube of the fundamental ideal.
Adjoining a two-fold Pfister form to any even-rank class multiplies its Clifford invariant
by the corresponding quaternion symbol.

Together with additivity and descent to Witt classes, these generator values determine the
Clifford homomorphism on the square of the fundamental ideal and its vanishing on the cube.

We use the minus-sign convention for Pfister forms. The computations use the actual Clifford
invariant, defined by the Clifford algebra in even rank, and its binary-plane recurrence.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, §3,
  especially Theorem 3.4.
-/

public section

namespace TauCeti

namespace RegularFormClass

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The Clifford invariant of a scalar multiple of a two-fold Pfister form is the quaternion
symbol of its parameters. -/
theorem cliffordInvariant_mk_rankOne_mul_pfisterFormClass_two (t a b : Kˣ) :
    cliffordInvariant (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => t⟩ *
      pfisterFormClass ![a, b]) = BrauerGroup.quaternionClass a b := by
  have hw : (⟨4, fun i => t * ![1, -a, -b, a * b] i⟩ : RegularFormPresentation K) =
      ⟨4, ![t, -(t * a), -(t * b), t * a * b]⟩ := by
    congr 1
    funext i
    fin_cases i <;> simp [mul_assoc]
  rw [pfisterFormClass_two, mk_mul_mk, RegularFormPresentation.rankOne_tmul, hw,
    cliffordInvariant_mk_quaternary]
  have hleft : -(t * -(t * a)) * -(t * b) = (-(t * b) * a) * t ^ 2 := by
    simp [pow_two, mul_comm, mul_left_comm]
  have hright : -(t * -(t * a)) * (t * a * b) = (t * b) * (t * a) ^ 2 := by
    simp [pow_two, mul_comm, mul_left_comm]
  rw [hleft, hright, BrauerGroup.quaternionClass_mul_sq_left,
    BrauerGroup.quaternionClass_mul_sq_right]
  have hfirst : BrauerGroup.quaternionClass t (-(t * a)) =
      BrauerGroup.quaternionClass t a := by
    rw [← neg_mul, BrauerGroup.quaternionClass_mul, BrauerGroup.quaternionClass_neg_self,
      one_mul]
  have hsecond : BrauerGroup.quaternionClass (-(t * b) * a) (t * b) =
      BrauerGroup.quaternionClass a t * BrauerGroup.quaternionClass a b := by
    rw [BrauerGroup.quaternionClass_mul_left,
      BrauerGroup.quaternionClass_comm (-(t * b)), BrauerGroup.quaternionClass_neg_self,
      one_mul, BrauerGroup.quaternionClass_mul]
  rw [hfirst, hsecond, BrauerGroup.quaternionClass_comm t a, ← mul_assoc, ← pow_two,
    BrauerGroup.quaternionClass_sq, one_mul]

/-- The Clifford invariant of `⟨⟨a,b⟩⟩` is the quaternion class `[(a,b)]`. -/
theorem cliffordInvariant_pfisterFormClass_two (a b : Kˣ) :
    cliffordInvariant (pfisterFormClass ![a, b]) = BrauerGroup.quaternionClass a b := by
  simpa using cliffordInvariant_mk_rankOne_mul_pfisterFormClass_two (1 : Kˣ) a b

/-- Splitting off a two-fold Pfister form multiplies the Clifford invariant by its quaternion
symbol, for any remaining class of even rank. -/
theorem cliffordInvariant_pfisterFormClass_two_add (a b : Kˣ) {x : RegularFormClass K}
    (hx : Even x.rank) :
    cliffordInvariant (pfisterFormClass ![a, b] + x) =
      BrauerGroup.quaternionClass a b * cliffordInvariant x := by
  have hp : pfisterFormClass ![a, b] =
      Quotient.mk (regularFormSetoid K) ⟨2, ![1, -a]⟩ +
        Quotient.mk (regularFormSetoid K) ⟨2, ![-b, a * b]⟩ := by
    rw [pfisterFormClass_two, mk_add_mk, RegularFormPresentation.append_def]
    congr 1
    exact Sigma.ext rfl (heq_of_eq (by funext i; fin_cases i <;> rfl))
  have hscale : (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ : RegularFormClass K) *
      Quotient.mk _ ⟨2, ![-b, a * b]⟩ = Quotient.mk _ ⟨2, ![-(a * b), a * a * b]⟩ := by
    rw [mk_mul_mk, RegularFormPresentation.rankOne_tmul]
    congr 1
    exact Sigma.ext rfl (heq_of_eq (by
      funext i
      fin_cases i <;> simp [mul_assoc]))
  have htail : (Quotient.mk (regularFormSetoid K)
      ⟨1, fun _ => -(-(a * b) * (a * a * b))⟩ : RegularFormClass K) *
      Quotient.mk _ ⟨1, fun _ => a⟩ = 1 := by
    rw [mk_rankOne_mul_mk_rankOne]
    have hu : -(-(a * b) * (a * a * b)) * a = (a * a * b) * (a * a * b) := by
      simp [mul_comm, mul_left_comm]
    rw [hu, ← mk_rankOne_mul_mk_rankOne, mk_rankOne_mul_self]
  have hsymbol : BrauerGroup.quaternionClass (-(a * b)) (a * a * b) =
      BrauerGroup.quaternionClass a b := by
    have hu : a * a * b = b * a ^ 2 := by simp [pow_two, mul_comm, mul_left_comm]
    have hneg : -(a * b) = a * -b := by simp
    rw [hu, BrauerGroup.quaternionClass_mul_sq_right]
    rw [hneg, BrauerGroup.quaternionClass_mul_left,
      BrauerGroup.quaternionClass_comm (-b), BrauerGroup.quaternionClass_neg_self, mul_one]
  rw [hp, add_assoc, cliffordInvariant_mk_binary_add 1 (-a) (by simpa using even_two.add hx)]
  simp only [BrauerGroup.quaternionClass_one_left, one_mul, neg_neg]
  rw [mul_add, hscale, cliffordInvariant_mk_binary_add _ _ (by simpa using hx),
    ← mul_assoc, htail, one_mul, hsymbol]

/-- The Clifford invariant of a three-fold Pfister form is trivial. -/
@[simp]
theorem cliffordInvariant_pfisterFormClass_three (a b c : Kˣ) :
    cliffordInvariant (pfisterFormClass ![a, b, c]) = 1 := by
  rw [← Fin.cons_self_tail ![a, b, c], pfisterFormClass_cons]
  simp only [Matrix.cons_val_zero, Fin.tail_vecCons]
  rw [add_mul, one_mul,
    cliffordInvariant_pfisterFormClass_two_add b c
      (by simpa using (even_two : Even (2 : ℕ)).add even_two),
    cliffordInvariant_mk_rankOne_mul_pfisterFormClass_two, ← pow_two,
    BrauerGroup.quaternionClass_sq]

end RegularFormClass

end TauCeti
