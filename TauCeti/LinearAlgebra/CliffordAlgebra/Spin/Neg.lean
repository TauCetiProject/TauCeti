/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Center
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic

/-!
# The Spin groups of a quadratic form and of its negative

Mathlib's `CliffordAlgebra.evenEquivEvenNeg` identifies the even Clifford algebras of `Q` and
`-Q`; it sends a product of two vectors `ι Q a * ι Q b` to `-(ι (-Q) a * ι (-Q) b)`. When `2` is
invertible, this file restricts that equivalence to a group isomorphism
`CliffordAlgebra.spinGroupEquivNeg Q : spinGroup Q ≃* spinGroup (-Q)`. Both Spin groups act on the
common underlying module, and the isomorphism preserves these actions on the nose. It also
sends the central element `-1` to `-1`.

Over the reals this compares a Spin group built from a positive-definite form with the Clifford
algebra of the negative-definite form, in which vectors satisfy `c(v)² = -|v|²`. There is no
algebra isomorphism between the full Clifford algebras of `Q` and `-Q` in general, so the comparison
necessarily passes through the even subalgebras.

A Spin element is a product of an even number of vectors of invertible norm
(`CliffordAlgebra.exists_even_length_list_of_spinGroup`). The same vectors, read in the Clifford
algebra of `-Q`, conjugate vectors in the same way, which is what identifies the two actions.

## Main results

* `CliffordAlgebra.spinGroupEquivNeg`: the group isomorphism `spinGroup Q ≃* spinGroup (-Q)`.
* `CliffordAlgebra.coe_spinGroupEquivNeg_apply`: its Clifford value is `evenEquivEvenNeg`.
* `CliffordAlgebra.coe_spinGroupEquivNeg_apply_of_coe_eq_ι_mul_ι`: a product of two vectors
  `ι Q a * ι Q b` goes to `-(ι (-Q) a * ι (-Q) b)`.
* `CliffordAlgebra.spinVectorAction_spinGroupEquivNeg`: the isomorphism preserves the vector
  actions.
* `CliffordAlgebra.spinGroupEquivNeg_negOne`: the isomorphism sends `-1` to `-1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §§1–3.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

section Products

variable {Q : QuadraticForm R M}

/-- Moving a vector `m` past `ι Q v` replaces it by `r • v - m`, where `r * Q v` is the polar
pairing. This description is unchanged when `Q` is replaced by `-Q`. -/
private theorem ι_mul_ι_eq_ι_smul_sub_mul_ι (v m : M) {r : R}
    (hr : r * Q v = polar Q v m) :
    ι Q v * ι Q m = ι Q (r • v - m) * ι Q v := by
  rw [map_sub, map_smul, sub_mul, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def,
    ← map_mul (algebraMap R (CliffordAlgebra Q)), hr,
    ← ι_mul_ι_add_swap, add_sub_cancel_right]

/-- A product of vectors of invertible norm moves a vector past itself in the same way in the
Clifford algebras of `Q` and of `-Q`. -/
private theorem exists_prod_map_ι_mul_ι_eq (l : List M) (hl : ∀ v ∈ l, IsUnit (Q v)) (m : M) :
    ∃ w : M, (l.map (ι Q)).prod * ι Q m = ι Q w * (l.map (ι Q)).prod ∧
      (l.map (ι (-Q))).prod * ι (-Q) m = ι (-Q) w * (l.map (ι (-Q))).prod := by
  induction l with
  | nil => exact ⟨m, by simp, by simp⟩
  | cons v l ih =>
    obtain ⟨w, h₁, h₂⟩ := ih fun u hu ↦ hl u (List.mem_cons_of_mem v hu)
    let r := Ring.inverse (Q v) * polar Q v w
    have hr : r * Q v = polar Q v w := by
      rw [mul_right_comm, Ring.inverse_mul_cancel _ (hl v List.mem_cons_self), one_mul]
    have hr' : r * (-Q) v = polar (-Q) v w := by
      simp [hr, polar_neg]
    refine ⟨r • v - w, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, mul_assoc, h₁, ← mul_assoc,
        ι_mul_ι_eq_ι_smul_sub_mul_ι v w hr, mul_assoc]
    · rw [List.map_cons, List.prod_cons, mul_assoc, h₂, ← mul_assoc,
        ι_mul_ι_eq_ι_smul_sub_mul_ι v w hr', mul_assoc]

/-- On a product of `2k` vectors, `evenEquivEvenNeg` is the same product in the Clifford algebra of
`-Q`, multiplied by `(-1) ^ k`. -/
private theorem coe_evenEquivEvenNeg_prod_map_ι :
    ∀ (l : List M), Even l.length → ∀ h : (l.map (ι Q)).prod ∈ even Q,
      (evenEquivEvenNeg Q ⟨_, h⟩ : CliffordAlgebra (-Q)) =
        (-1 : R) ^ (l.length / 2) • (l.map (ι (-Q))).prod
  | [], _, h => by
    have h₁ : (⟨_, h⟩ : even Q) = 1 := Subtype.ext (by simp)
    rw [h₁, map_one]
    simp
  | [_], hl, _ => absurd hl (by simp)
  | a :: b :: l, hl, h => by
    have hl' : Even l.length := by simpa [Nat.even_add_one] using hl
    have hsplit : (⟨_, h⟩ : even Q) =
        (even.ι Q).bilin a b * ⟨_, prod_map_ι_mem_even_of_even_length hl'⟩ :=
      Subtype.ext (by simp [mul_assoc])
    have hlen : (a :: b :: l).length / 2 = l.length / 2 + 1 := by
      simp only [List.length_cons]
      omega
    rw [hsplit, map_mul, evenEquivEvenNeg_apply, evenToNeg_ι,
      Subalgebra.coe_mul, NegMemClass.coe_neg, coe_even_ι_bilin,
      coe_evenEquivEvenNeg_prod_map_ι l hl' _, hlen]
    simp [pow_succ, mul_assoc]

variable [Invertible (2 : R)]

/-- Every Spin element is a product of vectors of invertible norm, and its image under
`evenEquivEvenNeg` is the same product in the Clifford algebra of `-Q`, up to sign. -/
private theorem exists_list_of_spinGroup (x : spinGroup Q) :
    ∃ l : List M, (∀ v ∈ l, IsUnit (Q v)) ∧ (x : CliffordAlgebra Q) = (l.map (ι Q)).prod ∧
      (evenEquivEvenNeg Q (spinGroupToEven Q x) : CliffordAlgebra (-Q)) =
        (-1 : R) ^ (l.length / 2) • (l.map (ι (-Q))).prod := by
  obtain ⟨l, hl, heven, hx⟩ := exists_even_length_list_of_spinGroup x
  have h : (l.map (ι Q)).prod ∈ even Q := prod_map_ι_mem_even_of_even_length heven
  have hx' : spinGroupToEven Q x = ⟨_, h⟩ := Subtype.ext (by simp [hx])
  exact ⟨l, hl, hx, by rw [hx', coe_evenEquivEvenNeg_prod_map_ι l heven h]⟩

/-- The image of a Spin element under `evenEquivEvenNeg` lies in the Spin group of `-Q`. Stated for
any `Q'` equal to `-Q`, so that it also covers the inverse direction. -/
private theorem coe_evenToNeg_mem_spinGroup (Q' : QuadraticForm R M) (h : Q' = -Q)
    (x : spinGroup Q) :
    (evenToNeg Q Q' h (spinGroupToEven Q x) : CliffordAlgebra Q') ∈ spinGroup Q' := by
  subst h
  rw [← evenEquivEvenNeg_apply]
  obtain ⟨l, hl, -, hy⟩ := exists_list_of_spinGroup x
  set y := evenEquivEvenNeg Q (spinGroupToEven Q x)
  have hstar : star (y : CliffordAlgebra (-Q)) =
      evenEquivEvenNeg Q (reverseEven Q (spinGroupToEven Q x)) := by
    rw [← reverse_eq_star_of_mem_even, ← coe_reverseEven_apply, evenEquivEvenNeg_reverseEven]
  have hrev₁ : reverseEven Q (spinGroupToEven Q x) * spinGroupToEven Q x = 1 :=
    Subtype.ext (by
      rw [Subalgebra.coe_mul, coe_reverseEven_apply, reverse_eq_star_of_mem_even,
        coe_spinGroupToEven_apply, spinGroup.coe_star_mul_self, Subalgebra.coe_one])
  have hrev₂ : spinGroupToEven Q x * reverseEven Q (spinGroupToEven Q x) = 1 :=
    Subtype.ext (by
      rw [Subalgebra.coe_mul, coe_reverseEven_apply, reverse_eq_star_of_mem_even,
        coe_spinGroupToEven_apply, spinGroup.mul_star_self_of_mem x.2, Subalgebra.coe_one])
  have hunit₁ : star (y : CliffordAlgebra (-Q)) * y = 1 := by
    rw [hstar, ← Subalgebra.coe_mul, ← map_mul, hrev₁, map_one, Subalgebra.coe_one]
  have hunit₂ : (y : CliffordAlgebra (-Q)) * star (y : CliffordAlgebra (-Q)) = 1 := by
    rw [hstar, ← Subalgebra.coe_mul, ← map_mul, hrev₂, map_one, Subalgebra.coe_one]
  refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨?_, Unitary.mem_iff.mpr ⟨hunit₁, hunit₂⟩⟩,
    y.2⟩
  let u : (CliffordAlgebra (-Q))ˣ := ⟨y, star (y : CliffordAlgebra (-Q)), hunit₂, hunit₁⟩
  refine (lipschitzGroup.coe_mem_iff_mem (x := u)).mpr ?_
  cases l with
  | nil => exact mem_lipschitzGroup_of_coe_eq_prod_map_ι [] (by simp) (by simpa [u] using hy)
  | cons a l =>
    -- Absorb the sign into the first vector.
    refine mem_lipschitzGroup_of_coe_eq_prod_map_ι
      (((-1 : R) ^ ((a :: l).length / 2)) • a :: l) (fun v hv ↦ ?_) ?_
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact isUnit_apply_smul (isUnit_one.neg.pow _)
          (by simpa using (hl _ List.mem_cons_self).neg)
      · simpa using (hl v (List.mem_cons_of_mem a hv)).neg
    · simp only [u, hy, List.map_cons, List.prod_cons, map_smul, smul_mul_assoc]

omit [Invertible (2 : R)] in
/-- `spinGroupToEven` on an explicitly packaged Spin element. -/
private theorem spinGroupToEven_mk (x : CliffordAlgebra Q) (hx : x ∈ spinGroup Q) :
    spinGroupToEven Q ⟨x, hx⟩ = ⟨x, spinGroup.mem_even hx⟩ :=
  Subtype.ext (coe_spinGroupToEven_apply Q _)

end Products

variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The Spin groups of `Q` and `-Q` are isomorphic, through Mathlib's identification
`evenEquivEvenNeg` of their even Clifford algebras. A product of two vectors `ι Q a * ι Q b` goes to
`-(ι (-Q) a * ι (-Q) b)`, and the vector actions agree. -/
def spinGroupEquivNeg : spinGroup Q ≃* spinGroup (-Q) where
  toFun x := ⟨evenEquivEvenNeg Q (spinGroupToEven Q x), by
    rw [evenEquivEvenNeg_apply]
    exact coe_evenToNeg_mem_spinGroup (-Q) rfl x⟩
  invFun y := ⟨(evenEquivEvenNeg Q).symm (spinGroupToEven (-Q) y), by
    rw [evenEquivEvenNeg_symm_apply]
    exact coe_evenToNeg_mem_spinGroup Q (neg_neg Q).symm y⟩
  left_inv x := Subtype.ext (by
    simp only [spinGroupToEven_mk, Subtype.coe_eta, AlgEquiv.symm_apply_apply,
      coe_spinGroupToEven_apply])
  right_inv y := Subtype.ext (by
    simp only [spinGroupToEven_mk, Subtype.coe_eta, AlgEquiv.apply_symm_apply,
      coe_spinGroupToEven_apply])
  map_mul' x y := Subtype.ext (by simp only [map_mul, Subalgebra.coe_mul, Submonoid.coe_mul])

/-- The Clifford value of `spinGroupEquivNeg Q x` is the image of `x` under `evenEquivEvenNeg`. -/
@[simp]
theorem coe_spinGroupEquivNeg_apply (x : spinGroup Q) :
    (spinGroupEquivNeg Q x : CliffordAlgebra (-Q)) = evenEquivEvenNeg Q (spinGroupToEven Q x) :=
  (rfl)

/-- The Clifford value of the inverse isomorphism is given by the inverse of `evenEquivEvenNeg`. -/
@[simp]
theorem coe_spinGroupEquivNeg_symm_apply (y : spinGroup (-Q)) :
    ((spinGroupEquivNeg Q).symm y : CliffordAlgebra Q) =
      (evenEquivEvenNeg Q).symm (spinGroupToEven (-Q) y) :=
  (rfl)

/-- On even parts, `spinGroupEquivNeg` is `evenEquivEvenNeg`. -/
@[simp]
theorem spinGroupToEven_spinGroupEquivNeg (x : spinGroup Q) :
    spinGroupToEven (-Q) (spinGroupEquivNeg Q x) = evenEquivEvenNeg Q (spinGroupToEven Q x) :=
  Subtype.ext (by rw [coe_spinGroupToEven_apply, coe_spinGroupEquivNeg_apply])

/-- A Spin element that is a product of two vectors `ι Q a * ι Q b` goes to the negative of the
corresponding product `-(ι (-Q) a * ι (-Q) b)`. -/
theorem coe_spinGroupEquivNeg_apply_of_coe_eq_ι_mul_ι {x : spinGroup Q} {a b : M}
    (hx : (x : CliffordAlgebra Q) = ι Q a * ι Q b) :
    (spinGroupEquivNeg Q x : CliffordAlgebra (-Q)) = -(ι (-Q) a * ι (-Q) b) := by
  have h : spinGroupToEven Q x = (even.ι Q).bilin a b :=
    Subtype.ext (by rw [coe_spinGroupToEven_apply, hx, coe_even_ι_bilin])
  rw [coe_spinGroupEquivNeg_apply, h, evenEquivEvenNeg_apply, evenToNeg_ι, NegMemClass.coe_neg,
    coe_even_ι_bilin]

/-- The isomorphism `spinGroupEquivNeg` preserves the vector actions: the Spin elements of `Q` and
of `-Q` that correspond act by the same linear automorphism of the common module. -/
@[simp]
theorem spinVectorAction_spinGroupEquivNeg (x : spinGroup Q) :
    spinVectorAction (-Q) (spinGroupEquivNeg Q x) = spinVectorAction Q x := by
  ext m
  obtain ⟨l, hl, hx, hy⟩ := exists_list_of_spinGroup x
  obtain ⟨w, h₁, h₂⟩ := exists_prod_map_ι_mul_ι_eq l hl m
  have hQ : spinVectorAction Q x m = w := by
    apply ι_injective Q
    rw [ι_spinVectorAction_apply, hx, h₁, mul_assoc, ← hx, spinGroup.mul_star_self_of_mem x.2,
      mul_one]
  have hnegQ : spinVectorAction (-Q) (spinGroupEquivNeg Q x) m = w := by
    apply ι_injective (-Q)
    rw [ι_spinVectorAction_apply, coe_spinGroupEquivNeg_apply, hy, smul_mul_assoc, h₂,
      ← mul_smul_comm, ← hy, ← coe_spinGroupEquivNeg_apply, mul_assoc,
      spinGroup.mul_star_self_of_mem (spinGroupEquivNeg Q x).2, mul_one]
  rw [hQ, hnegQ]

/-- The isomorphism `spinGroupEquivNeg` sends the central element `-1` to `-1`. -/
@[simp]
theorem spinGroupEquivNeg_negOne {K : Type*} [Field K] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    spinGroupEquivNeg Q (spinGroup.negOne Q hQ) = spinGroup.negOne (-Q) (neg_ne_zero.mpr hQ) := by
  have h : spinGroupToEven Q (spinGroup.negOne Q hQ) = -1 :=
    Subtype.ext (by rw [coe_spinGroupToEven_apply, spinGroup.coe_negOne, NegMemClass.coe_neg,
      OneMemClass.coe_one])
  apply Subtype.ext
  rw [coe_spinGroupEquivNeg_apply, h, map_neg, map_one, spinGroup.coe_negOne, NegMemClass.coe_neg,
    OneMemClass.coe_one]

end CliffordAlgebra
