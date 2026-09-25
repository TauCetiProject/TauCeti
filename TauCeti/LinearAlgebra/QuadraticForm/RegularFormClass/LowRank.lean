/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.AlgEquiv
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Regular quadratic forms of rank at most three

Over a field `K` in which two is invertible, two regular quadratic forms of the same rank `n ≤ 3`
are isometric exactly when they have the same discriminant `d` and the same Hasse invariant `s`
(Lam V.3.21). The bound on the rank cannot be dropped: over `ℝ` the forms `⟨1, 1, 1, 1⟩` and
`⟨-1, -1, -1, -1⟩` both have trivial discriminant and trivial Hasse invariant, since
`[(-1, -1)]⁶ = 1`, and they are not isometric, one being positive and the other negative definite.

The proof reduces every rank at most three to rank three by adding copies of `⟨1⟩`, which changes
`d` and `s` in the same way on both sides, and then cancels those copies by Witt cancellation. In
rank three, scaling by the discriminant makes the discriminant trivial and changes the Hasse
invariant by a factor that depends only on the discriminant. A ternary form of trivial discriminant
is `⟨-a, -b, ab⟩`, the pure norm form of the quaternion algebra `ℍ[K,a,b]`, and its Hasse invariant
is `[(a, b)] · [(-1, -1)]`. Two such forms with the same Hasse invariant therefore come from
quaternion algebras with the same Brauer class, hence isomorphic, and isomorphic quaternion algebras
have isometric pure norm forms.

## Main results

* `TauCeti.RegularFormClass.hasseInvariant_mk_neg_neg_mul`: the Hasse invariant of
  `⟨-a, -b, ab⟩` is `[(a, b)] · [(-1, -1)]`.
* `TauCeti.RegularFormClass.exists_eq_mk_neg_neg_mul`: a class of rank three and trivial
  discriminant is the class of some `⟨-a, -b, ab⟩`.
* `TauCeti.RegularFormClass.eq_iff_discr_eq_and_hasseInvariant_eq`: classes of the same rank at
  most three are equal exactly when their discriminants and Hasse invariants agree.
* `TauCeti.equivalent_iff_discr_eq_and_hasseInvariant_eq`: the same statement for regular forms
  on finite-dimensional spaces of the same dimension at most three.

## References

* [Tau Ceti roadmap, QuadraticFormInvariants, Layer 5](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/QuadraticFormInvariants/README.md):
  the classification blueprint using padding, discriminant scaling, and quaternion pure norms.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter V, §3, (3.21).
-/

public section

open Finset QuadraticMap

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

namespace RegularFormClass

open BrauerGroup

/-- Classes of rank three and trivial discriminant with the same Hasse invariant are equal. -/
private theorem eq_of_rank_eq_three_of_discr_eq_zero {x y : RegularFormClass K}
    (hx : x.rank = 3) (hy : y.rank = 3) (hdx : discr x = 0) (hdy : discr y = 0)
    (hs : hasseInvariant x = hasseInvariant y) : x = y := by
  obtain ⟨a, b, rfl⟩ := exists_eq_mk_neg_neg_mul hx hdx
  obtain ⟨c, d, rfl⟩ := exists_eq_mk_neg_neg_mul hy hdy
  rw [hasseInvariant_mk_neg_neg_mul, hasseInvariant_mk_neg_neg_mul, mul_left_inj,
    quaternionClass_eq_iff] at hs
  obtain ⟨f⟩ := hs
  have hw (a b : Kˣ) : (fun i => ((![-a, -b, a * b] i : Kˣ) : K)) = ![-(a : K), -b, a * b] := by
    funext i
    fin_cases i <;> simp
  rw [mk_eq_mk_iff, presentedForm_eq_weightedSumSquares_coe,
    presentedForm_eq_weightedSumSquares_coe, hw, hw]
  exact QuaternionAlgebra.equivalent_weightedSumSquares_of_algEquiv
    (isUnit_of_invertible (2 : K)).isRegular f

/-- Classes of rank three with the same discriminant and the same Hasse invariant are equal. -/
private theorem eq_of_rank_eq_three {x y : RegularFormClass K} (hx : x.rank = 3)
    (hy : y.rank = 3) (hd : discr x = discr y) (hs : hasseInvariant x = hasseInvariant y) :
    x = y := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Kˣ, squareClass δ = discr x := by
    obtain ⟨δ, hδ⟩ := QuotientAddGroup.mk_surjective (discr x)
    exact ⟨Additive.toMul δ, by rw [squareClass_def]; exact hδ⟩
  let r : RegularFormClass K := Quotient.mk (regularFormSetoid K) ⟨1, fun _ => δ⟩
  have h2 : (2 : ℕ) • squareClass δ = 0 :=
    ZModModule.char_nsmul_eq_zero 2 (squareClass δ : SquareClassGroup K)
  -- Scaling by the discriminant `δ` makes both discriminants trivial.
  have hdisc (z : RegularFormClass K) (hz : z.rank = 3) (hdz : discr z = discr x) :
      discr (r * z) = 0 := by
    -- After `succ_nsmul`, rewrite `3 + 1` as `2 * 2` to use the square-class exponent-two law.
    rw [discr_mk_rankOne_mul, hz, hdz, ← hδ, ← succ_nsmul, show 3 + 1 = 2 * 2 from rfl, mul_nsmul,
      h2, nsmul_zero]
  have hrank (z : RegularFormClass K) (hz : z.rank = 3) : (r * z).rank = 3 := by
    rw [rank_mul, rank_mk, hz, one_mul]
  have hrs : r * x = r * y := by
    refine eq_of_rank_eq_three_of_discr_eq_zero (hrank x hx) (hrank y hy) (hdisc x hx rfl)
      (hdisc y hy hd.symm) ?_
    rw [hasseInvariant_mk_rankOne_mul, hasseInvariant_mk_rankOne_mul, hx, hy, hd, hs]
  calc x = r * r * x := by rw [mk_rankOne_mul_self, one_mul]
    _ = r * r * y := by rw [mul_assoc, hrs, ← mul_assoc]
    _ = y := by rw [mk_rankOne_mul_self, one_mul]

/-- **Classification in rank at most three** (Lam V.3.21): two regular-form classes of the same
rank `n ≤ 3` with the same discriminant and the same Hasse invariant are equal. -/
theorem eq_of_discr_eq_of_hasseInvariant_eq {x y : RegularFormClass K} (hrank : x.rank = y.rank)
    (h3 : x.rank ≤ 3) (hd : discr x = discr y) (hs : hasseInvariant x = hasseInvariant y) :
    x = y := by
  -- Pad both classes with `3 - n` copies of `⟨1⟩` to reach rank three, then cancel them.
  let z : RegularFormClass K := (3 - x.rank) • 1
  have hz : ∀ w : RegularFormClass K, w.rank = x.rank → (w + z).rank = 3 := fun w hw => by
    have hn (m : ℕ) : (m • (1 : RegularFormClass K)).rank = m := by
      induction m with
      | zero => simp
      | succ m ih => rw [succ_nsmul, rank_add, ih, rank_one]
    rw [rank_add, hw, hn]
    omega
  refine add_right_cancel (b := z) (eq_of_rank_eq_three (hz x rfl) (hz y hrank.symm) ?_ ?_)
  · rw [discr_add, discr_add, hd]
  · rw [hasseInvariant_add, hasseInvariant_add, hd, hs]

/-- **Classification in rank at most three** (Lam V.3.21): two regular-form classes of the same
rank `n ≤ 3` are equal exactly when they have the same discriminant and the same Hasse
invariant. -/
theorem eq_iff_discr_eq_and_hasseInvariant_eq {x y : RegularFormClass K}
    (hrank : x.rank = y.rank) (h3 : x.rank ≤ 3) :
    x = y ↔ discr x = discr y ∧ hasseInvariant x = hasseInvariant y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hd, hs⟩ => eq_of_discr_eq_of_hasseInvariant_eq hrank h3 hd hs⟩

end RegularFormClass

/-- **Classification of regular forms in dimension at most three** (Lam V.3.21): two regular
quadratic forms on finite-dimensional spaces of the same dimension `n ≤ 3` are isometric exactly
when they have the same discriminant and the same Hasse invariant. -/
theorem equivalent_iff_discr_eq_and_hasseInvariant_eq {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {R : QuadraticForm K W} (hR : R.Nondegenerate)
    (hdim : Module.finrank K V = Module.finrank K W) (h3 : Module.finrank K V ≤ 3) :
    Q.Equivalent R ↔
      RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass R hR) ∧
      RegularFormClass.hasseInvariant (formClass Q hQ) =
        RegularFormClass.hasseInvariant (formClass R hR) := by
  rw [← formClass_eq_iff Q hQ R hR]
  exact RegularFormClass.eq_iff_discr_eq_and_hasseInvariant_eq (by simpa using hdim)
    (by simpa using h3)

end TauCeti
