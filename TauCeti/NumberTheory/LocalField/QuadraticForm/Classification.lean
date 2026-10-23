/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Isotropy
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.WittChain
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Classification of regular quadratic forms over a local field

Over a nonarchimedean local field in which two is invertible, the rank, plain discriminant,
and local Hasse invariant form a complete set of invariants for regular quadratic forms.
The classification applies to isometry classes and to forms on arbitrary finite-dimensional
spaces, including the zero space. No restriction on the residue characteristic is imposed.
Because the rank is part of the invariant tuple, the signed discriminant may replace the plain
one.

Two spaces of positive dimension whose dimensions sum to at least five represent a common
nonzero value: their difference is isotropic by the local isotropy bound. In dimensions at
least three, this allows a common line to be split off and the classification to be reduced
inductively to the binary criterion. The diagonal-chain API aligns the represented value
with the leading coefficient; the orthogonal-sum formulas recover the invariants of the tails.

Since the local Hasse invariant takes only the values `±1`, a rank and a discriminant leave at most
two classes, with opposite Hasse invariants. Consequently, if `p ≠ p'` share their rank and
discriminant, then `p ⊥ x ≅ p' ⊥ y` for any classes `x ≠ y` that share their rank and
discriminant.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.3, Theorem 7.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20.
-/

public section

open QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

namespace RegularFormClass

/-- Classes of rank two with equal discriminants and equal local Hasse invariants are equal. -/
private theorem eq_of_rank_eq_two {x y : RegularFormClass K} (hx : x.rank = 2)
    (hy : y.rank = 2) (hd : discr x = discr y) (hs : localHasse x = localHasse y) : x = y := by
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      obtain ⟨m, w⟩ := p
      obtain ⟨n, v⟩ := q
      simp only [rank_mk] at hx hy
      subst m n
      have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
      have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [hw, hv] at hd hs
      rw [discr_mk, discr_mk, Fin.prod_univ_two, Fin.prod_univ_two,
        squareClass_eq_iff_isSquare_mul] at hd
      rw [localHasse_mk_binary, localHasse_mk_binary] at hs
      rw [mk_eq_mk_iff, presentedForm_two, presentedForm_two]
      exact (equivalent_binary_iff_isSquare_and_hilbertSymbol_eq _ _ _ _).mpr ⟨hd, hs⟩

/-- **Local classification in rank at most two.** Equal rank, discriminant and local Hasse
invariant determine a regular-form class in dimensions zero, one and two. -/
private theorem eq_of_rank_le_two {x y : RegularFormClass K}
    (hrank : x.rank = y.rank) (h2 : x.rank ≤ 2) (hd : discr x = discr y)
    (hs : localHasse x = localHasse y) : x = y := by
  by_cases hx : x.rank = 0
  · have hy : y.rank = 0 := hrank.symm.trans hx
    rw [rank_eq_zero_iff.mp hx, rank_eq_zero_iff.mp hy]
  by_cases hx₁ : x.rank = 1
  · -- Adjoin the same line to reach rank two, then cancel it.
    refine add_right_cancel (b := 1) (eq_of_rank_eq_two
      (by simp [rank_add, hx₁]) (by simp [rank_add, ← hrank, hx₁]) ?_ ?_)
    · simp only [discr_add, hd]
    · rw [localHasse_add, localHasse_add, hd, hs]
  exact eq_of_rank_eq_two (by omega) (by omega) hd hs

private theorem eq_of_rank_eq_aux (n : ℕ) : ∀ x y : RegularFormClass K,
    x.rank = n → y.rank = n → discr x = discr y → localHasse x = localHasse y → x = y := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hx hy hd hs
    by_cases hn : n ≤ 2
    · exact eq_of_rank_le_two (hx.trans hy.symm) (hx ▸ hn) hd hs
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    induction x using Quotient.inductionOn with
    | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
        obtain ⟨r, w⟩ := p
        obtain ⟨s, v⟩ := q
        simp only [rank_mk] at hx hy
        subst r s
        -- The local isotropy bound supplies a common unit value in every rank at least three.
        obtain ⟨a, haw, hav⟩ :=
          QuadraticForm.exists_mem_unitValueSet_and_mem_of_five_le_finrank_add
            (presentedForm ⟨m + 3, w⟩) (nondegenerate_presentedForm _)
            (presentedForm ⟨m + 3, v⟩) (nondegenerate_presentedForm _)
            (by simp) (by simp) (by simp; omega)
        -- Split the common line off both classes.
        obtain ⟨x', hx'r, hx'⟩ := exists_eq_mk_rankOne_add_of_mem_unitValueSet w a haw
        obtain ⟨y', hy'r, hy'⟩ := exists_eq_mk_rankOne_add_of_mem_unitValueSet v a hav
        -- Cancelling the common discriminant and Hasse cross term identifies the tail invariants.
        rw [hx', hy', discr_add, discr_add] at hd
        -- Instance search does not find `IsLeftCancelAdd (SquareClassGroup K)`, so the common
        -- summand is cancelled through the injectivity of translation in the group.
        have hdt : discr x' = discr y' :=
          (Equiv.addLeft (discr (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩))).injective hd
        rw [hx', hy', localHasse_add, localHasse_add, hdt] at hs
        have hst : localHasse x' = localHasse y' := mul_left_cancel (mul_right_cancel hs)
        rw [hx', hy', ih (m + 2) (by omega) x' y' hx'r hy'r hdt hst]

/-- **Local classification.** Equal rank, plain discriminant, and local Hasse invariant
determine the isometry class of a regular quadratic form. -/
theorem eq_of_discr_eq_of_localHasse_eq {x y : RegularFormClass K}
    (hrank : x.rank = y.rank) (hd : discr x = discr y) (hs : localHasse x = localHasse y) :
    x = y :=
  eq_of_rank_eq_aux x.rank x y rfl hrank.symm hd hs

/-- **The complete local invariant criterion**, including equality of ranks. -/
theorem eq_iff_rank_eq_and_discr_eq_and_localHasse_eq {x y : RegularFormClass K} :
    x = y ↔ x.rank = y.rank ∧ discr x = discr y ∧ localHasse x = localHasse y :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl⟩,
    fun ⟨hr, hd, hs⟩ => eq_of_discr_eq_of_localHasse_eq hr hd hs⟩

/-- **The complete local invariant criterion with the signed discriminant.** Since the rank is
part of the tuple, the signed discriminant may replace the plain one. -/
theorem eq_iff_rank_eq_and_signedDiscr_eq_and_localHasse_eq {x y : RegularFormClass K} :
    x = y ↔ x.rank = y.rank ∧ signedDiscr x = signedDiscr y ∧ localHasse x = localHasse y := by
  rw [eq_iff_rank_eq_and_discr_eq_and_localHasse_eq]
  refine and_congr_right fun hrank => ?_
  rw [signedDiscr_eq_sign_add_discr, signedDiscr_eq_sign_add_discr, hrank]
  -- Instance search does not find `IsLeftCancelAdd (SquareClassGroup K)`, so the rank term is
  -- cancelled through the injectivity of translation in the group.
  exact and_congr_left'
    (Equiv.addLeft ((rank y).choose 2 • squareClass (-1 : Kˣ))).injective.eq_iff.symm

/-- **At most two classes of each rank and discriminant.** Distinct classes with the same rank
and plain discriminant have opposite local Hasse invariants. -/
theorem localHasse_eq_neg_of_ne {x y : RegularFormClass K} (hrank : x.rank = y.rank)
    (hd : discr x = discr y) (hne : x ≠ y) : localHasse x = -localHasse y :=
  Int.units_ne_iff_eq_neg.mp fun hs => hne (eq_of_discr_eq_of_localHasse_eq hrank hd hs)

/-- **Exchanging two pairs of distinct classes.** Let `p ≠ p'` be classes with the same rank and
plain discriminant, and let `x, y` be classes with the same rank and plain discriminant. Then
`p + x = p' + y`, that is `p ⊥ x ≅ p' ⊥ y`, exactly when `x ≠ y`. -/
theorem add_eq_add_iff_ne {p p' x y : RegularFormClass K} (hpr : p.rank = p'.rank)
    (hpd : discr p = discr p') (hp : p ≠ p') (hxr : x.rank = y.rank) (hxd : discr x = discr y) :
    p + x = p' + y ↔ x ≠ y := by
  refine ⟨fun h hxy => hp (add_right_cancel (hxy ▸ h)), fun hxy => ?_⟩
  refine eq_of_discr_eq_of_localHasse_eq (by simp [rank_add, hpr, hxr]) (by simp [hpd, hxd]) ?_
  rw [localHasse_add, localHasse_add, localHasse_eq_neg_of_ne hpr hpd hp,
    localHasse_eq_neg_of_ne hxr hxd hxy, hpd, hxd, neg_mul_neg]

end RegularFormClass

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Local classification.** Two regular local quadratic forms are isometric exactly when
their dimensions, plain discriminants, and local Hasse invariants agree. -/
theorem equivalent_iff_finrank_eq_and_discr_eq_and_localHasse_eq
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {R : QuadraticForm K W} (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Module.finrank K V = Module.finrank K W ∧
      RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass R hR) ∧
      RegularFormClass.localHasse (formClass Q hQ) =
        RegularFormClass.localHasse (formClass R hR) := by
  rw [← formClass_eq_iff Q hQ R hR,
    RegularFormClass.eq_iff_rank_eq_and_discr_eq_and_localHasse_eq, rank_formClass, rank_formClass]

end QuadraticForm
