/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Hasse
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Binary quadratic forms over a local field

Over a nonarchimedean local field of characteristic different from two, a binary regular
quadratic form is determined by its discriminant and local Hasse invariant. Its nonzero
represented values are determined by the same invariants: `⟨a, b⟩` represents a unit `c`
exactly when `(c, -ab) = (a, b)`. This describes both the hyperbolic case, which represents
every unit, and the anisotropic case, whose values form a coset of the quadratic norm group.

The classification is stated on isometry classes and on arbitrary finite-dimensional quadratic
spaces, including dimensions zero and one. The representation criterion is likewise stated
for arbitrary regular binary spaces, so a caller need not choose a diagonalization.
These are the binary inputs to classification by splitting off a represented line and cancelling.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.2, Theorem 6 and its corollary,
  and §2.3, Theorem 7, in dimension two.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20–21.
-/

public section

open QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- A binary diagonal form over a local field represents a unit `c` exactly when its Hilbert
symbol with the negative discriminant equals the local Hasse invariant of the form. -/
theorem mem_unitValueSet_binary_iff_hilbertSymbol_eq (a b c : Kˣ) :
    c ∈ unitValueSet (weightedSumSquares K ![(a : K), (b : K)]) ↔
      hilbertSymbol c (-(a * b)) = hilbertSymbol a b := by
  have hself : hilbertSymbol (-(a * b)) a = hilbertSymbol a b := by
    rw [hilbertSymbol_comm, ← mul_neg, hilbertSymbol_self_mul (Invertible.ne_zero 2), neg_neg]
  rw [mem_unitValueSet_binary_iff_mul_mem_quadraticNormSubgroup,
    ← Units.val_mul, ← Units.val_neg,
    ← hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup (-(a * b)),
    hilbertSymbol_mul_right (Invertible.ne_zero 2), hself, hilbertSymbol_comm (-(a * b)) c]
  rw [mul_eq_one_iff_eq_inv, Int.units_inv_eq_self, eq_comm]

/-- **Local binary classification.** Two binary diagonal forms over a nonarchimedean local field
are isometric exactly when their discriminants and local Hasse invariants agree. -/
theorem equivalent_binary_iff_isSquare_and_hilbertSymbol_eq (a b c d : Kˣ) :
    (weightedSumSquares K ![(a : K), (b : K)]).Equivalent
      (weightedSumSquares K ![(c : K), (d : K)]) ↔
      IsSquare (a * b * (c * d)) ∧ hilbertSymbol a b = hilbertSymbol c d := by
  refine ⟨fun h => ⟨isSquare_mul_mul_of_equivalent_binary h,
    hilbertSymbol_eq_of_equivalent_binary h⟩, ?_⟩
  rintro ⟨hd, hs⟩
  refine equivalent_binary_of_isSquare_of_mem_unitValueSet hd ?_
    (mem_unitValueSet_binary_left c d)
  rw [mem_unitValueSet_binary_iff_hilbertSymbol_eq]
  have hneg : IsSquare (-(a * b) * -(c * d)) := by simpa using hd
  rw [hilbertSymbol_congr_sq c c (-(a * b)) (-(c * d)) ⟨c, rfl⟩ hneg, hs]
  exact (mem_unitValueSet_binary_iff_hilbertSymbol_eq c d c).mp
    (mem_unitValueSet_binary_left c d)

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
      rw [hw, hv] at hd hs ⊢
      rw [discr_mk, discr_mk, Fin.prod_univ_two, Fin.prod_univ_two,
        squareClass_eq_iff_isSquare_mul] at hd
      rw [localHasse_mk_binary, localHasse_mk_binary] at hs
      rw [mk_eq_mk_iff, presentedForm_eq_weightedSumSquares_coe,
        presentedForm_eq_weightedSumSquares_coe]
      have coe_vec (a b : Kˣ) : (fun i => (![a, b] i : K)) = ![(a : K), (b : K)] := by
        ext i
        fin_cases i <;> rfl
      rw [coe_vec, coe_vec]
      exact (equivalent_binary_iff_isSquare_and_hilbertSymbol_eq _ _ _ _).mpr ⟨hd, hs⟩

/-- **Local classification in rank at most two.** Equal rank, discriminant and local Hasse
invariant determine a regular-form class in dimensions zero, one and two. -/
theorem eq_of_discr_eq_of_localHasse_eq {x y : RegularFormClass K}
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

/-- **Local classification in rank at most two**, as a characterization of equality of
isometry classes by the plain discriminant and local Hasse invariant. -/
theorem eq_iff_discr_eq_and_localHasse_eq {x y : RegularFormClass K}
    (hrank : x.rank = y.rank) (h2 : x.rank ≤ 2) :
    x = y ↔ discr x = discr y ∧ localHasse x = localHasse y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩,
    fun ⟨hd, hs⟩ => eq_of_discr_eq_of_localHasse_eq hrank h2 hd hs⟩

end RegularFormClass

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Local classification in dimension at most two.** Regular forms of the same dimension at
most two are isometric exactly when their plain discriminants and local Hasse invariants agree. -/
theorem equivalent_iff_discr_eq_and_localHasse_eq
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {R : QuadraticForm K W} (hR : R.Nondegenerate)
    (hdim : Module.finrank K V = Module.finrank K W) (h2 : Module.finrank K V ≤ 2) :
    Q.Equivalent R ↔
      RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass R hR) ∧
      RegularFormClass.localHasse (formClass Q hQ) =
        RegularFormClass.localHasse (formClass R hR) := by
  rw [← formClass_eq_iff Q hQ R hR]
  exact RegularFormClass.eq_iff_discr_eq_and_localHasse_eq
    (by simpa using hdim) (by simpa using h2)

/-- **The represented units of a regular binary space.** A unit `c` is represented exactly when
its Hilbert symbol with the negative discriminant equals the local Hasse invariant of the space.
The discriminant is the plain discriminant, written in the additive square-class group. -/
theorem mem_unitValueSet_iff_hilbertSymbol_eq_localHasse_of_finrank_eq_two
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 2) (c : Kˣ) :
    c ∈ Q.unitValueSet ↔
      hilbertSymbolOnSquareClasses (squareClass c)
        (squareClass (-1 : Kˣ) + RegularFormClass.discr (formClass Q hQ)) =
      RegularFormClass.localHasse (formClass Q hQ) := by
  obtain ⟨⟨n, w⟩, hw⟩ := exists_presentedForm_equivalent Q hQ
  have hn : n = 2 := by
    obtain ⟨e⟩ := hw
    simpa [hV] using e.toLinearEquiv.finrank_eq.symm
  subst n
  have hwvec : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [formClass_mk Q hQ ⟨2, w⟩ hw, hwvec, RegularFormClass.localHasse_mk_binary,
    RegularFormClass.discr_mk, Fin.prod_univ_two, ← squareClass_mul, neg_one_mul,
    hilbertSymbolOnSquareClasses_squareClass, hw.unitValueSet_eq]
  rw [presentedForm_eq_weightedSumSquares_coe]
  have coe_vec : (fun i => (w i : K)) = ![(w 0 : K), (w 1 : K)] := by
    ext i
    fin_cases i <;> rfl
  rw [coe_vec]
  exact mem_unitValueSet_binary_iff_hilbertSymbol_eq _ _ _

end QuadraticForm
