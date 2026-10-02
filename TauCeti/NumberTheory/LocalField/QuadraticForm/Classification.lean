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

Two spaces of positive dimension whose dimensions sum to at least five represent a common
nonzero value: their difference is isotropic by the local isotropy bound. In dimensions at
least three, this allows a common line to be split off and the classification to be reduced
inductively to the binary criterion. The diagonal-chain API aligns the represented value
with the leading coefficient; the orthogonal-sum formulas recover the invariants of the tails.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.3, Theorem 7.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20.
-/

public section

open QuadraticMap

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Two regular local quadratic spaces of positive dimension whose dimensions sum to at least
five represent a common nonzero value. -/
theorem exists_mem_unitValueSet_and_mem_unitValueSet
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (R : QuadraticForm K W)
    (hR : R.Nondegenerate) (hV : 0 < Module.finrank K V) (hW : 0 < Module.finrank K W)
    (hVW : 5 ≤ Module.finrank K V + Module.finrank K W) :
    ∃ a : Kˣ, a ∈ Q.unitValueSet ∧ a ∈ R.unitValueSet := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hW
  have hnonempty : Q.unitValueSet.Nonempty := by
    obtain ⟨y, a, ha⟩ := hQ.exists_isUnit
    exact ⟨a, mem_unitValueSet.mpr ((represents_iff _ _).mpr ⟨y, ha.symm⟩)⟩
  have hneg : (-R).Nondegenerate := (QuadraticMap.nondegenerate_neg R).mpr hR
  have hiso : ¬(Q.prod (-R)).Anisotropic :=
    not_anisotropic_of_five_le_finrank _ (hQ.prod hneg) (by simpa using hVW)
  obtain ⟨a, ha, hb⟩ :=
    (not_anisotropic_prod_iff_exists_mem_unitValueSet_neg_mem hQ.radical_eq_bot
      hneg.radical_eq_bot hnonempty).mp hiso
  refine ⟨a, ha, ?_⟩
  obtain ⟨y, hy⟩ := (represents_iff _ _).mp (mem_unitValueSet.mp hb)
  exact mem_unitValueSet.mpr ((represents_iff _ _).mpr ⟨y, by simpa using hy⟩)

end QuadraticForm

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
        obtain ⟨a, haw, hav⟩ := QuadraticForm.exists_mem_unitValueSet_and_mem_unitValueSet
          (presentedForm ⟨m + 3, w⟩) (nondegenerate_presentedForm _)
          (presentedForm ⟨m + 3, v⟩) (nondegenerate_presentedForm _)
          (by simp) (by simp) (by simp; omega)
        rw [presentedForm_eq_weightedSumSquares_coe] at haw hav
        obtain ⟨w', hw', hw'a⟩ := exists_diagonalChain_first_eq_of_mem_unitValueSet w a haw
        obtain ⟨v', hv', hv'a⟩ := exists_diagonalChain_first_eq_of_mem_unitValueSet v a hav
        let L := (a : K) • (QuadraticMap.sq : QuadraticForm K K)
        have hsq : (QuadraticMap.sq : QuadraticForm K K).Anisotropic :=
          fun _ hx => mul_self_eq_zero.mp hx
        have hL : L.Nondegenerate :=
          (QuadraticMap.nondegenerate_smul_iff a.isUnit _).mpr hsq.nondegenerate
        let l := formClass L hL
        let x' := Quotient.mk (regularFormSetoid K) ⟨m + 2, Fin.tail w'⟩
        let y' := Quotient.mk (regularFormSetoid K) ⟨m + 2, Fin.tail v'⟩
        -- Align both diagonalizations with the common line, then split off their tails.
        have hsplit (u u' : Fin (m + 3) → Kˣ) (hu : DiagonalChain u u') (ha : u' 0 = a) :
            Quotient.mk (regularFormSetoid K) ⟨m + 3, u⟩ = l +
              Quotient.mk (regularFormSetoid K) ⟨m + 2, Fin.tail u'⟩ := by
          have heq : Quotient.mk (regularFormSetoid K) ⟨m + 3, u⟩ =
              Quotient.mk (regularFormSetoid K) ⟨m + 3, u'⟩ :=
            mk_eq_mk_iff.mpr (by
              simpa only [presentedForm_eq_weightedSumSquares_coe] using hu.equivalent)
          dsimp only [l]
          rw [heq, ← formClass_presentedForm ⟨m + 3, u'⟩,
            ← formClass_presentedForm ⟨m + 2, Fin.tail u'⟩, ← formClass_prod]
          apply (formClass_eq_iff _ _ _ _).mpr
          dsimp only [L]
          rw [← ha]
          exact ⟨(presentedFormConsIsometryEquiv u').symm⟩
        have hx' : Quotient.mk (regularFormSetoid K) ⟨m + 3, w⟩ = l + x' :=
          hsplit w w' hw' hw'a
        have hy' : Quotient.mk (regularFormSetoid K) ⟨m + 3, v⟩ = l + y' :=
          hsplit v v' hv' hv'a
        -- Cancelling the common discriminant and Hasse cross term identifies the tail invariants.
        rw [hx', hy', discr_add, discr_add] at hd
        have hdt : discr x' = discr y' := by
          simpa using congrArg (fun t => -discr l + t) hd
        rw [hx', hy', localHasse_add, localHasse_add, hdt] at hs
        have hst : localHasse x' = localHasse y' := mul_left_cancel (mul_right_cancel hs)
        rw [hx', hy', ih (m + 2) (by omega) x' y' (rank_mk _) (rank_mk _) hdt hst]

/-- **Local classification.** Equal rank, plain discriminant, and local Hasse invariant
determine the isometry class of a regular quadratic form. -/
theorem eq_of_discr_eq_of_localHasse_eq {x y : RegularFormClass K}
    (hrank : x.rank = y.rank) (hd : discr x = discr y) (hs : localHasse x = localHasse y) :
    x = y :=
  eq_of_rank_eq_aux x.rank x y rfl hrank.symm hd hs

/-- At fixed rank, the plain discriminant and local Hasse invariant classify regular local
quadratic forms. -/
theorem eq_iff_discr_eq_and_localHasse_eq {x y : RegularFormClass K}
    (hrank : x.rank = y.rank) :
    x = y ↔ discr x = discr y ∧ localHasse x = localHasse y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩,
    fun ⟨hd, hs⟩ => eq_of_discr_eq_of_localHasse_eq hrank hd hs⟩

/-- **The complete local invariant criterion**, including equality of ranks. -/
theorem eq_iff_rank_eq_and_discr_eq_and_localHasse_eq {x y : RegularFormClass K} :
    x = y ↔ x.rank = y.rank ∧ discr x = discr y ∧ localHasse x = localHasse y :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl⟩,
    fun ⟨hr, hd, hs⟩ => eq_of_discr_eq_of_localHasse_eq hr hd hs⟩

end RegularFormClass

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Local classification at fixed dimension.** Two regular local quadratic forms on spaces
of the same dimension are isometric exactly when their plain discriminants and Hasse signs agree. -/
theorem equivalent_iff_discr_eq_and_localHasse_eq
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {R : QuadraticForm K W} (hR : R.Nondegenerate)
    (hdim : Module.finrank K V = Module.finrank K W) :
    Q.Equivalent R ↔
      RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass R hR) ∧
      RegularFormClass.localHasse (formClass Q hQ) =
        RegularFormClass.localHasse (formClass R hR) := by
  rw [← formClass_eq_iff Q hQ R hR]
  exact RegularFormClass.eq_iff_discr_eq_and_localHasse_eq (by simpa using hdim)

/-- **Local classification.** Two regular local quadratic forms are isometric exactly when
their dimensions, plain discriminants, and Hasse signs agree. -/
theorem equivalent_iff_finrank_eq_and_discr_eq_and_localHasse_eq
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {R : QuadraticForm K W} (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Module.finrank K V = Module.finrank K W ∧
      RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass R hR) ∧
      RegularFormClass.localHasse (formClass Q hQ) =
        RegularFormClass.localHasse (formClass R hR) := by
  rw [← formClass_eq_iff Q hQ R hR,
    RegularFormClass.eq_iff_rank_eq_and_discr_eq_and_localHasse_eq, rank_formClass, rank_formClass]

end QuadraticForm
