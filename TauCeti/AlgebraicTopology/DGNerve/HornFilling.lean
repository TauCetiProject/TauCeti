/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Basic
import TauCeti.Data.Finset.Basic

/-!
# Filling inner horns of coherences in the differential graded nerve

An `n`-simplex of the differential graded nerve is a string of objects with coherences satisfying
the dg nerve equation `d f = TauCeti.DGNerve.boundary f` (`TauCeti.DGNerve.Simplex`). This file
shows that coherences satisfying the equation on an inner horn `Λ[n, k]`, `0 < k < n`, are the
coherences on the horn of an `n`-simplex. This is the algebraic content of the statement that the
differential graded nerve is a quasicategory.

Only two coherences do not belong to the horn: the one through all interior vertices, which is
taken to be zero, and the one omitting `k`, which is then chosen so that the equation holds on the
full set of interior vertices. The equation for the latter follows from the fact that the boundary
of the boundary vanishes: for an arbitrary family of morphisms, the differential of the right-hand
side of the dg nerve equation is a combination of the defects of the equation on smaller sets of
interior vertices. Expanding the right-hand side twice, its terms cancel in pairs indexed by
ordered pairs of interior vertices, using the Leibniz rule and associativity.

## Main results

* `TauCeti.DGNerve.Coherences.exists_simplex_of_horn`: coherences satisfying the dg nerve equation
  on an inner horn are those of a simplex.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Proposition 1.3.1.10.
-/

public section

open CategoryTheory Finset Simplicial

namespace TauCeti

universe v u

namespace DGNerve

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C] {n : ℕ}
  {X : Fin (n + 1) → C}

/-! ### The boundary of an arbitrary family of morphisms -/

/-- The sign `(-1) ^ #{s ∈ S | t ≤ s}` of the face term at `t` in the dg nerve equation. -/
private noncomputable abbrev faceSign (S : Finset (Fin (n + 1))) (t : Fin (n + 1)) : ℤˣ :=
  (#{s ∈ S | t ≤ s} : ℤ).negOnePow

/-- The Koszul sign `(-1) ^ (#{s ∈ S | s < t} * #{s ∈ S | t < s})` of the composite term at `t`
in the dg nerve equation. -/
private noncomputable abbrev compSign (S : Finset (Fin (n + 1))) (t : Fin (n + 1)) : ℤˣ :=
  (#{s ∈ S | s < t} * #{s ∈ S | t < s} : ℤ).negOnePow

variable (F : ∀ (i j : Fin (n + 1)), Finset (Fin (n + 1)) → ∀ p : ℤ, DGHom R p (X i) (X j))

/-- The right-hand side of the dg nerve equation, evaluated on an arbitrary family `F` of
morphisms indexed by all pairs of vertices, sets of interior vertices and degrees. -/
private noncomputable def bd (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ) :
    DGHom R e (X i) (X j) :=
  ∑ t ∈ S, faceSign S t • (F i j (S.erase t) e - compSign S t •
    dgComp R (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
      (F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega))

/-- The face term indexed by an ordered pair `(t, u)` of the double expansion of the boundary of
the boundary. -/
private noncomputable def pFace (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t u : Fin (n + 1)) : DGHom R (e + 1) (X i) (X j) :=
  (faceSign S t * faceSign (S.erase t) u) • F i j ((S.erase t).erase u) (e + 1)

/-- The composite term at `u` of the face at `t`. -/
private noncomputable def pComp (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t u : Fin (n + 1)) : DGHom R (e + 1) (X i) (X j) :=
  (faceSign S t * faceSign (S.erase t) u * compSign (S.erase t) u) •
    dgComp R (F i u {s ∈ S.erase t | s < u} (-#{s ∈ S.erase t | s < u}))
      (F u j {s ∈ S.erase t | u < s} (e + 1 + #{s ∈ S.erase t | s < u})) (by omega)

/-- The face at `u < t` of the first factor of the composite term at `t`. -/
private noncomputable def lFace (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t u : Fin (n + 1)) : DGHom R (e + 1) (X i) (X j) :=
  (faceSign S t * compSign S t * faceSign {s ∈ S | s < t} u) •
    dgComp R (F i t ({s ∈ S | s < t}.erase u) (-#{s ∈ S | s < t} + 1))
      (F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega)

/-- The composite at `u < t` of the first factor of the composite term at `t`. -/
private noncomputable def lComp (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t u : Fin (n + 1)) : DGHom R (e + 1) (X i) (X j) :=
  (faceSign S t * compSign S t * faceSign {s ∈ S | s < t} u *
      compSign {s ∈ S | s < t} u) •
    dgComp R
      (dgComp R (n := -#{s ∈ S | s < t} + 1)
        (F i u {s ∈ {s ∈ S | s < t} | s < u} (-#{s ∈ {s ∈ S | s < t} | s < u}))
        (F u t {s ∈ {s ∈ S | s < t} | u < s}
          (-#{s ∈ S | s < t} + 1 + #{s ∈ {s ∈ S | s < t} | s < u})) (by omega))
      (F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega)

/-- The face at `u > t` of the second factor of the composite term at `t`. -/
private noncomputable def rFace (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t u : Fin (n + 1)) : DGHom R (e + 1) (X i) (X j) :=
  (faceSign S t * compSign S t * (-#{s ∈ S | s < t} : ℤ).negOnePow *
      faceSign {s ∈ S | t < s} u) •
    dgComp R (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
      (F t j ({s ∈ S | t < s}.erase u) (e + #{s ∈ S | s < t} + 1)) (by omega)

/-- The composite at `u > t` of the second factor of the composite term at `t`. -/
private noncomputable def rComp (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t u : Fin (n + 1)) : DGHom R (e + 1) (X i) (X j) :=
  (faceSign S t * compSign S t * (-#{s ∈ S | s < t} : ℤ).negOnePow *
      faceSign {s ∈ S | t < s} u * compSign {s ∈ S | t < s} u) •
    dgComp R (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
      (dgComp R (n := e + #{s ∈ S | s < t} + 1)
        (F t u {s ∈ {s ∈ S | t < s} | s < u} (-#{s ∈ {s ∈ S | t < s} | s < u}))
        (F u j {s ∈ {s ∈ S | t < s} | u < s}
          (e + #{s ∈ S | s < t} + 1 + #{s ∈ {s ∈ S | t < s} | s < u})) (by omega))
      (by omega)

/-- The term indexed by an ordered pair `(t, u)` of the double expansion of the boundary of the
boundary. -/
private noncomputable def pairTerm (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t u : Fin (n + 1)) : DGHom R (e + 1) (X i) (X j) :=
  (if u ≠ t then pFace F i j S e t u - pComp F i j S e t u else 0) -
    (if u < t then lFace F i j S e t u - lComp F i j S e t u else 0) -
    (if t < u then rFace F i j S e t u - rComp F i j S e t u else 0)

/-- The face part of the boundary of the boundary is the sum of the face and composite terms
indexed by the pairs `(t, u)` with `u ≠ t`. -/
private lemma faceSign_smul_bd_erase (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t : Fin (n + 1)) :
    faceSign S t • bd F i j (S.erase t) (e + 1) =
      ∑ u ∈ S.erase t, (pFace F i j S e t u - pComp F i j S e t u) := by
  rw [bd, smul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [pFace, pComp, smul_sub, smul_smul, mul_assoc]

/-- The part of the boundary of the boundary coming from the first factor of a composite. -/
private lemma smul_dgComp_bd_left (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t : Fin (n + 1)) :
    faceSign S t • compSign S t •
        dgComp R (bd F i t {s ∈ S | s < t} (-#{s ∈ S | s < t} + 1))
          (F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega) =
      ∑ u ∈ {s ∈ S | s < t}, (lFace F i j S e t u - lComp F i j S e t u) := by
  rw [bd, sum_dgComp, smul_sum, smul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [lFace, lComp, units_smul_dgComp, sub_eq_add_neg, add_dgComp, neg_dgComp,
    smul_add, smul_neg, smul_smul, mul_assoc]

/-- The part of the boundary of the boundary coming from the second factor of a composite. -/
private lemma smul_dgComp_bd_right (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ)
    (t : Fin (n + 1)) :
    faceSign S t • compSign S t • (-#{s ∈ S | s < t} : ℤ).negOnePow •
        dgComp R (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
          (bd F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t} + 1)) (by omega) =
      ∑ u ∈ {s ∈ S | t < s}, (rFace F i j S e t u - rComp F i j S e t u) := by
  rw [bd, dgComp_sum, smul_sum, smul_sum, smul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [rFace, rComp, dgComp_units_smul, sub_eq_add_neg, dgComp_add, dgComp_neg,
    smul_add, smul_neg, smul_smul, mul_assoc]

/-- The term at `t` of the boundary of the boundary is the sum of the terms indexed by the pairs
`(t, u)`. -/
private lemma smul_bd_sub_eq_sum_pairTerm (i j : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (e : ℤ) (t : Fin (n + 1)) :
    faceSign S t • (bd F i j (S.erase t) (e + 1) - compSign S t •
      (dgComp R (bd F i t {s ∈ S | s < t} (-#{s ∈ S | s < t} + 1))
          (F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega) +
        (-#{s ∈ S | s < t} : ℤ).negOnePow • dgComp R (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
          (bd F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t} + 1)) (by omega))) =
      ∑ u ∈ S, pairTerm F i j S e t u := by
  rw [sum_congr rfl fun u _ ↦ pairTerm.eq_1 F i j S e t u, sum_sub_distrib, sum_sub_distrib,
    ← sum_filter, ← sum_filter, ← sum_filter, filter_ne', ← faceSign_smul_bd_erase,
    ← smul_dgComp_bd_left, ← smul_dgComp_bd_right, smul_sub,
    smul_add, smul_add]
  abel

/-! ### Cancellation of the terms of the boundary of the boundary -/

/-- The numbers of elements of `S` on either side of two elements `t < u` of `S`, also with `t` or
`u` removed or inside one of the halves, in terms of the numbers of elements before `t`, between
`t` and `u`, and after `u`. These are the counts behind the signs of the cancellation lemmas. -/
private lemma card_filter_of_lt {S : Finset (Fin (n + 1))} {t u : Fin (n + 1)} (ht : t ∈ S)
    (hu : u ∈ S) (htu : t < u) :
    #{s ∈ S | t ≤ s} = #{s ∈ S | t < s ∧ s < u} + #{s ∈ S | u < s} + 2 ∧
    #{s ∈ S | t < s} = #{s ∈ S | t < s ∧ s < u} + #{s ∈ S | u < s} + 1 ∧
    #{s ∈ S | u ≤ s} = #{s ∈ S | u < s} + 1 ∧
    #{s ∈ S | s < u} = #{s ∈ S | s < t} + #{s ∈ S | t < s ∧ s < u} + 1 ∧
    #{s ∈ S.erase t | u ≤ s} = #{s ∈ S | u < s} + 1 ∧
    #{s ∈ S.erase t | s < u} = #{s ∈ S | s < t} + #{s ∈ S | t < s ∧ s < u} ∧
    #{s ∈ S.erase t | u < s} = #{s ∈ S | u < s} ∧
    #{s ∈ S.erase u | t ≤ s} = #{s ∈ S | t < s ∧ s < u} + #{s ∈ S | u < s} + 1 ∧
    #{s ∈ S.erase u | s < t} = #{s ∈ S | s < t} ∧
    #{s ∈ S.erase u | t < s} = #{s ∈ S | t < s ∧ s < u} + #{s ∈ S | u < s} ∧
    #{s ∈ {s ∈ S | s < u} | t ≤ s} = #{s ∈ S | t < s ∧ s < u} + 1 ∧
    #{s ∈ {s ∈ S | t < s} | u ≤ s} = #{s ∈ S | u < s} + 1 := by
  -- Each count is read off a pointwise decomposition of the indicator of its predicate.
  have h (P Q₁ Q₂ : Fin (n + 1) → Prop) [DecidablePred P] [DecidablePred Q₁] [DecidablePred Q₂]
      (k₁ k₂ : ℕ) (hP : ∀ s, (if P s then 1 else 0) = (if Q₁ s then 1 else 0) +
        (if Q₂ s then 1 else 0) + k₁ * (if s = t then 1 else 0) + k₂ * (if s = u then 1 else 0)) :
      #{s ∈ S | P s} = #{s ∈ S | Q₁ s} + #{s ∈ S | Q₂ s} + k₁ + k₂ :=
    card_filter_eq_of_ite_eq ht hu P Q₁ Q₂ k₁ k₂ fun s _ ↦ hP s
  have h' (P Q : Fin (n + 1) → Prop) [DecidablePred P] [DecidablePred Q] (k₁ k₂ : ℕ)
      (hP : ∀ s, (if P s then 1 else 0) = (if Q s then 1 else 0) +
        k₁ * (if s = t then 1 else 0) + k₂ * (if s = u then 1 else 0)) :
      #{s ∈ S | P s} = #{s ∈ S | Q s} + k₁ + k₂ := by
    simpa using h P Q (fun _ ↦ False) k₁ k₂ (by simpa using hP)
  simp only [← filter_ne', filter_filter]
  have h₁ := h (t ≤ ·) (fun s ↦ t < s ∧ s < u) (u < ·) 1 1 fun s ↦ by split_ifs <;> omega
  have h₂ := h (t < ·) (fun s ↦ t < s ∧ s < u) (u < ·) 0 1 fun s ↦ by split_ifs <;> omega
  have h₃ := h' (u ≤ ·) (u < ·) 0 1 fun s ↦ by split_ifs <;> omega
  have h₄ := h (· < u) (· < t) (fun s ↦ t < s ∧ s < u) 1 0 fun s ↦ by split_ifs <;> omega
  have h₅ := h' (fun s ↦ s ≠ t ∧ u ≤ s) (u < ·) 0 1 fun s ↦ by split_ifs <;> omega
  have h₆ := h (fun s ↦ s ≠ t ∧ s < u) (· < t) (fun s ↦ t < s ∧ s < u) 0 0
    fun s ↦ by split_ifs <;> omega
  have h₇ := h' (fun s ↦ s ≠ t ∧ u < s) (u < ·) 0 0 fun s ↦ by split_ifs <;> omega
  have h₈ := h (fun s ↦ s ≠ u ∧ t ≤ s) (fun s ↦ t < s ∧ s < u) (u < ·) 1 0
    fun s ↦ by split_ifs <;> omega
  have h₉ := h' (fun s ↦ s ≠ u ∧ s < t) (· < t) 0 0 fun s ↦ by split_ifs <;> omega
  have h₁₀ := h (fun s ↦ s ≠ u ∧ t < s) (fun s ↦ t < s ∧ s < u) (u < ·) 0 0
    fun s ↦ by split_ifs <;> omega
  have h₁₁ := h' (fun s ↦ s < u ∧ t ≤ s) (fun s ↦ t < s ∧ s < u) 1 0 fun s ↦ by split_ifs <;> omega
  have h₁₂ := h' (fun s ↦ t < s ∧ u ≤ s) (u < ·) 0 1 fun s ↦ by split_ifs <;> omega
  omega

/-- Composites of members of the family indexed by equal sets and degrees agree. -/
private lemma dgComp_congr {i t j : Fin (n + 1)} {A A' B B' : Finset (Fin (n + 1))}
    {p p' q q' r : ℤ} (hA : A = A') (hB : B = B') (hp : p = p') (hq : q = q')
    {h : p + q = r} {h' : p' + q' = r} :
    dgComp R (F i t A p) (F t j B q) h = dgComp R (F i t A' p') (F t j B' q') h' := by
  subst hA hB hp hq
  rfl

/-- The two face terms indexed by `(t, u)` and `(u, t)` cancel. -/
private lemma pFace_add_pFace {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} (e : ℤ)
    {t u : Fin (n + 1)} (ht : t ∈ S) (hu : u ∈ S) (htu : t < u) :
    pFace F i j S e t u + pFace F i j S e u t = 0 := by
  obtain ⟨h₁, -, h₃, -, h₅, -, -, h₈, -⟩ := card_filter_of_lt ht hu htu
  have hs : faceSign S u * faceSign (S.erase u) t =
      -(faceSign S t * faceSign (S.erase t) u) := by
    simp only [faceSign, h₁, h₃, h₅, h₈, ← Int.negOnePow_add, ← Int.negOnePow_succ]
    rw [Int.negOnePow_eq_iff]
    push_cast
    rw [Int.even_iff]
    ring_nf
    omega
  rw [pFace, pFace, erase_right_comm, hs, Units.neg_smul, add_neg_cancel]

/-- The composite term at `u` of the face at `t < u` cancels the face at `t` of the first factor
of the composite term at `u`. -/
private lemma pComp_add_lFace {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} (e : ℤ)
    {t u : Fin (n + 1)} (ht : t ∈ S) (hu : u ∈ S) (htu : t < u) :
    pComp F i j S e t u + lFace F i j S e u t = 0 := by
  obtain ⟨h₁, -, h₃, h₄, h₅, h₆, h₇, -, -, -, h₁₁, -⟩ := card_filter_of_lt ht hu htu
  have hs : faceSign S u * compSign S u * faceSign {s ∈ S | s < u} t =
      -(faceSign S t * faceSign (S.erase t) u * compSign (S.erase t) u) := by
    simp only [faceSign, compSign, h₁, h₃, h₄, h₅, h₆, h₇, h₁₁, ← Int.negOnePow_add,
      ← Int.negOnePow_succ]
    rw [Int.negOnePow_eq_iff]
    push_cast
    rw [Int.even_iff]
    ring_nf
    omega
  have hv : dgComp R (n := e + 1) (F i u ({s ∈ S | s < u}.erase t) (-#{s ∈ S | s < u} + 1))
        (F u j {s ∈ S | u < s} (e + #{s ∈ S | s < u})) (by omega) =
      dgComp R (F i u {s ∈ S.erase t | s < u} (-#{s ∈ S.erase t | s < u}))
        (F u j {s ∈ S.erase t | u < s} (e + 1 + #{s ∈ S.erase t | s < u})) (by omega) := by
    refine dgComp_congr F (filter_erase _ _ _).symm ?_ ?_ ?_
    · rw [filter_erase, erase_eq_of_notMem (by simp [htu.le.not_gt])]
    · rw [h₄, h₆]
      push_cast
      ring
    · rw [h₄, h₆]
      push_cast
      ring
  rw [lFace, hs, hv, pComp, Units.neg_smul, add_neg_cancel]

/-- The composite term at `t` of the face at `u > t` cancels the face at `u` of the second factor
of the composite term at `t`. -/
private lemma pComp_add_rFace {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} (e : ℤ)
    {t u : Fin (n + 1)} (ht : t ∈ S) (hu : u ∈ S) (htu : t < u) :
    pComp F i j S e u t + rFace F i j S e t u = 0 := by
  obtain ⟨h₁, h₂, h₃, -, -, -, -, h₈, h₉, h₁₀, -, h₁₂⟩ := card_filter_of_lt ht hu htu
  have hs : faceSign S t * compSign S t * (-#{s ∈ S | s < t} : ℤ).negOnePow *
        faceSign {s ∈ S | t < s} u =
      -(faceSign S u * faceSign (S.erase u) t * compSign (S.erase u) t) := by
    simp only [faceSign, compSign, h₁, h₂, h₃, h₈, h₉, h₁₀, h₁₂, ← Int.negOnePow_add,
      ← Int.negOnePow_succ]
    rw [Int.negOnePow_eq_iff]
    push_cast
    rw [Int.even_iff]
    ring_nf
    omega
  have hv : dgComp R (n := e + 1) (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
        (F t j ({s ∈ S | t < s}.erase u) (e + #{s ∈ S | s < t} + 1)) (by omega) =
      dgComp R (F i t {s ∈ S.erase u | s < t} (-#{s ∈ S.erase u | s < t}))
        (F t j {s ∈ S.erase u | t < s} (e + 1 + #{s ∈ S.erase u | s < t})) (by omega) := by
    refine dgComp_congr F ?_ (filter_erase _ _ _).symm ?_ ?_
    · rw [filter_erase, erase_eq_of_notMem (by simp [htu.le.not_gt])]
    · rw [h₉]
    · rw [h₉]
      ring
  rw [rFace, hs, hv, pComp, Units.neg_smul, add_neg_cancel]

/-- Associativity of triple composites of members of the family, up to equal sets and degrees. -/
private lemma dgComp_dgComp_congr {i t u j : Fin (n + 1)} {A A' B B' D D' : Finset (Fin (n + 1))}
    {p p' q q' r r' m m' N : ℤ} (hA : A = A') (hB : B = B') (hD : D = D') (hp : p = p')
    (hq : q = q') (hr : r = r') {h₁ : p + q = m} {h₂ : m + r = N} {h₃ : q' + r' = m'}
    {h₄ : p' + m' = N} :
    dgComp R (dgComp R (F i t A p) (F t u B q) h₁) (F u j D r) h₂ =
      dgComp R (F i t A' p') (dgComp R (F t u B' q') (F u j D' r') h₃) h₄ := by
  subst hA hB hD hp hq hr h₁ h₃
  exact dgComp_assoc R _ _ _ rfl rfl (by omega)

/-- The triple composites indexed by `(u, t)` and `(t, u)` cancel. -/
private lemma lComp_add_rComp {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} (e : ℤ)
    {t u : Fin (n + 1)} (ht : t ∈ S) (hu : u ∈ S) (htu : t < u) :
    lComp F i j S e u t + rComp F i j S e t u = 0 := by
  obtain ⟨h₁, h₂, h₃, h₄, -, -, -, -, -, -, h₁₁, h₁₂⟩ := card_filter_of_lt ht hu htu
  have h₁₃ : #{s ∈ {s ∈ S | t < s} | s < u} = #{s ∈ S | t < s ∧ s < u} := by
    rw [filter_filter]
  have e₁₂ : {s ∈ {s ∈ S | s < u} | s < t} = {s ∈ S | s < t} := by
    rw [filter_filter]
    exact filter_congr fun s _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨h.trans htu, h⟩⟩
  have e₁₃ : {s ∈ {s ∈ S | s < u} | t < s} = {s ∈ {s ∈ S | t < s} | s < u} := by
    rw [filter_filter, filter_filter]
    exact filter_congr fun s _ ↦ and_comm
  have e₁₆ : {s ∈ {s ∈ S | t < s} | u < s} = {s ∈ S | u < s} := by
    rw [filter_filter]
    exact filter_congr fun s _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨htu.trans h, h⟩⟩
  have hs : faceSign S t * compSign S t * (-#{s ∈ S | s < t} : ℤ).negOnePow *
        faceSign {s ∈ S | t < s} u * compSign {s ∈ S | t < s} u =
      -(faceSign S u * compSign S u * faceSign {s ∈ S | s < u} t *
        compSign {s ∈ S | s < u} t) := by
    simp only [faceSign, compSign, e₁₂, e₁₃, e₁₆, h₁, h₂, h₃, h₄, h₁₁, h₁₂, h₁₃,
      ← Int.negOnePow_add, ← Int.negOnePow_succ]
    rw [Int.negOnePow_eq_iff]
    push_cast
    rw [Int.even_iff]
    ring_nf
    omega
  have hv : dgComp R (n := e + 1) (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
        (dgComp R (n := e + #{s ∈ S | s < t} + 1)
          (F t u {s ∈ {s ∈ S | t < s} | s < u} (-#{s ∈ {s ∈ S | t < s} | s < u}))
          (F u j {s ∈ {s ∈ S | t < s} | u < s}
            (e + #{s ∈ S | s < t} + 1 + #{s ∈ {s ∈ S | t < s} | s < u})) (by omega))
        (by omega) =
      dgComp R
        (dgComp R (n := -#{s ∈ S | s < u} + 1)
          (F i t {s ∈ {s ∈ S | s < u} | s < t} (-#{s ∈ {s ∈ S | s < u} | s < t}))
          (F t u {s ∈ {s ∈ S | s < u} | t < s}
            (-#{s ∈ S | s < u} + 1 + #{s ∈ {s ∈ S | s < u} | s < t})) (by omega))
        (F u j {s ∈ S | u < s} (e + #{s ∈ S | s < u})) (by omega) := by
    refine (dgComp_dgComp_congr F e₁₂ e₁₃ e₁₆.symm ?_ ?_ ?_).symm
    · rw [e₁₂]
    · rw [e₁₂, h₄, h₁₃]
      push_cast
      ring
    · rw [h₄, h₁₃]
      push_cast
      ring
  rw [rComp, hs, hv, lComp, Units.neg_smul, add_neg_cancel]

/-- The terms indexed by `(t, u)` and `(u, t)` cancel. -/
private lemma pairTerm_add_pairTerm (i j : Fin (n + 1)) {S : Finset (Fin (n + 1))} (e : ℤ)
    {t u : Fin (n + 1)} (ht : t ∈ S) (hu : u ∈ S) :
    pairTerm F i j S e t u + pairTerm F i j S e u t = 0 := by
  -- Reduce to `t < u`; the face, composite and triple-composite terms cancel in four pairs.
  wlog htu : t < u generalizing t u
  · rcases (not_lt.1 htu).lt_or_eq with htu | rfl
    · rw [add_comm (pairTerm F i j S e t u)]
      exact this hu ht htu
    · simp [pairTerm]
  have key : pairTerm F i j S e t u + pairTerm F i j S e u t =
      (pFace F i j S e t u + pFace F i j S e u t) -
        (pComp F i j S e t u + lFace F i j S e u t) -
        (pComp F i j S e u t + rFace F i j S e t u) +
        (lComp F i j S e u t + rComp F i j S e t u) := by
    simp only [pairTerm, ne_eq, htu.ne, htu.ne', htu, lt_asymm htu, not_false_eq_true,
      ↓reduceIte]
    abel
  rw [key, pFace_add_pFace F e ht hu htu, pComp_add_lFace F e ht hu htu,
    pComp_add_rFace F e ht hu htu, lComp_add_rComp F e ht hu htu]
  simp

/-- **The boundary of the boundary vanishes**: substituting the right-hand side of the dg nerve
equation into the differential of its own right-hand side gives zero, for an arbitrary family. -/
private lemma sum_smul_bd_sub_eq_zero (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ) :
    ∑ t ∈ S, faceSign S t • (bd F i j (S.erase t) (e + 1) - compSign S t •
      (dgComp R (bd F i t {s ∈ S | s < t} (-#{s ∈ S | s < t} + 1))
          (F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega) +
        (-#{s ∈ S | s < t} : ℤ).negOnePow • dgComp R (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
          (bd F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t} + 1)) (by omega))) = 0 := by
  rw [sum_congr rfl fun t _ ↦ smul_bd_sub_eq_sum_pairTerm F i j S e t, ← sum_product']
  refine sum_involution (fun p _ ↦ p.swap) (fun p hp ↦ ?_) (fun p hp h ↦ ?_)
    (fun p hp ↦ mem_product.2 ⟨(mem_product.1 hp).2, (mem_product.1 hp).1⟩) fun p _ ↦ rfl
  · exact pairTerm_add_pairTerm F i j e (mem_product.1 hp).1 (mem_product.1 hp).2
  · obtain ⟨t, u⟩ := p
    intro h'
    obtain rfl : u = t := (Prod.ext_iff.1 h').1
    simp [pairTerm] at h

/-- The defect of the dg nerve equation for an arbitrary family `F`: the differential of a member
minus the right-hand side of the equation. -/
private noncomputable def defect (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (p : ℤ) :
    DGHom R (p + 1) (X i) (X j) :=
  dgDifferential R p (F i j S p) - bd F i j S (p + 1)

/-- **The differential of the boundary**: for an arbitrary family `F`, the differential of the
right-hand side of the dg nerve equation is expressed through the defects of the dg nerve equation
on the smaller sets of interior vertices. -/
private lemma dgDifferential_bd (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (e : ℤ) :
    dgDifferential R e (bd F i j S e) =
      ∑ t ∈ S, faceSign S t • (defect F i j (S.erase t) e - compSign S t •
        (dgComp R (defect F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
          (F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega) +
        (-#{s ∈ S | s < t} : ℤ).negOnePow • dgComp R (F i t {s ∈ S | s < t} (-#{s ∈ S | s < t}))
          (defect F t j {s ∈ S | t < s} (e + #{s ∈ S | s < t})) (by omega))) := by
  rw [← sub_eq_zero, ← sum_smul_bd_sub_eq_zero F i j S e, bd, map_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [map_zsmul_unit, map_sub, map_zsmul_unit, dgDifferential_dgComp]
  simp only [defect, sub_eq_add_neg, add_dgComp, neg_dgComp, dgComp_add, dgComp_neg, smul_add,
    smul_neg]
  abel

/-! ### Filling an inner horn -/

/-- The family of all morphisms indexed by vertices, interior vertices and degrees determined by
coherences, extended by zero where the coherence is not defined. -/
private noncomputable def Coherences.get (f : Coherences R X) (i j : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (p : ℤ) : DGHom R p (X i) (X j) :=
  if h : i ≤ j ∧ S ⊆ Ioo i j ∧ p + #S = 0 then f i j S p h.1 h.2.1 h.2.2 else 0

private lemma Coherences.get_eq (f : Coherences R X) {i j : Fin (n + 1)}
    {S : Finset (Fin (n + 1))} {p : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j) (hp : p + #S = 0) :
    f.get i j S p = f i j S p hij hS hp :=
  dite_eq_left ⟨hij, hS, hp⟩

/-- The right-hand side of the dg nerve equation is `TauCeti.DGNerve.bd` of any family extending
the coherences. -/
private lemma boundary_eq_bd (f : Coherences R X)
    (hF : ∀ i j S d hij hS hd, f i j S d hij hS hd = F i j S d) {i j : Fin (n + 1)}
    {S : Finset (Fin (n + 1))} {d : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j) (hd : d + #S = 0) :
    boundary R f i j S d hij hS hd = bd F i j S (d + 1) := by
  rw [boundary_def, bd, ← sum_attach S]
  refine sum_congr rfl fun t _ ↦ ?_
  have hc := card_filter_lt_add_card_filter_gt_add_one t.2
  simp only [hF]
  rw [dgComp_congr F rfl rfl rfl (q' := d + 1 + #{s ∈ S | s < t.1}) (by omega)]

/-- The defect of the dg nerve equation vanishes on coherences satisfying it. -/
private lemma defect_get_eq_zero {f : Coherences R X} {i j : Fin (n + 1)}
    {S : Finset (Fin (n + 1))} {p : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j) (hp : p + #S = 0)
    (h : dgDifferential R p (f i j S p hij hS hp) = boundary R f i j S p hij hS hp) :
    defect f.get i j S p = 0 := by
  rw [defect, sub_eq_zero, f.get_eq hij hS hp, h,
    boundary_eq_bd f.get f (fun _ _ _ _ _ _ _ ↦ (f.get_eq _ _ _).symm)]

variable (k : Fin (n + 1))

/-- The coherence indexed by `i`, `S` and `j` belongs to the horn `Λ[n, k]`: some vertex other
than `k` is missing from `{i} ∪ S ∪ {j}`. -/
private def IsHornFace (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) : Prop :=
  ∃ l, l ≠ k ∧ l ≠ i ∧ l ≠ j ∧ l ∉ S

/-- A coherence outside an inner horn joins the first vertex to the last one through all interior
vertices except possibly `k`. -/
private lemma eq_zero_and_eq_last_of_not_isHornFace {k : Fin (n + 1)} (hk₀ : 0 < k)
    (hkn : k < Fin.last n) {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} (hij : i ≤ j)
    (hS : S ⊆ Ioo i j) (h : ¬ IsHornFace k i j S) :
    i = 0 ∧ j = Fin.last n ∧ ∀ l ∈ Ioo i j, l ≠ k → l ∈ S := by
  simp only [IsHornFace, not_exists, not_and, not_not] at h
  have hi : i = 0 := by
    by_contra hi
    have h0 := hS (h 0 hk₀.ne (Ne.symm hi) fun h0 ↦ hi (le_antisymm (h0 ▸ hij) (Fin.zero_le _)))
    exact (Fin.zero_le i).not_gt (mem_Ioo.1 h0).1
  have hj : j = Fin.last n := by
    by_contra hj
    have hl := hS (h (Fin.last n) hkn.ne' (fun hl ↦ hj (le_antisymm (Fin.le_last _)
      (hl ▸ hij))) (Ne.symm hj))
    exact (Fin.le_last j).not_gt (mem_Ioo.1 hl).2
  exact ⟨hi, hj, fun l hl hlk ↦ h l hlk (mem_Ioo.1 hl).1.ne' (mem_Ioo.1 hl).2.ne⟩

open Classical in
/-- The family filling the horn `Λ[n, k]`: on the coherences of the horn it is `F`; the coherence
through all interior vertices is zero, and the coherence omitting `k` is chosen to solve the dg
nerve equation on the full set of interior vertices. -/
private noncomputable def fill (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (p : ℤ) :
    DGHom R p (X i) (X j) :=
  if IsHornFace k i j S then F i j S p
  else if S = Ioo i j then 0
  else F i j S p - faceSign (Ioo i j) k • bd F i j (Ioo i j) p

private lemma fill_of_isHornFace {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} (p : ℤ)
    (h : IsHornFace k i j S) : fill F k i j S p = F i j S p := by
  rw [fill, ite_eq_left h]

/-- The boundary of the filling family agrees with that of `F` when every coherence it involves
belongs to the horn. -/
private lemma bd_fill {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} (e : ℤ)
    (h : ∀ t ∈ S, IsHornFace k i j (S.erase t) ∧ IsHornFace k i t {s ∈ S | s < t} ∧
      IsHornFace k t j {s ∈ S | t < s}) :
    bd (fill F k) i j S e = bd F i j S e := by
  refine sum_congr rfl fun t ht ↦ ?_
  rw [fill_of_isHornFace F k _ (h t ht).1, fill_of_isHornFace F k _ (h t ht).2.1,
    fill_of_isHornFace F k _ (h t ht).2.2]

/-- The coherences involved in the boundary of a coherence of the horn belong to the horn. -/
private lemma IsHornFace.bd {k i j : Fin (n + 1)} {S : Finset (Fin (n + 1))}
    (h : IsHornFace k i j S) :
    ∀ t ∈ S, IsHornFace k i j (S.erase t) ∧ IsHornFace k i t {s ∈ S | s < t} ∧
      IsHornFace k t j {s ∈ S | t < s} := by
  obtain ⟨l, hlk, hli, hlj, hlS⟩ := h
  intro t ht
  refine ⟨⟨l, hlk, hli, hlj, fun hl ↦ hlS (mem_of_mem_erase hl)⟩,
    ⟨l, hlk, hli, ?_, fun hl ↦ hlS (mem_filter.1 hl).1⟩,
    ⟨l, hlk, ?_, hlj, fun hl ↦ hlS (mem_filter.1 hl).1⟩⟩ <;>
  · rintro rfl
    exact hlS ht

variable {k}

/-- On the full set of interior vertices, the boundary of the filling family vanishes: the
coherence omitting `k` was chosen to cancel the boundary of `F`. -/
private lemma bd_fill_Ioo (hk₀ : 0 < k) (hkn : k < Fin.last n) (e : ℤ) :
    bd (fill F k) 0 (Fin.last n) (Ioo 0 (Fin.last n)) e = 0 := by
  have hk : k ∈ Ioo 0 (Fin.last n) := mem_Ioo.2 ⟨hk₀, hkn⟩
  have hL : ∀ t ∈ Ioo 0 (Fin.last n), IsHornFace k 0 t {s ∈ Ioo 0 (Fin.last n) | s < t} :=
    fun t ht ↦ ⟨Fin.last n, hkn.ne', (hk₀.trans hkn).ne', (mem_Ioo.1 ht).2.ne', by simp⟩
  have hU : ∀ t ∈ Ioo 0 (Fin.last n),
      IsHornFace k t (Fin.last n) {s ∈ Ioo 0 (Fin.last n) | t < s} :=
    fun t ht ↦ ⟨0, hk₀.ne, (mem_Ioo.1 ht).1.ne, (hk₀.trans hkn).ne, by simp⟩
  have hnot : ¬ IsHornFace k 0 (Fin.last n) ((Ioo 0 (Fin.last n)).erase k) := by
    rintro ⟨l, hlk, hl₀, hln, hl⟩
    exact hl (mem_erase.2 ⟨hlk, mem_Ioo.2 ⟨lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hl₀),
      lt_of_le_of_ne (Fin.le_last _) hln⟩⟩)
  have hrest : ∀ t ∈ (Ioo 0 (Fin.last n)).erase k,
      IsHornFace k 0 (Fin.last n) ((Ioo 0 (Fin.last n)).erase t) := fun t ht ↦
    ⟨t, ne_of_mem_erase ht, (mem_Ioo.1 (mem_of_mem_erase ht)).1.ne',
      (mem_Ioo.1 (mem_of_mem_erase ht)).2.ne, notMem_erase _ _⟩
  rw [bd, ← add_sum_erase _ _ hk, sum_congr rfl fun t ht ↦ by
      rw [fill_of_isHornFace F k _ (hrest t ht),
        fill_of_isHornFace F k _ (hL t (mem_of_mem_erase ht)),
        fill_of_isHornFace F k _ (hU t (mem_of_mem_erase ht))],
    fill_of_isHornFace F k _ (hL k hk), fill_of_isHornFace F k _ (hU k hk), fill,
    ite_eq_right hnot, ite_eq_right fun h ↦ (erase_eq_self.1 h) hk]
  conv_lhs => rw [bd, ← add_sum_erase _ _ hk]
  simp only [smul_sub, smul_add, smul_smul, ← mul_assoc, Int.units_mul_self, one_mul, one_smul]
  abel

/-- The filling family satisfies the dg nerve equation everywhere, provided the coherences satisfy
it on the horn. -/
private lemma dgDifferential_fill (hk₀ : 0 < k) (hkn : k < Fin.last n) {f : Coherences R X}
    (heq : ∀ i j S d hij hS hd, IsHornFace k i j S →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd)
    {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} {d : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) :
    dgDifferential R d (fill f.get k i j S d) = bd (fill f.get k) i j S (d + 1) := by
  by_cases hH : IsHornFace k i j S
  · rw [fill_of_isHornFace _ _ _ hH, bd_fill _ _ _ hH.bd, f.get_eq hij hS hd,
      heq i j S d hij hS hd hH, boundary_eq_bd f.get f fun _ _ _ _ _ _ _ ↦ (f.get_eq _ _ _).symm]
  obtain ⟨rfl, rfl, hsub⟩ := eq_zero_and_eq_last_of_not_isHornFace hk₀ hkn hij hS hH
  have hk : k ∈ Ioo 0 (Fin.last n) := mem_Ioo.2 ⟨hk₀, hkn⟩
  by_cases hS' : S = Ioo 0 (Fin.last n)
  · subst hS'
    rw [fill, ite_eq_right hH, ite_eq_left rfl, map_zero, bd_fill_Ioo _ hk₀ hkn]
  -- The remaining coherence omits exactly `k`; by the choice made in `fill`, the equation for it
  -- follows from the differential of the boundary on the full set of interior vertices, all of
  -- whose other defects vanish on the horn.
  obtain rfl : S = (Ioo 0 (Fin.last n)).erase k := by
    have hkS : k ∉ S := fun hkS ↦ hS' (subset_antisymm hS fun l hl ↦
      (eq_or_ne l k).elim (· ▸ hkS) (hsub l hl))
    ext l
    simp only [mem_erase]
    exact ⟨fun hl ↦ ⟨fun h ↦ hkS (h ▸ hl), hS hl⟩, fun hl ↦ hsub l hl.2 hl.1⟩
  have hcard := card_erase_add_one hk
  have hdef : ∀ i' j' S' (p : ℤ), i' ≤ j' → S' ⊆ Ioo i' j' → p + #S' = 0 → IsHornFace k i' j' S' →
      defect f.get i' j' S' p = 0 := fun i' j' S' p hij' hS' hp hH' ↦
    defect_get_eq_zero hij' hS' hp (heq i' j' S' p hij' hS' hp hH')
  have hL : ∀ t ∈ Ioo 0 (Fin.last n), defect f.get 0 t {s ∈ Ioo 0 (Fin.last n) | s < t}
      (-#{s ∈ Ioo 0 (Fin.last n) | s < t}) = 0 := fun t ht ↦
    hdef _ _ _ _ (Fin.zero_le _) (filter_lt_subset_Ioo subset_rfl) (neg_add_cancel _)
      ⟨Fin.last n, hkn.ne', (hk₀.trans hkn).ne', (mem_Ioo.1 ht).2.ne', by simp⟩
  have hU : ∀ t ∈ Ioo 0 (Fin.last n), defect f.get t (Fin.last n)
      {s ∈ Ioo 0 (Fin.last n) | t < s} (d + #{s ∈ Ioo 0 (Fin.last n) | s < t}) = 0 :=
    fun t ht ↦ hdef _ _ _ _ (Fin.le_last _) (filter_gt_subset_Ioo subset_rfl)
      (by have := card_filter_lt_add_card_filter_gt_add_one ht; omega)
      ⟨0, hk₀.ne, (mem_Ioo.1 ht).1.ne, (hk₀.trans hkn).ne, by simp⟩
  rw [fill, ite_eq_right hH, ite_eq_right hS', map_sub, map_zsmul_unit, dgDifferential_bd,
    sum_eq_single_of_mem k hk fun t ht htk ↦ ?_, bd_fill _ _ _ fun t ht ↦ ?_]
  · rw [hL k hk, hU k hk, zero_dgComp, dgComp_zero, smul_zero, add_zero, smul_zero, sub_zero,
      smul_smul, Int.units_mul_self, one_smul, defect, sub_sub_cancel]
  · have ht' := mem_of_mem_erase ht
    exact ⟨⟨t, ne_of_mem_erase ht, (mem_Ioo.1 ht').1.ne', (mem_Ioo.1 ht').2.ne, notMem_erase _ _⟩,
      ⟨Fin.last n, hkn.ne', (hk₀.trans hkn).ne', (mem_Ioo.1 ht').2.ne', by simp⟩,
      ⟨0, hk₀.ne, (mem_Ioo.1 ht').1.ne, (hk₀.trans hkn).ne, by simp⟩⟩
  · rw [hdef _ _ _ _ (Fin.zero_le _) (erase_subset _ _)
        (by have := card_erase_add_one ht; omega)
        ⟨t, htk, (mem_Ioo.1 ht).1.ne', (mem_Ioo.1 ht).2.ne, notMem_erase _ _⟩,
      hL t ht, hU t ht]
    simp

variable (k) in
/-- **Filling an inner horn of coherences**: coherences on the objects `X` that are normalized and
satisfy the dg nerve equation on the inner horn `Λ[n, k]` are those of an `n`-simplex. -/
private noncomputable def hornExtension (hk₀ : 0 < k) (hkn : k < Fin.last n) (f : Coherences R X)
    (hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (X i))
    (heq : ∀ i j S d hij hS hd, IsHornFace k i j S →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd) :
    Simplex R C n where
  obj := X
  coh i j S d _ _ _ := fill f.get k i j S d
  coh_self i := by
    have h : IsHornFace k i i ∅ := by
      by_cases hi : i = 0
      · exact ⟨Fin.last n, hkn.ne', fun h ↦ (hk₀.trans hkn).ne' (h.trans hi), fun h ↦
          (hk₀.trans hkn).ne' (h.trans hi), notMem_empty _⟩
      · exact ⟨0, hk₀.ne, Ne.symm hi, Ne.symm hi, notMem_empty _⟩
    rw [fill_of_isHornFace _ _ _ h, f.get_eq le_rfl (empty_subset _) (by simp), hself]
  dgDifferential_coh _ _ _ _ hij hS hd := by
    rw [boundary_eq_bd (fill f.get k) _ fun _ _ _ _ _ _ _ ↦ rfl]
    exact dgDifferential_fill hk₀ hkn heq hij hS hd

/-- The filling simplex agrees with the given coherences on the horn. -/
private lemma hornExtension_coh (hk₀ : 0 < k) (hkn : k < Fin.last n) (f : Coherences R X)
    (hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (X i))
    (heq : ∀ i j S d hij hS hd, IsHornFace k i j S →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd)
    {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} {d : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) (h : IsHornFace k i j S) :
    (hornExtension k hk₀ hkn f hself heq).coh i j S d hij hS hd = f i j S d hij hS hd := by
  dsimp only [hornExtension]
  rw [fill_of_isHornFace _ _ _ h, f.get_eq hij hS hd]

/-! ### Inner horn filling -/

/-- **Inner horn filling for coherences**: normalized coherences on the objects `X` satisfying the
dg nerve equation for every coherence of the inner horn `Λ[n, k]`, that is, every coherence missing
some vertex other than `k`, are the coherences on the horn of an `n`-simplex. The two remaining
coherences are the one through all interior vertices, which can be taken to be zero, and the one
omitting `k`, which is then determined by the equation on the full set of interior vertices. -/
theorem Coherences.exists_simplex_of_horn (f : Coherences R X) {k : Fin (n + 1)} (hk₀ : 0 < k)
    (hkn : k < Fin.last n) (hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (X i))
    (heq : ∀ i j S d hij hS hd, (∃ l, l ≠ k ∧ l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd) :
    ∃ x : Simplex R C n, x.obj = X ∧ ∀ i j S d hij hS hd, (∃ l, l ≠ k ∧ l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      x.coh i j S d hij hS hd ≍ f i j S d hij hS hd :=
  ⟨hornExtension k hk₀ hkn f hself heq, rfl, fun _ _ _ _ hij hS hd h ↦
    heq_of_eq (hornExtension_coh hk₀ hkn f hself heq hij hS hd h)⟩

end DGNerve

end TauCeti
