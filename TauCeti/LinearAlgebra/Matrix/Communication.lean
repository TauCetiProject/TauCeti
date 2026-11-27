/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import TauCeti.LinearAlgebra.Matrix.Metzler

import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible

/-!
# Communication of states for a rate matrix

For a square matrix `B`, read the entry `B i j` with `i ≠ j` as the rate of jumps from `i` to `j`.
State `i` **leads to** state `j` (`Matrix.LeadsTo`) when `j` is reached from `i` by a finite chain
of steps `a → b` with `a ≠ b` and `0 < B a b`; the empty chain is allowed, so every state leads to
itself. The diagonal of `B` plays no role. The matrix is an **irreducible generator**
(`Matrix.IsIrreducibleGenerator`) when every state leads to every state. For a Q-matrix these are
the relation "i leads to j" and the irreducibility of the class structure of a continuous-time
Markov chain on finitely many states.

Unlike Mathlib's `Matrix.IsIrreducible`, these notions ask nothing of the signs of the entries
and accept chains of length zero, so they apply directly to a Q-matrix, whose diagonal is
nonpositive. The two are related through the uniformized matrix `1 + r⁻¹ • Q`, which is entrywise
nonnegative for a rate `r > 0` with `-Q i i ≤ r` for every `i`: then `Q` is an irreducible
generator if and only if `1 + r⁻¹ • Q` is irreducible
(`Matrix.IsQMatrix.isIrreducible_one_add_inv_smul_iff`). On two or more states the closed chain
through each state that irreducibility asks for comes from the off-diagonal entries of `Q`
(`Matrix.IsIrreducibleGenerator.transGen_self`); on one state the only Q-matrix is `0` and
`1 + r⁻¹ • 0 = 1` has a positive diagonal entry.

For a matrix whose off-diagonal entries are nonnegative, being an irreducible generator is the
strong connectivity of the directed graph of its positive off-diagonal entries, which
`Matrix.forall_reflTransGen_ne_and_pos_iff` characterizes by the absence of a disconnecting cut.

## Main definitions

* `Matrix.LeadsTo B i j`: `j` is reached from `i` through positive off-diagonal entries of `B`.
* `Matrix.IsIrreducibleGenerator B`: every state leads to every state.

## Main results

* `Matrix.leadsTo_iff_reflTransGen_pos`: steps along positive diagonal entries may be allowed in
  the chains without changing `Matrix.LeadsTo`.
* `Matrix.LeadsTo.mono`: `Matrix.LeadsTo` only depends on which off-diagonal entries are positive.
* `Matrix.leadsTo_transpose_iff`, `Matrix.leadsTo_add_diagonal_iff`, `Matrix.leadsTo_smul_iff`,
  `Matrix.leadsTo_one_add_smul_iff`: `Matrix.LeadsTo` is unchanged by transposition (with the
  states swapped), by adding a diagonal matrix and by multiplication by a positive scalar.
* `Matrix.LeadsTo.mem_of_mem`: a set of states that no positive off-diagonal entry leaves is closed
  under `Matrix.LeadsTo`.
* `Matrix.isIrreducible_iff_isIrreducibleGenerator`: on two or more states, an entrywise
  nonnegative matrix is irreducible if and only if it is an irreducible generator.
* `Matrix.IsIrreducibleGenerator.transGen_self`: on two or more states, an irreducible generator
  has a closed chain of positive off-diagonal entries through every state.
* `Matrix.one_add_inv_smul_nonneg_iff`: for `r > 0`, the matrix `1 + r⁻¹ • B` is entrywise
  nonnegative if and only if `B` is Metzler with `-B i i ≤ r` for every `i`.
* `Matrix.IsMetzler.isIrreducible_one_add_inv_smul_iff`,
  `Matrix.IsQMatrix.isIrreducible_one_add_inv_smul_iff`: under that condition, `B` is an
  irreducible generator if and only if `1 + r⁻¹ • B` is irreducible, for a Metzler matrix on two
  or more states and for a Q-matrix on any finite set of states.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Chapter 3, for the class
  structure of a continuous-time chain.
* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, 2017, Section 20.1, for the matrix `1 + r⁻¹ • Q`.
-/

public section

open Relation

namespace Matrix

variable {n R R' : Type*}

section LeadsTo

variable [Zero R] [LT R] {B C : Matrix n n R} {i j k : n}

/-- State `i` **leads to** state `j` for the matrix `B` when `j` is reached from `i` by a finite
chain, possibly empty, of steps `a → b` with `a ≠ b` and `0 < B a b`. The diagonal of `B` plays no
role. -/
def LeadsTo (B : Matrix n n R) (i j : n) : Prop :=
  ReflTransGen (fun a b ↦ a ≠ b ∧ 0 < B a b) i j

/-- A square matrix is an **irreducible generator** when every state leads to every state through
its positive off-diagonal entries. -/
def IsIrreducibleGenerator (B : Matrix n n R) : Prop :=
  ∀ i j, B.LeadsTo i j

theorem leadsTo_iff : B.LeadsTo i j ↔ ReflTransGen (fun a b ↦ a ≠ b ∧ 0 < B a b) i j :=
  Iff.rfl

theorem isIrreducibleGenerator_iff : B.IsIrreducibleGenerator ↔ ∀ i j, B.LeadsTo i j :=
  Iff.rfl

@[refl, simp]
theorem LeadsTo.refl (B : Matrix n n R) (i : n) : B.LeadsTo i i :=
  ReflTransGen.refl

@[trans]
theorem LeadsTo.trans (hij : B.LeadsTo i j) (hjk : B.LeadsTo j k) : B.LeadsTo i k :=
  ReflTransGen.trans hij hjk

/-- A positive entry is a step of the relation `Matrix.LeadsTo`; a positive diagonal entry is the
empty chain. -/
theorem leadsTo_of_pos (h : 0 < B i j) : B.LeadsTo i j := by
  rcases eq_or_ne i j with rfl | hij
  · exact LeadsTo.refl B i
  · exact ReflTransGen.single ⟨hij, h⟩

/-- Steps along positive diagonal entries may be allowed in the chains of `Matrix.LeadsTo`. -/
theorem leadsTo_iff_reflTransGen_pos : B.LeadsTo i j ↔ ReflTransGen (fun a b ↦ 0 < B a b) i j := by
  refine ⟨fun h ↦ ReflTransGen.mono (fun _ _ h ↦ h.2) _ _ h, fun h ↦ ?_⟩
  induction h with
  | refl => exact LeadsTo.refl B i
  | tail _ hbc ih => exact ih.trans (leadsTo_of_pos hbc)

/-- A set of states that no positive off-diagonal entry leaves contains every state that one of
its members leads to. In particular a state whose row has no positive off-diagonal entry, an
absorbing state of a Q-matrix, leads to no other state. -/
theorem LeadsTo.mem_of_mem {s : Set n} (hs : ∀ a ∈ s, ∀ b, a ≠ b → 0 < B a b → b ∈ s)
    (h : B.LeadsTo i j) (hi : i ∈ s) : j ∈ s := by
  induction h with
  | refl => exact hi
  | tail _ hbc ih => exact hs _ ih _ hbc.1 hbc.2

/-- `Matrix.LeadsTo` only depends on which off-diagonal entries are positive. -/
theorem LeadsTo.mono [Zero R'] [LT R'] {C : Matrix n n R'}
    (hBC : ∀ a b, a ≠ b → 0 < B a b → 0 < C a b) (h : B.LeadsTo i j) : C.LeadsTo i j :=
  ReflTransGen.mono (fun a b (hab : a ≠ b ∧ 0 < B a b) ↦ ⟨hab.1, hBC a b hab.1 hab.2⟩) _ _ h

theorem IsIrreducibleGenerator.mono [Zero R'] [LT R'] {C : Matrix n n R'}
    (hBC : ∀ a b, a ≠ b → 0 < B a b → 0 < C a b) (h : B.IsIrreducibleGenerator) :
    C.IsIrreducibleGenerator :=
  fun i j ↦ (h i j).mono hBC

/-- A state leads to another for the transposed matrix exactly when the second leads to the first
for the matrix itself. -/
@[simp]
theorem leadsTo_transpose_iff : Bᵀ.LeadsTo i j ↔ B.LeadsTo j i := by
  rw [leadsTo_iff, leadsTo_iff, ← reflTransGen_swap]
  exact Iff.of_eq (congrArg (ReflTransGen · j i) (by ext a b; simp [ne_comm]))

@[simp]
theorem isIrreducibleGenerator_transpose_iff :
    Bᵀ.IsIrreducibleGenerator ↔ B.IsIrreducibleGenerator := by
  simp only [isIrreducibleGenerator_iff, leadsTo_transpose_iff]
  exact forall_comm

/-- On at most one state every matrix is an irreducible generator. -/
theorem isIrreducibleGenerator_of_subsingleton [Subsingleton n] (B : Matrix n n R) :
    B.IsIrreducibleGenerator :=
  fun i j ↦ Subsingleton.elim i j ▸ LeadsTo.refl B i

/-- On two or more states, an irreducible generator has a closed chain of positive off-diagonal
entries, of positive length, through every state. -/
theorem IsIrreducibleGenerator.transGen_self [Nontrivial n] (h : B.IsIrreducibleGenerator)
    (i : n) : TransGen (fun a b ↦ a ≠ b ∧ 0 < B a b) i i := by
  obtain ⟨j, hji⟩ := exists_ne i
  obtain (rfl | hij) := reflTransGen_iff_eq_or_transGen.mp (h i j)
  · exact absurd rfl hji
  obtain (rfl | hji') := reflTransGen_iff_eq_or_transGen.mp (h j i)
  · exact absurd rfl hji
  exact hij.trans hji'

end LeadsTo

section AddDiagonal

variable [AddZeroClass R] [LT R] [DecidableEq n] {B : Matrix n n R} {i j : n}

/-- Adding a diagonal matrix does not change `Matrix.LeadsTo`. -/
@[simp]
theorem leadsTo_add_diagonal_iff (d : n → R) : (B + diagonal d).LeadsTo i j ↔ B.LeadsTo i j := by
  have hoff : ∀ a b, a ≠ b → (B + diagonal d) a b = B a b := fun a b hab ↦ by
    rw [Matrix.add_apply, diagonal_apply_ne d hab, add_zero]
  exact ⟨LeadsTo.mono fun a b hab h ↦ hoff a b hab ▸ h,
    LeadsTo.mono fun a b hab h ↦ (hoff a b hab).symm ▸ h⟩

@[simp]
theorem isIrreducibleGenerator_add_diagonal_iff (d : n → R) :
    (B + diagonal d).IsIrreducibleGenerator ↔ B.IsIrreducibleGenerator :=
  forall₂_congr fun _ _ ↦ leadsTo_add_diagonal_iff d

end AddDiagonal

section Smul

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {B : Matrix n n R} {i j : n}
  {c : R}

/-- Multiplying by a positive scalar does not change `Matrix.LeadsTo`. -/
theorem leadsTo_smul_iff (hc : 0 < c) : (c • B).LeadsTo i j ↔ B.LeadsTo i j :=
  ⟨LeadsTo.mono fun _ _ _ h ↦ (mul_pos_iff_of_pos_left hc).mp h,
    LeadsTo.mono fun _ _ _ h ↦ mul_pos hc h⟩

theorem isIrreducibleGenerator_smul_iff (hc : 0 < c) :
    (c • B).IsIrreducibleGenerator ↔ B.IsIrreducibleGenerator :=
  forall₂_congr fun _ _ ↦ leadsTo_smul_iff hc

/-- For `c > 0`, a state leads to another for `1 + c • B` exactly when it does for `B`. This is
the case of the uniformized matrix `1 + r⁻¹ • Q` of a Q-matrix at a rate `r > 0`. -/
theorem leadsTo_one_add_smul_iff [DecidableEq n] (hc : 0 < c) :
    (1 + c • B).LeadsTo i j ↔ B.LeadsTo i j := by
  rw [← diagonal_one, add_comm, leadsTo_add_diagonal_iff, leadsTo_smul_iff hc]

end Smul

section Nonneg

variable [Ring R] [LinearOrder R] [Nontrivial n] {A : Matrix n n R}

/-- On two or more states, an entrywise nonnegative matrix is irreducible in the sense of
`Matrix.IsIrreducible` if and only if it is an irreducible generator: the closed chains of
positive length that irreducibility asks for come from the off-diagonal entries. -/
theorem isIrreducible_iff_isIrreducibleGenerator (hA : ∀ i j, 0 ≤ A i j) :
    A.IsIrreducible ↔ A.IsIrreducibleGenerator := by
  rw [isIrreducible_iff_forall_transGen hA]
  refine ⟨fun h i j ↦ leadsTo_iff_reflTransGen_pos.mpr (h i j).to_reflTransGen, fun h i j ↦ ?_⟩
  have hmono := TransGen.mono (r := fun a b ↦ a ≠ b ∧ 0 < A a b) fun _ _ h ↦ h.2
  rcases eq_or_ne i j with rfl | hij
  · exact hmono _ _ (h.transGen_self i)
  · obtain (rfl | h') := reflTransGen_iff_eq_or_transGen.mp (h i j)
    · exact absurd rfl hij
    · exact hmono _ _ h'

end Nonneg

section Uniformized

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq n] {B : Matrix n n R}
  {r : R}

/-- For a rate `r > 0`, the matrix `1 + r⁻¹ • B` is entrywise nonnegative if and only if `B` is
Metzler and every diagonal entry of `B` is at least `-r`. -/
theorem one_add_inv_smul_nonneg_iff (hr : 0 < r) :
    (∀ i j, 0 ≤ (1 + r⁻¹ • B) i j) ↔ B.IsMetzler ∧ ∀ i, -B i i ≤ r := by
  have hdiag (i : n) : 0 ≤ (1 + r⁻¹ • B) i i ↔ -B i i ≤ r := by
    simp only [Matrix.add_apply, one_apply_eq, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_le_mul_iff_of_pos_left hr, mul_add, mul_inv_cancel_left₀ hr.ne']
    constructor <;> intro h <;> linarith
  have hoff {i j : n} (hij : i ≠ j) : 0 ≤ (1 + r⁻¹ • B) i j ↔ 0 ≤ B i j := by
    simp [one_apply_ne hij, mul_nonneg_iff_of_pos_left (inv_pos.mpr hr)]
  refine ⟨fun h ↦ ⟨isMetzler_iff.mpr fun i j hij ↦ (hoff hij).mp (h i j),
    fun i ↦ (hdiag i).mp (h i i)⟩,
    fun ⟨hB, hd⟩ i j ↦ ?_⟩
  rcases eq_or_ne i j with rfl | hij
  · exact (hdiag i).mpr (hd i)
  · exact (hoff hij).mpr (hB.apply_nonneg hij)

/-- **Irreducible generators and irreducible uniformized matrices.** Let `B` be a Metzler matrix
on two or more states and `r > 0` a rate with `-B i i ≤ r` for every `i`, so that `1 + r⁻¹ • B` is
entrywise nonnegative. Then `B` is an irreducible generator if and only if `1 + r⁻¹ • B` is
irreducible. -/
theorem IsMetzler.isIrreducible_one_add_inv_smul_iff [Nontrivial n] (hB : B.IsMetzler)
    (hr : 0 < r) (hdiag : ∀ i, -B i i ≤ r) :
    (1 + r⁻¹ • B).IsIrreducible ↔ B.IsIrreducibleGenerator := by
  rw [isIrreducible_iff_isIrreducibleGenerator ((one_add_inv_smul_nonneg_iff hr).mpr ⟨hB, hdiag⟩)]
  exact forall₂_congr fun _ _ ↦ leadsTo_one_add_smul_iff (inv_pos.mpr hr)

/-- **Irreducible Q-matrices and irreducible uniformized matrices.** Let `Q` be a Q-matrix and
`r > 0` a rate with `-Q i i ≤ r` for every `i`, so that `1 + r⁻¹ • Q` is entrywise nonnegative.
Then `Q` is an irreducible generator if and only if `1 + r⁻¹ • Q` is irreducible. On one state
`Q = 0` and `1 + r⁻¹ • Q = 1`. -/
theorem IsQMatrix.isIrreducible_one_add_inv_smul_iff [Fintype n] {Q : Matrix n n R}
    (hQ : Q.IsQMatrix) (hr : 0 < r) (hdiag : ∀ i, -Q i i ≤ r) :
    (1 + r⁻¹ • Q).IsIrreducible ↔ Q.IsIrreducibleGenerator := by
  rcases subsingleton_or_nontrivial n with hn | hn
  · refine iff_of_true ?_ (isIrreducibleGenerator_of_subsingleton Q)
    rw [hQ.eq_zero, smul_zero, add_zero, isIrreducible_iff_forall_transGen fun i j ↦ ?_]
    · intro i j
      obtain rfl := Subsingleton.elim i j
      exact TransGen.single (by simp)
    · rw [Matrix.one_apply]
      split_ifs <;> simp
  · exact hQ.isMetzler.isIrreducible_one_add_inv_smul_iff hr hdiag

end Uniformized

section Examples

/-! ### Examples

The two-state Q-matrix `[[-1, 1], [2, -2]]` is an irreducible generator, and so its uniformized
matrix at the rate `2` is irreducible. In `[[-1, 1], [0, 0]]` the second state is absorbing and
does not lead to the first. In the three-state cycle with rates `1` from `0` to `1`, from `1` to
`2` and from `2` to `0`, every state leads to every state although the entry from `0` to `2` is
zero. -/

example : (!![-1, 1; 2, -2] : Matrix (Fin 2) (Fin 2) ℝ).IsQMatrix :=
  ⟨isMetzler_iff.mpr (by simp [Fin.forall_fin_two]), by simp [Fin.forall_fin_two, Fin.sum_univ_two]⟩

example : (!![-1, 1; 2, -2] : Matrix (Fin 2) (Fin 2) ℝ).IsIrreducibleGenerator := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [LeadsTo.refl _ _, leadsTo_of_pos (by simp), leadsTo_of_pos (by simp), LeadsTo.refl _ _]

example : (1 + (2 : ℝ)⁻¹ • !![-1, 1; 2, -2] : Matrix (Fin 2) (Fin 2) ℝ).IsIrreducible := by
  refine (IsQMatrix.isIrreducible_one_add_inv_smul_iff
    ⟨isMetzler_iff.mpr (by simp [Fin.forall_fin_two]), by simp [Fin.forall_fin_two,
      Fin.sum_univ_two]⟩ two_pos (by simp [Fin.forall_fin_two])).mpr fun i j ↦ ?_
  fin_cases i <;> fin_cases j
  exacts [LeadsTo.refl _ _, leadsTo_of_pos (by simp), leadsTo_of_pos (by simp), LeadsTo.refl _ _]

example : ¬ (!![-1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).LeadsTo 1 0 := fun h ↦ by
  have := h.mem_of_mem (s := {1}) (fun a ha b hab hpos ↦ by
    obtain rfl := Set.mem_singleton_iff.mp ha
    fin_cases b <;> simp_all) rfl
  simp at this

example : (!![-1, 1, 0; 0, -1, 1; 1, 0, -1] : Matrix (Fin 3) (Fin 3) ℝ).IsIrreducibleGenerator := by
  have h01 : (!![-1, 1, 0; 0, -1, 1; 1, 0, -1] : Matrix (Fin 3) (Fin 3) ℝ).LeadsTo 0 1 :=
    leadsTo_of_pos (by simp)
  have h12 : (!![-1, 1, 0; 0, -1, 1; 1, 0, -1] : Matrix (Fin 3) (Fin 3) ℝ).LeadsTo 1 2 :=
    leadsTo_of_pos (by simp)
  have h20 : (!![-1, 1, 0; 0, -1, 1; 1, 0, -1] : Matrix (Fin 3) (Fin 3) ℝ).LeadsTo 2 0 :=
    leadsTo_of_pos (by simp)
  intro i j
  fin_cases i <;> fin_cases j
  exacts [LeadsTo.refl _ _, h01, h01.trans h12, h12.trans h20, LeadsTo.refl _ _, h12, h20,
    h20.trans h01, LeadsTo.refl _ _]

end Examples

end Matrix
