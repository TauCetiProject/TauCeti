/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
import TauCeti.LinearAlgebra.RootSystem.ConsecutiveDifferenceBase
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Root pairings with the pairings of type `A`

The roots of a root system of type `A` are the differences `e_i - e_j`, `i ≠ j`, and the pairing of
`e_i - e_j` with the coroot of `e_k - e_l` is `δ_ik - δ_il - δ_jk + δ_jl`. This file reads the
structure of a root pairing off these two facts alone, for a root pairing whose roots are indexed,
surjectively, by a family `idx i j hij`, `i ≠ j`. This is how the restricted root systems of
`𝔰𝔩_n(ℝ)` and of `𝔰𝔩_n(ℂ)` viewed as real are recognised.

## Main definitions

* `RootPairing.typeABase`: for `n = r + 1` and roots of rank `r`, the base of consecutive
  differences `e_k - e_{k+1}`, `k < r`.

## Main results

* `RootPairing.isReduced_of_pairing_eq_delta`: a root pairing with the pairings of type `A` is
  reduced.
* `RootPairing.hasCartanType_typeABase`: the base of consecutive differences has Cartan type `A_r`.
-/

public section

open Function Module Set TauCeti

namespace RootPairing

variable {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]

section CommRing

variable [CommRing R] [Module R M] [Module R N] {P : RootPairing ι R M N}

section Delta

variable {n : Type*} [DecidableEq n] {idx : ∀ i j : n, i ≠ j → ι}

/-- **A root pairing with the pairings of type `A` is reduced**: if every root is some `e_i - e_j`
and the pairing of `e_i - e_j` with the coroot of `e_k - e_l` is `δ_ik - δ_il - δ_jk + δ_jl`, the
only roots proportional to a root `α` are `±α`, by `RootPairing.isReduced_of_pairing_comm`. -/
theorem isReduced_of_pairing_eq_delta [IsDomain R] [NeZero (2 : R)] [IsTorsionFree R M]
    (hidx : ∀ μ, ∃ i j, ∃ hij : i ≠ j, μ = idx i j hij)
    (hpair : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l), P.pairing (idx i j hij) (idx k l hkl) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) - (if j = k then 1 else 0) +
        (if j = l then 1 else 0)) :
    P.IsReduced := by
  refine isReduced_of_pairing_comm P fun μ ν ↦ ?_
  obtain ⟨i, j, hij, rfl⟩ := hidx μ
  obtain ⟨k, l, hkl, rfl⟩ := hidx ν
  rw [hpair, hpair]
  simp only [@eq_comm _ k, @eq_comm _ l]
  ring

end Delta

/-! ### The base of consecutive differences -/

section Base

variable {r : ℕ} {idx : ∀ i j : Fin (r + 1), i ≠ j → ι} {s : Fin r → ι}

/-- The pairing of the consecutive differences `e_a - e_{a+1}` and `e_b - e_{b+1}` is the
`(a, b)` entry of the Cartan matrix of type `A_r`. -/
theorem pairing_eq_cartanMatrix_A_of_pairing_eq_delta
    (hpair : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l), P.pairing (idx i j hij) (idx k l hkl) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) - (if j = k then 1 else 0) +
        (if j = l then 1 else 0))
    (hs : ∀ k, s k = idx k.castSucc k.succ Fin.castSucc_lt_succ.ne) (a b : Fin r) :
    P.pairing (s a) (s b) = (CartanMatrix.A r a b : R) := by
  rw [hs, hs, hpair]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> omega

/-- Distinct consecutive differences index distinct roots. -/
theorem injective_of_pairing_eq_delta [CharZero R]
    (hpair : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l), P.pairing (idx i j hij) (idx k l hkl) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) - (if j = k then 1 else 0) +
        (if j = l then 1 else 0))
    (hs : ∀ k, s k = idx k.castSucc k.succ Fin.castSucc_lt_succ.ne) : Injective s := by
  intro a b hab
  have h := pairing_eq_cartanMatrix_A_of_pairing_eq_delta hpair hs a b
  rw [hab, pairing_eq_cartanMatrix_A_of_pairing_eq_delta hpair hs b b] at h
  by_contra hne
  have h2 : CartanMatrix.A r b b = 2 := by simp [CartanMatrix.A]
  rw [h2] at h
  have hA : CartanMatrix.A r a b = 2 := by exact_mod_cast h.symm
  simp only [CartanMatrix.A, Matrix.of_apply, hne, ite_false] at hA
  split_ifs at hA
  norm_num at hA

end Base

end CommRing

/-! ### The base of consecutive differences over a field -/

section Field

variable [Finite ι] [Field R] [CharZero R] [Module R M] [Module R N] {P : RootPairing ι R M N}
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] {r : ℕ}
  {idx : ∀ i j : Fin (r + 1), i ≠ j → ι} {s : Fin r → ι}
  (v : Fin (r + 1) → M) (hidx : ∀ μ, ∃ i j, ∃ hij : i ≠ j, μ = idx i j hij)
  (hpair : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l), P.pairing (idx i j hij) (idx k l hkl) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) - (if j = k then 1 else 0) +
        (if j = l then 1 else 0))
  (hv : ∀ i j (hij : i ≠ j), P.root (idx i j hij) = v i - v j)
  (hs : ∀ k, s k = idx k.castSucc k.succ Fin.castSucc_lt_succ.ne) (hrank : finrank R M = r)

/-- **The base of consecutive differences** `e_k - e_{k+1}`, `k < r`, of a root system of rank `r`
whose roots are the `e_i - e_j = v i - v j`, `i ≠ j`, with the pairings of type `A`. -/
noncomputable def typeABase : P.Base :=
  have hsp := root_mem_or_neg_mem_closure_of_forall_exists_eq_sub v (fun k ↦ by rw [hs, hv])
    fun μ ↦ by
      obtain ⟨i, j, hij, rfl⟩ := hidx μ
      exact ⟨i, j, hv i j hij⟩
  Base.mk' P (range s)
    (linearIndepOn_root_range_of_root_mem_or_neg_mem_closure
      (injective_of_pairing_eq_delta hpair hs) hsp hrank) hsp

/-- The simple roots of `RootPairing.typeABase` are the consecutive differences. -/
theorem typeABase_support :
    (typeABase v hidx hpair hv hs hrank).support =
      simpleSupport (injective_of_pairing_eq_delta hpair hs) := by
  ext μ
  simp [typeABase, Base.mk']

/-- **The base of consecutive differences has Cartan type `A_r`**: its Cartan matrix is
`CartanMatrix.A r`. -/
theorem hasCartanType_typeABase :
    HasCartanType P (typeABase v hidx hpair hv hs hrank) (.A r) :=
  hasCartanType_of_pairing_eq (t := .A r) (injective_of_pairing_eq_delta hpair hs)
    (typeABase_support v hidx hpair hv hs hrank) fun a b ↦
      (pairing_eq_cartanMatrix_A_of_pairing_eq_delta hpair hs a b).trans (by simp)

end Field

end RootPairing
