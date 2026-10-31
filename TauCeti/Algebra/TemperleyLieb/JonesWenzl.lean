/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Basic
public import TauCeti.QuantumGroups.QuantumInteger.Chebyshev
import Mathlib.Tactic.LinearCombination

/-!
# Jones–Wenzl projections

The Jones–Wenzl projection `f_n` is the element of the Temperley–Lieb algebra on `n` strands
that is idempotent, has augmentation `1` (coefficient `1` on the identity diagram), and is killed
on both sides by every generator `e i`. It is the basic building block of the semisimple theory
of the Temperley–Lieb algebras: its trace is the quantum dimension `[n + 1]`, its image is the
simple object of highest weight `n`, and at a root of unity the first projection whose trace
vanishes generates the negligible ideal.

This file constructs `f_n` by Wenzl's quadratic recursion
`f_(n+2) = f_(n+1) - ([n + 1] / [n + 2]) f_(n+1) e_(n+1) f_(n+1)`,
where `f_(n+1)` is included on the first `n + 1` strands by `TauCeti.TemperleyLieb.strandIncl`,
`e_(n+1)` is the last generator, and `[k]` is the quantum integer `TauCeti.qInt R δ k`. The
division is `Ring.inverse`, so the definition makes sense over every commutative ring, and its
characteristic properties hold whenever `[1], …, [n]` are units.

Uniqueness needs no invertibility: an element killed on the right by every generator multiplies
every `x` on the left as the scalar `aug x`, because the generators and the scalars span the
algebra; two normalized elements, one killed on the left and one on the right, are therefore
equal.

## Main definitions

* `TauCeti.TemperleyLieb.jonesWenzl δ n`: the Jones–Wenzl projection on `n` strands.

## Main results

* `TauCeti.TemperleyLieb.jonesWenzl_add_two`: Wenzl's quadratic recursion.
* `TauCeti.TemperleyLieb.aug_jonesWenzl`: the augmentation of `f_n` is `1`.
* `TauCeti.TemperleyLieb.isIdempotentElem_jonesWenzl`, `TauCeti.TemperleyLieb.e_mul_jonesWenzl`,
  `TauCeti.TemperleyLieb.jonesWenzl_mul_e`: when `[1], …, [n]` are units, `f_n` is an idempotent
  killed on both sides by every generator.
* `TauCeti.TemperleyLieb.jonesWenzl_mul_strandIncl_jonesWenzl`,
  `TauCeti.TemperleyLieb.strandIncl_jonesWenzl_mul_jonesWenzl`: absorption of `f_(n+1)` by
  `f_(n+2)`.
* `TauCeti.TemperleyLieb.e_last_mul_strandIncl_jonesWenzl_mul_e_last`: the capping identity
  `e_(n+1) f_(n+1) e_(n+1) = ([n + 2] / [n + 1]) f_n e_(n+1)`.
* `TauCeti.TemperleyLieb.eq_of_e_mul_eq_zero_of_mul_e_eq_zero`: uniqueness, over any commutative
  semiring.
* `TauCeti.TemperleyLieb.eq_jonesWenzl_of_e_mul_eq_zero`,
  `TauCeti.TemperleyLieb.eq_jonesWenzl_of_mul_e_eq_zero`: the characterization of `f_n`.
* `TauCeti.TemperleyLieb.existsUnique_jonesWenzl`: existence and uniqueness of the Jones–Wenzl
  projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* H. Wenzl, *On sequences of projections*, C. R. Math. Rep. Acad. Sci. Canada 9 (1987), 5–9.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
-/

public section

namespace TauCeti.TemperleyLieb

section Uniqueness

variable {R : Type*} [CommSemiring R] {δ : R} {n : ℕ}

/-- An element killed on the right by every generator multiplies every element on the left as
the scalar given by the augmentation. -/
theorem mul_eq_aug_smul_of_mul_e_eq_zero {f : TemperleyLieb R δ n}
    (hf : ∀ i, f * e δ i = 0) (x : TemperleyLieb R δ n) : f * x = aug x • f := by
  have hx : x ∈ Algebra.adjoin R (Set.range (e δ (n := n))) := adjoin_range_e (R := R) ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [hf]
  | algebraMap r => simp [Algebra.smul_def, Algebra.commutes]
  | add x y _ _ hx hy => rw [mul_add, hx, hy, map_add, add_smul]
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, smul_mul_assoc, hy, smul_smul, map_mul]

/-- An element killed on the left by every generator multiplies every element on the right as
the scalar given by the augmentation. -/
theorem mul_eq_aug_smul_of_e_mul_eq_zero {f : TemperleyLieb R δ n}
    (hf : ∀ i, e δ i * f = 0) (x : TemperleyLieb R δ n) : x * f = aug x • f := by
  have hx : x ∈ Algebra.adjoin R (Set.range (e δ (n := n))) := adjoin_range_e (R := R) ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [hf]
  | algebraMap r => simp [Algebra.smul_def]
  | add x y _ _ hx hy => rw [add_mul, hx, hy, map_add, add_smul]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, mul_smul_comm, hx, smul_smul, map_mul, mul_comm]

/-- **Uniqueness of the Jones–Wenzl projection**, with no invertibility hypothesis: an element of
augmentation `1` killed on the left by every generator equals an element of augmentation `1`
killed on the right by every generator. -/
theorem eq_of_e_mul_eq_zero_of_mul_e_eq_zero {f g : TemperleyLieb R δ n} (hf : aug f = 1)
    (hg : aug g = 1) (hfe : ∀ i, e δ i * f = 0) (hge : ∀ i, g * e δ i = 0) : f = g :=
  calc f = aug g • f := by rw [hg, one_smul]
    _ = g * f := (mul_eq_aug_smul_of_e_mul_eq_zero hfe g).symm
    _ = aug f • g := mul_eq_aug_smul_of_mul_e_eq_zero hge f
    _ = g := by rw [hf, one_smul]

end Uniqueness

variable {R : Type*} [CommRing R]

open Ring (inverse)

variable (δ : R) in
/-- The **Jones–Wenzl projection** `f_n` on `n` strands, by Wenzl's quadratic recursion: `f_0` and
`f_1` are `1`, and `f_(m+2) = f_(m+1) - ([m + 1] / [m + 2]) f_(m+1) e_(m+1) f_(m+1)` with
`f_(m+1)` included on the first `m + 1` strands and `e_(m+1)` the last generator. Division is
`Ring.inverse`; the defining properties hold when `[1], …, [n]` are units
(`TauCeti.TemperleyLieb.existsUnique_jonesWenzl`). -/
noncomputable def jonesWenzl : (n : ℕ) → TemperleyLieb R δ n
  | 0 => 1
  | 1 => 1
  | m + 2 => strandIncl (jonesWenzl (m + 1)) -
      (qInt R δ (m + 1) * inverse (qInt R δ (m + 2))) •
        (strandIncl (jonesWenzl (m + 1)) * e δ (Fin.last m) * strandIncl (jonesWenzl (m + 1)))

variable {δ : R}

/-- The Jones–Wenzl projection on no strands is `1`. -/
@[simp]
theorem jonesWenzl_zero : jonesWenzl δ 0 = 1 := by
  rw [jonesWenzl]

/-- The Jones–Wenzl projection on one strand is `1`. -/
@[simp]
theorem jonesWenzl_one : jonesWenzl δ 1 = 1 := by
  rw [jonesWenzl]

/-- **Wenzl's recursion** for the Jones–Wenzl projections. -/
theorem jonesWenzl_add_two (m : ℕ) :
    jonesWenzl δ (m + 2) = strandIncl (jonesWenzl δ (m + 1)) -
      (qInt R δ (m + 1) * inverse (qInt R δ (m + 2))) •
        (strandIncl (jonesWenzl δ (m + 1)) * e δ (Fin.last m) *
          strandIncl (jonesWenzl δ (m + 1))) := by
  rw [jonesWenzl]

/-- The Jones–Wenzl projection on two strands is `1 - δ⁻¹ e`. -/
theorem jonesWenzl_two : jonesWenzl δ 2 = 1 - inverse δ • e δ 0 := by
  rw [jonesWenzl_add_two]
  simp

/-- The Jones–Wenzl projection has augmentation `1`: its coefficient on the identity diagram is
`1`. -/
@[simp]
theorem aug_jonesWenzl : ∀ n, aug (jonesWenzl δ n) = 1
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by simp [jonesWenzl_add_two, aug_jonesWenzl (m + 1)]

section Recursion

variable {m : ℕ}

/-- Absorption on the right, given that `f_(m+1)` is idempotent. -/
private theorem jonesWenzl_mul_strandIncl_aux (hf : IsIdempotentElem (jonesWenzl δ (m + 1))) :
    jonesWenzl δ (m + 2) * strandIncl (jonesWenzl δ (m + 1)) = jonesWenzl δ (m + 2) := by
  have hF := (hf.map (strandIncl (R := R) (δ := δ) (n := m))).eq
  conv_lhs => rw [jonesWenzl_add_two]
  rw [jonesWenzl_add_two]
  simp only [sub_mul, smul_mul_assoc, mul_assoc, hF]

/-- Absorption on the left, given that `f_(m+1)` is idempotent. -/
private theorem strandIncl_mul_jonesWenzl_aux (hf : IsIdempotentElem (jonesWenzl δ (m + 1))) :
    strandIncl (jonesWenzl δ (m + 1)) * jonesWenzl δ (m + 2) = jonesWenzl δ (m + 2) := by
  have hF := (hf.map (strandIncl (R := R) (δ := δ) (n := m))).eq
  conv_lhs => rw [jonesWenzl_add_two]
  rw [jonesWenzl_add_two, mul_sub, mul_smul_comm, ← mul_assoc, ← mul_assoc, hF]

/-- The capping identity, with the scalar written as `δ - [m + 1] / [m + 2]`, given that
`f_(m+1)` is idempotent. -/
private theorem e_last_mul_strandIncl_jonesWenzl_mul_e_last_aux
    (hf : IsIdempotentElem (jonesWenzl δ (m + 1))) :
    e δ (Fin.last (m + 1)) * strandIncl (jonesWenzl δ (m + 2)) * e δ (Fin.last (m + 1)) =
      (δ - qInt R δ (m + 1) * inverse (qInt R δ (m + 2))) •
        (strandIncl (strandIncl (jonesWenzl δ (m + 1))) * e δ (Fin.last (m + 1))) := by
  set H := strandIncl (strandIncl (jonesWenzl δ (m + 1)))
  set E : TemperleyLieb R δ (m + 3) := e δ (Fin.last (m + 1))
  have hH : H * H = H := (hf.map (strandIncl.comp strandIncl)).eq
  have hc : E * H = H * E := (commute_e_last_strandIncl_strandIncl _).eq
  have h₁ : E * H * E = δ • (H * E) := by rw [hc, mul_assoc, e_mul_self, mul_smul_comm]
  have h₂ : E * (H * e δ (Fin.last m).castSucc * H) * E = H * E :=
    calc E * (H * e δ (Fin.last m).castSucc * H) * E
        = E * H * e δ (Fin.last m).castSucc * (H * E) := by simp only [mul_assoc]
      _ = H * E * e δ (Fin.last m).castSucc * (E * H) := by rw [hc]
      _ = H * (E * e δ (Fin.last m).castSucc * E) * H := by simp only [mul_assoc]
      _ = H * E := by
        rw [e_mul_e_mul_e (Or.inr (by simp)), mul_assoc, hc, ← mul_assoc, hH]
  rw [jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul, strandIncl_e, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, h₁, h₂, sub_smul]

/-- Capping `f_(m+2)` twice with the last generator multiplies by `δ - [m + 1] / [m + 2]`, given
that `f_(m+1)` is idempotent. -/
private theorem e_last_mul_strandIncl_mul_e_last_mul_strandIncl_succ_aux
    (hf : IsIdempotentElem (jonesWenzl δ (m + 1))) :
    e δ (Fin.last (m + 1)) * strandIncl (jonesWenzl δ (m + 2)) * e δ (Fin.last (m + 1)) *
        strandIncl (jonesWenzl δ (m + 2)) =
      (δ - qInt R δ (m + 1) * inverse (qInt R δ (m + 2))) •
        (e δ (Fin.last (m + 1)) * strandIncl (jonesWenzl δ (m + 2))) ∧
    strandIncl (jonesWenzl δ (m + 2)) * e δ (Fin.last (m + 1)) *
        strandIncl (jonesWenzl δ (m + 2)) * e δ (Fin.last (m + 1)) =
      (δ - qInt R δ (m + 1) * inverse (qInt R δ (m + 2))) •
        (strandIncl (jonesWenzl δ (m + 2)) * e δ (Fin.last (m + 1))) := by
  have hHF : strandIncl (strandIncl (jonesWenzl δ (m + 1))) *
      strandIncl (jonesWenzl δ (m + 2)) = strandIncl (jonesWenzl δ (m + 2)) := by
    rw [← map_mul, strandIncl_mul_jonesWenzl_aux hf]
  have hFH : strandIncl (jonesWenzl δ (m + 2)) *
      strandIncl (strandIncl (jonesWenzl δ (m + 1))) = strandIncl (jonesWenzl δ (m + 2)) := by
    rw [← map_mul, jonesWenzl_mul_strandIncl_aux hf]
  have hkey := e_last_mul_strandIncl_jonesWenzl_mul_e_last_aux hf
  constructor
  · rw [hkey, smul_mul_assoc, ← (commute_e_last_strandIncl_strandIncl _).eq, mul_assoc, hHF]
  · rw [mul_assoc _ (e δ _), mul_assoc, hkey, mul_smul_comm, ← mul_assoc, hFH]

/-- Capping `f_(m+1)` twice with the last generator multiplies by `δ - [m] / [m + 1]`, given that
`f_m` is idempotent; this is the scalar that Wenzl's recursion inverts. -/
private theorem e_last_mul_strandIncl_mul_e_last_mul_strandIncl_aux
    (hf : IsIdempotentElem (jonesWenzl δ m)) :
    e δ (Fin.last m) * strandIncl (jonesWenzl δ (m + 1)) * e δ (Fin.last m) *
        strandIncl (jonesWenzl δ (m + 1)) =
      (δ - qInt R δ m * inverse (qInt R δ (m + 1))) •
        (e δ (Fin.last m) * strandIncl (jonesWenzl δ (m + 1))) ∧
    strandIncl (jonesWenzl δ (m + 1)) * e δ (Fin.last m) * strandIncl (jonesWenzl δ (m + 1)) *
        e δ (Fin.last m) =
      (δ - qInt R δ m * inverse (qInt R δ (m + 1))) •
        (strandIncl (jonesWenzl δ (m + 1)) * e δ (Fin.last m)) := by
  cases m with
  | zero => simp
  | succ m => exact e_last_mul_strandIncl_mul_e_last_mul_strandIncl_succ_aux hf

/-- The scalar of Wenzl's recursion inverts the scalar produced by capping. -/
private theorem qInt_mul_inverse_mul_sub_eq_one (hu : IsUnit (qInt R δ (m + 1)))
    (hv : IsUnit (qInt R δ (m + 2))) :
    qInt R δ (m + 1) * inverse (qInt R δ (m + 2)) *
      (δ - qInt R δ m * inverse (qInt R δ (m + 1))) = 1 := by
  linear_combination (-(qInt R δ m * inverse (qInt R δ (m + 2)))) *
      Ring.mul_inverse_cancel _ hu - inverse (qInt R δ (m + 2)) * qInt_add_two δ m +
    Ring.mul_inverse_cancel _ hv

/-- The inductive step of the construction: if `f_m` and `f_(m+1)` are idempotent, `f_(m+1)` is
killed by every generator, and `[m + 1]`, `[m + 2]` are units, then `f_(m+2)` is an idempotent
killed by every generator. -/
private theorem jonesWenzl_add_two_spec (hf₀ : IsIdempotentElem (jonesWenzl δ m))
    (hf : IsIdempotentElem (jonesWenzl δ (m + 1)))
    (hfe : ∀ i, e δ i * jonesWenzl δ (m + 1) = 0 ∧ jonesWenzl δ (m + 1) * e δ i = 0)
    (hu : IsUnit (qInt R δ (m + 1))) (hv : IsUnit (qInt R δ (m + 2))) :
    IsIdempotentElem (jonesWenzl δ (m + 2)) ∧
      ∀ i, e δ i * jonesWenzl δ (m + 2) = 0 ∧ jonesWenzl δ (m + 2) * e δ i = 0 := by
  obtain ⟨hEFEF, hFEFE⟩ := e_last_mul_strandIncl_mul_e_last_mul_strandIncl_aux hf₀
  have hcl := qInt_mul_inverse_mul_sub_eq_one hu hv
  have hlast : e δ (Fin.last m) * jonesWenzl δ (m + 2) = 0 ∧
      jonesWenzl δ (m + 2) * e δ (Fin.last m) = 0 := by
    rw [jonesWenzl_add_two]
    constructor
    · rw [mul_sub, mul_smul_comm, ← mul_assoc, ← mul_assoc, hEFEF, smul_smul, hcl, one_smul,
        sub_self]
    · rw [sub_mul, smul_mul_assoc, hFEFE, smul_smul, hcl, one_smul, sub_self]
  refine ⟨?_, fun i ↦ ?_⟩
  · -- `f_(m+2) * f_(m+2) = f_(m+2) * f_(m+1) - c • (f_(m+2) * e_(m+1) * f_(m+1))`.
    rw [IsIdempotentElem]
    nth_rewrite 2 [jonesWenzl_add_two]
    rw [mul_sub, mul_smul_comm, ← mul_assoc, ← mul_assoc, jonesWenzl_mul_strandIncl_aux hf,
      hlast.2, zero_mul, smul_zero, sub_zero]
  · induction i using Fin.lastCases with
    | last => exact hlast
    | cast j =>
      have h₁ : e δ j.castSucc * strandIncl (jonesWenzl δ (m + 1)) = 0 := by
        rw [← strandIncl_e, ← map_mul, (hfe j).1, map_zero]
      have h₂ : strandIncl (jonesWenzl δ (m + 1)) * e δ j.castSucc = 0 := by
        rw [← strandIncl_e, ← map_mul, (hfe j).2, map_zero]
      rw [jonesWenzl_add_two]
      constructor
      · rw [mul_sub, mul_smul_comm, ← mul_assoc, ← mul_assoc, h₁, zero_mul, zero_mul, smul_zero,
          sub_zero]
      · rw [sub_mul, smul_mul_assoc, mul_assoc, h₂, mul_zero, smul_zero, sub_zero]

/-- The Jones–Wenzl projection on `n` strands is an idempotent killed by every generator when
`[1], …, [n]` are units. -/
private theorem jonesWenzl_spec :
    ∀ n, (∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) →
      IsIdempotentElem (jonesWenzl δ n) ∧
        ∀ i, e δ i * jonesWenzl δ n = 0 ∧ jonesWenzl δ n * e δ i = 0
  | 0, _ => ⟨by simp [IsIdempotentElem], fun i ↦ i.elim0⟩
  | 1, _ => ⟨by simp [IsIdempotentElem], fun i ↦ i.elim0⟩
  | m + 2, h => by
    have h₁ := jonesWenzl_spec (m + 1) fun k hk ↦ h k (Finset.Icc_subset_Icc le_rfl (by omega) hk)
    have h₀ := jonesWenzl_spec m fun k hk ↦ h k (Finset.Icc_subset_Icc le_rfl (by omega) hk)
    exact jonesWenzl_add_two_spec h₀.1 h₁.1 h₁.2 (h _ (by simp)) (h _ (by simp))

end Recursion

variable {n : ℕ}

/-- The Jones–Wenzl projection is idempotent when `[1], …, [n]` are units. -/
theorem isIdempotentElem_jonesWenzl (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) :
    IsIdempotentElem (jonesWenzl δ n) :=
  (jonesWenzl_spec n h).1

/-- Every generator kills the Jones–Wenzl projection on the left when `[1], …, [n]` are units. -/
theorem e_mul_jonesWenzl (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) (i : Fin (n - 1)) :
    e δ i * jonesWenzl δ n = 0 :=
  ((jonesWenzl_spec n h).2 i).1

/-- Every generator kills the Jones–Wenzl projection on the right when `[1], …, [n]` are units. -/
theorem jonesWenzl_mul_e (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) (i : Fin (n - 1)) :
    jonesWenzl δ n * e δ i = 0 :=
  ((jonesWenzl_spec n h).2 i).2

/-- The Jones–Wenzl projection multiplies every element on the left as its augmentation, when
`[1], …, [n]` are units. -/
theorem jonesWenzl_mul (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k))
    (x : TemperleyLieb R δ n) : jonesWenzl δ n * x = aug x • jonesWenzl δ n :=
  mul_eq_aug_smul_of_mul_e_eq_zero (jonesWenzl_mul_e h) x

/-- The Jones–Wenzl projection multiplies every element on the right as its augmentation, when
`[1], …, [n]` are units. -/
theorem mul_jonesWenzl (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k))
    (x : TemperleyLieb R δ n) : x * jonesWenzl δ n = aug x • jonesWenzl δ n :=
  mul_eq_aug_smul_of_e_mul_eq_zero (e_mul_jonesWenzl h) x

section Recursion

variable {m : ℕ}

/-- **Absorption** on the right: `f_(m+2) f_(m+1) = f_(m+2)`, with `f_(m+1)` included on the first
`m + 1` strands, when `[1], …, [m + 1]` are units. -/
theorem jonesWenzl_mul_strandIncl_jonesWenzl
    (h : ∀ k ∈ Finset.Icc 1 (m + 1), IsUnit (qInt R δ k)) :
    jonesWenzl δ (m + 2) * strandIncl (jonesWenzl δ (m + 1)) = jonesWenzl δ (m + 2) :=
  jonesWenzl_mul_strandIncl_aux (isIdempotentElem_jonesWenzl h)

/-- **Absorption** on the left: `f_(m+1) f_(m+2) = f_(m+2)`, with `f_(m+1)` included on the first
`m + 1` strands, when `[1], …, [m + 1]` are units. -/
theorem strandIncl_jonesWenzl_mul_jonesWenzl
    (h : ∀ k ∈ Finset.Icc 1 (m + 1), IsUnit (qInt R δ k)) :
    strandIncl (jonesWenzl δ (m + 1)) * jonesWenzl δ (m + 2) = jonesWenzl δ (m + 2) :=
  strandIncl_mul_jonesWenzl_aux (isIdempotentElem_jonesWenzl h)

/-- **The capping identity** `e_(m+2) f_(m+2) e_(m+2) = ([m + 3] / [m + 2]) f_(m+1) e_(m+2)`
on `m + 3` strands, with `f_(m+2)` included on the first `m + 2` strands and `f_(m+1)` on the
first `m + 1`, when `[1], …, [m + 2]` are units. -/
theorem e_last_mul_strandIncl_jonesWenzl_mul_e_last
    (h : ∀ k ∈ Finset.Icc 1 (m + 2), IsUnit (qInt R δ k)) :
    e δ (Fin.last (m + 1)) * strandIncl (jonesWenzl δ (m + 2)) * e δ (Fin.last (m + 1)) =
      (qInt R δ (m + 3) * inverse (qInt R δ (m + 2))) •
        (strandIncl (strandIncl (jonesWenzl δ (m + 1))) * e δ (Fin.last (m + 1))) := by
  rw [e_last_mul_strandIncl_jonesWenzl_mul_e_last_aux
    (isIdempotentElem_jonesWenzl fun k hk ↦ h k (Finset.Icc_subset_Icc le_rfl (by omega) hk))]
  have h₃ : qInt R δ (m + 3) = δ * qInt R δ (m + 2) - qInt R δ (m + 1) := qInt_add_two δ (m + 1)
  congr 1
  linear_combination (-δ) * Ring.mul_inverse_cancel _ (h (m + 2) (by simp)) -
    inverse (qInt R δ (m + 2)) * h₃

end Recursion

/-- The Jones–Wenzl projection is the only element of augmentation `1` killed on the left by every
generator, when `[1], …, [n]` are units. -/
theorem eq_jonesWenzl_of_e_mul_eq_zero (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k))
    {f : TemperleyLieb R δ n} (hf : aug f = 1) (hfe : ∀ i, e δ i * f = 0) : f = jonesWenzl δ n :=
  eq_of_e_mul_eq_zero_of_mul_e_eq_zero hf (aug_jonesWenzl n) hfe (jonesWenzl_mul_e h)

/-- The Jones–Wenzl projection is the only element of augmentation `1` killed on the right by
every generator, when `[1], …, [n]` are units. -/
theorem eq_jonesWenzl_of_mul_e_eq_zero (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k))
    {f : TemperleyLieb R δ n} (hf : aug f = 1) (hfe : ∀ i, f * e δ i = 0) : f = jonesWenzl δ n :=
  (eq_of_e_mul_eq_zero_of_mul_e_eq_zero (aug_jonesWenzl n) hf (e_mul_jonesWenzl h) hfe).symm

/-- **Existence and uniqueness of the Jones–Wenzl projection.** When `[1], …, [n]` are units,
exactly one element of the Temperley–Lieb algebra on `n` strands is idempotent, has augmentation
`1`, and is killed on both sides by every generator; it is `TauCeti.TemperleyLieb.jonesWenzl`. -/
theorem existsUnique_jonesWenzl (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) :
    ∃! f : TemperleyLieb R δ n, IsIdempotentElem f ∧ aug f = 1 ∧
      ∀ i : Fin (n - 1), e δ i * f = 0 ∧ f * e δ i = 0 :=
  ⟨jonesWenzl δ n, ⟨isIdempotentElem_jonesWenzl h, aug_jonesWenzl n,
      fun i ↦ ⟨e_mul_jonesWenzl h i, jonesWenzl_mul_e h i⟩⟩,
    fun _ ⟨_, hf, hfe⟩ ↦ eq_jonesWenzl_of_e_mul_eq_zero h hf fun i ↦ (hfe i).1⟩

end TauCeti.TemperleyLieb
