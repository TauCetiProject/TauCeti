/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Hasse
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister.Basic

/-!
# The Stiefel–Whitney classes of Pfister forms

Let `K` be a field in which `2` is invertible, and write `⟨⟨a₁, …, aₙ⟩⟩` for the `n`-fold Pfister
form `⟨1, -a₁⟩ ⊗ ⋯ ⊗ ⟨1, -aₙ⟩` (`TauCeti.pfisterFormClass`). This file computes its first and
second Stiefel–Whitney classes in every fold:

* `w₁⟨⟨a⟩⟩ = (-a)` and `w₂⟨⟨a⟩⟩ = 0`;
* `w₁⟨⟨a, b⟩⟩ = 0` and `w₂⟨⟨a, b⟩⟩ = (a) ∪ (b) + (-1) ∪ (-1)`;
* `w₁` and `w₂` vanish on every Pfister form of fold at least three.

The vanishing of `w₁` from fold two on is the triviality of the discriminant
(`TauCeti.discr_pfisterFormClass`). For `w₂`, the computation rests on one general formula,
`TauCeti.sw2Class_add_mk_rankOne_mul`: for a form `q` of rank `n`,

`w₂(q ⊥ ⟨c⟩ ⊗ q) = C(n, 2) · (c) ∪ (-1) + (c) ∪ w₁(q) + w₁(q) ∪ (-1)`,

so `w₂` of `⟨1, c⟩ ⊗ q` depends on `q` only through its rank and its discriminant. Since
`⟨⟨a₁, …, aₙ⟩⟩ = ⟨1, -a₁⟩ ⊗ ⟨⟨a₂, …, aₙ⟩⟩`, the three folds above follow. The two-fold value is
consistent with the Clifford invariant: Lam's comparison
`TauCeti.brauer2EquivH2_cliffordInvariant` in rank `4` and trivial discriminant reads
`ι(c(q)) = w₂(q) + (-1) ∪ (-1)`, and `c⟨⟨a, b⟩⟩ = [(a, b)]`.

Multiplying a Pfister form of fold at least two by a scalar does not change its `w₂`
(`TauCeti.sw2Class_mk_rankOne_mul_pfisterFormClass`), so the two-fold value and the vanishing from
fold three on hold on every form similar to such a Pfister form. In fold one this fails:
`w₂(⟨c⟩ ⊗ ⟨⟨a⟩⟩) = (c) ∪ (-ca)` need not vanish.

## Main results

* `TauCeti.sw1Class_pfisterFormClass_one` and `TauCeti.sw2Class_pfisterFormClass_one`: the
  one-fold values.
* `TauCeti.sw1Class_pfisterFormClass`: `w₁` vanishes from fold two on.
* `TauCeti.sw2Class_pfisterFormClass_two`: `w₂⟨⟨a, b⟩⟩ = (a) ∪ (b) + (-1) ∪ (-1)`.
* `TauCeti.sw2Class_pfisterFormClass_of_three_le`: `w₂` vanishes from fold three on.
* `TauCeti.sw2Class_mk_rankOne_mul_pfisterFormClass`: scaling invariance from fold two on.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, GSM 67 (2005), Chapter V, §3, and
  Chapter X, §1.
-/

public section

noncomputable section

namespace TauCeti

open _root_.ContinuousCohomology

universe u

/-! ### The first class -/

section FirstClass

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- **`w₁⟨⟨a⟩⟩ = (-a)`**: the first Stiefel–Whitney class of the one-fold Pfister form
`⟨1, -a⟩`. -/
theorem sw1Class_pfisterFormClass_one (a : Fin 1 → Kˣ) :
    sw1Class (pfisterFormClass a) = kummerClass (-(a 0)) := by
  rw [pfisterFormClass_one, sw1Class_mk, sw1_fin_two]
  simp

/-- **`w₁` vanishes on Pfister forms of fold at least two**, because their discriminant is
trivial. -/
@[simp]
theorem sw1Class_pfisterFormClass {n : ℕ} (a : Fin n → Kˣ) (hn : 2 ≤ n) :
    sw1Class (pfisterFormClass a) = 0 := by
  rw [sw1Class_eq_kummerSquareClassEquiv_discr, discr_pfisterFormClass a hn, map_zero]

end FirstClass

/-! ### The second class -/

section SecondClass

variable {K : Type} [Field K] [Invertible (2 : K)]

/-- **`w₂⟨⟨a⟩⟩ = 0`**: the one-fold Pfister form `⟨1, -a⟩` has trivial second class. -/
theorem sw2Class_pfisterFormClass_one (a : Fin 1 → Kˣ) : sw2Class (pfisterFormClass a) = 0 := by
  rw [pfisterFormClass_one, sw2Class_mk_binary]
  simp

/-- **`w₂⟨⟨a, b⟩⟩ = (a) ∪ (b) + (-1) ∪ (-1)`**: the second Stiefel–Whitney class of the
two-fold Pfister form `⟨1, -a, -b, ab⟩`. -/
theorem sw2Class_pfisterFormClass_two (a b : Kˣ) :
    sw2Class (pfisterFormClass ![a, b]) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (-1)) (kummerClass (-1)) := by
  rw [← Fin.cons_self_tail ![a, b], pfisterFormClass_cons, add_mul, one_mul,
    sw2Class_add_mk_rankOne_mul, sw1Class_pfisterFormClass_one, rank_pfisterFormClass]
  simp only [Matrix.cons_val_zero, Fin.tail_def, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    pow_one, Nat.choose_self, one_smul]
  rw [← neg_one_mul a, ← neg_one_mul b]
  simp only [kummerClass_mul, map_add, LinearMap.add_apply]
  rw [cup_kummerClass_comm (-1) b]
  set N := (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
    (kummerClass (-1)) (kummerClass (-1))
  set A := (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass (-1))
  set B := (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass b) (kummerClass (-1))
  set C := (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b)
  calc _ = C + N + (N + N) + (A + A) + (B + B) := by abel
    _ = _ := by simp only [ZModModule.add_self, add_zero]

/-- **`w₂` vanishes on Pfister forms of fold at least three.** -/
@[simp]
theorem sw2Class_pfisterFormClass_of_three_le {n : ℕ} (a : Fin n → Kˣ) (hn : 3 ≤ n) :
    sw2Class (pfisterFormClass a) = 0 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn1
  have hm : 2 ≠ 2 ^ m := (Nat.pow_lt_pow_right one_lt_two (by omega : 1 < m)).ne
  obtain ⟨k, hk⟩ := Nat.prime_two.dvd_choose_pow two_ne_zero hm
  rw [← Fin.cons_self_tail a, pfisterFormClass_cons, add_mul, one_mul,
    sw2Class_add_mk_rankOne_mul, rank_pfisterFormClass, sw1Class_pfisterFormClass _ (by omega),
    hk, two_mul, add_nsmul, ZModModule.add_self]
  simp

/-- **Scaling a Pfister form of fold at least two does not change its second class**:
`w₂(⟨c⟩ ⊗ ⟨⟨a₁, …, aₙ⟩⟩) = w₂⟨⟨a₁, …, aₙ⟩⟩` for `n ≥ 2`. -/
@[simp]
theorem sw2Class_mk_rankOne_mul_pfisterFormClass (c : Kˣ) {n : ℕ} (a : Fin n → Kˣ)
    (hn : 2 ≤ n) :
    sw2Class (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => c⟩ * pfisterFormClass a) =
      sw2Class (pfisterFormClass a) := by
  have hn' : 2 ≠ 2 ^ n := (Nat.pow_lt_pow_right one_lt_two (by omega : 1 < n)).ne
  obtain ⟨k, hk⟩ := Nat.prime_two.dvd_choose_pow two_ne_zero hn'
  rw [sw2Class_mk_rankOne_mul, rank_pfisterFormClass, sw1Class_pfisterFormClass a hn, hk,
    two_mul, add_nsmul, ZModModule.add_self]
  simp

end SecondClass

end TauCeti
