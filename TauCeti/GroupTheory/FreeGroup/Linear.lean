/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.PingPong
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Free groups of countable rank are linear over `ℤ`

The matrices `A = [[1, 2], [0, 1]]` and `B = [[1, 0], [2, 1]]` freely generate a free subgroup of
rank two of `SL(2, ℤ)` (Sanov). The proof is ping-pong on `ℤ²`: every nonzero power of `A` maps
the cone `{|x| < |y|}` into the cone `{|y| < |x|}`, and every nonzero power of `B` does the
reverse. In Mathlib's vocabulary, `A` and `B` are the transvections
`Matrix.SpecialLinearGroup.transvection` with parameter `2` at the positions `(0, 1)` and
`(1, 0)`.

The conjugates `Bᵏ A B⁻ᵏ`, for `k` ranging over any set of distinct integers, also freely
generate a free subgroup. Hence every free group of countable rank embeds in `SL(2, ℤ)`, and,
comparing with the rank-two embedding, the elements `bᵏ a b⁻ᵏ` of the free group `F(a, b)`
freely generate a free subgroup of `F(a, b)`. In particular `FreeGroup (Fin n)` embeds in
`FreeGroup (Fin 2)` by sending the `i`-th generator to `bⁱ a b⁻ⁱ`.

Linearity over the Noetherian ring `ℤ` is the input from which equational Noetherianity of free
groups of finite rank follows, through the Hilbert basis theorem.

## Main results

* `TauCeti.injective_freeGroup_lift_transvection_two`: Sanov's theorem, `A` and `B` freely
  generate a free subgroup of `SL(2, ℤ)`.
* `TauCeti.injective_freeGroup_lift_conj_transvection_two`: the conjugates `Bᵏ A B⁻ᵏ` for
  distinct `k` freely generate a free subgroup of `SL(2, ℤ)`.
* `TauCeti.exists_injective_freeGroup_SL`: every free group of countable rank embeds in
  `SL(2, ℤ)`.
* `TauCeti.injective_freeGroup_lift_conj_zpow_of`: the elements `bᵏ a b⁻ᵏ` for distinct `k`
  freely generate a free subgroup of `FreeGroup (Fin 2)`.

## References

* I. N. Sanov, *A property of a representation of a free group*, Doklady Akad. Nauk SSSR 57
  (1947), 657–659.
* P. de la Harpe, *Topics in geometric group theory*, University of Chicago Press, 2000,
  §II.B.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.2 (free groups are linear, hence equationally
  Noetherian).
-/

public section

open scoped Pointwise MatrixGroups

open Matrix Matrix.SpecialLinearGroup

namespace TauCeti

/-- A nonzero power of the transvection with parameter `2` at `(i, j)` maps the cone
`{|v i| < |v j|}` of `ℤ²` into the opposite cone `{|v j| < |v i|}`. -/
private lemma transvection_two_zpow_smul_subset {i j : Fin 2} (hij : i ≠ j) {n : ℤ}
    (hn : n ≠ 0) :
    transvection hij (2 : ℤ) ^ n • {v : Fin 2 → ℤ | |v i| < |v j|} ⊆
      {v : Fin 2 → ℤ | |v j| < |v i|} := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [Set.mem_ofPred_eq] at hv ⊢
  -- The `n`-th power is the transvection with parameter `n * 2`, which adds `n * 2 * v j` to
  -- the `i`-th coordinate and leaves the `j`-th coordinate unchanged.
  have hpow : transvection hij (2 : ℤ) ^ n = transvection hij (n * 2) := by
    have h := map_zpow (transvectionHom hij) (Multiplicative.ofAdd (2 : ℤ)) n
    rw [transvectionHom_apply, transvectionHom_apply, toAdd_zpow, toAdd_ofAdd, smul_eq_mul] at h
    exact h.symm
  have hi : (transvection hij (n * 2) • v) i = v i + n * 2 * v j := by
    simp [SpecialLinearGroup.smul_def, transvection_coe, Matrix.add_mulVec,
      Matrix.single_mulVec_eq, mul_assoc]
  have hj : (transvection hij (n * 2) • v) j = v j := by
    simp [SpecialLinearGroup.smul_def, transvection_coe, Matrix.add_mulVec,
      Matrix.single_mulVec_eq, hij.symm]
  rw [hpow, hi, hj]
  have h2 : 2 * |v j| ≤ |n * 2 * v j| := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [Int.one_le_abs hn, abs_nonneg (v j)]
  have h3 : |n * 2 * v j| ≤ |v i + n * 2 * v j| + |-v i| := by
    simpa using abs_add_le (v i + n * 2 * v j) (-v i)
  rw [abs_neg] at h3
  linarith

/-- The cone `{|v 1| < |v 0|}` of `ℤ²` meets the opposite cone in no point. -/
private lemma disjoint_cones :
    Disjoint {v : Fin 2 → ℤ | |v 1| < |v 0|} {v : Fin 2 → ℤ | |v 0| < |v 1|} :=
  Set.disjoint_left.mpr fun _ h h' => by
    simp only [Set.mem_ofPred_eq] at h h'
    exact lt_asymm h h'

/-- **Sanov's theorem.** The matrices `[[1, 2], [0, 1]]` and `[[1, 0], [2, 1]]` freely generate
a free subgroup of rank two of `SL(2, ℤ)`. -/
theorem injective_freeGroup_lift_transvection_two :
    Function.Injective (FreeGroup.lift ![transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (2 : ℤ),
      transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (2 : ℤ)]) :=
  FreeGroup.injective_lift_of_ping_pong_pair ⟨![1, 0], by simp⟩ ⟨![0, 1], by simp⟩
    disjoint_cones (fun _ hn => transvection_two_zpow_smul_subset _ hn)
    (fun _ hn => transvection_two_zpow_smul_subset _ hn)

/-- For distinct integers `k i`, the conjugates `Bᵏ⁽ⁱ⁾ A B⁻ᵏ⁽ⁱ⁾` of `A = [[1, 2], [0, 1]]` by
powers of `B = [[1, 0], [2, 1]]` freely generate a free subgroup of `SL(2, ℤ)`. -/
theorem injective_freeGroup_lift_conj_transvection_two {ι : Type*} {k : ι → ℤ}
    (hk : Function.Injective k) :
    Function.Injective (FreeGroup.lift fun i =>
      transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (2 : ℤ) ^ k i *
        transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (2 : ℤ) *
          (transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (2 : ℤ) ^ k i)⁻¹) :=
  FreeGroup.injective_lift_conj_zpow_of_ping_pong ⟨![1, 0], by simp⟩ disjoint_cones
    (fun _ hn => transvection_two_zpow_smul_subset _ hn)
    (fun _ hn => transvection_two_zpow_smul_subset _ hn) hk

/-- **Free groups of countable rank are linear over `ℤ`.** Every free group on a countable basis
embeds in `SL(2, ℤ)`. -/
theorem exists_injective_freeGroup_SL (ι : Type*) [Countable ι] :
    ∃ f : FreeGroup ι →* SL(2, ℤ), Function.Injective f := by
  obtain ⟨k, hk⟩ := Countable.exists_injective_nat ι
  exact ⟨_, injective_freeGroup_lift_conj_transvection_two (Nat.cast_injective.comp hk)⟩

/-- For distinct integers `k i`, the elements `bᵏ⁽ⁱ⁾ a b⁻ᵏ⁽ⁱ⁾` of the free group `F(a, b)` freely
generate a free subgroup. In particular `FreeGroup (Fin n)` embeds in `FreeGroup (Fin 2)` by
sending the `i`-th generator to `bⁱ a b⁻ⁱ`. -/
theorem injective_freeGroup_lift_conj_zpow_of {ι : Type*} {k : ι → ℤ}
    (hk : Function.Injective k) :
    Function.Injective (FreeGroup.lift fun i =>
      (FreeGroup.of (1 : Fin 2) ^ k i * FreeGroup.of 0 * (FreeGroup.of 1 ^ k i)⁻¹)) := by
  -- Composing with Sanov's embedding gives the conjugate family in `SL(2, ℤ)`.
  refine Function.Injective.of_comp (f := FreeGroup.lift
    ![transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (2 : ℤ),
      transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (2 : ℤ)]) ?_
  rw [← MonoidHom.coe_comp]
  convert injective_freeGroup_lift_conj_transvection_two hk using 2
  ext i
  simp

end TauCeti
