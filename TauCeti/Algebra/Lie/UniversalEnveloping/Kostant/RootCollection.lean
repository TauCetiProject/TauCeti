/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.DividedPowers.RootString.Signed
public import TauCeti.LinearAlgebra.RootSystem.Finite.DoubleChain
public import Mathlib.Algebra.Lie.BaseChange

/-!
# Collection of independent Chevalley root divided powers

In the rational enveloping algebra of the integral Chevalley Lie algebra, independent
root vectors commute when their sum is absent. When their root strings have length at
most two, their divided powers collect with integer coefficients. The three possible
noncommuting configurations are a central bracket and the two orientations of a double
chain. The cocharacter lattice is the full lattice of the supplied root pairing; no
irreducibility or integral splitting of its central directions is required.

These cases exhaust independent pairs if the sum of the lower and upper string
lengths is at most two for every independent pair. Indeed, if `γ = α + β` is a root,
split according to the presence of `α + γ` and `β + γ`. In a double chain the given
length bound excludes the other double root by `Finite.DoubleChain`. The formulas
require only the local bound on the string actually used. The versions with
`eq_swap_add` in their names isolate the leading swapped product and bound every
correction's total divided-power degree strictly below the input degree.

The formulas use the native Chevalley root brackets and string coefficients. The
associative identities are the central-commutator rule in
`TauCeti.RingTheory.DividedPowers.NormalOrdering` and the signed double-chain rule in
`TauCeti.RingTheory.DividedPowers.RootString.Signed`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

open scoped TensorProduct
open TauCeti.Associative Finset

namespace RootPairing.ChevalleyLieAlgebra

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite ι]
  {P : RootPairing ι ℤ X Y} (c : P.ChevalleyConstants)

local notation "Lℚ" => ℚ ⊗[ℤ] ChevalleyLieAlgebra c
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ Lℚ
local notation "e" => (fun i : ι ↦ _root_.UniversalEnvelopingAlgebra.ι ℚ
  ((1 : ℚ) ⊗ₜ[ℤ] root c i))

private theorem root_mul_root {α β γ : ι}
    (hγ : P.root γ = P.root α + P.root β) :
    e α * e β = e β * e α + c.structConst α β • e γ := by
  apply TauCeti.UniversalEnvelopingAlgebra.mul_eq_mul_add_zsmul_of_lie_eq (RingHom.id U)
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
    root_lie_root_of_root_eq_add c hγ, TensorProduct.tmul_smul]

private theorem commute_root {α β : ι}
    (hnot : P.root α + P.root β ∉ Set.range P.root)
    (hne : P.root α + P.root β ≠ 0) : Commute (e α) (e β) := by
  apply TauCeti.UniversalEnvelopingAlgebra.commute_of_lie_eq_zero (RingHom.id U)
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
    root_lie_root_of_notMem_of_add_ne_zero c hnot hne, TensorProduct.tmul_zero]

/-- Nonopposite root vectors whose sum is absent have commuting divided powers. No
string-length bound is needed, so this applies to independent roots in every type and
to pairs in different components. -/
theorem commute_dividedPower_root {α β : ι}
    (hnot : P.root α + P.root β ∉ Set.range P.root)
    (hne : P.root α + P.root β ≠ 0) (m n : ℕ) :
    Commute (dividedPower m (e α)) (dividedPower n (e β)) :=
  commute_dividedPower_dividedPower (commute_root c hnot hne) m n

/-- If neither double root exists, collection has just the sum-root factor. Its coefficient
is the corresponding power of the integral Chevalley bracket coefficient. -/
theorem dividedPower_root_mul_of_no_double {α β γ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hαγ : P.root α + P.root γ ∉ Set.range P.root)
    (hβγ : P.root β + P.root γ ∉ Set.range P.root) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      ∑ k ∈ range (min m n + 1), (c.structConst α β ^ k) •
        (dividedPower (n - k) (e β) * dividedPower k (e γ) *
          dividedPower (m - k) (e α)) := by
  let := c.isReduced
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hαγ0 : P.root α + P.root γ ≠ 0 := by
    intro h
    have := hli.eq_zero_of_pair (s := (2 : ℤ)) (t := 1)
      (by rw [hγ] at h; simpa [two_smul, add_assoc] using h)
    norm_num at this
  have hβγ0 : P.root β + P.root γ ≠ 0 := by
    intro h
    have := hli.eq_zero_of_pair (s := (1 : ℤ)) (t := 2)
      (by rw [hγ] at h; simpa [two_smul, add_assoc, add_left_comm] using h)
    norm_num at this
  rw [dividedPower_mul_dividedPower_of_commutator_eq (root_mul_root c hγ)
    ((commute_root c hαγ hαγ0).smul_right _) ((commute_root c hβγ hβγ0).smul_right _)]
  apply sum_congr rfl
  intro k _
  simp only [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc]

/-- The leading term in central-bracket collection is the swapped product; every
correction has strictly smaller total divided-power degree. -/
theorem dividedPower_root_mul_eq_swap_add_of_no_double {α β γ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hαγ : P.root α + P.root γ ∉ Set.range P.root)
    (hβγ : P.root β + P.root γ ∉ Set.range P.root) (m n : ℕ) :
    (dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ k ∈ (range (min m n + 1)).erase 0, (c.structConst α β ^ k) •
          (dividedPower (n - k) (e β) * dividedPower k (e γ) *
            dividedPower (m - k) (e α))) ∧
      ∀ k ∈ (range (min m n + 1)).erase 0, (n - k) + k + (m - k) < m + n := by
  constructor
  · rw [dividedPower_root_mul_of_no_double c hγ hαγ hβγ]
    simpa only [pow_zero, dividedPower_zero, mul_one, one_smul, Nat.sub_zero] using
      (add_sum_erase (range (min m n + 1))
        (fun k ↦ (c.structConst α β ^ k) •
          (dividedPower (n - k) (e β) * dividedPower k (e γ) *
            dividedPower (m - k) (e α))) (by simp : 0 ∈ range (min m n + 1))).symm
  · intro k hk
    obtain ⟨hne, hk⟩ := mem_erase.mp hk
    rw [mem_range] at hk
    omega

section DoubleChain

private theorem double_chain_constants {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) :
    (c.structConst α β).natAbs = 1 ∧
      c.structConst α γ = 2 * (c.structConst α γ).sign := by
  have hli := P.linearIndependent_of_root_eq_add_of_root_eq_add hγ hδ
  have hbot := P.chainBotCoeff_eq_zero_of_chainBotCoeff_add_chainTopCoeff_le_two hγ hδ hlen
  have hbotγ := P.chainBotCoeff_of_add hli (by simpa only [add_comm] using hγ)
  have h₁ := c.natAbs_structConst hγ
  have h₂ := c.natAbs_structConst hδ
  rw [hbot] at h₁
  rw [hbotγ, hbot] at h₂
  norm_num at h₂
  constructor
  · exact h₁
  · have h := Int.sign_mul_natAbs (c.structConst α γ)
    rw [h₂] at h
    simpa [mul_comm] using h.symm

private theorem double_chain_commute {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) :
    Commute (e α) (e δ) ∧ Commute (e β) (e γ) := by
  have hli := P.linearIndependent_of_root_eq_add_of_root_eq_add hγ hδ
  have hbot := P.chainBotCoeff_eq_zero_of_chainBotCoeff_add_chainTopCoeff_le_two hγ hδ hlen
  have htop := P.chainTopCoeff_eq_two_of_chainTopCoeff_le_two hγ hδ (by omega)
  constructor
  · apply commute_root c
      (P.root_add_root_notMem_range_root_of_chainTopCoeff_le_two hγ hδ htop.le)
    intro h
    have := hli.eq_zero_of_pair (s := (3 : ℤ)) (t := 1)
      (by convert h using 1; rw [hδ, hγ]; module)
    norm_num at this
  · apply commute_root c
      (P.root_add_root_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
        hγ hbot htop)
    intro h
    have := hli.eq_zero_of_pair (s := (1 : ℤ)) (t := 2)
      (by rw [hγ] at h; simpa [two_smul, add_assoc, add_left_comm] using h)
    norm_num at this

/-- Collection along `β, α + β, 2α + β`, with the full integral Chevalley table.
The double-root coefficient is the product of the first bracket sign and the sign of
the second bracket, whose absolute value is two. -/
theorem dividedPower_root_mul_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      ∑ p ∈ chainLeTwoIndex m n,
        (c.structConst α β ^ p.1 *
          (c.structConst α β * (c.structConst α γ).sign) ^ p.2) •
          (dividedPower (n - p.1 - p.2) (e β) * dividedPower p.1 (e γ) *
            dividedPower p.2 (e δ) * dividedPower (m - p.1 - 2 * p.2) (e α)) := by
  have hconst := (double_chain_constants c hγ hδ hlen).2
  have hcomm : e α * e β - e β * e α = c.structConst α β • e γ :=
    sub_eq_iff_eq_add'.mpr (root_mul_root c hγ)
  have hmul : c.structConst α β * c.structConst α γ =
      2 * (c.structConst α β * (c.structConst α γ).sign) := by nth_rw 1 [hconst]; ring
  apply dividedPower_mul_dividedPower_of_commutator_eq_of_iterated_commutator_eq
    (root_mul_root c hγ)
  · rw [hcomm, mul_smul_comm, smul_mul_assoc, root_mul_root c hδ,
      smul_add, smul_smul, hmul]
  · exact (double_chain_commute c hγ hδ hlen).1
  · exact (double_chain_commute c hγ hδ hlen).2

/-- Collection in the reversed double chain `α, α + β, α + 2β`.
The double-root coefficient acquires a minus sign, and the two middle factors occur
in the reversed order. -/
theorem dividedPower_root_mul_of_reverse_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root β + P.root γ)
    (hlen : P.chainBotCoeff β α + P.chainTopCoeff β α ≤ 2) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      ∑ p ∈ chainLeTwoIndex n m,
        (c.structConst α β ^ p.1 *
          (-(c.structConst α β * (c.structConst β γ).sign)) ^ p.2) •
          (dividedPower (n - p.1 - 2 * p.2) (e β) * dividedPower p.2 (e δ) *
            dividedPower p.1 (e γ) * dividedPower (m - p.1 - p.2) (e α)) := by
  have hγ' : P.root γ = P.root β + P.root α := by simpa only [add_comm] using hγ
  have hconst := (double_chain_constants c hγ' hδ hlen).2
  have hxy : MulOpposite.op (e β) * MulOpposite.op (e α) =
      MulOpposite.op (e α) * MulOpposite.op (e β) +
        c.structConst α β • MulOpposite.op (e γ) := by
    simpa only [MulOpposite.op_mul, MulOpposite.op_add, MulOpposite.op_smul] using
      congrArg MulOpposite.op (root_mul_root c hγ)
  have hxz : MulOpposite.op (e β) * MulOpposite.op (e γ) =
      MulOpposite.op (e γ) * MulOpposite.op (e β) +
        (-c.structConst β γ) • MulOpposite.op (e δ) := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_add,
      MulOpposite.unop_smul]
    rw [root_mul_root c hδ, neg_smul, add_neg_cancel_right]
  have hmul : c.structConst α β * (-c.structConst β γ) =
      2 * (-(c.structConst α β * (c.structConst β γ).sign)) := by
    nth_rw 1 [hconst]
    ring
  have hxxy : MulOpposite.op (e β) *
        (MulOpposite.op (e β) * MulOpposite.op (e α) -
          MulOpposite.op (e α) * MulOpposite.op (e β)) =
      (MulOpposite.op (e β) * MulOpposite.op (e α) -
          MulOpposite.op (e α) * MulOpposite.op (e β)) * MulOpposite.op (e β) +
        (2 * (-(c.structConst α β * (c.structConst β γ).sign))) • MulOpposite.op (e δ) := by
    rw [hxy, add_sub_cancel_left, mul_smul_comm, smul_mul_assoc, hxz,
      smul_add, smul_smul, hmul]
  have h := dividedPower_mul_dividedPower_of_commutator_eq_of_iterated_commutator_eq
    hxy hxxy (double_chain_commute c hγ' hδ hlen).1.op
    (double_chain_commute c hγ' hδ hlen).2.op n m
  -- Opposite multiplication reverses every factor; its powers and scalar action are unchanged.
  have hpow (k : ℕ) (u : Uᵐᵒᵖ) :
      MulOpposite.unop (dividedPower k u) = dividedPower k (MulOpposite.unop u) := by
    simp only [dividedPower_def, MulOpposite.unop_smul, MulOpposite.unop_pow]
  simpa only [MulOpposite.unop_mul, Finset.unop_sum, MulOpposite.unop_smul,
    hpow, MulOpposite.unop_op, mul_assoc] using congrArg MulOpposite.unop h

/-- The double-chain correction is an explicit finite integer linear combination in
`β, γ, δ, α` order, and its terms have smaller total divided-power degree. -/
theorem dividedPower_root_mul_eq_swap_add_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) (m n : ℕ) :
    (dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ p ∈ (chainLeTwoIndex m n).erase (0, 0),
          (c.structConst α β ^ p.1 *
            (c.structConst α β * (c.structConst α γ).sign) ^ p.2) •
            (dividedPower (n - p.1 - p.2) (e β) * dividedPower p.1 (e γ) *
              dividedPower p.2 (e δ) * dividedPower (m - p.1 - 2 * p.2) (e α))) ∧
      ∀ p ∈ (chainLeTwoIndex m n).erase (0, 0),
        (n - p.1 - p.2) + p.1 + p.2 + (m - p.1 - 2 * p.2) < m + n := by
  constructor
  · rw [dividedPower_root_mul_of_double_chain c hγ hδ hlen]
    simpa only [pow_zero, dividedPower_zero, mul_one, one_mul, one_smul,
      Nat.sub_zero, Nat.mul_zero] using
      (add_sum_erase (chainLeTwoIndex m n)
        (fun p ↦ (c.structConst α β ^ p.1 *
          (c.structConst α β * (c.structConst α γ).sign) ^ p.2) •
            (dividedPower (n - p.1 - p.2) (e β) * dividedPower p.1 (e γ) *
              dividedPower p.2 (e δ) * dividedPower (m - p.1 - 2 * p.2) (e α)))
        (by simp : (0, 0) ∈ chainLeTwoIndex m n)).symm
  · intro p hp
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    have := mem_chainLeTwoIndex.mp hp
    have : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Prod.ext h.1 h.2)
    omega

/-- In the reversed double chain, correction products have `β, δ, γ, α` order.
Their coefficients are integers and their total divided-power degrees strictly decrease. -/
theorem dividedPower_root_mul_eq_swap_add_of_reverse_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root β + P.root γ)
    (hlen : P.chainBotCoeff β α + P.chainTopCoeff β α ≤ 2) (m n : ℕ) :
    (dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ p ∈ (chainLeTwoIndex n m).erase (0, 0),
          (c.structConst α β ^ p.1 *
            (-(c.structConst α β * (c.structConst β γ).sign)) ^ p.2) •
            (dividedPower (n - p.1 - 2 * p.2) (e β) * dividedPower p.2 (e δ) *
              dividedPower p.1 (e γ) * dividedPower (m - p.1 - p.2) (e α))) ∧
      ∀ p ∈ (chainLeTwoIndex n m).erase (0, 0),
        (n - p.1 - 2 * p.2) + p.2 + p.1 + (m - p.1 - p.2) < m + n := by
  constructor
  · rw [dividedPower_root_mul_of_reverse_double_chain c hγ hδ hlen]
    simpa only [pow_zero, dividedPower_zero, mul_one, one_mul, one_smul,
      Nat.sub_zero, Nat.mul_zero] using
      (add_sum_erase (chainLeTwoIndex n m)
        (fun p ↦ (c.structConst α β ^ p.1 *
          (-(c.structConst α β * (c.structConst β γ).sign)) ^ p.2) •
            (dividedPower (n - p.1 - 2 * p.2) (e β) * dividedPower p.2 (e δ) *
              dividedPower p.1 (e γ) * dividedPower (m - p.1 - p.2) (e α)))
        (by simp : (0, 0) ∈ chainLeTwoIndex n m)).symm
  · intro p hp
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    have := mem_chainLeTwoIndex.mp hp
    have : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Prod.ext h.1 h.2)
    omega

/-- At degrees two and one, the last double-chain term has the product of the two
bracket signs, rather than just the second sign. -/
theorem dividedPower_two_root_mul_root_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) :
    dividedPower 2 (e α) * e β = e β * dividedPower 2 (e α) +
      c.structConst α β • (e γ * e α) +
        ((c.structConst α β).sign * (c.structConst α γ).sign) • e δ := by
  have hsign : c.structConst α β = (c.structConst α β).sign := by
    have h := Int.sign_mul_natAbs (c.structConst α β)
    rw [(double_chain_constants c hγ hδ hlen).1] at h
    simpa using h.symm
  have hprod : c.structConst α β * (c.structConst α γ).sign =
      (c.structConst α β).sign * (c.structConst α γ).sign := congrArg
        (fun z ↦ z * (c.structConst α γ).sign) hsign
  have hindex : chainLeTwoIndex 2 1 = {(0, 0), (1, 0), (0, 1)} := by
    ext ⟨b, k⟩
    simp only [mem_chainLeTwoIndex, mem_insert, mem_singleton, Prod.mk.injEq]
    omega
  have h := dividedPower_root_mul_of_double_chain c hγ hδ hlen 2 1
  simpa [hindex, hprod, add_assoc] using h

end DoubleChain

end RootPairing.ChevalleyLieAlgebra
