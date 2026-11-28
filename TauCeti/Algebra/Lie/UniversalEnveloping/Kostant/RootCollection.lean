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
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Collection of independent Chevalley root divided powers

In the rational enveloping algebra of the integral Chevalley Lie algebra, independent
root vectors commute when their sum is absent. When the lower plus upper length of the relevant
root string is at most two (at most three roots), their divided powers collect with
integer coefficients. The three possible
noncommuting configurations are a central bracket and the two orientations of a double
chain. The cocharacter lattice is the full lattice of the supplied root pairing; no
irreducibility or integral splitting of its central directions is required.

These cases exhaust independent pairs if the sum of the lower and upper string
lengths is at most two for every independent pair. Indeed, if `γ = α + β` is a root,
split according to the presence of `α + γ` and `β + γ`. In a double chain the given
length bound excludes the other double root by `Finite.DoubleChain`. The formulas
require only the local bound on the string actually used. The versions with
`eq_swap_add` in their names isolate the leading swapped product. The degree lemmas in
`NormalOrdering` and `RootString.Basic` bound each correction's total degree strictly below
the input degree.

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

/-- Root vectors in the rational enveloping algebra satisfy the integral Chevalley
commutator relation when their roots add to a root. -/
theorem ι_root_mul_ι_root_of_root_eq_add {α β γ : ι}
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

private theorem commute_root_of_root_eq_add {α β γ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hnot : P.root α + P.root γ ∉ Set.range P.root) : Commute (e α) (e γ) := by
  let := c.isReduced
  apply commute_root c hnot
  simpa only [ne_eq, add_eq_zero_iff_eq_neg] using
    (P.root_ne_and_root_ne_neg_of_root_eq_add hγ).2

/-- Nonopposite root vectors whose sum is absent have commuting divided powers. No
string-length bound is needed, so this applies to independent roots in every type and
to pairs in different components. -/
theorem commute_dividedPower_root_dividedPower_root {α β : ι}
    (hnot : P.root α + P.root β ∉ Set.range P.root)
    (hne : P.root α + P.root β ≠ 0) (m n : ℕ) :
    Commute (dividedPower m (e α)) (dividedPower n (e β)) :=
  commute_dividedPower_dividedPower (commute_root c hnot hne) m n

/-- If neither double root exists, collection has just the sum-root factor. Its coefficient
is the corresponding power of the integral Chevalley bracket coefficient. -/
theorem dividedPower_root_mul_dividedPower_root_of_no_double {α β γ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hαγ : P.root α + P.root γ ∉ Set.range P.root)
    (hβγ : P.root β + P.root γ ∉ Set.range P.root) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      ∑ k ∈ range (min m n + 1), (c.structConst α β ^ k) •
        (dividedPower (n - k) (e β) * dividedPower k (e γ) *
          dividedPower (m - k) (e α)) := by
  rw [dividedPower_mul_dividedPower_of_commutator_eq (ι_root_mul_ι_root_of_root_eq_add c hγ)
    ((commute_root_of_root_eq_add c hγ hαγ).smul_right _)
    ((commute_root_of_root_eq_add c (hγ.trans (add_comm _ _)) hβγ).smul_right _)]
  apply sum_congr rfl
  intro k _
  simp only [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc]

/-- Isolate the swapped leading product in central-bracket collection.
The corrections' degree decrease is given by `TauCeti.Associative.centralBracket_degree_lt`. -/
theorem dividedPower_root_mul_dividedPower_root_eq_swap_add_of_no_double {α β γ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hαγ : P.root α + P.root γ ∉ Set.range P.root)
    (hβγ : P.root β + P.root γ ∉ Set.range P.root) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ k ∈ (range (min m n + 1)).erase 0, (c.structConst α β ^ k) •
          (dividedPower (n - k) (e β) * dividedPower k (e γ) *
            dividedPower (m - k) (e α)) := by
  rw [dividedPower_root_mul_dividedPower_root_of_no_double c hγ hαγ hβγ]
  rw [← add_sum_erase (range (min m n + 1)) _ (by simp : 0 ∈ range (min m n + 1))]
  simp only [pow_zero, dividedPower_zero, mul_one, one_smul, Nat.sub_zero]

section DoubleChain

private theorem double_chain_commute {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) :
    Commute (e α) (e δ) ∧ Commute (e β) (e γ) := by
  have hbot := P.chainBotCoeff_eq_zero_of_chainBotCoeff_add_chainTopCoeff_le_two hγ hδ hlen
  have htop := P.chainTopCoeff_eq_two_of_chainTopCoeff_le_two hγ hδ (by omega)
  exact ⟨commute_root_of_root_eq_add c hδ
      (P.root_add_root_notMem_range_root_of_chainTopCoeff_le_two hγ hδ htop.le),
    commute_root_of_root_eq_add c (hγ.trans (add_comm _ _))
      (P.root_add_root_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
        hγ hbot htop)⟩

/-- Collection along `β, α + β, 2α + β`, with the full integral Chevalley table.
The double-root coefficient is the product of the first bracket sign and the sign of
the second bracket, whose absolute value is two. -/
theorem dividedPower_root_mul_dividedPower_root_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      ∑ p ∈ chainLeTwoIndex m n,
        (c.structConst α β ^ p.1 *
          (c.structConst α β * (c.structConst α γ).sign) ^ p.2) •
          (dividedPower (n - p.1 - p.2) (e β) * dividedPower p.1 (e γ) *
            dividedPower p.2 (e δ) * dividedPower (m - p.1 - 2 * p.2) (e α)) := by
  have hconst := c.structConst_eq_two_mul_sign_of_chain_le_two hγ hlen
  have hcomm : e α * e β - e β * e α = c.structConst α β • e γ :=
    sub_eq_iff_eq_add'.mpr (ι_root_mul_ι_root_of_root_eq_add c hγ)
  have hmul : c.structConst α β * c.structConst α γ =
      2 * (c.structConst α β * (c.structConst α γ).sign) := by nth_rw 1 [hconst]; ring
  apply dividedPower_mul_dividedPower_of_commutator_eq_of_iterated_commutator_eq
    (ι_root_mul_ι_root_of_root_eq_add c hγ)
  · rw [hcomm, mul_smul_comm, smul_mul_assoc, ι_root_mul_ι_root_of_root_eq_add c hδ,
      smul_add, smul_smul, hmul]
  · exact (double_chain_commute c hγ hδ hlen).1
  · exact (double_chain_commute c hγ hδ hlen).2

/-- Collection in the reversed double chain `α, α + β, α + 2β`.
The double-root coefficient acquires a minus sign, and the two middle factors occur
in the reversed order. -/
theorem dividedPower_root_mul_dividedPower_root_of_reverse_double_chain {α β γ δ : ι}
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
  have hconst := c.structConst_eq_two_mul_sign_of_chain_le_two hγ' hlen
  have hxy : MulOpposite.op (e β) * MulOpposite.op (e α) =
      MulOpposite.op (e α) * MulOpposite.op (e β) +
        c.structConst α β • MulOpposite.op (e γ) := by
    simpa only [MulOpposite.op_mul, MulOpposite.op_add, MulOpposite.op_smul] using
      congrArg MulOpposite.op (ι_root_mul_ι_root_of_root_eq_add c hγ)
  have hxz : MulOpposite.op (e β) * MulOpposite.op (e γ) =
      MulOpposite.op (e γ) * MulOpposite.op (e β) +
        (-c.structConst β γ) • MulOpposite.op (e δ) := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_add,
      MulOpposite.unop_smul]
    rw [ι_root_mul_ι_root_of_root_eq_add c hδ, neg_smul, add_neg_cancel_right]
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
  simpa only [MulOpposite.unop_mul, Finset.unop_sum, MulOpposite.unop_smul,
    MulOpposite.unop_dividedPower, MulOpposite.unop_op, mul_assoc] using congrArg MulOpposite.unop h

/-- Isolate the swapped leading product, with double-chain corrections in `β, γ, δ, α` order.
Their degree decrease is given by `TauCeti.Associative.chainLeTwoIndex_degree_lt`. -/
theorem dividedPower_root_mul_dividedPower_root_eq_swap_add_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ p ∈ (chainLeTwoIndex m n).erase (0, 0),
          (c.structConst α β ^ p.1 *
            (c.structConst α β * (c.structConst α γ).sign) ^ p.2) •
            (dividedPower (n - p.1 - p.2) (e β) * dividedPower p.1 (e γ) *
              dividedPower p.2 (e δ) * dividedPower (m - p.1 - 2 * p.2) (e α)) := by
  rw [dividedPower_root_mul_dividedPower_root_of_double_chain c hγ hδ hlen]
  rw [← add_sum_erase (chainLeTwoIndex m n) _ (by simp : (0, 0) ∈ chainLeTwoIndex m n)]
  simp only [pow_zero, dividedPower_zero, mul_one, one_smul,
    Nat.sub_zero, Nat.mul_zero]

/-- Isolate the swapped leading product, with reverse-chain corrections in `β, δ, γ, α` order.
Their degree decrease is given by `TauCeti.Associative.chainLeTwoIndex_reverse_degree_lt`. -/
theorem dividedPower_root_mul_dividedPower_root_eq_swap_add_of_reverse_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root β + P.root γ)
    (hlen : P.chainBotCoeff β α + P.chainTopCoeff β α ≤ 2) (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ p ∈ (chainLeTwoIndex n m).erase (0, 0),
          (c.structConst α β ^ p.1 *
            (-(c.structConst α β * (c.structConst β γ).sign)) ^ p.2) •
            (dividedPower (n - p.1 - 2 * p.2) (e β) * dividedPower p.2 (e δ) *
              dividedPower p.1 (e γ) * dividedPower (m - p.1 - p.2) (e α)) := by
  rw [dividedPower_root_mul_dividedPower_root_of_reverse_double_chain c hγ hδ hlen]
  rw [← add_sum_erase (chainLeTwoIndex n m) _ (by simp : (0, 0) ∈ chainLeTwoIndex n m)]
  simp only [pow_zero, dividedPower_zero, mul_one, one_smul,
    Nat.sub_zero, Nat.mul_zero]

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
    rw [c.natAbs_structConst_eq_one_of_double_chain hγ hδ hlen] at h
    simpa using h.symm
  have hprod : c.structConst α β * (c.structConst α γ).sign =
      (c.structConst α β).sign * (c.structConst α γ).sign := congrArg
        (fun z ↦ z * (c.structConst α γ).sign) hsign
  have h := dividedPower_root_mul_dividedPower_root_of_double_chain c hγ hδ hlen 2 1
  rw [sum_chainLeTwoIndex_two_one] at h
  simpa only [dividedPower_one, pow_zero, mul_one, tsub_zero, dividedPower_zero,
    mul_zero, one_mul, pow_one, tsub_self, Nat.add_one_sub_one,
    one_smul, hprod, add_assoc] using h

end DoubleChain

end RootPairing.ChevalleyLieAlgebra
