/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.GroupTheory.Index.NSmul
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The index of `n G` in a group containing `ℤ_p` with finite index

Let `G` be a commutative group with a subgroup `U` of finite index that is isomorphic to the
additive group of `ℤ_p`. For a natural number `n ≠ 0` the `n`-torsion `G[n]` is finite, `n G` has
finite index, and

`#(G ⧸ n G) = #G[n] · p ^ v_p(n)`,

where `v_p(n) = multiplicity p n` is the `p`-adic valuation of `n`.

The factor `p ^ v_p(n) = #(ℤ_p ⧸ n ℤ_p)` is the inverse of the `p`-adic absolute value `|n|_p`;
for `n = 2` it is `1` for odd `p` and `2` for `p = 2`. The point is that the ratio
`#(G ⧸ n G) / #G[n]` does not change on passing to a subgroup of finite index
(`AddSubgroup.index_range_nsmul_add_card_ker`), and on `ℤ_p` it is `#(ℤ_p ⧸ n ℤ_p) / 1`, because
`ℤ_p` has no torsion. Only the abstract group structure enters.

This is the shape of the local Kummer index of an abelian variety over a `p`-adic field: the
points over the ring of integers reducing to the identity in a deep enough level of the formal
group form a subgroup of finite index isomorphic to `ℤ_p ^ g`, and the ratio
`#(A(ℚ_p) ⧸ 2 A(ℚ_p)) / #A(ℚ_p)[2]` is the local factor at `p` of the average size of the
`2`-Selmer group of elliptic curves.

## Main results

* `PadicInt.index_range_nsmul`: `#(ℤ_p ⧸ n ℤ_p) = p ^ v_p(n)` for `n ≠ 0`.
* `AddSubgroup.finite_ker_nsmulAddMonoidHom_of_addEquiv_padicInt`: `G[n]` is finite.
* `AddSubgroup.index_range_nsmul_of_addEquiv_padicInt`: `#(G ⧸ n G) = #G[n] · p ^ v_p(n)`.
* `AddSubgroup.finiteIndex_range_nsmul_of_addEquiv_padicInt`: `n G` has finite index in `G`.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), Lemma 3.20.
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **The index of `n ℤ_p` in `ℤ_p` is `p ^ v_p(n)`** for a natural number `n ≠ 0`, the inverse of
the `p`-adic absolute value of `n`. -/
theorem index_range_nsmul {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := ℤ_[p]) n).range.index = p ^ multiplicity p n := by
  set v := multiplicity p n
  -- `n = p ^ v * m` with `m` prime to `p`, so `n ℤ_p = p ^ v ℤ_p` is the kernel of reduction
  have hm : IsUnit (n.divMaxPow p : ℤ_[p]) :=
    isUnit_natCast_iff.mpr (Nat.not_dvd_divMaxPow (Fact.out : p.Prime).one_lt hn)
  have hdvd (x : ℤ_[p]) : (n : ℤ_[p]) ∣ x ↔ (p : ℤ_[p]) ^ v ∣ x := by
    rw [← Nat.pow_multiplicity_mul_divMaxPow p n, Nat.cast_mul, Nat.cast_pow, hm.mul_right_dvd]
  have hrange :
      (nsmulAddMonoidHom (α := ℤ_[p]) n).range = (toZModPow (p := p) v).toAddMonoidHom.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
      ← RingHom.mem_ker, ker_toZModPow, Ideal.mem_span_singleton, ← hdvd, AddMonoidHom.mem_range,
      dvd_def]
    simp only [nsmulAddMonoidHom_apply, nsmul_eq_mul, eq_comm]
  rw [hrange, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (ZMod.ringHom_surjective (toZModPow v)), AddSubgroup.card_top,
    Nat.card_zmod]

end PadicInt

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G] (U : AddSubgroup G) {p : ℕ} [Fact p.Prime] (e : U ≃+ ℤ_[p])
  {n : ℕ}

include e in
/-- A subgroup isomorphic to `ℤ_p` has no nonzero `n`-torsion for `n ≠ 0`. -/
private theorem ker_nsmulAddMonoidHom_eq_bot_of_addEquiv_padicInt (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := U) n).ker = ⊥ := by
  rw [AddMonoidHom.ker_eq_bot_iff]
  intro x y hxy
  apply e.injective
  have h := congrArg e hxy
  simp only [nsmulAddMonoidHom_apply, map_nsmul] at h
  exact nsmul_right_injective hn h

variable [U.FiniteIndex]

include e in
/-- **The `n`-torsion of a group containing `ℤ_p` with finite index is finite** for `n ≠ 0`: it
meets the subgroup trivially, so it embeds in the finite quotient. -/
theorem finite_ker_nsmulAddMonoidHom_of_addEquiv_padicInt (hn : n ≠ 0) :
    Finite (nsmulAddMonoidHom (α := G) n).ker := by
  have hker := ker_nsmulAddMonoidHom_eq_bot_of_addEquiv_padicInt U e hn
  refine Finite.of_injective (fun x ↦ (x : G ⧸ U)) fun x y hxy ↦ ?_
  rw [QuotientAddGroup.eq] at hxy
  -- `-x + y` is `n`-torsion in `U`, hence zero
  have h0 : (⟨-x + y, hxy⟩ : U) ∈ (nsmulAddMonoidHom (α := U) n).ker := by
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, ← Subtype.coe_inj, coe_nsmul, smul_add,
      smul_neg]
    simp [show n • (x : G) = 0 from x.property, show n • (y : G) = 0 from y.property]
  rw [hker, mem_bot, ← Subtype.coe_inj] at h0
  exact Subtype.ext (neg_add_eq_zero.mp h0)

include e in
/-- **The index of `n G` in a group `G` containing `ℤ_p` with finite index**: for `n ≠ 0`,

`#(G ⧸ n G) = #G[n] · p ^ v_p(n)`,

where the last factor is the inverse of the `p`-adic absolute value of `n`. For `n = 2` it reads
`#(G ⧸ 2 G) = #G[2]` for odd `p` and `#(G ⧸ 2 G) = 2 · #G[2]` for `p = 2`. -/
theorem index_range_nsmul_of_addEquiv_padicInt (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      Nat.card (nsmulAddMonoidHom (α := G) n).ker * p ^ multiplicity p n := by
  -- `(G : n G) · #U[n] = #G[n] · (U : n U)`, with `#U[n] = 1` and `(U : n U) = (ℤ_p : n ℤ_p)`
  have h := index_range_nsmul_add_card_ker U n
  rw [ker_nsmulAddMonoidHom_eq_bot_of_addEquiv_padicInt U e hn, card_bot, mul_one,
    e.index_range_nsmulAddMonoidHom n, PadicInt.index_range_nsmul hn] at h
  exact h

include e in
/-- **`n G` has finite index** in a group `G` containing `ℤ_p` with finite index, for `n ≠ 0`. -/
theorem finiteIndex_range_nsmul_of_addEquiv_padicInt (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.FiniteIndex := by
  have := finite_ker_nsmulAddMonoidHom_of_addEquiv_padicInt U e hn
  refine ⟨?_⟩
  rw [index_range_nsmul_of_addEquiv_padicInt U e hn]
  exact mul_ne_zero Nat.card_pos.ne' (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end AddSubgroup
