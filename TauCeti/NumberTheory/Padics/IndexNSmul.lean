/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.GroupTheory.Index.NSmul
import TauCeti.GroupTheory.Index.PrimaryComponent
import TauCeti.NumberTheory.Padics.RingHoms

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

For example, the points of an elliptic curve over `ℚ_p` contain a subgroup of finite index
isomorphic to `ℤ_p`, and the ratio `#(E(ℚ_p) ⧸ 2 E(ℚ_p)) / #E(ℚ_p)[2]` is the local factor at `p`
of the average size of the `2`-Selmer group of elliptic curves.

## Main results

* `AddSubgroup.finite_ker_nsmulAddMonoidHom_of_addEquiv_padicInt`: `G[n]` is finite.
* `AddSubgroup.index_range_nsmul_of_addEquiv_padicInt`: `#(G ⧸ n G) = #G[n] · p ^ v_p(n)`.
* `AddSubgroup.finiteIndex_range_nsmul_of_addEquiv_padicInt`: `n G` has finite index in `G`.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), Lemma 3.20.
-/

public section

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G] (U : AddSubgroup G) {p : ℕ} [Fact p.Prime] (e : U ≃+ ℤ_[p])
  {n : ℕ}

include e in
/-- Multiplication by `n ≠ 0` is injective on a subgroup isomorphic to `ℤ_p`. -/
private theorem injective_nsmul_of_addEquiv_padicInt (hn : n ≠ 0) :
    Function.Injective (fun x : U ↦ n • x) := fun x y h ↦
  e.injective (nsmul_right_injective hn (by simpa [map_nsmul] using congrArg e h))

variable [U.FiniteIndex]

include e in
/-- **The `n`-torsion of a group containing `ℤ_p` with finite index is finite** for `n ≠ 0`. -/
theorem finite_ker_nsmulAddMonoidHom_of_addEquiv_padicInt (hn : n ≠ 0) :
    Finite (nsmulAddMonoidHom (α := G) n).ker := by
  -- `G[n]` lies in the `n`-primary component `G[n^∞]`, which is finite
  have := U.finite_primaryComponent_of_injective (injective_nsmul_of_addEquiv_padicInt U e hn)
  have hle : (nsmulAddMonoidHom (α := G) n).ker ≤ AddCommGroup.primaryComponent G n :=
    fun x hx ↦ AddCommGroup.mem_primaryComponent.mpr ⟨1, by simpa using hx⟩
  exact Finite.of_injective _ (inclusion_injective hle)

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
  rw [(AddMonoidHom.ker_eq_bot_iff _).mpr (injective_nsmul_of_addEquiv_padicInt U e hn),
    card_bot, mul_one, e.index_range_nsmulAddMonoidHom n, PadicInt.index_range_nsmul hn] at h
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
