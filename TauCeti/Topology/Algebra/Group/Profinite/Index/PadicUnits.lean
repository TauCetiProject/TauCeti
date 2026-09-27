/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.DyadicUnits
public import TauCeti.Topology.Algebra.Group.Profinite.Index.Tower
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Supernatural indices of the closed subgroups of `ℤ_2ˣ`

The closed subgroups of the profinite group `ℤ_2ˣ` are the principal unit groups
`U^(f) = 1 + 2^f ℤ_2`, the subgroups `V^(f) = {±1} × U^(f)`, the subgroup `{±1}` and the twisted
subgroups `U^[f] = closure ⟨-1 + 2^f⟩`. Their ordinary indices are the powers of two
`2 ^ (f - 1)`, `2 ^ (f - 2)` and `2 ^ (f - 1)`, so as supernatural numbers their indices are the
supernatural prime powers with those exponents. This file records that table, together with the
one entry that has no finite index: the supernatural index of `{±1}` has infinite exponent at `2`,
which is the value `2 ^ ∞` that the `V`-family formula takes at `f = ∞`.

The last line of the table is the supernatural index `(A : A²)` of the closed subgroup of squares
of a closed subgroup `A ≤ ℤ_2ˣ`. It is `p` for a principal unit group in `ℤ_pˣ`, and for `p = 2`
it is `2` for `U^(f)` and `U^[f]` and `4` for `V^(f)`; the three values `1`, `2` and `4` are the
only ones it takes. It is the numerical invariant that distinguishes the non-procyclic family
`V^(f)` from the procyclic ones, and the one read off from the image of a continuous character of
a pro-`2` group in `ℤ_2ˣ`.

## Main results

* `TauCeti.profiniteIndex_unitsPrincipal_two`, `TauCeti.profiniteIndex_unitsPlusMinus`,
  `TauCeti.profiniteIndex_topologicalClosure_zpowers_two`: the supernatural indices
  `2 ^ (f - 1)`, `2 ^ (f - 2)` and `2 ^ (f - 1)` of `U^(f)`, `V^(f)` and `U^[f]` in `ℤ_2ˣ`.
* `TauCeti.profiniteIndex_zpowers_neg_one_apply_two_eq_top`: the index of `{±1}` in `ℤ_2ˣ` has
  infinite exponent at `2`, which is the entry `2 ^ ∞` of the `V`-family at `f = ∞`.
* `TauCeti.profiniteIndex_subgroupOf_map_powMonoidHom_unitsPrincipal`,
  `TauCeti.profiniteIndex_subgroupOf_map_powMonoidHom_two_unitsPlusMinus`,
  `TauCeti.profiniteIndex_subgroupOf_map_powMonoidHom_two_topologicalClosure_zpowers_two`:
  the values `p`, `4` and `2` of `(A : A²)` on the three families.
* `TauCeti.profiniteIndex_subgroupOf_map_powMonoidHom_two_eq_one_or_two_or_four`: `(A : A²)` is
  `1`, `2` or `4` for every closed subgroup `A ≤ ℤ_2ˣ`.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), the remark
  following the corollary to Theorem 4.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The indices of the closed subgroups of `ℤ_2ˣ` -/

/-- The supernatural index of the principal unit group `U^(f) = 1 + 2^f ℤ_2` in `ℤ_2ˣ` is
`2 ^ (f - 1)`. -/
theorem profiniteIndex_unitsPrincipal_two (f : ℕ) :
    Subgroup.profiniteIndex (unitsPrincipal 2 f) =
      Supernatural.primePower (⟨2, Nat.prime_two⟩ : Nat.Primes) ((f - 1 : ℕ) : ℕ∞) :=
  Subgroup.profiniteIndex_eq_primePower (isOpen_unitsPrincipal 2 f) (index_unitsPrincipal_two f)

/-- The supernatural index of `V^(f) = {±1} × U^(f)` in `ℤ_2ˣ` is `2 ^ (f - 2)`. -/
theorem profiniteIndex_unitsPlusMinus {f : ℕ} (hf : 2 ≤ f) :
    Subgroup.profiniteIndex (unitsPlusMinus f) =
      Supernatural.primePower (⟨2, Nat.prime_two⟩ : Nat.Primes) ((f - 2 : ℕ) : ℕ∞) :=
  Subgroup.profiniteIndex_eq_primePower (isOpen_unitsPlusMinus f) (index_unitsPlusMinus hf)

/-- The supernatural index of the twisted subgroup `U^[f]` in `ℤ_2ˣ` is `2 ^ (f - 1)`, for
`f ≥ 2` and `-u` of exact level `f`. -/
theorem profiniteIndex_topologicalClosure_zpowers_two {f : ℕ} (hf : 2 ≤ f) {u : ℤ_[2]ˣ}
    (hneg : -u ∈ unitsPrincipal 2 f) (hneg' : -u ∉ unitsPrincipal 2 (f + 1)) :
    Subgroup.profiniteIndex (Subgroup.zpowers u).topologicalClosure =
      Supernatural.primePower (⟨2, Nat.prime_two⟩ : Nat.Primes) ((f - 1 : ℕ) : ℕ∞) := by
  have hidx := index_topologicalClosure_zpowers_two hf hneg hneg'
  have : ((Subgroup.zpowers u).topologicalClosure).FiniteIndex :=
    ⟨by rw [hidx]; exact pow_ne_zero _ two_ne_zero⟩
  exact Subgroup.profiniteIndex_eq_primePower
    (Subgroup.isOpen_of_isClosed_of_finiteIndex _ (Subgroup.isClosed_topologicalClosure _)) hidx

/-- The exponent at `2` of the supernatural index of `{±1}` in `ℤ_2ˣ` is infinite: `{±1}` is
contained in every `V^(f)`, whose index `2 ^ (f - 2)` is unbounded. This is the value `2 ^ ∞` that
the index of the `V`-family takes at `f = ∞`, where `V^(∞) = {±1}`. -/
theorem profiniteIndex_zpowers_neg_one_apply_two_eq_top :
    Subgroup.profiniteIndex (Subgroup.zpowers (-1 : ℤ_[2]ˣ))
      (⟨2, Nat.prime_two⟩ : Nat.Primes) = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n ↦ ?_
  have hle : Subgroup.profiniteIndex (unitsPlusMinus (n + 2)) ≤
      Subgroup.profiniteIndex (Subgroup.zpowers (-1 : ℤ_[2]ˣ)) :=
    Subgroup.profiniteIndex_anti (Subgroup.zpowers_le.mpr (neg_one_mem_unitsPlusMinus (n + 2)))
  have key := Supernatural.le_iff.mp hle (⟨2, Nat.prime_two⟩ : Nat.Primes)
  rw [profiniteIndex_unitsPlusMinus (by omega), Supernatural.primePower_apply_self
    (⟨2, Nat.prime_two⟩ : Nat.Primes) ((n + 2 - 2 : ℕ) : ℕ∞), Nat.add_sub_cancel] at key
  exact key

/-! ### The supernatural index of the squares -/

/-- `(U^(f) : (U^(f))^p) = p` as a supernatural number, for `f ≥ 1`, and `f ≥ 2` when
`p = 2`. -/
theorem profiniteIndex_subgroupOf_map_powMonoidHom_unitsPrincipal {f : ℕ} (hf : 0 < f)
    (hf₂ : p = 2 → 2 ≤ f) :
    Subgroup.profiniteIndex
        (((unitsPrincipal p f).map (powMonoidHom p)).subgroupOf (unitsPrincipal p f)) =
      Supernatural.primePower (⟨p, hp.out⟩ : Nat.Primes) 1 :=
  Subgroup.profiniteIndex_subgroupOf_eq_primePower
    (Subgroup.isClosed_map (isClosed_unitsPrincipal p f).isCompact _ (continuous_pow p))
    (isClosed_unitsPrincipal p f)
    (by rw [relIndex_map_powMonoidHom_unitsPrincipal hf hf₂, pow_one])

/-- `(V^(f) : (V^(f))²) = 4` as a supernatural number, for `f ≥ 2`. -/
theorem profiniteIndex_subgroupOf_map_powMonoidHom_two_unitsPlusMinus {f : ℕ} (hf : 2 ≤ f) :
    Subgroup.profiniteIndex
        (((unitsPlusMinus f).map (powMonoidHom 2)).subgroupOf (unitsPlusMinus f)) =
      Supernatural.primePower (⟨2, Nat.prime_two⟩ : Nat.Primes) 2 :=
  Subgroup.profiniteIndex_subgroupOf_eq_primePower
    (Subgroup.isClosed_map (isClosed_unitsPlusMinus f).isCompact _ (continuous_pow 2))
    (isClosed_unitsPlusMinus f)
    (by rw [relIndex_map_powMonoidHom_two_unitsPlusMinus hf]; rfl)

/-- `(U^[f] : (U^[f])²) = 2` as a supernatural number, for `f ≥ 2` and `-u` of exact level
`f`. -/
theorem profiniteIndex_subgroupOf_map_powMonoidHom_two_topologicalClosure_zpowers_two {f : ℕ}
    (hf : 2 ≤ f) {u : ℤ_[2]ˣ} (hneg : -u ∈ unitsPrincipal 2 f)
    (hneg' : -u ∉ unitsPrincipal 2 (f + 1)) :
    Subgroup.profiniteIndex
        (((Subgroup.zpowers u).topologicalClosure.map (powMonoidHom 2)).subgroupOf
          (Subgroup.zpowers u).topologicalClosure) =
      Supernatural.primePower (⟨2, Nat.prime_two⟩ : Nat.Primes) 1 :=
  Subgroup.profiniteIndex_subgroupOf_eq_primePower
    (Subgroup.isClosed_map (Subgroup.isClosed_topologicalClosure _).isCompact _
      (continuous_pow 2))
    (Subgroup.isClosed_topologicalClosure _)
    (by rw [relIndex_map_powMonoidHom_two_topologicalClosure_zpowers_two hf hneg hneg']; rfl)

/-- **The supernatural index `(A : A²)` of a closed subgroup of `ℤ_2ˣ` is `1`, `2` or `4`.** Which
of the three values occurs is recorded at the level of ordinary indices by
`TauCeti.relIndex_map_powMonoidHom_two_eq_one_iff` and
`TauCeti.relIndex_map_powMonoidHom_two_eq_four_iff`. -/
theorem profiniteIndex_subgroupOf_map_powMonoidHom_two_eq_one_or_two_or_four
    {A : Subgroup ℤ_[2]ˣ} (hA : IsClosed (A : Set ℤ_[2]ˣ)) :
    Subgroup.profiniteIndex ((A.map (powMonoidHom 2)).subgroupOf A) = 1 ∨
      Subgroup.profiniteIndex ((A.map (powMonoidHom 2)).subgroupOf A) =
        Supernatural.primePower (⟨2, Nat.prime_two⟩ : Nat.Primes) 1 ∨
      Subgroup.profiniteIndex ((A.map (powMonoidHom 2)).subgroupOf A) =
        Supernatural.primePower (⟨2, Nat.prime_two⟩ : Nat.Primes) 2 := by
  have hsq : IsClosed ((A.map (powMonoidHom 2) : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
    Subgroup.isClosed_map hA.isCompact _ (continuous_pow 2)
  rcases relIndex_map_powMonoidHom_two_eq_one_or_two_or_four hA with h | h | h
  · refine Or.inl ((Subgroup.profiniteIndex_subgroupOf_eq_primePower hsq hA
      (q := (⟨2, Nat.prime_two⟩ : Nat.Primes)) (k := 0) (by rw [h]; rfl)).trans ?_)
    exact Supernatural.primePower_zero _
  · exact Or.inr (Or.inl (Subgroup.profiniteIndex_subgroupOf_eq_primePower hsq hA (by rw [h]; rfl)))
  · exact Or.inr (Or.inr (Subgroup.profiniteIndex_subgroupOf_eq_primePower hsq hA (by rw [h]; rfl)))

end TauCeti
