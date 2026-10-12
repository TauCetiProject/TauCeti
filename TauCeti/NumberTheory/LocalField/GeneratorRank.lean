/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Rank

/-!
# The lower bound for the generator rank of a local absolute Galois group

Let `K` be a finite extension of `ℚ_p` and `N = [K : ℚ_p]`. This file proves that the absolute
Galois group `G_K` needs at least `N + 2` topological generators:

```text
N + 2 ≤ d(G_K).
```

When `μ_p ⊆ K` this is visible on the maximal pro-`p` quotient, whose generator rank is exactly
`N + 2`. When `μ_p ⊄ K` the maximal pro-`p` quotient only needs `N + 1` generators, and the bound
comes from the open subgroup `G_L` for `L = K(μ_p)`. With `m = [L : K]`, the field `L` contains
`μ_p`, so `d(G_L) ≥ d(G_L(p)) = [L : ℚ_p] + 2 = mN + 2`, while Schreier's bound for an open
subgroup of index `m` gives `d(G_L) ≤ 1 + m (d(G_K) - 1)`. Hence `m (d(G_K) - 1) > mN`, that is
`d(G_K) ≥ N + 2`. The argument with `L = K(μ_p)` covers both cases at once, with `m = 1` when
`μ_p ⊆ K`.

The bound is stated twice: unconditionally, as a lower bound on the size of every finite set
generating a dense subgroup of `G_K`, and for the natural-number generator rank, which takes a
proof of topological finite generation as an argument.

## Main results

* `TauCeti.finrank_add_two_le_card_of_topologicalClosure_closure_eq_top_absoluteGaloisGroup`:
  every finite subset of `G_K` generating a dense subgroup has at least `[K : ℚ_p] + 2` elements.
* `TauCeti.le_topologicalGeneratorRankNat_absoluteGaloisGroup`: `[K : ℚ_p] + 2 ≤ d(G_K)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.4.1) and
  (7.5.11).
* M. Jarden and A. Shusterman, *The absolute Galois group of a `p`-adic field*, Theorem 2.1.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]

/-- **The lower bound for the generator rank of a local absolute Galois group.** For a finite
extension `K` of `ℚ_p`, the absolute Galois group `G_K` needs at least `[K : ℚ_p] + 2` topological
generators. The finite-generation witness is an argument, so that the natural-valued rank is only
read on a topologically finitely generated group. -/
theorem le_topologicalGeneratorRankNat_absoluteGaloisGroup
    (hG : IsTopologicallyFinitelyGenerated (Field.absoluteGaloisGroup K)) :
    Module.finrank ℚ_[p] K + 2 ≤
      topologicalGeneratorRankNat (Field.absoluteGaloisGroup K) hG := by
  -- The field `L = K(μ_p)`, with the local-field structure extending that of `K`.
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  let L := CyclotomicField p K
  have : FiniteDimensional K L := IsCyclotomicExtension.finiteDimensional {p} K L
  let := finiteExtensionValuativeRel K L
  let := finiteExtensionNormedFieldTopology K L
  have := finiteExtension_isNonarchimedeanLocalField K L
  have := finiteExtension_valuativeExtension K L
  have := ValuativeExtension.trans ℚ_[p] K L
  have hmu : ∃ ζ : L, IsPrimitiveRoot ζ p :=
    ⟨IsCyclotomicExtension.zeta p K L, IsCyclotomicExtension.zeta_spec p K L⟩
  -- `G_L` is the open subgroup `U` of `G_K` of index `m = [L : K]`.
  let U := galoisSubgroup K L IsSepClosed.lift
  have hG' := (isTopologicallyFinitelyGenerated_congr (absoluteGaloisGroupRestrictEquiv K)).mp hG
  have hU := hG'.of_openSubgroup_of_finiteIndex U
  let e : Field.absoluteGaloisGroup L ≃ₜ* U.toSubgroup :=
    (absoluteGaloisGroupRestrictEquiv L).trans (galoisSubgroupEquiv K L IsSepClosed.lift)
  have hL := (isTopologicallyFinitelyGenerated_congr e).mpr hU
  -- Schreier: `d(G_L) ≤ 1 + m (d(G_K) - 1)`.
  have hschreier : topologicalGeneratorRankNat (Field.absoluteGaloisGroup L) hL ≤
      1 + Module.finrank K L *
        (topologicalGeneratorRankNat (Field.absoluteGaloisGroup K) hG - 1) := by
    rw [topologicalGeneratorRankNat_congr e hL, topologicalGeneratorRankNat_congr
      (absoluteGaloisGroupRestrictEquiv K) hG, ← galoisSubgroup_index K L IsSepClosed.lift]
    exact topologicalGeneratorRankNat_le_of_openSubgroup_of_finiteIndex hG' U
  -- `d(G_L(p)) = [L : ℚ_p] + 2 = Nm + 2` and `d(G_L(p)) ≤ d(G_L)`.
  have hpro := topologicalGeneratorRankNat_le_of_surjective
    (absoluteGaloisGroupProPQuotientMap p L).toMonoidHom
    (absoluteGaloisGroupProPQuotientMap p L).continuous QuotientGroup.mk_surjective hL
  rw [topologicalGeneratorRankNat_absoluteGaloisGroupProP_of_mu p L _ hmu,
    ← Module.finrank_mul_finrank ℚ_[p] K L] at hpro
  -- `Nm + 2 ≤ 1 + m (d(G_K) - 1)` forces `N + 2 ≤ d(G_K)`.
  by_contra! hlt
  have hsub : topologicalGeneratorRankNat (Field.absoluteGaloisGroup K) hG - 1 ≤
      Module.finrank ℚ_[p] K := by
    omega
  have := Nat.mul_le_mul_left (Module.finrank K L) hsub
  linarith [hpro.trans hschreier]

/-- **Every finite set topologically generating a local absolute Galois group has at least
`[K : ℚ_p] + 2` elements.** This is the lower half of the exact generator rank of `G_K`, stated
without assuming topological finite generation: a finite generating set is itself a witness. -/
theorem finrank_add_two_le_card_of_topologicalClosure_closure_eq_top_absoluteGaloisGroup
    (s : Finset (Field.absoluteGaloisGroup K))
    (hs : (Subgroup.closure (s : Set (Field.absoluteGaloisGroup K))).topologicalClosure = ⊤) :
    Module.finrank ℚ_[p] K + 2 ≤ s.card :=
  (le_topologicalGeneratorRankNat_absoluteGaloisGroup p K
    (isTopologicallyFinitelyGenerated_iff.mpr ⟨s, hs⟩)).trans (topologicalGeneratorRankNat_le _ hs)

end TauCeti
