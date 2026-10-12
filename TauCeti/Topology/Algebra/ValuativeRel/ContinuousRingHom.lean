/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Continuous ring homomorphisms preserve valuations

Let `K` and `L` be division rings whose topologies are induced by their valuative relations, with
archimedean value groups (that is, of rank at most one), and with the valuation of `K`
nontrivial. This file proves that every continuous ring homomorphism `f : K →+* L` preserves and
reflects the valuative relation: `f x ≤ᵥ f y ↔ x ≤ᵥ y`. Nonarchimedean local fields satisfy these
hypotheses. So a field isomorphism of nonarchimedean local fields that is a homeomorphism is
compatible with their valuations, and an algebra between such fields whose structure map is
continuous is a `ValuativeExtension`; this is what allows constructions made from the valuation of
a local field to be compared along an isomorphism that is only known to be topological.

The bridge between topology and valuation is topological nilpotence. In a valuative topology the
open unit ball `{x | v x < 1}` is a neighbourhood of `0`, so a topologically nilpotent element has
valuation `< 1` (`IsTopologicallyNilpotent.valuation_lt_one`); conversely, when the value group is
archimedean, the powers of an element of valuation `< 1` enter every ball around `0`
(`isTopologicallyNilpotent_iff_valuation_lt_one`, in
`TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent`). Since a continuous homomorphism
preserves topological nilpotence, `v_K x < 1` implies `v_L (f x) < 1`. For the reverse
implication, let `v_K x ≥ 1` and pick `π` with `0 < v_K π < 1`. Then `v_K (π / xⁿ) < 1` for
every `n`, so `v_L (f π) < v_L (f x) ^ n` for every `n`, which, the value group of `L` being
archimedean, forces `v_L (f x) ≥ 1`. Two valuations on a division ring with the same open unit
ball are equivalent (`Valuation.isEquiv_iff_val_lt_one`). This is the argument of Neukirch,
Chapter II, Proposition (3.3), for absolute values.

## Main results

* `RingHom.isEquiv_comap_valuation_of_continuous`: the pullback of the valuation of `L` along a
  continuous `f : K →+* L` is equivalent to the valuation of `K`.
* `RingHom.map_vle_map_iff_of_continuous`: a continuous `f : K →+* L` satisfies
  `f x ≤ᵥ f y ↔ x ≤ᵥ y`.
* `ValuativeExtension.of_continuous_algebraMap`: an algebra whose structure map is continuous is a
  valuative extension.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (3.3).
-/

public section

open ValuativeRel

section RingHom

variable {K L : Type*} [DivisionRing K] [ValuativeRel K] [TopologicalSpace K]
  [IsValuativeTopology K] [IsNontrivial K] [MulArchimedean (ValueGroupWithZero K)]
  [DivisionRing L] [ValuativeRel L] [TopologicalSpace L] [IsValuativeTopology L]
  [MulArchimedean (ValueGroupWithZero L)]

namespace RingHom

/-- **A continuous ring homomorphism preserves the valuation up to equivalence**: the pullback of
the valuation of `L` along a continuous `f : K →+* L` is equivalent to the valuation of `K`. -/
theorem isEquiv_comap_valuation_of_continuous (f : K →+* L) (hf : Continuous f) :
    ((valuation L).comap f).IsEquiv (valuation K) := by
  refine Valuation.isEquiv_iff_val_lt_one.mpr fun {x} ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  swap
  · -- Continuity carries topological nilpotence from `x` to `f x`.
    exact ((TauCeti.isTopologicallyNilpotent_of_valuation_lt_one hx).map hf).valuation_lt_one
  -- Otherwise `1 ≤ v_K x`. With `0 < v_K a < 1`, `v_K (a / xⁿ) < 1`, hence
  -- `v_L (f a) < v_L (f x) ^ n` for every `n`, contradicting `v_L (f x) < 1` as the value group
  -- of `L` is archimedean.
  rw [Valuation.comap_apply] at hx
  by_contra hx1
  rw [not_lt] at hx1
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx1
  obtain ⟨γ, hγ0, hπ⟩ := IsNontrivial.exists_lt_one (R := K)
  obtain ⟨a, rfl⟩ := valuation_surjective γ
  have ha : a ≠ 0 := by rintro rfl; simp at hγ0
  have hfa : valuation L (f a) ≠ 0 := by simpa using f.injective.ne ha
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx (Units.mk0 _ hfa)
  have hlt : valuation K (a / x ^ n) < 1 := by
    rw [map_div₀, map_pow, div_lt_one₀ (pow_pos (zero_lt_iff.mpr (by simpa using hx0)) n)]
    exact hπ.trans_le (one_le_pow₀ hx1)
  have hlt' := ((TauCeti.isTopologicallyNilpotent_of_valuation_lt_one hlt).map hf).valuation_lt_one
  rw [map_div₀, map_pow, map_div₀, map_pow,
    div_lt_one₀ (pow_pos (zero_lt_iff.mpr (by simpa using f.injective.ne hx0)) n)] at hlt'
  exact hn.not_gt hlt'

/-- **A continuous ring homomorphism preserves and reflects the valuative relation.** -/
@[simp]
theorem map_vle_map_iff_of_continuous (f : K →+* L) (hf : Continuous f) (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rw [(valuation L).vle_iff_le, (valuation K).vle_iff_le]
  exact f.isEquiv_comap_valuation_of_continuous hf x y

end RingHom

end RingHom

section Algebra

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
  [IsNontrivial K] [MulArchimedean (ValueGroupWithZero K)]
  [DivisionRing L] [ValuativeRel L] [TopologicalSpace L] [IsValuativeTopology L]
  [MulArchimedean (ValueGroupWithZero L)]

/-- **An algebra whose structure map is continuous is a valuative extension**: the valuative
relation of `L` restricts to that of `K`. -/
theorem ValuativeExtension.of_continuous_algebraMap [Algebra K L]
    (hf : Continuous (algebraMap K L)) : ValuativeExtension K L :=
  ⟨(algebraMap K L).map_vle_map_iff_of_continuous hf⟩

end Algebra
