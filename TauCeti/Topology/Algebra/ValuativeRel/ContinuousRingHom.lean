/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Continuity and compatibility of valued field homomorphisms

The algebra map of a compatible valued field extension is continuous if nonzero values of the
base field are coinitial among the nonzero values of the extension. Algebraic extensions satisfy
this condition, with no restriction on the rank of the valuations or completeness of the fields.
Compatibility alone does not imply continuity for transcendental extensions.

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

* `TauCeti.continuous_algebraMap_of_coinitial`: coinitiality of nonzero base-field values implies
  continuity of the algebra map of a compatible extension.
* `TauCeti.continuous_algebraMap_of_valuativeExtension`: the algebra map of an algebraic
  compatible extension is continuous.
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

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsValuativeTopology K] [DivisionRing L] [ValuativeRel L] [TopologicalSpace L]
  [IsValuativeTopology L] [Algebra K L] [ValuativeExtension K L]

/-- The algebra map of a compatible extension is continuous if the nonzero base-field values
are coinitial among the nonzero target values. -/
theorem continuous_algebraMap_of_coinitial
    (h : ∀ y : L, y ≠ 0 → ∃ x : K, x ≠ 0 ∧ algebraMap K L x ≤ᵥ y) :
    Continuous (algebraMap K L) := by
  refine continuous_of_continuousAt_zero (algebraMap K L) ?_
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)).mpr fun γ _ ↦ ?_
  obtain ⟨y, hy⟩ := valuation_surjective γ.val
  have hy0 : y ≠ 0 := by
    intro h0
    exact γ.ne_zero (by simpa [h0] using hy.symm)
  obtain ⟨x, hx0, hxy⟩ := h y hy0
  refine ⟨Units.mk0 (valuation K x) (by simpa using hx0), trivial, fun z hz ↦ ?_⟩
  have hz' : z <ᵥ x := (valuation K).vlt_iff_lt.mpr hz
  exact ((valuation L).vlt_iff_lt.mp (ValuativeExtension.vlt_iff_vlt.mpr hz')).trans_le
    (((valuation L).vle_iff_le.mp hxy).trans_eq hy)

end TauCeti

/-- The algebra map of an algebraic compatible extension is continuous for the valuative
topologies. -/
theorem TauCeti.continuous_algebraMap_of_valuativeExtension (K L : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsValuativeTopology L]
    [Algebra K L] [ValuativeExtension K L] [Algebra.IsAlgebraic K L] :
    Continuous (algebraMap K L) :=
  continuous_algebraMap_of_coinitial K L fun y hy ↦
    (Algebra.IsAlgebraic.isAlgebraic y).exists_ne_zero_vle hy

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
