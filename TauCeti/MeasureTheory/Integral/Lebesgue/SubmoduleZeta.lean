/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import TauCeti.LinearAlgebra.Submodule.Zeta
import TauCeti.MeasureTheory.Integral.Lebesgue.BiUnion

/-!
# Lebesgue integrals bounded by the submodule zeta function

Let `f ≥ 0` be a function on a measure space `(X, ρ)`, and sort the points of a set `s` by the
submodules of finite index of a module `N` over a ring `R`: almost every `x ∈ s` lies in some set
`S M` with `[N : M]^μ · f x · ρ (S M) ≤ V`. The weights `[N : M]^(-μ) V` are those of the submodule
zeta function `ζ_N(μ) = ∑_M [N : M]^(-μ)` (`Module.submoduleZeta`), so the bound by a weighted
countable cover (`TauCeti.setLIntegral_le_tsum_of_ae_exists_mul_measure_le`) becomes
`∫_s f dρ ≤ ζ_N(μ) V` once the submodules of finite index are countable, for instance when
`ζ_N(μ)` is finite (`Module.countable_of_submoduleZeta_ne_top`). This is how an integral over the
frequencies of Gauss sums is bounded, the frequencies being sorted by a conductor ideal.

## Main results

* `Module.setLIntegral_le_submoduleZeta_mul`: the bound `∫_s f dρ ≤ ζ_N(μ) V` when almost every
  `x ∈ s` lies in some `S M`, with `M` of finite index and `[N : M]^μ f x ρ (S M) ≤ V`.

## Attribution

`Module.setLIntegral_le_submoduleZeta_mul` and its proof plan (cut the domain into the pieces
where the bound holds for one ideal, and use the countability of the ideals of finite index) follow
`New.lintegral_le_idealZeta_mul` in the file `src/Lib/SiegelWeil/Mass.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). Here it is
stated for the submodules of a module over any ring, assuming only that the submodules of finite
index are countable, and derived from the bound for an arbitrary weighted countable cover.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Module

variable {R N X : Type*} [Ring R] [AddCommGroup N] [Module R N] [MeasurableSpace X]
  {ρ : Measure X} {f : X → ℝ≥0∞}

/-- **Integrals bounded by the submodule zeta function.** Let the submodules of finite index of
`N` be countable, and let `S M` be sets indexed by the submodules `M` of `N`. If almost every
`x ∈ s` lies in some `S M` with `M` of finite index and `[N : M]^μ · f x · ρ (S M) ≤ V`, then
`∫_s f dρ ≤ ζ_N(μ) · V`. For `N = R` this is the bound by the ideal zeta sum
`ζ_R(μ) = ∑_I [R : I]^(-μ)` over the left ideals of finite index. The countability holds when
`ζ_N(μ)` is finite (`Module.countable_of_submoduleZeta_ne_top`). -/
theorem setLIntegral_le_submoduleZeta_mul [Countable {M : Submodule R N // M.cardQuot ≠ 0}]
    {s : Set X} {S : Submodule R N → Set X} {μ : ℕ} {V : ℝ≥0∞}
    (h : ∀ᵐ x ∂ρ, x ∈ s → ∃ M : Submodule R N, M.cardQuot ≠ 0 ∧ x ∈ S M ∧
      (M.cardQuot : ℝ≥0∞) ^ μ * f x * ρ (S M) ≤ V) :
    ∫⁻ x in s, f x ∂ρ ≤ submoduleZeta R N μ * V := by
  rw [submoduleZeta_def, ← ENNReal.tsum_mul_right]
  refine TauCeti.setLIntegral_le_tsum_of_ae_exists_mul_measure_le (S := fun M ↦ S M.val)
    (h.mono fun x hx hxs ↦ ?_)
  obtain ⟨M, hM, hxM, hle⟩ := hx hxs
  refine ⟨⟨M, hM⟩, hxM, ?_⟩
  have h_index : (M.cardQuot : ℝ≥0∞) ^ μ ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hM)
  rw [mul_assoc, ENNReal.mul_le_iff_le_inv h_index (ENNReal.pow_ne_top
    (ENNReal.natCast_ne_top _))] at hle
  rwa [← ENNReal.inv_pow]

end Module
