/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import TauCeti.LinearAlgebra.Submodule.Zeta

/-!
# Lebesgue integrals over a weighted countable cover

Let `f ≥ 0` be a function on a measure space `(X, ρ)` and `(S i)` a countable family of sets with
weights `w i`. If almost every point `x` of a set `s` lies in some `S i` with
`f x · ρ (S i) ≤ w i`, then `∫_s f dρ ≤ ∑ᵢ w i`. On the points of `S i` where that bound holds,
`f` is at most `w i / ρ (S i)`, so their integral is at most `w i`; then sum over `i`. No
measurability of `f`, `s` or the `S i` is needed.

The main application sorts the points by the submodules of finite index of a module `N` over a
ring `R`, with the weights `[N : M]^(-μ) V` of the submodule zeta function
`ζ_N(μ) = ∑_M [N : M]^(-μ)` (`Module.submoduleZeta`). Its finiteness makes the submodules of
finite index countable, and the bound becomes `∫_s f dρ ≤ ζ_N(μ) V`. This is how an integral over
the frequencies of Gauss sums is bounded, the frequencies being sorted by a conductor ideal.

## Main results

* `TauCeti.setLIntegral_le_tsum_of_ae_exists_mul_measure_le`: the bound by a weighted countable
  cover.
* `Module.setLIntegral_le_submoduleZeta_mul`: the bound `∫_s f dρ ≤ ζ_N(μ) V` when almost every
  `x ∈ s` lies in some `S M`, with `M` of finite index and `[N : M]^μ f x ρ (S M) ≤ V`.

## Attribution

`Module.setLIntegral_le_submoduleZeta_mul` and its proof plan (cut the domain into the pieces
where the bound holds for one ideal, and get the countability of the ideals of finite index from
the finiteness of the zeta sum) follow `New.lintegral_le_idealZeta_mul` in the file
`src/Lib/SiegelWeil/Mass.lean` of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic, PBC). Here it is stated for the submodules of a module over any ring,
under `ζ_N(μ) < ∞`, and derived from the bound for an arbitrary weighted countable cover.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X} {f : X → ℝ≥0∞}

/-- If `f x · ρ S ≤ w` on a subset `t` of `S`, then the integral of `f` over `t` is at most `w`. -/
private theorem setLIntegral_le_of_forall_mul_measure_le {t S : Set X} {w : ℝ≥0∞} (hts : t ⊆ S)
    (h : ∀ x ∈ t, f x * ρ S ≤ w) : ∫⁻ x in t, f x ∂ρ ≤ w := by
  rcases eq_or_ne (ρ S) 0 with h0 | h0
  · rw [setLIntegral_measure_zero _ _ (measure_mono_null hts h0)]
    exact zero_le
  rcases eq_or_ne w ∞ with htop | htop
  · exact htop ▸ le_top
  calc ∫⁻ x in t, f x ∂ρ
    _ ≤ ∫⁻ _ in t, w / ρ S ∂ρ := setLIntegral_mono measurable_const fun x hx ↦
        (ENNReal.le_div_iff_mul_le (.inl h0) (.inr htop)).2 (h x hx)
    _ = w / ρ S * ρ t := setLIntegral_const t _
    _ ≤ ρ S * (w / ρ S) := by rw [mul_comm]; gcongr
    _ ≤ w := ENNReal.mul_div_le

/-- **Integrals over a weighted countable cover.** Let `(S i)` be a countable family of sets with
weights `w i`. If almost every `x ∈ s` lies in some `S i` with `f x · ρ (S i) ≤ w i`, then
`∫_s f dρ ≤ ∑ᵢ w i`. -/
theorem setLIntegral_le_tsum_of_ae_exists_mul_measure_le {ι : Type*} [Countable ι] {s : Set X}
    {S : ι → Set X} {w : ι → ℝ≥0∞} (h : ∀ᵐ x ∂ρ, x ∈ s → ∃ i, x ∈ S i ∧ f x * ρ (S i) ≤ w i) :
    ∫⁻ x in s, f x ∂ρ ≤ ∑' i, w i := by
  -- The points of `S i` where the bound holds cover almost all of `s`.
  let T (i : ι) : Set X := {x | x ∈ S i ∧ f x * ρ (S i) ≤ w i}
  have h_cover : s ≤ᵐ[ρ] ⋃ i, T i :=
    h.mono fun x hx hxs ↦ mem_iUnion.2 (hx hxs)
  calc ∫⁻ x in s, f x ∂ρ
    _ ≤ ∫⁻ x in ⋃ i, T i, f x ∂ρ := lintegral_mono' (Measure.restrict_mono_ae h_cover) le_rfl
    _ ≤ ∑' i, ∫⁻ x in T i, f x ∂ρ := lintegral_iUnion_le T f
    _ ≤ ∑' i, w i := tsum_le_tsum fun i ↦
        setLIntegral_le_of_forall_mul_measure_le (fun _ hx ↦ hx.1) fun _ hx ↦ hx.2

end TauCeti

namespace Module

variable {R N X : Type*} [Ring R] [AddCommGroup N] [Module R N] [MeasurableSpace X]
  {ρ : Measure X} {f : X → ℝ≥0∞}

/-- **Integrals bounded by the submodule zeta function.** Let `ζ_N(μ)` be finite, and let `S M`
be sets indexed by the submodules `M` of `N`. If almost every `x ∈ s` lies in some `S M` with `M`
of finite index and `[N : M]^μ · f x · ρ (S M) ≤ V`, then `∫_s f dρ ≤ ζ_N(μ) · V`. For `N = R`
this is the bound by the ideal zeta sum `ζ_R(μ) = ∑_I [R : I]^(-μ)` over the left ideals of
finite index. -/
theorem setLIntegral_le_submoduleZeta_mul {s : Set X} {S : Submodule R N → Set X} {μ : ℕ}
    {V : ℝ≥0∞} (hζ : submoduleZeta R N μ ≠ ∞)
    (h : ∀ᵐ x ∂ρ, x ∈ s → ∃ M : Submodule R N, M.cardQuot ≠ 0 ∧ x ∈ S M ∧
      (M.cardQuot : ℝ≥0∞) ^ μ * f x * ρ (S M) ≤ V) :
    ∫⁻ x in s, f x ∂ρ ≤ submoduleZeta R N μ * V := by
  have := countable_of_submoduleZeta_ne_top hζ
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
