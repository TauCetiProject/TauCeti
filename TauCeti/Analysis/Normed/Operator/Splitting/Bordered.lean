/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Splitting.Family
-- Private: used only inside proofs.
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Bordered operators and kernel vectors near a corank-one operator

The bordered operator `(w, μ) ↦ (L w + μ ℓ, ℓ w)` of `L : E → E*` and `ℓ ∈ E*` is injective
when the kernel of `L` lies in the line spanned by `v`, every `L w` vanishes at `v` (as when `L` is
symmetric and `L v = 0`), and `ℓ v = 1`. It is the pair of
`(w, μ) ↦ L w + μ ℓ` with the coordinate `(w, μ) ↦ ℓ w`, so if `E` is finite-dimensional over a
complete field, the kernel section `ContinuousLinearMap.kerSection` of that pair gives, for
operators `L z` near such an `L z₀`, a vector `W z` tending to `v` as `z → z₀`, which is the kernel
vector of `L z` normalized by `ℓ` whenever `L z` is degenerate.

## Main results

* `ContinuousLinearMap.injective_coprod_toSpanSingleton_prod_comp_fst`: the bordered operator of
  an operator whose kernel lies in a line that its range annihilates is injective.
* `ContinuousLinearMap.exists_tendsto_eventually_apply_eq_zero`: for operators `L z` near an
  operator `L z₀` with kernel spanned by `v`, a vector annihilated by its range, a kernel vector
  of `L z` normalized by `ℓ`, tending to `v` as `z → z₀`.
-/

public section

namespace ContinuousLinearMap

open Filter Function Module Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If the kernel of `H₀ : E → E*` lies in the line spanned by `v`, every `H₀ w` vanishes at `v`
(as when `H₀` is symmetric and `H₀ v = 0`), and `ℓ v = 1`, the bordered operator
`(w, μ) ↦ (H₀ w + μ ℓ, ℓ w)` of `H₀` and `ℓ` is injective. -/
theorem injective_coprod_toSpanSingleton_prod_comp_fst {H₀ : E →L[𝕜] StrongDual 𝕜 E}
    {v : E} (hrange : ∀ w, H₀ w v = 0) {ℓ : StrongDual 𝕜 E} (hℓ : ℓ v = 1)
    (hker : ∀ u, H₀ u = 0 → ∃ c : 𝕜, u = c • v) :
    Injective ((H₀.coprod (toSpanSingleton 𝕜 ℓ)).prod (ℓ ∘L fst 𝕜 E 𝕜)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨w, μ⟩ h
  simp only [prod_apply, coprod_apply, toSpanSingleton_apply, comp_apply, coe_fst',
    Prod.mk_eq_zero] at h
  obtain ⟨h1, h2⟩ := h
  -- Pairing the first component with `v` kills `H₀ w` and leaves `μ`.
  have hμ : μ = 0 := by simpa [hrange w, hℓ] using congrArg (· v) h1
  subst hμ
  -- Over a general field `simp` does not apply `zero_smul` to `StrongDual 𝕜 E` by itself, so the
  -- instance `zero_smul 𝕜 ℓ` is supplied here and below.
  obtain ⟨c, rfl⟩ := hker w (by simpa [zero_smul 𝕜 ℓ] using h1)
  simp_all

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- **Kernel vectors near a corank-one operator.** Let `L z : E → E*` depend continuously on `z`
at `z₀`, with the kernel of `L z₀` the line spanned by `v`, every `L z₀ w` vanishing at `v` (as
when `L z₀` is symmetric), and let `ℓ v = 1`.
Then there is a function `W`, tending to `v` at `z₀`, such that near `z₀`, whenever `L z` has a
nonzero kernel vector, `W z` is the kernel vector of `L z` normalized by `ℓ`. It is the first
component of the kernel section, at `1`, of `(w, μ) ↦ L z w + μ ℓ` with coordinate
`(w, μ) ↦ ℓ w`; the pair is the bordered operator of `L z` and `ℓ`, invertible near `z₀`. -/
theorem exists_tendsto_eventually_apply_eq_zero {X : Type*} [TopologicalSpace X]
    {L : X → E →L[𝕜] StrongDual 𝕜 E} {z₀ : X} (hL : ContinuousAt L z₀)
    {v : E} (hv : L z₀ v = 0) (hrange : ∀ w, L z₀ w v = 0) {ℓ : StrongDual 𝕜 E}
    (hℓ : ℓ v = 1) (hker : ∀ u, L z₀ u = 0 → ∃ c : 𝕜, u = c • v) :
    ∃ W : X → E, Tendsto W (𝓝 z₀) (𝓝 v) ∧
      ∀ᶠ z in 𝓝 z₀, ∀ u, L z u = 0 → u ≠ 0 → L z (W z) = 0 ∧ ℓ (W z) = 1 := by
  -- Completeness of `E × 𝕜`, needed for the continuity of the kernel section.
  have := FiniteDimensional.completeSpace 𝕜 E
  set A := fun z ↦ (L z).coprod (toSpanSingleton 𝕜 ℓ)
  set q := ℓ ∘L fst 𝕜 E 𝕜
  have hdim : finrank 𝕜 (E × 𝕜) = finrank 𝕜 (StrongDual 𝕜 E × 𝕜) := by
    simp [dual_finrank_eq]
  have h₀ : ((A z₀).prod q).IsInvertible := (isInvertible_iff_injective_of_finrank_eq hdim).2
    (injective_coprod_toSpanSingleton_prod_comp_fst hrange hℓ hker)
  have hA : ContinuousAt A z₀ := hL.continuousLinearMapCoprod continuousAt_const
  -- A vector `(w, 0)` with `L z w = 0` and `ℓ w = 1` is the kernel section at `1`.
  have hsec : ∀ z, ((A z).prod q).IsInvertible → ∀ w, L z w = 0 → ℓ w = 1 →
      (A z).kerSection q 1 = (w, 0) := fun z hz w hw hℓw ↦ by
    have hmem : ((w, 0) : E × 𝕜) ∈ (A z).ker := by simp [A, hw, zero_smul 𝕜 ℓ]
    simpa [q, hℓw] using kerSection_apply_of_mem_ker hz hmem
  refine ⟨fun z ↦ ((A z).kerSection q 1).1, ?_, ?_⟩
  · have h := (continuous_fst.continuousAt.comp ((apply 𝕜 _ (1 : 𝕜)).continuous.continuousAt.comp
      (hA.kerSection continuousAt_const h₀))).tendsto
    simpa [Function.comp_def, hsec z₀ h₀ v hv hℓ] using h
  · have hpair : ContinuousAt (fun z ↦ (A z).prod q) z₀ :=
      (prodL 𝕜).continuous.continuousAt.comp (f := fun z ↦ (A z, q)) (hA.prodMk continuousAt_const)
    filter_upwards [hpair.eventually h₀.eventually_nhds] with z hz u hu hu0
    -- The kernel vector `u` is not killed by `ℓ`, since `(u, 0)` is not killed by the pair.
    have hℓu : ℓ u ≠ 0 := fun h0 ↦ hu0 <| congrArg Prod.fst <|
      hz.injective (a₁ := (u, 0)) (a₂ := 0) (by simp [A, q, hu, h0, zero_smul 𝕜 ℓ])
    -- As for `zero_smul`, `simp` needs this instance of `smul_zero` on `StrongDual 𝕜 E`.
    have h0 : (ℓ u)⁻¹ • (0 : StrongDual 𝕜 E) = 0 := smul_zero (M := 𝕜) (A := StrongDual 𝕜 E) _
    rw [hsec z hz ((ℓ u)⁻¹ • u) (by simp [hu, h0]) (by simp [hℓu])]
    simp [hu, hℓu, h0]

end ContinuousLinearMap
