/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Torsion

/-!
# Base change of derived complete modules of finite rank over a discrete valuation ring

Let `W` be a discrete valuation ring which is derived `π`-complete for an element `π`, and `X` a
derived `π`-complete `W`-module of finite rank. Then for every `W`-algebra `S` which is derived
complete for the image of `π`, the base change `S ⊗[W] X` is derived complete
(`TauCeti.IsDerivedComplete.baseChange`). Derived completeness is not preserved by tensor products
in general; here the rank hypothesis makes `X` a free module of finite rank up to a power of `π`
(`TauCeti.IsDerivedComplete.exists_comp_eq_pow_smul_of_rank_lt_aleph0`): there are maps
`τ : Wˢ → X` and `σ : X → Wˢ` with `τ ∘ σ = πᵏ` and `σ ∘ τ = πᵏ`. Their base changes are again
inverse to each other up to `πᵏ`, and derived completeness passes along such maps
(`TauCeti.IsDerivedComplete.of_comp_eq_smul`) from `Sˢ` to `S ⊗[W] X`.

The map `τ` is given by a maximal linearly independent family, which is finite, of size `s`, by
the rank hypothesis. Every element of `X` then has a nonzero multiple in the image of `τ`, so the
quotient `X ⧸ τ(Wˢ)` is `π`-power torsion. It is derived complete, as the cokernel of a map of
derived complete modules, so it is killed by a single power `πᵏ`
(`TauCeti.IsDerivedComplete.exists_isTorsionBy_pow`), and `σ` is `πᵏ` followed by the inverse of
`τ` on its image.

## Main results

* `TauCeti.IsDerivedComplete.exists_comp_eq_pow_smul_of_rank_lt_aleph0`: a derived complete
  module of finite rank over a derived complete discrete valuation ring is free of finite rank up
  to a power of `π`.
* `TauCeti.IsDerivedComplete.baseChange`: base change of such a module along an algebra which is
  derived complete for `π` is derived complete.

## References

* ShortProof, `grh/src/Lib/PadicComparison/Completion.lean` in
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>,
  Apache 2.0, Copyright 2026 Anthropic, PBC. The finite-rank construction and base-change
  argument follow `New.Variety.IsDerivedComplete.baseChange`.
* [Stacks Project, Section 15.93, Tag 091N](https://stacks.math.columbia.edu/tag/091N).
-/

public section

open Function TensorProduct

namespace TauCeti

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {π : W}
  {X : Type*} [AddCommGroup X] [Module W X]

namespace IsDerivedComplete

/-- **Derived complete modules of finite rank are free up to a power of `π`.** Let `W` be a
discrete valuation ring and `X` a `W`-module of finite rank, both derived `π`-complete. Then there
are `s`, `k` and linear maps `τ : Wˢ → X` and `σ : X → Wˢ` with `τ ∘ σ = πᵏ` and `σ ∘ τ = πᵏ`. -/
theorem exists_comp_eq_pow_smul_of_rank_lt_aleph0 (hW : IsDerivedComplete (Ideal.span {π}) W)
    (hX : IsDerivedComplete (Ideal.span {π}) X) (hrank : Module.rank W X < Cardinal.aleph0) :
    ∃ (s k : ℕ) (τ : (Fin s → W) →ₗ[W] X) (σ : X →ₗ[W] (Fin s → W)),
      (∀ x, τ (σ x) = π ^ k • x) ∧ ∀ v, σ (τ v) = π ^ k • v := by
  have hπ : ¬IsUnit π := fun hu ↦ by
    rw [Ideal.span_singleton_eq_top.2 hu, isDerivedComplete_top_iff] at hW
    exact not_subsingleton W hW
  -- A maximal linearly independent family, finite by the rank hypothesis, numbered by `Fin n`.
  obtain ⟨t, ht, hmax⟩ := exists_maximal_linearIndepOn W (id : X → X)
  have : Finite t := Cardinal.lt_aleph0_iff_finite.1
    (ht.linearIndependent.cardinal_le_rank.trans_lt hrank)
  set n := Nat.card t
  let v : Fin n → X := Subtype.val ∘ (Finite.equivFin t).symm
  set τ := Fintype.linearCombination W v
  have hτ : Injective τ := linearIndependent_iff_injective_fintypeLinearCombination.1 <|
    ht.linearIndependent.comp _ (Finite.equivFin t).symm.injective
  -- Every element of `X` has a nonzero multiple in the image of `τ`.
  have hdep (x : X) : ∃ b : W, b ≠ 0 ∧ b • x ∈ LinearMap.range τ := by
    rw [Fintype.range_linearCombination, Set.range_comp, (Finite.equivFin t).symm.range_eq_univ,
      Set.image_univ, Subtype.range_coe]
    by_cases hx : x ∈ t
    · exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hx⟩
    · simpa using hmax x hx
  -- The quotient `X ⧸ τ(Wⁿ)` is `π`-power torsion and derived complete, hence killed by `πᵏ`.
  have htors : Module.IsTorsion' (X ⧸ LinearMap.range τ) (Submonoid.powers π) := by
    refine Submodule.isTorsion'_powers_iff π |>.2 fun q ↦ ?_
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨b, hb, hbx⟩ := hdep x
      obtain ⟨j, c, hc⟩ := IsDiscreteValuationRing.exists_dvd_pow_of_ne_zero_of_not_isUnit hb hπ
      refine ⟨j, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hc, mul_comm, mul_smul]
      exact Submodule.smul_mem _ c hbx
  obtain ⟨k, hk⟩ := ((pi fun _ ↦ hW).quotient_range hX τ).exists_isTorsionBy_pow
    (Ideal.mem_span_singleton_self π) htors
  have hkτ (x : X) : π ^ k • x ∈ LinearMap.range τ := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hk (x := Submodule.Quotient.mk x)
  -- `σ` is `πᵏ` followed by the inverse of `τ` on its image.
  let σ : X →ₗ[W] (Fin n → W) := (LinearEquiv.ofInjective τ hτ).symm.toLinearMap ∘ₗ
    ((π ^ k) • LinearMap.id).codRestrict (LinearMap.range τ) hkτ
  have hτσ (x : X) : τ (σ x) = π ^ k • x := by
    simp [σ]
  exact ⟨n, k, τ, σ, hτσ, fun w ↦ hτ (by rw [hτσ, map_smul])⟩

/-- **Base change of derived complete modules of finite rank.** Let `W` be a discrete valuation
ring and `X` a `W`-module of finite rank, both derived `π`-complete, and `S` a `W`-algebra which
is derived complete for the image of `π`. Then `S ⊗[W] X` is derived complete for the image
of `π`. -/
theorem baseChange (hW : IsDerivedComplete (Ideal.span {π}) W)
    (hX : IsDerivedComplete (Ideal.span {π}) X) (hrank : Module.rank W X < Cardinal.aleph0)
    (S : Type*) [CommRing S] [Algebra W S]
    (hS : IsDerivedComplete (Ideal.span {algebraMap W S π}) S) :
    IsDerivedComplete (Ideal.span {algebraMap W S π}) (S ⊗[W] X) := by
  obtain ⟨s, k, τ, σ, hτσ, -⟩ := exists_comp_eq_pow_smul_of_rank_lt_aleph0 hW hX hrank
  have hcomp : τ ∘ₗ σ = (π ^ k) • LinearMap.id := LinearMap.ext hτσ
  refine (((pi fun _ ↦ hS).of_linearEquiv (piScalarRight W S S (Fin s)).symm)).of_comp_eq_smul
    (τ.baseChange S) (σ.baseChange S) (c := algebraMap W S π ^ k) (fun z ↦ ?_) ?_
  · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]
    simp [LinearMap.baseChange_smul, ← map_pow, algebraMap_smul]
  · exact Ideal.span_le.2 <| Set.singleton_subset_iff.2 ⟨k, Ideal.mem_span_singleton_self _⟩

end IsDerivedComplete

end TauCeti
