/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.ModuleTopology
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.Topology.Algebra.Module.Equicontinuity

/-!
# The universal property of restricted series with module coefficients

Let `A` be a ring and `M` a topological `A`-module whose topology comes from a uniform additive
group structure. With the topology of uniform convergence of coefficients
(`TauCeti.Huber.restrictedMvPowerSeriesSubmoduleUniformSpace`), the module `M⟨T₁, …, Tₖ⟩` of
restricted series behaves as the completed direct sum of copies of `M`, one for each monomial `Tˢ`.
This file proves the corresponding universal property.

Each monomial gives an `A`-linear map `m ↦ m Tˢ` from `M` to `M⟨T₁, …, Tₖ⟩`. Every restricted
series `f` is the sum `f = ∑ₛ fₛ Tˢ` of its monomial terms in this topology
(`hasSum_restrictedMvPowerSeriesSubmoduleMonomial`). The target `N` is a complete Hausdorff
nonarchimedean topological `A`-module, and `(φₛ)ₛ` is a family of `A`-linear maps `M → N`,
indexed by the monomials and equicontinuous at `0`. Then

```text
Φ(f) = ∑ₛ φₛ(fₛ)
```

converges and defines the unique continuous `A`-linear map `Φ : M⟨T₁, …, Tₖ⟩ → N` with
`Φ(m Tˢ) = φₛ(m)`. The equicontinuity hypothesis cannot be dropped: for every continuous linear
`Ψ` out of `M⟨T₁, …, Tₖ⟩` the family `Ψ(· Tˢ)` is equicontinuous at `0`
(`equicontinuousAt_comp_restrictedMvPowerSeriesSubmoduleMonomial`), because `m Tˢ` lies in the
basic neighbourhood `{f | ∀ t, fₜ ∈ V}` of `0` as soon as `m ∈ V`. Continuous `A`-linear maps
out of `M⟨T₁, …, Tₖ⟩` therefore correspond exactly to such families.

The expansion `f = ∑ₛ fₛ Tˢ`, uniqueness, and the equicontinuity of `Ψ(· Tˢ)` hold more
generally over a semiring `A`, for `M` any uniform `A`-module with continuous addition and
fixed-scalar multiplication; `M` need not have additive inverses. The equicontinuity statement
also needs no additive-group structure on its target. Neither completeness nor separatedness
of `M` is used. They are needed only for `M⟨T₁, …, Tₖ⟩` itself to be complete and Hausdorff
(`completeSpace_restrictedMvPowerSeriesSubmodule` and
`t2Space_restrictedMvPowerSeriesSubmodule`). The completeness and the nonarchimedean property of
`N` are what make the sums `∑ₛ φₛ(fₛ)` converge, and they are not needed for uniqueness
(`restrictedMvPowerSeriesSubmodule_linearMap_ext_of_continuous`).

This is the module-coefficient counterpart of the universal property of the ring `A⟨T₁, …, Tₖ⟩`
(Wedhorn, Proposition 5.50, `existsUnique_continuous_ringHom_weightedRestrictedSubring`). That
statement concerns the multiplicative structure, which `M⟨T₁, …, Tₖ⟩` does not have, so neither
result implies the other.

## Main definitions

* `TauCeti.Huber.restrictedMvPowerSeriesSubmoduleMonomial`: the monomial map `m ↦ m Tˢ`,
  `M →ₗ[A] M⟨T₁, …, Tₖ⟩`.
* `TauCeti.Huber.restrictedMvPowerSeriesSubmoduleLift`: the map `f ↦ ∑ₛ φₛ(fₛ)` out of
  `M⟨T₁, …, Tₖ⟩` induced by an equicontinuous family `(φₛ)ₛ`.

## Main results

* `TauCeti.Huber.hasSum_restrictedMvPowerSeriesSubmoduleMonomial`: every restricted series is the
  sum of its monomial terms.
* `TauCeti.Huber.restrictedMvPowerSeriesSubmoduleMap_monomial`: the functoriality of
  `M ↦ M⟨T₁, …, Tₖ⟩` acts on monomials through their coefficients.
* `TauCeti.Huber.restrictedMvPowerSeriesSubmodule_linearMap_ext_of_continuous`: a continuous
  linear map out of `M⟨T₁, …, Tₖ⟩` into a Hausdorff module is determined by its values on
  monomials.
* `TauCeti.Huber.continuous_restrictedMvPowerSeriesSubmoduleLift` and
  `TauCeti.Huber.restrictedMvPowerSeriesSubmoduleLift_monomial`: the lift is continuous and takes
  the prescribed values on monomials.
* `TauCeti.Huber.existsUnique_continuous_linearMap_restrictedMvPowerSeriesSubmodule`: the
  universal property.
* `TauCeti.Huber.equicontinuousAt_comp_restrictedMvPowerSeriesSubmoduleMonomial`: its converse,
  that every continuous linear map out of `M⟨T₁, …, Tₖ⟩` arises from an equicontinuous family.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §5.6 and Proposition 5.50.
-/

public section

open Filter Topology Uniformity

namespace TauCeti.Huber

section General

variable {k : ℕ} {A M : Type*} [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]
  [ContinuousAdd M] [ContinuousConstSMul A M]

section Lift

variable {N : Type*} [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [Module A N]

/-- The terms `φₛ(fₛ)` tend to `0`, because the coefficients `fₛ` do and the `φₛ` are
equicontinuous at `0`. -/
private theorem tendsto_cofinite_apply_coeff {φ : (Fin k →₀ ℕ) → M →ₗ[A] N}
    (hφ : EquicontinuousAt (fun s ↦ ⇑(φ s)) 0) (f : restrictedMvPowerSeriesSubmodule k A M) :
    Tendsto (fun s ↦ φ s (((f : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) s)) cofinite
      (𝓝 0) := fun W hW ↦ mem_map.mpr <| by
  filter_upwards [(isRestricted_iff.mp (mem_restrictedMvPowerSeriesSubmodule.mp f.2)).eventually
    (equicontinuousAt_eventually_forall_apply_mem hφ hW)] with s hs
  exact hs s

variable [ContinuousConstSMul A N] [T2Space N] [CompleteSpace N] [NonarchimedeanAddGroup N]

/-- The linear map `f ↦ ∑ₛ φₛ(fₛ)` out of `M⟨T₁, …, Tₖ⟩` induced by a family of linear maps
`φₛ : M → N` equicontinuous at `0`, into a complete Hausdorff nonarchimedean module. It sends
`m Tˢ` to `φₛ(m)` (`restrictedMvPowerSeriesSubmoduleLift_monomial`). When `M` is a uniform
additive group it is continuous for the topology of uniform convergence of coefficients
(`continuous_restrictedMvPowerSeriesSubmoduleLift`), and it is the unique continuous linear map
sending `m Tˢ` to `φₛ(m)`
(`existsUnique_continuous_linearMap_restrictedMvPowerSeriesSubmodule`). -/
noncomputable def restrictedMvPowerSeriesSubmoduleLift (φ : (Fin k →₀ ℕ) → M →ₗ[A] N)
    (hφ : EquicontinuousAt (fun s ↦ ⇑(φ s)) 0) :
    restrictedMvPowerSeriesSubmodule k A M →ₗ[A] N where
  toFun f := ∑' s, φ s (((f : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) s)
  map_add' f g := by
    have hf := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_cofinite_apply_coeff hφ f)
    have hg := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_cofinite_apply_coeff hφ g)
    rw [← (hf.hasSum.add hg.hasSum).tsum_eq]
    exact tsum_congr fun s ↦ map_add (φ s) _ _
  map_smul' a f := by
    have hf := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_cofinite_apply_coeff hφ f)
    rw [RingHom.id_apply, ← (hf.hasSum.const_smul a).tsum_eq]
    exact tsum_congr fun s ↦ map_smul (φ s) _ _

/-- The lift of `(φₛ)ₛ` sends `f` to the sum of the terms `φₛ(fₛ)`. -/
theorem hasSum_restrictedMvPowerSeriesSubmoduleLift {φ : (Fin k →₀ ℕ) → M →ₗ[A] N}
    (hφ : EquicontinuousAt (fun s ↦ ⇑(φ s)) 0) (f : restrictedMvPowerSeriesSubmodule k A M) :
    HasSum (fun s ↦ φ s (((f : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) s))
      (restrictedMvPowerSeriesSubmoduleLift φ hφ f) :=
  (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_cofinite_apply_coeff hφ f)).hasSum

/-- The lift of `(φₛ)ₛ` sends the monomial `m Tˢ` to `φₛ(m)`. -/
@[simp]
theorem restrictedMvPowerSeriesSubmoduleLift_monomial {φ : (Fin k →₀ ℕ) → M →ₗ[A] N}
    (hφ : EquicontinuousAt (fun s ↦ ⇑(φ s)) 0) (s : Fin k →₀ ℕ) (m : M) :
    restrictedMvPowerSeriesSubmoduleLift φ hφ (restrictedMvPowerSeriesSubmoduleMonomial s m) =
      φ s m := by
  refine (hasSum_restrictedMvPowerSeriesSubmoduleLift hφ _).unique ?_
  simpa using hasSum_single (f := fun t ↦ φ t ((Pi.single s m : (Fin k →₀ ℕ) → M) t)) s
    fun t ht ↦ by simp [ht]

end Lift

end General

section Uniform

variable {k : ℕ} {A M : Type*} [Semiring A] [AddCommMonoid M] [UniformSpace M] [ContinuousAdd M]
  [Module A M] [ContinuousConstSMul A M]

/-- **Every restricted series is the sum of its monomial terms**: `f = ∑ₛ fₛ Tˢ` for the
topology of uniform convergence of coefficients. -/
theorem hasSum_restrictedMvPowerSeriesSubmoduleMonomial
    (f : restrictedMvPowerSeriesSubmodule k A M) :
    letI := restrictedMvPowerSeriesSubmoduleUniformSpace k A M;
    HasSum (fun s ↦ restrictedMvPowerSeriesSubmoduleMonomial s
      (((f : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) s)) f := by
  let := restrictedMvPowerSeriesSubmoduleUniformSpace k A M
  -- Keep the coefficient function at its function type, so that `Pi.single` sums simplify.
  set a : (Fin k →₀ ℕ) → M := ((f : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M)
  rw [HasSum, SummationFilter.unconditional_filter,
    isUniformInducing_restrictedMvPowerSeriesSubmodule_coefficients.isInducing.tendsto_nhds_iff]
  refine (UniformFun.hasBasis_nhds (Fin k →₀ ℕ) M (UniformFun.ofFun a)).tendsto_right_iff.mpr
    fun V hV ↦ ?_
  have hfin := eventually_cofinite.mp
    ((isRestricted_iff.mp (mem_restrictedMvPowerSeriesSubmodule.mp f.2)).eventually
      (mem_nhds_right 0 hV))
  filter_upwards [eventually_ge_atTop hfin.toFinset] with S hS t
  -- Reading off the coefficient at `t` is additive, so it commutes with the partial sum.
  let c : restrictedMvPowerSeriesSubmodule k A M →ₗ[A] M :=
    (LinearMap.proj t).comp (restrictedMvPowerSeriesSubmodule k A M).subtype
  have hc : (((∑ s ∈ S, restrictedMvPowerSeriesSubmoduleMonomial s (a s) :
      restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) t =
      ∑ s ∈ S, (Pi.single s (a s) : (Fin k →₀ ℕ) → M) t :=
    (map_sum c _ S).trans <| Finset.sum_congr rfl fun s _ ↦
      coeff_restrictedMvPowerSeriesSubmoduleMonomial s (a s) t
  -- The partial sum over `S` agrees with `f` on `S` and vanishes off `S`.
  -- Expose the coefficient function inside `UniformFun.toFun`; simplification cannot cross
  -- the semireducible `MvPowerSeries` wrapper at module coefficients to apply `hc`.
  change (a t, (((∑ s ∈ S, restrictedMvPowerSeriesSubmoduleMonomial s (a s) :
      restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) t) ∈ V
  rw [hc, Finset.sum_pi_single]
  by_cases ht : t ∈ S
  · simpa [ht] using refl_mem_uniformity hV
  · have : t ∉ hfin.toFinset := fun h ↦ ht (hS h)
    simpa [ht] using this

/-- **A continuous linear map out of `M⟨T₁, …, Tₖ⟩` is determined by its values on monomials**,
since every restricted series is the sum of its monomial terms. -/
theorem restrictedMvPowerSeriesSubmodule_linearMap_ext_of_continuous {N : Type*}
    [AddCommMonoid N] [TopologicalSpace N] [T2Space N] [Module A N] :
    letI := restrictedMvPowerSeriesSubmoduleUniformSpace k A M;
    ∀ {Ψ Ψ' : restrictedMvPowerSeriesSubmodule k A M →ₗ[A] N}, Continuous Ψ → Continuous Ψ' →
      (∀ s m, Ψ (restrictedMvPowerSeriesSubmoduleMonomial s m) =
        Ψ' (restrictedMvPowerSeriesSubmoduleMonomial s m)) → Ψ = Ψ' := by
  let := restrictedMvPowerSeriesSubmoduleUniformSpace k A M
  intro Ψ Ψ' hΨ hΨ' h
  ext f
  have hf := hasSum_restrictedMvPowerSeriesSubmoduleMonomial f
  exact (hf.map Ψ hΨ).unique (by simpa only [Function.comp_def, h] using hf.map Ψ' hΨ')

/-- **The converse of the universal property**: the values `Ψ(m Tˢ)` of a continuous linear map
`Ψ` out of `M⟨T₁, …, Tₖ⟩` form a family of linear maps `M → N` equicontinuous at `0`. -/
theorem equicontinuousAt_comp_restrictedMvPowerSeriesSubmoduleMonomial {N : Type*}
    [AddCommMonoid N] [UniformSpace N] [Module A N] :
    letI := restrictedMvPowerSeriesSubmoduleUniformSpace k A M;
    ∀ {Ψ : restrictedMvPowerSeriesSubmodule k A M →ₗ[A] N}, Continuous Ψ →
      EquicontinuousAt (fun s ↦ ⇑(Ψ ∘ₗ restrictedMvPowerSeriesSubmoduleMonomial s)) 0 := by
  let := restrictedMvPowerSeriesSubmoduleUniformSpace k A M
  intro Ψ hΨ U hU
  have hΨW : Ψ ⁻¹' {y | (0, y) ∈ U} ∈ 𝓝 0 :=
    hΨ.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact mem_nhds_left 0 hU)
  obtain ⟨V, hV, hVW⟩ := hasBasis_nhds_zero_restrictedMvPowerSeriesSubmodule.mem_iff.mp hΨW
  filter_upwards [hV] with m hm s
  -- The monomial `m Tˢ` has every coefficient in `V`: `m` at `s` and `0` elsewhere.
  have hmono : ∀ t, (((restrictedMvPowerSeriesSubmoduleMonomial (A := A) s m :
      restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M) :
        (Fin k →₀ ℕ) → M) t ∈ V := fun t ↦ by
    by_cases ht : t = s
    · simpa [ht] using hm
    · simpa [ht] using mem_of_mem_nhds hV
  simpa using hVW hmono

end Uniform

variable {k : ℕ} {A M : Type*} [Ring A] [AddCommGroup M] [UniformSpace M]
  [IsUniformAddGroup M] [Module A M] [ContinuousConstSMul A M]

section Lift

variable {N : Type*} [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [Module A N]
  [ContinuousConstSMul A N] [T2Space N] [CompleteSpace N] [NonarchimedeanAddGroup N]

/-- The lift of `(φₛ)ₛ` is continuous for the topology of uniform convergence of coefficients. -/
theorem continuous_restrictedMvPowerSeriesSubmoduleLift {φ : (Fin k →₀ ℕ) → M →ₗ[A] N}
    (hφ : EquicontinuousAt (fun s ↦ ⇑(φ s)) 0) :
    letI := restrictedMvPowerSeriesSubmoduleUniformSpace k A M;
    Continuous (restrictedMvPowerSeriesSubmoduleLift φ hφ) := by
  let := restrictedMvPowerSeriesSubmoduleUniformSpace k A M
  have := isUniformAddGroup_restrictedMvPowerSeriesSubmodule (k := k) (A := A) (M := M)
  refine continuous_of_continuousAt_zero (restrictedMvPowerSeriesSubmoduleLift φ hφ) ?_
  rw [ContinuousAt, map_zero]
  intro U hU
  -- Shrink `U` to an open subgroup `W`; a sum of terms in `W` stays in the closed set `W`.
  obtain ⟨W, hWU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V, hV, hVW⟩ := eventually_iff_exists_mem.mp
    (equicontinuousAt_eventually_forall_apply_mem hφ (W.isOpen.mem_nhds W.zero_mem))
  refine mem_map.mpr <| mem_of_superset
    (hasBasis_nhds_zero_restrictedMvPowerSeriesSubmodule.mem_of_mem hV) fun f hf ↦ hWU ?_
  exact tsum_mem W.isClosed fun s ↦ hVW _ (hf s) s

/-- **The universal property of `M⟨T₁, …, Tₖ⟩`.** A family of `A`-linear maps `φₛ : M → N`, one
for each monomial and equicontinuous at `0`, into a complete Hausdorff nonarchimedean module
extends uniquely to a continuous `A`-linear map `M⟨T₁, …, Tₖ⟩ → N` sending `m Tˢ` to `φₛ(m)`. -/
theorem existsUnique_continuous_linearMap_restrictedMvPowerSeriesSubmodule
    (φ : (Fin k →₀ ℕ) → M →ₗ[A] N) (hφ : EquicontinuousAt (fun s ↦ ⇑(φ s)) 0) :
    letI := restrictedMvPowerSeriesSubmoduleUniformSpace k A M;
    ∃! Ψ : restrictedMvPowerSeriesSubmodule k A M →ₗ[A] N,
      Continuous Ψ ∧ ∀ s m, Ψ (restrictedMvPowerSeriesSubmoduleMonomial s m) = φ s m := by
  let := restrictedMvPowerSeriesSubmoduleUniformSpace k A M
  refine ⟨restrictedMvPowerSeriesSubmoduleLift φ hφ,
    ⟨continuous_restrictedMvPowerSeriesSubmoduleLift hφ,
      restrictedMvPowerSeriesSubmoduleLift_monomial hφ⟩, fun Ψ ⟨hΨ, h⟩ ↦ ?_⟩
  exact restrictedMvPowerSeriesSubmodule_linearMap_ext_of_continuous hΨ
    (continuous_restrictedMvPowerSeriesSubmoduleLift hφ) fun s m ↦ by simp [h]

end Lift

end TauCeti.Huber
