/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Normal.Closure

/-!
# A criterion for a group of automorphisms to be closed

A subgroup `U` of the automorphism group `M ≃ₐ[K] M` of a field extension is *closed* when it is
recovered from its fixed field, `(fixedField U).fixingSubgroup = U`: every automorphism fixing
`M ^ U` pointwise already lies in `U`. For a finite extension every subgroup is closed (Mathlib's
`IntermediateField.fixingSubgroup_fixedField`), and so is every finite subgroup of an arbitrary
extension (`IntermediateField.fixingSubgroup_fixedField_of_finite`). For a normal extension the
subgroups closed in the Krull topology are closed (`TauCeti.fixingSubgroup_fixedField`), but
`ℂ / ℚ` is not normal, and in general not every subgroup of finite index in `ℂ ≃ₐ[ℚ] ℂ` is closed.

This file proves that `U` is closed as soon as it contains the fixing subgroup of some field `E`
that is a *finite* extension of `M ^ U`. For `M = ℂ`, a subgroup of `Aut(ℂ)` containing
`Aut(ℂ / E)` for a finite extension `E` of `ℂ ^ U` is `Aut(ℂ / ℂ ^ U)`. In particular a subgroup
containing the automorphisms that fix a number field pointwise is closed. Closedness is what lets
statements about the degree `[M ^ V : M ^ U]` for subgroups `V ≤ U` be read off from the index
`[U : V]`, as in the descent arguments for fields of moduli.

The proof passes to the normal closure `N` of `E / M ^ U` inside `M`. It is finite over `M ^ U`
and stable under every automorphism of `M` over `M ^ U` (`AlgHom.map_normalClosure_le`), so
restriction to `N` sends `U` to a subgroup of `N ≃ₐ[M ^ U] N` with fixed field `M ^ U`. By
Artin's theorem that subgroup is the whole group, so every `σ` fixing `M ^ U` agrees on `N` with
some `u ∈ U`. Then `u⁻¹ * σ` fixes `E`, so it lies in `U`, and so does `σ`. No normality,
separability or algebraic closedness is needed.

## Main results

* `IntermediateField.fixingSubgroup_fixedField_of_fixingSubgroup_le`: if the fixing subgroup of an
  extension `E` of finite degree over `M ^ U` lies in `U`, then `U` is closed.
* `IntermediateField.fixingSubgroup_fixedField_of_fixingSubgroup_le_of_finiteDimensional`: the
  same conclusion for an intermediate field `E` of finite degree over the base field `K`.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (1.5), where the statement is made for subgroups of `Aut(ℂ)`.
-/

public section

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M] {U : Subgroup (M ≃ₐ[K] M)}

/-- **A subgroup containing the automorphisms over a finite extension of its fixed field is
closed.** If `E` is an extension of finite degree of the fixed field `M ^ U` inside `M` and every
automorphism fixing `E` pointwise lies in `U`, then `U` is the whole fixing subgroup of `M ^ U`.

No hypothesis on `M / K` is needed; in particular `M` need not be algebraic over `M ^ U`. -/
theorem fixingSubgroup_fixedField_of_fixingSubgroup_le (E : IntermediateField (fixedField U) M)
    [FiniteDimensional (fixedField U) E] (hE : (E.restrictScalars K).fixingSubgroup ≤ U) :
    (fixedField U).fixingSubgroup = U := by
  have hUL : U ≤ (fixedField U).fixingSubgroup :=
    (le_fixedField_iff_le_fixingSubgroup _ _).mp le_rfl
  refine le_antisymm (fun σ hσ ↦ ?_) hUL
  -- The normal closure `N` of `E / M ^ U` in `M` is finite over `M ^ U`, and every automorphism
  -- of `M` over `M ^ U` maps it into itself, so restriction to `N` is a homomorphism `ρ`.
  let N := normalClosure (fixedField U) E M
  have : FiniteDimensional (fixedField U) N := normalClosure.is_finiteDimensional _ E M
  have hN (τ : M ≃ₐ[fixedField U] M) (x : N) : τ x ∈ N :=
    (τ : M →ₐ[fixedField U] M).map_normalClosure_le ⟨x, x.2, rfl⟩
  let ρ : (M ≃ₐ[fixedField U] M) →* (N ≃ₐ[fixedField U] N) :=
    { toFun τ := AlgEquiv.ofBijective
        (((τ : M →ₐ[fixedField U] M).comp N.val).codRestrict N.toSubalgebra (hN τ))
        (Algebra.IsAlgebraic.algHom_bijective _)
      map_one' := by ext; rfl
      map_mul' _ _ := by ext; rfl }
  have hρ (τ : M ≃ₐ[fixedField U] M) (x : N) : (ρ τ x : M) = τ x := rfl
  -- The restrictions of the elements of `U` form a subgroup `H` of `Gal(N / M ^ U)` whose fixed
  -- field is `M ^ U`.
  let H : Subgroup (N ≃ₐ[fixedField U] N) :=
    ((U.subgroupOf (fixedField U).fixingSubgroup).map
      (fixedField U).fixingSubgroupEquiv.toMonoidHom).map ρ
  have hH : fixedField H = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    have hxU : (x : M) ∈ fixedField U := by
      refine (mem_fixedField_iff U (x : M)).mpr fun u hu ↦ ?_
      have h := (mem_fixedField_iff H x).mp hx
        (ρ ((fixedField U).fixingSubgroupEquiv ⟨u, hUL hu⟩)) ⟨_, ⟨⟨u, hUL hu⟩, hu, rfl⟩, rfl⟩
      simpa [hρ] using congrArg Subtype.val h
    exact mem_bot.mpr ⟨⟨x, hxU⟩, rfl⟩
  -- By Artin's theorem `H` is all of `Gal(N / M ^ U)`, so `σ` agrees on `N` with some `u ∈ U`.
  have hσH : ρ ((fixedField U).fixingSubgroupEquiv ⟨σ, hσ⟩) ∈ H := by
    rw [← fixingSubgroup_fixedField H, hH, fixingSubgroup_bot]
    exact Subgroup.mem_top _
  obtain ⟨_, ⟨u, hu, rfl⟩, huσ⟩ := hσH
  replace hu : (u : M ≃ₐ[K] M) ∈ U := Subgroup.mem_subgroupOf.mp hu
  -- Then `u⁻¹ * σ` fixes `E ≤ N` pointwise, so it lies in `U`.
  have hfix : (u : M ≃ₐ[K] M)⁻¹ * σ ∈ U := hE <| (mem_fixingSubgroup_iff _ _).mpr fun x hx ↦ by
    have hxN : x ∈ N := le_normalClosure E ((mem_restrictScalars K).mp hx)
    have h := congrArg Subtype.val (AlgEquiv.ext_iff.mp huσ ⟨x, hxN⟩)
    simp only [hρ, MulEquiv.coe_toMonoidHom, coe_fixingSubgroupEquiv_apply] at h
    rw [AlgEquiv.mul_apply, ← h]
    exact (u : M ≃ₐ[K] M).symm_apply_apply x
  simpa using U.mul_mem hu hfix

/-- **A subgroup containing the automorphisms over a field of finite degree is closed.** If `E`
is an intermediate field of finite degree over `K` and every automorphism fixing `E` pointwise
lies in `U`, then `U` is the whole fixing subgroup of its fixed field. For example, a subgroup of
`ℂ ≃ₐ[ℚ] ℂ` containing all automorphisms that fix a number field pointwise is closed. -/
theorem fixingSubgroup_fixedField_of_fixingSubgroup_le_of_finiteDimensional
    (E : IntermediateField K M) [FiniteDimensional K E] (hE : E.fixingSubgroup ≤ U) :
    (fixedField U).fixingSubgroup = U := by
  -- The field generated by `E` over `M ^ U` is finite over `M ^ U` and contains `E`.
  have : FiniteDimensional (fixedField U) (adjoin (fixedField U) (E : Set M)) :=
    Module.rank_lt_aleph0_iff.mp <|
      (adjoin_rank_le_of_isAlgebraic_right (fixedField U) E).trans_lt (Module.rank_lt_aleph0 K E)
  refine fixingSubgroup_fixedField_of_fixingSubgroup_le (adjoin (fixedField U) (E : Set M))
    (le_trans ?_ hE)
  exact fixingSubgroup_le fun x hx ↦ subset_adjoin (fixedField U) (E : Set M) hx

end IntermediateField
