/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.LocalRing
public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.RingTheory.Unramified.LocalRing

/-!
# Unramified extensions of local fields

Let `L/K` be an extension of nonarchimedean local fields whose valuations are compatible, in the
sense of `ValuativeExtension K L`. This file defines the predicate

`TauCeti.IsUnramified K L`

by the two conditions that the value group of `K` is carried onto that of `L`, in the form
`ramificationIndex K L = 1`, and that the residue extension `𝓀[L] / 𝓀[K]` is separable. The
second condition is automatic here, because the residue field of a nonarchimedean local field is
finite and hence perfect, but it is the condition that makes the predicate the arithmetic notion
of unramifiedness for a general valued field, and it is what the comparison with the étale
notions rests on.

The file proves the equivalent forms of the predicate that later work uses: the value-group form,
the valuation form `v_L ∘ algebraMap = v_K`, the ideal form `𝓂[K] 𝒪[L] = 𝓂[L]`, the degree form
`f(L/K) = [L : K]`, and the comparison with `Algebra.FormallyUnramified 𝒪[K] 𝒪[L]` and
`Algebra.IsUnramifiedAt 𝒪[K] 𝓂[L]`, which makes Mathlib's unramifiedness theory available for
extensions of local fields. Unramifiedness is also shown to be stable in a tower in both
directions.

## Main definitions

* `TauCeti.IsUnramified`: an extension of nonarchimedean local fields is unramified when its
  ramification index is `1` and its residue extension is separable.

## Main results

* `TauCeti.isUnramified_iff_ramificationIndex_eq_one`: the separability condition is automatic,
  so the predicate is `e(L/K) = 1`.
* `TauCeti.isUnramified_iff_surjective_normalizedValuation`: `L/K` is unramified exactly when the
  normalized value group of `K` is carried onto that of `L`.
* `TauCeti.isUnramified_iff_normalizedValuation_algebraMap`: `L/K` is unramified exactly when the
  normalized valuation of `L` restricts to that of `K`.
* `TauCeti.isUnramified_iff_map_maximalIdeal_eq`: `L/K` is unramified exactly when `𝓂[K]`
  generates `𝓂[L]`.
* `TauCeti.IsUnramified.irreducible_algebraMap`: in an unramified extension a uniformizer of `K`
  stays a uniformizer of `L`.
* `TauCeti.isUnramified_iff_inertiaDegree_eq_finrank`: `L/K` is unramified exactly when
  `f(L/K) = [L : K]`.
* `TauCeti.isUnramified_tower_iff`, `TauCeti.IsUnramified.trans`,
  `TauCeti.IsUnramified.tower_bot` and `TauCeti.IsUnramified.tower_top`: `M/K` is unramified
  exactly when both steps of a tower `M/L/K` are.
* `TauCeti.isUnramified_iff_formallyUnramified` and `TauCeti.isUnramified_iff_isUnramifiedAt`:
  the comparison with Mathlib's `Algebra.FormallyUnramified` and `Algebra.IsUnramifiedAt` for
  `𝒪[L]` over `𝒪[K]`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4 and Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

variable (K L) in
/-- An extension `L/K` of nonarchimedean local fields with compatible valuations is
**unramified** when the normalized value group of `K` is carried onto that of `L`, that is
`e(L/K) = 1`, and the residue extension `𝓀[L] / 𝓀[K]` is separable.

The separability condition is automatic for nonarchimedean local fields, whose residue fields
are finite and hence perfect; it is carried in the definition because it is what the notion means
for a general valued field, and it is one of the two halves of Mathlib's criterion
`Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`. -/
class IsUnramified : Prop where
  /-- The ramification index of an unramified extension is `1`. -/
  ramificationIndex_eq_one : ramificationIndex K L = 1
  /-- The residue extension of an unramified extension is separable. -/
  isSeparable_residueField : Algebra.IsSeparable 𝓀[K] 𝓀[L]

attribute [simp] IsUnramified.ramificationIndex_eq_one

variable (K L) in
/-- **An extension of nonarchimedean local fields is unramified exactly when `e(L/K) = 1`.** The
residue extension of such an extension is automatically separable, its residue fields being
finite. -/
theorem isUnramified_iff_ramificationIndex_eq_one :
    IsUnramified K L ↔ ramificationIndex K L = 1 :=
  ⟨fun _ ↦ IsUnramified.ramificationIndex_eq_one, fun h ↦ ⟨h, inferInstance⟩⟩

variable (K L) in
/-- **An extension of nonarchimedean local fields is unramified exactly when the normalized value
group of `K` is carried onto the normalized value group of `L`.** This is the form the definition
takes for a general valued field: the map of value groups is injective in any case, so
unramifiedness is exactly its surjectivity. -/
theorem isUnramified_iff_surjective_normalizedValuation :
    IsUnramified K L ↔ Function.Surjective
      ((normalizedValuation L).comp (Units.map (algebraMap K L : K →* L))) := by
  rw [isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_def, Subgroup.index_eq_one,
    MonoidHom.range_eq_top]

variable (K L) in
/-- **An extension of nonarchimedean local fields is unramified exactly when the normalized
valuation of `L` restricts along the algebra map to the normalized valuation of `K`.** -/
theorem isUnramified_iff_normalizedValuation_algebraMap :
    IsUnramified K L ↔ ∀ x : Kˣ,
      normalizedValuation L (Units.map (algebraMap K L : K →* L) x) = normalizedValuation K x := by
  rw [isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_eq_iff]
  simp only [pow_one]

/-- In an unramified extension the normalized valuation of `L` extends that of `K`. -/
theorem IsUnramified.normalizedValuation_algebraMap [IsUnramified K L] (x : Kˣ) :
    normalizedValuation L (Units.map (algebraMap K L : K →* L) x) = normalizedValuation K x :=
  (isUnramified_iff_normalizedValuation_algebraMap K L).1 ‹_› x

variable (K L) in
/-- **An extension of nonarchimedean local fields is unramified exactly when the maximal ideal of
`𝒪[K]` generates the maximal ideal of `𝒪[L]`.** -/
theorem isUnramified_iff_map_maximalIdeal_eq :
    IsUnramified K L ↔ 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) = 𝓂[L] := by
  rw [isUnramified_iff_ramificationIndex_eq_one, map_maximalIdeal_eq_maximalIdeal_pow]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  refine ⟨fun h ↦ by rw [h, pow_one], fun h ↦ ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton] at h
  have hdvd : ϖ ^ ramificationIndex K L ∣ ϖ ^ 1 := by simpa using h.dvd
  have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hdvd
  have := ramificationIndex_pos (K := K) (L := L)
  omega

/-- In an unramified extension the maximal ideal of `𝒪[K]` generates the maximal ideal of
`𝒪[L]`. -/
theorem IsUnramified.map_maximalIdeal [IsUnramified K L] :
    𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) = 𝓂[L] :=
  (isUnramified_iff_map_maximalIdeal_eq K L).1 ‹_›

/-- **In an unramified extension a uniformizer of `K` stays a uniformizer of `L`.** -/
theorem IsUnramified.irreducible_algebraMap [IsUnramified K L] {π : 𝒪[K]} (hπ : Irreducible π) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← IsUnramified.map_maximalIdeal (K := K),
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.map_span,
    Set.image_singleton]

variable (K L) in
/-- **An extension of nonarchimedean local fields is unramified exactly when its residue degree
is its degree**, that is `f(L/K) = [L : K]`. -/
theorem isUnramified_iff_inertiaDegree_eq_finrank :
    IsUnramified K L ↔ inertiaDegree K L = Module.finrank K L := by
  rw [isUnramified_iff_ramificationIndex_eq_one, ← ramificationIndex_mul_inertiaDegree]
  refine ⟨fun h ↦ by rw [h, one_mul], fun h ↦ ?_⟩
  exact Nat.eq_of_mul_eq_mul_right inertiaDegree_pos (by rw [← h, one_mul])

/-- In an unramified extension the residue degree is the degree of the extension. -/
theorem IsUnramified.inertiaDegree_eq_finrank [IsUnramified K L] :
    inertiaDegree K L = Module.finrank K L :=
  (isUnramified_iff_inertiaDegree_eq_finrank K L).1 ‹_›

section Tower

variable (K L) (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M] [ValuativeExtension K M]

/-- **Unramifiedness in a tower** `M/L/K`: the extension `M/K` is unramified exactly when both
`L/K` and `M/L` are. -/
theorem isUnramified_tower_iff :
    IsUnramified K M ↔ IsUnramified K L ∧ IsUnramified L M := by
  simp only [isUnramified_iff_ramificationIndex_eq_one,
    ramificationIndex_tower (K := K) (L := L) M, mul_eq_one]

/-- Unramifiedness is transitive in a tower `M/L/K`. -/
theorem IsUnramified.trans [IsUnramified K L] [IsUnramified L M] : IsUnramified K M :=
  (isUnramified_tower_iff K L M).2 ⟨‹_›, ‹_›⟩

/-- The bottom step of an unramified tower is unramified. -/
theorem IsUnramified.tower_bot [IsUnramified K M] : IsUnramified K L :=
  ((isUnramified_tower_iff K L M).1 ‹_›).1

/-- The top step of an unramified tower is unramified. -/
theorem IsUnramified.tower_top [IsUnramified K M] : IsUnramified L M :=
  ((isUnramified_tower_iff K L M).1 ‹_›).2

end Tower

variable (K L) in
/-- **An extension of nonarchimedean local fields is unramified exactly when `𝒪[L]` is formally
unramified over `𝒪[K]`.** -/
theorem isUnramified_iff_formallyUnramified :
    IsUnramified K L ↔ Algebra.FormallyUnramified 𝒪[K] 𝒪[L] := by
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, isUnramified_iff_map_maximalIdeal_eq]
  exact ⟨fun h ↦ ⟨inferInstance, h⟩, fun h ↦ h.2⟩

variable (K L) in
/-- **An extension of nonarchimedean local fields is unramified exactly when `𝒪[L]` is unramified
over `𝒪[K]` at `𝓂[L]`**, in Mathlib's sense. -/
theorem isUnramified_iff_isUnramifiedAt :
    IsUnramified K L ↔ Algebra.IsUnramifiedAt 𝒪[K] 𝓂[L] := by
  rw [isUnramifiedAt_maximalIdeal_iff, isUnramified_iff_formallyUnramified]

end TauCeti
