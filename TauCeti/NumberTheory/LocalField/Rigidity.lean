/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.RingTheory.Valuation.Discrete.Henselian

import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Valuation and topological rigidity of nonarchimedean local fields

The integer ring `𝒪[K]` of a nonarchimedean local field `K` (of mixed or equal characteristic) is a
Henselian discrete valuation ring with finite residue field `𝓀[K]`. Specializing F. K. Schmidt's
discrete-valuation rigidity (`ValuativeExtension.of_henselianLocalRing`) to `K` shows that the
valuation equivalence class, the topology, the integer ring, the residue field, the normalized
valuation, and the normalized absolute value of `K` are all intrinsic to its bare field structure,
and that algebraic extensions into rank-one discrete valued fields are automatically compatible and
topological embeddings:

* Every algebraic extension `L / K` carrying a nontrivial rank-one discrete `ValuativeRel` (in
  particular, every algebraic extension of nonarchimedean local fields) is automatically a
  `ValuativeExtension K L`, with no topological compatibility assumption on `algebraMap K L`.
* When `L` also carries its valuative topology, `algebraMap K L` is automatically continuous, a
  topological embedding, and (because `K` is complete) a closed embedding.
* Every abstract ring isomorphism `e : K ≃+* L` from a nonarchimedean local field `K` onto a
  nontrivial rank-one discrete valued field `L` automatically preserves and reflects the valuative
  relation, restricts to `𝒪[K] ≃+* 𝒪[L]`, descends to `𝓀[K] ≃+* 𝓀[L]` (preserving `#𝓀`), and is a
  homeomorphism when `L` carries its valuative topology; when `L` is also a nonarchimedean local
  field, `e` preserves `normalizedValuationWithZero`, `normalizedValuation`, and
  `normalizedAbsoluteValue`.
* On a fixed bare field `K`, at most one pair `(ValuativeRel K, TopologicalSpace K)` makes `K` a
  nonarchimedean local field (`IsNonarchimedeanLocalField.valuativeRel_eq`,
  `IsNonarchimedeanLocalField.topologicalSpace_eq`).

`ValuativeExtension.of_isAlgebraic` is intentionally stated as a theorem rather than a global
instance because `TopologicalSpace K` does not appear in `ValuativeExtension K L`.

## Main definitions

* `RingEquiv.integerRingEquivOfIsNonarchimedeanLocalField`: restriction of an abstract ring
  isomorphism `e : K ≃+* L` to `𝒪[K] ≃+* 𝒪[L]`.
* `RingEquiv.residueFieldEquivOfIsNonarchimedeanLocalField`: the induced residue-field isomorphism
  `𝓀[K] ≃+* 𝓀[L]`.

## Main results

* `ValuativeExtension.of_isAlgebraic`: an algebraic extension `L / K` from a nonarchimedean local
  field `K` into a nontrivial rank-one discrete valued field `L` is automatically a
  `ValuativeExtension K L`.
* `TauCeti.continuous_algebraMap_of_isAlgebraic`,
  `TauCeti.isEmbedding_algebraMap_of_isAlgebraic`, and
  `TauCeti.isClosedEmbedding_algebraMap_of_isAlgebraic`: automatic continuity, topological
  embedding, and closed embedding of `algebraMap K L` for the valuative topologies.
* `RingHom.map_vle_map_iff_of_isIntegral`, `RingHom.continuous_of_isIntegral`,
  `RingHom.isEmbedding_of_isIntegral`, and `RingHom.isClosedEmbedding_of_isIntegral`: the
  homomorphism forms for an integral ring homomorphism `f : K →+* L`.
* `RingEquiv.map_vle_map_iff_of_isNonarchimedeanLocalField`,
  `RingEquiv.mem_integer_iff_of_isNonarchimedeanLocalField`,
  `RingEquiv.continuous_of_isNonarchimedeanLocalField`, and
  `RingEquiv.isHomeomorph_of_isNonarchimedeanLocalField`: automatic valuation preservation,
  integer-ring preservation, continuity, and homeomorphism property of `e : K ≃+* L`.
* `RingEquiv.natCard_residueField_eq`, `RingEquiv.normalizedValuationWithZero_apply`,
  `RingEquiv.normalizedValuation_unitsMap`, and `RingEquiv.normalizedAbsoluteValue_apply`:
  invariance of `#𝓀`, the normalized valuation, and the normalized absolute value under any
  abstract ring isomorphism between nonarchimedean local fields.
* `IsNonarchimedeanLocalField.valuativeRel_eq` and
  `IsNonarchimedeanLocalField.topologicalSpace_eq`: uniqueness of the `ValuativeRel` and
  `TopologicalSpace` making a field a nonarchimedean local field.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. **108** (1933), 1–25.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section
noncomputable section

open scoped WithZero
open IsLocalRing Topology ValuativeRel

/-- **Every algebraic extension of a nonarchimedean local field into a nontrivial rank-one discrete
valued field is automatically a `ValuativeExtension`.** In particular, any algebraic algebra between
nonarchimedean local fields is compatible with their valuations without assuming continuity of
`algebraMap K L`. -/
theorem ValuativeExtension.of_isAlgebraic (K L : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    [Algebra K L] [Algebra.IsAlgebraic K L] :
    ValuativeExtension K L :=
  .of_henselianLocalRing K L

namespace TauCeti

section Algebra

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsValuativeTopology L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
  [Algebra K L] [Algebra.IsAlgebraic K L]

/-- **Automatic continuity of algebraic algebra maps from a nonarchimedean local field.** If `K` is
a nonarchimedean local field and `L / K` is an algebraic extension carrying a nontrivial rank-one
discrete valuative topology, then `algebraMap K L` is continuous with no compatibility hypothesis.
-/
theorem continuous_algebraMap_of_isAlgebraic : Continuous (algebraMap K L) := by
  have : ValuativeExtension K L := .of_isAlgebraic K L
  exact continuous_algebraMap_of_valuativeExtension K L

/-- **Algebraic algebra maps from a nonarchimedean local field are topological embeddings.** -/
theorem isEmbedding_algebraMap_of_isAlgebraic : IsEmbedding (algebraMap K L) := by
  have : ValuativeExtension K L := .of_isAlgebraic K L
  exact isEmbedding_algebraMap_of_valuativeExtension K L

/-- **Algebraic algebra maps from a nonarchimedean local field are closed embeddings.** Completeness
of `K` upgrades the topological embedding to a closed embedding without requiring `L` to be
complete. -/
theorem isClosedEmbedding_algebraMap_of_isAlgebraic : IsClosedEmbedding (algebraMap K L) := by
  have : ValuativeExtension K L := .of_isAlgebraic K L
  let _ : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let _ : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  let _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup (G := L)
  exact isClosedEmbedding_algebraMap_of_valuativeExtension K L

end Algebra

end TauCeti

section RingHom

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Any integral ring homomorphism `f : K →+* L` (equivalently, one over which `L` is algebraic)
from a nonarchimedean local field `K` into a nontrivial rank-one discrete valued field `L`
preserves and reflects the valuative relation. -/
theorem RingHom.map_vle_map_iff_of_isIntegral [Field L] [ValuativeRel L] [IsDiscrete L]
    [IsRankLeOne L] [IsNontrivial L] (f : K →+* L) (hf : f.IsIntegral) (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y :=
  f.map_vle_map_iff_of_henselianLocalRing hf x y

/-- Any integral ring homomorphism from a nonarchimedean local field into a nontrivial rank-one
discrete valued field with its valuative topology is automatically continuous. -/
theorem RingHom.continuous_of_isIntegral [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsValuativeTopology L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    (f : K →+* L) (hf : f.IsIntegral) : Continuous f := by
  let _ : Algebra K L := f.toAlgebra
  have : Algebra.IsIntegral K L := ⟨hf⟩
  exact TauCeti.continuous_algebraMap_of_isAlgebraic K L

/-- Any integral ring homomorphism from a nonarchimedean local field into a nontrivial rank-one
discrete valued field with its valuative topology is a topological embedding. -/
theorem RingHom.isEmbedding_of_isIntegral [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsValuativeTopology L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    (f : K →+* L) (hf : f.IsIntegral) : IsEmbedding f := by
  let _ : Algebra K L := f.toAlgebra
  have : Algebra.IsIntegral K L := ⟨hf⟩
  exact TauCeti.isEmbedding_algebraMap_of_isAlgebraic K L

/-- Any integral ring homomorphism from a nonarchimedean local field into a nontrivial rank-one
discrete valued field with its valuative topology is a closed embedding. -/
theorem RingHom.isClosedEmbedding_of_isIntegral [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsValuativeTopology L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    (f : K →+* L) (hf : f.IsIntegral) : IsClosedEmbedding f := by
  let _ : Algebra K L := f.toAlgebra
  have : Algebra.IsIntegral K L := ⟨hf⟩
  exact TauCeti.isClosedEmbedding_algebraMap_of_isAlgebraic K L

end RingHom

namespace RingEquiv

section DiscreteTarget

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
  [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]

/-- **Every abstract ring isomorphism from a nonarchimedean local field onto a nontrivial rank-one
discrete valued field preserves and reflects the valuative relation.** -/
theorem map_vle_map_iff_of_isNonarchimedeanLocalField (e : K ≃+* L) (x y : K) :
    e x ≤ᵥ e y ↔ x ≤ᵥ y :=
  e.map_vle_map_iff_of_henselianLocalRing x y

/-- An abstract ring isomorphism from a nonarchimedean local field onto a nontrivial rank-one
discrete valued field preserves and reflects membership in the ring of integers. -/
@[simp]
theorem mem_integer_iff_of_isNonarchimedeanLocalField (e : K ≃+* L) (x : K) :
    e x ∈ 𝒪[L] ↔ x ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← (valuation L).map_one,
    ← (valuation K).map_one, ← (valuation L).vle_iff_le, ← (valuation K).vle_iff_le,
    ← map_one e, e.map_vle_map_iff_of_isNonarchimedeanLocalField]

/-- Restriction of an abstract ring isomorphism `e : K ≃+* L` (from a nonarchimedean local field
`K` onto a nontrivial rank-one discrete valued field `L`) to the rings of integers `𝒪[K] ≃+* 𝒪[L]`.
-/
def integerRingEquivOfIsNonarchimedeanLocalField (e : K ≃+* L) : 𝒪[K] ≃+* 𝒪[L] :=
  e.restrict 𝒪[K] 𝒪[L] fun x ↦ (e.mem_integer_iff_of_isNonarchimedeanLocalField x).symm

/-- Coercing `e.integerRingEquivOfIsNonarchimedeanLocalField x` to `L` evaluates `e` on `x`. -/
@[simp]
theorem coe_integerRingEquivOfIsNonarchimedeanLocalField_apply (e : K ≃+* L) (x : 𝒪[K]) :
    (e.integerRingEquivOfIsNonarchimedeanLocalField x : L) = e x :=
  (rfl)

/-- The residue-field isomorphism `𝓀[K] ≃+* 𝓀[L]` induced by an abstract ring isomorphism
`e : K ≃+* L`. -/
def residueFieldEquivOfIsNonarchimedeanLocalField (e : K ≃+* L) : 𝓀[K] ≃+* 𝓀[L] :=
  ResidueField.mapEquiv e.integerRingEquivOfIsNonarchimedeanLocalField

/-- The induced residue-field isomorphism intertwines the residue maps of `𝒪[K]` and `𝒪[L]`. -/
@[simp]
theorem residueFieldEquivOfIsNonarchimedeanLocalField_residue (e : K ≃+* L) (x : 𝒪[K]) :
    e.residueFieldEquivOfIsNonarchimedeanLocalField (residue 𝒪[K] x) =
      residue 𝒪[L] (e.integerRingEquivOfIsNonarchimedeanLocalField x) :=
  ResidueField.map_residue (e.integerRingEquivOfIsNonarchimedeanLocalField : 𝒪[K] →+* 𝒪[L]) x

/-- Isomorphic nonarchimedean local fields (or a nonarchimedean local field and an abstractly
isomorphic nontrivial rank-one discrete valued field) have residue fields of the same cardinality.
-/
theorem natCard_residueField_eq (e : K ≃+* L) : Nat.card 𝓀[K] = Nat.card 𝓀[L] :=
  Nat.card_congr e.residueFieldEquivOfIsNonarchimedeanLocalField.toEquiv

/-- **Every abstract ring isomorphism from a nonarchimedean local field onto a nontrivial rank-one
discrete valued field with its valuative topology is automatically continuous.** -/
theorem continuous_of_isNonarchimedeanLocalField [TopologicalSpace L] [IsValuativeTopology L]
    (e : K ≃+* L) : Continuous e :=
  e.toRingHom.continuous_of_isIntegral (RingHom.isIntegral_of_surjective _ e.surjective)

/-- **Every abstract ring isomorphism between nonarchimedean local fields (or onto any nontrivial
rank-one discrete valued field with its valuative topology) is automatically a homeomorphism.** -/
theorem isHomeomorph_of_isNonarchimedeanLocalField [TopologicalSpace L] [IsValuativeTopology L]
    (e : K ≃+* L) : IsHomeomorph e :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨e.toRingHom.isEmbedding_of_isIntegral (RingHom.isIntegral_of_surjective _ e.surjective),
      e.surjective⟩

end DiscreteTarget

section LocalFieldTarget

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- **Every abstract ring isomorphism between nonarchimedean local fields preserves the
zero-extended normalized valuation.** -/
@[simp]
theorem normalizedValuationWithZero_apply (e : K ≃+* L) (x : K) :
    TauCeti.normalizedValuationWithZero L (e x) = TauCeti.normalizedValuationWithZero K x := by
  let vL : Valuation L ℤᵐ⁰ :=
    (valuation L).map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L :
      ValueGroupWithZero L →*₀o ℤᵐ⁰)
  have hvL_surj : Function.Surjective vL := fun z ↦ by
    obtain ⟨y, hy⟩ := valuation_surjective
      ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).symm z)
    exact ⟨y, by simp [vL, hy]⟩
  have hvL_comp : vL.Compatible :=
    ⟨fun a b ↦ by
      rw [(valuation L).vle_iff_le]
      exact (OrderIsoClass.map_le_map_iff
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L)).symm⟩
  let vK : Valuation K ℤᵐ⁰ := vL.comap e.toRingHom
  have hvK_surj : Function.Surjective vK := hvL_surj.comp e.surjective
  have hvK_comp : vK.Compatible :=
    ⟨fun a b ↦ by
      rw [← e.map_vle_map_iff_of_isNonarchimedeanLocalField, hvL_comp.vle_iff_le]
      rfl⟩
  rw [vL.normalizedValuationWithZero_eq_inv_of_surjective hvL_surj (e x),
    vK.normalizedValuationWithZero_eq_inv_of_surjective hvK_surj x]
  rfl

/-- **Every abstract ring isomorphism between nonarchimedean local fields preserves the normalized
valuation on units.** -/
@[simp]
theorem normalizedValuation_unitsMap (e : K ≃+* L) (x : Kˣ) :
    TauCeti.normalizedValuation L (Units.map (e : K →+* L) x) =
      TauCeti.normalizedValuation K x := by
  apply WithZero.coe_inj.mp
  rw [← TauCeti.normalizedValuationWithZero_coe, ← TauCeti.normalizedValuationWithZero_coe]
  exact e.normalizedValuationWithZero_apply x

/-- **Every abstract ring isomorphism between nonarchimedean local fields preserves the normalized
absolute value.** -/
@[simp]
theorem normalizedAbsoluteValue_apply (e : K ≃+* L) (x : K) :
    TauCeti.normalizedAbsoluteValue L (e x) = TauCeti.normalizedAbsoluteValue K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hex : e x ≠ 0 := by simpa using hx
    have hu : Units.mk0 (e x) hex = Units.map (e : K →+* L) (Units.mk0 x hx) :=
      Units.ext rfl
    rw [TauCeti.normalizedAbsoluteValue_apply_ne_zero (e x) hex,
      TauCeti.normalizedAbsoluteValue_apply_ne_zero x hx, hu, e.normalizedValuation_unitsMap,
      e.natCard_residueField_eq]

end LocalFieldTarget

end RingEquiv

namespace IsNonarchimedeanLocalField

/-- **Uniqueness of the valuative relation of a nonarchimedean local field.** A bare field `K`
admits at most one `ValuativeRel` making it a nonarchimedean local field (and in fact at most one
nontrivial rank-one discrete `ValuativeRel` once some nonarchimedean local field structure exists
on `K`). -/
theorem valuativeRel_eq {K : Type*} [Field K]
    (r₁ r₂ : ValuativeRel K) (t₁ : TopologicalSpace K)
    [@IsNonarchimedeanLocalField K _ r₁ t₁]
    [@IsDiscrete K _ r₂] [@IsRankLeOne K _ r₂] [@IsNontrivial K _ r₂] :
    r₁ = r₂ := by
  let _ := r₁
  let _ := t₁
  have := TauCeti.henselianLocalRing_integer K
  exact ValuativeRel.eq_of_henselianLocalRing r₁ r₂

/-- **Uniqueness of the topology of a nonarchimedean local field.** Any two nonarchimedean local
field structures on the same bare field `K` induce identical topologies. -/
theorem topologicalSpace_eq {K : Type*} [Field K]
    (r₁ r₂ : ValuativeRel K) (t₁ t₂ : TopologicalSpace K)
    [h₁ : @IsNonarchimedeanLocalField K _ r₁ t₁]
    [h₂ : @IsNonarchimedeanLocalField K _ r₂ t₂] :
    t₁ = t₂ := by
  have hr : r₁ = r₂ := valuativeRel_eq r₁ r₂ t₁
  subst hr
  have ht₁ : t₁ = (@valuation K _ r₁).subgroups_basis.topology :=
    @Valuation.toTopologicalSpace_eq K _ r₁ _ _ t₁ h₁.toIsValuativeTopology (@valuation K _ r₁) _
  have ht₂ : t₂ = (@valuation K _ r₁).subgroups_basis.topology :=
    @Valuation.toTopologicalSpace_eq K _ r₁ _ _ t₂ h₂.toIsValuativeTopology (@valuation K _ r₁) _
  exact ht₁.trans ht₂.symm

end IsNonarchimedeanLocalField
