/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Reciprocity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso
import TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.Strict
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.ChangeOfGroup
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Sylow
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ContinuousMulEquiv

/-!
# The low-degree cohomology of `A(L)`

Let `L/K` be a finite Galois extension of `p`-adic fields with group `G = Gal(L/K)`, and let
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` be the `p`-adic completion of `Lˣ`, a `ℤ_p`-representation of `G`.
Through local reciprocity (`TauCeti.padicCompletionUnitsEquivAbelianizationProP`), `A(L)` is the
class module `V^ab(p)` of `G_K ⧸ V ≃ G`, where `V = G_L`, equivariantly
(`TauCeti.padicCompletionUnitsEquivAbelianizationProP_smul`). As `scd_p G_K = 2` (NSW (7.2.5)),
NSW (3.6.4) computes the low-degree cohomology of the class module, and this file reads it on
`A(L)`:

* for every `p`-subgroup `S` of `G`, `H¹(S, A(L)) = 0` and `H²(S, A(L))` has order `#S`;
* `H²(G, A(L))` is cyclic of order the `p`-part of `#G`.

These are the inputs of Tate's theorem for `A(L)` on the `p`-subgroups of `G`.

## Main statements

* `TauCeti.isZero_groupCohomology_one_res_padicCompletionUnits`: `H¹(S, A(L)) = 0`.
* `TauCeti.natCard_groupCohomology_two_res_padicCompletionUnits`: `#H²(S, A(L)) = #S`.
* `TauCeti.exists_zmultiples_eq_top_groupCohomology_two_padicCompletionUnits`: `H²(G, A(L))` is
  cyclic of order `p ^ v_p(#G)`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.6.4) and
  (7.2.5).
-/

public section

namespace TauCeti

open CategoryTheory Limits ContCohomology

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L]

/-- Local reciprocity for `A(L)`, as an additive isomorphism from the class module `V^ab(p)`. -/
private noncomputable def classModuleAddEquiv (ι : L →ₐ[K] SeparableClosure K) :
    Additive (abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L ι).toSubgroup) ≃+
      Rep.of (padicCompletionUnitsRepresentation p L K) :=
  (padicCompletionUnitsEquivAbelianizationProP p K L ι).symm.toMulEquiv.toAdditive

/-- `G_K ⧸ V ≃ Gal(L/K)`, for `V` the subgroup of `G_K` fixing `ι(L)`. -/
private noncomputable def quotientGaloisSubgroupEquiv (ι : L →ₐ[K] SeparableClosure K) :
    AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L ι).toSubgroup ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (galoisSubgroup_toSubgroup K L ι)).trans
    (quotientFixingSubgroupFieldRangeEquiv K L ι)

/-- `classModuleAddEquiv` intertwines the action of `G_K ⧸ V` on `V^ab(p)` with the action of
`Gal(L/K)` on `A(L)`, along `G_K ⧸ V ≃ Gal(L/K)`. -/
private theorem classModuleAddEquiv_smul (ι : L →ₐ[K] SeparableClosure K)
    (q : AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L ι).toSubgroup)
    (m : Additive (abelianizationProP p (AbsoluteGaloisGroup K)
      (galoisSubgroup K L ι).toSubgroup)) :
    classModuleAddEquiv p K L ι (q • m) =
      (Rep.of (padicCompletionUnitsRepresentation p L K)).ρ
        (quotientGaloisSubgroupEquiv K L ι q) (classModuleAddEquiv p K L ι m) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    set e := padicCompletionUnitsEquivAbelianizationProP p K L ι
    obtain ⟨z, rfl⟩ : ∃ z, Additive.ofMul (e z) = m := ⟨e.symm m.toMul, by simp⟩
    have h := padicCompletionUnitsEquivAbelianizationProP_smul p K L ι g z
    rw [quotientGaloisSubgroupEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
      quotientFixingSubgroupFieldRangeEquiv_mk]
    -- The action on `Additive V^ab(p)` is the conjugation action on `V^ab(p)`, and
    -- `classModuleAddEquiv` is `e⁻¹` read additively.
    change Additive.ofMul (e.symm
      ((QuotientGroup.mk g : AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L ι).toSubgroup) • e z)) = _
    rw [← h, ContinuousMulEquiv.symm_apply_apply]
    have hz : classModuleAddEquiv p K L ι (Additive.ofMul (e z)) = Additive.ofMul z :=
      congrArg Additive.ofMul (e.symm_apply_apply z)
    rw [hz, Rep.of_ρ, padicCompletionUnitsRepresentation_apply,
      padicCompletionUnitsLinearMap_apply]
    rfl

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

omit [Algebra ℚ_[p] K] in
/-- `scd_p G_K ≤ 2` (NSW (7.2.5)), read on `G_K = Gal(Kˢ/K)` through the restriction isomorphism
from Mathlib's `Field.absoluteGaloisGroup K`. -/
private theorem strictCohomologicalDimensionAt_absoluteGaloisGroup_le_two :
    strictCohomologicalDimensionAt.{0} p (AbsoluteGaloisGroup K) ≤ 2 := by
  rw [← strictCohomologicalDimensionAt_congr (absoluteGaloisGroupRestrictEquiv K),
    ClassFieldTheory.strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two]

/-- Both statements on a `p`-subgroup `S`, read off from the pair `V ◁ W` with `W` the preimage of
`S` in `G_K`, through the change of group and local reciprocity. -/
private theorem groupCohomology_res_padicCompletionUnits
    (S : Subgroup (L ≃ₐ[K] L)) (hS : IsPGroup p S) :
    Subsingleton (groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 1) ∧
      Nat.card (groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) =
        Nat.card S := by
  have hp : p.Prime := Fact.out
  have hdim := strictCohomologicalDimensionAt_absoluteGaloisGroup_le_two p K
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let V := (galoisSubgroup K L ι).toSubgroup
  have hV : IsOpen (V : Set (AbsoluteGaloisGroup K)) := (galoisSubgroup K L ι).isOpen
  have : DiscreteTopology (AbsoluteGaloisGroup K ⧸ V) := QuotientGroup.discreteTopology hV
  let e : AbsoluteGaloisGroup K ⧸ V ≃* (L ≃ₐ[K] L) := quotientGaloisSubgroupEquiv K L ι
  -- `S` is the image of `T ≤ G_K ⧸ V`, which is the image of its preimage `W ≤ G_K`.
  let T : Subgroup (AbsoluteGaloisGroup K ⧸ V) := S.comap e.toMonoidHom
  let W : Subgroup (AbsoluteGaloisGroup K) := T.comap (QuotientGroup.mk' V)
  have hVW : V ≤ W := QuotientGroup.le_comap_mk' V T
  have hmap : W.map (QuotientGroup.mk' V) = T :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) T
  have hTS : T.map e.toMonoidHom = S := Subgroup.map_comap_eq_self_of_surjective e.surjective S
  let φ : W.map (QuotientGroup.mk' V) ≃* S :=
    ((MulEquiv.subgroupCongr hmap).trans (e.subgroupMap T)).trans (MulEquiv.subgroupCongr hTS)
  let B := Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))
  have hψ (t : W.map (QuotientGroup.mk' V))
      (m : Additive (abelianizationProP p (AbsoluteGaloisGroup K) V)) :
      classModuleAddEquiv p K L ι (t • m) = B.ρ (φ t) (classModuleAddEquiv p K L ι m) :=
    classModuleAddEquiv_smul p K L ι (t : AbsoluteGaloisGroup K ⧸ V) m
  -- The pair `V.subgroupOf W ◁ W`: `W` is open, so `scd_p W ≤ 2`, and `W ⧸ V` is a `p`-group.
  have hWopen : IsOpen (W : Set (AbsoluteGaloisGroup K)) := Subgroup.isOpen_mono hVW hV
  have : CompactSpace W := isCompact_iff_compactSpace.mp (W.isClosed_of_isOpen hWopen).isCompact
  have hdimW : strictCohomologicalDimensionAt.{0} p W ≤ 2 :=
    (strictCohomologicalDimensionAt_le_of_isClosed (W.isClosed_of_isOpen hWopen)).trans hdim
  let eWV := quotientSubgroupOfEquivMap V W hV
  have : Finite (L ≃ₐ[K] L) := inferInstance
  have : Finite (W ⧸ V.subgroupOf W) := .of_equiv _ (eWV.toMulEquiv.trans φ).symm.toEquiv
  have hpWV : IsPGroup p (W ⧸ V.subgroupOf W) :=
    hS.of_equiv (eWV.toMulEquiv.trans φ).symm
  have h1 := subsingleton_h1_abelianizationProP_of_isPGroup hp hdimW
    (W.subgroupOf_isOpen V hV) hpWV
  have h2 := (abelianizationProPClass_generates_of_isPGroup hp hdimW
    (W.subgroupOf_isOpen V hV) hpWV).2
  let E₁ := (abelianizationProPSubgroupOfH1Equiv p hVW hV).trans
    (explicitH1AddEquivGroupCohomology (B := B) φ (classModuleAddEquiv p K L ι) hψ)
  let E₂ := (abelianizationProPSubgroupOfH2Equiv p hVW hV).trans
    (explicitH2AddEquivGroupCohomology (B := B) φ (classModuleAddEquiv p K L ι) hψ)
  exact ⟨E₁.symm.injective.subsingleton, by
    rw [← Nat.card_congr E₂.toEquiv, h2, Nat.card_congr (eWV.toMulEquiv.trans φ).toEquiv]⟩

/-- **`H¹` of `A(L)` vanishes on `p`-subgroups** (NSW (3.6.4), read through local reciprocity):
`H¹(S, A(L)) = 0` for every `p`-subgroup `S` of `Gal(L/K)`. -/
theorem isZero_groupCohomology_one_res_padicCompletionUnits
    (S : Subgroup (L ≃ₐ[K] L)) (hS : IsPGroup p S) :
    IsZero (groupCohomology
      (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 1) :=
  have := (groupCohomology_res_padicCompletionUnits p K L S hS).1
  ModuleCat.isZero_of_subsingleton _

/-- **`H²` of `A(L)` on a `p`-subgroup has the order of the subgroup** (NSW (3.6.4), read through
local reciprocity): `#H²(S, A(L)) = #S` for every `p`-subgroup `S` of `Gal(L/K)`. -/
theorem natCard_groupCohomology_two_res_padicCompletionUnits
    (S : Subgroup (L ≃ₐ[K] L)) (hS : IsPGroup p S) :
    Nat.card (groupCohomology
      (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) =
      Nat.card S :=
  (groupCohomology_res_padicCompletionUnits p K L S hS).2

/-- **`H²(Gal(L/K), A(L))` is cyclic of order the `p`-part of `[L : K]`** (NSW (3.6.4), read
through local reciprocity): some class `u` generates `H²(Gal(L/K), A(L))`, and this group has
order `p ^ v_p(#Gal(L/K))`. The generator is the image of the class `u_{G_K/V}(p)` of the class
module. -/
theorem exists_zmultiples_eq_top_groupCohomology_two_padicCompletionUnits :
    ∃ u : groupCohomology (Rep.of (padicCompletionUnitsRepresentation p L K)) 2,
      AddSubgroup.zmultiples u = ⊤ ∧
        Nat.card (groupCohomology (Rep.of (padicCompletionUnitsRepresentation p L K)) 2) =
          p ^ padicValNat p (Nat.card (L ≃ₐ[K] L)) := by
  have hdim := strictCohomologicalDimensionAt_absoluteGaloisGroup_le_two p K
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let V := (galoisSubgroup K L ι).toSubgroup
  have hV : IsOpen (V : Set (AbsoluteGaloisGroup K)) := (galoisSubgroup K L ι).isOpen
  have : DiscreteTopology (AbsoluteGaloisGroup K ⧸ V) := QuotientGroup.discreteTopology hV
  let e : AbsoluteGaloisGroup K ⧸ V ≃* (L ≃ₐ[K] L) := quotientGaloisSubgroupEquiv K L ι
  let E := explicitH2AddEquivGroupCohomology e (classModuleAddEquiv p K L ι)
    (classModuleAddEquiv_smul p K L ι)
  obtain ⟨hgen, hcard⟩ := abelianizationProPClass_generates (Fact.out : p.Prime) hdim hV
  refine ⟨E (abelianizationProPClass p _ V hV), ?_, ?_⟩
  · have := AddMonoidHom.map_zmultiples E.toAddMonoidHom (abelianizationProPClass p _ V hV)
    rw [hgen, AddSubgroup.map_top_of_surjective _ E.surjective] at this
    exact this.symm
  · rw [← Nat.card_congr E.toEquiv, hcard, Nat.card_congr e.toEquiv]

end TauCeti
