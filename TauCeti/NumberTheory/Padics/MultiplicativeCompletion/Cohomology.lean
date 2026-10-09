/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Reciprocity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso
import TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.Strict
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Sylow

/-!
# The low-degree cohomology of `A(L)`

Let `L/K` be a finite Galois extension of `p`-adic fields with group `G = Gal(L/K)`, and let
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` be the `p`-adic completion of `Lˣ`, a `ℤ_p`-representation of `G`.
Through local reciprocity (`TauCeti.padicCompletionUnitsEquivAbelianizationProP`), `A(L)` is the
class module `V^ab(p)` of `G_K ⧸ V ≃ G`, where `V = G_L`, equivariantly
(`TauCeti.padicCompletionUnitsEquivAbelianizationProP_smul`). As `scd_p G_K = 2` (NSW (7.2.5)),
NSW (3.6.4) computes the low-degree cohomology of the class module, and this file reads it on
`A(L)`:

* for every subgroup `S` of `G`, `H¹(S, A(L)) = 0` and `H²(S, A(L))` is cyclic of order the
  `p`-part of `#S`; in particular `H²(S, A(L))` has order `#S` when `S` is a `p`-group;
* `H²(G, A(L))` is cyclic of order the `p`-part of `#G`.

These are the inputs of Tate's theorem for `A(L)` on the `p`-subgroups of `G`.

## Main statements

* `TauCeti.isZero_groupCohomology_one_res_padicCompletionUnits`: `H¹(S, A(L)) = 0`.
* `TauCeti.exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits`: `H²(S, A(L))`
  is cyclic of order `p ^ v_p(#S)`.
* `TauCeti.natCard_groupCohomology_two_res_padicCompletionUnits`: `#H²(S, A(L)) = #S` for a
  `p`-subgroup `S`.
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

omit [IsGalois K L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L] in
/-- `classModuleAddEquiv` is the inverse of local reciprocity, read additively. -/
private theorem classModuleAddEquiv_apply (ι : L →ₐ[K] SeparableClosure K)
    (m : Additive (abelianizationProP p (AbsoluteGaloisGroup K)
      (galoisSubgroup K L ι).toSubgroup)) :
    classModuleAddEquiv p K L ι m =
      Additive.ofMul ((padicCompletionUnitsEquivAbelianizationProP p K L ι).symm m.toMul) :=
  (rfl)

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
    rw [quotientGaloisSubgroupEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
      quotientFixingSubgroupFieldRangeEquiv_mk, classModuleAddEquiv_apply,
      classModuleAddEquiv_apply, Additive.toMul_smul, toMul_ofMul,
      ← padicCompletionUnitsEquivAbelianizationProP_smul]
    simp [e, padicCompletionUnitsRepresentation_apply, padicCompletionUnitsLinearMap_apply]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

omit [Algebra ℚ_[p] K] in
/-- The low-degree cohomology of a representation `B` of a group `H`, matched with `V^ab(p)` on
`W.map (mk' V) ≤ G_K ⧸ V` for an open `W ⊇ V` compatibly with the actions, read off from the class
module of `G_K` (NSW (3.6.4)): `H¹(H, B) = 0`, and `H²(H, B)` is cyclic of order the `p`-part of
`#H`. -/
private theorem groupCohomology_of_le {V W : Subgroup (AbsoluteGaloisGroup K)} [V.Normal]
    (hV : IsOpen (V : Set (AbsoluteGaloisGroup K))) (hVW : V ≤ W) {H : Type} [Group H]
    {B : Rep ℤ_[p] H} (φ : W.map (QuotientGroup.mk' V) ≃* H)
    (ψ : Additive (abelianizationProP p (AbsoluteGaloisGroup K) V) ≃+ B)
    (hψ : ∀ t m, ψ (t • m) = B.ρ (φ t) (ψ m)) :
    Subsingleton (groupCohomology B 1) ∧ ∃ u : groupCohomology B 2,
      AddSubgroup.zmultiples u = ⊤ ∧
        Nat.card (groupCohomology B 2) = p ^ padicValNat p (Nat.card H) := by
  have hp : p.Prime := Fact.out
  have hdim := (ClassFieldTheory.strictCohomologicalDimensionAt_galSeparableClosure_eq_two
    (K := K) p).le
  have : DiscreteTopology (AbsoluteGaloisGroup K ⧸ V) := QuotientGroup.discreteTopology hV
  have := subsingleton_h1_map_abelianizationProP hp hdim hV hVW
  obtain ⟨hgen, hcard⟩ := explicitRes2_abelianizationProPClass_generates hp hdim hV hVW
  let E := explicitH2AddEquivGroupCohomology φ ψ hψ
  let u := explicitRes2 _ _ (W.map (QuotientGroup.mk' V)) (abelianizationProPClass p _ V hV)
  refine ⟨(explicitH1AddEquivGroupCohomology φ ψ hψ).symm.injective.subsingleton, E u, ?_, ?_⟩
  · have := AddMonoidHom.map_zmultiples E.toAddMonoidHom u
    rw [hgen, AddSubgroup.map_top_of_surjective _ E.surjective] at this
    exact this.symm
  · rw [← Nat.card_congr E.toEquiv, hcard, Nat.card_congr φ.toEquiv]

/-- Both statements on a subgroup `S`, through the pair `V ◁ W` with `W` the preimage of `S` in
`G_K`. -/
private theorem groupCohomology_res_padicCompletionUnits (S : Subgroup (L ≃ₐ[K] L)) :
    Subsingleton (groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 1) ∧
      ∃ u : groupCohomology
          (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2,
        AddSubgroup.zmultiples u = ⊤ ∧
          Nat.card (groupCohomology
            (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) =
            p ^ padicValNat p (Nat.card S) := by
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let V := (galoisSubgroup K L ι).toSubgroup
  let e : AbsoluteGaloisGroup K ⧸ V ≃* (L ≃ₐ[K] L) := quotientGaloisSubgroupEquiv K L ι
  -- `S` is the image of `T ≤ G_K ⧸ V`, which is the image of its preimage `W ≤ G_K`.
  let T : Subgroup (AbsoluteGaloisGroup K ⧸ V) := S.comap e.toMonoidHom
  let W : Subgroup (AbsoluteGaloisGroup K) := T.comap (QuotientGroup.mk' V)
  have hmap : W.map (QuotientGroup.mk' V) = T :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) T
  have hTS : T.map e.toMonoidHom = S := Subgroup.map_comap_eq_self_of_surjective e.surjective S
  exact groupCohomology_of_le p K (galoisSubgroup K L ι).isOpen (QuotientGroup.le_comap_mk' V T)
    (B := Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K)))
    (((MulEquiv.subgroupCongr hmap).trans (e.subgroupMap T)).trans (MulEquiv.subgroupCongr hTS))
    (classModuleAddEquiv p K L ι) fun t m ↦ classModuleAddEquiv_smul p K L ι t m

/-- **`H¹` of `A(L)` vanishes on every subgroup** (NSW (3.6.4), read through local reciprocity):
`H¹(S, A(L)) = 0` for every subgroup `S` of `Gal(L/K)`. -/
theorem isZero_groupCohomology_one_res_padicCompletionUnits (S : Subgroup (L ≃ₐ[K] L)) :
    IsZero (groupCohomology
      (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 1) :=
  have := (groupCohomology_res_padicCompletionUnits p K L S).1
  ModuleCat.isZero_of_subsingleton _

/-- **`H²` of `A(L)` on a subgroup is cyclic of order the `p`-part of the subgroup** (NSW (3.6.4),
read through local reciprocity): for every subgroup `S` of `Gal(L/K)`, some class `u` generates
`H²(S, A(L))`, and this group has order `p ^ v_p(#S)`. -/
theorem exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits
    (S : Subgroup (L ≃ₐ[K] L)) :
    ∃ u : groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2,
      AddSubgroup.zmultiples u = ⊤ ∧
        Nat.card (groupCohomology
          (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) =
          p ^ padicValNat p (Nat.card S) :=
  (groupCohomology_res_padicCompletionUnits p K L S).2

/-- **`H²` of `A(L)` on a `p`-subgroup has the order of the subgroup** (NSW (3.6.4), read through
local reciprocity): `#H²(S, A(L)) = #S` for every `p`-subgroup `S` of `Gal(L/K)`. -/
theorem natCard_groupCohomology_two_res_padicCompletionUnits
    (S : Subgroup (L ≃ₐ[K] L)) (hS : IsPGroup p S) :
    Nat.card (groupCohomology
      (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) =
      Nat.card S := by
  obtain ⟨-, -, hcard⟩ := exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits
    p K L S
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
  rw [hcard, hn, padicValNat.prime_pow]

/-- **`H²(Gal(L/K), A(L))` is cyclic of order the `p`-part of `[L : K]`** (NSW (3.6.4), read
through local reciprocity): some class `u` generates `H²(Gal(L/K), A(L))`, and this group has
order `p ^ v_p(#Gal(L/K))`. The generator is the image of the class `u_{G_K/V}(p)` of the class
module. -/
theorem exists_zmultiples_eq_top_groupCohomology_two_padicCompletionUnits :
    ∃ u : groupCohomology (Rep.of (padicCompletionUnitsRepresentation p L K)) 2,
      AddSubgroup.zmultiples u = ⊤ ∧
        Nat.card (groupCohomology (Rep.of (padicCompletionUnitsRepresentation p L K)) 2) =
          p ^ padicValNat p (Nat.card (L ≃ₐ[K] L)) := by
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let V := (galoisSubgroup K L ι).toSubgroup
  have hmap : (⊤ : Subgroup (AbsoluteGaloisGroup K)).map (QuotientGroup.mk' V) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective V)
  exact (groupCohomology_of_le p K (galoisSubgroup K L ι).isOpen le_top
    (((MulEquiv.subgroupCongr hmap).trans Subgroup.topEquiv).trans
      (quotientGaloisSubgroupEquiv K L ι))
    (classModuleAddEquiv p K L ι) fun t m ↦ classModuleAddEquiv_smul p K L ι t m).2

end TauCeti
