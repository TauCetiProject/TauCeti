/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.Herbrand.Jump
public import TauCeti.NumberTheory.LocalField.Herbrand.Tower

/-!
# The upper numbering passes to quotients

Let `M/K` be a finite Galois extension of nonarchimedean local fields with group `G`, and let
`H ≤ G` be a normal subgroup, with fixed field `L = M^H`, so that restriction identifies `G / H`
with `Gal(L/K)`. The lower numbering is not compatible with this quotient, but the upper
numbering is:

`(G/H)^v = G^v H / H`  for every `v ≥ -1`.

This is Herbrand's theorem `(G/H)_{φ_{M/L}(u)} = G_u H / H` read through the transitivity
`ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}` of the inverse Herbrand functions: both give
`φ_{M/L}(ψ_{M/K}(v)) = ψ_{L/K}(v)`. It is the reason upper numbering is the one that is
functorial in quotients, and hence the one that defines a filtration of an infinite Galois
group; and it transports the upper breaks along the prime-order quotient series in the proof of
the Hasse–Arf theorem.

The statement is given in three forms.

* For a tower `M/L/K` with `L/K` Galois, the image of `G^v` under restriction to `L` is the
  upper ramification group of `L/K` at `v`.
* For a normal subgroup `H`, define the quotient filtration `upperRamificationGroupQuotient H`
  of `G ⧸ H` as the image of `G^v` and express it as `G^v H / H`.
* For every compatible local-field structure on `M^H`, the restriction equivalence
  `IsGalois.normalAutEquivQuotient` carries this quotient filtration to the upper filtration of
  `M^H/K`.

As a consequence, every upper break of `L/K` is an upper break of `M/K`.

## Main definitions

* `TauCeti.LocalFieldsRamification.upperRamificationGroupQuotient`: the upper ramification
  filtration of `G ⧸ H`.

## Main results

* `TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`:
  `G^v` restricts onto `Gal(L/K)^v`.
* `TauCeti.LocalFieldsRamification.UpperJump.of_tower`: an upper break of `L/K` is an upper
  break of `M/K`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_fixedField`: the quotient filtration
  maps to `Gal(M^H/K)^v` under `G ⧸ H ≃* Gal(M^H/K)`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_quotient`: the defined quotient
  filtration equals `G^v H / H`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroupQuotient_antitone`: the quotient
  filtration is decreasing.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Proposition 14.
-/

public section
noncomputable section

open IntermediateField

namespace TauCeti.LocalFieldsRamification

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [Algebra K M] [ValuativeExtension K M]
  [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]

/-- **Herbrand's theorem in the upper numbering.** For a tower `M/L/K` of Galois extensions, the
image of the upper ramification group `G^v` of `M/K` under restriction to `L` is the upper
ramification group of `L/K` at the same index: `(G/H)^v = G^v H / H` for `H = Gal(M/L)`. -/
@[simp]
theorem map_restrictNormalHom_upperRamificationGroup (v : RamificationIndexDomain) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    (upperRamificationGroup K M v).map (AlgEquiv.restrictNormalHom L) =
      upperRamificationGroup K L v := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  -- `G^v = G_{ψ_{M/K}(v)}` restricts onto `(G/H)_{φ_{M/L}(ψ_{M/K}(v))}`, and
  -- `φ_{M/L}(ψ_{M/K}(v)) = φ_{M/L}(ψ_{M/L}(ψ_{L/K}(v))) = ψ_{L/K}(v)`.
  rw [upperRamificationGroup_def, map_restrictNormalHom_lowerRamificationGroupReal,
    upperRamificationGroup_def, ← herbrandOrderIso_symm_apply K M, inverseHerbrand_tower K L M,
    OrderIso.trans_apply, herbrandOrderIso_symm_apply, herbrandOrderIso_symm_apply,
    herbrand_inverseHerbrand]

variable {K L M} in
/-- In a tower `M/L/K` of Galois extensions, every upper break of `L/K` is an upper break of
`M/K`. -/
theorem UpperJump.of_tower {v : RamificationIndexDomain} (h : UpperJump K L v) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    UpperJump K M v := by
  have : Module.Finite K M := Module.Finite.trans L M
  refine (upperJump_iff K M v).2 fun w hvw ↦ ?_
  -- If `G^w = G^v`, then their images `(G/H)^w` and `(G/H)^v` would agree.
  refine lt_of_le_of_ne (upperRamificationGroup_antitone K M hvw.le) fun heq ↦
    ((upperJump_iff K L v).1 h w hvw).ne ?_
  rw [← map_restrictNormalHom_upperRamificationGroup K L M, heq,
    map_restrictNormalHom_upperRamificationGroup]

end Tower

section Quotient

variable {K M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsGalois K M] (H : Subgroup (M ≃ₐ[K] M)) [H.Normal]

/-- The **upper ramification filtration of the quotient** `G ⧸ H`, for a normal subgroup `H` of
`G = Gal(M/K)`: the image of `G^v` under the quotient map `G → G ⧸ H`. -/
def upperRamificationGroupQuotient (v : RamificationIndexDomain) :
    Subgroup ((M ≃ₐ[K] M) ⧸ H) :=
  (upperRamificationGroup K M v).map (QuotientGroup.mk' H)

/-- For a normal subgroup `H` of `G = Gal(M/K)`, the defined quotient filtration is
`G^v H / H`. -/
theorem upperRamificationGroup_quotient (v : RamificationIndexDomain) :
    upperRamificationGroupQuotient H v =
      (upperRamificationGroup K M v ⊔ H).map (QuotientGroup.mk' H) := by
  simp [upperRamificationGroupQuotient, Subgroup.map_sup]

/-- A representative belongs to the quotient upper ramification group exactly when it belongs
to `G^v H`. -/
@[simp]
theorem mem_upperRamificationGroupQuotient_mk_iff (v : RamificationIndexDomain)
    (σ : M ≃ₐ[K] M) :
    QuotientGroup.mk' H σ ∈ upperRamificationGroupQuotient H v ↔
      σ ∈ upperRamificationGroup K M v ⊔ H := by
  rw [← Subgroup.mem_comap, upperRamificationGroupQuotient,
    QuotientGroup.comap_map_mk', sup_comm]

/-- The upper ramification filtration on a quotient is decreasing. -/
theorem upperRamificationGroupQuotient_antitone :
    Antitone (upperRamificationGroupQuotient H) :=
  fun _ _ hvw ↦ Subgroup.map_mono (upperRamificationGroup_antitone K M hvw)

/-- Each upper ramification group in the quotient is normal. -/
instance instNormalUpperRamificationGroupQuotient (v : RamificationIndexDomain) :
    (upperRamificationGroupQuotient H v).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)

/-- **The upper numbering of a quotient, field-theoretically.** For a normal subgroup `H` of
`G = Gal(M/K)` and any local-field structure on the fixed field `M^H` compatible with `K`, the
restriction isomorphism `G ⧸ H ≃* Gal(M^H/K)` maps the quotient upper ramification group at `v`
onto the upper ramification group of `M^H/K`. -/
@[simp]
theorem upperRamificationGroup_fixedField [ValuativeRel (fixedField H)]
    [TopologicalSpace (fixedField H)] [IsNonarchimedeanLocalField (fixedField H)]
    [ValuativeExtension K (fixedField H)] (v : RamificationIndexDomain) :
    (upperRamificationGroupQuotient H v).map
        (IsGalois.normalAutEquivQuotient H) =
      upperRamificationGroup K (fixedField H) v := by
  -- Under `G ⧸ H ≃* Gal(M^H/K)`, the class of `σ` is the restriction of `σ` to `M^H`.
  have hcomp : (IsGalois.normalAutEquivQuotient H : _ →* _).comp (QuotientGroup.mk' H) =
      AlgEquiv.restrictNormalHom (fixedField H) :=
    MonoidHom.ext (IsGalois.normalAutEquivQuotient_apply H)
  rw [upperRamificationGroupQuotient, Subgroup.map_map, hcomp,
    map_restrictNormalHom_upperRamificationGroup K (fixedField H) M]

end Quotient

end TauCeti.LocalFieldsRamification
