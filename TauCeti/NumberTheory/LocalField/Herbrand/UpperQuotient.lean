/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.Herbrand.Jump
import TauCeti.NumberTheory.LocalField.Herbrand.Tower

/-!
# The upper numbering in a Galois tower

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

On the subgroup side, the upper filtration of `H = Gal(M/L)` is the trace of that of `G`, after
reindexing by `ψ_{L/K}`: `H ∩ G^v = H^{ψ_{L/K}(v)}`. The two compatibilities together describe the
upper breaks of `M/K` completely: they are the upper breaks of `L/K` together with the images under
`φ_{L/K}` of the upper breaks of `M/L`. Along a prime-degree tower of an abelian extension, this
reduces the integrality of the upper breaks to the integrality of `φ_{L/K}` at the single break of
each prime-degree step.

## Main definitions

* `Subgroup.upperRamificationGroupQuotient`: the upper ramification filtration of `G ⧸ H`.

## Main results

* `TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`:
  `G^v` restricts onto `Gal(L/K)^v`.
* `TauCeti.LocalFieldsRamification.UpperJump.of_tower`: an upper break of `L/K` is an upper
  break of `M/K`.
* `TauCeti.LocalFieldsRamification.comap_restrictScalarsHom_upperRamificationGroup`:
  `H ∩ G^v = H^{ψ_{L/K}(v)}`.
* `TauCeti.LocalFieldsRamification.upperJump_iff_upperJump_or_upperJump_inverseHerbrand`: `v` is an
  upper break of `M/K` exactly when it is one of `L/K` or `ψ_{L/K}(v)` is one of `M/L`.
* `Subgroup.upperRamificationGroup_fixedField`: the quotient filtration maps to `Gal(M^H/K)^v`
  under `G ⧸ H ≃* Gal(M^H/K)`.
* `Subgroup.upperRamificationGroup_quotient`: the defined quotient filtration equals `G^v H / H`.
* `Subgroup.upperRamificationGroupQuotient_antitone`: the quotient filtration is decreasing.

The quotient API takes the normal subgroup `H` as its first explicit argument, so it lives in
Mathlib's `Subgroup` namespace and is available as `H.upperRamificationGroupQuotient v`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Propositions 14 and 15, and
  Chapter V, §7.
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

/-- **The upper numbering of a normal subgroup.** For a tower `M/L/K` of Galois extensions, the
upper filtration of `H = Gal(M/L)` is the trace of that of `G = Gal(M/K)`, reindexed by the
inverse Herbrand function of `L/K`: `H ∩ G^v = H^{ψ_{L/K}(v)}`. -/
@[simp]
theorem comap_restrictScalarsHom_upperRamificationGroup (v : RamificationIndexDomain) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    (upperRamificationGroup K M v).comap (AlgEquiv.restrictScalarsHom (S := L) K) =
      upperRamificationGroup L M (inverseHerbrand K L v) := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  -- `H ∩ G_{ψ_{M/K}(v)} = H_{ψ_{M/K}(v)}`, and `ψ_{M/K}(v) = ψ_{M/L}(ψ_{L/K}(v))`.
  rw [upperRamificationGroup_def, comap_restrictScalarsHom_lowerRamificationGroupReal K M L,
    upperRamificationGroup_def, ← herbrandOrderIso_symm_apply K M, inverseHerbrand_tower K L M,
    OrderIso.trans_apply, herbrandOrderIso_symm_apply, herbrandOrderIso_symm_apply]

/-- The image of `Gal(M/L)^{ψ_{L/K}(v)}` in `Gal(M/K)` is the trace `H ∩ G^v` of the upper
filtration of `M/K` on the image `H` of `Gal(M/L)`. -/
theorem map_restrictScalarsHom_upperRamificationGroup (v : RamificationIndexDomain) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    (upperRamificationGroup L M (inverseHerbrand K L v)).map
        (AlgEquiv.restrictScalarsHom (S := L) K) =
      (AlgEquiv.restrictScalarsHom (S := L) K).range ⊓ upperRamificationGroup K M v := by
  rw [← comap_restrictScalarsHom_upperRamificationGroup K L M, Subgroup.map_comap_eq]

/-- **Upper breaks in a tower.** For a tower `M/L/K` of Galois extensions, `v` is an upper break of
`M/K` exactly when it is an upper break of `L/K` or `ψ_{L/K}(v)` is an upper break of `M/L`. Thus
the upper breaks of `M/K` are those of `L/K` together with the images under `φ_{L/K}` of those of
`M/L`. -/
theorem upperJump_iff_upperJump_or_upperJump_inverseHerbrand (v : RamificationIndexDomain) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    UpperJump K M v ↔ UpperJump K L v ∨ UpperJump L M (inverseHerbrand K L v) := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  constructor
  · intro hv
    refine or_iff_not_imp_left.2 fun hL ↦ (upperJump_iff L M _).2 fun x hx ↦ ?_
    -- Since `v` is not an upper break of `L/K`, the filtration of `L/K` is constant on some
    -- `[v, w₀]` with `v < w₀`.
    obtain ⟨w₀, hvw₀, hw₀⟩ : ∃ w₀, v < w₀ ∧
        upperRamificationGroup K L w₀ = upperRamificationGroup K L v := by
      simp only [upperJump_iff, not_forall] at hL
      obtain ⟨w₀, hvw₀, hlt⟩ := hL
      exact ⟨w₀, hvw₀, (upperRamificationGroup_antitone K L hvw₀.le).eq_of_not_lt hlt⟩
    set w := min w₀ (herbrand K L x)
    have hvw : v < w := lt_min hvw₀ <| by
      simpa only [herbrand_inverseHerbrand] using herbrand_strictMono K L hx
    have hw : upperRamificationGroup K L w = upperRamificationGroup K L v :=
      le_antisymm (upperRamificationGroup_antitone K L hvw.le)
        (hw₀ ▸ upperRamificationGroup_antitone K L (min_le_left _ _))
    have hxw : inverseHerbrand K L w ≤ x := by
      simpa only [inverseHerbrand_herbrand] using
        (inverseHerbrand_strictMono K L).monotone (min_le_right w₀ (herbrand K L x))
    refine (upperRamificationGroup_antitone L M hxw).trans_lt ?_
    rw [← comap_restrictScalarsHom_upperRamificationGroup,
      ← comap_restrictScalarsHom_upperRamificationGroup]
    refine lt_of_le_of_ne (Subgroup.comap_mono (upperRamificationGroup_antitone K M hvw.le))
      fun heq ↦ ((upperJump_iff K M v).1 hv w hvw).not_ge fun σ hσ ↦ ?_
    -- `G^w` and `G^v` have the same image `(G/H)^w = (G/H)^v` and the same trace on `H`, so the
    -- smaller one contains the larger: `σ = τ ρ` with `τ ∈ G^w` and `ρ ∈ H ∩ G^v = H ∩ G^w`.
    obtain ⟨τ, hτ, hτσ⟩ : AlgEquiv.restrictNormalHom L σ ∈
        (upperRamificationGroup K M w).map (AlgEquiv.restrictNormalHom L) := by
      rw [map_restrictNormalHom_upperRamificationGroup, hw,
        ← map_restrictNormalHom_upperRamificationGroup K L M]
      exact Subgroup.mem_map_of_mem _ hσ
    obtain ⟨ρ, hρ⟩ : τ⁻¹ * σ ∈ (AlgEquiv.restrictScalarsHom (S := L) K).range := by
      rw [AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M, MonoidHom.mem_ker,
        map_mul, map_inv, hτσ, inv_mul_cancel]
    have hρw : ρ ∈ (upperRamificationGroup K M w).comap
        (AlgEquiv.restrictScalarsHom (S := L) K) := by
      rw [heq, Subgroup.mem_comap, hρ]
      exact mul_mem (inv_mem (upperRamificationGroup_antitone K M hvw.le hτ)) hσ
    rw [Subgroup.mem_comap, hρ] at hρw
    simpa only [mul_inv_cancel_left] using mul_mem hτ hρw
  · rintro (hL | hM)
    · exact hL.of_tower
    -- A strict drop `H ∩ G^w < H ∩ G^v` of the traces forces a strict drop `G^w < G^v`.
    refine (upperJump_iff K M v).2 fun w hvw ↦
      lt_of_le_of_ne (upperRamificationGroup_antitone K M hvw.le) fun heq ↦ ?_
    have hlt := (upperJump_iff L M _).1 hM _ (inverseHerbrand_strictMono K L hvw)
    rw [← comap_restrictScalarsHom_upperRamificationGroup,
      ← comap_restrictScalarsHom_upperRamificationGroup, heq] at hlt
    exact hlt.ne rfl

end Tower

end TauCeti.LocalFieldsRamification

namespace Subgroup

open TauCeti.LocalFieldsRamification

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
    (σ : (M ≃ₐ[K] M) ⧸ H) ∈ upperRamificationGroupQuotient H v ↔
      σ ∈ upperRamificationGroup K M v ⊔ H := by
  rw [← QuotientGroup.mk'_apply H σ]
  rw [← mem_comap, upperRamificationGroupQuotient, QuotientGroup.comap_map_mk', sup_comm]

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
  have : ValuativeExtension (fixedField H) M :=
    _root_.IntermediateField.valuativeExtension_of_isNonarchimedeanLocalField (fixedField H)
  -- Under `G ⧸ H ≃* Gal(M^H/K)`, the class of `σ` is the restriction of `σ` to `M^H`.
  have hcomp : (IsGalois.normalAutEquivQuotient H : _ →* _).comp (QuotientGroup.mk' H) =
      AlgEquiv.restrictNormalHom (fixedField H) :=
    MonoidHom.ext (IsGalois.normalAutEquivQuotient_apply H)
  rw [upperRamificationGroupQuotient, Subgroup.map_map, hcomp,
    map_restrictNormalHom_upperRamificationGroup K (fixedField H) M]

end Quotient

end Subgroup
