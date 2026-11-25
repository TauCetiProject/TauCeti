/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Basic
public import TauCeti.RingTheory.IntegralClosure.Action
public import TauCeti.RingTheory.IntegralClosure.Map
public import TauCeti.RingTheory.LocalRing.Herbrand.IntegralClosure

/-!
# Herbrand functions and upper numbering in Galois field towers of DVRs

For a finite Galois extension `L / K` whose integral closure of a local base ring `A` is a DVR
with separable residue extension, and a normal intermediate field `E / K`, we transport the
quotient Herbrand identities from `TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Basic` along
Galois fixed fields (`IsGalois.normalAutEquivQuotient`) and `K`-tower restriction
(`AlgEquiv.restrictNormalHom E`, `AlgEquiv.restrictScalarsHom K`), adapting
`NumberTheory/LocalField/Herbrand/{Tower,UpperQuotient}.lean`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Propositions 14–15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, pp. 127–128.
-/

public section
noncomputable section
open IsLocalRing
namespace TauCeti.IsLocalRing

open _root_.IntermediateField

section FixedField

variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
  [IsLocalRing A] [FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L)]
  [IsDiscreteValuationRing (integralClosure A L)]
  [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]

/-- **Herbrand's theorem for Galois fixed fields**: `IsGalois.normalAutEquivQuotient H` maps
`(Gal(L/K)^v).map (QuotientGroup.mk' H)` onto `Gal(fixedField H / K)^v`. -/
@[simp] theorem map_normalAutEquivQuotient_map_mk'_upperRamificationGroup_integralClosure
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (v : ℝ) :
    ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (QuotientGroup.mk' H)).map (IsGalois.normalAutEquivQuotient H : _ →* _) =
      upperRamificationGroup (fixedField H ≃ₐ[K] fixedField H)
        (integralClosure A (fixedField H)) v := by
  rw [← upperRamificationGroup_quotient_eq_map A (integralClosure A L) (L ≃ₐ[K] L) H v,
    upperRamificationGroup_fixedPoints_integralClosure_eq_comap A H v]
  exact Subgroup.map_comap_eq_self_of_surjective (IsGalois.normalAutEquivQuotient H).surjective _

end FixedField

section Helpers

variable (A E : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Field E]
  [Algebra A K] [Algebra K L] [Algebra A L] [Algebra K E] [Algebra E L] [Algebra A E]
  [IsScalarTower A K L] [IsScalarTower K E L]
  [IsDiscreteValuationRing (integralClosure A L)]

private theorem herbrandFun_embeddingSubgroup_integralClosure [IsScalarTower A E L] (u : ℝ) :
    herbrandFun (TauCeti.embeddingSubgroup K E L) (integralClosure A L) u =
      herbrandFun (L ≃ₐ[E] L) (integralClosure A L) u :=
  (herbrandFun_eq_of_smul_eq
    (φ := (TauCeti.algEquivEquivEmbeddingSubgroup K E L : (L ≃ₐ[E] L) →* _))
    (TauCeti.algEquivEquivEmbeddingSubgroup K E L).bijective
    (fun _ _ ↦ (TauCeti.algEquivEquivEmbeddingSubgroup_smul_integralClosure _ _).symm) u).symm

private theorem upperJump_embeddingSubgroup_integralClosure_iff [IsScalarTower A E L]
    (v : ℝ) :
    UpperJump (TauCeti.embeddingSubgroup K E L) (integralClosure A L) v ↔
      UpperJump (L ≃ₐ[E] L) (integralClosure A L) v :=
  (upperJump_iff_of_smul_eq (S := integralClosure A L)
    (φ := (TauCeti.algEquivEquivEmbeddingSubgroup K E L : (L ≃ₐ[E] L) →* _))
    (TauCeti.algEquivEquivEmbeddingSubgroup K E L).bijective
    (fun _ _ ↦ (TauCeti.algEquivEquivEmbeddingSubgroup_smul_integralClosure _ _).symm) v).symm

section QuotientHelpers

variable [FiniteDimensional K L] [IsGalois K L] [IsScalarTower A K E]
  [IsLocalRing (integralClosure A E)] [Normal K E]

private theorem herbrandFun_quotient_embeddingSubgroup_integralClosure (u : ℝ) :
    herbrandFun ((L ≃ₐ[K] L) ⧸ TauCeti.embeddingSubgroup K E L)
        (FixedPoints.subalgebra A (integralClosure A L) (TauCeti.embeddingSubgroup K E L)) u =
      herbrandFun (E ≃ₐ[K] E) (integralClosure A E) u := by
  have := IsGalois.tower_bot_of_normal K E L
  rw [herbrandFun_fixedPoints_integralClosure A (TauCeti.embeddingSubgroup K E L),
    (TauCeti.equivFixedFieldEmbeddingSubgroup K E L).herbrandFun_integralClosure_eq_of_algEquiv]

private theorem inverseHerbrandFun_quotient_embeddingSubgroup_integralClosure (v : ℝ) :
    inverseHerbrandFun ((L ≃ₐ[K] L) ⧸ TauCeti.embeddingSubgroup K E L)
        (FixedPoints.subalgebra A (integralClosure A L) (TauCeti.embeddingSubgroup K E L)) v =
      inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v := by
  have := IsGalois.tower_bot_of_normal K E L
  rw [inverseHerbrandFun_fixedPoints_integralClosure A (TauCeti.embeddingSubgroup K E L),
    (TauCeti.equivFixedFieldEmbeddingSubgroup K E
      L).inverseHerbrandFun_integralClosure_eq_of_algEquiv]

private theorem upperJump_quotient_embeddingSubgroup_integralClosure_iff (v : ℝ) :
    UpperJump ((L ≃ₐ[K] L) ⧸ TauCeti.embeddingSubgroup K E L)
        (FixedPoints.subalgebra A (integralClosure A L) (TauCeti.embeddingSubgroup K E L)) v ↔
      UpperJump (E ≃ₐ[K] E) (integralClosure A E) v := by
  have := IsGalois.tower_bot_of_normal K E L
  rw [upperJump_fixedPoints_integralClosure_iff A (TauCeti.embeddingSubgroup K E L),
    ← (TauCeti.equivFixedFieldEmbeddingSubgroup K E L).upperJump_integralClosure_iff_of_algEquiv]

end QuotientHelpers

end Helpers

section Tower

variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
  [IsLocalRing A] [FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L)]
  [IsDiscreteValuationRing (integralClosure A L)]
  [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
  (E : Type*) [Field E] [Algebra K E] [Algebra E L] [Algebra A E] [IsScalarTower A K E]
  [IsScalarTower K E L] [IsLocalRing (integralClosure A E)] [Normal K E]

/-- **Herbrand's theorem for normal subextensions** in a field tower `L / E / K` (`L / K` finite
Galois, `E / K` normal): `AlgEquiv.restrictNormalHom E` maps `Gal(L/K)^v` onto `Gal(E/K)^v`. -/
@[simp] theorem map_restrictNormalHom_upperRamificationGroup_integralClosure (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom E) =
      upperRamificationGroup (E ≃ₐ[K] E) (integralClosure A E) v := by
  have := IsGalois.tower_bot_of_normal K E L
  let eK := TauCeti.equivFixedFieldEmbeddingSubgroup K E L
  apply Subgroup.map_injective (f := MonoidHom.ofClass eK.autCongr)
    (by simpa using eK.autCongr.injective)
  rw [Subgroup.map_map,
    TauCeti.autCongr_equivFixedFieldEmbeddingSubgroup_comp_restrictNormalHom K E L,
    ← Subgroup.map_map,
    map_normalAutEquivQuotient_map_mk'_upperRamificationGroup_integralClosure A _ v,
    eK.upperRamificationGroup_integralClosure_eq_comap_autCongr v,
    Subgroup.map_comap_eq_self_of_surjective (by simpa using eK.autCongr.surjective)]

variable [IsScalarTower A E L]

/-- **Transitivity of `herbrandFun` in a field tower `L / E / K`** (`L / K` finite Galois, `E / K`
normal): `φ_{L/K}(u) = φ_{E/K}(φ_{L/E}(u))`. -/
theorem herbrandFun_integralClosure_tower (u : ℝ) :
    herbrandFun (L ≃ₐ[K] L) (integralClosure A L) u =
      herbrandFun (E ≃ₐ[K] E) (integralClosure A E)
        (herbrandFun (L ≃ₐ[E] L) (integralClosure A L) u) := by
  rw [herbrandFun_tower A (integralClosure A L) (L ≃ₐ[K] L) (TauCeti.embeddingSubgroup K E L) u,
    herbrandFun_embeddingSubgroup_integralClosure,
    herbrandFun_quotient_embeddingSubgroup_integralClosure]

section FiniteIntermediate

variable [FiniteDimensional K E] [FiniteDimensional E L]

/-- **Transitivity of `inverseHerbrandFun` in a field tower `L / E / K`** (`L / K` finite Galois,
`E / K` normal): `ψ_{L/K}(v) = ψ_{L/E}(ψ_{E/K}(v))`. -/
theorem inverseHerbrandFun_integralClosure_tower (v : ℝ) :
    inverseHerbrandFun (L ≃ₐ[K] L) (integralClosure A L) v =
      inverseHerbrandFun (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  rw [← herbrandFun_inj (L ≃ₐ[K] L) (integralClosure A L), herbrandFun_inverseHerbrandFun,
    herbrandFun_integralClosure_tower A E, herbrandFun_inverseHerbrandFun,
    herbrandFun_inverseHerbrandFun]

/-- **Upper filtration of `Gal(L/E)` in a field tower `L / E / K`**: pulling `Gal(L/K)^v` back along
`AlgEquiv.restrictScalarsHom K` gives `Gal(L/E)^{ψ_{E/K}(v)}`. -/
@[simp] theorem comap_restrictScalarsHom_upperRamificationGroup_integralClosure (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).comap
        (AlgEquiv.restrictScalarsHom (S := E) K) =
      upperRamificationGroup (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    inverseHerbrandFun_integralClosure_tower A E v, ramificationGroupReal_def,
    ramificationGroupReal_def]
  exact (ramificationGroup_eq_comap_of_smul_eq (e := AlgEquiv.restrictScalarsHom (S := E) K)
    (fun _ _ ↦ by simp) _).symm

/-- **Image of `Gal(L/E)^{ψ_{E/K}(v)}` in `Gal(L/K)`** in a field tower `L / E / K`. -/
theorem map_restrictScalarsHom_upperRamificationGroup_integralClosure (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v)).map
        (AlgEquiv.restrictScalarsHom (S := E) K) =
      (AlgEquiv.restrictScalarsHom (S := E) K).range ⊓
        upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v := by
  rw [← comap_restrictScalarsHom_upperRamificationGroup_integralClosure A E v,
    Subgroup.map_comap_eq]

end FiniteIntermediate

/-- **Upper breaks in a field tower `L / E / K`** (`L / K` finite Galois, `E / K` normal):
`v` is an upper break of `Gal(L/K)` iff it is one of `Gal(E/K)` or `ψ_{E/K}(v)` is one of
`Gal(L/E)`. -/
theorem upperJump_integralClosure_tower_iff (v : ℝ) :
    UpperJump (L ≃ₐ[K] L) (integralClosure A L) v ↔
      UpperJump (E ≃ₐ[K] E) (integralClosure A E) v ∨
        UpperJump (L ≃ₐ[E] L) (integralClosure A L)
          (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  rw [upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun A (integralClosure A L)
      (L ≃ₐ[K] L) (TauCeti.embeddingSubgroup K E L) v,
    upperJump_quotient_embeddingSubgroup_integralClosure_iff,
    upperJump_embeddingSubgroup_integralClosure_iff,
    inverseHerbrandFun_quotient_embeddingSubgroup_integralClosure]

end Tower

end TauCeti.IsLocalRing
