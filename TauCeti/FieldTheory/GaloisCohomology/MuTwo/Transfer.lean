/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Corestriction
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic

/-!
# Restriction and corestriction of mod-two Kummer classes

Let `L/K` be a finite extension of fields in which `2` is invertible, and `σ : L →ₐ[K] Kˢ` a
`K`-embedding into a separable closure. Restriction `TauCeti.galoisRes` and corestriction
`TauCeti.galoisCor` along `σ` act on `H¹(-, 𝔽₂)`, and the Kummer class `(a) ∈ H¹(G_K, 𝔽₂)` of a
unit is `TauCeti.kummerClass`. This file proves the two transfer laws of Kummer classes:

```text
res (a) = (a)     for a ∈ Kˣ, read in Lˣ,
cor (b) = (N b)   for b ∈ Lˣ, with N = N_{L/K}.
```

Both are the Kummer squares at `n = 2` of `TauCeti.Kummer`, read through the `μ₂` coefficient
dictionary `TauCeti.mu2EquivZMod2`; the one input specific to `μ₂` is that the dictionaries of `K`
and of `L` agree along the identification of separable closures
(`TauCeti.mu2EquivZMod2_kummerCoeffMap`), because that identification sends `-1` to `-1`.

Restriction is the restriction square `TauCeti.kummerRes_kummerCocycleClass` of the explicit Kummer
cocycle classes, and corestriction is the norm square `TauCeti.kummerCor_kummerMap` of the Kummer
isomorphism. Both are carried to `𝔽₂` coefficients by commuting squares of compatible pairs,
`TauCeti.ContCohomology.explicitMap1_explicitMap1_of_comp_eq`, whose coefficient sides are the
agreement of the two dictionaries; corestriction also uses its naturality in the coefficients,
`TauCeti.ContCohomology.explicitCor1_explicitMap1_id`.

## Main results

* `TauCeti.mu2EquivZMod2_kummerCoeffMap`, `TauCeti.mu2EquivZMod2_kummerCoeffMapSymm`: the value
  dictionaries `μ₂ ≃+ ZMod 2` of `K` and `L` agree along the identification of separable closures.
* `TauCeti.galoisRes_kummerClass`: restriction of the Kummer class of `a ∈ Kˣ` is the Kummer class
  of its image in `Lˣ`.
* `TauCeti.galoisCor_kummerClass`: corestriction of the Kummer class of `b ∈ Lˣ` is the Kummer
  class of `N_{L/K} b`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  display following it.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

variable [Invertible (2 : K)] [Invertible (2 : L)]

/-- **The `μ₂` dictionaries of `K` and `L` agree along the identification of separable
closures**: `TauCeti.kummerCoeffMap` sends `-1` to `-1`, so it does not change the value in
`ZMod 2`. -/
@[simp]
theorem mu2EquivZMod2_kummerCoeffMap (x : KummerCoeff K 2) :
    mu2EquivZMod2 L (kummerCoeffMap K 2 L σ x) = mu2EquivZMod2 K x := by
  rcases eq_zero_or_eq_mu2NegOne x with rfl | rfl
  · simp
  · have h : kummerCoeffMap K 2 L σ mu2NegOne = mu2NegOne :=
      Additive.toMul.injective (Subtype.ext (Units.ext (by simp)))
    rw [h, mu2EquivZMod2_apply_mu2NegOne, mu2EquivZMod2_apply_mu2NegOne]

/-- The inverse identification `TauCeti.kummerCoeffMapSymm` does not change the value in
`ZMod 2` either. -/
@[simp]
theorem mu2EquivZMod2_kummerCoeffMapSymm (y : KummerCoeff L 2) :
    mu2EquivZMod2 K (kummerCoeffMapSymm K 2 L σ y) = mu2EquivZMod2 L y := by
  rw [← mu2EquivZMod2_kummerCoeffMap K L σ, kummerCoeffMap_kummerCoeffMapSymm]

/-- **The coefficient dictionaries along `L/K`**: reading a value of `μ₂(Kˢ)` in `𝔽₂` and carrying
it to the trivial `𝔽₂` object of `G_L` is carrying it to `μ₂(Lˢ)` by `TauCeti.kummerCoeffMap` and
reading it there. -/
private theorem comp_kummerCoeffEquiv_eq_comp_kummerCoeffMap :
    ((trivialF2Equiv (AbsoluteGaloisGroup K)).trans
        (trivialF2Equiv (AbsoluteGaloisGroup L)).symm).toAddMonoidHom.comp
        (kummerCoeffEquiv K).toAddMonoidHom =
      (kummerCoeffEquiv L).toAddMonoidHom.comp (kummerCoeffMap K 2 L σ) :=
  AddMonoidHom.ext fun x => (trivialF2Equiv _).injective (by simp)

/-- The coefficient dictionaries along `L/K` in the other direction: reading a value of `μ₂(Lˢ)`
in `𝔽₂` and carrying it to the trivial `𝔽₂` object of `G_K` is carrying it to `μ₂(Kˢ)` by
`TauCeti.kummerCoeffMapSymm` and reading it there. -/
private theorem comp_kummerCoeffEquiv_eq_comp_kummerCoeffMapSymm :
    ((trivialF2Equiv (AbsoluteGaloisGroup L)).trans
        (trivialF2Equiv (AbsoluteGaloisGroup K)).symm).toAddMonoidHom.comp
        (kummerCoeffEquiv L).toAddMonoidHom =
      (kummerCoeffEquiv K).toAddMonoidHom.comp (kummerCoeffMapSymm K 2 L σ) :=
  AddMonoidHom.ext fun y => (trivialF2Equiv _).injective (by simp)

omit [Invertible (2 : L)] in
/-- The explicit mod-two Kummer class is the generic Kummer cocycle class pushed along the
coefficient dictionary `μ₂ ≃ 𝔽₂`, written as a compatible-pair pullback along the identity so
that it composes with the other pullbacks below. -/
private theorem kummerCocycleModTwoClass_eq_explicitMap1 {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    kummerCocycleModTwoClass K hα =
      explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K 2) (AbsoluteGaloisGroup K)
        (trivialF2 (AbsoluteGaloisGroup K)).V (ContinuousMonoidHom.id (AbsoluteGaloisGroup K))
        (kummerCoeffEquiv K).toAddMonoidHom continuous_of_discreteTopology
        (fun g x => by simp [TopRep.distribMulAction_smul]) (kummerCocycleClass hα) := by
  rw [kummerCocycleModTwoClass_def, kummerCocycleClass_def, H1pi, QuotientAddGroup.mk'_apply,
    explicitMap1_mk]
  congr 1
  refine Subtype.ext (funext fun g => (trivialF2Equiv _).injective ?_)
  rw [kummerCocycleModTwo_apply, cocyclesMap1_apply]
  simp [mu2EquivZMod2_kummerCocycle]

variable [FiniteDimensional K L]

/-- **Restriction of a Kummer class** (NSW, the display after (6.2.1), at `n = 2`): for a
`K`-embedding `σ : L →ₐ[K] Kˢ` of a finite extension, restriction `H¹(G_K, 𝔽₂) → H¹(G_L, 𝔽₂)`
sends the Kummer class of `a ∈ Kˣ` to the Kummer class of its image in `Lˣ`. -/
theorem galoisRes_kummerClass (a : Kˣ) :
    galoisRes K L σ 1 (kummerClass a) =
      kummerClass (Units.map (algebraMap K L).toMonoidHom a) := by
  obtain ⟨α, hα⟩ := exists_pow_eq_units_map (isUnit_of_invertible (2 : K)) a
  have hβ := units_map_separableClosureRingEquiv_symm_pow σ hα
  rw [kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq K a α hα,
    kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq L _ _ hβ, galoisRes_eq_map,
    ← ConcreteCategory.comp_apply,
    eqToHom_comp_trivialF2Map _ (ofDiscreteModule_trivialF2 _) (ofDiscreteModule_trivialF2 _)
      ((trivialF2Equiv _).trans (trivialF2Equiv _).symm).toAddMonoidHom
      (fun h x => by simp [TopRep.distribMulAction_smul])
      (fun m => by simp),
    ConcreteCategory.comp_apply, explicitH1AddEquivContinuousCohomology_map]
  congr 2
  -- The generic restriction square, with the restriction to `σ(L)`'s fixing subgroup and the
  -- transport to `G_L` combined into one compatible pair.
  have hres : explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K 2) (AbsoluteGaloisGroup L)
      (KummerCoeff L 2)
      ((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
        (absoluteGaloisGroupEquivFixingSubgroup K L σ :
          AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup))
      (kummerCoeffMap K 2 L σ) continuous_of_discreteTopology
      (fun g x => kummerCoeffMap_smul K 2 L σ g x) (kummerCocycleClass hα) =
        kummerCocycleClass hβ := by
    have h := congrArg Multiplicative.toAdd (kummerRes_kummerCocycleClass K 2 L σ hα)
    rw [toAdd_kummerRes, toAdd_ofAdd, toAdd_ofAdd, explicitRes1_eq_explicitMap1] at h
    rw [← h, ← AddMonoidHom.comp_apply, ← explicitMap1_comp]
    · exact DFunLike.congr_fun (explicitMap1_congr_of_eq _ _ _ _ _ _ _ _ rfl
        (AddMonoidHom.comp_id _).symm) _
    · exact fun g x => kummerCoeffMap_smul K 2 L σ g x
  rw [kummerCocycleModTwoClass_eq_explicitMap1 K hα, kummerCocycleModTwoClass_eq_explicitMap1 L hβ]
  refine Eq.trans ?_ (congrArg (explicitMap1 _ _ _ _ (ContinuousMonoidHom.id _) _ _ _) hres)
  exact explicitMap1_explicitMap1_of_comp_eq
    (hφ := by
      exact ContinuousMonoidHom.ext fun g => AlgEquiv.ext fun y =>
        (galoisSubgroupEquiv_apply K L σ g y).trans
          (absoluteGaloisGroupEquivFixingSubgroup_apply K L σ g y).symm)
    (hqf := by exact comp_kummerCoeffEquiv_eq_comp_kummerCoeffMap K L σ) ..

omit [Invertible (2 : K)] in
/-- The norm square of the Kummer isomorphism on explicit cocycle classes: the Kummer class of
`N_{L/K} b` is the corestriction of the transported Kummer class of `b`. -/
private theorem kummerCocycleClass_norm {b : Lˣ} {β : (SeparableClosure L)ˣ}
    (hβ : β ^ 2 = Units.map (algebraMap L (SeparableClosure L)).toMonoidHom b)
    {γ : (SeparableClosure K)ˣ}
    (hγ : γ ^ 2 =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom (Algebra.normUnits K b)) :
    kummerCocycleClass hγ =
      explicitCor1 (AbsoluteGaloisGroup K) (KummerCoeff K 2) σ.fieldRange.fixingSubgroup
        (isOpen_fixingSubgroup_fieldRange K L σ)
        (explicitMap1 (AbsoluteGaloisGroup L) (KummerCoeff L 2) ↥σ.fieldRange.fixingSubgroup
          (KummerCoeff K 2)
          ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
            ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
          (kummerCoeffMapSymm K 2 L σ) continuous_of_discreteTopology
          (kummerCoeffMapSymm_smul K 2 L σ) (kummerCocycleClass hβ)) := by
  have h := congrArg Multiplicative.toAdd
    (kummerCor_kummerMap K 2 L σ (isUnit_of_invertible (2 : L)) b)
  rw [toAdd_kummerCor, kummerMap_eq_kummerCocycleClass _ hβ] at h
  exact (kummerMap_eq_kummerCocycleClass _ hγ).symm.trans h.symm

/-- Corestriction of the explicit mod-two Kummer class of `b` along `L/K` is the explicit mod-two
Kummer class of `N_{L/K} b`. -/
private theorem explicitCor1_kummerCocycleModTwoClass {b : Lˣ} {β : (SeparableClosure L)ˣ}
    (hβ : β ^ 2 = Units.map (algebraMap L (SeparableClosure L)).toMonoidHom b)
    {γ : (SeparableClosure K)ˣ}
    (hγ : γ ^ 2 =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom (Algebra.normUnits K b)) :
    explicitCor1 (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V
        σ.fieldRange.fixingSubgroup (isOpen_fixingSubgroup_fieldRange K L σ)
        (explicitMap1 (AbsoluteGaloisGroup L) (trivialF2 (AbsoluteGaloisGroup L)).V
          ↥σ.fieldRange.fixingSubgroup (trivialF2 (AbsoluteGaloisGroup K)).V
          ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
            ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
          ((trivialF2Equiv _).trans (trivialF2Equiv _).symm).toAddMonoidHom
          continuous_of_discreteTopology
          (fun h x => by simp [Subgroup.smul_def, TopRep.distribMulAction_smul])
          (kummerCocycleModTwoClass L hβ)) =
      kummerCocycleModTwoClass K hγ := by
  have hcK : ∀ (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2),
      (kummerCoeffEquiv K).toAddMonoidHom (g • x) = g • (kummerCoeffEquiv K).toAddMonoidHom x :=
    fun g x => by simp [TopRep.distribMulAction_smul]
  rw [kummerCocycleModTwoClass_eq_explicitMap1 K hγ, kummerCocycleClass_norm K L σ hβ hγ,
    ← explicitCor1_explicitMap1_id _ _ _ _ _ continuous_of_discreteTopology hcK]
  refine congrArg (explicitCor1 _ _ _ _) ?_
  rw [kummerCocycleModTwoClass_eq_explicitMap1 L hβ]
  exact explicitMap1_explicitMap1_of_comp_eq (hφ := by exact ContinuousMonoidHom.ext fun _ => rfl)
    (hqf := by exact comp_kummerCoeffEquiv_eq_comp_kummerCoeffMapSymm K L σ) ..

/-- Corestriction along `L/K` of the Kummer class of `b`, computed at any open subgroup `U` of
`G_K` presented by an isomorphism `e : G_L ≃ₜ* U` that agrees with the one of `σ`. Quantifying
over `U` and `e` is what lets the statement be specialized both to the subgroup fixing `σ(L)`,
where the norm square of the Kummer isomorphism lives, and to `galoisSubgroup K L σ`. -/
private theorem trivialF2CorMap_trivialF2Map_kummerClass
    (U : Subgroup (AbsoluteGaloisGroup K)) (hU : IsOpen (U : Set (AbsoluteGaloisGroup K)))
    [U.FiniteIndex] (e : AbsoluteGaloisGroup L ≃ₜ* U) (hUσ : U = σ.fieldRange.fixingSubgroup)
    (he : ∀ (g : AbsoluteGaloisGroup L) (y : SeparableClosure K),
      (e g : AbsoluteGaloisGroup K) y =
        separableClosureRingEquiv K L σ (g ((separableClosureRingEquiv K L σ).symm y)))
    (b : Lˣ) :
    trivialF2CorMap (AbsoluteGaloisGroup K) U hU 1
        (trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom e.symm) 1 (kummerClass b)) =
      kummerClass (Algebra.normUnits K b) := by
  subst hUσ
  obtain rfl : e = absoluteGaloisGroupEquivFixingSubgroup K L σ :=
    ContinuousMulEquiv.ext fun g => Subtype.ext (AlgEquiv.ext fun y => by
      rw [he, absoluteGaloisGroupEquivFixingSubgroup_apply])
  obtain ⟨β, hβ⟩ := exists_pow_eq_units_map (isUnit_of_invertible (2 : L)) b
  obtain ⟨γ, hγ⟩ :=
    exists_pow_eq_units_map (isUnit_of_invertible (2 : K)) (Algebra.normUnits K b)
  have hmap := ConcreteCategory.congr_hom (eqToHom_comp_trivialF2Map
    (ContinuousMonoidHom.toContinuousMonoidHom (absoluteGaloisGroupEquivFixingSubgroup K L σ).symm)
    (ofDiscreteModule_trivialF2 _) (ofDiscreteModule_subgroup_trivialF2 _ _)
    ((trivialF2Equiv _).trans (trivialF2Equiv _).symm).toAddMonoidHom
    (fun h x => by simp [Subgroup.smul_def, TopRep.distribMulAction_smul])
    (fun m => by
      rw [eqToHom_ofDiscreteModule_trivialF2_apply]
      exact (congrArg _ (TopRep.eqToHom_hom_apply _ _)).trans
        ((trivialF2Equiv_cast (AbsoluteGaloisGroup K) _ _).trans (by simp))) 1)
    (explicitH1AddEquivContinuousCohomology _ _ (kummerCocycleModTwoClass L hβ))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    explicitH1AddEquivContinuousCohomology_map] at hmap
  rw [kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq L b β hβ,
    kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq K _ γ hγ, hmap,
    trivialF2CorMap_explicitH1AddEquivContinuousCohomology]
  exact congrArg _ (congrArg _ (explicitCor1_kummerCocycleModTwoClass K L σ hβ hγ))

/-- **Corestriction of a Kummer class is the Kummer class of the norm** (NSW, the display after
(6.2.1), at `n = 2`): for a `K`-embedding `σ : L →ₐ[K] Kˢ` of a finite extension, corestriction
`H¹(G_L, 𝔽₂) → H¹(G_K, 𝔽₂)` sends the Kummer class of `b ∈ Lˣ` to the Kummer class of
`N_{L/K} b`. -/
theorem galoisCor_kummerClass (b : Lˣ) :
    galoisCor K L σ 1 (kummerClass b) = kummerClass (Algebra.normUnits K b) := by
  rw [galoisCor_def, galoisF2Iso_inv, ConcreteCategory.comp_apply]
  exact trivialF2CorMap_trivialF2Map_kummerClass K L σ _ _ (galoisSubgroupEquiv K L σ)
    (galoisSubgroup_toSubgroup K L σ) (galoisSubgroupEquiv_apply K L σ) b

end TauCeti
