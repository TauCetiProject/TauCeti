/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# Restriction and corestriction of Brauer classes along a field extension

Let `L/K` be an extension and `σ : L →ₐ[K] Kˢ` a `K`-embedding into a separable closure of `K`.
Through `σ`, the absolute Galois group `G_L` is the subgroup `Gal(Kˢ/σ(L))` of `G_K` fixing
`σ(L)` (`TauCeti.absoluteGaloisGroupEquivFixingSubgroup`), and the identification of separable
closures carries the units of `Kˢ`, with the action of this subgroup, to the units of `Lˢ`, with
the action of `G_L` (`TauCeti.unitsCoeffMap`, `TauCeti.unitsCoeffMapSymm`). This file defines the
two maps between the Brauer groups `Br K = H²(G_K, (Kˢ)ˣ)` and `Br L` that they induce:

* restriction `brRes K L σ : Br K →+ Br L`, restriction to `Gal(Kˢ/σ(L))` followed by the
  transport to `G_L`;
* corestriction `brCor K L σ : Br L →+ Br K`, for a finite `L/K`: the transport to
  `Gal(Kˢ/σ(L))`, an open subgroup of index `[L : K]`, followed by corestriction to `G_K`.

Both are computed on the explicit model `H²(Gal(Kˢ/K), (Kˢ)ˣ)` of `Br K` (`unitsRepH2Equiv`),
exactly as `TauCeti.kummerRes` and `TauCeti.kummerCor` are on `H¹(·, μₙ)`. Restriction is the
pullback along the single compatible pair `G_L → G_K`, `(Kˢ)ˣ → (Lˢ)ˣ`
(`brRes_eq_explicitMap2`), and corestriction after restriction is multiplication by the degree
(`brCor_brRes`). Together with the restriction square `inv_L (brRes x) = [L : K] • inv_K x` of a
local invariant, the latter gives the corestriction square `inv_K (brCor y) = inv_L y`, since
restriction is then surjective.

## Main definitions

* `TauCeti.ClassFieldTheory.brRes`: restriction `Br K → Br L`.
* `TauCeti.ClassFieldTheory.brCor`: corestriction `Br L → Br K`, for a finite `L/K`.

## Main results

* `TauCeti.ClassFieldTheory.brRes_eq_explicitMap2`: restriction is the pullback along
  `G_L → G_K` and `(Kˢ)ˣ → (Lˢ)ˣ`.
* `TauCeti.ClassFieldTheory.brRes_relBrInfl`: restriction carries a relative Brauer class to
  the relative class obtained by base change.
  Its two ingredients are `TauCeti.restrictNormalHom_absoluteGaloisGroupEquivFixingSubgroup`
  (the Galois-group square) and `TauCeti.unitsCoeffMap_embeddedUnitsInvariants` (the coefficient
  square).
* `TauCeti.ClassFieldTheory.brCor_brRes`: `brCor (brRes x) = [L : K] • x`.

## References

* J.-P. Serre, *Local Fields*, Chapter VII, §7 and Chapter XIII, §3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5,
  and (1.5.7).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- **Restriction of Brauer classes** `Br K → Br L` along the extension `L/K` embedded in `Kˢ` by
`σ`: restriction from `G_K` to the subgroup `Gal(Kˢ/σ(L))` fixing `σ(L)`, followed by the
pullback along `G_L ≃ₜ* Gal(Kˢ/σ(L))` with the coefficient identification
`TauCeti.unitsCoeffMap K L σ : (Kˢ)ˣ → (Lˢ)ˣ`. -/
def brRes : Br K →+ Br L :=
  ((unitsRepH2Equiv L : H2 (AbsoluteGaloisGroup L) (UnitsCoeff L) →+ Br L).comp
    (explicitMap2 (↥σ.fieldRange.fixingSubgroup) (UnitsCoeff K) (AbsoluteGaloisGroup L)
      (UnitsCoeff L)
      (absoluteGaloisGroupEquivFixingSubgroup K L σ :
        AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup)
      (unitsCoeffMap K L σ) continuous_of_discreteTopology (unitsCoeffMap_smul K L σ))).comp
    ((explicitRes2 (AbsoluteGaloisGroup K) (UnitsCoeff K) σ.fieldRange.fixingSubgroup).comp
      ((unitsRepH2Equiv K).symm : Br K →+ H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)))

/-- `brRes K L σ` is restriction to the subgroup fixing `σ(L)` followed by the transport to `G_L`,
read on the explicit models of `Br K` and `Br L`. -/
theorem brRes_apply (x : Br K) :
    brRes K L σ x =
      unitsRepH2Equiv L (explicitMap2 (↥σ.fieldRange.fixingSubgroup) (UnitsCoeff K)
        (AbsoluteGaloisGroup L) (UnitsCoeff L)
        (absoluteGaloisGroupEquivFixingSubgroup K L σ :
          AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup)
        (unitsCoeffMap K L σ) continuous_of_discreteTopology (unitsCoeffMap_smul K L σ)
        (explicitRes2 (AbsoluteGaloisGroup K) (UnitsCoeff K) σ.fieldRange.fixingSubgroup
          ((unitsRepH2Equiv K).symm x))) :=
  (rfl)

/-- **Restriction is a pullback along a compatible pair**: on the explicit models, `brRes K L σ`
pulls a class back along the composite `G_L ≃ Gal(Kˢ/σ(L)) ↪ G_K`, with coefficients carried by
`TauCeti.unitsCoeffMap K L σ : (Kˢ)ˣ → (Lˢ)ˣ`. -/
theorem brRes_eq_explicitMap2 (x : Br K) :
    brRes K L σ x =
      unitsRepH2Equiv L (explicitMap2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (AbsoluteGaloisGroup L) (UnitsCoeff L)
        ((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
          (absoluteGaloisGroupEquivFixingSubgroup K L σ :
            AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup))
        (unitsCoeffMap K L σ) continuous_of_discreteTopology
        (fun g x => unitsCoeffMap_smul K L σ g x) ((unitsRepH2Equiv K).symm x)) := by
  rw [brRes_apply, explicitRes2_eq_explicitMap2]
  -- `explicitMap2_comp` composes the two pullbacks; its composite coefficient map
  -- `(unitsCoeffMap K L σ).comp (AddMonoidHom.id _)` is `unitsCoeffMap K L σ` by definition of
  -- `AddMonoidHom.comp`.
  exact congrArg (unitsRepH2Equiv L) (DFunLike.congr_fun (explicitMap2_comp _ _ _ _
    (ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup)
    (AddMonoidHom.id _) continuous_id (id_subgroupSubtype_smul _ _ _) _ _
    (absoluteGaloisGroupEquivFixingSubgroup K L σ :
      AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup)
    (unitsCoeffMap K L σ) continuous_of_discreteTopology (unitsCoeffMap_smul K L σ)) _).symm

section Relative

variable (K₀ L₀ E M : Type) [Field K₀] [Field L₀] [Field E] [Field M] [Algebra K₀ L₀]
  [Algebra K₀ E] [Algebra K₀ M] [Algebra L₀ M] [Algebra E M] [IsScalarTower K₀ L₀ M]
  [IsScalarTower K₀ E M] [FiniteDimensional K₀ E] [FiniteDimensional L₀ M] [Normal K₀ E]
  [Normal L₀ M] (sigma : L₀ →ₐ[K₀] SeparableClosure K₀)
  (rho : E →ₐ[K₀] SeparableClosure K₀) (tau : M →ₐ[L₀] SeparableClosure L₀)

/-- **Restriction commutes with relative Brauer inflation.** Suppose `E/K₀` and `M/L₀` are finite
normal extensions in a base-change square, with their embeddings into the chosen separable
closures compatible under `separableClosureRingEquiv K₀ L₀ sigma`. Restricting the relative class
of `E/K₀` from `Br K₀` to `Br L₀` is the relative class of `M/L₀` obtained by the usual
base-change map

`H²(Gal(E/K₀), Eˣ) → H²(Gal(M/L₀), Mˣ)`.

This is the finite-layer comparison used to reduce the restriction square for the local Brauer
invariant to its arithmetic normalization on unramified layers. -/
theorem brRes_relBrInfl
    (hcompat : ∀ x : E,
      separableClosureRingEquiv K₀ L₀ sigma (tau (algebraMap E M x)) = rho x)
    (x : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K₀) Eˣ) 2) :
    brRes K₀ L₀ sigma (relBrInfl K₀ E rho x) =
      relBrInfl L₀ M tau
        (groupCohomology.map
          ((AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K₀))
          (unitsBaseChangeHom K₀ E L₀ M) 2 x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    rw [relBrInfl_H2π, brRes_eq_explicitMap2, AddEquiv.symm_apply_apply]
    rw [explicitMap2_mk (AbsoluteGaloisGroup K₀) (UnitsCoeff K₀)
      (AbsoluteGaloisGroup L₀) (UnitsCoeff L₀)
      ((ContinuousMonoidHom.subgroupSubtype sigma.fieldRange.fixingSubgroup).comp
        (absoluteGaloisGroupEquivFixingSubgroup K₀ L₀ sigma :
          AbsoluteGaloisGroup L₀ →ₜ* ↥sigma.fieldRange.fixingSubgroup))
      (unitsCoeffMap K₀ L₀ sigma) continuous_of_discreteTopology
      (fun g x => unitsCoeffMap_smul K₀ L₀ sigma g x) (relBrCocycle K₀ E rho c),
      groupCohomology.H2π_comp_map_apply, relBrInfl_H2π]
    congr 1
    apply congrArg (H2pi (AbsoluteGaloisGroup L₀) (UnitsCoeff L₀))
    apply Subtype.ext
    funext ⟨g, h⟩
    rw [cocyclesMap2_apply (AbsoluteGaloisGroup K₀) (UnitsCoeff K₀)
      (AbsoluteGaloisGroup L₀) (UnitsCoeff L₀)
      ((ContinuousMonoidHom.subgroupSubtype sigma.fieldRange.fixingSubgroup).comp
        (absoluteGaloisGroupEquivFixingSubgroup K₀ L₀ sigma :
          AbsoluteGaloisGroup L₀ →ₜ* ↥sigma.fieldRange.fixingSubgroup))
      (unitsCoeffMap K₀ L₀ sigma) continuous_of_discreteTopology
      (fun g x => unitsCoeffMap_smul K₀ L₀ sigma g x),
      relBrCocycle_apply, relBrCocycle_apply, ContinuousMonoidHom.comp_toFun,
      ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.subgroupSubtype_apply,
      ContinuousMonoidHom.subgroupSubtype_apply, ContinuousMonoidHom.coe_coe,
      restrictNormalHom_absoluteGaloisGroupEquivFixingSubgroup K₀ L₀ sigma E M rho tau hcompat g,
      restrictNormalHom_absoluteGaloisGroupEquivFixingSubgroup K₀ L₀ sigma E M rho tau hcompat h]
    rw [congrFun (groupCohomology.coe_mapCocycles₂
      (f := ((AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K₀)))
      (φ := unitsBaseChangeHom K₀ E L₀ M) c)
      (tau.restrictNormalHom g, tau.restrictNormalHom h)]
    -- Unfold the standard degree-two cochain pullback at this pair; its coefficient leg is
    -- exactly `unitsBaseChangeHom`.
    change
      unitsCoeffMap K₀ L₀ sigma
          (embeddedUnitsEquivInvariants K₀ E rho
            (Rep.toAdditive (c (_, _)) : Additive Eˣ) : UnitsCoeff K₀) =
        (embeddedUnitsEquivInvariants L₀ M tau
          (Rep.toAdditive ((unitsBaseChangeHom K₀ E L₀ M).hom (c (_, _)))) : UnitsCoeff L₀)
    generalize c (_, _) = z
    obtain ⟨a, rfl⟩ := (Rep.toAdditive (M := Gal(E/K₀)) (G := Eˣ)).symm.surjective z
    rw [← ofMul_toMul a, unitsBaseChangeHom_apply]
    simpa only [AddEquiv.apply_symm_apply, embeddedUnitsEquivInvariants_apply, toMul_ofMul] using
      unitsCoeffMap_embeddedUnitsInvariants K₀ L₀ sigma E M rho tau hcompat a.toMul

end Relative

/-- The transport of `H²` from `Gal(Kˢ/σ(L))` to `G_L` and back is the identity. -/
private theorem explicitMap2_symm_explicitMap2
    (x : H2 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K)) :
    explicitMap2 (AbsoluteGaloisGroup L) (UnitsCoeff L) ↥σ.fieldRange.fixingSubgroup
        (UnitsCoeff K)
        ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
          ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
        (unitsCoeffMapSymm K L σ) continuous_of_discreteTopology (unitsCoeffMapSymm_smul K L σ)
        (explicitMap2 (↥σ.fieldRange.fixingSubgroup) (UnitsCoeff K) (AbsoluteGaloisGroup L)
          (UnitsCoeff L)
          (absoluteGaloisGroupEquivFixingSubgroup K L σ :
            AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup)
          (unitsCoeffMap K L σ) continuous_of_discreteTopology (unitsCoeffMap_smul K L σ) x) =
      x := by
  -- Compose the two transports, recognise the composite pair as the identity, then cancel.
  rw [← AddMonoidHom.comp_apply, ← explicitMap2_comp, explicitMap2_congr_of_eq _ _ _ _ _
    (ContinuousMonoidHom.id _) _ (AddMonoidHom.id _) (hq := continuous_id)
    (hψ := fun _ _ => rfl) (ContinuousMonoidHom.ext fun h => by simp)
    (AddMonoidHom.ext fun x => by simp)]
  simp

variable [FiniteDimensional K L]

/-- **Corestriction of Brauer classes** `Br L → Br K` along the finite extension `L/K` embedded in
`Kˢ` by `σ`: the pullback along `Gal(Kˢ/σ(L)) ≃ₜ* G_L` with the coefficient identification
`TauCeti.unitsCoeffMapSymm K L σ : (Lˢ)ˣ → (Kˢ)ˣ`, followed by corestriction from the open
subgroup `Gal(Kˢ/σ(L))` to `G_K`. -/
def brCor : Br L →+ Br K :=
  ((unitsRepH2Equiv K : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) →+ Br K).comp
    (explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) σ.fieldRange.fixingSubgroup
      (isOpen_fixingSubgroup_fieldRange K L σ))).comp
    ((explicitMap2 (AbsoluteGaloisGroup L) (UnitsCoeff L) ↥σ.fieldRange.fixingSubgroup
      (UnitsCoeff K)
      ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
        ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
      (unitsCoeffMapSymm K L σ) continuous_of_discreteTopology
      (unitsCoeffMapSymm_smul K L σ)).comp
      ((unitsRepH2Equiv L).symm : Br L →+ H2 (AbsoluteGaloisGroup L) (UnitsCoeff L)))

/-- `brCor K L σ` is the transport to the subgroup fixing `σ(L)` followed by corestriction to
`G_K`, read on the explicit models of `Br L` and `Br K`. -/
theorem brCor_apply (y : Br L) :
    brCor K L σ y =
      unitsRepH2Equiv K (explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        σ.fieldRange.fixingSubgroup (isOpen_fixingSubgroup_fieldRange K L σ)
        (explicitMap2 (AbsoluteGaloisGroup L) (UnitsCoeff L) ↥σ.fieldRange.fixingSubgroup
          (UnitsCoeff K)
          ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
            ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
          (unitsCoeffMapSymm K L σ) continuous_of_discreteTopology
          (unitsCoeffMapSymm_smul K L σ) ((unitsRepH2Equiv L).symm y))) :=
  (rfl)

/-- **Corestriction after restriction is multiplication by the degree**:
`brCor (brRes x) = [L : K] • x` for every Brauer class `x` of `K`. -/
@[simp]
theorem brCor_brRes (x : Br K) : brCor K L σ (brRes K L σ x) = Module.finrank K L • x := by
  -- Cancel the coefficient transports, leaving corestriction after restriction on `H²`.
  simp only [brCor_apply, brRes_apply, AddEquiv.symm_apply_apply, explicitMap2_symm_explicitMap2]
  -- `cor ∘ res` is multiplication by the index `[G_K : Gal(Kˢ/σ(L))] = [L : K]`.
  rw [explicitCor2_comp_res2, ← galoisSubgroup_toSubgroup K L σ, galoisSubgroup_index]
  simp

end TauCeti.ClassFieldTheory
