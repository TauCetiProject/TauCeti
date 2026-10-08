/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ComparisonDegreeTwo

/-!
# Base change of Brauer classes along an arbitrary field extension

For an arbitrary field extension `L/K`, not necessarily algebraic, this file defines the
**base change** of cohomological Brauer classes

`brBaseChange K L : Br K →+ Br L`.

Choose a `K`-embedding `τ : Kˢ →ₐ[K] Lˢ` of separable closures. It induces the compatible pair
made of the continuous homomorphism `TauCeti.absoluteGaloisGroupMap τ : G_L → G_K` and the map
`(Kˢ)ˣ → (Lˢ)ˣ` of units, `unitsCoeffBaseChange τ`, and `brBaseChange K L` is the pullback along
this pair on the explicit model `H²(Gal(Kˢ/K), (Kˢ)ˣ)` of `Br K` (`unitsRepH2Equiv`). For the
completion `K_v` of a number field it is the localization map `Br K → Br K_v`, restriction to the
decomposition group, which is how the local invariants of a global Brauer class are defined.

The map does not depend on `τ` (`brBaseChange_apply` holds for every `τ`): two embeddings differ
by an automorphism `h` of `Kˢ`, which changes the compatible pair by the inner automorphism of
`h`, and inner automorphisms act trivially on cohomology
(`TauCeti.ContCohomology.explicitMap2_eq_self_of_inner`). Consequently base change is functorial
(`brBaseChange_self`, `brBaseChange_brBaseChange`), and for an extension embedded in `Kˢ` it is
the restriction `brRes` of `TauCeti.NumberTheory.ClassFieldTheory.Brauer.Restriction`, whichever
embedding is used there (`brBaseChange_eq_brRes`).

On central simple algebras, base change is `A ↦ A ⊗_K L`; that comparison is not made here.

## Main definitions

* `TauCeti.ClassFieldTheory.unitsCoeffBaseChange τ`: the map `(Kˢ)ˣ → (Lˢ)ˣ` along `τ`.
* `TauCeti.ClassFieldTheory.brBaseChange K L`: base change `Br K →+ Br L`.

## Main results

* `TauCeti.ClassFieldTheory.explicitMap2_absoluteGaloisGroupMap_eq`: a pullback on `H²` along
  the decomposition map of an embedding `τ` of separable closures and a coefficient map that
  depends on `τ` compatibly with the Galois action does not depend on `τ`.
* `TauCeti.ClassFieldTheory.brBaseChange_apply`: base change is the pullback along the compatible
  pair of any embedding `τ` of separable closures.
* `TauCeti.ClassFieldTheory.brBaseChange_self`,
  `TauCeti.ClassFieldTheory.brBaseChange_brBaseChange`: functoriality in the extension.
* `TauCeti.ClassFieldTheory.brBaseChange_eq_brRes`: for an extension embedded in `Kˢ`, base
  change is restriction.
* `TauCeti.ClassFieldTheory.brBaseChange_relBrInfl`: base change of a class inflated from a finite
  normal layer `L/K` is inflated from any finite normal layer `M/F` receiving `L`, along restriction
  `Gal(M/F) → Gal(L/K)` and the inclusion `Lˣ → Mˣ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5,
  and Chapter VIII, §1, for the localization maps of Galois cohomology.
* J.-P. Serre, *Local Fields*, Chapter X, §4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

universe u v w

/-! ### The coefficient map -/

section Coefficients

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- **The units of `Kˢ` as units of `Lˢ`** along an embedding `τ : Kˢ →ₐ[K] Lˢ`: the coefficient
leg of base change of Brauer classes. -/
def unitsCoeffBaseChange : UnitsCoeff K →+ UnitsCoeff L :=
  MonoidHom.toAdditive (Units.map (τ : SeparableClosure K →* SeparableClosure L))

/-- `unitsCoeffBaseChange τ` applies `τ` to a unit. -/
@[simp]
theorem toMul_unitsCoeffBaseChange (x : UnitsCoeff K) :
    (unitsCoeffBaseChange τ x).toMul =
      Units.map (τ : SeparableClosure K →* SeparableClosure L) x.toMul :=
  (rfl)

/-- **`unitsCoeffBaseChange τ` is equivariant** along `absoluteGaloisGroupMap τ : G_L → G_K`. -/
theorem unitsCoeffBaseChange_smul (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
    unitsCoeffBaseChange τ (absoluteGaloisGroupMap τ g • x) = g • unitsCoeffBaseChange τ x := by
  refine Additive.toMul.injective (Units.ext ?_)
  simp only [toMul_unitsCoeffBaseChange, Additive.toMul_smul, AlgEquiv.smul_units_def,
    Units.coe_map, MonoidHom.coe_ofClass, absoluteGaloisGroupMap_commutes]

/-- Changing the embedding `τ` by an automorphism `h` of `Kˢ` precomposes the coefficient map with
the action of `h`. -/
theorem unitsCoeffBaseChange_comp (h : AbsoluteGaloisGroup K) (x : UnitsCoeff K) :
    unitsCoeffBaseChange (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) x =
      unitsCoeffBaseChange τ (h • x) := by
  refine Additive.toMul.injective (Units.ext ?_)
  simp only [toMul_unitsCoeffBaseChange, Additive.toMul_smul, AlgEquiv.smul_units_def,
    Units.coe_map, MonoidHom.coe_ofClass, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

end Coefficients

/-! ### Base change of Brauer classes -/

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

/-- **Pullbacks along embeddings of separable closures do not depend on the embedding.** Let
`M` be a discrete `G_K`-module, `N` a discrete `G_L`-module, and `F τ : M → N` a coefficient map
for every `K`-embedding `τ : Kˢ →ₐ[K] Lˢ`, equivariant along `absoluteGaloisGroupMap τ`, such
that changing `τ` by an automorphism `h` of `Kˢ` precomposes `F τ` with the action of `h`. Then
the pullback on the explicit `H²` along `(absoluteGaloisGroupMap τ, F τ)` is the same for every
`τ`: a second embedding is `τ ∘ h`, and the pair of `τ ∘ h` is that of `τ` after the inner pair
of `h`, which acts trivially on cohomology. -/
theorem explicitMap2_absoluteGaloisGroupMap_eq
    {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    {N : Type v} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (AbsoluteGaloisGroup L) N] [ContinuousSMul (AbsoluteGaloisGroup L) N]
    (F : (SeparableClosure K →ₐ[K] SeparableClosure L) → M →+ N)
    (hF : ∀ τ (g : AbsoluteGaloisGroup L) (m : M), F τ (absoluteGaloisGroupMap τ g • m) = g • F τ m)
    (hFcomp : ∀ τ (h : AbsoluteGaloisGroup K) (m : M),
      F (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) m = F τ (h • m))
    (τ τ' : SeparableClosure K →ₐ[K] SeparableClosure L) :
    explicitMap2 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup L) N (absoluteGaloisGroupMap τ)
        (F τ) continuous_of_discreteTopology (hF τ) =
      explicitMap2 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup L) N
        (absoluteGaloisGroupMap τ') (F τ') continuous_of_discreteTopology (hF τ') := by
  obtain ⟨h, rfl⟩ := τ.exists_comp_eq_of_normal τ'
  -- The inner compatible pair of `h` on `H²(G_K, M)`.
  let c : AbsoluteGaloisGroup K →ₜ* AbsoluteGaloisGroup K :=
    { toMonoidHom := (MulAut.conj h⁻¹).toMonoidHom
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const }
  have hc (x : AbsoluteGaloisGroup K) : c x = h⁻¹ * x * h := by simp [c]
  let f := DistribSMul.toAddMonoidHom M h
  have hf (x : AbsoluteGaloisGroup K) (m : M) : f (c x • m) = x • f m := by
    simp only [f, DistribSMul.toAddMonoidHom_apply, hc, smul_smul]
    congr 1
    group
  -- The pair of `τ ∘ h` is the pair of `τ` after the inner pair of `h`.
  have hgrp : absoluteGaloisGroupMap (τ.comp h) = c.comp (absoluteGaloisGroupMap τ) :=
    ContinuousMonoidHom.ext fun g ↦ by
      rw [ContinuousMonoidHom.comp_toFun, hc, absoluteGaloisGroupMap_comp]
  have hcoeff : F (τ.comp h) = (F τ).comp f := AddMonoidHom.ext fun m ↦ hFcomp τ h m
  have hψ : ∀ (g : AbsoluteGaloisGroup L) (m : M),
      (F τ).comp f (c.comp (absoluteGaloisGroupMap τ) g • m) = g • (F τ).comp f m :=
    fun g m ↦ by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ContinuousMonoidHom.comp_toFun, hf,
        hF]
  have hpair := explicitMap2_congr_of_eq (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup L) N _ _ _ _
    (hf := continuous_of_discreteTopology) (hq := continuous_of_discreteTopology)
    (hφ := hF (τ.comp h)) (hψ := hψ) hgrp hcoeff
  rw [hpair, explicitMap2_comp (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup K) M c f
    continuous_of_discreteTopology hf (AbsoluteGaloisGroup L) N (absoluteGaloisGroupMap τ) (F τ)
    continuous_of_discreteTopology (hF τ)]
  refine AddMonoidHom.ext fun x ↦ ?_
  rw [AddMonoidHom.comp_apply, explicitMap2_eq_self_of_inner _ _ h c hc f (fun _ ↦ rfl)]

/-- **Base change of Brauer classes** `Br K → Br L` along an arbitrary field extension `L/K`: the
pullback along the absolute Galois groups `G_L → G_K` and the units `(Kˢ)ˣ → (Lˢ)ˣ` induced by an
embedding of separable closures `Kˢ → Lˢ`. It does not depend on the embedding
(`brBaseChange_apply`). For a completion `K_v` of a number field `K` it is the localization map
`Br K → Br K_v`. -/
def brBaseChange : Br K →+ Br L :=
  ((unitsRepH2Equiv L : H2 (AbsoluteGaloisGroup L) (UnitsCoeff L) →+ Br L).comp
    (explicitMap2 (AbsoluteGaloisGroup K) (UnitsCoeff K) (AbsoluteGaloisGroup L) (UnitsCoeff L)
      (absoluteGaloisGroupMap IsSepClosed.lift) (unitsCoeffBaseChange IsSepClosed.lift)
      continuous_of_discreteTopology (unitsCoeffBaseChange_smul IsSepClosed.lift))).comp
    ((unitsRepH2Equiv K).symm : Br K →+ H2 (AbsoluteGaloisGroup K) (UnitsCoeff K))

/-- **Base change is the pullback along any embedding of separable closures**: for every
`K`-embedding `τ : Kˢ →ₐ[K] Lˢ`, `brBaseChange K L` is the pullback along `G_L → G_K` and
`(Kˢ)ˣ → (Lˢ)ˣ` induced by `τ`, read on the explicit models of `Br K` and `Br L`. -/
theorem brBaseChange_apply (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (x : Br K) :
    brBaseChange K L x =
      unitsRepH2Equiv L (explicitMap2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (AbsoluteGaloisGroup L) (UnitsCoeff L) (absoluteGaloisGroupMap τ)
        (unitsCoeffBaseChange τ) continuous_of_discreteTopology (unitsCoeffBaseChange_smul τ)
        ((unitsRepH2Equiv K).symm x)) := by
  rw [brBaseChange, explicitMap2_absoluteGaloisGroupMap_eq K L (fun τ ↦ unitsCoeffBaseChange τ)
    unitsCoeffBaseChange_smul unitsCoeffBaseChange_comp IsSepClosed.lift τ]
  rfl

/-- Base change along the trivial extension `K/K` is the identity. -/
@[simp]
theorem brBaseChange_self (x : Br K) : brBaseChange K K x = x := by
  have hpair := explicitMap2_congr_of_eq (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup K) (UnitsCoeff K) (absoluteGaloisGroupMap (AlgHom.id K _))
    (ContinuousMonoidHom.id _) (unitsCoeffBaseChange (AlgHom.id K _)) (AddMonoidHom.id _)
    (hf := continuous_of_discreteTopology) (hq := continuous_id)
    (hφ := unitsCoeffBaseChange_smul (AlgHom.id K _)) (hψ := fun _ _ ↦ rfl)
    (ContinuousMonoidHom.ext fun _ ↦ (absoluteGaloisGroupMap_eq_iff _).2 fun _ ↦ rfl)
    (AddMonoidHom.ext fun _ ↦ Additive.toMul.injective (Units.ext (by simp)))
  rw [brBaseChange_apply K K (AlgHom.id K _), hpair,
    explicitMap2_id (G := AbsoluteGaloisGroup K) (M := UnitsCoeff K), AddMonoidHom.id_apply,
    AddEquiv.apply_symm_apply]

/-- **Base change is transitive**: for a tower `K ⊆ L ⊆ M`, base change from `K` to `L` followed
by base change from `L` to `M` is base change from `K` to `M`. -/
@[simp]
theorem brBaseChange_brBaseChange (M : Type w) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (x : Br K) :
    brBaseChange L M (brBaseChange K L x) = brBaseChange K M x := by
  let τ : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  let τ' : SeparableClosure L →ₐ[L] SeparableClosure M := IsSepClosed.lift
  -- The composite `Kˢ → Lˢ → Mˢ` is a `K`-embedding.
  have : IsScalarTower K L (SeparableClosure M) := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K M (SeparableClosure M),
      IsScalarTower.algebraMap_apply K L M, ← IsScalarTower.algebraMap_apply L M]
  let τ'' : SeparableClosure K →ₐ[K] SeparableClosure M := (τ'.restrictScalars K).comp τ
  have hpair := explicitMap2_congr_of_eq (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup M) (UnitsCoeff M) (absoluteGaloisGroupMap τ'')
    ((absoluteGaloisGroupMap τ).comp (absoluteGaloisGroupMap τ')) (unitsCoeffBaseChange τ'')
    ((unitsCoeffBaseChange τ').comp (unitsCoeffBaseChange τ))
    (hf := continuous_of_discreteTopology) (hq := continuous_of_discreteTopology)
    (hφ := unitsCoeffBaseChange_smul τ'')
    (hψ := (absoluteGaloisGroupMap τ).comp_map_smul (absoluteGaloisGroupMap τ')
      (unitsCoeffBaseChange τ) (unitsCoeffBaseChange τ')
      (unitsCoeffBaseChange_smul τ) (unitsCoeffBaseChange_smul τ'))
    (ContinuousMonoidHom.ext fun g ↦
      (absoluteGaloisGroupMap_absoluteGaloisGroupMap τ τ' τ'' (fun _ ↦ rfl) g).symm)
    (AddMonoidHom.ext fun _ ↦ Additive.toMul.injective (Units.ext (by simp [τ''])))
  rw [brBaseChange_apply K L τ, brBaseChange_apply L M τ', brBaseChange_apply K M τ'',
    AddEquiv.symm_apply_apply, hpair,
    explicitMap2_comp (G := AbsoluteGaloisGroup K) (M := UnitsCoeff K)
      (H := AbsoluteGaloisGroup L) (N := UnitsCoeff L)
      (K := AbsoluteGaloisGroup M) (P := UnitsCoeff M), AddMonoidHom.comp_apply]

/-- **Base change along an embedded extension is restriction**: if `L/K` is embedded in `Kˢ` by
`σ`, then `brBaseChange K L` is the restriction `brRes K L σ`. In particular `brRes K L σ` does
not depend on `σ`. -/
theorem brBaseChange_eq_brRes (σ : L →ₐ[K] SeparableClosure K) :
    brBaseChange K L = brRes K L σ := by
  -- Base change along the inverse of the identification `Lˢ ≃ Kˢ` extending `σ`.
  let ψ : SeparableClosure K →ₐ[K] SeparableClosure L :=
    (AlgEquiv.ofRingEquiv (f := (separableClosureRingEquiv K L σ).symm)
      (separableClosureRingEquiv_symm_algebraMap_base K L σ) :
        SeparableClosure K →ₐ[K] SeparableClosure L)
  refine AddMonoidHom.ext fun x ↦ ?_
  have hpair := explicitMap2_congr_of_eq (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup L) (UnitsCoeff L) (absoluteGaloisGroupMap ψ)
    ((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
      (absoluteGaloisGroupEquivFixingSubgroup K L σ :
        AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup))
    (unitsCoeffBaseChange ψ) (unitsCoeffMap K L σ)
    (hf := continuous_of_discreteTopology) (hq := continuous_of_discreteTopology)
    (hφ := unitsCoeffBaseChange_smul ψ) (hψ := fun g m ↦ unitsCoeffMap_smul K L σ g m)
    (ContinuousMonoidHom.ext fun g ↦ (absoluteGaloisGroupMap_eq_iff ψ).2 fun y ↦ by simp [ψ])
    (AddMonoidHom.ext fun _ ↦ Additive.toMul.injective (Units.ext (by simp [ψ])))
  rw [brBaseChange_apply K L ψ, brRes_eq_explicitMap2, hpair]

/-! ### Base change of inflated classes -/

section Relative

variable (K : Type) [Field K] (F : Type) [Field F] [Algebra K F]
  (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Normal K L]
  (M : Type) [Field M] [Algebra F M] [FiniteDimensional F M] [Normal F M]
  [Algebra K M] [IsScalarTower K F M] [Algebra L M] [IsScalarTower K L M]
  (σ : L →ₐ[K] SeparableClosure K) (σ' : M →ₐ[F] SeparableClosure F)

/-- **Base change of an inflated Brauer class.** Let `L/K` be finite normal, embedded in `Kˢ`
by `σ`, let `F/K` be any extension and `M/F` finite normal, embedded in `Fˢ` by `σ'`, with a
compatible `K`-embedding `L → M`. Then base change to `F` of the class inflated from
`y ∈ H²(Gal(L/K), Lˣ)` is the class inflated from the image of `y` in `H²(Gal(M/F), Mˣ)`, along
restriction `Gal(M/F) → Gal(L/K)` and the inclusion `Lˣ → Mˣ`. -/
theorem brBaseChange_relBrInfl (y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) :
    brBaseChange K F (relBrInfl K L σ y) =
      relBrInfl F M σ' (groupCohomology.map
        ((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K))
        (unitsBaseChangeHom K L F M) 2 y) := by
  -- An embedding `τ : Kˢ → Fˢ` with `τ ∘ σ = σ' ∘ (L → M)`, extending the embedding
  -- `σ' ∘ (L → M)` of `σ(L)` to the separable extension `Kˢ/σ(L)`.
  obtain ⟨τ, hτ⟩ : ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure F,
      ∀ x : L, τ (σ x) = σ' (algebraMap L M x) := by
    obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) σ.fieldRange
      (E := SeparableClosure K) (M := SeparableClosure F)
      (((σ'.restrictScalars K).comp (IsScalarTower.toAlgHom K L M)).comp
        (σ.equivFieldRange.symm : σ.fieldRange →ₐ[K] L))
    refine ⟨τ, fun x ↦ ?_⟩
    have := congrArg (fun g : σ.fieldRange →ₐ[K] SeparableClosure F ↦ g (σ.equivFieldRange x)) hτ
    simpa [AlgHom.domRestrict] using this
  -- Restricting `g ∈ G_F` to `M` and then to `L` is restricting its image in `G_K` to `L`.
  have hres (g : AbsoluteGaloisGroup F) : σ.restrictNormalHom (absoluteGaloisGroupMap τ g) =
      (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
        (σ'.restrictNormalHom g) := by
    refine σ.restrictNormalHom_eq_iff.2 fun x ↦ τ.injective ?_
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, absoluteGaloisGroupMap_commutes, hτ, hτ,
      ← AlgHom.restrictNormalHom_commutes]
    congr 1
    exact (AlgEquiv.restrictNormal_commutes ((σ'.restrictNormalHom g).restrictScalars K) L x).symm
  induction y using groupCohomology.H2_induction_on with
  | h c =>
  rw [groupCohomology.H2π_comp_map_apply, relBrInfl_H2π, relBrInfl_H2π, brBaseChange_apply K F τ,
    AddEquiv.symm_apply_apply, explicitMap2_mk]
  congr 2
  refine Subtype.ext (funext fun p ↦ ?_)
  obtain ⟨g, h⟩ := p
  refine (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ g h).trans ?_
  refine Additive.toMul.injective (Units.ext ?_)
  rw [toMul_unitsCoeffBaseChange, relBrCocycle_apply, relBrCocycle_apply, hres, hres]
  simp only [embeddedUnitsEquivInvariants_apply, toMul_coe_embeddedUnitsInvariants]
  rw [toMul_mapCocycles₂_unitsBaseChangeHom]
  -- Both sides are `σ' (algebraMap L M u)` for the same unit `u` of `L`, by the choice of `τ`.
  exact hτ _

end Relative

end TauCeti.ClassFieldTheory
