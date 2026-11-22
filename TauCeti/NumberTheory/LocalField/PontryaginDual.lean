/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.Different.Quotient
public import TauCeti.NumberTheory.LocalField.IntegerRing.Quotient
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.Continuous.Pontryagin.Module
public import TauCeti.RingTheory.DedekindDomain.Different.Quotient
public import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology
import TauCeti.RingTheory.Length
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Coefficient-linear Pontryagin duality over rings of integers of local fields

For a nonarchimedean local field `L` with ring of integers `𝒪[L]`, `L ⧸ 𝒪[L]` is a discrete
injective `𝒪[L]`-module whose `𝓂[L]`-torsion has length `1`, so `TauCeti.ModulePontryaginDual`
gives compact–discrete duality between discrete torsion `𝒪[L]`-modules and compact `𝒪[L]`-modules,
and self-duality of `𝒪[L] ⧸ 𝓂[L]^n`.

For a compatible separable extension `L / K`, trace induces a canonical continuous `𝒪[K]`-linear
equivalence `traceDualPontryaginEquiv` (using the inverse different `𝒪[L]ᵛ`), and choosing a
uniformizer `ϖ` of `𝒪[L]` gives the comparison equivalence `pontryaginDualEquivOfUniformizer`
with coefficients in `L ⧸ 𝒪[L]`. Both comparisons are compatible with `𝒪[L]`-actions and
contragredient group representations.

## References

* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §2.
* J.-P. Serre, *Local Fields*, Chapter III, §§3 and 6.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing TauCeti.ModulePontryaginDual

namespace TauCeti

section SingleField

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- **Cogenerator condition for `L ⧸ 𝒪[L]`**: `Hom_𝒪[L](𝒪[L] ⧸ 𝔪, L ⧸ 𝒪[L])` has length `1` for
every maximal ideal `𝔪` of `𝒪[L]`. -/
theorem length_linearMap_quotient_maximalIdeal_eq_one :
    ∀ 𝔪 : Ideal 𝒪[L], 𝔪.IsMaximal →
      Module.length 𝒪[L] ((𝒪[L] ⧸ 𝔪) →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L))) = 1 := by
  intro 𝔪 h𝔪; obtain rfl := IsLocalRing.eq_maximalIdeal h𝔪
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hpow : (𝓂[L] ^ 1 : Ideal 𝒪[L]) = 𝓂[L] := pow_one _
  have e : ((𝒪[L] ⧸ 𝓂[L]) →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L))) ≃ₗ[𝒪[L]] (𝒪[L] ⧸ 𝓂[L]) :=
    (𝓂[L].quotientLinearMapEquivTorsionBySet _).trans
      ((LinearEquiv.ofEq _ _ (by rw [hpow])).symm.trans
        ((quotientMaximalIdealPowEquivTorsionBySet hϖ 1).symm.trans
          (Submodule.quotEquivOfEq _ _ hpow)))
  rw [e.length_eq, Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal 𝒪[L]).out

/-- **Compactness of the dual of a discrete torsion `𝒪[L]`-module**: `Hom_𝒪[L](M, L ⧸ 𝒪[L])` is
a compact `𝒪[L]`-module whenever `M` is discrete and torsion. -/
theorem isCompactModule_dual_of_isTorsion {M : Type*} [AddCommGroup M] [Module 𝒪[L] M]
    [TopologicalSpace M] [DiscreteTopology M] (hM : Module.IsTorsion 𝒪[L] M) :
    IsCompactModule 𝒪[L] (ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) := by
  have := continuousSMul_iff_isTorsion.mpr hM
  exact isCompactModule_of_discrete (length_linearMap_quotient_maximalIdeal_eq_one L)

/-- **The dual of a compact `𝒪[L]`-module is torsion**: every continuous `𝒪[L]`-linear functional
on a compact `𝒪[L]`-module into `L ⧸ 𝒪[L]` is killed by a nonzero element of `𝒪[L]`. -/
theorem isTorsion_dual_of_isCompactModule {N : Type*} [AddCommGroup N] [Module 𝒪[L] N]
    [TopologicalSpace N] (hN : IsCompactModule 𝒪[L] N) :
    Module.IsTorsion 𝒪[L] (ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) N) := by
  have := hN.compactSpace; exact continuousSMul_iff_isTorsion.mp inferInstance

variable {L} in
/-- **Self-duality of `𝒪[L] ⧸ 𝓂[L]^n`**: choosing a uniformizer `ϖ`, the Pontryagin dual of
`𝒪[L] ⧸ 𝓂[L]^n` with respect to `L ⧸ 𝒪[L]` is continuously `𝒪[L]`-linearly equivalent to
`𝒪[L] ⧸ 𝓂[L]^n`. -/
def dualQuotientMaximalIdealPowEquiv {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) ≃L[𝒪[L]]
      (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
  have : DiscreteTopology (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    Submodule.Quotient.discreteTopology_of_isOpen _ ((isAdic_maximalIdeal L).isOpen_pow n)
  ⟨(equivLinearMap 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) _).trans
      (((𝓂[L] ^ n : Ideal 𝒪[L]).quotientLinearMapEquivTorsionBySet _).trans
        (quotientMaximalIdealPowEquivTorsionBySet hϖ n).symm),
    continuous_of_discreteTopology, continuous_of_discreteTopology⟩

end SingleField

section Extension

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

/-- **Topological inverse-different trace comparison**: postcomposition with the trace map
`L ⧸ 𝒪[L]ᵛ → K ⧸ 𝒪[K]` gives a canonical continuous `𝒪[K]`-linear equivalence
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]ᵛ) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def traceDualPontryaginEquiv (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
  choose n b y hy hsum using exists_sum_trace_mul_smul_eq 𝒪[K] K (B := 𝒪[L]) (L := L)
  let DL := L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)
  let DK := K ⧸ (1 : Submodule 𝒪[K] K)
  let e := traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M
  let trCM : C(DL, DK) := ⟨traceDualQuotientMap 𝒪[K] K 𝒪[L] L, continuous_of_discreteTopology⟩
  let mulCM (i : Fin n) : C(DK, DL) :=
    ⟨mulByTraceDualQuotientMap 𝒪[K] K 𝒪[L] L (y i) (hy i), continuous_of_discreteTopology⟩
  let smulCM (i : Fin n) : C(M, M) := ⟨(b i • ·), continuous_const_smul (b i)⟩
  let toF : ModulePontryaginDual 𝒪[L] DL M → ModulePontryaginDual 𝒪[K] DK M := fun φ ↦
    ⟨⟨e φ.toContinuousLinearMap.toLinearMap, (trCM.continuous.comp (map_continuous φ)).congr fun m ↦
      (traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L _ m).symm⟩⟩
  let invF : ModulePontryaginDual 𝒪[K] DK M → ModulePontryaginDual 𝒪[L] DL M := fun ψ ↦
    ⟨⟨e.symm ψ.toContinuousLinearMap.toLinearMap,
      (continuous_finsetSum Finset.univ fun i _ ↦
        (mulCM i).continuous.comp ((map_continuous ψ).comp (smulCM i).continuous)).congr fun m ↦
          (traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum _ m).symm⟩⟩
  have hto :
      ModulePontryaginDual.toContinuousMap ∘ toF = fun φ ↦ trCM.comp φ.toContinuousMap := by
    ext φ m
    simp only [Function.comp_apply, toContinuousMap_apply, ContinuousMap.comp_apply]
    exact traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L φ.toContinuousLinearMap.toLinearMap m
  have hinv :
      ModulePontryaginDual.toContinuousMap ∘ invF =
        fun ψ ↦ ∑ i, (mulCM i).comp (ψ.toContinuousMap.comp (smulCM i)) := by
    ext ψ m
    simp only [Function.comp_apply, toContinuousMap_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.comp_apply]
    exact traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum _ m
  refine
    { toFun := toF, invFun := invF,
      left_inv := fun _ ↦ ext fun m ↦ LinearMap.congr_fun (e.symm_apply_apply _) m,
      right_inv := fun _ ↦ ext fun m ↦ LinearMap.congr_fun (e.apply_symm_apply _) m,
      map_add' := fun _ _ ↦ ext fun m ↦ LinearMap.congr_fun (e.map_add _ _) m,
      map_smul' := fun a _ ↦ ext fun m ↦ LinearMap.congr_fun (e.map_smul a _) m,
      continuous_toFun := by
        rw [isInducing_toContinuousMap.continuous_iff, hto]
        exact (ContinuousMap.continuous_postcomp trCM).comp continuous_toContinuousMap,
      continuous_invFun := by
        rw [isInducing_toContinuousMap.continuous_iff, hinv]
        exact continuous_finsetSum Finset.univ fun i _ ↦
          (ContinuousMap.continuous_postcomp (mulCM i)).comp
            ((ContinuousMap.continuous_precomp (smulCM i)).comp continuous_toContinuousMap) }

section TraceDualApply

variable {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
  [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]

@[simp] theorem traceDualPontryaginEquiv_apply
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) : traceDualPontryaginEquiv K L M φ m = traceDualQuotientMap 𝒪[K] K 𝒪[L] L (φ m) := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
  exact traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L _ m

/-- Compatibility of `traceDualPontryaginEquiv` with the `𝒪[L]`-action on `M`. -/
theorem traceDualPontryaginEquiv_smul_apply (b : 𝒪[L])
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) :
    traceDualPontryaginEquiv K L M (b • φ) m = traceDualPontryaginEquiv K L M φ (b • m) := by
  simp [traceDualPontryaginEquiv_apply, map_smul]

end TraceDualApply

/-- Compatibility of `traceDualPontryaginEquiv` with contragredient group representations. -/
theorem traceDualPontryaginEquiv_contragredient {G M : Type*} [Group G]
    [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul 𝒪[L] M]
    (ρ : ContRepresentation 𝒪[L] G M) (g : G)
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M) :
    traceDualPontryaginEquiv K L M
        (ρ.contragredient (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) g φ) =
      (ρ.restrictScalars 𝒪[K]).contragredient (K ⧸ (1 : Submodule 𝒪[K] K)) g
        (traceDualPontryaginEquiv K L M φ) := by
  ext m
  simp [traceDualPontryaginEquiv_apply, ContRepresentation.restrictScalars_apply]

section Uniformizer

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

/-- **Change of coefficient ring for local-field Pontryagin duals**: after choosing a uniformizer
`ϖ`, dividing by `ϖ ^ d(L/K)` and taking `Tr_{L/K}` yields
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def pontryaginDualEquivOfUniformizer (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M :=
  let e := (quotientEquivTraceDualQuotientOfUniformizer K L hϖ).pontryaginDualCongrCodomain (M := M)
  ContinuousLinearEquiv.trans
    ⟨e.toLinearEquiv.restrictScalars 𝒪[K], e.continuous, e.symm.continuous⟩
    (traceDualPontryaginEquiv K L M)

section UniformizerApply

variable {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
  [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]

@[simp] theorem pontryaginDualEquivOfUniformizer_apply
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) (m : M) :
    pontryaginDualEquivOfUniformizer K L hϖ M φ m =
      traceDualQuotientMap 𝒪[K] K 𝒪[L] L
        (quotientEquivTraceDualQuotientOfUniformizer K L hϖ (φ m)) := by
  dsimp only [pontryaginDualEquivOfUniformizer, ContinuousLinearEquiv.trans_apply]
  rw [traceDualPontryaginEquiv_apply]
  exact congrArg _
    ((quotientEquivTraceDualQuotientOfUniformizer K L hϖ).pontryaginDualCongrCodomain_apply
      (M := M) φ m)

/-- Compatibility of `pontryaginDualEquivOfUniformizer` with the `𝒪[L]`-action on `M`. -/
theorem pontryaginDualEquivOfUniformizer_smul_apply (b : 𝒪[L])
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) (m : M) :
    pontryaginDualEquivOfUniformizer K L hϖ M (b • φ) m =
      pontryaginDualEquivOfUniformizer K L hϖ M φ (b • m) := by
  simp [pontryaginDualEquivOfUniformizer_apply, map_smul]

end UniformizerApply

/-- Compatibility of `pontryaginDualEquivOfUniformizer` with contragredient group
representations. -/
theorem pontryaginDualEquivOfUniformizer_contragredient {G M : Type*} [Group G] [AddCommGroup M]
    [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul 𝒪[L] M] (ρ : ContRepresentation 𝒪[L] G M)
    (g : G) (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) :
    pontryaginDualEquivOfUniformizer K L hϖ M
        (ρ.contragredient (L ⧸ (1 : Submodule 𝒪[L] L)) g φ) =
      (ρ.restrictScalars 𝒪[K]).contragredient (K ⧸ (1 : Submodule 𝒪[K] K)) g
        (pontryaginDualEquivOfUniformizer K L hϖ M φ) := by
  ext m
  simp [pontryaginDualEquivOfUniformizer_apply, ContRepresentation.restrictScalars_apply]

end Uniformizer

end Extension

end TauCeti
