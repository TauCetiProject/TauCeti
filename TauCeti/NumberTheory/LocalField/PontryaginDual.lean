/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
public import TauCeti.NumberTheory.LocalField.Different.Quotient
public import TauCeti.NumberTheory.LocalField.IntegerRing.Quotient
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RepresentationTheory.Continuous.ModulePontryaginDual
public import TauCeti.RepresentationTheory.Continuous.TopRep.RestrictScalars
public import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology
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

/-- **Compactness of the dual of a discrete torsion `𝒪[L]`-module**: `Hom_𝒪[L](M, L ⧸ 𝒪[L])` is
a compact `𝒪[L]`-module whenever `M` is discrete and torsion. -/
theorem isCompactModule_dual_of_isTorsion {M : Type*} [AddCommGroup M] [Module 𝒪[L] M]
    [TopologicalSpace M] [DiscreteTopology M] (hM : Module.IsTorsion 𝒪[L] M) :
    IsCompactModule 𝒪[L] (ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) := by
  have := continuousSMul_iff_isTorsion.mpr hM
  exact isCompactModule_dual_of_discrete (length_linearMap_quotient_maximalIdeal_eq_one L)

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

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

local instance : Module.Finite K L := finite_of_valuativeExtension K L
local instance : IsIntegralClosure 𝒪[L] 𝒪[K] L := isIntegralClosure_integerRing K L

variable (K L)

/-- Transport a linear equivalence between linear maps to a continuous linear equivalence on
`ModulePontryaginDual`, given continuous-map realizations of both directions. -/
private def pontryaginDualEquivOfLinearEquiv {R₁ R₂ S E₁ E₂ M : Type*}
    [CommRing R₁] [CommRing R₂] [CommSemiring S]
    [AddCommGroup E₁] [Module R₁ E₁] [Module S E₁] [SMulCommClass R₁ S E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousConstSMul S E₁]
    [AddCommGroup E₂] [Module R₂ E₂] [Module S E₂] [SMulCommClass R₂ S E₂]
    [TopologicalSpace E₂] [IsTopologicalAddGroup E₂] [ContinuousConstSMul S E₂]
    [AddCommGroup M] [Module R₁ M] [Module R₂ M] [TopologicalSpace M]
    (e : (M →ₗ[R₁] E₁) ≃ₗ[S] (M →ₗ[R₂] E₂))
    (hto : ∃ F : C(M, E₁) → C(M, E₂), Continuous F ∧
      ∀ (φ : ModulePontryaginDual R₁ E₁ M) (m : M),
        e φ.toContinuousLinearMap.toLinearMap m = F φ.toContinuousMap m)
    (hinv : ∃ G : C(M, E₂) → C(M, E₁), Continuous G ∧
      ∀ (ψ : ModulePontryaginDual R₂ E₂ M) (m : M),
        e.symm ψ.toContinuousLinearMap.toLinearMap m = G ψ.toContinuousMap m) :
    ModulePontryaginDual R₁ E₁ M ≃L[S] ModulePontryaginDual R₂ E₂ M where
  toFun φ :=
    ⟨⟨e φ.toContinuousLinearMap.toLinearMap,
      (hto.choose φ.toContinuousMap).continuous.congr fun m ↦ (hto.choose_spec.2 φ m).symm⟩⟩
  invFun ψ :=
    ⟨⟨e.symm ψ.toContinuousLinearMap.toLinearMap,
      (hinv.choose ψ.toContinuousMap).continuous.congr fun m ↦ (hinv.choose_spec.2 ψ m).symm⟩⟩
  left_inv _ := ext fun m ↦ LinearMap.congr_fun (e.symm_apply_apply _) m
  right_inv _ := ext fun m ↦ LinearMap.congr_fun (e.apply_symm_apply _) m
  map_add' _ _ := ext fun m ↦ LinearMap.congr_fun (e.map_add _ _) m
  map_smul' a _ := ext fun m ↦ LinearMap.congr_fun (e.map_smul a _) m
  continuous_toFun := isInducing_toContinuousMap.continuous_iff.mpr <|
    (hto.choose_spec.1.comp continuous_toContinuousMap).congr fun φ ↦
      ContinuousMap.ext fun m ↦ by simp [hto.choose_spec.2 φ m]
  continuous_invFun := isInducing_toContinuousMap.continuous_iff.mpr <|
    (hinv.choose_spec.1.comp continuous_toContinuousMap).congr fun ψ ↦
      ContinuousMap.ext fun m ↦ by simp [hinv.choose_spec.2 ψ m]

/-- Postcomposition by `traceDualQuotientMap` realizes the forward direction of
`traceDualLinearMapEquiv` as a continuous map on `C(M, L ⧸ 𝒪[L]ᵛ)`. -/
private theorem exists_continuousMap_traceDualLinearMapEquiv (M : Type*) [AddCommGroup M]
    [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] :
    ∃ F : C(M, L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) →
        C(M, K ⧸ (1 : Submodule 𝒪[K] K)),
      Continuous F ∧
        ∀ (φ : ModulePontryaginDual 𝒪[L]
            (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M) (m : M),
          traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M φ.toContinuousLinearMap.toLinearMap m =
            F φ.toContinuousMap m := by
  let trCM : C(L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L),
      K ⧸ (1 : Submodule 𝒪[K] K)) :=
    ⟨traceDualQuotientMap 𝒪[K] K 𝒪[L] L, continuous_of_discreteTopology⟩
  exact ⟨fun g ↦ trCM.comp g, ContinuousMap.continuous_postcomp trCM, fun φ m ↦ by
    simp [trCM]⟩

/-- A finite trace-dual family realizes `(traceDualLinearMapEquiv).symm` as a continuous map on
`C(M, K ⧸ 𝒪[K])`. -/
private theorem exists_continuousMap_traceDualLinearMapEquiv_symm (M : Type*) [AddCommGroup M]
    [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M]
    [ContinuousConstSMul 𝒪[L] M] :
    ∃ G : C(M, K ⧸ (1 : Submodule 𝒪[K] K)) →
        C(M, L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)),
      Continuous G ∧
        ∀ (ψ : ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M) (m : M),
          (traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).symm ψ.toContinuousLinearMap.toLinearMap m =
            G ψ.toContinuousMap m := by
  obtain ⟨n, b, y, hy, hsum⟩ := exists_sum_trace_mul_smul_eq 𝒪[K] K (B := 𝒪[L]) (L := L)
  let mulCM (i : Fin n) :
      C(K ⧸ (1 : Submodule 𝒪[K] K), L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :=
    ⟨mulByTraceDualQuotientMap 𝒪[K] K 𝒪[L] L (y i) (hy i), continuous_of_discreteTopology⟩
  let smulCM (i : Fin n) : C(M, M) := ⟨(b i • ·), continuous_const_smul (b i)⟩
  refine ⟨fun g ↦ ∑ i, (mulCM i).comp (g.comp (smulCM i)),
    continuous_finsetSum Finset.univ fun i _ ↦
      (ContinuousMap.continuous_postcomp (mulCM i)).comp
        (ContinuousMap.continuous_precomp (smulCM i)),
    fun ψ m ↦ ?_⟩
  simpa [mulCM, smulCM] using
    traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum
      ψ.toContinuousLinearMap.toLinearMap m

/-- **Topological inverse-different trace comparison**: postcomposition with the trace map
`L ⧸ 𝒪[L]ᵛ → K ⧸ 𝒪[K]` gives a canonical continuous `𝒪[K]`-linear equivalence
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]ᵛ) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def traceDualPontryaginEquiv (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M :=
  pontryaginDualEquivOfLinearEquiv (traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M)
    (exists_continuousMap_traceDualLinearMapEquiv K L M)
    (exists_continuousMap_traceDualLinearMapEquiv_symm K L M)

section TraceDualApply

variable {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
  [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]

@[simp] theorem traceDualPontryaginEquiv_apply
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) : traceDualPontryaginEquiv K L M φ m = traceDualQuotientMap 𝒪[K] K 𝒪[L] L (φ m) :=
  traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L _ m

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
