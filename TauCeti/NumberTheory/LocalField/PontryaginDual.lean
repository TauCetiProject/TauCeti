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

section
variable {L}

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

/-- Evaluating `(dualQuotientMaximalIdealPowEquiv hϖ n).symm [a]` at `[b]` gives
`[a * b / ϖ ^ n]`. -/
@[simp]
theorem dualQuotientMaximalIdealPowEquiv_symm_apply_mk {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    (n : ℕ) (a b : 𝒪[L]) :
    (dualQuotientMaximalIdealPowEquiv hϖ n).symm (Ideal.Quotient.mk (𝓂[L] ^ n) a)
        (Ideal.Quotient.mk (𝓂[L] ^ n) b) =
      Submodule.Quotient.mk ((a : L) * (b : L) / (ϖ : L) ^ n) := by
  have : DiscreteTopology (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    Submodule.Quotient.discreteTopology_of_isOpen _ ((isAdic_maximalIdeal L).isOpen_pow n)
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv]
  simp only [dualQuotientMaximalIdealPowEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, equivLinearMap_symm_apply,
    Ideal.quotientLinearMapEquivTorsionBySet_symm_apply_mk,
    quotientMaximalIdealPowEquivTorsionBySet_mk, ← Submodule.Quotient.mk_smul, Algebra.smul_def,
    Algebra.algebraMap_ofSubsemiring_apply]
  rw [mul_div_assoc', mul_comm (b : L) (a : L)]

/-- Evaluating `(dualQuotientMaximalIdealPowEquiv hϖ n).symm [a]` at `1` gives `[a / ϖ ^ n]`. -/
@[simp]
theorem dualQuotientMaximalIdealPowEquiv_symm_apply_one {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    (n : ℕ) (a : 𝒪[L]) :
    (dualQuotientMaximalIdealPowEquiv hϖ n).symm (Ideal.Quotient.mk (𝓂[L] ^ n) a) 1 =
      Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n) := by
  simpa using dualQuotientMaximalIdealPowEquiv_symm_apply_mk hϖ n a 1

/-- Evaluating `dualQuotientMaximalIdealPowEquiv hϖ n φ` under the torsion identification
`quotientMaximalIdealPowEquivTorsionBySet hϖ n` recovers `φ 1`. -/
@[simp]
theorem quotientMaximalIdealPowEquivTorsionBySet_dualQuotientMaximalIdealPowEquiv
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ)
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L))
      (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L]))) :
    (quotientMaximalIdealPowEquivTorsionBySet hϖ n
        (dualQuotientMaximalIdealPowEquiv hϖ n φ) : L ⧸ (1 : Submodule 𝒪[L] L)) = φ 1 := by
  have : DiscreteTopology (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    Submodule.Quotient.discreteTopology_of_isOpen _ ((isAdic_maximalIdeal L).isOpen_pow n)
  simp [dualQuotientMaximalIdealPowEquiv]

/-- `dualQuotientMaximalIdealPowEquiv hϖ n φ = [a]` if and only if `φ 1 = [a / ϖ ^ n]`. -/
theorem dualQuotientMaximalIdealPowEquiv_eq_mk_iff {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ)
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L))
      (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L]))) (a : 𝒪[L]) :
    dualQuotientMaximalIdealPowEquiv hϖ n φ = Ideal.Quotient.mk (𝓂[L] ^ n) a ↔
      φ 1 = Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n) := by
  rw [← quotientMaximalIdealPowEquivTorsionBySet_dualQuotientMaximalIdealPowEquiv hϖ n φ]
  refine ⟨fun h ↦ by rw [h, quotientMaximalIdealPowEquivTorsionBySet_mk], fun h ↦ ?_⟩
  rw [← quotientMaximalIdealPowEquivTorsionBySet_mk hϖ n a] at h
  exact (quotientMaximalIdealPowEquivTorsionBySet hϖ n).injective (Subtype.ext h)

end

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

local instance : Module.Finite K L := finite_of_valuativeExtension K L
local instance : IsIntegralClosure 𝒪[L] 𝒪[K] L := isIntegralClosure_integerRing K L

variable (K L)

/-- Postcomposition by `traceDualQuotientMap` on `C(M, L ⧸ 𝒪[L]ᵛ)`. -/
private def traceDualContinuousMap (M : Type*) [TopologicalSpace M] :
    C(M, L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) →
      C(M, K ⧸ (1 : Submodule 𝒪[K] K)) :=
  ContinuousMap.comp ⟨traceDualQuotientMap 𝒪[K] K 𝒪[L] L, continuous_of_discreteTopology⟩

omit [Algebra.IsSeparable K L] in
private theorem continuous_traceDualContinuousMap (M : Type*) [TopologicalSpace M] :
    Continuous (traceDualContinuousMap K L M) :=
  ContinuousMap.continuous_postcomp _

private theorem traceDualLinearMapEquiv_eq_traceDualContinuousMap (M : Type*) [AddCommGroup M]
    [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M]
    (φ : ModulePontryaginDual 𝒪[L]
      (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M) (m : M) :
    traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M φ.toContinuousLinearMap.toLinearMap m =
      traceDualContinuousMap K L M φ.toContinuousMap m := by
  simp [traceDualContinuousMap]

/-- Sum over a finite trace-dual family `(b, y)` on `C(M, K ⧸ 𝒪[K])`. -/
private def traceDualFamilyContinuousMap (M : Type*) [AddCommGroup M] [Module 𝒪[L] M]
    [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] {n : ℕ} (b : Fin n → 𝒪[L])
    (y : Fin n → L) (hy : ∀ i, y i ∈ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :
    C(M, K ⧸ (1 : Submodule 𝒪[K] K)) →
      C(M, L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :=
  fun g ↦ ∑ i,
    (⟨mulByTraceDualQuotientMap 𝒪[K] K 𝒪[L] L (y i) (hy i),
        continuous_of_discreteTopology⟩ :
      C(K ⧸ (1 : Submodule 𝒪[K] K),
        L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L))).comp
      (g.comp ⟨(b i • ·), continuous_const_smul (b i)⟩)

omit [Algebra.IsSeparable K L] in
private theorem continuous_traceDualFamilyContinuousMap (M : Type*) [AddCommGroup M]
    [Module 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] {n : ℕ}
    (b : Fin n → 𝒪[L]) (y : Fin n → L)
    (hy : ∀ i, y i ∈ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :
    Continuous (traceDualFamilyContinuousMap K L M b y hy) :=
  continuous_finsetSum Finset.univ fun _ _ ↦
    (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)

private theorem traceDualLinearMapEquiv_symm_eq_traceDualFamilyContinuousMap (M : Type*)
    [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
    [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] {n : ℕ} (b : Fin n → 𝒪[L])
    (y : Fin n → L) (hy : ∀ i, y i ∈ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L))
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap 𝒪[L] L (b i)) • y i = x)
    (ψ : ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M) (m : M) :
    (traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).symm ψ.toContinuousLinearMap.toLinearMap m =
      traceDualFamilyContinuousMap K L M b y hy ψ.toContinuousMap m := by
  simpa [traceDualFamilyContinuousMap] using
    traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum
      ψ.toContinuousLinearMap.toLinearMap m

/-- **Topological inverse-different trace comparison**: postcomposition with the trace map
`L ⧸ 𝒪[L]ᵛ → K ⧸ 𝒪[K]` gives a canonical continuous `𝒪[K]`-linear equivalence
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]ᵛ) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def traceDualPontryaginEquiv (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M :=
  let h := exists_sum_trace_mul_smul_eq 𝒪[K] K (B := 𝒪[L]) (L := L)
  let b := h.choose_spec.choose
  let y := h.choose_spec.choose_spec.choose
  have hy := h.choose_spec.choose_spec.choose_spec.1
  have hsum := h.choose_spec.choose_spec.choose_spec.2
  (traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).pontryaginDualEquiv
    (traceDualContinuousMap K L M)
    (continuous_traceDualContinuousMap K L M)
    (traceDualLinearMapEquiv_eq_traceDualContinuousMap K L M)
    (traceDualFamilyContinuousMap K L M b y hy)
    (continuous_traceDualFamilyContinuousMap K L M b y hy)
    (traceDualLinearMapEquiv_symm_eq_traceDualFamilyContinuousMap K L M b y hy hsum)

section TraceDualApply

variable {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
  [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]

@[simp] theorem traceDualPontryaginEquiv_apply
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) : traceDualPontryaginEquiv K L M φ m = traceDualQuotientMap 𝒪[K] K 𝒪[L] L (φ m) := by
  simp [traceDualPontryaginEquiv]

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
