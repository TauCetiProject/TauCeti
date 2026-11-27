/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.Different.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.Topology.Algebra.Module.Quotient
import TauCeti.Topology.Algebra.ValuativeRel.Integer

/-!
# Different-dual and direct trace quotients for local fields

For a compatible finite separable extension `L / K` of nonarchimedean local fields, the inverse
different `𝒪[L]ᵛ` is an open `𝒪[L]`-submodule of `L` (`TauCeti.isOpen_traceDual_one`), so
`L ⧸ 𝒪[L]ᵛ` carries the discrete topology (`TauCeti.instDiscreteTopologyQuotientTraceDual`).
Given a uniformizer `ϖ` of `𝒪[L]`, dividing by `ϖ ^ d(L/K)` gives a continuous `𝒪[L]`-linear
equivalence `(L ⧸ 𝒪[L]) ≃L[𝒪[L]] (L ⧸ 𝒪[L]ᵛ)`
(`TauCeti.quotientEquivTraceDualQuotientOfUniformizer`).

By contrast, the naive pairing `directTracePairing : L ⧸ 𝒪[L] → Hom_𝒪[K](𝒪[L], K ⧸ 𝒪[K])` is
injective iff `L / K` is unramified (`TauCeti.ker_directTracePairing_eq_bot_iff_isUnramified`),
with `[ϖ⁻¹]` a nonzero kernel element whenever `L / K` is ramified
(`TauCeti.mk_inv_uniformizer_ne_zero` and `TauCeti.mk_inv_uniformizer_mem_ker_directTracePairing`).

## References

* J.-P. Serre, *Local Fields*, Chapter III, §§3 and 6.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

local instance : Module.Finite K L := finite_of_valuativeExtension K L
local instance : IsIntegralClosure 𝒪[L] 𝒪[K] L := isIntegralClosure_integerRing K L

variable (K L)

/-- The inverse different `𝒪[L]ᵛ` is an open `𝒪[L]`-submodule of `L`. -/
theorem isOpen_traceDual_one :
    IsOpen (Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L) : Set L) :=
  Submodule.isOpen_mono Submodule.one_le_traceDual_one (isOpen_one_submodule_integerRing L)

/-- The quotient `L ⧸ 𝒪[L]ᵛ` carries the discrete topology. -/
instance instDiscreteTopologyQuotientTraceDual :
    DiscreteTopology (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :=
  Submodule.Quotient.discreteTopology_of_isOpen _ (isOpen_traceDual_one K L)

variable [Algebra.IsSeparable K L]

/-- Given a uniformizer `ϖ` of `𝒪[L]`, dividing by `ϖ ^ d(L/K)` gives a continuous `𝒪[L]`-linear
equivalence `(L ⧸ 𝒪[L]) ≃L[𝒪[L]] (L ⧸ 𝒪[L]ᵛ)`. -/
def quotientEquivTraceDualQuotientOfUniformizer {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    (L ⧸ (1 : Submodule 𝒪[L] L)) ≃L[𝒪[L]]
      (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :=
  ⟨quotientEquivTraceDualQuotientOfDifferentIdealEqSpan 𝒪[K] K 𝒪[L] L
      (differentIdeal_eq_span_pow_uniformizer K L hϖ),
    continuous_of_discreteTopology, continuous_of_discreteTopology⟩

@[simp] theorem quotientEquivTraceDualQuotientOfUniformizer_mk {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    (x : L) :
    quotientEquivTraceDualQuotientOfUniformizer K L hϖ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x / ((ϖ : L) ^ differentExponent K L)) := by
  simp only [quotientEquivTraceDualQuotientOfUniformizer, ContinuousLinearEquiv.coe_mk,
    quotientEquivTraceDualQuotientOfDifferentIdealEqSpan_mk, map_pow,
    Algebra.algebraMap_ofSubsemiring_apply]

/-- **Exact criterion for the naive trace pairing**: `directTracePairing` is injective if and only
if `L / K` is unramified. -/
theorem ker_directTracePairing_eq_bot_iff_isUnramified :
    LinearMap.ker (directTracePairing 𝒪[K] K 𝒪[L] L) = ⊥ ↔ IsUnramified K L :=
  (ker_directTracePairing_eq_bot_iff_differentIdeal_eq_top 𝒪[K] K 𝒪[L] L).trans
    (differentIdeal_eq_top_iff K L)

/-- **Explicit witness in the kernel of the naive trace pairing**: whenever `L / K` is ramified
and `ϖ` is a uniformizer of `𝒪[L]`, `[ϖ⁻¹]` lies in `ker(directTracePairing 𝒪[K] K 𝒪[L] L)`. -/
theorem mk_inv_uniformizer_mem_ker_directTracePairing (hram : ¬ IsUnramified K L)
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    Submodule.Quotient.mk (p := (1 : Submodule 𝒪[L] L)) ((ϖ : L)⁻¹) ∈
      LinearMap.ker (directTracePairing 𝒪[K] K 𝒪[L] L) := by
  rw [mem_ker_directTracePairing_iff,
    mem_traceDual_one_iff_mul_of_differentIdeal_eq_span
      (differentIdeal_eq_span_pow_uniformizer K L hϖ)]
  have hd : 1 ≤ differentExponent K L :=
    Nat.one_le_iff_ne_zero.mpr (mt (differentExponent_eq_zero_iff K L).mp hram)
  have hpow : (ϖ : L) ^ differentExponent K L =
      (ϖ : L) * (ϖ : L) ^ (differentExponent K L - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  refine Submodule.mem_one.mpr ⟨ϖ ^ (differentExponent K L - 1), ?_⟩
  simp only [map_pow, Algebra.algebraMap_ofSubsemiring_apply]
  rw [hpow, inv_mul_cancel_left₀ (ZeroMemClass.coe_eq_zero.not.mpr hϖ.ne_zero)]

end TauCeti
