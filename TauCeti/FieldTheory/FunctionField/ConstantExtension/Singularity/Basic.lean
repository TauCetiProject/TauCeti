/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.IntegralBasis
public import TauCeti.FieldTheory.FunctionField.Place.Extension.PurelyInseparable

/-!
# The local singularity degree of a constant field extension

For a place `P` of a field extension `F / k` and an algebraic constant extension `k' / k` inside
`F' = F · k'`, the `k'`-span `𝒪_P · k'` (`TauCeti.Place.constantSpanIntegers`) lies in the
integral closure `𝒪'_P` of `𝒪_P` in `F'` (`TauCeti.Place.integralClosureSubmodule`). When `F` and
`k'` are linearly disjoint over `k`, `𝒪_P · k' ≅ 𝒪_P ⊗_k k'` is the semilocal ring of the
base-changed curve along the fiber over `P`, and `𝒪'_P` is its normalization.

Their quotient `𝒪'_P ⧸ 𝒪_P · k'` (`TauCeti.Place.singularityQuotient`) measures the local
normalization defect at `P`, and its `k'`-dimension `δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P · k')` is the
**singularity degree** (`TauCeti.Place.singularityDegree`). When `F' / F` is purely inseparable,
there is a unique place `P'` over `P`, so `𝒪'_P = 𝒪_{P'}` and `𝒪_{P'} ⧸ P'.constantSpanSubmodule`
is `k`-linearly isomorphic to `P.singularityQuotient k' F'`.

## Main definitions

* `TauCeti.Place.singularityQuotient`: the quotient `𝒪'_P ⧸ 𝒪_P · k'`.
* `TauCeti.Place.singularityDegree`: its `k'`-dimension `δ_P`.
* `TauCeti.Place.singularityQuotientLinearEquiv`: when `F' / F` is purely inseparable,
  `𝒪_{P'} ⧸ 𝒪_P · k'` is `k`-linearly isomorphic to `P.singularityQuotient k' F'`.

## Main results

* `TauCeti.Place.singularityDegree_eq_zero_iff`: when `𝒪'_P ⧸ 𝒪_P · k'` is finite-dimensional,
  `δ_P = 0` exactly when `𝒪_P · k'` is integrally closed in `F'`.
* `TauCeti.Place.singularityQuotientLinearEquiv_mk`: action of `singularityQuotientLinearEquiv` on
  quotient representatives.

## References

* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
-/

public section

open Module

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

namespace Place

section Singularity

variable (k' F') (P : Place k F) [Algebra.IsIntegral k k']

/-- The quotient `𝒪'_P ⧸ 𝒪_P · k'`, which measures how far `𝒪_P ⊗_k k'` is from being integrally
closed in `F'`. -/
abbrev singularityQuotient : Type v' :=
  ↥(integralClosureSubmodule k' F' P) ⧸
    (constantSpanIntegers k' F' P).submoduleOf (integralClosureSubmodule k' F' P)

/-- The **singularity degree** `δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P · k')` of `P` in `F' = F · k'`: the
total `k'`-dimensional normalization defect along the fiber over `P` of the curve of `F / k` after
extending the constants to `k'`. The fiber may consist of several points, and `δ_P` sums their
contributions. -/
noncomputable def singularityDegree : ℕ :=
  finrank k' (singularityQuotient k' F' P)

theorem singularityDegree_def :
    singularityDegree k' F' P = finrank k' (singularityQuotient k' F' P) :=
  (rfl)

/-- **A place has singularity degree zero exactly when `𝒪_P · k'` is integrally closed**: when
`𝒪'_P ⧸ 𝒪_P · k'` is finite-dimensional, `δ_P = 0` if and only if `𝒪_P ⊗_k k'` is the integral
closure of `𝒪_P` in `F'`. -/
theorem singularityDegree_eq_zero_iff [FiniteDimensional k' (singularityQuotient k' F' P)] :
    singularityDegree k' F' P = 0 ↔
      constantSpanIntegers k' F' P = integralClosureSubmodule k' F' P := by
  rw [singularityDegree_def, Module.finrank_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.submoduleOf_eq_top]
  exact ⟨fun hle ↦ le_antisymm (constantSpanIntegers_le_integralClosureSubmodule k' F' P) hle,
    fun heq ↦ heq.ge⟩

end Singularity

variable (k F) in
/-- When `F' / F` is purely inseparable, `P'` is the unique place over `P = P'|_F`, so `𝒪'_P`
coincides with `𝒪_{P'}` and `P'.integers ⧸ P'.constantSpanSubmodule k F` is `k`-linearly isomorphic
to `P.singularityQuotient k' F'`. -/
noncomputable def singularityQuotientLinearEquiv [Algebra.IsIntegral k k']
    [IsPurelyInseparable F F'] (hF' : IsFunctionField k' F') (P' : Place k' F') :
    letI := Place.integersAlgebraBase k P'
    haveI := Place.isScalarTower_integersAlgebraBase k P'
    haveI := Place.isScalarTower_integers_restrict k F P'
    (P'.integers ⧸ P'.constantSpanSubmodule k F) ≃ₗ[k]
      (P'.restrict k F).singularityQuotient k' F' :=
  letI := Place.integersAlgebraBase k P'
  haveI := Place.isScalarTower_integersAlgebraBase k P'
  haveI := Place.isScalarTower_integers_restrict k F P'
  let P := P'.restrict k F
  have : IsIntegralClosure P'.integers P.integers F' := Place.isIntegralClosure_integers hF' P'
  let e := IsIntegralClosure.equiv P.integers P'.integers F' (integralClosure P.integers F')
  have he (z : P'.integers) : ((e z : integralClosure P.integers F') : F') = (z : F') :=
    IsIntegralClosure.algebraMap_equiv P.integers P'.integers F' (integralClosure P.integers F') z
  let toIC (z : F') (hz : z ∈ P.integralClosureSubmodule k' F') : integralClosure P.integers F' :=
    ⟨z, (mem_integralClosure_iff P.integers F').2 ((P.mem_integralClosureSubmodule_iff k' F').1 hz)⟩
  let eTop : P'.integers ≃ₗ[k] ↥(P.integralClosureSubmodule k' F') :=
    { toFun := fun x ↦ ⟨((e x : integralClosure P.integers F') : F'),
        (P.mem_integralClosureSubmodule_iff k' F').2
          ((mem_integralClosure_iff P.integers F').1 (e x).property)⟩
      invFun := fun y ↦ e.symm (toIC y.val y.property)
      left_inv := fun x ↦ by simp [e, toIC]
      right_inv := fun y ↦ Subtype.ext <| by simp [toIC]
      map_add' := fun x y ↦ Subtype.ext <| by simp
      map_smul' := fun c x ↦ Subtype.ext <| by
        rw [RingHom.id_apply, Submodule.coe_smul_of_tower, he, Algebra.smul_def, Algebra.smul_def,
          Subring.coe_mul, IsScalarTower.algebraMap_apply k k' P'.integers,
          Place.coe_algebraMap_constants, ← IsScalarTower.algebraMap_apply k k' F', he] }
  ((Submodule.Quotient.restrictScalarsEquiv k (P'.constantSpanSubmodule k F)).symm.trans
    (Submodule.Quotient.equiv ((P'.constantSpanSubmodule k F).restrictScalars k)
      (((P.constantSpanIntegers k' F').submoduleOf
        (P.integralClosureSubmodule k' F')).restrictScalars k) eTop (by
        ext ⟨z, hz⟩
        simp only [Submodule.mem_map, Submodule.restrictScalars_mem,
          Place.mem_constantSpanSubmodule_iff, eTop]
        refine ⟨fun ⟨x, hx, hxz⟩ ↦ ?_, fun hz' ↦ ⟨e.symm (toIC z hz), ?_, Subtype.ext ?_⟩⟩
        · have hxz' : (x : F') = z := by simpa [he] using congrArg Subtype.val hxz
          exact hxz' ▸ hx
        · have hz_eq : ((e.symm (toIC z hz) : P'.integers) : F') = z := by
            simp [← he, toIC]
          rwa [hz_eq]
        · simp [toIC]))).trans
    (Submodule.Quotient.restrictScalarsEquiv k _)

/-- `Place.singularityQuotientLinearEquiv` sends the class of `x : P'.integers` to the class of
the same ambient element `(x : F')` in `(P'.restrict k F).integralClosureSubmodule k' F'`. -/
@[simp]
theorem singularityQuotientLinearEquiv_mk [Algebra.IsIntegral k k']
    [IsPurelyInseparable F F'] (hF' : IsFunctionField k' F') (P' : Place k' F')
    (x : P'.integers) :
    P'.singularityQuotientLinearEquiv k F hF' (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(x : F'),
        ((P'.restrict k F).mem_integralClosureSubmodule_iff k' F').2
          ((Place.isIntegral_integers_restrict_iff hF' P').2 x.property)⟩ := by
  let _ := Place.integersAlgebraBase k P'
  have := Place.isScalarTower_integersAlgebraBase k P'
  have := Place.isScalarTower_integers_restrict k F P'
  have : IsIntegralClosure P'.integers (P'.restrict k F).integers F' :=
    Place.isIntegralClosure_integers hF' P'
  have he : ((IsIntegralClosure.equiv (P'.restrict k F).integers P'.integers F'
      (integralClosure (P'.restrict k F).integers F') x :
      integralClosure (P'.restrict k F).integers F') : F') = (x : F') :=
    IsIntegralClosure.algebraMap_equiv (P'.restrict k F).integers P'.integers F'
      (integralClosure (P'.restrict k F).integers F') x
  simp [singularityQuotientLinearEquiv, he]

end Place

end TauCeti
