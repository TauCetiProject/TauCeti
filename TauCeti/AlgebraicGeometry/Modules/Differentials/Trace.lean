/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Canonical

/-!
# The residue trace on first cohomology of differentials

Let `X` be an integral Noetherian separated curve over an exact constant field `k`, with
discrete valuation rings at its codimension-one points, invertible relative differentials,
and all the places of its function field. A separating rational function `t` identifies
`Ω_{X/k}` with the sheaf of the divisor of `dt`. The Weil differential attached to `dt`
annihilates the kernel of the repartition map, and hence defines a linear form on
`H¹(X, Ω_{X/k})`.

`relativeDifferentialsTrace` is this linear form, with the separating function and its divisor
explicit. Its value on the class represented by `(a_P dt)_P` is the sum of the local
components of the Kähler–Weil differentials `a_P dt`, evaluated at `1`. These local components
of Weil differentials need no separability assumption on residue fields. Tate's residue
theory is the reference for their interpretation as residues; this file proves the
local-component formula.
The trace is nonzero and is uniquely determined by its values on repartition classes.

Independence of the separating function and the normalized duality theorem for arbitrary
quasi-coherent sheaves are separate from this construction.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. École Norm. Sup. (4) 1 (1968),
  Sections 3–4.
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, Section 5.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open scoped IntermediateField

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  {t : X.functionField} (ht : Transcendental k t)
  [Algebra.IsSeparable k⟮t⟯ X.functionField]
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)
  (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
  (hdim : ∀ y : X, coheight y ≤ 1) (K : SchemeWeilDivisor X)
  (hK : ∀ y : CodimensionOnePoint X, WeilDivisor.coeff K y =
    weilDifferentialOrder hF hk (weilDifferentialOfSeparating hF ht).property
      (coe_weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)))

include hK in
omit [AlgebraicGeometry.IsNoetherian X]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)] in
/-- The Weil differential `dt` is bounded by the divisor used in the sheaf comparison. -/
private lemma weilDifferentialOfSeparating_mem_canonicalFiltration :
    (weilDifferentialOfSeparating hF ht :
      Module.Dual k (repartitionSpace k X.functionField)) ∈
        weilDifferentialFiltration (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim K) := by
  have he : K = (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
      (weilDifferentialDivisor hF hk (weilDifferentialOfSeparating hF ht).property
        (coe_weilDifferentialOfSeparating_ne_zero hF ht)) := by
    ext y
    simpa only [SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_symm,
      coeff_weilDifferentialDivisor] using hK y
  rw [he, (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).apply_symm_apply]
  exact (isGreatest_weilDifferentialDivisor hF hk (weilDifferentialOfSeparating hF ht).property
    (coe_weilDifferentialOfSeparating_ne_zero hF ht)).1

/-- The trace on `H¹(X, Ω_{X/k})` obtained from the Weil differential `dt` and its divisor.
The comparison with `𝒪_X(K)` transports the actual repartition linear form to cohomology. -/
def relativeDifferentialsTrace :
    Module.Dual k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 1) :=
  ((SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration hex hdim hF K).symm
    ⟨_, weilDifferentialOfSeparating_mem_canonicalFiltration ht hF hk hex hdim K hK⟩).comp
    (Scheme.Modules.cohomologyBaseLinearEquivOfIso k
      (relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK) 1).toLinearMap

/-- The class of the repartition `(a_P dt)_P` in first cohomology of relative differentials. -/
def repartitionToRelativeDifferentialsCohomologyOne :
    repartitionSpace k X.functionField →ₗ[k]
      Scheme.Modules.Cohomology (X.relativeDifferentials k) 1 :=
  (Scheme.Modules.cohomologyBaseLinearEquivOfIso k
    (relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK) 1).symm.toLinearMap.comp
      (SchemeWeilDivisor.repartitionToCohomologyOne hex hdim K)

/-- The canonical-divisor comparison sends a differential-repartition class to the
corresponding divisor-sheaf cohomology class. -/
@[simp]
lemma cohomologyMap_repartitionToRelativeDifferentialsCohomologyOne
    (a : repartitionSpace k X.functionField) :
    Scheme.Modules.cohomologyMap
        (relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK).hom 1
        (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a) =
      SchemeWeilDivisor.repartitionToCohomologyOne hex hdim K a := by
  rw [← Scheme.Modules.coe_cohomologyMapBaseLinear k X,
    ← Scheme.Modules.cohomologyBaseLinearEquivOfIso_apply,
    repartitionToRelativeDifferentialsCohomologyOne, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- Every first cohomology class of relative differentials has a repartition representative
in the rational basis `dt`. -/
theorem repartitionToRelativeDifferentialsCohomologyOne_surjective :
    Function.Surjective
      (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK) :=
  (Scheme.Modules.cohomologyBaseLinearEquivOfIso k
    (relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK) 1).symm.surjective.comp
      (SchemeWeilDivisor.repartitionToCohomologyOne_surjective hex hdim K)

/-- On a repartition representative, the trace is the Weil differential `dt` evaluated on
its rational coefficients. -/
@[simp]
lemma relativeDifferentialsTrace_repartitionToRelativeDifferentialsCohomologyOne
    (a : repartitionSpace k X.functionField) :
    relativeDifferentialsTrace ht hF hk hex hdim K hK
        (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a) =
      (weilDifferentialOfSeparating hF ht :
        Module.Dual k (repartitionSpace k X.functionField)) a := by
  simp only [relativeDifferentialsTrace, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Scheme.Modules.cohomologyBaseLinearEquivOfIso_apply,
    Scheme.Modules.coe_cohomologyMapBaseLinear,
    cohomologyMap_repartitionToRelativeDifferentialsCohomologyOne]
  simpa only [LinearEquiv.apply_symm_apply] using
    (SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration_apply_apply
      hex hdim hF K
      ((SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration hex hdim hF K).symm
        ⟨_, weilDifferentialOfSeparating_mem_canonicalFiltration ht hF hk hex hdim K hK⟩) a).symm

/-- The trace is the sum of the local components of `dt` evaluated on the repartition
coefficients; these have finite support even when some residue fields are inseparable. -/
theorem relativeDifferentialsTrace_eq_finsum
    (a : repartitionSpace k X.functionField) :
    relativeDifferentialsTrace ht hF hk hex hdim K hK
        (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a) =
      ∑ᶠ P : Place k X.functionField,
        repartitionDualComponent (weilDifferentialOfSeparating hF ht) P
          ((a : Place k X.functionField → X.functionField) P) := by
  rw [relativeDifferentialsTrace_repartitionToRelativeDifferentialsCohomologyOne]
  exact apply_eq_finsum_repartitionDualComponent (weilDifferentialOfSeparating hF ht).property a

/-- The residue formula on differential repartitions: each summand is the local component
of the Weil differential attached to `a_P dt`, evaluated at `1`. -/
theorem relativeDifferentialsTrace_eq_finsum_residue
    (a : repartitionSpace k X.functionField) :
    relativeDifferentialsTrace ht hF hk hex hdim K hK
        (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a) =
      ∑ᶠ P : Place k X.functionField,
        repartitionDualComponent
          (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hk ht
            ((a : Place k X.functionField → X.functionField) P •
              KaehlerDifferential.D k X.functionField t)) P 1 := by
  let := weilDifferentialSpaceModule hF
  rw [relativeDifferentialsTrace_eq_finsum]
  congr 1
  funext P
  rw [map_smul, kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul, mul_one]

/-- The residue trace on first cohomology of relative differentials is nonzero. -/
theorem relativeDifferentialsTrace_ne_zero :
    relativeDifferentialsTrace ht hF hk hex hdim K hK ≠ 0 := by
  intro h
  apply coe_weilDifferentialOfSeparating_ne_zero hF ht
  ext a
  have ha :=
    relativeDifferentialsTrace_repartitionToRelativeDifferentialsCohomologyOne
      ht hF hk hex hdim K hK a
  simpa only [h, LinearMap.zero_apply] using ha.symm

/-- Values on differential repartitions uniquely determine the trace. -/
theorem relativeDifferentialsTrace_unique
    (φ : Module.Dual k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 1))
    (hφ : ∀ a : repartitionSpace k X.functionField,
      φ (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a) =
        (weilDifferentialOfSeparating hF ht :
          Module.Dual k (repartitionSpace k X.functionField)) a) :
    φ = relativeDifferentialsTrace ht hF hk hex hdim K hK := by
  ext c
  obtain ⟨a, rfl⟩ :=
    repartitionToRelativeDifferentialsCohomologyOne_surjective ht hF hk hex hdim K hK c
  rw [hφ, relativeDifferentialsTrace_repartitionToRelativeDifferentialsCohomologyOne]

end

end TauCeti.AlgebraicGeometry
