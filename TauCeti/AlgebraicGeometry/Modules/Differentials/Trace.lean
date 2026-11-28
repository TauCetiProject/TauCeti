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

The trace does not depend on the separating function (`relativeDifferentialsTrace_eq`). For a
second separating function `t'`, the chain rule `dt = (dt/dt') dt'` shows that the class of
`(a_P dt)_P` is that of `((dt/dt') a_P dt')_P`, and that the Weil differential of `dt` is `dt/dt'`
times that of `dt'`. Hence `relativeDifferentialsResidueTrace`, the trace built from a chosen
separating function, is the residue trace `tr_{X/k}`, characterized by the residue formula for
every separating function.

The normalized duality theorem is separate from this construction; for line bundles it is
`InvertibleSheaf.bijective_residueTraceDualityHom` in
`TauCeti/AlgebraicGeometry/Modules/Differentials/SerreDuality.lean`.

## Main declarations

* `isGreatest_weilDifferentialFiltration_equivFunctionFieldDivisor`: the divisor `K` of `dt`
  is the largest divisor bounding the Weil differential `dt`;
* `relativeDifferentialsTrace`: the trace built from a separating function `t`;
* `relativeDifferentialsTrace_eq`: it does not depend on `t`;
* `relativeDifferentialsResidueTrace`: the residue trace `tr_{X/k}`, with
  `relativeDifferentialsResidueTrace_eq_finsum_residue`, the residue formula.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. École Norm. Sup. (4) 1 (1968),
  Sections 3–4.
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, Section 5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 4.3.2, for the chain
  rule behind the independence of the separating function.
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
/-- The divisor `K` of `dt` is the largest divisor bounding the Weil differential `dt`; in
particular `dt` is bounded by the divisor used in the sheaf comparison. -/
theorem isGreatest_weilDifferentialFiltration_equivFunctionFieldDivisor :
    IsGreatest {E : Divisor k X.functionField |
        (weilDifferentialOfSeparating hF ht : Module.Dual k (repartitionSpace k X.functionField)) ∈
          weilDifferentialFiltration E}
      (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim K) := by
  have he : K = (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
      (weilDifferentialDivisor hF hk (weilDifferentialOfSeparating hF ht).property
        (coe_weilDifferentialOfSeparating_ne_zero hF ht)) := by
    ext y
    simpa only [SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_symm,
      coeff_weilDifferentialDivisor] using hK y
  rw [he, (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).apply_symm_apply]
  exact isGreatest_weilDifferentialDivisor hF hk _ _

/-- The trace on `H¹(X, Ω_{X/k})` obtained from the Weil differential `dt` and its divisor.
The comparison with `𝒪_X(K)` transports the actual repartition linear form to cohomology. -/
def relativeDifferentialsTrace :
    Module.Dual k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 1) :=
  ((SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration hex hdim hF K).symm
    ⟨_, (isGreatest_weilDifferentialFiltration_equivFunctionFieldDivisor
      ht hF hk hex hdim K hK).1⟩).comp
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
        ⟨_, (isGreatest_weilDifferentialFiltration_equivFunctionFieldDivisor
          ht hF hk hex hdim K hK).1⟩) a).symm

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

section ChangeOfSeparatingFunction

variable {t' : X.functionField} (ht' : Transcendental k t')
  [Algebra.IsSeparable k⟮t'⟯ X.functionField] (K' : SchemeWeilDivisor X)
  (hK' : ∀ y : CodimensionOnePoint X, WeilDivisor.coeff K' y =
    weilDifferentialOrder hF hk (weilDifferentialOfSeparating hF ht').property
      (coe_weilDifferentialOfSeparating_ne_zero hF ht') (X.toPlace (k := k) (y : X)))

/-- **Change of separating function on differential repartitions.** The class of the repartition
`(a_P dt)_P` is the class of `((dt/dt') a_P dt')_P`, since `dt = (dt/dt') dt'`. -/
theorem repartitionToRelativeDifferentialsCohomologyOne_eq_repartitionMul
    (a : repartitionSpace k X.functionField) :
    repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a =
      repartitionToRelativeDifferentialsCohomologyOne ht' hF hk hex hdim K' hK'
        (repartitionMul hF (derivativeOfSeparating ht' t) a) := by
  obtain rfl := eq_sub_principalDivisor_derivativeOfSeparating ht hF hk K hK ht' K' hK'
  set g : Additive X.functionFieldˣ := Additive.ofMul (Units.mk0 (derivativeOfSeparating ht' t)
    (derivativeOfSeparating_ne_zero ht'))
  have hg : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      derivativeOfSeparating ht' t := by
    rw [toMul_ofMul, Units.val_mk0]
  -- Through `dt` and then `dt'`, the divisor sheaves are compared by multiplication by `dt/dt'`.
  have hφ : (relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK).inv ≫
      (relativeDifferentialsIsoDivisorSheaf ht' hF hk hdim _ hK').hom =
        SchemeWeilDivisor.sheafMul g K := by
    rw [← cancel_mono (SchemeWeilDivisor.sheafι _), Category.assoc,
      relativeDifferentialsIsoDivisorSheaf_inv_hom_sheafι, SchemeWeilDivisor.sheafMul_ι, hg]
  have hR := cohomologyMap_repartitionToRelativeDifferentialsCohomologyOne ht' hF hk hex hdim _ hK'
    (repartitionMul hF (derivativeOfSeparating ht' t) a)
  rw [← Scheme.Modules.coe_cohomologyMapBaseLinear k X] at hR
  apply (Scheme.Modules.cohomologyBaseLinearEquivOfIso k
    (relativeDifferentialsIsoDivisorSheaf ht' hF hk hdim _ hK') 1).injective
  -- Both sides are classes in `H¹(𝒪_X(K'))`; the right side is the image of the class of `a` in
  -- `H¹(𝒪_X(K))` under multiplication by `dt/dt'`, that is, under `H¹` of the comparison `hφ`.
  rw [Scheme.Modules.cohomologyBaseLinearEquivOfIso_apply,
    Scheme.Modules.cohomologyBaseLinearEquivOfIso_apply, hR, ← hg,
    ← SchemeWeilDivisor.repartitionToCohomologyOne_sheafMul hex hdim hF g K a, ← hφ,
    Scheme.Modules.cohomologyMapBaseLinear_comp]
  simp only [repartitionToRelativeDifferentialsCohomologyOne, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Scheme.Modules.cohomologyBaseLinearEquivOfIso_symm_apply]

/-- **The residue trace does not depend on the separating function**: the traces built from two
separating functions `t` and `t'` and the divisors of `dt` and `dt'` are equal. -/
theorem relativeDifferentialsTrace_eq :
    relativeDifferentialsTrace ht hF hk hex hdim K hK =
      relativeDifferentialsTrace ht' hF hk hex hdim K' hK' := by
  refine (relativeDifferentialsTrace_unique ht hF hk hex hdim K hK _ fun a ↦ ?_).symm
  let := weilDifferentialSpaceModule hF
  rw [repartitionToRelativeDifferentialsCohomologyOne_eq_repartitionMul ht hF hk hex hdim K hK
      ht' K' hK',
    relativeDifferentialsTrace_repartitionToRelativeDifferentialsCohomologyOne,
    weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul hF hk ht' ht,
    coe_weilDifferentialSpaceModule_smul, repartitionDualMul_apply_apply]

end ChangeOfSeparatingFunction

/-- The separating function from which `relativeDifferentialsResidueTrace` is built. -/
private def residueTraceSeparating : X.functionField :=
  (exists_transcendental_and_isSeparable_adjoin_of_isInvertible hF).choose

omit [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))] in
private lemma transcendental_residueTraceSeparating :
    Transcendental k (residueTraceSeparating hF) :=
  (exists_transcendental_and_isSeparable_adjoin_of_isInvertible hF).choose_spec.1

private instance isSeparable_residueTraceSeparating :
    Algebra.IsSeparable k⟮residueTraceSeparating hF⟯ X.functionField :=
  (exists_transcendental_and_isSeparable_adjoin_of_isInvertible hF).choose_spec.2

/-- The divisor of `dt` for the separating function `t = residueTraceSeparating hF`. -/
private def residueTraceDivisor : SchemeWeilDivisor X :=
  (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
    (weilDifferentialDivisor hF hk
      (weilDifferentialOfSeparating hF (transcendental_residueTraceSeparating hF)).property
      (coe_weilDifferentialOfSeparating_ne_zero hF (transcendental_residueTraceSeparating hF)))

omit [AlgebraicGeometry.IsNoetherian X] in
private lemma coeff_residueTraceDivisor (y : CodimensionOnePoint X) :
    WeilDivisor.coeff (residueTraceDivisor hF hk hex hdim) y =
      weilDifferentialOrder hF hk
        (weilDifferentialOfSeparating hF (transcendental_residueTraceSeparating hF)).property
        (coe_weilDifferentialOfSeparating_ne_zero hF (transcendental_residueTraceSeparating hF))
        (X.toPlace (k := k) (y : X)) := by
  simp only [residueTraceDivisor, SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_symm,
    coeff_weilDifferentialDivisor]

/-- **The residue trace** `tr_{X/k} : H¹(X, Ω_{X/k}) → k` of an integral curve over an exact
constant field, with invertible differentials and all the places of its function field: on the
class represented by a repartition of differentials `(η_P)_P` it is the sum over the places `P`
of the local components at `1` of the Weil differentials attached to the `η_P` (by Tate's theory,
these are the `k`-valued residues of the `η_P`). It is
`relativeDifferentialsTrace` for any separating function `t` and the divisor of `dt`
(`relativeDifferentialsResidueTrace_eq`); a separating function exists because the
differentials are invertible. -/
def relativeDifferentialsResidueTrace :
    Module.Dual k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 1) :=
  relativeDifferentialsTrace (transcendental_residueTraceSeparating hF) hF hk hex hdim
    (residueTraceDivisor hF hk hex hdim) (coeff_residueTraceDivisor hF hk hex hdim)

/-- The residue trace is the trace built from any separating function `t` and the divisor
of `dt`. -/
theorem relativeDifferentialsResidueTrace_eq :
    relativeDifferentialsResidueTrace hF hk hex hdim =
      relativeDifferentialsTrace ht hF hk hex hdim K hK :=
  relativeDifferentialsTrace_eq _ hF hk hex hdim _ _ ht K hK

/-- On the class of the repartition `(a_P dt)_P`, the residue trace is the Weil differential `dt`
evaluated on the coefficients `(a_P)_P`. -/
@[simp]
theorem relativeDifferentialsResidueTrace_repartitionToRelativeDifferentialsCohomologyOne
    (a : repartitionSpace k X.functionField) :
    relativeDifferentialsResidueTrace hF hk hex hdim
        (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a) =
      (weilDifferentialOfSeparating hF ht :
        Module.Dual k (repartitionSpace k X.functionField)) a := by
  rw [relativeDifferentialsResidueTrace_eq ht hF hk hex hdim K hK,
    relativeDifferentialsTrace_repartitionToRelativeDifferentialsCohomologyOne]

/-- **The residue formula.** On the class of the repartition of differentials `(a_P dt)_P`, the
residue trace is the sum over the places `P` of the local components at `1` of the Weil
differentials attached to `a_P dt` (by Tate's theory, the `k`-valued residues of `a_P dt`). -/
theorem relativeDifferentialsResidueTrace_eq_finsum_residue
    (a : repartitionSpace k X.functionField) :
    relativeDifferentialsResidueTrace hF hk hex hdim
        (repartitionToRelativeDifferentialsCohomologyOne ht hF hk hex hdim K hK a) =
      ∑ᶠ P : Place k X.functionField,
        repartitionDualComponent
          (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hk ht
            ((a : Place k X.functionField → X.functionField) P •
              KaehlerDifferential.D k X.functionField t)) P 1 := by
  rw [relativeDifferentialsResidueTrace_eq ht hF hk hex hdim K hK,
    relativeDifferentialsTrace_eq_finsum_residue]

/-- The residue trace is nonzero. -/
theorem relativeDifferentialsResidueTrace_ne_zero :
    relativeDifferentialsResidueTrace hF hk hex hdim ≠ 0 :=
  relativeDifferentialsTrace_ne_zero _ hF hk hex hdim _ _

end

end TauCeti.AlgebraicGeometry
