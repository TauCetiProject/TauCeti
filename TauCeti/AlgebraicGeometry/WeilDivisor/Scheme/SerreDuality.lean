/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.RepartitionCohomology
public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor

/-!
# Serre duality for divisor sheaves on a curve

Let `X` be an integral separated Noetherian curve over a field `k` whose codimension-one local
rings are discrete valuation rings and whose structure morphism satisfies the existence part of
the valuative criterion (a proper curve, for instance), so that its codimension-one points are the
places of the function field `k(X)`. This file identifies the cohomology of the sheaves
`𝒪_X(D)` with the function-field objects of Weil's theory of repartitions and differentials, and
when `k` is integrally closed in `k(X)` (`IsIntegrallyClosedIn k X.functionField`), deduces
**Serre duality** in the form

`H¹(X, 𝒪_X(D))^∨ ≃ H⁰(X, 𝒪_X(K - D))`,

for `K` a canonical divisor, that is, a divisor whose class in the function field is the
canonical class of Weil differentials.

The two halves are:

* `H⁰(X, 𝒪_X(D)) = L(D)`: a global section of `𝒪_X(D)` is a rational function whose order at
  every codimension-one point `x` is at least `-D(x)`, which is exactly membership in the
  Riemann–Roch space of the corresponding function-field divisor;
* `H¹(X, 𝒪_X(D))^∨ = Ω(D)`: first cohomology is the repartition quotient
  `A_{k(X)} / (A_{k(X)}(D) + k(X))`, and the Weil differentials bounded by `D` are by definition
  the linear forms on the repartitions that vanish on `A_{k(X)}(D) + k(X)`.

Combined with the function-field duality `L(W - D) ≃ Ω(D)`, `x ↦ x · ω`, for `W` the divisor of a
nonzero Weil differential `ω`, this is Serre duality. The pairing is explicit: a section `f` of
`𝒪_X(K - D)` pairs with the class of a repartition `a` to `ω(f · a)`.

Under the same constant-field hypothesis, taking `D = 0` computes the genus:
`dim_k H¹(X, 𝒪_X)` is the genus of the function field, and a canonical divisor has degree
`2g - 2`.

## Main declarations

* `SchemeWeilDivisor.globalSectionsEquivRiemannRochSpace`: `Γ(X, 𝒪_X(D)) ≃ L(D)`;
* `SchemeWeilDivisor.finrank_cohomology_zero_sheaf_eq_dim`: `dim_k H⁰(X, 𝒪_X(D)) = ℓ(D)`;
* `SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration`:
  `H¹(X, 𝒪_X(D))^∨ ≃ Ω(D)`;
* `SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero`: **Serre duality**,
  `H¹(X, 𝒪_X(D))^∨ ≃ H⁰(X, 𝒪_X(K - D))`, with the pairing
  `SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne`;
* `SchemeWeilDivisor.finrank_cohomology_one_sheaf_eq_finrank_cohomology_zero_sheaf_sub`:
  `dim_k H¹(X, 𝒪_X(D)) = dim_k H⁰(X, 𝒪_X(K - D))` for every canonical divisor `K`;
* `SchemeWeilDivisor.genus_eq_genus_functionField`: the genus `dim_k H¹(X, 𝒪_X)` of `X` is the
  genus of its function field;
* `SchemeWeilDivisor.relativeDegree_eq_two_mul_genus_sub_two`: a canonical divisor has degree
  `2g - 2`.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II (repartitions and the duality
  theorem).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5, in particular Theorem 1.5.14.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, Corollary 7.7, and Chapter IV, Section 1.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [X.IsSeparated]
  (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
  (hdim : ∀ x : X, coheight x ≤ 1)

/-- The top open of an integral scheme is nonempty. -/
local instance nonemptyTopOpensSerreDuality : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice inferInstance, trivial⟩⟩

/-! ### Global sections and Riemann–Roch spaces -/

section GlobalSections

variable [IsLocallyNoetherian X]

/-- A rational function is a global section of `𝒪_X(D)` exactly when it lies in the Riemann–Roch
space of the corresponding function-field divisor. -/
theorem rationalFunctionsEquiv_symm_mem_sections_top_iff (D : SchemeWeilDivisor X)
    (f : X.functionField) :
    (Scheme.rationalFunctionsEquiv ⊤).symm f ∈ sections D ⊤ ↔
      f ∈ riemannRochSpace (equivFunctionFieldDivisor hex hdim D) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [map_zero, Submodule.zero_mem]
  rw [mem_sections_iff, LinearEquiv.apply_symm_apply, mem_riemannRochSpace_iff_neg_le_ord hf,
    ← (CodimensionOnePoint.equivPlace (k := k) hex hdim).forall_congr_right]
  simp only [hf, false_or, TopologicalSpace.Opens.mem_top, forall_const,
    CodimensionOnePoint.equivPlace_apply, coeff_equivFunctionFieldDivisor_toPlace,
    CodimensionOnePoint.toPlace_ord]

/-- **Global sections of `𝒪_X(D)` form the Riemann–Roch space `L(D)`.** A global section of the
sheaf of a Weil divisor `D` is a rational function `f` with `ord_x f ≥ -D(x)` at every
codimension-one point `x`, and the map to the function field identifies these with the
Riemann–Roch space of the function-field divisor corresponding to `D`. -/
def globalSectionsEquivRiemannRochSpace (D : SchemeWeilDivisor X) :
    Γ(sheaf D, ⊤) ≃ₗ[k] riemannRochSpace (equivFunctionFieldDivisor hex hdim D) :=
  let ι : Γ(sheaf D, ⊤) →ₗ[k] X.functionField :=
    (Scheme.globalRationalFunctionsEquivFunctionField (k := k) (X := X)).toLinearMap ∘ₗ
      { toFun := (sheafι D).app ⊤
        map_add' := map_add _
        map_smul' c s := by
          rw [Scheme.Modules.base_smul_globalSections, Scheme.Modules.Hom.app_smul,
            Scheme.Modules.base_smul_globalSections, RingHom.id_apply] }
  have hι : Function.Injective ι :=
    (Scheme.globalRationalFunctionsEquivFunctionField (k := k) (X := X)).injective.comp
      (sheafι_app_injective D ⊤)
  have hrange : LinearMap.range ι = riemannRochSpace (equivFunctionFieldDivisor hex hdim D) := by
    ext f
    rw [LinearMap.mem_range, ← rationalFunctionsEquiv_symm_mem_sections_top_iff hex hdim,
      ← SetLike.mem_coe, ← range_sheafι_app D ⊤, Set.mem_range]
    refine exists_congr fun s ↦ ?_
    simp only [ι, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearEquiv.coe_coe, Scheme.globalRationalFunctionsEquivFunctionField_apply,
      LinearEquiv.eq_symm_apply]
  (LinearEquiv.ofInjective ι hι).trans (LinearEquiv.ofEq _ _ hrange)

/-- The Riemann–Roch space element attached to a global section of `𝒪_X(D)` is its underlying
rational function. -/
@[simp]
lemma coe_globalSectionsEquivRiemannRochSpace_apply (D : SchemeWeilDivisor X)
    (s : Γ(sheaf D, ⊤)) :
    (globalSectionsEquivRiemannRochSpace hex hdim D s : X.functionField) =
      Scheme.rationalFunctionsEquiv ⊤ ((sheafι D).app ⊤ s) := by
  simp [globalSectionsEquivRiemannRochSpace]

/-- **`dim_k H⁰(X, 𝒪_X(D)) = ℓ(D)`**: the dimension of the zeroth cohomology of `𝒪_X(D)` is the
dimension of the Riemann–Roch space of the corresponding function-field divisor. -/
theorem finrank_cohomology_zero_sheaf_eq_dim (D : SchemeWeilDivisor X) :
    finrank k (Scheme.Modules.Cohomology (sheaf D) 0) =
      Divisor.dim (equivFunctionFieldDivisor hex hdim D) := by
  rw [Divisor.dim_def]
  exact ((Scheme.Modules.cohomologyZeroBaseLinearEquiv k X (sheaf D)).trans
    (globalSectionsEquivRiemannRochSpace hex hdim D)).finrank_eq

end GlobalSections

/-! ### First cohomology and Weil differentials -/

section Duality

variable [IsNoetherian X] (hF : IsFunctionField k X.functionField)

/-- **The dual of `H¹(X, 𝒪_X(D))` is the space `Ω(D)` of Weil differentials bounded by `D`.**
First cohomology is the repartition quotient `A_{k(X)} / (A_{k(X)}(D) + k(X))`, whose linear
forms are the linear forms on repartitions vanishing on `A_{k(X)}(D) + k(X)`. -/
def cohomologyOneDualEquivWeilDifferentialFiltration (D : SchemeWeilDivisor X) :
    Module.Dual k (Scheme.Modules.Cohomology (sheaf D) 1) ≃ₗ[k]
      weilDifferentialFiltration (equivFunctionFieldDivisor hex hdim D) :=
  (repartitionQuotientEquivCohomologyOne hex hdim hF D).dualMap.trans <|
    (Submodule.dualQuotEquivDualAnnihilator _).trans <|
      LinearEquiv.ofEq _ _ (weilDifferentialFiltration_eq_dualAnnihilator _).symm

/-- The Weil differential attached to a linear form `φ` on `H¹(X, 𝒪_X(D))` evaluates a
repartition by applying `φ` to its cohomology class. -/
@[simp]
lemma cohomologyOneDualEquivWeilDifferentialFiltration_apply_apply (D : SchemeWeilDivisor X)
    (φ : Module.Dual k (Scheme.Modules.Cohomology (sheaf D) 1))
    (a : repartitionSpace k X.functionField) :
    (cohomologyOneDualEquivWeilDifferentialFiltration hex hdim hF D φ :
        Module.Dual k (repartitionSpace k X.functionField)) a =
      φ (repartitionToCohomologyOne hex hdim D a) := by
  rw [cohomologyOneDualEquivWeilDifferentialFiltration, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  -- The left-hand side is `φ` applied to the class of `a` under the repartition-quotient
  -- equivalence, by `Submodule.dualQuotEquivDualAnnihilator_apply` and
  -- `LinearEquiv.dualMap_apply`, both of which hold by `rfl`; rewriting with them fails because
  -- the instances on the quotient are only unfolded at default transparency.
  exact congrArg φ (repartitionQuotientEquivCohomologyOne_mk hex hdim hF D a)

variable (hk : IsIntegrallyClosedIn k X.functionField)
  {ω : Module.Dual k (repartitionSpace k X.functionField)} (hω : ω ≠ 0) {K : SchemeWeilDivisor X}
  (hK : IsGreatest {E : Divisor k X.functionField | ω ∈ weilDifferentialFiltration E}
    (equivFunctionFieldDivisor hex hdim K))

/-- **Serre duality for divisor sheaves on a curve with `k` integrally closed in `k(X)`.**
Let `ω` be a nonzero Weil differential of the function field and `K` the divisor on `X`
corresponding to its divisor `(ω)`. For every Weil divisor `D`, the dual of `H¹(X, 𝒪_X(D))` is
`H⁰(X, 𝒪_X(K - D))`; a section `f` pairs with the
class of a repartition `a` to `ω(f · a)`
(`SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne`).
-/
def cohomologyOneDualEquivCohomologyZero (D : SchemeWeilDivisor X) :
    Module.Dual k (Scheme.Modules.Cohomology (sheaf D) 1) ≃ₗ[k]
      Scheme.Modules.Cohomology (sheaf (K - D)) 0 :=
  (cohomologyOneDualEquivWeilDifferentialFiltration hex hdim hF D).trans <|
    (riemannRochSpaceEquivWeilDifferentialFiltration hF hk hω hK _).symm.trans <|
      (LinearEquiv.ofEq _ _ (by rw [map_sub])).trans <|
        (globalSectionsEquivRiemannRochSpace hex hdim (K - D)).symm.trans
          (Scheme.Modules.cohomologyZeroBaseLinearEquiv k X (sheaf (K - D))).symm

/-- **The Serre duality pairing.** Under `SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero`,
a section `s` of `𝒪_X(K - D)`, with underlying rational function `f`, is the linear form on
`H¹(X, 𝒪_X(D))` sending the class of a repartition `a` to `ω(f · a)`.

Not `@[simp]`: `SchemeWeilDivisor.repartitionToCohomologyOne_apply` already rewrites the class of a
repartition on the left-hand side, so this rule would not be in simp-normal form. -/
lemma cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne
    (D : SchemeWeilDivisor X) (s : Scheme.Modules.Cohomology (sheaf (K - D)) 0)
    (a : repartitionSpace k X.functionField) :
    (cohomologyOneDualEquivCohomologyZero hex hdim hF hk hω hK D).symm s
        (repartitionToCohomologyOne hex hdim D a) =
      ω (repartitionMul hF (Scheme.rationalFunctionsEquiv ⊤
        ((sheafι (K - D)).app ⊤ (Scheme.Modules.cohomologyZeroEquiv _ s))) a) := by
  rw [← cohomologyOneDualEquivWeilDifferentialFiltration_apply_apply hex hdim hF]
  simp [cohomologyOneDualEquivCohomologyZero, repartitionDualMul_apply_apply]

end Duality

/-! ### Dimensions, the genus and the canonical degree -/

section Dimension

variable [IsNoetherian X] (hF : IsFunctionField k X.functionField)
  (hk : IsIntegrallyClosedIn k X.functionField)

/-- **Serre duality, in dimensions.** Assume `k` is integrally closed in `k(X)`. For every
canonical divisor `K` on the curve `X` (a divisor whose function-field divisor represents the
canonical class) and every Weil divisor `D`,
`dim_k H¹(X, 𝒪_X(D)) = dim_k H⁰(X, 𝒪_X(K - D))`. -/
theorem finrank_cohomology_one_sheaf_eq_finrank_cohomology_zero_sheaf_sub
    {K : SchemeWeilDivisor X}
    (hK : (Place.orderSystem hF).divisorClass (equivFunctionFieldDivisor hex hdim K) =
      canonicalClass hF hk)
    (D : SchemeWeilDivisor X) :
    finrank k (Scheme.Modules.Cohomology (sheaf D) 1) =
      finrank k (Scheme.Modules.Cohomology (sheaf (K - D)) 0) := by
  obtain ⟨ω, -, hω, hW⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass hF hk hK
  have := finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim hF D
  rw [← Subspace.dual_finrank_eq]
  exact (cohomologyOneDualEquivCohomologyZero hex hdim hF hk hω hW D).finrank_eq

include hex hdim hF hk in
/-- When `k` is integrally closed in `k(X)`, the first cohomology of `𝒪_X(0)` has dimension the
genus of the function field: its dual is the space of regular Weil differentials. -/
theorem finrank_cohomology_one_sheaf_zero_eq_genus :
    finrank k (Scheme.Modules.Cohomology (sheaf (0 : SchemeWeilDivisor X)) 1) =
      genus k X.functionField := by
  have := finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim hF 0
  rw [← Subspace.dual_finrank_eq,
    (cohomologyOneDualEquivWeilDifferentialFiltration hex hdim hF 0).finrank_eq, map_zero,
    finrank_weilDifferentialFiltration_zero hF hk]

variable [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

include hex hdim hF hk in
/-- **The genus of a curve is the genus of its function field when `k` is integrally closed in
`k(X)`.** The genus `dim_k H¹(X, 𝒪_X)` of `X` agrees with the genus of `k(X)` defined through
Riemann's theorem. -/
theorem genus_eq_genus_functionField :
    X.genus k = genus k X.functionField := by
  rw [Scheme.genus_def, ← Scheme.Modules.finrank_cohomology_congr k (sheafZeroIsoTrivial hdim) 1]
  exact finrank_cohomology_one_sheaf_zero_eq_genus hex hdim hF hk

/-- **A canonical divisor has degree `2g - 2` when `k` is integrally closed in `k(X)`.** Every
divisor `K` on `X` whose function-field divisor represents the canonical class has degree
`2g - 2`, where `g = dim_k H¹(X, 𝒪_X)` is the genus of `X`. -/
theorem relativeDegree_eq_two_mul_genus_sub_two {K : SchemeWeilDivisor X}
    (hK : (Place.orderSystem hF).divisorClass (equivFunctionFieldDivisor hex hdim K) =
      canonicalClass hF hk) :
    relativeDegree (X ↘ Spec (.of k)) K = 2 * X.genus k - 2 := by
  rw [genus_eq_genus_functionField hex hdim hF hk,
    ← degree_equivFunctionFieldDivisor hex hdim]
  exact ((divisorClass_eq_canonicalClass_iff hF hk _).mp hK).1

end Dimension

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
