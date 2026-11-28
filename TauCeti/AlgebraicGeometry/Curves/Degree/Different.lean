/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Degree.RiemannHurwitz
public import TauCeti.AlgebraicGeometry.Curves.Smooth
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Scheme.Place.Hom
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.FunctionField
public import TauCeti.FieldTheory.FunctionField.Different.Divisor
import TauCeti.AlgebraicGeometry.CartierDivisor.WeilComparison
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
import TauCeti.FieldTheory.FunctionField.Different.Kaehler
import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.RingTheory.FittingIdeal.Semilinear
import TauCeti.RingTheory.Kaehler.MapSemilinear

/-!
# The Cartier ramification divisor and the trace-dual different on curves

Let `f : X ⟶ Y` be a dominant morphism of integral curves over a field `k` with finite separable
function-field extension `k(X) / k(Y)` along `f^*`. At every point `x : X` where both `𝒪_{X,x}`
and `𝒪_{Y,f x}` are discrete valuation rings and the residue extension `κ(x) / κ(f x)` is
separable, identifying the local rings with the valuation rings of the corresponding places
`P_x` and `P_{f x} = P_x|_{k(Y)}` transports the Kähler different formula
(`TauCeti.Place.fittingIdeal_kaehlerDifferential_integers_eq_maximalIdeal_pow`) to the stalk of
the ramification ideal sheaf:

`(ramificationIdealSheaf k f).stalkIdeal x = 𝔪_x ^ d(P_x ∣ P_{f x})`

(`ramificationIdealSheaf_stalkIdeal_eq_maximalIdeal_pow_differentExponent`). Consequently, when
`Ω_{X/k}` and `Ω_{Y/k}` are invertible, the Cartier ramification divisor `ramificationCartierDivisor
k f` has order `d(P_x ∣ P_{f x})` at `x`
(`orderAt_ramificationCartierDivisor_eq_differentExponent`).

When every codimension-one point of `X` satisfies this separable-residue condition (in particular
automatically when `k` is a perfect field and `X`, `Y` are regular proper curves over `k`), the
associated Weil divisor `(ramificationCartierDivisor k f).toWeilDivisor` corresponds under
`SchemeWeilDivisor.equivFunctionFieldDivisor` to the trace-dual different divisor
`Divisor.different k X.functionField`
(`equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor`), and its subscheme rank
`dim_k Γ(R_f, 𝒪_{R_f})` equals `deg Diff(k(X)/k(Y))`, specializing the scheme-theoretic
Riemann–Hurwitz formula to `deg Ω_{X/k} = [k(X) : k(Y)] · deg Ω_{Y/k} + deg Diff`.

## Main results

* `ramificationIdealSheaf_stalkIdeal_eq_maximalIdeal_pow_differentExponent`:
  `(ramificationIdealSheaf k f).stalkIdeal x = 𝔪_x ^ d(P_x ∣ P_{f x})`.
* `orderAt_ramificationCartierDivisor_eq_differentExponent`:
  `(ramificationCartierDivisor k f).orderAt x = d(P_x ∣ P_{f x})`.
* `equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor`:
  the Weil divisor of `ramificationCartierDivisor k f` matches `Divisor.different` on the
  separable-residue branch.
* `equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor_of_perfectField`:
  automatic specialization to regular proper curves over a perfect field.
* `finrank_ramificationIdealSheaf_eq_degree_different_of_perfectField`:
  `dim_k Γ(R_f, 𝒪_{R_f}) = deg Diff(k(X)/k(Y))`.
* `eulerDegree_relativeDifferentials_eq_finrank_mul_add_degree_different_of_perfectField`:
  `deg Ω_{X/k} = [k(X) : k(Y)] · deg Ω_{Y/k} + deg Diff(k(X)/k(Y))`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009, §3.4.
* J.-P. Serre, *Local Fields*, Chapter III, §6.
* R. Hartshorne, *Algebraic Geometry*, Theorem IV.2.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]

/-- **Local coincidence of the ramification ideal sheaf and the trace-dual different.** Let
`f : X ⟶ Y` be a dominant morphism of integral schemes over `Spec k` with finite separable
function-field extension along `f^*`, and let `x : X` be a point where `𝒪_{X,x}` and
`𝒪_{Y,f x}` are discrete valuation rings with separable residue extension `κ(x) / κ(f x)`. Then
the stalk ideal of `ramificationIdealSheaf k f` at `x` is `𝔪_{X,x} ^ d(P_x ∣ P_{f x})`. -/
theorem ramificationIdealSheaf_stalkIdeal_eq_maximalIdeal_pow_differentExponent
    [IsIntegral X] [IsIntegral Y]
    [(cokernel (cotangentMap k f)).IsFiniteType]
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z)
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]
    [Algebra.IsSeparable ((X.toPlace (k := k) x).restrict k Y.functionField).ResidueField
      (X.toPlace (k := k) x).ResidueField] :
    (ramificationIdealSheaf k f).stalkIdeal x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^
        Place.differentExponent k Y.functionField (X.toPlace (k := k) x) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have hres : (X.toPlace (k := k) x).restrict k Y.functionField = Y.toPlace (k := k) (f x) :=
    f.toPlace_restrict_eq hmap x
  let P' := X.toPlace (k := k) x
  let P := P'.restrict k Y.functionField
  let _ := Place.algebraIntegersExtension (F' := X.functionField) P
  let _ := Place.isScalarTowerIntegersExtension (F' := X.functionField) P
  let _ := Place.moduleFinite_kaehlerDifferential_integers (k := k) (F := Y.functionField) P'
  let e₀ : Y.presheaf.stalk (f x) ≃+* P.integers :=
    (Y.stalkToPlaceIntegersAlgEquiv (k := k) (f x)).toRingEquiv.trans
      (RingEquiv.subringCongr (congrArg (fun q : Place k Y.functionField ↦ q.integers.toSubring)
        hres.symm))
  let e : X.presheaf.stalk x ≃+* P'.integers :=
    (X.stalkToPlaceIntegersAlgEquiv (k := k) x).toRingEquiv
  have he : ∀ y : Y.presheaf.stalk (f x), e (algebraMap _ _ y) = algebraMap _ _ (e₀ y) := by
    intro y
    refine Subtype.ext ?_
    rw [RingHom.algebraMap_toAlgebra, Place.coe_algebraMap_integers]
    dsimp only [e, e₀]
    rw [RingEquiv.trans_apply, RingEquiv.coe_subringCongr_apply,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv,
      X.coe_stalkToPlaceIntegersAlgEquiv (k := k) x,
      Y.coe_stalkToPlaceIntegersAlgEquiv (k := k) (f x), hmap]
    exact (f.functionFieldMap_algebraMap_stalk x y).symm
  let eM := KaehlerDifferential.mapSemilinearEquivOfRingEquiv e₀ e fun r ↦ (he r).symm
  have hfitt := ramificationIdealSheaf_stalkIdeal_eq_fittingIdeal_kaehlerDifferential k f x
  let _ := moduleFinite_kaehlerDifferential_stalk k f x
  let _ := RingHomInvPair.of_ringEquiv e
  let _ := RingHomInvPair.of_ringEquiv e.symm
  have hmax : Ideal.map (e.symm : P'.integers →+* X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal P'.integers) = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.symm
  rw [hfitt,
    ← Ideal.map_of_equiv e (I := TauCeti.fittingIdeal (X.presheaf.stalk x)
      Ω[X.presheaf.stalk x⁄Y.presheaf.stalk (f x)] 0),
    ← TauCeti.fittingIdeal_eq_map_of_semilinearEquiv eM 0,
    Place.fittingIdeal_kaehlerDifferential_integers_eq_maximalIdeal_pow (k := k)
      (F := Y.functionField) P',
    Ideal.map_pow, hmax]

/-- **Order of the Cartier ramification divisor at a point with separable residue field**: when
`Ω_{X/k}` and `Ω_{Y/k}` are invertible and `f : X ⟶ Y` is dominant with finite separable
function-field extension, the order of `ramificationCartierDivisor k f` at a codimension-one point
`x` whose image stalk is a discrete valuation ring and whose residue extension is separable equals
the trace-dual different exponent `d(P_x ∣ P_{f x})`. -/
theorem orderAt_ramificationCartierDivisor_eq_differentExponent
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
    [SheafOfModules.isInvertible Y (Y.relativeDifferentials k)]
    [Mono (cotangentMap k f)]
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z)
    (x : CodimensionOnePoint X) [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f (x : X)))]
    [Algebra.IsSeparable ((X.toPlace (k := k) (x : X)).restrict k Y.functionField).ResidueField
      (X.toPlace (k := k) (x : X)).ResidueField] :
    (ramificationCartierDivisor k f).orderAt x =
      Place.differentExponent k Y.functionField (X.toPlace (k := k) (x : X)) := by
  refine (Scheme.CartierDivisor.IsEffective.orderAt_eq_iff_stalkIdeal_eq_maximalIdeal_pow
    (isEffective_ramificationCartierDivisor k f) x).mpr ?_
  rw [idealSheaf_ramificationCartierDivisor]
  exact ramificationIdealSheaf_stalkIdeal_eq_maximalIdeal_pow_differentExponent k f hmap (x : X)

/-- **Identification of the Cartier ramification divisor with the trace-dual different on the
separable-residue branch.** Let `f : X ⟶ Y` be a dominant morphism of regular integral proper curves
over `k` with finite separable function-field extension `k(X) / k(Y)` along `f^*`, invertible
relative differentials `Ω_{X/k}` and `Ω_{Y/k}`, and separable residue extensions at all
codimension-one points of `X`. Then the Weil divisor of `ramificationCartierDivisor k f` corresponds
under `SchemeWeilDivisor.equivFunctionFieldDivisor` to `Divisor.different k X.functionField`. -/
theorem equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor
    [X.IsCurveOver k] [Y.IsCurveOver k]
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    [∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y))]
    [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
    [SheafOfModules.isInvertible Y (Y.relativeDifferentials k)]
    [Mono (cotangentMap k f)]
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z)
    (hsep : ∀ x : CodimensionOnePoint X,
      Algebra.IsSeparable ((X.toPlace (k := k) (x : X)).restrict k Y.functionField).ResidueField
        (X.toPlace (k := k) (x : X)).ResidueField) :
    haveI := Scheme.IsCurveOver.isNoetherian k X
    haveI := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
    SchemeWeilDivisor.equivFunctionFieldDivisor
        (Scheme.IsCurveOver.valuativeCriterion_existence k X)
        (Scheme.IsCurveOver.coheight_le_one (k := k))
        (ramificationCartierDivisor k f).toWeilDivisor =
      Divisor.different k X.functionField
        (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y)) := by
  have := Scheme.IsCurveOver.isNoetherian k X
  have := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  ext P
  obtain ⟨x, rfl⟩ :=
    (CodimensionOnePoint.equivPlace (k := k)
      (Scheme.IsCurveOver.valuativeCriterion_existence k X)
      (Scheme.IsCurveOver.coheight_le_one (k := k))).surjective P
  rw [CodimensionOnePoint.equivPlace_apply,
    SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_toPlace,
    Scheme.CartierDivisor.coeff_toWeilDivisor, Divisor.coeff_different]
  have : IsDiscreteValuationRing (Y.presheaf.stalk (f (x : X))) :=
    f.isDiscreteValuationRing_stalk_image (k := k) hmap
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k).le (x : X)
  have := hsep x
  rw [orderAt_ramificationCartierDivisor_eq_differentExponent k f hmap x]

/-- The subscheme rank `dim_k Γ(R_f, 𝒪_{R_f})` of the ramification locus equals
`deg Diff(k(X) / k(Y))` on the separable-residue branch. -/
theorem finrank_ramificationIdealSheaf_eq_degree_different
    [X.IsCurveOver k] [Y.IsCurveOver k]
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    [∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y))]
    [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
    [SheafOfModules.isInvertible Y (Y.relativeDifferentials k)]
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z)
    (hsep : ∀ x : CodimensionOnePoint X,
      Algebra.IsSeparable ((X.toPlace (k := k) (x : X)).restrict k Y.functionField).ResidueField
        (X.toPlace (k := k) (x : X)).ResidueField) :
    haveI : (cokernel (cotangentMap k f)).IsFiniteType := by infer_instance
    (((ramificationIdealSheaf k f).subschemeι ≫ X ↘ Spec (.of k)).finrank default : ℤ) =
      Divisor.degree (Divisor.different k X.functionField
        (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y))) := by
  have hmono : Mono (cotangentMap k f) :=
    mono_cotangentMap_of_ne_zero k f (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f
      (f.isSeparable_functionFieldMap hmap))
  have hI := isEffectiveCartier_ramificationIdealSheaf k f
  have hdimX : RelativeDimensionLE 1 (X ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field (X ↘ Spec (.of k))).mpr
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  have hfin : IsFinite ((ramificationIdealSheaf k f).subschemeι ≫ X ↘ Spec (.of k)) :=
    hI.isFinite_subschemeι_comp
  have : IsNoetherian X := Scheme.IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have hdeg : (((ramificationIdealSheaf k f).subschemeι ≫
      X ↘ Spec (.of k)).finrank default : ℤ) =
      LineBundleClass.eulerDegree k (ramificationCartierDivisor k f).toLineBundleClass := by
    rw [toLineBundleClass_ramificationCartierDivisor,
      ← inv_mk_toInvertibleSheaf_ramificationIdealSheaf k f,
      LineBundleClass.eulerDegree_inv k (Scheme.IsCurveOver.coheight_le_one (k := k)),
      LineBundleClass.eulerDegree_mk,
      hI.eulerDegree_toInvertibleSheaf k _ default, neg_neg]
  rw [hdeg, Scheme.CartierDivisor.toLineBundleClass_eq_toWeilDivisor
      (Scheme.IsCurveOver.coheight_le_one (k := k)),
    LineBundleClass.eulerDegree_toLineBundleClass k
      (Scheme.IsCurveOver.coheight_le_one (k := k)),
    ← SchemeWeilDivisor.degree_equivFunctionFieldDivisor
      (Scheme.IsCurveOver.valuativeCriterion_existence k X)
      (Scheme.IsCurveOver.coheight_le_one (k := k)),
    equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor k f hmap hsep]

/-- **Scheme-theoretic Riemann–Hurwitz formula with the trace-dual different** on the
separable-residue branch:
`deg Ω_{X/k} = [k(X) : k(Y)] · deg Ω_{Y/k} + deg Diff(k(X) / k(Y))`. -/
theorem eulerDegree_relativeDifferentials_eq_finrank_mul_add_degree_different
    [X.IsCurveOver k] [Y.IsCurveOver k]
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    [∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y))]
    [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
    [SheafOfModules.isInvertible Y (Y.relativeDifferentials k)]
    [IsFinite f]
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z)
    (hsep : ∀ x : CodimensionOnePoint X,
      Algebra.IsSeparable ((X.toPlace (k := k) (x : X)).restrict k Y.functionField).ResidueField
        (X.toPlace (k := k) (x : X)).ResidueField) :
    InvertibleSheaf.eulerDegree k ⟨X.relativeDifferentials k, inferInstance⟩ =
      Module.finrank Y.functionField X.functionField *
        InvertibleSheaf.eulerDegree k ⟨Y.relativeDifferentials k, inferInstance⟩ +
        Divisor.degree (Divisor.different k X.functionField
          (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y))) := by
  have : ∀ y : Y, ValuationRing (Y.presheaf.stalk y) :=
    Scheme.IsCurveOver.valuationRing_stalk k Y
  have : Flat f := f.flat_of_isDominant_of_valuationRing
  have hne : cotangentMap k f ≠ 0 :=
    cotangentMap_ne_zero_of_isDominant_of_isSeparable k f (f.isSeparable_functionFieldMap hmap)
  have : IsNoetherian X := Scheme.IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have hdimY : RelativeDimensionLE 1 (Y ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field (Y ↘ Spec (.of k))).mpr
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k).le
  have hdeg : Module.finrank f.functionFieldMap.hom.fieldRange X.functionField =
      Module.finrank Y.functionField X.functionField :=
    (Algebra.finrank_eq_of_equiv_equiv f.functionFieldMap.hom.rangeRestrictFieldEquiv
      (RingEquiv.refl X.functionField) (RingHom.ext fun z ↦ by
        simp [Subfield.algebraMap_ofSubfield, hmap])).symm
  rw [eulerDegree_relativeDifferentials_eq_finrank_mul_add_ramification k f hne,
    hdeg, finrank_ramificationIdealSheaf_eq_degree_different k f hmap hsep]

section PerfectField

variable [PerfectField k] [X.IsCurveOver k] [Y.IsCurveOver k]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

variable [∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y))]

/-- Over a perfect field `k`, for any dominant morphism `f : X ⟶ Y` of regular integral proper
curves with finite separable function-field extension `k(X) / k(Y)`, the Weil divisor of
`ramificationCartierDivisor k f` matches `Divisor.different k X.functionField`. -/
theorem equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor_of_perfectField
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z) :
    haveI := Scheme.IsCurveOver.isNoetherian k X
    haveI := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
    haveI := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k X
    haveI := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k Y
    haveI := isInvertible_relativeDifferentials (X := X) k
    haveI := isInvertible_relativeDifferentials (X := Y) k
    haveI : Mono (cotangentMap k f) :=
      mono_cotangentMap_of_ne_zero k f (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f
        (f.isSeparable_functionFieldMap hmap))
    SchemeWeilDivisor.equivFunctionFieldDivisor
        (Scheme.IsCurveOver.valuativeCriterion_existence k X)
        (Scheme.IsCurveOver.coheight_le_one (k := k))
        (ramificationCartierDivisor k f).toWeilDivisor =
      Divisor.different k X.functionField
        (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y)) := by
  have := Scheme.IsCurveOver.isNoetherian k X
  have := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k X
  have := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k Y
  have := isInvertible_relativeDifferentials (X := X) k
  have := isInvertible_relativeDifferentials (X := Y) k
  have : Mono (cotangentMap k f) :=
    mono_cotangentMap_of_ne_zero k f (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f
      (f.isSeparable_functionFieldMap hmap))
  have : Algebra.IsIntegral Y.functionField X.functionField :=
    Algebra.IsIntegral.of_finite Y.functionField X.functionField
  exact equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor k f hmap
    fun _ ↦
      Place.isSeparable_residueField_restrict_of_perfectField Scheme.IsCurveOver.isFunctionField _

/-- Over a perfect field `k`, `dim_k Γ(R_f, 𝒪_{R_f}) = deg Diff(k(X) / k(Y))`. -/
theorem finrank_ramificationIdealSheaf_eq_degree_different_of_perfectField
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z) :
    haveI : (cokernel (cotangentMap k f)).IsFiniteType := by infer_instance
    (((ramificationIdealSheaf k f).subschemeι ≫ X ↘ Spec (.of k)).finrank default : ℤ) =
      Divisor.degree (Divisor.different k X.functionField
        (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y))) := by
  have := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k X
  have := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k Y
  have := isInvertible_relativeDifferentials (X := X) k
  have := isInvertible_relativeDifferentials (X := Y) k
  have : Algebra.IsIntegral Y.functionField X.functionField :=
    Algebra.IsIntegral.of_finite Y.functionField X.functionField
  exact finrank_ramificationIdealSheaf_eq_degree_different k f hmap
    fun _ ↦
      Place.isSeparable_residueField_restrict_of_perfectField Scheme.IsCurveOver.isFunctionField _

/-- **Scheme-theoretic Riemann–Hurwitz formula with the trace-dual different over a perfect
field**: for any finite dominant morphism `f : X ⟶ Y` of regular integral proper curves over a
perfect field `k` with separable function-field extension,
`deg Ω_{X/k} = [k(X) : k(Y)] · deg Ω_{Y/k} + deg Diff(k(X) / k(Y))`. -/
theorem eulerDegree_relativeDifferentials_eq_finrank_mul_add_degree_different_of_perfectField
    [IsFinite f]
    [Algebra Y.functionField X.functionField]
    [IsScalarTower k Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField]
    (hmap : ∀ z : Y.functionField,
      algebraMap Y.functionField X.functionField z = f.functionFieldMap z) :
    haveI := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k X
    haveI := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k Y
    InvertibleSheaf.eulerDegree k
        ⟨X.relativeDifferentials k, isInvertible_relativeDifferentials (X := X) k⟩ =
      Module.finrank Y.functionField X.functionField *
        InvertibleSheaf.eulerDegree k
          ⟨Y.relativeDifferentials k, isInvertible_relativeDifferentials (X := Y) k⟩ +
        Divisor.degree (Divisor.different k X.functionField
          (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y))) := by
  have := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k X
  have := Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k Y
  have := isInvertible_relativeDifferentials (X := X) k
  have := isInvertible_relativeDifferentials (X := Y) k
  have : Algebra.IsIntegral Y.functionField X.functionField :=
    Algebra.IsIntegral.of_finite Y.functionField X.functionField
  exact eulerDegree_relativeDifferentials_eq_finrank_mul_add_degree_different k f hmap
    fun _ ↦
      Place.isSeparable_residueField_restrict_of_perfectField Scheme.IsCurveOver.isFunctionField _

end PerfectField

end TauCeti.AlgebraicGeometry

end
