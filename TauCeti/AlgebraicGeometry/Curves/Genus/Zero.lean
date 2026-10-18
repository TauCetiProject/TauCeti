/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.AlgebraicGeometry.RationalPoint.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Curves of genus zero with a divisor of degree one

Let `X` be a regular proper curve over a field `k`, that is, a curve over `k` whose local rings at
its codimension-one points are discrete valuation rings, and suppose that `k` is integrally closed
in the function field `k(X)`. If `X` has genus zero, `dim_k H¹(X, 𝒪_X) = 0`, and carries a divisor
of degree one, for instance the prime divisor of a `k`-rational point, then **`X` is the projective
line**: there is an isomorphism `X ≅ ℙ¹_k` over `k`.

This is the geometric form of Stichtenoth's Proposition 1.6.3. The genus of `X` is the genus of
`k(X)` (`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.genus_eq_genus_functionField`), and a divisor
of degree one on `X` is a divisor of degree one of `k(X)`, so the function field is rational
(`TauCeti.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one`). A `k`-isomorphism
`k(X) ≃ k(t)` then identifies `X` with `ℙ¹_k` through the two-chart models of the two function
fields: `X` is the two-chart model of `k(X)` (`AlgebraicGeometry.Scheme.isoTwoChartModel`), an
isomorphism of function fields induces an isomorphism of two-chart models
(`TauCeti.AlgebraicGeometry.twoChartModel.isoOfAlgEquiv`), and `ℙ¹_k` is the two-chart model of
`k(t)` (`TauCeti.AlgebraicGeometry.projectiveLine.isoTwoChartModel`).

Genus zero alone does not suffice: the function field of a conic without rational points has genus
zero but no divisor of degree one
(`TauCeti.not_exists_divisor_degree_eq_one_of_sq_add_sq_add_one_eq_zero`).

## Main definitions

* `AlgebraicGeometry.Scheme.isoProjectiveLine`: the isomorphism `X ≅ ℙ¹_k` over `k` induced by a
  `k`-isomorphism `k(t) ≃ k(X)`.

## Main results

* `AlgebraicGeometry.Scheme.functionFieldMap_isoProjectiveLine_hom`: the pullback of rational
  functions along `X.isoProjectiveLine e` is `e`.
* `AlgebraicGeometry.Scheme.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one`:
  a regular proper curve of genus zero with a divisor of degree one has rational function field.
* `AlgebraicGeometry.Scheme.exists_iso_projectiveLine_of_genus_eq_zero_of_divisor_degree_eq_one`:
  such a curve is isomorphic to `ℙ¹_k` over `k`.
* `AlgebraicGeometry.Scheme.exists_iso_projectiveLine_of_genus_eq_zero_of_section`: in particular,
  a regular proper curve of genus zero with a `k`-rational point is isomorphic to `ℙ¹_k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.6.3 and Remark 1.6.4.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Corollary I.6.12 and
  Example IV.1.3.5.
-/

public section

open CategoryTheory Limits TauCeti TauCeti.AlgebraicGeometry Order
open Module (finrank)

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-! ### The isomorphism induced by a rational function field -/

/-- **A curve with rational function field is the projective line**: the isomorphism `X ≅ ℙ¹_k`
induced by a `k`-isomorphism `e : k(t) ≃ k(X)`, through the two-chart models of `k(X)`, built from
the function `e t`, and of `k(t)`, built from `t`. Its pullback of rational functions is `e`
(`functionFieldMap_isoProjectiveLine_hom`). -/
noncomputable def isoProjectiveLine (e : RatFunc k ≃ₐ[k] X.functionField) :
    X ≅ projectiveLine k :=
  X.isoTwoChartModel (RatFunc.transcendental_apply_X e.toAlgHom e.injective).ne_zero
      (RatFunc.transcendental_apply_X e.toAlgHom e.injective) ≪≫
    twoChartModel.isoOfAlgEquiv (IsFunctionField.ratFunc k) _ RatFunc.X_ne_zero
      (RatFunc.transcendental_apply_X e.toAlgHom e.injective).ne_zero e
      (hxt := RatFunc.transcendental_X)
      (hx't := RatFunc.transcendental_apply_X e.toAlgHom e.injective) ≪≫
    (projectiveLine.isoTwoChartModel k).symm

/-- The isomorphism `X ⟶ ℙ¹_k` of `isoProjectiveLine` is a morphism over `k`. -/
instance (e : RatFunc k ≃ₐ[k] X.functionField) :
    (X.isoProjectiveLine e).hom.IsOver (Spec (.of k)) := by
  rw [isoProjectiveLine, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    twoChartModel.isoOfAlgEquiv_hom]
  infer_instance

/-- **The pullback of rational functions along `X ≅ ℙ¹_k` is `e`**: under the identification of the
function field of `ℙ¹_k` with `k(t)`, the pullback along `X.isoProjectiveLine e` is `e`. -/
@[simp]
theorem functionFieldMap_isoProjectiveLine_hom (e : RatFunc k ≃ₐ[k] X.functionField)
    (z : RatFunc k) :
    (X.isoProjectiveLine e).hom.functionFieldMap ((projectiveLine.functionFieldEquiv k).symm z) =
      e z := by
  simp only [isoProjectiveLine, Iso.trans_hom, Iso.symm_hom, twoChartModel.isoOfAlgEquiv_hom,
    Hom.functionFieldMap_comp, CommRingCat.comp_apply]
  rw [(AlgEquiv.eq_symm_apply _).mpr
      (projectiveLine.functionFieldEquiv_functionFieldMap_isoTwoChartModel_inv k z),
    (AlgEquiv.eq_symm_apply _).mpr
      (twoChartModel.functionFieldEquiv_functionFieldMap_homOfAlgHom ..),
    functionFieldMap_isoTwoChartModel_hom, AlgEquiv.coe_toAlgHom]

/-! ### Curves of genus zero -/

/-- **A curve of genus zero with a divisor of degree one has rational function field.** Let `X` be
a regular proper curve over `k`, with `k` integrally closed in `k(X)`. If `dim_k H¹(X, 𝒪_X) = 0`
and some divisor on `X` has degree one, then `k(X)` is `k`-isomorphic to the rational function
field `k(t)`. -/
theorem nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one
    (hk : IsIntegrallyClosedIn k X.functionField)
    (hg : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) = 0)
    {D : SchemeWeilDivisor X} (hD : SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D = 1) :
    Nonempty (X.functionField ≃ₐ[k] RatFunc k) := by
  have hX := IsCurveOver.topologicalKrullDim_eq_one (X := X) k
  have hdim := IsCurveOver.coheight_le_one (k := k) (X := X)
  let _ : IsNoetherian X := IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have hex := IsCurveOver.valuativeCriterion_existence k X
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hX
  have hF := IsCurveOver.isFunctionField (k := k) (X := X)
  have hgF : TauCeti.genus k X.functionField = 0 := by
    rw [← SchemeWeilDivisor.genus_eq_genus_functionField hex hdim hF hk, genus_def, hg]
  exact TauCeti.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one hF hk hgF
    ⟨SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim D, by
      rw [SchemeWeilDivisor.degree_equivFunctionFieldDivisor, hD]⟩

/-- **A curve of genus zero with a divisor of degree one is the projective line.** Let `X` be a
regular proper curve over `k`, with `k` integrally closed in `k(X)`. If `dim_k H¹(X, 𝒪_X) = 0` and
some divisor on `X` has degree one, for instance the prime divisor of a `k`-rational point, then
`X` is isomorphic to `ℙ¹_k` over `k`. -/
theorem exists_iso_projectiveLine_of_genus_eq_zero_of_divisor_degree_eq_one
    (hk : IsIntegrallyClosedIn k X.functionField)
    (hg : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) = 0)
    {D : SchemeWeilDivisor X} (hD : SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D = 1) :
    ∃ e : X ≅ projectiveLine k, e.hom.IsOver (Spec (.of k)) := by
  obtain ⟨e⟩ := X.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one hk hg hD
  exact ⟨X.isoProjectiveLine e.symm, inferInstance⟩

/-- **A curve of genus zero with a rational point is the projective line.** Let `X` be a regular
proper curve over `k`, with `k` integrally closed in `k(X)`. If `dim_k H¹(X, 𝒪_X) = 0` and `X` has
a `k`-rational point, then `X` is isomorphic to `ℙ¹_k` over `k`. -/
theorem exists_iso_projectiveLine_of_genus_eq_zero_of_section
    (hk : IsIntegrallyClosedIn k X.functionField)
    (hg : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) = 0)
    {s : Spec (.of k) ⟶ X} (hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 _) :
    ∃ e : X ≅ projectiveLine k, e.hom.IsOver (Spec (.of k)) :=
  X.exists_iso_projectiveLine_of_genus_eq_zero_of_divisor_degree_eq_one hk hg
    (relativeDegree_ofPoint_of_section hs
      (x₀ := ⟨_, IsCurveOver.coheight_section_eq_one k hs⟩) rfl)

end AlgebraicGeometry.Scheme
