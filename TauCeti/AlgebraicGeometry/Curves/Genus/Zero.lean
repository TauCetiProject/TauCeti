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
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import TauCeti.AlgebraicGeometry.Curves.Genus.BaseChange
import TauCeti.AlgebraicGeometry.Curves.Genus.ConstantExtension
import TauCeti.AlgebraicGeometry.Curves.Smooth
import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
import TauCeti.AlgebraicGeometry.Modules.Differentials.Rational
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Place.Proper
import TauCeti.FieldTheory.FunctionField.Consequences.SeparablePlace
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Curves of genus zero and the projective line

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

It does suffice after a separable extension of degree at most two, for smooth curves. Let `X` be a
smooth proper geometrically integral curve of genus zero over `k`. Its function field has exact
constant field `k` and a separating element, since the differentials `Ω_{k(X)/k}` are the generic
stalk of the invertible sheaf `Ω_{X/k}`, so it has a place of degree at most two whose residue field
is separable over `k` (`TauCeti.exists_place_degree_le_two_and_isSeparable_of_genus_eq_zero`). That
place is the place of a closed point `x` of `X`, with the same residue field. Over any extension
`K` of `k` into which `κ(x)` embeds, the base change `X_K` is again smooth, proper, geometrically
integral and of genus zero, and it has a `K`-rational point, so it is `ℙ¹_K`. Taking `K = κ(x)`,
`X` becomes the projective line over a separable extension of degree at most two.

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
* `AlgebraicGeometry.Scheme.exists_iso_projectiveLine_of_isPullback_of_genus_eq_zero`: a smooth
  proper geometrically integral curve of genus zero becomes `ℙ¹_K` over every extension `K` in which
  it has a point.
* `AlgebraicGeometry.Scheme.exists_finrank_residueField_le_two_and_isSeparable_of_genus_eq_zero`:
  such a curve has a point whose residue field is separable of degree at most two over `k`.
* `AlgebraicGeometry.Scheme.exists_finrank_le_two_and_iso_projectiveLine_of_genus_eq_zero`: such a
  curve becomes `ℙ¹_K` over a separable extension `K / k` of degree at most two.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.6.3 and Remark 1.6.4.
* [The Stacks Project, Chapter 55, Semistable Reduction](https://stacks.math.columbia.edu/tag/0C2P),
  the case of genus zero.
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

/-! ### Smooth curves of genus zero over a separable extension of degree at most two -/

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **A smooth curve of genus zero is the projective line over every field in which it has a
point.** Let `X` be a smooth proper geometrically integral curve over `k` with
`dim_k H¹(X, 𝒪_X) = 0`, let `K / k` be a field extension and `Y = X ×_k K`. If some point `x` of
`X` has residue field `κ(x)` embedding into `K` over `k`, that is, if `X` has a `K`-valued point,
then `Y` is isomorphic to `ℙ¹_K` over `K`. -/
theorem exists_iso_projectiveLine_of_isPullback_of_genus_eq_zero {K : Type u} [Field K]
    [Algebra k K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] {g : Y ⟶ X}
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hg : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) = 0)
    (x : X) (φ : X.residueField x →ₐ[k] K) :
    ∃ e : Y ≅ projectiveLine K, e.hom.IsOver (Spec (.of K)) := by
  have := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  have : IsProper (Y ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) H inferInstance
  have : GeometricallyIntegral (Y ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H inferInstance
  have := GeometricallyIntegral.isIntegral_of_subsingleton (Y ↘ Spec (.of K))
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of K))
  have := IsCurveOver.of_smooth K Y
  have := isDiscreteValuationRing_stalk_of_smooth (X := Y) K
  -- The `K`-valued point `Spec K ⟶ Spec κ(x) ⟶ X` lies over `k`, so it is a section of `Y`.
  have hp : (Spec.map (CommRingCat.ofHom (φ : X.residueField x →+* K)) ≫
      X.fromSpecResidueField x) ≫ (X ↘ Spec (.of k)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Category.assoc, X.fromSpecResidueField_comp_over (k := k), ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  refine Y.exists_iso_projectiveLine_of_genus_eq_zero_of_section
    isIntegrallyClosedIn_functionField_of_geometricallyIntegral ?_
    (H.lift_snd _ (𝟙 _) (by rw [hp, Category.id_comp]))
  rw [finrank_cohomology_one_trivial_eq_of_isPullback_of_smooth H, hg]

/-- **A smooth curve of genus zero has a point of degree at most two with separable residue
field.** Let `X` be a smooth proper geometrically integral curve over `k` with
`dim_k H¹(X, 𝒪_X) = 0`. Then some point `x` of `X` has residue field `κ(x)` a separable extension of
`k` of degree at most two. -/
theorem exists_finrank_residueField_le_two_and_isSeparable_of_genus_eq_zero
    (hg : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) = 0) :
    ∃ x : X, FiniteDimensional k (X.residueField x) ∧ finrank k (X.residueField x) ≤ 2 ∧
      Algebra.IsSeparable k (X.residueField x) := by
  have := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := IsCurveOver.of_smooth k X
  have := isDiscreteValuationRing_stalk_of_smooth (X := X) k
  have hdim := IsCurveOver.coheight_le_one (k := k) (X := X)
  have hex := IsCurveOver.valuativeCriterion_existence k X
  have hF := IsCurveOver.isFunctionField (k := k) (X := X)
  have hk : IsIntegrallyClosedIn k X.functionField :=
    isIntegrallyClosedIn_functionField_of_geometricallyIntegral
  have hgF : TauCeti.genus k X.functionField = 0 := by
    rw [← X.genus_eq_genus_functionField_of_smooth, genus_def, hg]
  -- The differentials of `k(X)` are one-dimensional, being the generic stalk of the invertible
  -- sheaf `Ω_{X/k}`, so `k(X)` has a separating element.
  have := isInvertible_relativeDifferentials (X := X) k
  obtain ⟨t, -, _⟩ := exists_transcendental_and_isSeparable_adjoin_of_isInvertible hF
  obtain ⟨P, hP, hsep⟩ := exists_place_degree_le_two_and_isSeparable_of_genus_eq_zero hF hk hgF t
  -- The place is the place of a closed point, whose residue field is that of the place.
  obtain ⟨x, rfl⟩ := CodimensionOnePoint.toPlace_surjective (k := k) hex hdim P
  let e := X.toPlaceResidueFieldAlgEquiv (k := k) (x : X)
  have := (X.toPlace (k := k) (x : X)).finiteDimensional_residueField hF
  refine ⟨x, e.symm.toLinearEquiv.finiteDimensional, ?_, AlgEquiv.Algebra.isSeparable e.symm⟩
  rwa [← Scheme.toPlace_degree]

/-- **A smooth curve of genus zero becomes the projective line over a separable extension of
degree at most two.** Let `X` be a smooth proper geometrically integral curve over `k` with
`dim_k H¹(X, 𝒪_X) = 0`. Then there is a separable extension `K / k` of degree at most two such that
`X ×_k K` is isomorphic to `ℙ¹_K` over `K`. -/
theorem exists_finrank_le_two_and_iso_projectiveLine_of_genus_eq_zero
    (hg : finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) = 0) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ finrank k K ≤ 2 ∧
      Algebra.IsSeparable k K ∧
      ∃ e : pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
        projectiveLine K, e.hom ≫ (projectiveLine K ↘ Spec (.of K)) = pullback.snd _ _ := by
  obtain ⟨x, h₁, h₂, h₃⟩ := X.exists_finrank_residueField_le_two_and_isSeparable_of_genus_eq_zero hg
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x)))
  let _ : (pullback (X ↘ Spec (.of k)) s).Over (Spec (.of (X.residueField x))) :=
    ⟨pullback.snd _ _⟩
  obtain ⟨e, he⟩ := X.exists_iso_projectiveLine_of_isPullback_of_genus_eq_zero
    (IsPullback.of_hasPullback (X ↘ Spec (.of k)) s) hg x (AlgHom.id k _)
  exact ⟨_, _, _, h₁, h₂, h₃, e, he.comp_over⟩

end AlgebraicGeometry.Scheme
