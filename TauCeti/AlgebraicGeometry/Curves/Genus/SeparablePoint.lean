/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import TauCeti.AlgebraicGeometry.Curves.Genus.ConstantExtension
import TauCeti.AlgebraicGeometry.Curves.Smooth
import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
import TauCeti.AlgebraicGeometry.Modules.Differentials.Rational
import TauCeti.FieldTheory.FunctionField.Consequences.SeparablePlace
import TauCeti.FieldTheory.FunctionField.Consequences.SeparatingElement

/-!
# Separable points of small degree on curves of genus at least two

Let `X` be a smooth proper geometrically integral curve of genus `g ≥ 2` over a field `k`, with no
assumption on `k`. Then `X` has a closed point `x` whose residue field `κ(x)` is a separable
extension of `k` of degree at most `2g - 2`. Consequently `X` acquires a rational point over a
finite separable extension `K / k` of degree at most `2g - 2`, namely `K = κ(x)`: the base change
`X ×_k K` has a section over `Spec K`.

This is the first factor of the degree bound `(2g - 2) · (ℓ^{2g})!` in the Stacks Project's proof of
semistable reduction: a rational point over a small separable extension is what lets torsion line
bundles on the curve be described by the points of its Jacobian.

The function field `F = k(X)` has `k` as exact constant field and a separating element, because
`X` is geometrically integral and smooth. Let `k'` be the algebraic closure of `k` inside an
algebraic closure of `F`, and `F' = F · k'`. Geometric integrality makes `F ⊗[k] k'` a domain, hence
a field, so `F` and `k'` are linearly disjoint in `F'`; `k'` is exact in `F'`, being algebraically
closed; and `F' / k'` keeps the genus `g` because `X` is smooth
(`TauCeti.AlgebraicGeometry.genus_eq_genus_functionField_of_constantCompositum_eq_top`). These are
the hypotheses under which an effective canonical divisor `W` of `F` contains a separating element
`t ∈ L(W)`, so that `[F : k(t)] ≤ deg W = 2g - 2`
(`exists_transcendental_and_isSeparable_adjoin_and_finrank_le_of_constantCompositum_eq_top`, in
the namespace `TauCeti.IsFunctionField`).
A place of `F` above a suitable rational place of `k(t)` then has separable residue field of degree
at most `[F : k(t)]` (`TauCeti.exists_place_degree_le_finrank_and_isSeparable`), and it is the place
of a closed point of `X` with the same residue field.

Over a perfect field `k` any point in the support of an effective canonical divisor already has
degree at most `2g - 2`. Over an imperfect field its residue field may be inseparable over `k`,
which is why the argument goes through a separating element.

## Main results

* `AlgebraicGeometry.Scheme.exists_finrank_residueField_le_and_isSeparable_of_two_le_genus`: a
  smooth proper geometrically integral curve of genus `g ≥ 2` has a point whose residue field is
  separable of degree at most `2g - 2` over `k`.
* `AlgebraicGeometry.Scheme.exists_finrank_le_and_section_of_two_le_genus`: such a curve has a
  rational point over a separable extension `K / k` of degree at most `2g - 2`.

## References

* [The Stacks Project, Section 55.18](https://stacks.math.columbia.edu/tag/0CDL), Theorem
  [0CDM](https://stacks.math.columbia.edu/tag/0CDM), whose degree bound uses a point of the curve
  over a separable extension of degree at most `2g - 2`.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.10.2 (separating elements) and Section III.6 (constant field extensions).
-/

public section

open CategoryTheory Limits TauCeti TauCeti.AlgebraicGeometry
open Module (finrank)

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **A smooth curve of genus at least two has a separable point of degree at most `2g - 2`.** Let
`X` be a smooth proper geometrically integral curve over `k` of genus
`g = dim_k H¹(X, 𝒪_X) ≥ 2`. Then some point `x` of `X` has residue field `κ(x)` a separable
extension of `k` of degree at most `2g - 2`. -/
theorem exists_finrank_residueField_le_and_isSeparable_of_two_le_genus
    (hg : 2 ≤ finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)) :
    ∃ x : X, FiniteDimensional k (X.residueField x) ∧
      finrank k (X.residueField x) ≤
        2 * finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) - 2 ∧
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
  have hgF : TauCeti.genus k X.functionField =
      finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) := by
    rw [← X.genus_eq_genus_functionField_of_smooth, genus_def]
  -- The differentials of `k(X)` are one-dimensional, being the generic stalk of the invertible
  -- sheaf `Ω_{X/k}`, so `k(X)` has a separating element.
  have := isInvertible_relativeDifferentials (X := X) k
  have hsep := exists_transcendental_and_isSeparable_adjoin_of_isInvertible hF
  -- The constant field extension `F' = k(X) · k'`, with `k'` the algebraic closure of `k` inside an
  -- algebraic closure `Ω` of `k(X)`.
  let Ω := AlgebraicClosure X.functionField
  let k' := algebraicClosure k Ω
  let F' := constantCompositum X.functionField k' Ω
  let := constantCompositumAlgebra X.functionField k' Ω
  have := isScalarTower_constantCompositum X.functionField k' Ω
  have := isScalarTower_base_constantCompositum k X.functionField k' Ω
  have h : constantCompositum X.functionField k' F' = ⊤ :=
    (constantCompositum_eq_top_iff X.functionField k' Ω F').2 rfl
  have : IsAlgClosed k' := IsAlgClosure.isAlgClosed k
  -- `k(X) ⊗[k] k'` is a domain by geometric integrality, hence a field, so `k(X)` and `k'` are
  -- linearly disjoint in `F'`.
  have hfield := Algebra.TensorProduct.isField_of_isAlgebraic k X.functionField k'
    (.inr inferInstance)
  have H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint X.functionField := by
    have := (IntermediateField.LinearDisjoint.of_isField' hfield
      (IsScalarTower.toAlgHom k X.functionField F') (IsScalarTower.toAlgHom k k' F')).symm
    rwa [IntermediateField.linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra] at this
  -- So `k(X)` has a separating element `t` with `[k(X) : k(t)] ≤ 2g - 2`.
  obtain ⟨t, -, _, ht⟩ :=
    hF.exists_transcendental_and_isSeparable_adjoin_and_finrank_le_of_constantCompositum_eq_top hk
      hsep h H isIntegrallyClosedIn_of_isAlgClosed
      (genus_eq_genus_functionField_of_constantCompositum_eq_top h) (hgF ▸ hg)
  obtain ⟨P, hP, hPsep⟩ := exists_place_degree_le_finrank_and_isSeparable hF t
  -- The place is the place of a closed point, whose residue field is that of the place.
  obtain ⟨x, rfl⟩ := CodimensionOnePoint.toPlace_surjective (k := k) hex hdim P
  let e := X.toPlaceResidueFieldAlgEquiv (k := k) (x : X)
  have := (X.toPlace (k := k) (x : X)).finiteDimensional_residueField hF
  refine ⟨x, e.symm.toLinearEquiv.finiteDimensional, ?_, AlgEquiv.Algebra.isSeparable e.symm⟩
  rw [← Scheme.toPlace_degree, ← hgF]
  exact hP.trans ht

/-- **A smooth curve of genus at least two has a rational point over a separable extension of
degree at most `2g - 2`.** Let `X` be a smooth proper geometrically integral curve over `k` of genus
`g = dim_k H¹(X, 𝒪_X) ≥ 2`. Then there is a separable extension `K / k` of degree at most `2g - 2`
such that `X ×_k K` has a `K`-rational point, that is, a section over `Spec K`. -/
theorem exists_finrank_le_and_section_of_two_le_genus
    (hg : 2 ≤ finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧
      finrank k K ≤
        2 * finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) - 2 ∧
      Algebra.IsSeparable k K ∧
      ∃ s : Spec (.of K) ⟶
        pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        s ≫ pullback.snd _ _ = 𝟙 _ := by
  obtain ⟨x, h₁, h₂, h₃⟩ := X.exists_finrank_residueField_le_and_isSeparable_of_two_le_genus hg
  -- The point `Spec κ(x) ⟶ X` lies over `k`, so it is a section of the base change to `κ(x)`.
  refine ⟨_, _, _, h₁, h₂, h₃, pullback.lift (X.fromSpecResidueField x) (𝟙 _) ?_,
    pullback.lift_snd _ _ _⟩
  rw [X.fromSpecResidueField_comp_over (k := k), Category.id_comp]

end AlgebraicGeometry.Scheme
