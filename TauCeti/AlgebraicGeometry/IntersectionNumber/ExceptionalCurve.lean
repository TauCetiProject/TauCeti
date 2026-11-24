/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.FieldTower
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# Exceptional curves of the first kind

Let `X` be a scheme. A closed subscheme `E ⊆ X`, given by its ideal sheaf `I`, is an
**exceptional curve of the first kind** when

* `E` is an effective Cartier divisor on `X`,
* `E` is isomorphic to the projective line `ℙ¹_κ` over some field `κ`, and
* the normal sheaf `𝒪_X(E)|_E` has degree `-1` on `E ≅ ℙ¹_κ`, that is, the self-intersection
  number `(E · E)` computed over `κ` is `-1`

(`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurve`). These are the curves that the
contraction theorem of Castelnuovo blows down on a regular surface, and a regular model of a
curve over a discrete valuation ring is *minimal* when its special fibre contains none of them.

The field `κ` in the definition is not extra data: it is the field `Γ(E, 𝒪_E)` of global
functions on `E`. Accordingly, if `E` is also a scheme over another field `k`, for instance the
residue field of a discrete valuation ring when `E` lies in the special fibre of a model, then its
numerical invariants over `k` are determined:

* `dim_k H⁰(E, 𝒪_E) = [κ : k]`,
* `H¹(E, 𝒪_E) = 0`, and
* `(E · E) = -[κ : k] = -dim_k H⁰(E, 𝒪_E)` over `k`.

The input is that every morphism from `ℙ¹_R` to an affine scheme `Spec S` factors through the
structure morphism `ℙ¹_R → Spec R`, because the global functions on `ℙ¹_R` are the constants
(`AlgebraicGeometry.Scheme.exists_over_comp_specMap_eq`). So the structure of `E`
over `k` makes `κ` an extension of `k`, and the tower laws for cohomology and for intersection
numbers apply. On the special fibre of a regular model these are the statements that an
exceptional component has genus zero and self-intersection minus its weight, that is, it is a
`(-1)`-index of the numerical type of the model.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurve`: the closed subscheme cut out by
  an ideal sheaf is an exceptional curve of the first kind.

## Main results

* `Scheme.IdealSheafData.IsExceptionalCurve.exists_algebra_finrank_cohomology_zero`:
  over a field `k`, `E ≅ ℙ¹_κ` over `k` for an extension `κ` of `k`, and
  `dim_k H⁰(E, 𝒪_E) = [κ : k]`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurve.finrank_cohomology_one_trivial`:
  `H¹(E, 𝒪_E) = 0`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurve.intersectionNumber_self`:
  `(E · E) = -dim_k H⁰(E, 𝒪_E)` over every field `k` over which `E` is a scheme.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002,
  Section 9.3.1 (exceptional divisors and Castelnuovo's criterion).
* The Stacks Project, Chapter *Resolution of Surfaces*, Section *Contracting exceptional curves*,
  for the definition used here, and [Section 55.9](https://stacks.math.columbia.edu/tag/0C9U)
  for the numerical type of a regular model.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open Module (finrank)
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **Exceptional curves of the first kind.** The closed subscheme `E` of `X` cut out by the ideal
sheaf `I` is an exceptional curve of the first kind when it is an effective Cartier divisor
isomorphic to the projective line `ℙ¹_κ` over some field `κ`, such that the normal sheaf
`𝒪_X(E)|_E` has degree `-1` on `ℙ¹_κ`: the self-intersection number `(E · E)` over `κ`, the
degree over `κ` of the pullback of `𝒪_X(E)` along `ℙ¹_κ ≅ E ⟶ X`, is `-1`. -/
structure IsExceptionalCurve (I : X.IdealSheafData) : Prop where
  /-- An exceptional curve of the first kind is an effective Cartier divisor. -/
  isEffectiveCartier : I.IsEffectiveCartier
  /-- An exceptional curve of the first kind is a projective line over a field on which its
  normal sheaf has degree `-1`. -/
  exists_iso_projectiveLine : ∃ (κ : Type u) (_ : Field κ) (e : projectiveLine κ ≅ I.subscheme),
    LineBundleClass.intersectionNumber κ (e.hom ≫ I.subschemeι)
      (LineBundleClass.mk isEffectiveCartier.toInvertibleSheaf)⁻¹ = -1

namespace IsExceptionalCurve

variable {I : X.IdealSheafData} (k : Type u) [Field k] [I.subscheme.Over (Spec (.of k))]

/-- **The invariants of an exceptional curve over a field.** If an exceptional curve of the first
kind `E` is a scheme over a field `k`, then `E ≅ ℙ¹_κ` for an extension `κ` of `k`, by an
isomorphism over `k`, such that `dim_k H⁰(E, 𝒪_E) = [κ : k]`, `H¹(E, 𝒪_E)` vanishes, and the
normal sheaf of `E` has degree `-[κ : k]` over `k`. -/
theorem exists_algebra_finrank_cohomology_zero (h : I.IsExceptionalCurve) :
    ∃ (κ : Type u) (_ : Field κ) (_ : Algebra k κ) (e : projectiveLine κ ≅ I.subscheme),
      e.hom ≫ I.subscheme ↘ Spec (.of k) =
        (projectiveLine κ ↘ Spec (.of κ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) ∧
      finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) = finrank k κ ∧
      finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) = 0 ∧
      LineBundleClass.intersectionNumber k I.subschemeι
        (LineBundleClass.mk h.isEffectiveCartier.toInvertibleSheaf)⁻¹ = -finrank k κ := by
  obtain ⟨κ, _, e, he⟩ := h.exists_iso_projectiveLine
  obtain ⟨φ, hφ⟩ := exists_over_comp_specMap_eq
    (projectiveLine.bijective_baseRingToGlobalSections κ) (e.hom ≫ I.subscheme ↘ Spec (.of k))
  let := φ.toAlgebra
  let : (projectiveLine κ).Over (Spec (.of k)) := ⟨e.hom ≫ I.subscheme ↘ Spec (.of k)⟩
  -- As a scheme over `k` through `e`, `ℙ¹_κ` is a pullback of `E` along the identity of `Spec k`.
  have H : IsPullback e.inv (I.subscheme ↘ Spec (.of k)) (projectiveLine κ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := hid ▸ inferInstance
    exact .of_horiz_isIso ⟨by rw [hid, Category.comp_id]; exact e.inv_hom_id_assoc _⟩
  -- `ℙ¹_κ`, as a scheme over `k` through `e`, lies over `Spec κ` compatibly: this is `hφ`, as the
  -- structure morphism to `Spec k` was defined to be `e.hom ≫ (E ↘ Spec k)` and `algebraMap k κ`
  -- is `φ`.
  have hκ : (projectiveLine κ ↘ Spec (.of κ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      projectiveLine κ ↘ Spec (.of k) := hφ
  refine ⟨κ, inferInstance, inferInstance, e, hκ.symm, ?_, ?_, ?_⟩
  · rw [finrank_cohomology_trivial_eq_of_isPullback H,
      Scheme.Modules.finrank_cohomology_eq_finrank_mul hκ,
      (projectiveLine.cohomologyZeroTrivialLinearEquiv κ).finrank_eq, Module.finrank_self, mul_one]
  · rw [finrank_cohomology_trivial_eq_of_isPullback H]
    exact Module.finrank_zero_of_subsingleton
  · -- Transport the degree along `e` and then pass from `κ` to `k` by the tower law.
    have hE : I.subschemeι = e.inv ≫ e.hom ≫ I.subschemeι := (e.inv_hom_id_assoc _).symm
    rw [hE, LineBundleClass.intersectionNumber_def, ← LineBundleClass.pullback_comp,
      -- `e.inv` is a morphism over `k`, since `ℙ¹_κ` lies over `k` through `e.hom`.
      LineBundleClass.eulerDegree_pullback_of_isIso e.inv (e.inv_hom_id_assoc _),
      ← LineBundleClass.intersectionNumber_def,
      LineBundleClass.intersectionNumber_eq_finrank_mul _ hκ, he, mul_neg_one]

/-- **An exceptional curve has no first cohomology.** If an exceptional curve of the first kind
`E` is a scheme over a field `k`, then `dim_k H¹(E, 𝒪_E) = 0`. -/
theorem finrank_cohomology_one_trivial (h : I.IsExceptionalCurve) :
    finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) = 0 := by
  obtain ⟨κ, _, _, -, -, -, h₁, -⟩ := exists_algebra_finrank_cohomology_zero k h
  exact h₁

/-- **The self-intersection of an exceptional curve.** If an exceptional curve of the first kind
`E` is a scheme over a field `k`, then its self-intersection number over `k`, the degree over `k`
of its normal sheaf `𝒪_X(E)|_E`, is `(E · E) = -dim_k H⁰(E, 𝒪_E)`: minus the degree over `k` of
the field `Γ(E, 𝒪_E)`. -/
theorem intersectionNumber_self (h : I.IsExceptionalCurve) :
    LineBundleClass.intersectionNumber k I.subschemeι
        (LineBundleClass.mk h.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
      -finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) := by
  obtain ⟨κ, _, _, -, -, h₀, -, h₂⟩ := exists_algebra_finrank_cohomology_zero k h
  rw [h₂, h₀]

end IsExceptionalCurve

end AlgebraicGeometry.Scheme.IdealSheafData
