/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Finite
public import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
import TauCeti.Topology.KrullDimension.Basic
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# The normalization genus of a curve

Let `X` be a curve over a field `k`: an integral scheme, proper of dimension one over `k`
(`AlgebraicGeometry.Scheme.IsCurveOver`). Its normalization `X^ν` is the normalization of `X` in its
function field, along `Spec k(X) ⟶ X`. This file shows that `X^ν` is again a curve over `k`, now
with discrete valuation rings as codimension-one local rings, so that `H¹(X^ν, 𝒪)` is
finite-dimensional, and defines the **normalization genus** of `X` as the genus of `X^ν`. It is the
genus attached to an irreducible component in the stability conditions for curves and stable maps.

The normalization is finite over `X`
(`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType`): the rings of
sections of affine opens of `X` are domains of finite type over `k`, hence Japanese. It is therefore
proper over `k` and regular
(`TauCeti.AlgebraicGeometry.isRegular_normalization_fromSpecStalk_genericPoint`). It is surjective
onto `X` (`TauCeti.AlgebraicGeometry.surjective_fromNormalization_of_locallyOfFiniteType`), so it
has dimension exactly one: a proper specialization in `X` lifts to one in `X^ν`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isCurveOver_normalization`: the normalization of a curve is a curve.
* `AlgebraicGeometry.Scheme.normalizationGenus`: the genus of the normalization of a curve.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.3.8 (normalization) and Chapter IV, §1.
* The Stacks Project, Lemma 33.41.1 (0C45).
-/

public section

open CategoryTheory AlgebraicGeometry Topology

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]

/-- **The normalization of a curve is a curve.** The normalization of a curve over `k` in its
function field is integral, proper over `k` and of dimension one. -/
instance isCurveOver_normalization :
    (X.fromSpecStalk (genericPoint X)).normalization.IsCurveOver k := by
  set f := X.fromSpecStalk (genericPoint X)
  have : IsFinite f.fromNormalization := isFinite_fromNormalization_of_locallyOfFiniteType k X
  have hdimX := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k
  refine Scheme.isCurveOver_iff.mpr ⟨inferInstance, ?_, le_antisymm ?_ ?_⟩
  · rw [normalization_over_hom]
    infer_instance
  · exact f.fromNormalization.topologicalKrullDim_le.trans hdimX.le
  · -- `X` has a point other than its generic point, since it has dimension one
    obtain ⟨p, hp⟩ : ∃ p : X, p ≠ genericPoint X := by
      by_contra! h
      have : Subsingleton X := ⟨fun a b ↦ (h a).trans (h b).symm⟩
      exact one_ne_zero (hdimX.symm.trans (topologicalKrullDim_eq_zero_iff_subsingleton.mpr this))
    -- a preimage of `p` is a proper specialization of the generic point of the normalization
    have hsurj := surjective_fromNormalization_of_locallyOfFiniteType k X
    obtain ⟨q, rfl⟩ := hsurj p
    refine one_le_topologicalKrullDim_of_specializes
      ((genericPoint_spec f.normalization).specializes (Set.mem_univ q)) fun hq ↦ hp ?_
    rw [← hq]
    refine IsGenericPoint.eq ?_ (genericPoint_spec X)
    have := (genericPoint_spec f.normalization).image f.fromNormalization.continuous
    rwa [Set.image_univ_of_surjective hsurj, closure_univ] at this

/-- The normalization of a curve is regular, so its codimension-one local rings are discrete
valuation rings. -/
instance isRegular_normalization_of_isCurveOver :
    IsRegular (X.fromSpecStalk (genericPoint X)).normalization := by
  have : IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType k X
  have := Scheme.IsCurveOver.isNoetherian k X
  exact isRegular_normalization_fromSpecStalk_genericPoint
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le

/-- The first cohomology of the structure sheaf of the normalization of a curve is
finite-dimensional. -/
instance finiteDimensional_cohomology_one_normalization :
    FiniteDimensional k (Scheme.Modules.Cohomology
      (InvertibleSheaf.trivial (X.fromSpecStalk (genericPoint X)).normalization).obj 1) := by
  have : ∀ y : CodimensionOnePoint (X.fromSpecStalk (genericPoint X)).normalization,
      IsDiscreteValuationRing
        ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk (y : _)) :=
    fun _ ↦ inferInstance
  exact finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]

/-- The **normalization genus** (geometric genus) of a curve `X` over a field `k`: the genus
`dim_k H¹(X^ν, 𝒪)` of its normalization `X^ν` in its function field. It is the genus of an
irreducible component used in stability conditions for curves and maps. -/
noncomputable def normalizationGenus : ℕ :=
  (X.fromSpecStalk (genericPoint X)).normalization.genus k

/-- The normalization genus is the genus of the normalization. -/
theorem normalizationGenus_def :
    X.normalizationGenus k = (X.fromSpecStalk (genericPoint X)).normalization.genus k :=
  normalizationGenus.eq_def k X

end AlgebraicGeometry.Scheme
