/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.Topology.KrullDimension.Basic
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# The normalization of a curve

Let `X` be a curve over a field `k`: an integral scheme, proper of dimension one over `k`
(`AlgebraicGeometry.Scheme.IsCurveOver`). Its normalization `X^ν` is the normalization of `X` in its
function field, along `Spec k(X) ⟶ X`. This file shows that `X^ν` is again a curve over `k`, and
that it is regular, so that its codimension-one local rings are discrete valuation rings.

The normalization is finite over `X`
(`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType`): the rings of
sections of affine opens of `X` are domains of finite type over `k`, hence Japanese. It is therefore
proper over `k` and regular
(`TauCeti.AlgebraicGeometry.isRegular_normalization_fromSpecStalk_genericPoint`). It is surjective
onto `X` (`AlgebraicGeometry.Scheme.Hom.isDominant_fromNormalization`), so it has dimension exactly
one: a proper specialization in `X` lifts to one in `X^ν`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_isCurveOver`: the normalization of a
  curve is finite over it.
* `TauCeti.AlgebraicGeometry.isCurveOver_normalization`: the normalization of a curve is a curve.
* `TauCeti.AlgebraicGeometry.isRegular_normalization_of_isCurveOver`: the normalization of a curve
  is regular.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.3.8 (normalization).
* The Stacks Project, Lemma 33.41.1 (0C45).
-/

public section

open CategoryTheory AlgebraicGeometry Topology

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]

/-- The normalization of a curve in its function field is finite over the curve. This is a
theorem rather than an instance: the field `k` does not occur in the conclusion. -/
theorem isFinite_fromNormalization_of_isCurveOver :
    IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization :=
  isFinite_fromNormalization_of_locallyOfFiniteType (X ↘ Spec (.of k))

/-- **The normalization of a curve is a curve.** The normalization of a curve over `k` in its
function field is integral, proper over `k` and of dimension one. -/
instance isCurveOver_normalization :
    (X.fromSpecStalk (genericPoint X)).normalization.IsCurveOver k := by
  set f := X.fromSpecStalk (genericPoint X)
  have : IsFinite f.fromNormalization := isFinite_fromNormalization_of_isCurveOver k X
  have hdimX := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k
  refine Scheme.isCurveOver_iff.mpr ⟨inferInstance, ?_, le_antisymm ?_ ?_⟩
  · rw [← comp_over f.fromNormalization (Spec (.of k))]
    infer_instance
  · exact f.fromNormalization.topologicalKrullDim_le.trans hdimX.le
  · -- `X` has a point other than its generic point, since it has dimension one
    obtain ⟨p, hp⟩ : ∃ p : X, p ≠ genericPoint X := by
      by_contra! h
      have : Subsingleton X := ⟨fun a b ↦ (h a).trans (h b).symm⟩
      exact one_ne_zero (hdimX.symm.trans (topologicalKrullDim_eq_zero_iff_subsingleton.mpr this))
    -- a preimage of `p` is a proper specialization of the generic point of the normalization
    obtain ⟨q, rfl⟩ := f.fromNormalization.surjective p
    refine ((genericPoint_spec f.normalization).specializes (Set.mem_univ q))
      |>.one_le_topologicalKrullDim_of_ne fun hq ↦ hp ?_
    rw [← hq]
    exact f.fromNormalization.genericPoint_eq_of_isDominant

/-- The normalization of a curve is regular, so its codimension-one local rings are discrete
valuation rings. -/
instance isRegular_normalization_of_isCurveOver :
    IsRegular (X.fromSpecStalk (genericPoint X)).normalization := by
  have := isFinite_fromNormalization_of_isCurveOver k X
  have := Scheme.IsCurveOver.isNoetherian k X
  exact isRegular_normalization_fromSpecStalk_genericPoint
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le

end TauCeti.AlgebraicGeometry
