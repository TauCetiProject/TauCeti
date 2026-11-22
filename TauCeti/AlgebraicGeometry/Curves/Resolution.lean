/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Modification
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.AlgebraicGeometry.Birational.KrullDimension
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Finite
import TauCeti.AlgebraicGeometry.Normalization.Regular

/-!
# Resolution of curves over an arbitrary field

Let `X` be a proper integral curve over an arbitrary field `k` (`X.IsCurveOver k`). Birational
equivalence preserves Krull dimension over a field
(`AlgebraicGeometry.Scheme.Birational.topologicalKrullDim_eq_of_locallyOfFiniteType`), so any
reduced modification of `X` over `k` is again a curve over `k`
(`AlgebraicGeometry.Scheme.IsCurveOver.of_isModification`). By Japanese finiteness over fields, the
normalization of `X` in its function field `k(X)` is finite over `X`, regular
(`AlgebraicGeometry.Scheme.IsCurveOver.isRegular_normalization`), and a curve over `k`
(`AlgebraicGeometry.Scheme.IsCurveOver.isCurveOver_normalization`).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section ResolutionOfCurves

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Any reduced scheme mapping by a `k`-modification to a curve over `k` is itself a curve over
`k`: it is birational to `X` hence irreducible, proper over `k` by composition, and has the same
Krull dimension one. -/
theorem IsCurveOver.of_isModification [Y.Over (Spec (.of k))] [X.IsCurveOver k] [IsReduced Y]
    (f : Y ⟶ X) [IsModification f] [f.IsOver (Spec (.of k))] : Y.IsCurveOver k := by
  have : IrreducibleSpace Y := (IsModification.birational f).irreducibleSpace
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have hproper : IsProper (Y ↘ Spec (.of k)) := by
    rw [← HomIsOver.comp_over (f := f) (S := Spec (.of k))]
    infer_instance
  refine isCurveOver_iff.mpr ⟨inferInstance, hproper, ?_⟩
  rw [(IsModification.birational f).topologicalKrullDim_eq_of_locallyOfFiniteType
    (Y ↘ Spec (.of k)) (X ↘ Spec (.of k))]
  exact IsCurveOver.topologicalKrullDim_eq_one k

/-- **Resolution of curves over an arbitrary field.** For any curve `X` over a field `k`, the
normalization of `X` in its function field `k(X)` is a regular scheme. No perfectness hypothesis on
`k` is needed, since fields are universally Japanese. -/
theorem IsCurveOver.isRegular_normalization [X.IsCurveOver k] :
    IsRegular (X.fromSpecStalk (genericPoint X)).normalization := by
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  have := IsCurveOver.isNoetherian k X
  exact isRegular_normalization_fromSpecStalk_genericPoint
    (IsCurveOver.topologicalKrullDim_eq_one k).le

/-- The normalization of a curve `X` over `k` in its function field, equipped with any structure
morphism over `Spec k` compatible with `fromNormalization`, is a curve over `k`. -/
instance IsCurveOver.isCurveOver_normalization [X.IsCurveOver k]
    [((X.fromSpecStalk (genericPoint X)).normalization).Over (Spec (.of k))]
    [((X.fromSpecStalk (genericPoint X)).fromNormalization).IsOver (Spec (.of k))] :
    ((X.fromSpecStalk (genericPoint X)).normalization).IsCurveOver k := by
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  exact IsCurveOver.of_isModification k (X.fromSpecStalk (genericPoint X)).fromNormalization

end ResolutionOfCurves

end AlgebraicGeometry.Scheme

end
