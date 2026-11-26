/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare.EmptyOpen
public import TauCeti.FieldTheory.RatFunc.PowerTower
public import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Examples: `K(t) → K(u)`, `t ↦ u²`, is not distinguished with empty open part

For a field `K`, the map of rational function fields `K(t) → K(u)` sending `t` to `u²` has degree
two: its image is the intermediate field `K(u²)` of `K(u)`, and `[K(u) : K(u²)] = 2`
(`TauCeti.RatFunc.finrank_adjoin_X_pow`). The two spectra are isomorphic as abstract schemes (both
are the spectrum of a rational function field in one variable over `K`), but the specified
morphism `Spec K(u) ⟶ Spec K(t)` is not an isomorphism. So no elementary distinguished square over
`Spec K(t)` with empty open part has `p` isomorphic over `Spec K(t)` to it
(`isEmpty_iso_SpecMap_squareHom`), and the same holds over `Spec K(u²)` for the inclusion
`K(u²) → K(u)` (`isEmpty_iso_SpecMap_adjoinXSq`). For `K = ℚ` this gives the example
`ℚ(t) → ℚ(u)`, `t ↦ u²`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.DistinguishedSquareRatFuncExample

open TauCeti.AlgebraicGeometry.Scheme

universe u

variable (K : Type u) [Field K]

/-- The intermediate field `K(u²)` of the rational function field `K(u)`. -/
noncomputable abbrev adjoinXSq : IntermediateField K (RatFunc K) :=
  IntermediateField.adjoin K {(RatFunc.X : RatFunc K) ^ 2}

/-- `u²` is transcendental over `K` in `K(u)`. -/
theorem transcendental_X_sq : Transcendental K (RatFunc.X ^ 2 : RatFunc K) :=
  RatFunc.transcendental_X.pow two_pos

/-- The `K(t)`-algebra structure on `K(u)` in which `t` acts as `u²`
(`TauCeti.ratFuncAlgebraOfTranscendental`). -/
noncomputable abbrev squareAlgebra : Algebra (RatFunc K) (RatFunc K) :=
  ratFuncAlgebraOfTranscendental (transcendental_X_sq K)

/-- The ring map `K(t) → K(u)` sending `t` to `u²`: the structure map of `squareAlgebra`. -/
noncomputable def squareHom : RatFunc K →+* RatFunc K :=
  letI := squareAlgebra K
  algebraMap (RatFunc K) (RatFunc K)

/-- `squareHom` is the structure map of `squareAlgebra`. -/
theorem squareHom_def :
    letI := squareAlgebra K
    squareHom K = algebraMap (RatFunc K) (RatFunc K) := by
  unfold squareHom
  rfl

@[simp]
theorem squareHom_X : squareHom K RatFunc.X = RatFunc.X ^ 2 := by
  rw [squareHom_def]
  exact algebraMap_ratFuncAlgebraOfTranscendental_X _

/-- `squareHom` fixes the constants from `K`. -/
theorem squareHom_algebraMap (a : K) :
    squareHom K (algebraMap K (RatFunc K) a) = algebraMap K (RatFunc K) a := by
  let _ := squareAlgebra K
  have := isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_X_sq K)
  rw [squareHom_def]
  exact (IsScalarTower.algebraMap_apply K (RatFunc K) (RatFunc K) a).symm

@[simp]
theorem squareHom_C (a : K) : squareHom K (RatFunc.C a) = RatFunc.C a := by
  simpa using squareHom_algebraMap K a

/-- **The inclusion `K(u²) → K(u)` is not distinguished with empty `U`.** -/
theorem isEmpty_iso_SpecMap_adjoinXSq
    (Q : ElementaryDistinguishedSquare (Spec (.of (adjoinXSq K)))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap (adjoinXSq K) (RatFunc K))) :=
  DistinguishedSquareEmptyOpenExample.isEmpty_iso_SpecMap_of_finrank_ne_one _ _ (by simp) Q

/-- **`K(t) → K(u)`, `t ↦ u²`, is not distinguished with empty `U`.** No elementary distinguished
square over `Spec K(t)` with empty open part has `p` isomorphic over `Spec K(t)` to the morphism
`Spec K(u) ⟶ Spec K(t)` of `squareHom`, although source and target are the same scheme. -/
theorem isEmpty_iso_SpecMap_squareHom
    (Q : ElementaryDistinguishedSquare (Spec (.of (RatFunc K)))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.map (CommRingCat.ofHom (squareHom K)))) := by
  let _ := squareAlgebra K
  have := isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_X_sq K)
  rw [squareHom_def]
  refine DistinguishedSquareEmptyOpenExample.isEmpty_iso_SpecMap_of_finrank_ne_one _ _ ?_ Q
  rw [← finrank_adjoin_algebraMap_X (k := K), algebraMap_ratFuncAlgebraOfTranscendental_X,
    RatFunc.finrank_adjoin_X_pow]
  decide

/-- The case `ℚ(t) → ℚ(u)`, `t ↦ u²`. -/
example (Q : ElementaryDistinguishedSquare (Spec (.of (RatFunc ℚ)))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.map (CommRingCat.ofHom (squareHom ℚ)))) :=
  isEmpty_iso_SpecMap_squareHom ℚ Q

end TauCeti.AlgebraicGeometry.DistinguishedSquareRatFuncExample
