/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare.EmptyOpen

/-!
# Examples: `K(t) → K(u)`, `t ↦ u²`, is not distinguished with empty open part

For a field `K`, the map of rational function fields `K(t) → K(u)` sending `t` to `u²` has degree
two: its image is the intermediate field `K(u²)` of `K(u)`, and `[K(u) : K(u²)] = 2`
(`finrank_adjoin_X_sq`). The two spectra are isomorphic as abstract schemes (both are the spectrum
of a rational function field in one variable over `K`), but the specified morphism
`Spec K(u) ⟶ Spec K(t)` is not an isomorphism. So no elementary distinguished square over
`Spec K(t)` with empty open part has `p` isomorphic over `Spec K(t)` to it
(`isEmpty_iso_SpecMap_squareHom`), and the same holds over `Spec K(u²)` for the inclusion
`K(u²) → K(u)` (`isEmpty_iso_SpecMap_adjoin_X_sq`). For `K = ℚ` this is the `ℚ(t) → ℚ(u)` Check of
the elementary distinguished squares.
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

/-- `u²` is not a constant rational function. -/
theorem X_sq_ne_C : ¬ ∃ c : K, (RatFunc.X : RatFunc K) ^ 2 = RatFunc.C c := by
  rintro ⟨c, hc⟩
  have h := congrArg RatFunc.num hc
  rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.num_algebraMap, ← RatFunc.algebraMap_C,
    RatFunc.num_algebraMap] at h
  simpa using congrArg Polynomial.natDegree h

/-- **`K(u)` has degree two over `K(u²)`.** -/
theorem finrank_adjoin_X_sq : Module.finrank (adjoinXSq K) (RatFunc K) = 2 := by
  rw [adjoinXSq, RatFunc.finrank_eq_max_natDegree,
    ← RatFunc.algebraMap_X, ← map_pow, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- The isomorphism `K(t) ≃ K(u²)` sending `t` to `u²`. -/
noncomputable abbrev adjoinXSqEquiv : RatFunc K ≃ₐ[K] adjoinXSq K :=
  RatFunc.algEquivOfTranscendental _ (RatFunc.transcendental_of_ne_C _ (X_sq_ne_C K))

/-- The ring map `K(t) → K(u)` sending `t` to `u²`. -/
@[expose]
noncomputable def squareHom : RatFunc K →+* RatFunc K :=
  (algebraMap (adjoinXSq K) (RatFunc K)).comp (adjoinXSqEquiv K).toRingEquiv.toRingHom

theorem squareHom_apply (f : RatFunc K) : squareHom K f = (adjoinXSqEquiv K f : RatFunc K) :=
  rfl

@[simp]
theorem squareHom_X : squareHom K RatFunc.X = RatFunc.X ^ 2 := by
  rw [squareHom_apply, ← RatFunc.algebraMap_X, RatFunc.algEquivOfTranscendental_algebraMap,
    Polynomial.aeval_X, IntermediateField.AdjoinSimple.coe_gen, RatFunc.algebraMap_X]

/-- `K(t) → K(u)`, `t ↦ u²`, is not surjective, since its image `K(u²)` has codimension two. -/
theorem not_bijective_squareHom : ¬ Function.Bijective (squareHom K) := by
  intro h
  have hval : Function.Bijective (algebraMap (adjoinXSq K) (RatFunc K)) := by
    refine ⟨Subtype.val_injective, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := h.2 y
    exact ⟨adjoinXSqEquiv K x, rfl⟩
  have := Module.finrank_of_bijective_algebraMap hval
  rw [finrank_adjoin_X_sq] at this
  omega

/-- **The inclusion `K(u²) → K(u)` is not distinguished with empty `U`.** -/
theorem isEmpty_iso_SpecMap_adjoin_X_sq
    (Q : ElementaryDistinguishedSquare (Spec (.of (adjoinXSq K)))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap (adjoinXSq K) (RatFunc K))) :=
  Q.isEmpty_iso_of_not_isIso _ fun hi ↦ by
    have := Module.finrank_of_bijective_algebraMap (isIso_SpecMap_iff.1 hi)
    rw [finrank_adjoin_X_sq] at this
    omega

/-- **`K(t) → K(u)`, `t ↦ u²`, is not distinguished with empty `U`.** No elementary distinguished
square over `Spec K(t)` with empty open part has `p` isomorphic over `Spec K(t)` to the morphism
`Spec K(u) ⟶ Spec K(t)` of `squareHom`, although source and target are the same scheme. -/
theorem isEmpty_iso_SpecMap_squareHom
    (Q : ElementaryDistinguishedSquare (Spec (.of (RatFunc K)))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.map (CommRingCat.ofHom (squareHom K)))) :=
  Q.isEmpty_iso_of_not_isIso _ fun hi ↦ not_bijective_squareHom K (isIso_SpecMap_iff.1 hi)

/-- The case `ℚ(t) → ℚ(u)`, `t ↦ u²`. -/
example (Q : ElementaryDistinguishedSquare (Spec (.of (RatFunc ℚ)))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.map (CommRingCat.ofHom (squareHom ℚ)))) :=
  isEmpty_iso_SpecMap_squareHom ℚ Q

end TauCeti.AlgebraicGeometry.DistinguishedSquareRatFuncExample
