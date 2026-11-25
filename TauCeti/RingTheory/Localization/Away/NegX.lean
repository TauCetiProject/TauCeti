/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The involution `X ↦ -X` of `k[X, X⁻¹]`

For a commutative ring `k`, the substitution `X ↦ -X` of `k[X]` sends `X` to a unit of the
localization `k[X, X⁻¹]` of `k[X]` away from `X`, so it extends to a ring automorphism of
`k[X, X⁻¹]`, which is its own inverse. The ring `k[X, X⁻¹]` is nontrivial when `k` is.

## Main definitions

* `TauCeti.Localization.negAwayX`: the automorphism `X ↦ -X` of `k[X, X⁻¹]`.

## Main results

* `TauCeti.Localization.negAwayX_algebraMap`: `negAwayX k` substitutes `-X` for `X` in
  polynomials.
* `TauCeti.Localization.negAwayX_symm`: `negAwayX k` is its own inverse.
* `TauCeti.Localization.nontrivial_awayX`: `k[X, X⁻¹]` is nontrivial over a nontrivial ring.
-/

public section

open Polynomial

namespace TauCeti.Localization

variable (k : Type*) [CommRing k]

/-- The automorphism `X ↦ -X` of `k[X, X⁻¹]`, the localization of `k[X]` away from `X`. -/
noncomputable def negAwayX : Localization.Away (X : k[X]) ≃+* Localization.Away (X : k[X]) :=
  let f : Localization.Away (X : k[X]) →+* Localization.Away (X : k[X]) :=
    IsLocalization.Away.lift X (g := (algebraMap k[X] (Localization.Away (X : k[X]))).comp
      (aeval (R := k) (-X : k[X])).toRingHom) (by
        simpa using (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (X : k[X]))
          (X : k[X])).neg)
  have hf : f.comp f = RingHom.id _ := IsLocalization.ringHom_ext (.powers (X : k[X])) <| by
    ext p <;> simp [f, IsLocalization.Away.lift_eq]
  RingEquiv.ofRingHom f f hf hf

/-- `negAwayX k` substitutes `-X` for `X` in polynomials. -/
@[simp]
theorem negAwayX_algebraMap (p : k[X]) :
    negAwayX k (algebraMap k[X] (Localization.Away (X : k[X])) p) =
      algebraMap k[X] (Localization.Away (X : k[X])) (aeval (-X) p) := by
  simp [negAwayX, IsLocalization.Away.lift_eq]

/-- `negAwayX k` is an involution. -/
@[simp]
theorem negAwayX_negAwayX (x : Localization.Away (X : k[X])) :
    negAwayX k (negAwayX k x) = x := by
  suffices ((negAwayX k).toRingHom.comp (negAwayX k).toRingHom) = RingHom.id _ from
    congr($this x)
  refine IsLocalization.ringHom_ext (.powers (X : k[X])) ?_
  ext p <;> simp

/-- `negAwayX k` is its own inverse. -/
@[simp]
theorem negAwayX_symm : (negAwayX k).symm = negAwayX k :=
  RingEquiv.ext fun x ↦ (negAwayX k).symm_apply_eq.2 (negAwayX_negAwayX k x).symm

/-- The localization `k[X, X⁻¹]` of `k[X]` away from `X` is nontrivial when `k` is. -/
instance nontrivial_awayX [Nontrivial k] : Nontrivial (Localization.Away (X : k[X])) :=
  (IsLocalization.Away.lift (X : k[X]) (g := evalRingHom 1) (by simp)).domain_nontrivial

end TauCeti.Localization
