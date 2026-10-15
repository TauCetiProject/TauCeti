/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
public import TauCeti.FieldTheory.KrullTopology

/-!
# Galois conjugation of changes of variables

An admissible change of variables with algebraic coefficients has a locally constant orbit
under the Krull topology. This gives continuity for the cocycles attached to pointed twists
of Weierstrass curves. Descent is developed in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisDescent.lean`.

Conjugation by algebra automorphisms is an action (`VariableChange.map_map_algEquiv`).
-/

public section

namespace WeierstrassCurve.VariableChange

/-- Conjugating a change of variables by `σ` and then by `τ` is conjugating by `τ * σ`. -/
lemma map_map_algEquiv {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    (C : VariableChange L) (σ τ : L ≃ₐ[R] L) :
    (C.map (σ : L →+* L)).map (τ : L →+* L) = C.map ((τ * σ : L ≃ₐ[R] L) : L →+* L) := by
  rw [map_map]
  exact congrArg C.map (RingHom.ext fun x ↦ (AlgEquiv.mul_apply τ σ x).symm)

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Conjugation of a change of variables with integral coefficients is locally constant
for the Krull topology. No algebraicity assumption on the whole extension is needed. -/
theorem isLocallyConstant_map (C : VariableChange L)
    (hu : IsIntegral K (C.u : L)) (hr : IsIntegral K C.r)
    (hs : IsIntegral K C.s) (ht : IsIntegral K C.t) :
    IsLocallyConstant fun σ : Gal(L/K) ↦ C.map (σ : L →+* L) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ₀ ↦ ?_
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 hu.isLocallyConstant_apply σ₀,
    (IsLocallyConstant.iff_eventually_eq _).1 hr.isLocallyConstant_apply σ₀,
    (IsLocallyConstant.iff_eventually_eq _).1 hs.isLocallyConstant_apply σ₀,
    (IsLocallyConstant.iff_eventually_eq _).1 ht.isLocallyConstant_apply σ₀]
    with σ hu hr hs ht
  -- `map` applies σ coefficientwise; `Units.map` coerces to the image of the unit value.
  exact VariableChange.ext (Units.ext hu) hr hs ht

/-- Over an algebraic extension, every change of variables has a locally constant Galois orbit. -/
theorem isLocallyConstant_map_of_isAlgebraic [Algebra.IsAlgebraic K L] (C : VariableChange L) :
    IsLocallyConstant fun σ : Gal(L/K) ↦ C.map (σ : L →+* L) :=
  C.isLocallyConstant_map (Algebra.IsIntegral.isIntegral _) (Algebra.IsIntegral.isIntegral _)
    (Algebra.IsIntegral.isIntegral _) (Algebra.IsIntegral.isIntegral _)

end WeierstrassCurve.VariableChange
