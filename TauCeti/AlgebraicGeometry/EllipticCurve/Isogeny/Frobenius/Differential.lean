/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability

/-!
# The Frobenius isogeny kills the differentials

Over a finite field, the Frobenius isogeny of a Weierstrass curve pulls every differential of the
function field back to zero. This is the differential-level form of its inseparability: the
invariant differential in particular is pulled back to `0`. The base-changed Frobenius over any
field extension also kills the invariant differential.

## Main results

* `TauCeti.Isogeny.pullbackDifferential_frobeniusIsogeny`: `π^*` is the zero map on differentials.
* `TauCeti.Isogeny.pullbackDifferential_baseChangeFrobenius_invariantDifferential`: the
  base-changed Frobenius kills the invariant differential over any field extension.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`) has the corresponding statements for the invariant
differential only, `omegaPullbackCoeff_frobenius` and
`frobenius_pullbackKaehler_invariantDifferential` in `BridgeFrobenius.lean`; the first statement
here is for every differential of the function field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.4.2, III.5.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F)

/-- **The Frobenius isogeny pulls every differential back to zero.** -/
@[simp]
theorem pullbackDifferential_frobeniusIsogeny : (frobeniusIsogeny W).pullbackDifferential = 0 := by
  -- `π^*(d f) = d (f ^ q) = q • f ^ (q - 1) • d f`, and `q = 0` in `K(W)`; the `d f` span.
  have hq : ((Nat.card F : ℕ) : W.FunctionField) = 0 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, ← map_natCast (algebraMap F W.FunctionField),
      FiniteField.cast_card_eq_zero, map_zero]
  refine LinearMap.ext fun η ↦ ?_
  have hη : η ∈ Submodule.span W.FunctionField
      (Set.range (KaehlerDifferential.D F W.FunctionField)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hη using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, rfl⟩ := h
    rw [pullbackDifferential_D, fieldPullback_frobeniusIsogeny_apply, Derivation.leibniz_pow,
      ← Nat.cast_smul_eq_nsmul W.FunctionField, hq, zero_smul, LinearMap.zero_apply]
  | zero => rw [map_zero, map_zero]
  | add _ _ _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c _ _ h => simp only [pullbackDifferential_smul, h, LinearMap.zero_apply, smul_zero]

variable {K : Type*} [Field K] [Algebra F K]

/-- The base-changed Frobenius kills the invariant differential, over any field extension. -/
@[simp]
theorem pullbackDifferential_baseChangeFrobenius_invariantDifferential :
    (baseChangeFrobenius K W).pullbackDifferential
      (invariantDifferential (W⁄K).toAffine) = 0 := by
  rw [baseChangeFrobenius_def]
  -- The transfer lemma uses `W.map`; rewriting does not unfold the semireducible base change
  -- in the differential's type, so present that type explicitly.
  change ((frobeniusIsogeny W).map (algebraMap F K)).pullbackDifferential
    (invariantDifferential (W.map (algebraMap F K))) = 0
  simpa only [pullbackDifferential_frobeniusIsogeny, LinearMap.zero_apply, map_zero] using
    (mapDifferential_pullback_invariantDifferential (frobeniusIsogeny W) (algebraMap F K)).symm

end TauCeti.Isogeny

end
