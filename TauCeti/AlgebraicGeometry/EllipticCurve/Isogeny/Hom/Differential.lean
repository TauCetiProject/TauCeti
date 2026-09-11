/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Derivation

/-!
# The pullback of the invariant differential is additive in the morphism

A morphism `f : W₁ → W₂` of elliptic curves pulls the invariant differential `ω₂` of `W₂` back to a
differential `f^*ω₂` on `W₁`: along the isogeny when `f` is nonzero, and to `0` when `f = 0`. This
file proves that the assignment `f ↦ f^*ω₂` is additive (Silverman III.5.2),
`(f + g)^*ω₂ = f^*ω₂ + g^*ω₂`, together with `(-f)^*ω₂ = -f^*ω₂`.

The pullback is functorial in the morphism (`pullbackDifferential_id` and
`pullbackDifferential_comp`), and additivity makes `f ↦ f^*ω₂` compatible with the group
structure of `Hom W₁ W₂`: the pullback of the invariant differential along a sum, a difference
or a negative of morphisms is computed termwise. Its first use is the separability of `1 − π`
over a finite field, `TauCeti.Isogeny.isSeparable_oneSubFrobeniusIsogeny`:
`(1 − π)^*ω = ω − π^*ω = ω ≠ 0`.

## Main definitions

* `TauCeti.Isogeny.Hom.pullbackDifferential`: the pullback of differentials along a morphism.

## Main results

* `TauCeti.Isogeny.Hom.pullbackDifferential_add_invariantDifferential`: `(f + g)^*ω = f^*ω + g^*ω`.
* `TauCeti.Isogeny.Hom.pullbackDifferential_neg_invariantDifferential`: `(-f)^*ω = -f^*ω`.
* `TauCeti.Isogeny.Hom.pullbackDifferential_sub_invariantDifferential`: `(f - g)^*ω = f^*ω - g^*ω`.
* `TauCeti.Isogeny.Hom.pullbackDifferential_id` and `pullbackDifferential_comp`: the pullback is
  functorial in the morphism.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`) states the additivity only in the form
`(1 + α)^*ω = ω + α^*ω` for an endomorphism `α`, as `kaehlerD_addPullback_x_eq_one_add_smul_omega`
in `RouteBGeneral.lean`, and for a scalar coefficient `omegaPullbackCoeff` of the pulled-back `d x`
rather than for the differential. Here the statement is for two arbitrary morphisms
`f, g : W₁ → W₂` and for the pulled-back differential itself; nothing is taken from the source.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5.2.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

namespace Hom

open scoped Classical in
/-- **The pullback of differentials along a morphism**: the pullback along the isogeny for a nonzero
morphism, and zero for the zero morphism. -/
noncomputable def pullbackDifferential (f : Hom W₁ W₂) :
    KaehlerDifferential F W₂.FunctionField →ₗ[F] KaehlerDifferential F W₁.FunctionField :=
  if hf : f = 0 then 0 else (toIsogeny hf).pullbackDifferential

@[simp]
theorem pullbackDifferential_zero : (0 : Hom W₁ W₂).pullbackDifferential = 0 :=
  dite_eq_left_of_eq_true (eq_true rfl)

@[simp]
theorem pullbackDifferential_ofIsogeny (φ : Isogeny W₁ W₂) :
    (ofIsogeny φ).pullbackDifferential = φ.pullbackDifferential := by
  rw [pullbackDifferential, dite_eq_right_of_eq_false (eq_false (ofIsogeny_ne_zero φ)),
    toIsogeny_ofIsogeny]

/-- **The identity morphism pulls differentials back trivially.** -/
@[simp]
theorem pullbackDifferential_id (W : WeierstrassCurve.Affine F) :
    (Hom.id W).pullbackDifferential = LinearMap.id := by
  rw [id_def, pullbackDifferential_ofIsogeny, Isogeny.pullbackDifferential_id]

/-- **The pullback of differentials along morphisms is functorial**: pulling back along a composite
is composing the pullbacks, in the reverse order. -/
@[simp]
theorem pullbackDifferential_comp {W₃ : WeierstrassCurve.Affine F} (g : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (g.comp f).pullbackDifferential = f.pullbackDifferential ∘ₗ g.pullbackDifferential := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp only [Hom.comp_zero, pullbackDifferential_zero, LinearMap.zero_comp]
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp only [Hom.zero_comp, pullbackDifferential_zero, LinearMap.comp_zero]
  rw [ofIsogeny_comp_ofIsogeny, pullbackDifferential_ofIsogeny, pullbackDifferential_ofIsogeny,
    pullbackDifferential_ofIsogeny, Isogeny.pullbackDifferential_comp]

/-- **Negation negates the pullback of the invariant differential.** -/
@[simp]
theorem pullbackDifferential_neg_invariantDifferential (f : Hom W₁ W₂) :
    (-f).pullbackDifferential (invariantDifferential W₂) =
      -f.pullbackDifferential (invariantDifferential W₂) := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [neg_zero, pullbackDifferential_zero, LinearMap.zero_apply, _root_.neg_zero]
  · rw [neg_ofIsogeny, pullbackDifferential_ofIsogeny, pullbackDifferential_ofIsogeny,
      Isogeny.pullbackDifferential_comp, LinearMap.comp_apply,
      pullbackDifferential_negIsogeny_invariantDifferential, map_neg]

variable [W₂.IsElliptic]

/-- **The pullback of the invariant differential is additive in the morphism**
(Silverman III.5.2): `(f + g)^*ω = f^*ω + g^*ω`. -/
@[simp]
theorem pullbackDifferential_add_invariantDifferential (f g : Hom W₁ W₂) :
    (f + g).pullbackDifferential (invariantDifferential W₂) =
      f.pullbackDifferential (invariantDifferential W₂) +
        g.pullbackDifferential (invariantDifferential W₂) := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [zero_add, pullbackDifferential_zero, LinearMap.zero_apply, zero_add]
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · rw [add_zero, pullbackDifferential_zero, LinearMap.zero_apply, add_zero]
  by_cases h : φ.pullback.tautologicalPoint + ψ.pullback.tautologicalPoint = 0
  · -- The tautological points cancel: `g = -f`.
    have hψ : ofIsogeny ψ = -ofIsogeny φ := tautologicalPoint_injective (by
      rw [tautologicalPoint_neg, tautologicalPoint_ofIsogeny, tautologicalPoint_ofIsogeny,
        eq_neg_iff_add_eq_zero, add_comm]
      exact h)
    rw [hψ, add_neg_cancel, pullbackDifferential_zero, LinearMap.zero_apply,
      pullbackDifferential_neg_invariantDifferential, add_neg_cancel]
  · -- The sum is the isogeny with pullback `CoordinatePullback.add`, whose tautological point is
    -- the sum of the two tautological points; read `ω` at all three points.
    set χ : Isogeny W₁ W₂ := ⟨φ.pullback.add ψ.pullback h,
      CoordinatePullback.mapsInfinity_add _ _ φ.mapsInfinity ψ.mapsInfinity h⟩ with hχ
    have hχP : χ.pullback.tautologicalPoint =
        φ.pullback.tautologicalPoint + ψ.pullback.tautologicalPoint :=
      CoordinatePullback.tautologicalPoint_add _ _ h
    have hu := evalEval_polynomialY_tautologicalPoint_ne_zero χ
    rw [hχP] at hu
    simp only [ofIsogeny_add_ofIsogeny φ ψ h, ← hχ, pullbackDifferential_ofIsogeny,
      pullbackDifferential_invariantDifferential, hχP]
    exact Point.inv_smul_derivation_xCoord_add (KaehlerDifferential.D F W₁.FunctionField)
      (CoordinatePullback.tautologicalPoint_ne_zero _)
      (CoordinatePullback.tautologicalPoint_ne_zero _) h
      (fun _ ↦ evalEval_polynomialY_tautologicalPoint_ne_zero φ)
      (fun _ ↦ evalEval_polynomialY_tautologicalPoint_ne_zero ψ) hu

/-- **The pullback of the invariant differential respects subtraction.** -/
@[simp]
theorem pullbackDifferential_sub_invariantDifferential (f g : Hom W₁ W₂) :
    (f - g).pullbackDifferential (invariantDifferential W₂) =
      f.pullbackDifferential (invariantDifferential W₂) -
        g.pullbackDifferential (invariantDifferential W₂) := by
  rw [sub_eq_add_neg, pullbackDifferential_add_invariantDifferential,
    pullbackDifferential_neg_invariantDifferential, sub_eq_add_neg]

end Hom

end TauCeti.Isogeny

end
