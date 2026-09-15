/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import TauCeti.FieldTheory.IntermediateField.FieldRange
import Mathlib.RingTheory.Unramified.Field

/-!
# The pullback of differentials along an isogeny, and separability

An isogeny `φ : W₁ → W₂` pulls differentials back along its function-field pullback,
`φ^* : Ω[K(W₂)/F] → Ω[K(W₁)/F]`. This file packages that map, records its basic properties, and
proves the differential criterion for separability: `φ` is separable exactly when `φ^*ω₂ ≠ 0`,
where `ω₂` is the invariant differential of `W₂` (Silverman II.4.2(c)).

## Main definitions

* `TauCeti.Isogeny.pullbackDifferential`: the pullback of differentials along an isogeny, the map
  `KaehlerDifferential.mapSemilinear` along the function-field pullback packaged `F`-linearly.

## Main results

* `TauCeti.Isogeny.pullbackDifferential_D` and `pullbackDifferential_smul`: the pullback of `d f` is
  `d (φ^* f)`, and the pullback is semilinear over the function-field pullback.
* `TauCeti.Isogeny.pullbackDifferential_id` and `pullbackDifferential_comp`: the pullback is
  functorial.
* `TauCeti.Isogeny.pullbackDifferential_invariantDifferential`: `φ^*ω₂` is `dx / W_Y` read at the
  tautological point of `φ`, and `pullbackDifferential_negIsogeny_invariantDifferential`: negation
  pulls `ω` back to `-ω`.
* `TauCeti.Isogeny.evalEval_polynomialY_tautologicalPoint_ne_zero`: the denominator `W_Y` does not
  vanish at the tautological point of an isogeny.
* `TauCeti.Isogeny.isSeparable_iff_pullbackDifferential_ne_zero`: **the differential criterion for
  separability** — the isogeny is separable if and only if it pulls the invariant differential back
  to a nonzero differential.

## Provenance

The criterion is Silverman II.4.2(c). The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0,
commit `513e83879e2f8cbc626eb9e04d660e92be16ccba`) proves it for endomorphisms as
`isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`, through
`isSeparable_iff_pullbackKaehler_injective` and, in `Curves/Differentials.lean`,
`pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`. Here it is stated for any isogeny, on
the pulled-back differential itself.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.4.2, III.5.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The pullback of differentials along an isogeny**, `φ^* : Ω[K(W₂)/F] → Ω[K(W₁)/F]`: the map of
Kähler differentials along the function-field pullback, `KaehlerDifferential.mapSemilinear
φ.fieldPullback`, packaged as an `F`-linear map. The semilinear map's type depends on `φ` through
`φ.fieldPullback`; the `F`-linear packaging is a type independent of `φ`. -/
noncomputable def pullbackDifferential (φ : Isogeny W₁ W₂) :
    KaehlerDifferential F W₂.FunctionField →ₗ[F] KaehlerDifferential F W₁.FunctionField where
  toFun := KaehlerDifferential.mapSemilinear φ.fieldPullback
  map_add' := map_add _
  map_smul' c η := by
    rw [RingHom.id_apply, ← algebraMap_smul W₂.FunctionField c η,
      KaehlerDifferential.mapSemilinear_smul, AlgHom.commutes, algebraMap_smul]

/-- The pullback of differentials is `KaehlerDifferential.mapSemilinear` along the function-field
pullback. -/
theorem pullbackDifferential_apply (φ : Isogeny W₁ W₂)
    (η : KaehlerDifferential F W₂.FunctionField) :
    φ.pullbackDifferential η = KaehlerDifferential.mapSemilinear φ.fieldPullback η :=
  (rfl)

/-- **The pullback commutes with the universal derivation**: `φ^*(d f) = d (φ^* f)`. -/
@[simp]
theorem pullbackDifferential_D (φ : Isogeny W₁ W₂) (f : W₂.FunctionField) :
    φ.pullbackDifferential (KaehlerDifferential.D F W₂.FunctionField f) =
      KaehlerDifferential.D F W₁.FunctionField (φ.fieldPullback f) :=
  KaehlerDifferential.mapSemilinear_D _ _

/-- **The pullback of differentials is semilinear over the function-field pullback.** -/
@[simp]
theorem pullbackDifferential_smul (φ : Isogeny W₁ W₂) (c : W₂.FunctionField)
    (η : KaehlerDifferential F W₂.FunctionField) :
    φ.pullbackDifferential (c • η) = φ.fieldPullback c • φ.pullbackDifferential η :=
  KaehlerDifferential.mapSemilinear_smul _ _ _

/-- **The identity isogeny pulls differentials back trivially.** -/
@[simp]
theorem pullbackDifferential_id (W : WeierstrassCurve.Affine F) :
    (Isogeny.id W).pullbackDifferential = LinearMap.id :=
  LinearMap.ext fun η ↦ by
    rw [pullbackDifferential_apply, id_fieldPullback, KaehlerDifferential.mapSemilinear_id_apply,
      LinearMap.id_apply]

/-- **The pullback of differentials is functorial**: pulling back along a composite is composing
the pullbacks, in the reverse order. -/
@[simp]
theorem pullbackDifferential_comp {W₃ : WeierstrassCurve.Affine F} (ψ : Isogeny W₂ W₃)
    (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).pullbackDifferential = φ.pullbackDifferential ∘ₗ ψ.pullbackDifferential :=
  LinearMap.ext fun η ↦ by
    rw [LinearMap.comp_apply, pullbackDifferential_apply, pullbackDifferential_apply,
      pullbackDifferential_apply, comp_fieldPullback, KaehlerDifferential.mapSemilinear_comp_apply]

/-- **The function-field pullback of the denominator `2y + a₁x + a₃` of the invariant differential
is `W_Y` at the tautological point of the isogeny.** The target is elliptic so that the tautological
point is a point of `W₂⁄K(W₁)`. -/
theorem fieldPullback_invariantDifferentialDenom [W₂.IsElliptic] (φ : Isogeny W₁ W₂) :
    φ.fieldPullback (invariantDifferentialDenom W₂) =
      (W₂⁄W₁.FunctionField).toAffine.polynomialY.evalEval
        (Point.xCoord φ.pullback.tautologicalPoint)
        (Point.yCoord φ.pullback.tautologicalPoint) := by
  simp only [invariantDifferentialDenom_def, map_add, map_mul, map_ofNat, AlgHom.commutes,
    evalEval_polynomialY, CoordinatePullback.xCoord_tautologicalPoint,
    CoordinatePullback.yCoord_tautologicalPoint, genericX_def, genericY_def,
    fieldPullback_algebraMap, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

/-- **`W_Y` does not vanish at the tautological point of an isogeny**: it is the pullback of the
nonzero denominator of the invariant differential along an injective map. -/
theorem evalEval_polynomialY_tautologicalPoint_ne_zero [W₂.IsElliptic] (φ : Isogeny W₁ W₂) :
    (W₂⁄W₁.FunctionField).toAffine.polynomialY.evalEval (Point.xCoord φ.pullback.tautologicalPoint)
      (Point.yCoord φ.pullback.tautologicalPoint) ≠ 0 := by
  rw [← fieldPullback_invariantDifferentialDenom]
  exact (map_ne_zero φ.fieldPullback).2 (invariantDifferentialDenom_ne_zero W₂)

/-- **The pullback of the invariant differential is `dx / W_Y` at the tautological point**: the
formula `ω₂ = dx / (2y + a₁x + a₃)` pulled back coordinate by coordinate. The target is elliptic so
that the tautological point is a point of `W₂⁄K(W₁)`. -/
theorem pullbackDifferential_invariantDifferential [W₂.IsElliptic] (φ : Isogeny W₁ W₂) :
    φ.pullbackDifferential (invariantDifferential W₂) =
      ((W₂⁄W₁.FunctionField).toAffine.polynomialY.evalEval
          (Point.xCoord φ.pullback.tautologicalPoint)
          (Point.yCoord φ.pullback.tautologicalPoint))⁻¹ •
        KaehlerDifferential.D F W₁.FunctionField (Point.xCoord φ.pullback.tautologicalPoint) := by
  simp only [invariantDifferential_def, pullbackDifferential_smul, pullbackDifferential_D, map_inv₀,
    fieldPullback_invariantDifferentialDenom, CoordinatePullback.xCoord_tautologicalPoint,
    genericX_def, fieldPullback_algebraMap, AdjoinRoot.mk_C]

/-- **Negation pulls the invariant differential back to its negative.** -/
@[simp]
theorem pullbackDifferential_negIsogeny_invariantDifferential (W : WeierstrassCurve.Affine F) :
    (negIsogeny W).pullbackDifferential (invariantDifferential W) = -invariantDifferential W := by
  -- Negation fixes `x` and sends `y` to `negY x y`.
  have hx : (negIsogeny W).fieldPullback (genericX W) = genericX W := by
    have : (negIsogeny W).fieldPullback (genericX W) = algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.conj W (AdjoinRoot.of W.polynomial Polynomial.X)) := by
      rw [genericX_def, fieldPullback_algebraMap, negIsogeny_pullback, negPullback_apply,
        AdjoinRoot.mk_C]
    rw [this, CoordinateRing.conj_mk_C, ← genericX_def]
  have hy : (negIsogeny W).fieldPullback (genericY W) =
      (W⁄W.FunctionField).toAffine.negY (genericX W) (genericY W) := by
    have : (negIsogeny W).fieldPullback (genericY W) = algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.conj W (AdjoinRoot.root W.polynomial)) := by
      rw [genericY_def, fieldPullback_algebraMap, negIsogeny_pullback, negPullback_apply,
        AdjoinRoot.mk_X]
    rw [this, CoordinateRing.conj_mk_Y, ← evalEval_genericX_genericY, ← map_negPolynomial,
      evalEval_negPolynomial]
    simp only [WeierstrassCurve.baseChange]
  rw [invariantDifferential_def, pullbackDifferential_smul, pullbackDifferential_D, map_inv₀, hx,
    ← neg_smul, neg_inv]
  congr 2
  simp only [invariantDifferentialDenom_def, map_add, map_mul, map_ofNat, AlgHom.commutes, hx, hy,
    negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  ring

/-- **An isogeny is separable exactly when it pulls the invariant differential back to a nonzero
differential.** -/
theorem isSeparable_iff_pullbackDifferential_ne_zero [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁ W₂) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField ↔
      φ.pullbackDifferential (invariantDifferential W₂) ≠ 0 := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have halg : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z :=
    RingHom.congr_fun (RingHom.algebraMap_toAlgebra φ.fieldPullback.toRingHom)
  have : IsScalarTower F W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (φ.fieldPullback.commutes c).symm
  have : FiniteDimensional W₂.FunctionField W₁.FunctionField :=
    φ.finiteDimensional_functionField halg
  -- Under this algebra structure, `KaehlerDifferential.map` is the pullback of differentials.
  have hφ : IsScalarTower.toAlgHom F W₂.FunctionField W₁.FunctionField = φ.fieldPullback :=
    AlgHom.ext halg
  have hmapφ : ∀ η, KaehlerDifferential.map F F W₂.FunctionField W₁.FunctionField η =
      φ.pullbackDifferential η := fun η ↦ by
    rw [pullbackDifferential_apply, ← KaehlerDifferential.mapSemilinear_toAlgHom_apply]
    exact congrArg (fun f : W₂.FunctionField →ₐ[F] W₁.FunctionField ↦
      KaehlerDifferential.mapSemilinear f η) hφ
  -- Separability over the field range is separability over `W₂.FunctionField` acting through
  -- `φ`: both are the equality of the separable degree with the degree.
  have hsep : Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField ↔
      Algebra.IsSeparable W₂.FunctionField W₁.FunctionField := by
    rw [← Field.finSepDegree_eq_finrank_iff, ← Field.finSepDegree_eq_finrank_iff,
      TauCeti.AlgHom.finSepDegree_fieldRange φ.fieldPullback halg,
      TauCeti.AlgHom.finrank_fieldRange φ.fieldPullback halg]
  -- A finite extension is separable exactly when its module of differentials vanishes.
  have hunr : Algebra.IsSeparable W₂.FunctionField W₁.FunctionField ↔
      Subsingleton (KaehlerDifferential W₂.FunctionField W₁.FunctionField) := by
    rw [← Algebra.FormallyUnramified.iff_isSeparable, Algebra.formallyUnramified_iff]
  -- By the exact sequence `K₁ ⊗ Ω[K₂/F] → Ω[K₁/F] → Ω[K₁/K₂] → 0`, that is the surjectivity of the
  -- first map.
  have hmap : Subsingleton (KaehlerDifferential W₂.FunctionField W₁.FunctionField) ↔
      (KaehlerDifferential.mapBaseChange F W₂.FunctionField W₁.FunctionField).range = ⊤ := by
    rw [KaehlerDifferential.range_mapBaseChange, LinearMap.ker_eq_top]
    refine ⟨fun h ↦ LinearMap.ext fun x ↦ Subsingleton.elim _ _, fun h ↦ ⟨fun a b ↦ ?_⟩⟩
    obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective F W₂.FunctionField W₁.FunctionField a
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective F W₂.FunctionField W₁.FunctionField b
    rw [h, LinearMap.zero_apply, LinearMap.zero_apply]
  -- The range of the first map is spanned by `φ^*ω₂`, since `ω₂` spans `Ω[K₂/F]`.
  have hrange :
      (KaehlerDifferential.mapBaseChange F W₂.FunctionField W₁.FunctionField).range =
        Submodule.span W₁.FunctionField {φ.pullbackDifferential (invariantDifferential W₂)} := by
    refine le_antisymm ?_ ?_
    · rintro v ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul x y =>
        obtain ⟨c, rfl⟩ := (existsUnique_smul_invariantDifferential W₂ y).exists
        rw [KaehlerDifferential.mapBaseChange_tmul, map_smul, hmapφ]
        exact Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _
          (Submodule.mem_span_singleton_self _))
      | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨1 ⊗ₜ invariantDifferential W₂, by
        rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, hmapφ]⟩
  -- In the one-dimensional `Ω[K₁/F]`, a differential spans exactly when it is nonzero.
  have hspan : ∀ v : KaehlerDifferential F W₁.FunctionField,
      Submodule.span W₁.FunctionField {v} = ⊤ ↔ v ≠ 0 := fun v ↦ by
    constructor
    · rintro h rfl
      rw [Submodule.span_zero_singleton] at h
      exact invariantDifferential_ne_zero W₁
        ((Submodule.mem_bot _).1 (h ▸ Submodule.mem_top))
    · intro hv
      exact (finrank_eq_one_iff_of_nonzero v hv).mp
        (TauCeti.finrank_kaehlerDifferential_eq_one_of_separating (transcendental_genericX W₁))
  rw [hsep, hunr, hmap, hrange, hspan]

end TauCeti.Isogeny

end
