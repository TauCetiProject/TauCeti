/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.FrobeniusFixed
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Basic

/-!
# The tautological point of `1 − π`

The tautological point is additive on morphisms, and the identity's is the generic point, so the
tautological point of `1 − π_q` is the generic point minus that of Frobenius.

## Main results

* `TauCeti.Isogeny.tautologicalPoint_oneSubFrobeniusIsogeny`: the tautological point of
  `1 − π_q` is `g − π_q(g)`.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

-- Not `@[simp]`: `tautologicalPoint_eq_map_genericPoint` already rewrites this left-hand side to
-- `Point.map (oneSubFrobeniusIsogeny W).fieldPullback (genericPoint W)`, so the annotation puts
-- the lemma out of simp-normal form.
/-- **The tautological point of `1 − π_q` is the generic point minus that of Frobenius.** -/
theorem tautologicalPoint_oneSubFrobeniusIsogeny :
    (oneSubFrobeniusIsogeny W).pullback.tautologicalPoint =
      genericPoint W - (frobeniusIsogeny W).pullback.tautologicalPoint := by
  rw [← Hom.tautologicalPoint_ofIsogeny, ofIsogeny_oneSubFrobeniusIsogeny]
  simp [Hom.one_def, Hom.id_def]

/-- **The tautological point of `1 − π_q`, transported into any extension, is `Q − Q^q`** for `Q`
the image there of the generic point. This is the form the embedding count needs: the left side
depends on the homomorphism only through the pulled-back field, while the right side is visibly a
difference of a point and its `q`-power image. -/
theorem map_tautologicalPoint_oneSubFrobeniusIsogeny {Ω : Type*} [Field Ω] [DecidableEq Ω]
    [Algebra F Ω] (σ : W.FunctionField →ₐ[F] Ω) :
    letI := Fintype.ofFinite F
    Point.map σ (oneSubFrobeniusIsogeny W).pullback.tautologicalPoint =
      Point.map σ (genericPoint W) -
        Point.map (_root_.FiniteField.frobeniusAlgHom F Ω) (Point.map σ (genericPoint W)) := by
  let _ := Fintype.ofFinite F
  rw [tautologicalPoint_oneSubFrobeniusIsogeny, map_sub, tautologicalPoint_eq_map_genericPoint,
    fieldPullback_frobeniusIsogeny, WeierstrassCurve.Affine.Point.map_frobeniusAlgHom_comm]

/-- **Two homomorphisms that agree on the pulled-back field move the generic point to points whose
difference is `q`-power fixed.** Their images of the tautological point of `1 − π_q` agree, and that
image is `Q − Q^q`, so the two `Q`'s differ by a Frobenius-fixed point. -/
theorem map_frobeniusAlgHom_sub_map_genericPoint_eq_self {Ω : Type*} [Field Ω] [DecidableEq Ω]
    [Algebra F Ω] (σ τ : W.FunctionField →ₐ[F] Ω)
    (h : ∀ z ∈ (oneSubFrobeniusIsogeny W).fieldPullback.fieldRange, σ z = τ z) :
    letI := Fintype.ofFinite F
    Point.map (_root_.FiniteField.frobeniusAlgHom F Ω)
        (Point.map σ (genericPoint W) - Point.map τ (genericPoint W)) =
      Point.map σ (genericPoint W) - Point.map τ (genericPoint W) := by
  let _ := Fintype.ofFinite F
  have hmem : ∀ x : W.CoordinateRing,
      (oneSubFrobeniusIsogeny W).pullback x ∈
        (oneSubFrobeniusIsogeny W).fieldPullback.fieldRange := fun x ↦
    AlgHom.mem_fieldRange.2 ⟨algebraMap W.CoordinateRing W.FunctionField x,
      (oneSubFrobeniusIsogeny W).fieldPullback_algebraMap x⟩
  have key := CoordinatePullback.map_tautologicalPoint_eq_of_apply_eq
    (oneSubFrobeniusIsogeny W).pullback σ τ (h _ (hmem _)) (h _ (hmem _))
  rw [map_tautologicalPoint_oneSubFrobeniusIsogeny,
    map_tautologicalPoint_oneSubFrobeniusIsogeny] at key
  rw [map_sub, eq_comm, ← sub_eq_zero]
  rw [← sub_eq_zero] at key
  rw [← key]
  abel

/-- **That difference descends to a rational point.** A point over an extension fixed by the
`q`-power map comes from the base field, so two homomorphisms agreeing on the pulled-back field
move the generic point by a rational point. -/
theorem exists_baseChange_eq_sub_map_genericPoint {Ω : Type*} [Field Ω] [DecidableEq Ω]
    [Algebra F Ω] [DecidableEq F] (σ τ : W.FunctionField →ₐ[F] Ω)
    (h : ∀ z ∈ (oneSubFrobeniusIsogeny W).fieldPullback.fieldRange, σ z = τ z) :
    ∃ P : (W⁄F).toAffine.Point, Point.baseChange F Ω P =
      Point.map σ (genericPoint W) - Point.map τ (genericPoint W) := by
  let _ := Fintype.ofFinite F
  exact (WeierstrassCurve.Affine.Point.map_frobeniusAlgHom_eq_self_iff_mem_range_baseChange
    W _).1 (map_frobeniusAlgHom_sub_map_genericPoint_eq_self W σ τ h)

end TauCeti.Isogeny

end
