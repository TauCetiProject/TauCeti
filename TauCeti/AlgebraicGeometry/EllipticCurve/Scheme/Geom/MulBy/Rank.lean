/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# Multiplication by `n` over a field has rank `n²`

Let `E` be an elliptic curve over a field `K`, that is over `Spec K`, and let `n` be a nonzero
integer. This file proves that multiplication by `n`, `[n] : E ⟶ E`, is finite and flat of rank
`n²` at every point: the fibre of `[n]` over every point of `E` is the spectrum of an algebra of
dimension `n²` over its residue field. Over a field `E` is the projective model of a Weierstrass
equation (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_iso_toEllipticCurveGeom`), and on
that model the rank is the degree `n²` of the function-field extension induced by `[n]`
(`WeierstrassCurve.finrank_projModelMulBy`).

Two consequences follow. Over a field, the `n`-torsion `E[n]`, the fibre of `[n]` over the zero
section, is finite and flat of rank `n²` over `Spec K`. Over an arbitrary base `S`, `[n]` is
surjective: a point of `E` lies in the fibre of `E` over a point `s` of `S`, that fibre is an
elliptic curve over the residue field of `s`, and multiplication by `n` on it is the base change
of `[n]`, finite flat of positive rank, hence surjective.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.flat_mulBy_left`: over a field, multiplication by a
  nonzero integer is flat.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_mulBy_left`: over a field, multiplication by
  a nonzero integer `n` has rank `n²` at every point.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.flat_torsion_hom` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_torsion_hom`: over a field, for `n ≠ 0`, the
  `n`-torsion is flat of rank `n²`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.surjective_mulBy_left`: over any base,
  multiplication by a nonzero integer is surjective.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

section Field

variable {K : Type u} [Field K] (E : EllipticCurveGeom (Spec (.of K)))

-- Over a field, multiplication by `n` on `E` is multiplication by `n` on the projective model of a
-- Weierstrass equation, read through an isomorphism of underlying schemes.
private theorem exists_iso_mulBy_left_eq (n : ℤ) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic) (e : W.projModel ≅ E.carrier),
      (E.mulBy n).left = e.inv ≫ W.projModelMulBy n ≫ e.hom := by
  obtain ⟨W, _, e, he, h0⟩ := E.exists_iso_toEllipticCurveGeom
  refine ⟨W, inferInstance, W.toEllipticCurveGeomIso.symm ≪≫ e, ?_⟩
  -- the pointed isomorphism `e` over `Spec K` carries `[n]` to `[n]`
  have h := mulBy_left_comp_of_isPullback (g := e.hom) (f := 𝟙 _)
    (.of_horiz_isIso ⟨by simp [he]⟩) (by simp [h0]) n
  simp [W.projModelMulBy_eq, h]

/-- **Over a field, multiplication by a nonzero integer is flat.** -/
theorem flat_mulBy_left {n : ℤ} (hn : n ≠ 0) : Flat (E.mulBy n).left := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨W, _, e, h⟩ := E.exists_iso_mulBy_left_eq n
  rw [h]
  infer_instance

/-- **Over a field, multiplication by `n` has rank `n²`** (Katz–Mazur 2.3.1). For an elliptic
curve `E` over a field and `n ≠ 0`, the finite flat morphism `[n] : E ⟶ E` has rank `n²` at every
point `x`: the fibre of `[n]` over `x` is the spectrum of an algebra of dimension `n²` over the
residue field of `x`. -/
@[simp]
theorem finrank_mulBy_left {n : ℤ} (hn : n ≠ 0) (x : E.carrier) :
    (E.mulBy n).left.finrank x = n.natAbs ^ 2 := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨W, _, e, h⟩ := E.exists_iso_mulBy_left_eq n
  obtain ⟨y, rfl⟩ : x ∈ Set.range e.hom := e.hom.surjective x
  rw [h, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_comp_right_of_isIso,
    W.finrank_projModelMulBy]

/-- **Over a field, the `n`-torsion is flat** for `n ≠ 0`: `E[n]` is the base change of the flat
morphism `[n]` along the zero section. -/
theorem flat_torsion_hom {n : ℤ} (hn : n ≠ 0) : Flat (E.torsion n).X.hom :=
  have := E.flat_mulBy_left hn
  MorphismProperty.of_isPullback (E.isPullback_torsion n) this

/-- **Over a field, the `n`-torsion has rank `n²`** (Katz–Mazur 2.3.1). For an elliptic curve `E`
over a field `K` and `n ≠ 0`, the `n`-torsion `E[n]` is finite and flat over `Spec K`
(`isFinite_torsion_hom`, `flat_torsion_hom`), and its coordinate ring has dimension `n²` over `K`:
it is the fibre of `[n]` over the zero section. -/
@[simp]
theorem finrank_torsion_hom {n : ℤ} (hn : n ≠ 0) (s : Spec (.of K)) :
    (E.torsion n).X.hom.finrank s = n.natAbs ^ 2 := by
  have := E.isFinite_mulBy_left hn
  have := E.flat_mulBy_left hn
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (E.isPullback_torsion n), E.finrank_mulBy_left hn]

end Field

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **Multiplication by a nonzero integer is surjective** (Katz–Mazur 2.3.1), over any base `S`.
A point of `E` over a point `s` of `S` comes from the elliptic curve over the residue field of `s`
obtained by base change, on which multiplication by `n` is the base change of `[n]` and is finite
and flat of rank `n² ≥ 1`, hence surjective. -/
theorem surjective_mulBy_left {n : ℤ} (hn : n ≠ 0) : Surjective (E.mulBy n).left := by
  constructor
  intro x
  -- the fibre `E'` of `E` over the image `s` of `x` in `S`, with its projection `g` to `E`
  let t : Spec (.of (S.residueField (E.structureMap x))) ⟶ S :=
    S.fromSpecResidueField (E.structureMap x)
  let E' := E.baseChange t
  let g : E'.carrier ⟶ E.carrier := (E.baseChangeIso t).hom ≫ pullback.fst _ _
  have hg : IsPullback g E'.structureMap E.structureMap t := E.isPullback_baseChange t
  obtain ⟨a⟩ : Nonempty (Spec (.of (S.residueField (E.structureMap x)))) := inferInstance
  obtain ⟨x', hx', -⟩ := Scheme.exists_preimage_of_isPullback hg x a
    (S.fromSpecResidueField_apply _ a).symm
  -- over the residue field, `[n]` is finite and flat of rank `n² ≥ 1`, hence surjective
  have : IsFinite (E'.mulBy n).left := E'.isFinite_mulBy_left hn
  have : Flat (E'.mulBy n).left := E'.flat_mulBy_left hn
  have : Surjective (E'.mulBy n).left :=
    ((E'.mulBy n).left.one_le_finrank_iff_surjective).mp fun y ↦ by
      rw [Pi.one_apply, E'.finrank_mulBy_left hn]
      exact Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)
  obtain ⟨y, rfl⟩ := (E'.mulBy n).left.surjective x'
  refine ⟨g y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← mulBy_left_comp_of_isPullback hg (by simp [g, E']) n,
    Scheme.Hom.comp_apply, hx']

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
