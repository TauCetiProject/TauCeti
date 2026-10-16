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
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Fiber

/-!
# Multiplication by `n` is finite locally free of rank `n²`

Let `E` be an elliptic curve over a scheme `S` and let `n` be a nonzero integer. This file proves
that multiplication by `n`, `[n] : E ⟶ E`, is finite locally free of rank `n²`: it is finite
(`EllipticCurveGeom.isFinite_mulBy_left`), flat and locally of finite presentation, and its fibre
over every point of `E` is the spectrum of an algebra of dimension `n²` over the residue field of
that point. Consequently the `n`-torsion `E[n]`, the fibre of `[n]` over the zero section, is
finite locally free of rank `n²` over `S`, and `[n]` is surjective.

Over a field `E` is the projective model of a Weierstrass equation
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_iso_toEllipticCurveGeom`), and on that model
`[n]` is flat of rank the degree `n²` of the function-field extension it induces
(`WeierstrassCurve.finrank_projModelMulBy`). Over an arbitrary base, `[n]` is a morphism over `S`
between schemes smooth over `S`, so it is locally of finite presentation. Its base change to the
fibre of `E` over a point `s` of `S` is multiplication by `n` on the elliptic curve over the
residue field of `s` obtained by base change, which is flat; by the fibrewise criterion for
flatness (`AlgebraicGeometry.Scheme.Hom.flat_of_flat_pullback_fiberι`) `[n]` is flat. The rank of
a finite flat morphism is invariant under base change, so it is `n²` everywhere.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.flat_mulBy_left`: multiplication by a nonzero
  integer is flat.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_mulBy_left`: multiplication by a nonzero
  integer `n` has rank `n²` at every point.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.flat_torsion_hom` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_torsion_hom`: for `n ≠ 0`, the `n`-torsion
  is finite locally free of rank `n²` over `S`; so is the closed subscheme of its ideal sheaf
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFinite_ker_torsionι_left` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.flat_ker_torsionι_left`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.surjective_mulBy_left`: multiplication by a nonzero
  integer is surjective.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, troisième partie, Théorème 11.3.10,
  the *critère de platitude par fibres*.
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

-- Over a field, multiplication by a nonzero integer is flat.
private theorem flat_mulBy_left_of_field {n : ℤ} (hn : n ≠ 0) : Flat (E.mulBy n).left := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨W, _, e, h⟩ := E.exists_iso_mulBy_left_eq n
  rw [h]
  infer_instance

-- Over a field, multiplication by a nonzero integer `n` has rank `n²` at every point.
private theorem finrank_mulBy_left_of_field {n : ℤ} (hn : n ≠ 0) (x : E.carrier) :
    (E.mulBy n).left.finrank x = n.natAbs ^ 2 := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨W, _, e, h⟩ := E.exists_iso_mulBy_left_eq n
  obtain ⟨y, rfl⟩ : x ∈ Set.range e.hom := e.hom.surjective x
  rw [h, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_comp_right_of_isIso,
    W.finrank_projModelMulBy]

end Field

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **Multiplication by a nonzero integer is flat** (Katz–Mazur 2.3.1), over any base `S`. -/
theorem flat_mulBy_left {n : ℤ} (hn : n ≠ 0) : Flat (E.mulBy n).left := by
  have := E.isFinite_mulBy_left hn
  have : Smooth E.structureMap := SmoothOfRelativeDimension.smooth 1 _
  have : Flat ((E.mulBy n).left ≫ E.structureMap) := by
    rw [mulBy_left_structureMap]
    infer_instance
  refine Scheme.Hom.flat_of_flat_pullback_fiberι _ E.structureMap fun s ↦ ?_
  -- the fibre of `E` over `s` is the elliptic curve `E'` over the residue field of `s`
  let t : Spec (.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
  let E' := E.baseChange t
  let g : E'.carrier ⟶ E.carrier := (E.baseChangeIso t).hom ≫ pullback.fst _ _
  have h0 : E'.zero ≫ g = t ≫ E.zero := by simp [g, E']
  have h := isPullback_mulBy_left_of_isPullback (E.isPullback_baseChange t) h0 n
  -- read the square of `[n]` through the identification of `E'` with the fibre `E ×_S κ(s)`
  have h' : IsPullback (pullback.fst E.structureMap t)
      ((E.baseChangeIso t).inv ≫ (E'.mulBy n).left ≫ (E.baseChangeIso t).hom)
      (E.mulBy n).left (pullback.fst E.structureMap t) :=
    h.of_iso (E.baseChangeIso t) (.refl _) (E.baseChangeIso t) (.refl _) (Category.comp_id _)
      (by simp [E']) (by simp) (Category.comp_id _)
  have := E'.flat_mulBy_left_of_field hn
  have hflat : Flat (pullback.snd (E.mulBy n).left (pullback.fst E.structureMap t)) := by
    rw [← h'.isoPullback_inv_snd]
    infer_instance
  -- the fibre `E.structureMap.fiber s` is by definition `E ×_S κ(s)`
  exact hflat

/-- **Multiplication by `n` has rank `n²`** (Katz–Mazur 2.3.1), over any base `S`. For `n ≠ 0`,
the finite flat morphism `[n] : E ⟶ E` has rank `n²` at every point `x`: the fibre of `[n]` over
`x` is the spectrum of an algebra of dimension `n²` over the residue field of `x`. -/
@[simp]
theorem finrank_mulBy_left {n : ℤ} (hn : n ≠ 0) (x : E.carrier) :
    (E.mulBy n).left.finrank x = n.natAbs ^ 2 := by
  have := E.isFinite_mulBy_left hn
  have := E.flat_mulBy_left hn
  -- `x` is the image of a point `x'` of the elliptic curve `E'` over the residue field of the
  -- image of `x` in `S`, on which `[n]` is the base change of `[n]`
  let t : Spec (.of (S.residueField (E.structureMap x))) ⟶ S :=
    S.fromSpecResidueField (E.structureMap x)
  let E' := E.baseChange t
  let g : E'.carrier ⟶ E.carrier := (E.baseChangeIso t).hom ≫ pullback.fst _ _
  have hg : IsPullback g E'.structureMap E.structureMap t := E.isPullback_baseChange t
  obtain ⟨a⟩ : Nonempty (Spec (.of (S.residueField (E.structureMap x)))) := inferInstance
  obtain ⟨x', hx', -⟩ := Scheme.exists_preimage_of_isPullback hg x a
    (S.fromSpecResidueField_apply _ a).symm
  -- the rank of a finite flat morphism is invariant under base change
  rw [← hx', ← Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_mulBy_left_of_isPullback hg (by simp [g, E']) n),
    E'.finrank_mulBy_left_of_field hn]

/-- **The `n`-torsion is flat** over `S` for `n ≠ 0`: `E[n]` is the base change of the flat
morphism `[n]` along the zero section. -/
theorem flat_torsion_hom {n : ℤ} (hn : n ≠ 0) : Flat (E.torsion n).X.hom :=
  MorphismProperty.of_isPullback (E.isPullback_torsion n) (E.flat_mulBy_left hn)

/-- The closed subscheme of the ideal sheaf of `E[n]` is finite over `S` for `n ≠ 0`. -/
instance isFinite_ker_torsionι_left {n : ℤ} [NeZero n] :
    IsFinite ((E.torsionι n).left.ker.subschemeι ≫ E.structureMap) := by
  have := E.isFinite_torsion_hom (NeZero.ne n)
  rw [subschemeι_ker_torsionι_left_structureMap]
  infer_instance

/-- The closed subscheme of the ideal sheaf of `E[n]` is flat over `S` for `n ≠ 0`. -/
instance flat_ker_torsionι_left {n : ℤ} [NeZero n] :
    Flat ((E.torsionι n).left.ker.subschemeι ≫ E.structureMap) := by
  have := E.flat_torsion_hom (NeZero.ne n)
  rw [subschemeι_ker_torsionι_left_structureMap]
  infer_instance

/-- **The `n`-torsion has rank `n²`** (Katz–Mazur 2.3.1). For an elliptic curve `E` over a scheme
`S` and `n ≠ 0`, the `n`-torsion `E[n]` is finite, flat and locally of finite presentation over
`S` (`isFinite_torsion_hom`, `flat_torsion_hom`, `locallyOfFinitePresentation_torsion_hom`), and
its rank at every point `s` of `S` is `n²`: it is the fibre of `[n]` over the zero section. -/
@[simp]
theorem finrank_torsion_hom {n : ℤ} (hn : n ≠ 0) (s : S) :
    (E.torsion n).X.hom.finrank s = n.natAbs ^ 2 := by
  have := E.isFinite_mulBy_left hn
  have := E.flat_mulBy_left hn
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (E.isPullback_torsion n), E.finrank_mulBy_left hn]

/-- **Multiplication by a nonzero integer is surjective** (Katz–Mazur 2.3.1), over any base `S`:
it is finite and flat of rank `n² ≥ 1` at every point. -/
theorem surjective_mulBy_left {n : ℤ} (hn : n ≠ 0) : Surjective (E.mulBy n).left := by
  have := E.isFinite_mulBy_left hn
  have := E.flat_mulBy_left hn
  refine (E.mulBy n).left.one_le_finrank_iff_surjective.mp fun x ↦ ?_
  rw [Pi.one_apply, E.finrank_mulBy_left hn]
  exact Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
