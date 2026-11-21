/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.TateNormalForm
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# The moduli problem of Tate points

A **Tate point** of an elliptic curve `E` over a scheme `S` is a section `P` such that none of
`P`, `2P` and `3P` meets the zero section (`EllipticCurveGeom.IsTatePoint`): the sections to which
the Tate normal form `Y² + aXY + bY = X³ + bX²` applies. Tate points pull back along arrows of
`Ell/B`, so they form a moduli problem over `Ell/B` (`ModuliProblem.tatePoint`).

This problem is relatively representable over every base `B`
(`ModuliProblem.tatePointRelRepData`): for an object `X = (E/S)` of `Ell/B`, the Tate points of
the base changes `E_T` of `E` are represented by the Tate locus of `E`, the open subscheme of
points `e` of `E` such that none of `e`, `2e` and `3e` lies on the zero section. As an open
subscheme of `E`, the representing scheme is smooth of relative dimension one over `S`
(`ModuliProblem.hasProperty_smoothOfRelativeDimension_tatePointRelRepData`), and it maps onto `S`
as soon as `E` has a Tate point over `S` (`ModuliProblem.surjective_tatePointRelRepData_rep_hom`).

The problem is also representable, by the universal Tate normal form over `B × Spec ℤ[a, b][Δ⁻¹]`
(`ModuliProblem.tatePointRepresentableBy`, in the file of `Y₁(N)`). Comparing the two projections
of the simultaneous problem of a naive `[Γ₁(N)]`-structure and a Tate point computes the relative
dimension of the fine modular curve `Y₁(N)`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.tatePoint B`: the moduli problem of Tate points over
  `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.tatePointEquiv`: its structures on an object `(E/S)` of
  `Ell/B` are the Tate points of `E` over `S`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.tatePointRelRepData B`: its relative representability by
  the Tate locus.

## Main results

* `ModuliProblem.hasProperty_smoothOfRelativeDimension_tatePointRelRepData`: the Tate point
  problem is smooth of relative dimension one over `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.surjective_tatePointRelRepData_rep_hom`: the
  representing scheme over an elliptic curve with a Tate point maps onto the base.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.3 (Tate normal form) and Chapter 4 (relatively
  representable moduli problems).
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

variable (B : Scheme.{u})

/-- **The moduli problem of Tate points** over `Ell/B`. Its structures on an object `(E/S)` of
`Ell/B` are the sections `P` of `E` such that none of `P`, `2P` and `3P` meets the zero section
(`tatePointEquiv`), and they pull back along an arrow of `Ell/B` by base change of points
(`tatePointEquiv_map`). -/
noncomputable def tatePoint : ModuliProblem B where
  obj X := ULift.{u + 1}
    {P : 𝟙_ (Over X.unop.base) ⟶ Over.mk X.unop.curve.structureMap // X.unop.curve.IsTatePoint P}
  map f := TypeCat.ofHom fun α ↦
    ⟨⟨EllipticCurveGeom.pointsPullback f.unop.isPullback f.unop.zero_total α.down.val,
      α.down.property.pointsPullback f.unop.isPullback f.unop.zero_total⟩⟩
  map_id X := by
    ext α
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr (by simp)).symm
  map_comp f g := by
    ext α
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr (by simp)).symm

variable {B}

/-- The structures of the Tate point problem on an object `(E/S)` of `Ell/B` are the Tate points
of `E` over `S`. -/
noncomputable def tatePointEquiv (X : EllObj B) :
    (tatePoint B).obj (op X) ≃
      {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap // X.curve.IsTatePoint P} :=
  Equiv.ulift

/-- The pull-back of a Tate point along an arrow `f` of `Ell/B` is its base change along `f`. -/
@[simp]
theorem tatePointEquiv_map {X Y : EllObj B} (f : X ⟶ Y) (α : (tatePoint B).obj (op Y)) :
    (tatePointEquiv X ((tatePoint B).map f.op α)).val =
      EllipticCurveGeom.pointsPullback f.isPullback f.zero_total (tatePointEquiv Y α).val :=
  (rfl)

/-! ### Relative representability by the Tate locus -/

section Representable

open EllipticCurveGeom

variable {X : EllObj B}

/-- **Tate points of a base change, read on the original curve.** For an object `X = (E/S)` of
`Ell/B` and a scheme `T` over `S`, a `T`-point of the base change `E_T` is a Tate point exactly
when the corresponding point of `E` with values in `T` (`EllObj.baseChangePointsEquiv`) lands in
the Tate locus of `E`. -/
theorem isTatePoint_baseChange_iff {T : Over X.base}
    {P : 𝟙_ (Over (X.baseChangeFunctor.obj T).base) ⟶
      Over.mk (X.baseChangeFunctor.obj T).curve.structureMap} :
    (X.baseChangeFunctor.obj T).curve.IsTatePoint P ↔
      Set.range (X.baseChangePointsEquiv T P).left ⊆ X.curve.tateLocus := by
  rw [isTatePoint_iff_of_isPullback (X.baseChangeFunctorHom T).isPullback
    (X.baseChangeFunctorHom T).zero_total, EllObj.baseChangePointsEquiv_apply_left,
    Set.range_subset_iff]
  -- the two sides differ only in the type of the point of the base: the base
  -- `(X.baseChangeFunctor.obj T).base` of the base change is `T.left` by definition
  exact Iff.rfl

/-- The Tate locus of the curve of `X = (E/S)`, as a scheme over `S`. -/
noncomputable abbrev tateLocusOver (X : EllObj B) : Over X.base :=
  Over.mk (X.curve.tateLocusOpens.ι ≫ X.curve.structureMap)

/-- The inclusion of the Tate locus into the curve, an open immersion. -/
noncomputable def tateLocusι (X : EllObj B) : tateLocusOver X ⟶ Over.mk X.curve.structureMap :=
  Over.homMk X.curve.tateLocusOpens.ι rfl

@[simp]
theorem tateLocusι_left (X : EllObj B) : (tateLocusι X).left = X.curve.tateLocusOpens.ι :=
  (rfl)

instance (X : EllObj B) : Mono (tateLocusι X) :=
  (Over.forget X.base).mono_of_mono_map (inferInstanceAs (Mono X.curve.tateLocusOpens.ι))

/-- The Tate point of the base change `E_T` given by a point `y` of the Tate locus with values in a
scheme `T` over `S`: the `T`-point of `E_T` corresponding to the point `y ≫ tateLocusι X` of `E`
with values in `T`. -/
noncomputable def tateLocusPoint {T : Over X.base} (y : T ⟶ tateLocusOver X) :
    (tatePoint B).obj (op (X.baseChangeFunctor.obj T)) :=
  (tatePointEquiv _).symm ⟨(X.baseChangePointsEquiv T).symm (y ≫ tateLocusι X), by
    rw [isTatePoint_baseChange_iff, MulEquiv.apply_symm_apply]
    rintro _ ⟨t, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply, tateLocusι_left, ← coe_tateLocusOpens,
      ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩⟩

/-- Under `baseChangePointsEquiv`, the Tate point attached to `y` is `y ≫ tateLocusι X`. -/
@[simp]
theorem baseChangePointsEquiv_tateLocusPoint {T : Over X.base} (y : T ⟶ tateLocusOver X) :
    X.baseChangePointsEquiv T (tatePointEquiv _ (tateLocusPoint y)).val = y ≫ tateLocusι X := by
  simp [tateLocusPoint]

private theorem bijective_tateLocusPoint (T : Over X.base) :
    Function.Bijective (tateLocusPoint (X := X) (T := T)) := by
  refine ⟨fun y y' h ↦ ?_, fun α ↦ ?_⟩
  · rw [← cancel_mono (tateLocusι X), ← baseChangePointsEquiv_tateLocusPoint,
      ← baseChangePointsEquiv_tateLocusPoint, h]
  · let x := X.baseChangePointsEquiv T (tatePointEquiv _ α).val
    have hrange : Set.range x.left ⊆ Set.range X.curve.tateLocusOpens.ι := by
      rw [Scheme.Opens.range_ι, coe_tateLocusOpens]
      exact isTatePoint_baseChange_iff.mp (tatePointEquiv _ α).property
    let y : T ⟶ tateLocusOver X :=
      Over.homMk (IsOpenImmersion.lift X.curve.tateLocusOpens.ι x.left hrange)
        (by simpa using Over.w x)
    have hy : y ≫ tateLocusι X = x := by
      ext1
      simp [y]
    refine ⟨y, (tatePointEquiv _).injective (Subtype.ext ?_)⟩
    apply (X.baseChangePointsEquiv T).injective
    rw [baseChangePointsEquiv_tateLocusPoint, hy]

/-- **Tate points are represented by the Tate locus.** For an object `X = (E/S)` of `Ell/B`, the
points of the Tate locus of `E` with values in a scheme `T` over `S` correspond to the Tate points
of the base change `E_T`, a point `y` corresponding to `tateLocusPoint y`. -/
noncomputable def tateLocusEquiv (T : Over X.base) :
    (T ⟶ tateLocusOver X) ≃ (tatePoint B).obj (op (X.baseChangeFunctor.obj T)) :=
  Equiv.ofBijective _ (bijective_tateLocusPoint T)

/-- The correspondence `tateLocusEquiv` is natural in the scheme `T` over `S`. -/
theorem tateLocusEquiv_comp {T' T : Over X.base} (f : T' ⟶ T) (y : T ⟶ tateLocusOver X) :
    tateLocusEquiv T' (f ≫ y) =
      (tatePoint B).map (X.baseChangeFunctor.map f).op (tateLocusEquiv T y) := by
  refine (tatePointEquiv _).injective (Subtype.ext ?_)
  apply (X.baseChangePointsEquiv T').injective
  simp only [tateLocusEquiv, Equiv.ofBijective_apply, baseChangePointsEquiv_tateLocusPoint,
    tatePointEquiv_map]
  rw [EllObj.baseChangePointsEquiv_pointsPullback, baseChangePointsEquiv_tateLocusPoint,
    Category.assoc]

variable (B) in
/-- **The moduli problem of Tate points is relatively representable.** For an object `X = (E/S)`
of `Ell/B`, the Tate points of the base changes `E_T` of `E` are represented by the Tate locus of
`E`, the open subscheme of points `e` such that none of `e`, `2e` and `3e` lies on the zero
section. -/
noncomputable def tatePointRelRepData : (tatePoint B).RelRepData where
  rep X := tateLocusOver X
  representableBy _ :=
    { homEquiv := tateLocusEquiv _
      homEquiv_comp f y := tateLocusEquiv_comp f y }

/-- The object representing the Tate point problem over `X = (E/S)` is the Tate locus of `E`. -/
@[simp]
theorem tatePointRelRepData_rep (X : EllObj B) :
    (tatePointRelRepData B).rep X = tateLocusOver X :=
  (rfl)

/-- **The Tate point problem is smooth of relative dimension one over `Ell/B`**: each representing
scheme is an open subscheme of an elliptic curve. -/
theorem hasProperty_smoothOfRelativeDimension_tatePointRelRepData :
    (tatePointRelRepData B).HasProperty (@SmoothOfRelativeDimension 1) :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦ inferInstanceAs
    (SmoothOfRelativeDimension (0 + 1) (X.curve.tateLocusOpens.ι ≫ X.curve.structureMap))

/-- **The Tate locus covers the base if there is a Tate point.** If the curve of `X = (E/S)` has
a Tate point over `S`, then the representing morphism of the Tate point problem over `X` is
surjective: the Tate point passes through the Tate locus over every point of `S`. -/
theorem surjective_tatePointRelRepData_rep_hom {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap}
    (hP : X.curve.IsTatePoint P) : Surjective ((tatePointRelRepData B).rep X).hom := by
  have hrange : Set.range P.left ⊆ Set.range X.curve.tateLocusOpens.ι := by
    rw [Scheme.Opens.range_ι, coe_tateLocusOpens]
    rintro _ ⟨s, rfl⟩
    exact hP.mem_tateLocus s
  -- `P` factors through the Tate locus by a section of its structure morphism
  let l := IsOpenImmersion.lift X.curve.tateLocusOpens.ι P.left hrange
  have hl : l ≫ (tateLocusOver X).hom = 𝟙 _ :=
    (IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (left_comp_structureMap P)
  rw [tatePointRelRepData_rep]
  exact ⟨fun s ↦ ⟨l s, (Scheme.Hom.comp_apply l _ s).symm.trans (by rw [hl]; rfl)⟩⟩

end Representable

end ModuliProblem

end TauCeti.AlgebraicGeometry
