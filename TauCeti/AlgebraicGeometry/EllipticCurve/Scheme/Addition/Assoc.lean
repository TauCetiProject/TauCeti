/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# Associativity of the Bosma–Lenstra addition morphism

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model over `S = Spec R`, and let `E ×_S E ⟶ E` be the Bosma–Lenstra addition morphism
`WeierstrassCurve.additionMorphism`. This file shows that the addition morphism is associative:
the two morphisms `(E ×_S E) ×_S E ⟶ E` that add the three components of the triple fibre
product, as `(a + b) + c` and as `a + (b + c)`, are equal.

Over a Noetherian integral domain `R`, the triple fibre product `(E ×_S E) ×_S E` is reduced and
`E` is a separated scheme, so two morphisms `(E ×_S E) ×_S E ⟶ E` are equal as soon as they agree
on the points of `(E ×_S E) ×_S E` with values in its residue fields. Such a point is a triple of
points of `E` with homogeneous coordinates `P`, `Q` and `T` over a field. The addition morphism
sends a pair of points given by homogeneous coordinates to the point with homogeneous coordinates
their sum for Mathlib's addition of point representatives, so the two morphisms send the triple to
the points with homogeneous coordinates `add (add P Q) T` and `add P (add Q T)`. These represent
the same point (`WeierstrassCurve.Projective.add_assoc_equiv`).

An elliptic Weierstrass curve over an arbitrary commutative ring is the base change of one over a
Noetherian integral domain (`WeierstrassCurve.exists_map_eq_of_isElliptic`). Associativity passes
to a base change `W.map f`, because `projModel (W.map f)` is the base change of `projModel W`
(`WeierstrassCurve.isPullback_projModelBaseChange`) and the addition morphism commutes with base
change (`WeierstrassCurve.additionMorphism_projModelBaseChange`): the base change morphism turns
the two sums of the three projections of the triple fibre product of `projModel (W.map f)` into
the two sums of their composites with the base change morphism, which are three morphisms to
`projModel W` over the same morphism to `S`.

## Main results

* `WeierstrassCurve.additionMorphism_assoc`: the addition morphism of an elliptic Weierstrass
  curve over a commutative ring is associative.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

`additionMorphism_assoc` is adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at
commit `c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawAxioms.lean`, declarations
`mulModelHom_assoc_specPoints`, associativity on three points with values in a field,
`mulOver_assoc_atlas`, associativity over the universal base, and `mulOver_assoc_of_map`,
`mulOver_assoc_of_eq` and `mulOver_assoc`, its transport to every elliptic Weierstrass curve. The
other files named below lie in the same directory.

The source states associativity as an equation of morphisms of `Over (Spec R)`, for its morphism
`mulOver` (file `GroupLawConstruction.lean`), with the whiskerings and the associator of the
cartesian monoidal structure:
`(mulOver W ▷ modelOver W) ≫ mulOver W =
(α_ (modelOver W) (modelOver W) (modelOver W)).hom ≫ (modelOver W ◁ mulOver W) ≫ mulOver W`.
Here it is an equation of morphisms of schemes `(E ×_S E) ×_S E ⟶ E`, for the two morphisms
`(E ×_S E) ×_S E ⟶ E ×_S E` built with `pullback.lift` from the projections and the addition
morphism. The source also has the `pullback.lift` form of the equation, for three morphisms from
a scheme to `E` over the same morphism to the base, as its private theorem `model_mul_assoc_lift`
(file `GroupLawDescent.lean`), deduced from Mathlib's `CategoryTheory.MonObj.lift_lift_assoc` for
its group object.

The source proves associativity over one ring, the copy `WeierstrassAtlasRingU` in `Type u` of its
universal ring (file `AdditionBaseChange.lean`), by its extensionality principle
`hom_ext_of_forall_specPoint` for field-valued points (file `PointsDictionary.lean`). It evaluates
the multiplication on pairs of points over a field with `mulModelHom_specPoints` (file
`AdditionSpecPoints.lean`), and concludes from `add_assoc` in `WeierstrassCurve.Affine.Point`
through its dictionary `projModelPointsEquiv` (file `PointsDictionary.lean`). Here the same
argument is carried out for every curve whose triple fibre product is reduced, in particular over
every Noetherian integral domain, with Mathlib's `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`
in place of `hom_ext_of_forall_specPoint`, on points given by homogeneous coordinates
(`WeierstrassCurve.exists_eq_lift_projModelPoint`, `WeierstrassCurve.exists_eq_projModelPoint` and
`WeierstrassCurve.lift_projModelPoint_additionMorphism_eq_add`), and concludes from
`WeierstrassCurve.Projective.add_assoc_equiv`, the form for point representatives of `add_assoc` in
Mathlib's `WeierstrassCurve.Projective.Point`.

For the transport, the source constructs the morphism of triple fibre products induced by the
base change morphism (`BaseChangeOf.tripleMap`), and shows that the two sides of the associativity
equation commute with it: the right whiskering of the multiplication within
`mulOver_assoc_of_map`, and the associator followed by the left whiskering in
`BaseChangeOf.assoc_whiskerLeft`, through `BaseChangeOf.assocSnd_pairMap` and the other private
`BaseChangeOf` lemmas of the file. Here that morphism is not constructed: associativity for `W` is
applied to the composites with the base change morphism of the three projections of the triple
fibre product of `projModel (W.map f)`. The reduction
`WeierstrassCurve.exists_map_eq_of_isElliptic` takes the place of the source's named universal
curve `universalWeierstrassLocU` over `WeierstrassAtlasRingU`. The source's `mulModelHom_lift_π`,
that the sum of two morphisms to `E` lies over the same morphism to the base as the first of
them, is written here in the proof arguments of `pullback.lift`, with
`WeierstrassCurve.additionMorphism_projModelOver`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- A point of `(E ×_{Spec R} E) ×_{Spec R} E` with values in a local ring is the triple of three
-- points of `E` given by homogeneous coordinates, over the same ring homomorphism.
private theorem exists_eq_lift_lift_projModelPoint {S : Type u} [CommRing S] [IsLocalRing S]
    (p : Spec (.of S) ⟶ pullback (pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver)
      W.projModelOver) :
    ∃ (g : R →+* S) (P Q T : Fin 3 → S) (hP : (W.toProjective.map g).Equation P)
      (hQ : (W.toProjective.map g).Equation Q) (hT : (W.toProjective.map g).Equation T)
      (i j k : Fin 3) (hi : IsUnit (P i)) (hj : IsUnit (Q j)) (hk : IsUnit (T k)), p = pullback.lift
        (pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
          ((W.projModelPoint_projModelOver g hP hi).trans
            (W.projModelPoint_projModelOver g hQ hj).symm))
        (W.projModelPoint g hT hk)
        (by rw [pullback.lift_fst_assoc, projModelPoint_projModelOver,
          projModelPoint_projModelOver]) := by
  -- the first projection of `p` is a pair of points with homogeneous coordinates, along some `g`
  obtain ⟨g, P, Q, hP, hQ, i, j, hi, hj, h₁⟩ :=
    W.exists_eq_lift_projModelPoint (p ≫ pullback.fst _ _)
  -- the second projection lies over the same morphism `Spec g`, so it is a point along `g`
  obtain ⟨T, hT, k, hk, h₂⟩ := W.exists_eq_projModelPoint (g := g) (x := p ≫ pullback.snd _ _)
    (by rw [Category.assoc, ← pullback.condition, ← Category.assoc, h₁, pullback.lift_fst_assoc,
      projModelPoint_projModelOver])
  exact ⟨g, P, Q, T, hP, hQ, hT, i, j, k, hi, hj, hk, pullback.hom_ext
    (h₁.trans (pullback.lift_fst _ _ _).symm) (h₂.trans (pullback.lift_snd _ _ _).symm)⟩

section Triple

variable [W.IsElliptic]

-- The morphism `(E ×_S E) ×_S E ⟶ E ×_S E` adding the first two components:
-- `(a, b, c) ↦ (a + b, c)`.
private noncomputable abbrev tripleAddLeft :
    pullback (pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver) W.projModelOver ⟶
      pullback W.projModelOver W.projModelOver :=
  pullback.lift (pullback.fst _ _ ≫ W.additionMorphism) (pullback.snd _ _)
    (by rw [Category.assoc, additionMorphism_projModelOver, ← pullback.condition])

-- The morphism `(E ×_S E) ×_S E ⟶ E ×_S E` adding the last two components:
-- `(a, b, c) ↦ (a, b + c)`.
private noncomputable abbrev tripleAddRight :
    pullback (pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver) W.projModelOver ⟶
      pullback W.projModelOver W.projModelOver :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition, ← pullback.condition]) ≫ W.additionMorphism)
    (by rw [Category.assoc, Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc,
      Category.assoc, ← pullback.condition])

variable {X : Scheme.{u}} {a b c : X ⟶ W.projModel}
  (hab : a ≫ W.projModelOver = b ≫ W.projModelOver)
  (hbc : b ≫ W.projModelOver = c ≫ W.projModelOver)

-- Adding the first two components of the triple `(a, b, c)` gives the pair `(a + b, c)`.
@[reassoc]
private theorem lift_lift_tripleAddLeft :
    pullback.lift (pullback.lift a b hab) c (by rw [pullback.lift_fst_assoc, hab, hbc]) ≫
        W.tripleAddLeft =
      pullback.lift (pullback.lift a b hab ≫ W.additionMorphism) c
        (by rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc, hab,
          hbc]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

-- Adding the last two components of the triple `(a, b, c)` gives the pair `(a, b + c)`.
@[reassoc]
private theorem lift_lift_tripleAddRight :
    pullback.lift (pullback.lift a b hab) c (by rw [pullback.lift_fst_assoc, hab, hbc]) ≫
        W.tripleAddRight =
      pullback.lift a (pullback.lift b c hbc ≫ W.additionMorphism)
        (by rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc, hab]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
      pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
    -- the last two components of the triple `(a, b, c)` form the pair `(b, c)`
    refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
        pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

-- If the addition morphism is associative, then `(a + b) + c = a + (b + c)` for any three
-- morphisms `a`, `b` and `c` to `E` over the same morphism to `S`.
private theorem lift_lift_additionMorphism_assoc
    (h : W.tripleAddLeft ≫ W.additionMorphism = W.tripleAddRight ≫ W.additionMorphism) :
    pullback.lift (pullback.lift a b hab ≫ W.additionMorphism) c
        (by rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc, hab,
          hbc]) ≫ W.additionMorphism =
      pullback.lift a (pullback.lift b c hbc ≫ W.additionMorphism)
        (by rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc, hab]) ≫
        W.additionMorphism := by
  rw [← W.lift_lift_tripleAddLeft_assoc hab hbc, ← W.lift_lift_tripleAddRight_assoc hab hbc, h]

end Triple

section Field

variable [W.IsElliptic] {K : Type u} [Field K]

open Projective in
-- Over a field, the addition morphism is associative on the three points with homogeneous
-- coordinates `P`, `Q` and `T`.
private theorem lift_lift_projModelPoint_additionMorphism_assoc {g : R →+* K} {P Q T : Fin 3 → K}
    {hP : (W.toProjective.map g).Equation P} {hQ : (W.toProjective.map g).Equation Q}
    {hT : (W.toProjective.map g).Equation T} {i j k : Fin 3} (hi : IsUnit (P i)) (hj : IsUnit (Q j))
    (hk : IsUnit (T k)) :
    pullback.lift
        (pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
          ((W.projModelPoint_projModelOver g hP hi).trans
            (W.projModelPoint_projModelOver g hQ hj).symm) ≫ W.additionMorphism)
        (W.projModelPoint g hT hk)
        (by rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc,
          projModelPoint_projModelOver, projModelPoint_projModelOver]) ≫ W.additionMorphism =
      pullback.lift (W.projModelPoint g hP hi)
        (pullback.lift (W.projModelPoint g hQ hj) (W.projModelPoint g hT hk)
          ((W.projModelPoint_projModelOver g hQ hj).trans
            (W.projModelPoint_projModelOver g hT hk).symm) ≫ W.additionMorphism)
        (by rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc,
          projModelPoint_projModelOver, projModelPoint_projModelOver]) ≫ W.additionMorphism := by
  -- a solution with a nonzero coordinate on an elliptic curve over a field is nonsingular
  have hP' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP
  have hQ' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨j, hj.ne_zero⟩)).mp hQ
  have hT' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨k, hk.ne_zero⟩)).mp hT
  -- the four sums are nonsingular, so each of them has a nonzero coordinate
  have hPQ := nonsingular_add hP' hQ'
  have hQT := nonsingular_add hQ' hT'
  obtain ⟨m, hm⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular hPQ)
  obtain ⟨n, hn⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular hQT)
  obtain ⟨r, hr⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_add hPQ hT'))
  obtain ⟨s, hs⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_add hP' hQT))
  -- the two inner sums are the points with homogeneous coordinates `add P Q` and `add Q T`, so
  -- the two sides are the points with homogeneous coordinates `add (add P Q) T` and
  -- `add P (add Q T)`, which differ by a unit
  obtain ⟨u, hu⟩ := add_assoc_equiv hP' hQ' hT'
  simp only [W.lift_projModelPoint_additionMorphism_eq_add hi hj hm.isUnit,
    W.lift_projModelPoint_additionMorphism_eq_add hj hk hn.isUnit]
  rw [W.lift_projModelPoint_additionMorphism_eq_add hm.isUnit hk hr.isUnit,
    W.lift_projModelPoint_additionMorphism_eq_add hi hn.isUnit hs.isUnit,
    projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, u, hu.symm⟩

-- The two ways of adding three components agree on every point of `(E ×_S E) ×_S E` with values
-- in a field.
private theorem comp_additionMorphism_assoc
    (p : Spec (.of K) ⟶ pullback (pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver)
      W.projModelOver) :
    p ≫ W.tripleAddLeft ≫ W.additionMorphism = p ≫ W.tripleAddRight ≫ W.additionMorphism := by
  -- `p` is the triple of the points with homogeneous coordinates `P`, `Q` and `T`
  obtain ⟨g, P, Q, T, hP, hQ, hT, i, j, k, hi, hj, hk, rfl⟩ :=
    W.exists_eq_lift_lift_projModelPoint p
  -- the two ways of adding its components give `(P + Q) + T` and `P + (Q + T)`
  have hQT := (W.projModelPoint_projModelOver g hQ hj).trans
    (W.projModelPoint_projModelOver g hT hk).symm
  rw [W.lift_lift_tripleAddLeft_assoc (hbc := hQT), W.lift_lift_tripleAddRight_assoc (hbc := hQT)]
  exact W.lift_lift_projModelPoint_additionMorphism_assoc hi hj hk

end Field

-- The addition morphism is associative whenever `(E ×_S E) ×_S E` is reduced, as it is over a
-- Noetherian integral domain: `E` is a separated scheme, so it suffices that the two sides agree
-- on the points of `(E ×_S E) ×_S E` with values in its residue fields.
private theorem additionMorphism_assoc_of_isReduced [W.IsElliptic]
    [IsReduced (pullback (pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver)
      W.projModelOver)] :
    W.tripleAddLeft ≫ W.additionMorphism = W.tripleAddRight ≫ W.additionMorphism :=
  ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
    (fun x _ ↦ W.comp_additionMorphism_assoc (Scheme.fromSpecResidueField _ x))
    (terminal.hom_ext _ _)

variable {R' : Type u} [CommRing R'] (f : R →+* R')

-- For a morphism `q` to `E' ×_{S'} E'`, where `E'` is the projective model of the base change
-- `W.map f` over `S' = Spec R'`, adding the two components of `q` and then changing the base is
-- changing the base of the two components and then adding.
private theorem comp_additionMorphism_projModelBaseChange [W.IsElliptic] {X : Scheme.{u}}
    (q : X ⟶ pullback (W.map f).projModelOver (W.map f).projModelOver) :
    q ≫ (W.map f).additionMorphism ≫ W.projModelBaseChange f =
      pullback.lift (q ≫ pullback.fst _ _ ≫ W.projModelBaseChange f)
        (q ≫ pullback.snd _ _ ≫ W.projModelBaseChange f)
        (by simp only [Category.assoc, projModelBaseChange_projModelOver,
          pullback.condition_assoc]) ≫ W.additionMorphism := by
  rw [additionMorphism_projModelBaseChange, ← Category.assoc]
  refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

-- If the addition morphism of `W` is associative, then so is the addition morphism of the base
-- change `W.map f`.
private theorem additionMorphism_assoc_map [W.IsElliptic]
    (h : W.tripleAddLeft ≫ W.additionMorphism = W.tripleAddRight ≫ W.additionMorphism) :
    (W.map f).tripleAddLeft ≫ (W.map f).additionMorphism =
      (W.map f).tripleAddRight ≫ (W.map f).additionMorphism := by
  -- a morphism to `projModel (W.map f)`, the base change of `projModel W` along `Spec f`, is
  -- determined by its composites with the base change morphism and with the structure morphism
  refine (W.isPullback_projModelBaseChange f).hom_ext ?_ ?_
  · -- the base change morphism turns the two sums of the three projections for `W.map f` into
    -- the two sums of their composites with the base change morphism for `W`, which are equal, as
    -- the addition morphism of `W` is associative
    simpa only [Category.assoc, comp_additionMorphism_projModelBaseChange, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc] using W.lift_lift_additionMorphism_assoc _ _ h
  · -- both sides lie over `Spec R'`
    simp only [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc]

/-- **The addition morphism is associative.** Let `W` be an elliptic Weierstrass curve over a
commutative ring `R`, and write `E = projModel W` and `S = Spec R`, with Bosma–Lenstra addition
morphism `μ : E ×_S E ⟶ E`. Write `fst` and `snd` for the projections of the triple fibre product
`(E ×_S E) ×_S E` to `E ×_S E` and to `E`, and for those of `E ×_S E`. The morphism
`(E ×_S E) ×_S E ⟶ E ×_S E` with components `fst ≫ μ` and `snd`, followed by `μ`, is equal to the
morphism with components `fst ≫ fst` and `(fst ≫ snd, snd) ≫ μ`, followed by `μ`: adding the first
two components and then the third is adding the first component and the sum of the last two. The
two morphisms to `E ×_S E` are the underlying morphisms of the pairs
`CartesianMonoidalCategory.lift` of the corresponding morphisms of the cartesian monoidal category
`Over S` (`CategoryTheory.Over.lift_left`), and the equation is that of
`CategoryTheory.MonObj.lift_lift_assoc` for the three projections `fst ≫ fst`, `fst ≫ snd` and
`snd`, the first two of which are the components of `fst`. -/
theorem additionMorphism_assoc [W.IsElliptic] :
    pullback.lift
        (pullback.fst (pullback.fst W.projModelOver W.projModelOver ≫ W.projModelOver)
          W.projModelOver ≫ W.additionMorphism)
        (pullback.snd _ _)
        (by rw [Category.assoc, additionMorphism_projModelOver, ← pullback.condition]) ≫
        W.additionMorphism =
      pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
        (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
          (by rw [Category.assoc, ← pullback.condition, ← pullback.condition]) ≫ W.additionMorphism)
        (by rw [Category.assoc, Category.assoc, additionMorphism_projModelOver,
          pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) ≫ W.additionMorphism := by
  -- `W` is the base change of an elliptic Weierstrass curve `W₀` over a Noetherian integral domain,
  -- over which `(E ×_S E) ×_S E` is reduced
  obtain ⟨R₀, _, _, _, W₀, _, f, rfl⟩ := W.exists_map_eq_of_isElliptic
  exact W₀.additionMorphism_assoc_map f W₀.additionMorphism_assoc_of_isReduced

end WeierstrassCurve
