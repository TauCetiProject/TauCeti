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
# Commutativity of the Bosma–Lenstra addition morphism

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model over `S = Spec R`, and let `E ×_S E ⟶ E` be the Bosma–Lenstra addition morphism
`WeierstrassCurve.additionMorphism`. This file shows that the addition morphism is commutative: it
is unchanged by composition with the isomorphism of `E ×_S E` swapping the two factors.

Over a Noetherian integral domain `R`, the fibre product `E ×_S E` is reduced and `E` is a
separated scheme, so two morphisms `E ×_S E ⟶ E` are equal as soon as they agree on the points of
`E ×_S E` with values in its residue fields. Such a point is a pair of points of `E` with
homogeneous coordinates `P` and `Q` over a field. The addition morphism sends it to the point with
homogeneous coordinates the sum `add P Q` of Mathlib's addition of point representatives, and
`add P Q` and `add Q P` represent the same point (`WeierstrassCurve.Projective.add_comm_equiv`).

An elliptic Weierstrass curve over an arbitrary commutative ring is the base change of one over a
Noetherian integral domain (`WeierstrassCurve.exists_map_eq_of_isElliptic`). Commutativity passes
to a base change `W.map f`, because `projModel (W.map f)` is the base change of `projModel W`
(`WeierstrassCurve.isPullback_projModelBaseChange`) and the addition morphism commutes with base
change (`WeierstrassCurve.additionMorphism_projModelBaseChange`).

## Main results

* `WeierstrassCurve.additionMorphism_comm`: the addition morphism of an elliptic Weierstrass curve
  over a commutative ring is commutative.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

`additionMorphism_comm` is adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at
commit `c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawAxioms.lean`, declarations
`mulModelHom_comm_atlas`, commutativity over the universal base, and `mulModelHom_comm`, its
transport to every elliptic Weierstrass curve. The other files named below lie in the same
directory.

The source proves commutativity over one ring, the copy `WeierstrassAtlasRingU` in `Type u` of its
universal ring (file `AdditionBaseChange.lean`), by its extensionality principle
`hom_ext_of_forall_specPoint` for field-valued points (file `PointsDictionary.lean`). It evaluates
the multiplication on a pair of points over a field with `mulModelHom_specPoints` (file
`AdditionSpecPoints.lean`), and concludes from the commutativity of `WeierstrassCurve.Affine.Point`
through its dictionary `projModelPointsEquiv` (file `PointsDictionary.lean`). Here the same
argument is carried out over every Noetherian integral domain, with Mathlib's
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq` in place of `hom_ext_of_forall_specPoint`, on
points given by homogeneous coordinates (`WeierstrassCurve.exists_eq_lift_projModelPoint` and
`WeierstrassCurve.lift_projModelPoint_additionMorphism_eq_add`), and concludes from
`WeierstrassCurve.Projective.add_comm_equiv`, which is not stated in the source. The transport to
every curve follows the source, with the reduction `WeierstrassCurve.exists_map_eq_of_isElliptic`
in place of the source's named universal curve `universalWeierstrassLocU` over
`WeierstrassAtlasRingU`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Field

variable [W.IsElliptic] {K : Type u} [Field K]

open Projective in
-- Over a field, the addition morphism sends the pair of points with homogeneous coordinates `Q`
-- and `P` to the same point as the pair of points with homogeneous coordinates `P` and `Q`.
private theorem lift_projModelPoint_additionMorphism_comm {g : R →+* K} {P Q : Fin 3 → K}
    {hP : (W.toProjective.map g).Equation P} {hQ : (W.toProjective.map g).Equation Q} {i j : Fin 3}
    (hi : IsUnit (P i)) (hj : IsUnit (Q j)) :
    pullback.lift (W.projModelPoint g hQ hj) (W.projModelPoint g hP hi)
        ((W.projModelPoint_projModelOver g hQ hj).trans
          (W.projModelPoint_projModelOver g hP hi).symm) ≫ W.additionMorphism =
      pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
        ((W.projModelPoint_projModelOver g hP hi).trans
          (W.projModelPoint_projModelOver g hQ hj).symm) ≫ W.additionMorphism := by
  -- a solution with a nonzero coordinate on an elliptic curve over a field is nonsingular
  have hP' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP
  have hQ' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨j, hj.ne_zero⟩)).mp hQ
  -- the sums `add P Q` and `add Q P` are nonsingular, so each of them has a nonzero coordinate
  obtain ⟨m, hm⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_add hP' hQ'))
  obtain ⟨n, hn⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_add hQ' hP'))
  -- the two pairs go to the points with homogeneous coordinates `add Q P` and `add P Q`, which
  -- differ by a unit
  obtain ⟨u, hu⟩ := add_comm_equiv (W' := W.toProjective.map g) Q P
  rw [W.lift_projModelPoint_additionMorphism_eq_add hj hi hn.isUnit,
    W.lift_projModelPoint_additionMorphism_eq_add hi hj hm.isUnit,
    projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, u, hu.symm⟩

-- The addition morphism and its composite with the swap of the two factors agree on every point
-- of `E ×_S E` with values in a field.
private theorem comp_pullbackSymmetry_hom_additionMorphism
    (p : Spec (.of K) ⟶ pullback W.projModelOver W.projModelOver) :
    p ≫ (pullbackSymmetry W.projModelOver W.projModelOver).hom ≫ W.additionMorphism =
      p ≫ W.additionMorphism := by
  -- `p` is the pair of the points with homogeneous coordinates `P` and `Q`
  obtain ⟨g, P, Q, hP, hQ, i, j, hi, hj, rfl⟩ := W.exists_eq_lift_projModelPoint p
  rw [← W.lift_projModelPoint_additionMorphism_comm hi hj, ← Category.assoc]
  -- and the swap takes it to the pair of the points with homogeneous coordinates `Q` and `P`
  refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullback.lift_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]

end Field

-- The addition morphism is commutative whenever `E ×_S E` is reduced, as it is over a Noetherian
-- integral domain: `E` is a separated scheme, so it suffices that the two sides agree on the
-- points of `E ×_S E` with values in its residue fields.
private theorem additionMorphism_comm_of_isReduced [W.IsElliptic]
    [IsReduced (pullback W.projModelOver W.projModelOver)] :
    (pullbackSymmetry W.projModelOver W.projModelOver).hom ≫ W.additionMorphism =
      W.additionMorphism :=
  ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
    (fun x _ ↦ W.comp_pullbackSymmetry_hom_additionMorphism (Scheme.fromSpecResidueField _ x))
    (terminal.hom_ext _ _)

variable {R' : Type u} [CommRing R'] (f : R →+* R')

-- If the addition morphism of `W` is commutative, then so is the addition morphism of the base
-- change `W.map f`.
private theorem additionMorphism_comm_map [W.IsElliptic]
    (h : (pullbackSymmetry W.projModelOver W.projModelOver).hom ≫ W.additionMorphism =
      W.additionMorphism) :
    (pullbackSymmetry (W.map f).projModelOver (W.map f).projModelOver).hom ≫
      (W.map f).additionMorphism = (W.map f).additionMorphism := by
  -- a morphism to `projModel (W.map f)`, the base change of `projModel W` along `Spec f`, is
  -- determined by its composites with the base change morphism and with the structure morphism
  refine (W.isPullback_projModelBaseChange f).hom_ext ?_ ?_
  · rw [Category.assoc, additionMorphism_projModelBaseChange, ← Category.assoc]
    -- the addition morphism of `W` is commutative
    conv_rhs => rw [← h, ← Category.assoc]
    -- and the swap of the two factors commutes with the base change morphism on both factors
    refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_fst_assoc, pullback.lift_snd]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_snd,
        pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_fst]
  · -- both sides lie over `Spec R'`
    rw [Category.assoc, additionMorphism_projModelOver, pullbackSymmetry_hom_comp_fst_assoc,
      pullback.condition]

/-- **The addition morphism is commutative.** Let `W` be an elliptic Weierstrass curve over a
commutative ring `R`, and write `E = projModel W` and `S = Spec R`. The Bosma–Lenstra addition
morphism `E ×_S E ⟶ E` is unchanged by composition with the isomorphism `pullbackSymmetry` of
`E ×_S E` that swaps the two factors. This isomorphism is the underlying morphism of the braiding
of the cartesian monoidal category `Over S` (`CategoryTheory.Over.braiding_hom_left`). -/
@[reassoc (attr := simp)]
theorem additionMorphism_comm [W.IsElliptic] :
    (pullbackSymmetry W.projModelOver W.projModelOver).hom ≫ W.additionMorphism =
      W.additionMorphism := by
  -- `W` is the base change of an elliptic Weierstrass curve `W₀` over a Noetherian integral domain,
  -- over which `E ×_S E` is reduced
  obtain ⟨R₀, _, _, _, W₀, _, f, rfl⟩ := W.exists_map_eq_of_isElliptic
  exact W₀.additionMorphism_comm_map f W₀.additionMorphism_comm_of_isReduced

end WeierstrassCurve
