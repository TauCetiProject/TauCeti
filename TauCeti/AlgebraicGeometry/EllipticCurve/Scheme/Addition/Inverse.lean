/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The inverse law for the Bosma–Lenstra addition morphism

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model over `S = Spec R`, with structure morphism `π : E ⟶ S` and zero section
`0 : S ⟶ E`, and let `E ×_S E ⟶ E` be the Bosma–Lenstra addition morphism
`WeierstrassCurve.additionMorphism`. This file shows that the negation morphism
`WeierstrassCurve.projModelNeg` is a right inverse for it: the morphism `E ⟶ E ×_S E` with
components the identity and negation, followed by the addition morphism, is `π ≫ 0`.

Over a Noetherian integral domain `R`, the scheme `E` is integral, hence reduced, and it is
separated, so two morphisms `E ⟶ E` are equal as soon as they agree on the points of `E` with
values in its residue fields. Such a point has homogeneous coordinates `P` over a field, negation
sends it to the point with homogeneous coordinates `neg P`, and the addition morphism sends the
pair to the point with homogeneous coordinates `add P (neg P)`. This represents the point at
infinity (`WeierstrassCurve.Projective.add_neg_equiv`), which is the value of `π ≫ 0`.

An elliptic Weierstrass curve over an arbitrary commutative ring is the base change of one over a
Noetherian integral domain (`WeierstrassCurve.exists_map_eq_of_isElliptic`), and the inverse law
passes to a base change `W.map f`, since the addition morphism, negation and the zero section all
commute with base change.

## Main results

* `WeierstrassCurve.additionMorphism_right_inv`: the sum of the identity and negation of
  `projModel W` is the structure morphism followed by the zero section.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* The argument is the one of `WeierstrassCurve.additionMorphism_comm`, whose provenance records
  its adaptation from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), file
  `projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawAxioms.lean` at commit
  `c3415f32a313e19ace43e05479aeaa0d56ca287a`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- The morphism `E ⟶ E ×_S E` with components the identity and the negation morphism.
private noncomputable abbrev liftNeg : W.projModel ⟶ pullback W.projModelOver W.projModelOver :=
  pullback.lift (𝟙 W.projModel) W.projModelNeg (by simp)

section Field

variable [W.IsElliptic] {K : Type u} [Field K]

open Projective in
-- Over a field, the sum of a point and its negation is the zero section.
private theorem projModelPoint_liftNeg_additionMorphism {g : R →+* K} {P : Fin 3 → K}
    {hP : (W.toProjective.map g).Equation P} {i : Fin 3} (hi : IsUnit (P i)) :
    W.projModelPoint g hP hi ≫ W.liftNeg ≫ W.additionMorphism =
      Spec.map (CommRingCat.ofHom g) ≫ W.projModelZero := by
  -- a solution with a nonzero coordinate on an elliptic curve over a field is nonsingular
  have hP' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP
  -- so are its negation and the sum of the two, which have nonzero coordinates
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_neg hP'))
  obtain ⟨m, hm⟩ := Function.ne_iff.mp
    (ne_zero_of_nonsingular (nonsingular_add hP' (nonsingular_neg hP')))
  -- the point is sent to the pair of the points with homogeneous coordinates `P` and `neg P`
  have hpair : W.projModelPoint g hP hi ≫ W.liftNeg =
      pullback.lift (W.projModelPoint g hP hi)
        (W.projModelPoint g (((W.toProjective.map g).equation_neg P).mpr hP) hj.isUnit)
        ((W.projModelPoint_projModelOver g hP hi).trans
          (W.projModelPoint_projModelOver g _ hj.isUnit).symm) := by
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp [W.projModelPoint_projModelNeg hi hj.isUnit]
  -- whose sum has homogeneous coordinates `add P (neg P)`, a unit multiple of `(0, 1, 0)`
  obtain ⟨u, hu⟩ := add_neg_equiv hP'
  rw [reassoc_of% hpair, W.lift_projModelPoint_additionMorphism_eq_add hi hj.isUnit hm.isUnit,
    SpecMap_projModelZero, projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, u, hu.symm⟩

-- The two sides of the inverse law agree on every point of `E` with values in a field.
private theorem comp_liftNeg_additionMorphism (p : Spec (.of K) ⟶ W.projModel) :
    p ≫ W.liftNeg ≫ W.additionMorphism = p ≫ W.projModelOver ≫ W.projModelZero := by
  -- `p` is the point with homogeneous coordinates `P`
  obtain ⟨g, P, hP, i, hi, rfl⟩ := W.exists_ringHom_eq_projModelPoint p
  rw [W.projModelPoint_liftNeg_additionMorphism hi, projModelPoint_projModelOver_assoc]

end Field

-- The inverse law holds whenever `E` is reduced, as it is over a Noetherian integral domain: `E`
-- is a separated scheme, so it suffices that the two sides agree on the points of `E` with values
-- in its residue fields.
private theorem liftNeg_additionMorphism_of_isReduced [W.IsElliptic] [IsReduced W.projModel] :
    W.liftNeg ≫ W.additionMorphism = W.projModelOver ≫ W.projModelZero :=
  ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
    (fun x _ ↦ W.comp_liftNeg_additionMorphism (Scheme.fromSpecResidueField _ x))
    (terminal.hom_ext _ _)

variable {R' : Type u} [CommRing R'] (f : R →+* R')

-- If the inverse law holds for `W`, then it holds for the base change `W.map f`.
private theorem liftNeg_additionMorphism_map [W.IsElliptic]
    (h : W.liftNeg ≫ W.additionMorphism = W.projModelOver ≫ W.projModelZero) :
    (W.map f).liftNeg ≫ (W.map f).additionMorphism =
      (W.map f).projModelOver ≫ (W.map f).projModelZero := by
  -- a morphism to `projModel (W.map f)`, the base change of `projModel W` along `Spec f`, is
  -- determined by its composites with the base change morphism and with the structure morphism
  refine (W.isPullback_projModelBaseChange f).hom_ext ?_ ?_
  · -- changing the base of the pair `(𝟙, neg)` of `W.map f` gives the base change morphism
    -- followed by the pair `(𝟙, neg)` of `W`
    have hpair : (W.map f).liftNeg ≫
        pullback.map _ _ _ _ (W.projModelBaseChange f) (W.projModelBaseChange f)
          (Spec.map (CommRingCat.ofHom f)) (W.projModelBaseChange_projModelOver f).symm
          (W.projModelBaseChange_projModelOver f).symm =
        W.projModelBaseChange f ≫ W.liftNeg := by
      refine pullback.hom_ext ?_ ?_ <;> simp
    rw [Category.assoc, additionMorphism_projModelBaseChange, reassoc_of% hpair, h,
      Category.assoc, projModelZero_projModelBaseChange, projModelBaseChange_projModelOver_assoc]
  · -- both sides lie over `Spec R'`
    simp

/-- **The inverse law for the addition morphism.** Let `W` be an elliptic Weierstrass curve over a
commutative ring `R`, and write `E = projModel W` and `S = Spec R`. The morphism `E ⟶ E ×_S E`
with components the identity and the negation morphism `projModelNeg`, followed by the
Bosma–Lenstra addition morphism `E ×_S E ⟶ E`, is the structure morphism `E ⟶ S` followed by the
zero section: every point plus its negation is zero. -/
@[reassoc (attr := simp)]
theorem additionMorphism_right_inv [W.IsElliptic] :
    pullback.lift (f := W.projModelOver) (g := W.projModelOver) (𝟙 W.projModel) W.projModelNeg
      (by simp) ≫ W.additionMorphism = W.projModelOver ≫ W.projModelZero := by
  -- `W` is the base change of an elliptic Weierstrass curve `W₀` over a Noetherian integral domain,
  -- over which `E` is integral, hence reduced
  obtain ⟨R₀, _, _, _, W₀, _, f, rfl⟩ := W.exists_map_eq_of_isElliptic
  exact W₀.liftNeg_additionMorphism_map f W₀.liftNeg_additionMorphism_of_isReduced

end WeierstrassCurve
