/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points

/-!
# Base change of the Bosma–Lenstra addition morphism

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model over `S = Spec R`, and let `f : R →+* R'` be a ring homomorphism. The curve
`W.map f` is elliptic, and its projective model `E' = projModel (W.map f)` over `S' = Spec R'` is
the base change of `E` along `Spec f`, through the base change morphism
`WeierstrassCurve.projModelBaseChange W f : E' ⟶ E`. This file shows that the Bosma–Lenstra
addition morphism `WeierstrassCurve.additionMorphism` is compatible with base change: the addition
morphism `E' ×_{S'} E' ⟶ E'` of `W.map f` followed by `E' ⟶ E` is the morphism
`E' ×_{S'} E' ⟶ E ×_S E` induced by `E' ⟶ E` followed by the addition morphism `E ×_S E ⟶ E` of
`W`.

The two composites are compared on the pieces of the chart cover
`WeierstrassCurve.additionCover` of `E' ×_{S'} E'`. Such a piece is a pair of points of `E'`, with
homogeneous coordinates `P` and `Q` having a unit coordinate each, at which one of the two addition
laws has a unit coordinate. The base change morphism does not change homogeneous coordinates
(`WeierstrassCurve.projModelPoint_projModelBaseChange`), and both addition morphisms send the pair
to the point whose homogeneous coordinates are the value of that law at `P` and `Q`.

## Main results

* `WeierstrassCurve.additionMorphism_projModelBaseChange`: the addition morphism commutes with
  base change along any ring homomorphism.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

The statement of `additionMorphism_projModelBaseChange` is adapted from AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawConstruction.lean`, declaration
`mulModelHom_map`. Only the statement is taken from the source. The source defines the addition
morphism of every elliptic curve by base change from the universal curve over a Jacobson domain
(`mulModelHomBC`, file `AdditionBaseChange.lean`), so that its compatibility with base change
follows from the uniqueness of a morphism into a fibre product. Here the addition morphism of
each curve is glued from its own chart cover, so the compatibility is checked piece by piece,
using `WeierstrassCurve.lift_projModelPoint_additionMorphism_of_isUnit_addXYZ` and
`WeierstrassCurve.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Algebra.TensorProduct (includeLeftRingHom includeRight)

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- A point `Spec φ` of the product of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)` is a pair of points of
-- `projModel W` with unit coordinates `Pᵢ` and `Qⱼ`, and `φ` takes the six law coordinates at the
-- universal points to the two laws at `P` and `Q`.
private theorem exists_SpecMap_chartPairι_eq_lift {A : CommRingCat.{u}} {i j : Fin 3}
    (φ : CommRingCat.of (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j) ⟶ A) :
    ∃ (g : R →+* A) (P Q : Fin 3 → A) (hP : (W.toProjective.map g).Equation P)
      (hQ : (W.toProjective.map g).Equation Q) (hi : IsUnit (P i)) (hj : IsUnit (Q j)),
      φ.hom ∘ W.chartPairLaw i j =
        Sum.elim ((W.toProjective.map g).addXYZ P Q) ((W.toProjective.map g).dblAddXYZ P Q) ∧
      Spec.map φ ≫ W.chartPairι i j =
        pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
          ((W.projModelPoint_projModelOver g hP hi).trans
            (W.projModelPoint_projModelOver g hQ hj).symm) := by
  -- a point `Spec α` of the chart `D₊(Xₘ)`, over `g`, has homogeneous coordinates the image under
  -- `α` of the universal point
  have key {m : Fin 3} (α : CommRingCat.of (W.toProjective.ChartRing m) ⟶ A) {g : R →+* A}
      (hg : α.hom.comp (algebraMap R _) = g) : ∃ hP hm, Spec.map α ≫ W.chartι m =
        W.projModelPoint g (P := α.hom ∘ W.toProjective.chartPoint m) (i := m) hP hm := by
    subst hg
    rw [W.chartι_eq_projModelPoint m]
    exact ⟨_, _, SpecMap_projModelPoint α.hom _⟩
  -- the two factors of `ChartRing i ⊗[R] ChartRing j` lie over the same homomorphism from `R`
  obtain ⟨hP, hi, h₁⟩ := key (CommRingCat.ofHom includeLeftRingHom ≫ φ)
    (g := (CommRingCat.ofHom (algebraMap R _) ≫ CommRingCat.ofHom includeLeftRingHom ≫ φ).hom) rfl
  obtain ⟨hQ, hj, h₂⟩ := key (CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom ≫ φ)
    (g := (CommRingCat.ofHom (algebraMap R _) ≫ CommRingCat.ofHom includeLeftRingHom ≫ φ).hom)
    (by simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc] using
      congrArg (φ.hom.comp ·) Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm)
  refine ⟨_, _, _, hP, hQ, hi, hj, W.comp_chartPairLaw φ, ?_⟩
  ext
  · rw [Category.assoc, chartPairι_fst, ← Spec.map_comp_assoc, h₁, pullback.lift_fst]
  · rw [Category.assoc, chartPairι_snd, ← Spec.map_comp_assoc, h₂, pullback.lift_snd]

variable {R' : Type u} [CommRing R'] (f : R →+* R')

section Points

variable {A : Type u} [CommRing A] {g : R' →+* A} {P Q : Fin 3 → A}
  {hP : ((W.map f).toProjective.map g).Equation P} {hQ : ((W.map f).toProjective.map g).Equation Q}
  {i j : Fin 3}

-- Base change sends the pair of points of `projModel (W.map f)` with homogeneous coordinates `P`
-- and `Q` to the pair of points of `projModel W` with the same homogeneous coordinates.
private theorem lift_projModelPoint_map_projModelBaseChange (hi : IsUnit (P i))
    (hj : IsUnit (Q j)) :
    pullback.lift ((W.map f).projModelPoint g hP hi) ((W.map f).projModelPoint g hQ hj)
        (((W.map f).projModelPoint_projModelOver g hP hi).trans
          ((W.map f).projModelPoint_projModelOver g hQ hj).symm) ≫
      pullback.map _ _ _ _ (W.projModelBaseChange f) (W.projModelBaseChange f)
        (Spec.map (CommRingCat.ofHom f)) (W.projModelBaseChange_projModelOver f).symm
        (W.projModelBaseChange_projModelOver f).symm =
      pullback.lift
        (W.projModelPoint (g.comp f) (by simpa only [← WeierstrassCurve.map_map] using hP) hi)
        (W.projModelPoint (g.comp f) (by simpa only [← WeierstrassCurve.map_map] using hQ) hj)
        ((W.projModelPoint_projModelOver _ _ hi).trans
          (W.projModelPoint_projModelOver _ _ hj).symm) := by
  ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
      projModelPoint_projModelBaseChange]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
      projModelPoint_projModelBaseChange]

-- On a pair of points of `projModel (W.map f)` at which the law selected by `k` has a unit
-- coordinate, adding and then changing the base is changing the base and then adding.
private theorem lift_projModelPoint_additionMorphism_projModelBaseChange [W.IsElliptic]
    (hi : IsUnit (P i)) (hj : IsUnit (Q j)) (k : Fin 3 ⊕ Fin 3)
    (hk : IsUnit (Sum.elim (((W.map f).toProjective.map g).addXYZ P Q)
      (((W.map f).toProjective.map g).dblAddXYZ P Q) k)) :
    pullback.lift ((W.map f).projModelPoint g hP hi) ((W.map f).projModelPoint g hQ hj)
        (((W.map f).projModelPoint_projModelOver g hP hi).trans
          ((W.map f).projModelPoint_projModelOver g hQ hj).symm) ≫
      (W.map f).additionMorphism ≫ W.projModelBaseChange f =
    pullback.lift ((W.map f).projModelPoint g hP hi) ((W.map f).projModelPoint g hQ hj)
        (((W.map f).projModelPoint_projModelOver g hP hi).trans
          ((W.map f).projModelPoint_projModelOver g hQ hj).symm) ≫
      pullback.map _ _ _ _ (W.projModelBaseChange f) (W.projModelBaseChange f)
        (Spec.map (CommRingCat.ofHom f)) (W.projModelBaseChange_projModelOver f).symm
        (W.projModelBaseChange_projModelOver f).symm ≫ W.additionMorphism := by
  rw [← Category.assoc, ← Category.assoc, W.lift_projModelPoint_map_projModelBaseChange f hi hj]
  -- both sides are the point of `projModel W` with homogeneous coordinates the law selected by
  -- `k` at `P` and `Q`, for the curve `(W.map f).map g = W.map (g.comp f)`
  rcases k with m | m <;> simp only [Sum.elim_inl, Sum.elim_inr] at hk
  · rw [(W.map f).lift_projModelPoint_additionMorphism_of_isUnit_addXYZ hi hj hk,
      projModelPoint_projModelBaseChange]
    simp only [WeierstrassCurve.map_map] at hk ⊢
    rw [W.lift_projModelPoint_additionMorphism_of_isUnit_addXYZ hi hj hk]
  · rw [(W.map f).lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ hi hj hk,
      projModelPoint_projModelBaseChange]
    simp only [WeierstrassCurve.map_map] at hk ⊢
    rw [W.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ hi hj hk]

end Points

/-- **The addition morphism commutes with base change.** Let `W` be an elliptic Weierstrass curve
over `R` and `f : R →+* R'` a ring homomorphism, and write `E = projModel W` over `S = Spec R` and
`E' = projModel (W.map f)` over `S' = Spec R'`. The Bosma–Lenstra addition morphism
`E' ×_{S'} E' ⟶ E'` of `W.map f`, followed by the base change morphism `E' ⟶ E`, is the morphism
`E' ×_{S'} E' ⟶ E ×_S E` induced by the base change morphism on both factors, followed by the
addition morphism `E ×_S E ⟶ E` of `W`. -/
@[reassoc (attr := simp)]
theorem additionMorphism_projModelBaseChange [W.IsElliptic] :
    (W.map f).additionMorphism ≫ W.projModelBaseChange f =
      pullback.map _ _ _ _ (W.projModelBaseChange f) (W.projModelBaseChange f)
        (Spec.map (CommRingCat.ofHom f)) (W.projModelBaseChange_projModelOver f).symm
        (W.projModelBaseChange_projModelOver f).symm ≫ W.additionMorphism := by
  refine (W.map f).additionCover.openCover.hom_ext _ _ fun ⟨⟨i, j⟩, k⟩ ↦ ?_
  -- the piece of the chart cover indexed by `((i, j), k)` is a pair of points of
  -- `projModel (W.map f)` with unit coordinates, at which the law selected by `k` has the unit
  -- coordinate `chartPairLaw i j k`
  obtain ⟨g, P, Q, hP, hQ, hi, hj, hlaw, h⟩ := (W.map f).exists_SpecMap_chartPairι_eq_lift
    (i := i) (j := j) (CommRingCat.ofHom (algebraMap _
      (Localization.Away ((W.map f).chartPairLaw i j k))))
  rw [Scheme.AffineOpenCover.openCover_f, additionCover_f, h]
  exact W.lift_projModelPoint_additionMorphism_projModelBaseChange f hi hj k
    (by simpa only [← hlaw, Function.comp_apply, CommRingCat.hom_ofHom] using
      IsLocalization.Away.algebraMap_isUnit ((W.map f).chartPairLaw i j k))

end WeierstrassCurve
