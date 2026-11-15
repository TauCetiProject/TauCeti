/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FormalPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Projective

/-!
# The addition morphism at the formal point

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model, and let `z₁` and `z₂` be the two variables of
`R⟦z₁, z₂⟧ = MvPowerSeries (Unit ⊕ Unit) R`. In the parameter `z = -X / Y` at the zero section, the
formal point of `E` (`WeierstrassCurve.projModelFormalPoint`) reparametrised by `X ↦ zᵢ` has
homogeneous coordinates `[zᵢ : -1 : w(zᵢ)]`, where `w` is the `w`-expansion `formalW W`. This file
proves that the Bosma–Lenstra addition morphism `E ×_{Spec R} E ⟶ E` sends this pair of points to
the formal point reparametrised by `X ↦ F(z₁, z₂)`, where `F = formalAdd W` is the addition series
of the chord construction (`WeierstrassCurve.lift_projModelFormalPoint_additionMorphism`). In other
words, the group law of `E`, written in the formal parameter along the zero section, is the formal
group law `F` (packaged as Mathlib's `FormalGroup` in `WeierstrassCurve.formalGroup`). It is the
input for reading statements about closed subschemes of `E` supported on the zero section, such as
the divisors `n[0]` being subgroup schemes, as statements about `F`.

The algebraic input comes from `TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Projective`:
the `Y`-coordinate of `dblAddXYZ` at `[z₁ : -1 : w(z₁)]` and `[z₂ : -1 : w(z₂)]` is a unit
(`WeierstrassCurve.isUnit_dblAddY_formalW`), so the addition morphism is computed by that law, and
its value is a unit multiple of `(F(z₁, z₂), -1, w(F(z₁, z₂)))`
(`WeierstrassCurve.dblAddXYZ_formalW_eq_smul`).

## Main results

* `WeierstrassCurve.lift_projModelFormalPoint_additionMorphism`: the addition morphism sends the
  pair of formal points reparametrised by `X ↦ z₁` and `X ↦ z₂` to the formal point
  reparametrised by `X ↦ F(z₁, z₂)`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §5.3, where the formal group law of an elliptic curve in a
  parameter along the zero section is used to study subgroup schemes supported on the zero section.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace WeierstrassCurve

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- **The addition morphism at the formal point.** Let `z₁` and `z₂` be the two variables of
`R⟦z₁, z₂⟧`. The Bosma–Lenstra addition morphism `E ×_{Spec R} E ⟶ E` of the projective model
`E = projModel W` sends the pair of formal points reparametrised by `X ↦ z₁` and by `X ↦ z₂` to
the formal point reparametrised by `X ↦ F(z₁, z₂)`, where `F = formalAdd W` is the addition series
of the chord construction. That is, the group law of `E`, written in the parameter `z = -X / Y`
at the zero section, is the formal group law `F`. -/
theorem lift_projModelFormalPoint_additionMorphism [W.IsElliptic] :
    pullback.lift
        (Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
          (PowerSeries.HasSubst.X (S := R) (Sum.inl () : Unit ⊕ Unit))).toRingHom) ≫
            W.projModelFormalPoint)
        (Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
          (PowerSeries.HasSubst.X (S := R) (Sum.inr () : Unit ⊕ Unit))).toRingHom) ≫
            W.projModelFormalPoint)
        (by simp only [Category.assoc, projModelFormalPoint_projModelOver, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]) ≫
          W.additionMorphism =
      Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
        (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalAdd)).toRingHom) ≫
          W.projModelFormalPoint := by
  simp only [SpecMap_substAlgHom_projModelFormalPoint]
  -- the `Y`-coordinate of `dblAddXYZ` is a unit, so the addition morphism is computed by that law,
  -- whose value is a unit multiple of `(F, -1, w(F))`
  have hY := W.isUnit_dblAddY_formalW
  rw [W.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ (m := 1) _ _
    (by simpa using hY), projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, -hY.unit, by rw [dblAddXYZ_formalW_eq_smul, Units.smul_def, Units.val_neg,
    IsUnit.unit_spec]⟩

end WeierstrassCurve
