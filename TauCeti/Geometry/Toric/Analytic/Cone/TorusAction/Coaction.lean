/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Scheme
public import TauCeti.Geometry.Toric.Analytic.Character.Action

/-!
# The affine toric coaction on complex points

Evaluating the affine coordinate-ring coaction at a complex torus point and an affine complex
point recovers the existing character action on the latter. The torus point is represented on
the zero-cone coordinate ring by translating its distinguished point. Thus the algebraic
coaction and the analytic action use the same characters, without choosing a lattice basis.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open Multiplicative
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- Evaluating the affine toric coaction against the torus point `t` and the chart point `x`
gives the existing action `t • x` on complex points. The torus point is realized in the
zero-cone chart as `t • default`. -/
@[simp]
theorem affineCoordinateRingCoaction_eval (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (t : ComplexTorus N)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    (Algebra.TensorProduct.lift
      (t • (default : AffineSemigroupComplexPoint (dualSemigroup hi (⊥ : PointedCone ℝ V))))
      x (fun _ _ ↦ Commute.all _ _)).comp (affineCoordinateRingCoaction hi σ) = t • x := by
  apply AffineSemigroupComplexPoint.ext
  intro m
  simp only [AlgHom.comp_apply, affineCoordinateRingCoaction_single,
    Algebra.TensorProduct.lift_tmul, AffineSemigroupComplexPoint.ambient_smul_apply_single,
    default_apply_single, mul_one]

/-- On complex points, the affine scheme action is the character action. The two points of the
action domain are paired by the fibre-product universal property over `Spec ℂ`.

The comparison is intended for explicit rewrites: applying it again to the translated torus point
in the pairing would produce an infinite expansion. -/
@[reassoc]
theorem specMap_smul_eq_lift_comp_affineToricSchemeAction
    {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (t : ComplexTorus N)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    Spec.map (CommRingCat.ofHom (t • x).toRingHom) =
      pullback.lift
        (Spec.map (CommRingCat.ofHom
          (t • (default : AffineSemigroupComplexPoint (dualSemigroup hi ⊥))).toRingHom))
        (Spec.map (CommRingCat.ofHom x.toRingHom)) (by simp [← Spec.map_comp,
          ← CommRingCat.ofHom_comp]) ≫
        affineToricSchemeAction hi σ := by
  let y := t • (default : AffineSemigroupComplexPoint (dualSemigroup hi ⊥))
  let e := Algebra.TensorProduct.lift y x (fun _ _ ↦ Commute.all _ _)
  have hp : pullback.lift
      (Spec.map (CommRingCat.ofHom y.toRingHom))
      (Spec.map (CommRingCat.ofHom x.toRingHom)) (by simp [← Spec.map_comp,
        ← CommRingCat.ofHom_comp]) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        (pullbackSpecIso ℂ (affineCoordinateRing hi ⊥) (affineCoordinateRing hi σ)).inv := by
    apply pullback.hom_ext <;>
      simp only [pullback.lift_fst, pullback.lift_snd, Category.assoc,
        pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
    all_goals
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      simp [e]
  rw [hp, Category.assoc, pullbackSpecIso_inv_comp_affineToricSchemeAction,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (affineCoordinateRingCoaction_eval hi σ t x).symm

end TauCeti.Toric
