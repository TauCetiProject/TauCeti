/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Unit
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Comm

/-!
# The unit law for the projective Weierstrass addition morphism

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W`, and
let `S = Spec R`. This file proves that the zero section is a right and a left identity for the
Bosma–Lenstra addition morphism `E ×_S E ⟶ E`.

The proof is scheme-theoretic over an arbitrary base. The standard charts `D₊(Y)` and `D₊(Z)`
cover `E`: the complement of `D₊(Z)` is exactly the zero section, which lies in `D₊(Y)`. On
`D₊(Z)`, the addition law attached to `Z = 0` evaluates at `(P, [0 : 1 : 0])` to `-P₂ • P`;
on `D₊(Y)`, the law attached to `Y = 0` evaluates to `P₁ • P`. The chosen chart coordinate is
one in each case, so both laws define the original projective point. The left unit law follows
from the right one, because the addition morphism is commutative
(`WeierstrassCurve.additionMorphism_comm`).

## Main results

* `WeierstrassCurve.additionMorphism_right_unit`: adding the zero section on the right is the
  identity morphism of `projModel W`.
* `WeierstrassCurve.additionMorphism_left_unit`: adding the zero section on the left is the
  identity morphism of `projModel W`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), `mulOver_oneOver` in
  `projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawAxioms.lean` at commit
  `c3415f32a313e19ace43e05479aeaa0d56ca287a`: a formalization of the same right unit law, proved
  by descent from a universal atlas and field-valued points rather than on two affine charts. The
  left unit law is deduced from the right one and commutativity as in `oneOver_mulOver`, in the
  same file.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

private theorem exists_mem_range_unitChart (x : W.projModel) :
    ∃ i : Fin 2, x ∈ Set.range (W.chartι i.succ) := by
  by_cases hx : x ∈ Set.range (W.chartι 2)
  · exact ⟨1, hx⟩
  · have hxZ : x ∉ Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) := by
      rw [← W.opensRange_chartι 2]
      exact fun h ↦ hx (Set.mem_range.mpr (Scheme.Hom.mem_opensRange.mp h))
    obtain ⟨q, rfl⟩ := (W.mem_range_projModelZero_iff x).mpr hxZ
    have hq : W.projModelZero q ∈ (W.chartι 1).opensRange := by
      rw [W.opensRange_chartι 1]
      exact (W.projModelZero_mem_basicOpen_iff q 1).2 rfl
    exact ⟨0, Set.mem_range.mpr (Scheme.Hom.mem_opensRange.mp hq)⟩

/-- The two affine charts `D₊(Y)` and `D₊(Z)` cover the projective Weierstrass model. -/
private noncomputable abbrev unitCover : W.projModel.AffineOpenCover where
  I₀ := Fin 2
  X i := .of (W.toProjective.ChartRing i.succ)
  f i := W.chartι i.succ
  idx x := (W.exists_mem_range_unitChart x).choose
  covers x := (W.exists_mem_range_unitChart x).choose_spec

-- Restricted to a standard chart, pairing a point with the zero section is the pair of their
-- homogeneous-coordinate descriptions.
private theorem chartι_comp_rightUnit (i : Fin 3) :
    W.chartι i ≫ pullback.lift (f := W.projModelOver) (g := W.projModelOver)
      (𝟙 W.projModel) (W.projModelOver ≫ W.projModelZero) (by simp) =
      pullback.lift (f := W.projModelOver) (g := W.projModelOver) (W.chartι i)
        (Spec.map (CommRingCat.ofHom (algebraMap R (W.toProjective.ChartRing i))) ≫
          W.projModelZero) (by simp) := by
  apply pullback.hom_ext <;> simp

/-- The zero section is a right identity for the Bosma–Lenstra addition morphism on the projective
Weierstrass model. This is an equality of scheme morphisms over an arbitrary commutative base
ring; in particular, it does not follow merely from an equality on geometric points. -/
@[reassoc (attr := simp)]
theorem additionMorphism_right_unit [W.IsElliptic] :
    pullback.lift (f := W.projModelOver) (g := W.projModelOver) (𝟙 W.projModel)
      (W.projModelOver ≫ W.projModelZero) (by simp) ≫ W.additionMorphism =
        𝟙 W.projModel := by
  refine W.unitCover.openCover.hom_ext _ _ fun (i : Fin 2) ↦ ?_
  dsimp only [unitCover, Scheme.AffineOpenCover.openCover, Scheme.AffineCover.cover]
    at i ⊢
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simp only [Category.comp_id]
    rw [Fin.succ_zero_eq_one']
    rw [← Category.assoc, W.chartι_comp_rightUnit 1]
    simp_rw [W.chartι_eq_projModelPoint, W.SpecMap_projModelZero]
    rw [W.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ (m := 1) _ _
      (by
        rw [congrFun (Projective.dblAddXYZ_zero_right
          (W.toProjective.map (algebraMap R (W.toProjective.ChartRing 1)))
          (W.toProjective.chartPoint 1)) 1]
        simp)]
    rw [projModelPoint_eq_projModelPoint_iff]
    refine ⟨rfl, 1, ?_⟩
    simp [Projective.dblAddXYZ_zero_right]
  · simp only [Category.comp_id]
    rw [Fin.succ_one_eq_two']
    rw [← Category.assoc, W.chartι_comp_rightUnit 2]
    simp_rw [W.chartι_eq_projModelPoint, W.SpecMap_projModelZero]
    rw [W.lift_projModelPoint_additionMorphism_of_isUnit_addXYZ (m := 2) _ _
      (by
        rw [congrFun (Projective.addXYZ_zero_right
          (W.toProjective.map (algebraMap R (W.toProjective.ChartRing 2)))
          (W.toProjective.chartPoint 2)) 2]
        have hP : IsUnit (W.toProjective.chartPoint 2 2) :=
          W.toProjective.chartPoint_self 2 ▸ isUnit_one
        simpa only [Pi.smul_apply, smul_eq_mul] using hP.neg.mul hP)]
    rw [projModelPoint_eq_projModelPoint_iff]
    refine ⟨rfl, -1, ?_⟩
    simp [Projective.addXYZ_zero_right, Units.smul_def]

/-- The zero section is a left identity for the Bosma–Lenstra addition morphism on the projective
Weierstrass model, over an arbitrary commutative base ring. -/
@[reassoc (attr := simp)]
theorem additionMorphism_left_unit [W.IsElliptic] :
    pullback.lift (f := W.projModelOver) (g := W.projModelOver)
      (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel) (by simp) ≫ W.additionMorphism =
        𝟙 W.projModel := by
  -- swapping the two factors turns the left unit law into the right one
  have h : pullback.lift (f := W.projModelOver) (g := W.projModelOver)
      (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel) (by simp) =
      pullback.lift (𝟙 W.projModel) (W.projModelOver ≫ W.projModelZero) (by simp) ≫
        (pullbackSymmetry _ _).hom := by
    apply pullback.hom_ext <;> simp
  rw [h, Category.assoc, additionMorphism_comm, additionMorphism_right_unit]

end WeierstrassCurve
