/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RealPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Cokernels of isogenies on real points

For a nonzero morphism of real elliptic curves, every double is in the image on real points.
Indeed, lift a real point to a complex point and add the lift to its conjugate. This sum
descends to a real point and maps to twice the original point. Together with the dual identity,
this proves surjectivity for odd-degree isogenies.

The real cokernel is finite. Thus the real local cokernel/kernel factor in the isogeny
transformation of the BSD quotient has an honest finite numerator, and that numerator is one
for odd-degree isogenies.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.6 and X.4.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {W₁ W₂ : WeierstrassCurve ℝ} [W₁.IsElliptic] [W₂.IsElliptic]

/-- Every double of a real point is in the image of a nonzero morphism of real elliptic curves.
Equivalently, its cokernel on real points is killed by two. -/
theorem two_nsmul_mem_range_pointMapHom (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0)
    (P : W₂.toAffine.Point) : 2 • P ∈ f.pointMapHom.range := by
  classical
  let fc := f.map (algebraMap ℝ ℂ)
  -- These type ascriptions align `Point.map`'s base-change spelling with the mapped curves.
  -- Instance synthesis does not unfold the two spellings when forming sums.
  let i₁ : W₁.toAffine.Point →+ (W₁.toAffine.map (algebraMap ℝ ℂ)).Point :=
    Point.map (W' := W₁) (Algebra.ofId ℝ ℂ)
  let i₂ : W₂.toAffine.Point →+ (W₂.toAffine.map (algebraMap ℝ ℂ)).Point :=
    Point.map (W' := W₂) (Algebra.ofId ℝ ℂ)
  have hfc : fc ≠ 0 := (f.map_eq_zero_iff _).not.mpr hf
  obtain ⟨Q, hQ⟩ := pointMap_surjective hfc (i₂ P)
  let cQ : (W₁.toAffine.map (algebraMap ℝ ℂ)).Point := Point.map Complex.conjAe.toAlgHom Q
  obtain ⟨R, hR⟩ := Point.exists_map_eq_add_conj (W := W₁) Q
  have hR : i₁ R = Q + cQ := hR
  refine ⟨R, Point.map_injective (W' := W₂) (Algebra.ofId ℝ ℂ) ?_⟩
  have hreal (S : W₁.toAffine.Point) : fc.pointMap (i₁ S) = i₂ (f.pointMap S) := by
    exact (congrArg fc.pointMap (Point.mapAlong_eq_map (W := W₁) S).symm).trans
      ((f.pointMap_map (algebraMap ℝ ℂ) S).trans
        (Point.mapAlong_eq_map (W := W₂) (f.pointMap S)))
  have hconj : Point.map Complex.conjAe.toAlgHom (i₂ P) = i₂ P :=
    (Point.exists_map_eq_iff_map_conj_eq_self _).mp ⟨P, rfl⟩
  calc
    i₂ (f.pointMapHom R) = i₂ (f.pointMap R) := congrArg i₂ (f.pointMapHom_apply R)
    _ = fc.pointMap (i₁ R) := (hreal R).symm
    _ = fc.pointMap (Q + cQ) := congrArg fc.pointMap hR
    _ = fc.pointMap Q + fc.pointMap cQ := fc.pointMap_add _ _
    _ = i₂ P + i₂ P := congrArg₂ (· + ·) hQ
      ((f.pointMap_map_algebraMap_map Complex.conjAe.toAlgHom Q).trans
        ((congrArg (Point.map Complex.conjAe.toAlgHom) hQ).trans hconj))
    _ = i₂ (2 • P) := by rw [two_nsmul, _root_.map_add]

/-- An odd-degree isogeny is surjective on real points. -/
theorem pointMap_surjective_of_odd_degree (f : Hom W₁.toAffine W₂.toAffine)
    (hdeg : Odd f.degree) : Function.Surjective f.pointMap := by
  classical
  have hf : f ≠ 0 := fun h ↦ by simp [h] at hdeg
  obtain ⟨k, hk⟩ := hdeg
  intro P
  obtain ⟨Q, hQ⟩ := f.two_nsmul_mem_range_pointMapHom hf P
  refine ⟨f.dual.pointMap P - k • Q, ?_⟩
  calc
    f.pointMap (f.dual.pointMap P - k • Q) =
        f.pointMapHom (f.dual.pointMap P - k • Q) := (f.pointMapHom_apply _).symm
    _ = f.pointMapHom (f.dual.pointMap P) - k • f.pointMapHom Q := by
      simp only [_root_.map_sub, _root_.map_nsmul]
    _ = f.degree • P - k • (2 • P) := by simp [hQ, pointMap_dual_pointMap]
    _ = P := by
      simp only [hk, add_nsmul, mul_nsmul, one_nsmul]
      abel

/-- The image of a nonzero morphism of real elliptic curves has finite index in the target's
real point group. In particular, its cokernel is finite. -/
theorem finiteIndex_range_pointMapHom_real (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    f.pointMapHom.range.FiniteIndex := by
  classical
  obtain ⟨φ, rfl⟩ := f.eq_zero_or_exists_ofIsogeny.resolve_left hf
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hperiod := φ.abs_mul_realPeriod_mul_index_eq_card_ker_mul hc
  have := (ofIsogeny φ).finite_ker_pointMapHom (ofIsogeny_ne_zero φ)
  apply AddSubgroup.finiteIndex_iff.mpr
  intro hz
  rw [hz, Nat.cast_zero, mul_zero] at hperiod
  have hpos : (0 : ℝ) < Nat.card (ofIsogeny φ).pointMapHom.ker * W₂.realPeriod :=
    mul_pos (Nat.cast_pos.mpr Nat.card_pos) W₂.realPeriod_pos
  linarith

end TauCeti.Isogeny.Hom
