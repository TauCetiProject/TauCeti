/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.IdealSheaf
import TauCeti.AlgebraicGeometry.IdealSheaf.RestrictionEulerCharacteristic
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Surface intersection as the degree on a Cartier curve

For an effective Cartier divisor `D = V(I)` on a projective scheme over a field, the
surface intersection of `𝒪_X(D)` with a line bundle is its degree on `D`, provided `D`
is integral of dimension at most one.

The comparison uses the twisted ideal sequence
`0 → L ⊗ I → L → i_* (L|D) → 0`. Its Euler characteristics are truncated at degree
three on `X` and degree two on `D`. The vanishing of `H²(D, L|D)` makes the
connecting map cut off by the degree-three truncation zero.

## References

* [The Stacks Project, Lemma 33.45.8, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU),
  the comparison in dimension two using the exact sequence of an effective Cartier divisor.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] (I : X.IdealSheafData) (hI : I.IsEffectiveCartier)

private lemma classEulerCharBelow_sub_mul_mk (a : LineBundleClass X)
    (hvan : ∀ L : InvertibleSheaf X, Subsingleton (Scheme.Modules.Cohomology
      ((InvertibleSheaf.pullback I.subschemeι).obj L).obj 2)) :
    LineBundleClass.eulerCharBelow k a 3 -
        LineBundleClass.eulerCharBelow k (a * LineBundleClass.mk hI.toInvertibleSheaf) 3 =
      LineBundleClass.eulerCharBelow k (LineBundleClass.pullback I.subschemeι a) 2 := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  let E := (InvertibleSheaf.toFiniteLocallyFree X).obj L
  let e := InvertibleSheaf.tensorProductObjIso L hI.toInvertibleSheaf ≪≫
    whiskerLeftIso L.obj (eqToIso hI.toInvertibleSheaf_obj)
  have h := I.eulerCharBelow_sub_tensor_sheaf k E 2
    (fun i _ _ ↦ (finiteDimensional_cohomology_congr k e i).mp inferInstance)
    (fun _ _ ↦ inferInstance)
    (by simpa only [E, InvertibleSheaf.pullback_toFiniteLocallyFree_obj_obj] using hvan L)
  rw [← LineBundleClass.mk_tensorProduct, LineBundleClass.pullback_mk,
    LineBundleClass.eulerCharBelow_mk, LineBundleClass.eulerCharBelow_mk,
    LineBundleClass.eulerCharBelow_mk, eulerCharBelow_congr k e 3]
  rw [InvertibleSheaf.pullback_toFiniteLocallyFree_obj_obj] at h
  exact h

/-- The surface intersection of an effective Cartier divisor with a line-bundle class
is the degree of the restricted class on the divisor, when the divisor is integral
of dimension at most one. -/
@[stacks 0BEU "the dimension-two comparison, using the twisted ideal sequence"]
theorem classIntersectionNumber_inv_mk_toInvertibleSheaf [IsIntegral I.subscheme]
    (hdim : topologicalKrullDim I.subscheme ≤ 1) (a : LineBundleClass X) :
    classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ a =
      LineBundleClass.intersectionNumber k I.subschemeι a := by
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hdim
  have hO₂ := Scheme.Modules.subsingleton_cohomology_trivial_of_topologicalKrullDim_le_one
    k hdim 2 le_rfl
  have hvan (L : InvertibleSheaf X) := InvertibleSheaf.subsingleton_cohomology_of_isIntegral k
    ((InvertibleSheaf.pullback I.subschemeι).obj L) le_rfl hO₂
  have hO := classEulerCharBelow_sub_mul_mk k I hI 1 hvan
  have hL := classEulerCharBelow_sub_mul_mk k I hI a⁻¹ hvan
  have hinv := LineBundleClass.intersectionNumber_inv_of_isIntegral k I.subschemeι a
  rw [LineBundleClass.intersectionNumber_def,
    LineBundleClass.eulerDegree_eq_eulerCharBelow_sub] at hinv
  simp only [one_mul, LineBundleClass.pullback_one] at hO
  rw [classIntersectionNumber_eq, inv_inv,
    mul_comm (LineBundleClass.mk hI.toInvertibleSheaf)]
  linarith

/-- For an effective Cartier divisor, the surface pairing of its native Cartier class
is the degree on the closed subscheme defined by its sections ideal. -/
theorem classIntersectionNumber_toLineBundleClass_of_isEffective [IsIntegral X]
    (D : Scheme.CartierDivisor X) (hD : D.IsEffective)
    [IsIntegral hD.sectionsIdealSheaf.subscheme]
    (hdim : topologicalKrullDim hD.sectionsIdealSheaf.subscheme ≤ 1)
    (a : LineBundleClass X) :
    classIntersectionNumber k X D.toLineBundleClass a =
      LineBundleClass.intersectionNumber k hD.sectionsIdealSheaf.subschemeι a := by
  simpa only [hD.mk_toInvertibleSheaf_sectionsIdealSheaf, inv_inv] using
    classIntersectionNumber_inv_mk_toInvertibleSheaf k hD.sectionsIdealSheaf
      hD.isEffectiveCartier_sectionsIdealSheaf hdim a

/-- When a second effective Cartier divisor meets the integral Cartier curve properly,
the surface pairing is the residue-degree-weighted sum of ambient local intersection lengths. -/
theorem classIntersectionNumber_inv_mk_toInvertibleSheaf_eq_finsum
    [IsIntegral I.subscheme] (hdim : topologicalKrullDim I.subscheme ≤ 1)
    {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (hJI : (J.comap I.subschemeι).IsEffectiveCartier) :
    classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ =
      ∑ᶠ y : I.subscheme, ((I.subscheme ↘ Spec (.of k)).residueDegree y : ℤ) *
        (Module.length (X.presheaf.stalk (I.subschemeι y))
          (X.presheaf.stalk (I.subschemeι y) ⧸
            (J.stalkIdeal (I.subschemeι y) ⊔ I.stalkIdeal (I.subschemeι y)))).toNat := by
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hdim
  rw [classIntersectionNumber_inv_mk_toInvertibleSheaf k I hI hdim,
    LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf_eq_finsum_of_isClosedImmersion
      k I.subschemeι hJ hJI, I.ker_subschemeι]

end TauCeti.AlgebraicGeometry.Chow
