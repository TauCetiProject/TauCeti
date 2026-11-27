/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Restriction
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.LinearAlgebra.BilinearMap.IntLinear

/-!
# Bilinearity of the surface intersection pairing

On an integral projective scheme of dimension at most two with factorial local rings, the
intersection pairing on line-bundle classes is additive in each argument. Prime divisors
generate the Picard group, and intersection with each prime divisor is the degree of the
restricted line bundle on its integral curve.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter V, Section 1.
* The Stacks Project, Tags 0BEU and 0BE9 (restriction to Cartier divisors and locally factorial
  schemes).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

private lemma classIntersectionNumber_third_difference (a b c : LineBundleClass X) :
    classIntersectionNumber k X (a * c) b - classIntersectionNumber k X a b =
      classIntersectionNumber k X c (a * b) - classIntersectionNumber k X c a := by
  simp only [classIntersectionNumber_eq, mul_inv_rev]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

private def intersectionAdditiveClasses : Subgroup (LineBundleClass X) where
  carrier := {c | ∀ a b, classIntersectionNumber k X (a * c) b =
    classIntersectionNumber k X a b + classIntersectionNumber k X c b}
  one_mem' := by simp
  mul_mem' := by
    intro c d hc hd a b
    rw [← mul_assoc, hd, hc, hd]
    ring
  inv_mem' := by
    intro c hc a b
    have h := hc (a * c⁻¹) b
    have h₁ := hc c⁻¹ b
    simp only [inv_mul_cancel_right, inv_mul_cancel, classIntersectionNumber_one_left] at h h₁
    linarith

variable [X.IsProjectiveOver k] [IsIntegral X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

private lemma primeClass_mem_intersectionAdditiveClasses [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 2) (η : CodimensionOnePoint X) :
    (LineBundleClass.mk
      (isEffectiveCartier_vanishingIdeal_closure_singleton η.property).toInvertibleSheaf)⁻¹ ∈
        intersectionAdditiveClasses k (X := X) := by
  let I := vanishingIdeal (⟨closure {(η : X)}, isClosed_closure⟩ : Closeds X)
  let hI : I.IsEffectiveCartier :=
    isEffectiveCartier_vanishingIdeal_closure_singleton η.property
  have hIproj : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have hdimI : topologicalKrullDim I.subscheme ≤ 1 := by
    rw [← topologicalKrullDim_range_of_isPreimmersion I.subschemeι,
      range_subschemeι, coe_support_vanishingIdeal]
    refine topologicalKrullDim_closure_singleton_le_of_not_isMax (d := 1) ?_ ?_
    · intro x
      exact WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans hdim)
    · exact Order.coheight_ne_zero.mp (by simp [η.property])
  have : RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hdimI
  intro a b
  have h := classIntersectionNumber_third_difference k a b
    (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
  rw [classIntersectionNumber_inv_mk_toInvertibleSheaf k I hI hdimI,
    classIntersectionNumber_inv_mk_toInvertibleSheaf k I hI hdimI,
    LineBundleClass.intersectionNumber_mul_of_isIntegral] at h
  rw [classIntersectionNumber_inv_mk_toInvertibleSheaf k I hI hdimI]
  linarith

private lemma intersectionAdditiveClasses_eq_top [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 2) : intersectionAdditiveClasses k (X := X) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨D, hD⟩ := Scheme.CartierDivisor.weilToLineBundleClassHom_surjective
    (X := X) (Additive.ofMul a)
  have hmem : (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul ∈
      intersectionAdditiveClasses k (X := X) := by
    clear hD
    induction D using Finsupp.induction_linear with
    | zero => simp only [map_zero, toMul_zero]; exact
        (intersectionAdditiveClasses k (X := X)).one_mem
    | add D E hD hE =>
      simpa only [map_add, toMul_add] using
        (intersectionAdditiveClasses k (X := X)).mul_mem hD hE
    | single η n =>
      rw [Scheme.CartierDivisor.weilToLineBundleClassHom_single, toMul_zsmul]
      exact (intersectionAdditiveClasses k (X := X)).zpow_mem
        (primeClass_mem_intersectionAdditiveClasses k hdim η) n
  simpa only [hD, toMul_ofMul] using hmem

/-- The surface intersection pairing is additive in its first line-bundle class on a projective
integral scheme of dimension at most two with factorial local rings. -/
theorem classIntersectionNumber_mul_left (hdim : topologicalKrullDim X ≤ 2)
    (a b c : LineBundleClass X) :
    classIntersectionNumber k X (a * b) c =
      classIntersectionNumber k X a c + classIntersectionNumber k X b c := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have hb : b ∈ intersectionAdditiveClasses k (X := X) := by
    rw [intersectionAdditiveClasses_eq_top k hdim]
    trivial
  exact hb a c

/-- The surface intersection pairing is additive in its second line-bundle class on a projective
integral scheme of dimension at most two with factorial local rings. -/
theorem classIntersectionNumber_mul_right (hdim : topologicalKrullDim X ≤ 2)
    (a b c : LineBundleClass X) :
    classIntersectionNumber k X a (b * c) =
      classIntersectionNumber k X a b + classIntersectionNumber k X a c := by
  rw [classIntersectionNumber_comm, classIntersectionNumber_mul_left k hdim,
    classIntersectionNumber_comm b a, classIntersectionNumber_comm c a]

/-- The integral intersection form on the Picard group of a projective integral scheme
of dimension at most two with factorial local rings. -/
noncomputable def classIntersectionForm (hdim : topologicalKrullDim X ≤ 2) :
    LinearMap.BilinForm ℤ (Additive (LineBundleClass X)) :=
  (AddMonoidHom.mk'
    (fun a : Additive (LineBundleClass X) ↦ AddMonoidHom.mk'
      (fun b : Additive (LineBundleClass X) ↦ classIntersectionNumber k X a.toMul b.toMul)
      (fun b c ↦ classIntersectionNumber_mul_right k hdim a.toMul b.toMul c.toMul))
    (fun a b ↦ AddMonoidHom.ext fun c ↦
      classIntersectionNumber_mul_left k hdim a.toMul b.toMul c.toMul)).toIntLinearMap₂

@[simp]
theorem classIntersectionForm_apply (hdim : topologicalKrullDim X ≤ 2)
    (a b : Additive (LineBundleClass X)) :
    classIntersectionForm k hdim a b = classIntersectionNumber k X a.toMul b.toMul := by
  simp [classIntersectionForm]

/-- The integral intersection form on the Picard group is symmetric. -/
theorem classIntersectionForm_isSymm (hdim : topologicalKrullDim X ≤ 2) :
    (classIntersectionForm k hdim).IsSymm :=
  ⟨fun a b ↦ by simpa only [classIntersectionForm_apply] using
    classIntersectionNumber_comm (k := k) a.toMul b.toMul⟩

end TauCeti.AlgebraicGeometry.Chow
