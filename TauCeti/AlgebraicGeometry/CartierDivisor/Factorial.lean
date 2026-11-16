/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.ClassGroup
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effectivity
public import TauCeti.AlgebraicGeometry.CartierDivisor.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial

/-!
# The Weil–Cartier and `Cl(X) ≃+ Pic(X)` equivalences on locally factorial schemes

Let `X` be a Noetherian integral scheme whose local rings are unique factorization domains (for
instance a regular scheme of dimension at most two, such as a regular model of a curve over a
discrete valuation ring). Each local ring `𝒪_{X,x}` is integrally closed, so `X` is normal
(`IsNormalScheme.of_uniqueFactorizationMonoid_stalk`), and the Cartier-to-Weil homomorphism
`D ↦ D.toWeilDivisor` is injective (`Scheme.CartierDivisor.toWeilDivisor_injective`).

Conversely, the closure `closure {η}` of each codimension-one point `η` is an effective Cartier
divisor (`Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton`) whose Cartier
divisor (`Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor`) has Weil divisor
`WeilDivisor.ofPoint η` (`toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton`).
Extending `ℤ`-linearly gives a two-sided inverse to `toWeilDivisorHom`, identifying Weil divisors
with Cartier divisors (`SchemeWeilDivisor.equivCartierDivisorOfUniqueFactorizationMonoid`) and
descending via `Scheme.CartierDivisor.classGroupAddEquivLineBundleClass` to an additive equivalence
between the Weil divisor class group `Cl(X)` and the Picard group `Additive (LineBundleClass X)`
(`SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid`).

## Main declarations

In the namespace `TauCeti.AlgebraicGeometry`:

* `toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton`: the Cartier divisor of
  `closure {η}` has Weil divisor `WeilDivisor.ofPoint η`;
* `SchemeWeilDivisor.equivCartierDivisorOfUniqueFactorizationMonoid`: the Weil–Cartier additive
  equivalence on Noetherian locally factorial integral schemes;
* `SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid`: the
  `Cl(X) ≃+ Pic(X)` additive equivalence on Noetherian locally factorial integral schemes.

## References

* [Stacks Project, Lemma 31.28.7 (0BE9)](https://stacks.math.columbia.edu/tag/0BE9) (the Picard
  group and Weil divisor class group on schemes with factorial stalks).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.11 and Corollary 6.16.
-/

public section

open _root_.AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

section LocallyFactorial

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- **The Weil divisor of a prime effective Cartier divisor.** On a Noetherian integral scheme with
factorial local rings, the Cartier divisor of the prime closed subscheme `closure {η}` has Weil
divisor `ofPoint η`. -/
@[simp]
theorem toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton [IsNoetherian X]
    (η : CodimensionOnePoint X) :
    (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
      η.2).toCartierDivisor.toWeilDivisor = WeilDivisor.ofPoint η := by
  apply WeilDivisor.ext
  intro ξ
  set hη := Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton η.2
  obtain ⟨U, hξU, a, ha, hUa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff _).mp hη (ξ : X)
  have : Nonempty U.1 := ⟨⟨ξ, hξU⟩⟩
  have ha0 : a ≠ 0 := fun h0 ↦ one_ne_zero (α := Γ(X, U)) (ha (by simp [h0] : a * 1 = a * 0))
  rw [hη.toCartierDivisor.coeff_toWeilDivisor_eq_ord ξ hξU _
      (hη.toCartierDivisor_restrict U ha0 hUa).symm,
    Units.val_mk0, ← X.algebraMap_germ_eq_germToFunctionField hξU a]
  set b := X.presheaf.germ U.1 ξ hξU a
  have hspan : ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {(η : X)}, isClosed_closure⟩).ideal U).map (X.presheaf.germ U.1 ξ hξU).hom =
      Ideal.span {b} := by
    rw [hUa, Ideal.map_span, Set.image_singleton]
  rcases eq_or_ne ξ η with rfl | hne
  · rw [WeilDivisor.coeff_ofPoint_self]
    rw [Scheme.IdealSheafData.map_ideal_vanishingIdeal_closure_singleton_of_specializes hξU
      specializes_rfl] at hspan
    exact Scheme.ord_algebraMap_stalk_eq_one ξ.2 specializes_rfl hspan
  · rw [WeilDivisor.coeff_ofPoint_of_ne hne]
    have hnot : ¬ (η : X) ⤳ (ξ : X) := fun hsp ↦
      hne (CodimensionOnePoint.eq_of_specializes hsp).symm
    rw [Scheme.IdealSheafData.map_ideal_vanishingIdeal_closure_singleton_of_not_specializes hξU
      hnot] at hspan
    have hu : IsUnit b := Ideal.span_singleton_eq_top.mp hspan.symm
    exact (Scheme.ord_algebraMap_stalk_eq_zero_iff ξ.2 specializes_rfl hu.ne_zero).mpr fun hm ↦
      (IsLocalRing.mem_maximalIdeal _).mp (by simpa using hm) hu

namespace SchemeWeilDivisor

/-- Auxiliary homomorphism sending a finitely supported Weil divisor on a locally Noetherian
locally factorial integral scheme to its Cartier divisor. -/
private def toCartierDivisorOfUniqueFactorizationMonoid [IsLocallyNoetherian X] :
    SchemeWeilDivisor X →+ Scheme.CartierDivisor X :=
  (Finsupp.linearCombination ℤ fun η : CodimensionOnePoint X ↦
    (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
      η.2).toCartierDivisor).toAddMonoidHom

private lemma toCartierDivisorOfUniqueFactorizationMonoid_ofPoint [IsLocallyNoetherian X]
    (η : CodimensionOnePoint X) :
    toCartierDivisorOfUniqueFactorizationMonoid (WeilDivisor.ofPoint η) =
      (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
        η.2).toCartierDivisor := by
  rw [← one_zsmul (WeilDivisor.ofPoint η), ← WeilDivisor.single_eq_zsmul_ofPoint,
    toCartierDivisorOfUniqueFactorizationMonoid]
  simp

variable [IsNoetherian X]

private lemma toWeilDivisor_toCartierDivisorOfUniqueFactorizationMonoid (D : SchemeWeilDivisor X) :
    (toCartierDivisorOfUniqueFactorizationMonoid D).toWeilDivisor = D := by
  have hcomp : Scheme.CartierDivisor.toWeilDivisorHom.comp
      (toCartierDivisorOfUniqueFactorizationMonoid (X := X)) = AddMonoidHom.id _ := by
    refine Finsupp.addHom_ext' fun η ↦ AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply,
      WeilDivisor.single_eq_zsmul_ofPoint, one_zsmul,
      Scheme.CartierDivisor.toWeilDivisorHom_apply,
      toCartierDivisorOfUniqueFactorizationMonoid_ofPoint,
      toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton, AddMonoidHom.id_apply]
  simpa only [AddMonoidHom.comp_apply, Scheme.CartierDivisor.toWeilDivisorHom_apply,
    AddMonoidHom.id_apply] using DFunLike.congr_fun hcomp D

/-- **The Weil–Cartier equivalence on locally factorial schemes.** On a Noetherian integral scheme
whose local rings are unique factorization domains, Weil divisors and Cartier divisors are
additively equivalent. Hartshorne, Proposition II.6.11. -/
def equivCartierDivisorOfUniqueFactorizationMonoid :
    SchemeWeilDivisor X ≃+ Scheme.CartierDivisor X where
  toFun := toCartierDivisorOfUniqueFactorizationMonoid
  invFun := Scheme.CartierDivisor.toWeilDivisor
  left_inv := toWeilDivisor_toCartierDivisorOfUniqueFactorizationMonoid
  right_inv D := Scheme.CartierDivisor.toWeilDivisor_injective
    (toWeilDivisor_toCartierDivisorOfUniqueFactorizationMonoid D.toWeilDivisor)
  map_add' := map_add toCartierDivisorOfUniqueFactorizationMonoid

/-- Evaluating the Weil–Cartier equivalence on `ofPoint η` gives the Cartier divisor of
`closure {η}`. -/
@[simp]
theorem equivCartierDivisorOfUniqueFactorizationMonoid_ofPoint (η : CodimensionOnePoint X) :
    equivCartierDivisorOfUniqueFactorizationMonoid (WeilDivisor.ofPoint η) =
      (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
        η.2).toCartierDivisor :=
  toCartierDivisorOfUniqueFactorizationMonoid_ofPoint η

/-- The inverse of the Weil–Cartier equivalence sends a Cartier divisor to its Weil divisor. -/
@[simp]
theorem equivCartierDivisorOfUniqueFactorizationMonoid_symm_apply (D : Scheme.CartierDivisor X) :
    equivCartierDivisorOfUniqueFactorizationMonoid.symm D = D.toWeilDivisor :=
  (rfl)

/-- Taking the Weil divisor of `equivCartierDivisorOfUniqueFactorizationMonoid D` recovers `D`. -/
@[simp]
theorem toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid (D : SchemeWeilDivisor X) :
    (equivCartierDivisorOfUniqueFactorizationMonoid D).toWeilDivisor = D :=
  toWeilDivisor_toCartierDivisorOfUniqueFactorizationMonoid D

/-- Applying `equivCartierDivisorOfUniqueFactorizationMonoid` to the Weil divisor of `D` recovers
`D`. -/
@[simp]
theorem equivCartierDivisorOfUniqueFactorizationMonoid_toWeilDivisor (D : Scheme.CartierDivisor X) :
    equivCartierDivisorOfUniqueFactorizationMonoid D.toWeilDivisor = D :=
  equivCartierDivisorOfUniqueFactorizationMonoid.apply_symm_apply D

/-- The Weil–Cartier equivalence on a Noetherian locally factorial integral scheme preserves
effectivity. -/
@[simp]
theorem isEffective_equivCartierDivisorOfUniqueFactorizationMonoid_iff (D : SchemeWeilDivisor X) :
    (equivCartierDivisorOfUniqueFactorizationMonoid D).IsEffective ↔ 0 ≤ D := by
  rw [Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg,
    toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid]

/-- The Weil–Cartier equivalence sends principal Weil divisors to principal Cartier divisors. -/
@[simp]
theorem equivCartierDivisorOfUniqueFactorizationMonoid_principalDivisor
    (g : Additive X.functionFieldˣ) :
    equivCartierDivisorOfUniqueFactorizationMonoid
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) =
      Scheme.principalCartierDivisor X g.toMul := by
  apply Scheme.CartierDivisor.toWeilDivisor_injective
  rw [toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid,
    Scheme.CartierDivisor.toWeilDivisor_principalCartierDivisor]

variable (X) in
/-- **`Cl(X) ≃+ Pic(X)` on locally factorial schemes.** On a Noetherian integral scheme whose local
rings are unique factorization domains, the Weil divisor class group is additively equivalent to
the Picard group of line-bundle classes. Stacks, Lemma 31.28.7 (0BE9); Hartshorne, Corollary
II.6.16. -/
@[stacks 0BE9]
def classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup ≃+ Additive (LineBundleClass X) :=
  (QuotientAddGroup.congr (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup
    (Scheme.CartierDivisor.principalSubgroup X) equivCartierDivisorOfUniqueFactorizationMonoid
    (by
      ext D
      simp only [AddSubgroup.mem_map, (WeilDivisor.OrderSystem.ofScheme X).mem_principalSubgroup,
        Scheme.CartierDivisor.mem_principalSubgroup]
      constructor
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨g.toMul, (equivCartierDivisorOfUniqueFactorizationMonoid_principalDivisor g).symm⟩
      · rintro ⟨f, hf⟩
        exact ⟨_, ⟨Additive.ofMul f, rfl⟩,
          (equivCartierDivisorOfUniqueFactorizationMonoid_principalDivisor _).trans hf⟩)).trans
    (Scheme.CartierDivisor.classGroupAddEquivLineBundleClass X)

/-- On the class of a Weil divisor `D`, the `Cl(X) ≃+ Pic(X)` equivalence sends `[D]` to the
line-bundle class of the corresponding Cartier divisor. -/
@[simp]
theorem classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass
    (D : SchemeWeilDivisor X) :
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D) =
      Additive.ofMul (equivCartierDivisorOfUniqueFactorizationMonoid D).toLineBundleClass := by
  rw [(WeilDivisor.OrderSystem.ofScheme X).divisorClass_eq_mk',
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid, AddEquiv.trans_apply]
  -- `QuotientAddGroup.congr` acts on `QuotientAddGroup.mk'` by applying the equivalence to a
  -- representative (`QuotientGroup.congr_mk'` is not tagged `@[to_additive]` in Mathlib).
  change Scheme.CartierDivisor.classGroupAddEquivLineBundleClass X
      (QuotientAddGroup.mk' (Scheme.CartierDivisor.principalSubgroup X)
        (equivCartierDivisorOfUniqueFactorizationMonoid D)) = _
  rw [← Scheme.CartierDivisor.divisorClass_eq_mk',
    Scheme.CartierDivisor.classGroupAddEquivLineBundleClass_divisorClass]

/-- The inverse of the `Cl(X) ≃+ Pic(X)` equivalence sends `[𝒪_X(D)]` to the Weil divisor class of
`D.toWeilDivisor`. -/
@[simp]
theorem classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_symm_toLineBundleClass
    (D : Scheme.CartierDivisor X) :
    (classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X).symm
        (Additive.ofMul D.toLineBundleClass) =
      (WeilDivisor.OrderSystem.ofScheme X).divisorClass D.toWeilDivisor := by
  have h := classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass
    (X := X) D.toWeilDivisor
  rw [equivCartierDivisorOfUniqueFactorizationMonoid_toWeilDivisor] at h
  rw [← h, AddEquiv.symm_apply_apply]

/-- The `Cl(X) ≃+ Pic(X)` equivalence sends the class of a prime divisor `ofPoint η` to the
inverse of the line-bundle class of the ideal sheaf of `closure {η}`, namely
`[𝒪_X(closure {η})]`. -/
theorem classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass_ofPoint
    (η : CodimensionOnePoint X) :
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass (WeilDivisor.ofPoint η)) =
      Additive.ofMul (LineBundleClass.mk
        (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
          η.2).toInvertibleSheaf)⁻¹ := by
  rw [classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass,
    equivCartierDivisorOfUniqueFactorizationMonoid_ofPoint,
    Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor]

end SchemeWeilDivisor

end LocallyFactorial

end

end TauCeti.AlgebraicGeometry
