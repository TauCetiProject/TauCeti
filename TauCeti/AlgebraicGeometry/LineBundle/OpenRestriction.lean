/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# Restriction of line-bundle classes to dense open subschemes

Let `X` be a Noetherian integral scheme whose local rings are unique factorization domains (for
instance a regular scheme all of whose points have codimension at most two, such as a regular model
of a curve over a discrete valuation ring), and let `j : U ⟶ X` be an open immersion from a
nonempty scheme `U`. Under the Weil–Cartier Picard group isomorphism
`Cl(X) ≃+ Additive (LineBundleClass X)` of `TauCeti.AlgebraicGeometry.CartierDivisor.Factorial`,
pullback of line-bundle classes along `j` corresponds to restriction of Weil divisors along the
injection of codimension-one points `CodimensionOnePoint U → CodimensionOnePoint X`.

The open-immersion Picard excision results built on this equivalence (surjectivity of
`LineBundleClass.pullback j` and the description of its kernel) are in
`TauCeti.AlgebraicGeometry.CartierDivisor.Excision`.

## Main declarations

In the namespace `TauCeti.AlgebraicGeometry.LineBundleClass`:

* `pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_of_isOpenImmersion` and
  `pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_eq_one_of_notMem_range`: pulling
  back the invertible ideal sheaf of `closure {x}` along an open immersion;
* `toAdditive_pullbackHom_classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass`
  proves compatibility of `Cl ≃+ Pic` with pullback along a nonempty open immersion.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.5.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Order _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace LineBundleClass

open Scheme.IdealSheafData SchemeWeilDivisor

section VanishingIdealPullback

variable {U X : Scheme.{u}}

/-- Along an open immersion `j : U ⟶ X`, if `closure {j u}` and `closure {u}` are effective Cartier
divisors on `X` and `U`, then the line-bundle class of the vanishing ideal sheaf of `closure {j u}`
pulls back to that of `closure {u}`. -/
theorem pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_of_isOpenImmersion
    (j : U ⟶ X) [IsOpenImmersion j] {u : U}
    (hju : (vanishingIdeal ⟨closure {j u}, isClosed_closure⟩).IsEffectiveCartier)
    (hu : (vanishingIdeal ⟨closure {u}, isClosed_closure⟩).IsEffectiveCartier) :
    pullback j (mk hju.toInvertibleSheaf) = mk hu.toInvertibleSheaf := by
  have hcomap := comap_vanishingIdeal_closure_singleton_of_isOpenImmersion j u
  have hU : ((vanishingIdeal ⟨closure {j u}, isClosed_closure⟩).comap j).IsEffectiveCartier :=
    hcomap ▸ hu
  rw [hju.pullback_mk_toInvertibleSheaf hU, mk_toInvertibleSheaf_congr hU hu hcomap]

/-- Along an open immersion `j : U ⟶ X`, if `closure {x}` is an effective Cartier divisor on `X` for
a point `x ∉ Set.range j`, then the line-bundle class of its vanishing ideal sheaf pulls back to `1`
on `U`. -/
theorem pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_eq_one_of_notMem_range
    (j : U ⟶ X) [IsOpenImmersion j] {x : X} (hx : x ∉ Set.range j)
    (h : (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).IsEffectiveCartier) :
    pullback j (mk h.toInvertibleSheaf) = 1 := by
  have hcomap := comap_vanishingIdeal_closure_singleton_eq_top_of_notMem_range j hx
  have hU : ((vanishingIdeal ⟨closure {x}, isClosed_closure⟩).comap j).IsEffectiveCartier :=
    hcomap ▸ isEffectiveCartier_top U
  rw [h.pullback_mk_toInvertibleSheaf hU,
    mk_toInvertibleSheaf_congr hU (isEffectiveCartier_top U) hcomap, mk_toInvertibleSheaf_top]

end VanishingIdealPullback

section Factorial

variable {U X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- **Compatibility of `Cl ≃+ Pic` with open restriction.** On a Noetherian locally factorial
integral scheme `X`, pulling back the line-bundle class attached to a Weil divisor `D` along a
nonempty open immersion `j : U ⟶ X` agrees with restricting `D` to `U` and taking its line-bundle
class. -/
theorem
    toAdditive_pullbackHom_classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U] (D : SchemeWeilDivisor X) :
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : IsNoetherian U := isNoetherian_of_isOpenImmersion j
    letI := j.uniqueFactorizationMonoid_stalk_of_isOpenImmersion
    MonoidHom.toAdditive (pullbackHom j)
        (SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
          ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D)) =
      SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid U
        ((WeilDivisor.OrderSystem.ofScheme U).divisorClass
          (WeilDivisor.pullback (CodimensionOnePoint.mapOfIsOpenImmersion_injective j) D)) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsNoetherian U := isNoetherian_of_isOpenImmersion j
  have := j.uniqueFactorizationMonoid_stalk_of_isOpenImmersion
  let φ : SchemeWeilDivisor X →+ Additive (LineBundleClass U) :=
    (MonoidHom.toAdditive (pullbackHom j)).comp
      (SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid
        X).toAddMonoidHom |>.comp (WeilDivisor.OrderSystem.ofScheme X).divisorClass
  let ψ : SchemeWeilDivisor X →+ Additive (LineBundleClass U) :=
    (SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid
      U).toAddMonoidHom.comp (WeilDivisor.OrderSystem.ofScheme U).divisorClass |>.comp
      (WeilDivisor.pullback (CodimensionOnePoint.mapOfIsOpenImmersion_injective j))
  refine WeilDivisor.induction_add_ofPoint (P := fun E ↦ φ E = ψ E)
    (by rw [map_zero, map_zero]) (fun E η ↦ ?_) D
  suffices hη : φ (WeilDivisor.ofPoint η) = ψ (WeilDivisor.ofPoint η) by
    rw [map_add, map_add, hη, add_right_cancel_iff]
  by_cases hmem : (η : X) ∈ Set.range j
  · obtain ⟨u, rfl⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion j).mpr hmem
    simp only [φ, ψ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      WeilDivisor.pullback_ofPoint,
      classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass_ofPoint,
      MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul, pullback_inv]
    have hcoe : vanishingIdeal
        ⟨closure {(CodimensionOnePoint.mapOfIsOpenImmersion j u : X)}, isClosed_closure⟩ =
        vanishingIdeal ⟨closure {j u.val}, isClosed_closure⟩ := by
      simp only [CodimensionOnePoint.coe_mapOfIsOpenImmersion]
    have hju : (vanishingIdeal ⟨closure {j u.val}, isClosed_closure⟩).IsEffectiveCartier :=
      hcoe ▸ isEffectiveCartier_vanishingIdeal_closure_singleton
        (CodimensionOnePoint.mapOfIsOpenImmersion j u).property
    rw [mk_toInvertibleSheaf_congr _ hju hcoe,
      pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_of_isOpenImmersion j hju
        (isEffectiveCartier_vanishingIdeal_closure_singleton u.property)]
  · have hnot : η ∉ Set.range (CodimensionOnePoint.mapOfIsOpenImmersion j) :=
      fun h ↦ hmem ((CodimensionOnePoint.mem_range_mapOfIsOpenImmersion j).mp h)
    simp only [φ, ψ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      WeilDivisor.pullback_ofPoint_of_notMem_range _ hnot, map_zero,
      classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass_ofPoint,
      MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul, pullback_inv]
    rw [pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_eq_one_of_notMem_range j
        hmem (isEffectiveCartier_vanishingIdeal_closure_singleton η.property),
      inv_one, ofMul_one]

end Factorial

end LineBundleClass

end TauCeti.AlgebraicGeometry
