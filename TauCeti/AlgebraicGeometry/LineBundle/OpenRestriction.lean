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

Because `j` induces an isomorphism of function fields `K(X) ≅ K(U)`, every principal Weil divisor
on `U` extends to a principal Weil divisor on `X`. Consequently (Hartshorne, Proposition II.6.5(a)
and (c)):

1. Restriction `LineBundleClass.pullback j : LineBundleClass X → LineBundleClass U` is surjective.
2. A line-bundle class `a : LineBundleClass X` restricts to `1` on `U` if and only if `a` is an
   integer-power product of the prime-divisor line bundles `[𝒪_X(closure {η})]` supported at the
   finitely many codimension-one points `η` of `X` lying outside `Set.range j`.

Generic-fibre specializations over a discrete valuation ring and for `TauCeti.Model` are given in
`TauCeti.AlgebraicGeometry.SpecialFiber.Picard` and
`TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Picard`.

## Main declarations

In the namespace `TauCeti.AlgebraicGeometry.LineBundleClass` (alongside
`TauCeti.AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_isOpenImmersion`):

* `pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_of_isOpenImmersion` and
  `pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_eq_one_of_notMem_range`: pulling
  back the invertible ideal sheaf of `closure {x}` along an open immersion;
*
`toAdditive_pullbackHom_classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass`:
  compatibility of `Cl ≃+ Pic` with pullback along a nonempty open immersion;
* `pullback_surjective_of_isOpenImmersion` and `pullback_eq_one_iff_of_isOpenImmersion`:
  surjectivity and kernel characterization of `Pic(X) → Pic(U)` on locally factorial Noetherian
  integral schemes, with regular codimension-at-most-two specializations
  `pullback_surjective_of_isRegular` and `pullback_eq_one_iff_of_isRegular`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.5 and Corollary II.6.16.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Order _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- Transferring factorial local rings along an open immersion `j : U ⟶ X`. -/
theorem uniqueFactorizationMonoid_stalk_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] (u : U) :
    UniqueFactorizationMonoid (U.presheaf.stalk u) :=
  (asIso (j.stalkMap u)).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

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
    letI := uniqueFactorizationMonoid_stalk_of_isOpenImmersion j
    MonoidHom.toAdditive (pullbackHom j)
        (SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
          ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D)) =
      SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid U
        ((WeilDivisor.OrderSystem.ofScheme U).divisorClass
          (WeilDivisor.pullback (CodimensionOnePoint.mapOfIsOpenImmersion_injective j) D)) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsNoetherian U := isNoetherian_of_isOpenImmersion j
  have := uniqueFactorizationMonoid_stalk_of_isOpenImmersion j
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
  · obtain ⟨u, rfl⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion_iff j).mpr hmem
    simp only [φ, ψ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      WeilDivisor.pullback_ofPoint,
      classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass_ofPoint,
      MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul, pullback_inv]
    have hcoe : vanishingIdeal
        ⟨closure {(CodimensionOnePoint.mapOfIsOpenImmersion j u : X)}, isClosed_closure⟩ =
        vanishingIdeal ⟨closure {j u.1}, isClosed_closure⟩ := by
      simp only [CodimensionOnePoint.coe_mapOfIsOpenImmersion]
    have hju : (vanishingIdeal ⟨closure {j u.1}, isClosed_closure⟩).IsEffectiveCartier :=
      hcoe ▸ isEffectiveCartier_vanishingIdeal_closure_singleton
        (CodimensionOnePoint.mapOfIsOpenImmersion j u).2
    rw [mk_toInvertibleSheaf_congr _ hju hcoe,
      pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_of_isOpenImmersion j hju
        (isEffectiveCartier_vanishingIdeal_closure_singleton u.2)]
  · have hnot : η ∉ Set.range (CodimensionOnePoint.mapOfIsOpenImmersion j) :=
      fun h ↦ hmem ((CodimensionOnePoint.mem_range_mapOfIsOpenImmersion_iff j).mp h)
    simp only [φ, ψ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      WeilDivisor.pullback_ofPoint_of_notMem_range _ hnot, map_zero,
      classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass_ofPoint,
      MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul, pullback_inv]
    rw [pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_eq_one_of_notMem_range j
        hmem (isEffectiveCartier_vanishingIdeal_closure_singleton η.2),
      inv_one, ofMul_one]

/-- **Surjectivity of Picard restriction to a dense open.** On a Noetherian locally factorial
integral scheme `X`, pullback of line-bundle classes along a nonempty open immersion `j : U ⟶ X`
is surjective. Hartshorne, Proposition II.6.5(a). -/
theorem pullback_surjective_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U] :
    Function.Surjective (pullback j) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsNoetherian U := isNoetherian_of_isOpenImmersion j
  have := uniqueFactorizationMonoid_stalk_of_isOpenImmersion j
  intro b
  obtain ⟨D, hD⟩ : ∃ D : SchemeWeilDivisor U,
      classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid U
        ((WeilDivisor.OrderSystem.ofScheme U).divisorClass D) = Additive.ofMul b := by
    obtain ⟨c, hc⟩ :=
      (classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid
        U).surjective (Additive.ofMul b)
    obtain ⟨D, rfl⟩ := (WeilDivisor.OrderSystem.ofScheme U).divisorClass_surjective c
    exact ⟨D, hc⟩
  let E : SchemeWeilDivisor X :=
    WeilDivisor.pushforward (CodimensionOnePoint.mapOfIsOpenImmersion j) D
  refine ⟨(classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
      ((WeilDivisor.OrderSystem.ofScheme X).divisorClass E)).toMul, ?_⟩
  have h :=
    toAdditive_pullbackHom_classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass
      j E
  rw [WeilDivisor.pullback_pushforward, hD, MonoidHom.toAdditive_apply_apply,
    pullbackHom_apply] at h
  exact Additive.ofMul.injective h

/-- On a Noetherian locally factorial integral scheme `X`, a Weil divisor supported inside a finite
set `F` of codimension-one points represents the product of the prime-divisor line bundles over `F`
raised to its coefficients. -/
private lemma toMul_classGroupAddEquiv_of_support_subset {F : Finset (CodimensionOnePoint X)}
    {D : SchemeWeilDivisor X} (hD : (D.support : Set (CodimensionOnePoint X)) ⊆ F) :
    (classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D)).toMul =
      ∏ η : F, (mk (isEffectiveCartier_vanishingIdeal_closure_singleton
        η.1.2).toInvertibleSheaf)⁻¹ ^ (WeilDivisor.coeff D η.1) := by
  have hsum : D = ∑ η ∈ F, WeilDivisor.coeff D η • WeilDivisor.ofPoint η :=
    (WeilDivisor.eq_sum_coeff_smul_ofPoint D).trans <| Finset.sum_subset hD fun η _ hnot ↦ by
      rw [WeilDivisor.coeff, Finsupp.notMem_support_iff.mp hnot, zero_smul]
  conv_lhs => rw [hsum]
  rw [map_sum, map_sum, toMul_sum, ← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun η _ ↦ ?_
  rw [map_zsmul, map_zsmul,
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass_ofPoint,
    toMul_zsmul, toMul_ofMul]

/-- Every line-bundle class in the kernel of restriction along a nonempty open immersion `j : U ⟶ X`
is represented by a Weil divisor whose restriction to `U` vanishes. -/
private lemma exists_divisor_pullback_eq_zero_of_pullback_eq_one (j : U ⟶ X) [IsOpenImmersion j]
    [Nonempty U] {a : LineBundleClass X} (ha : pullback j a = 1) :
    ∃ D' : SchemeWeilDivisor X,
      classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D') = Additive.ofMul a ∧
      WeilDivisor.pullback (CodimensionOnePoint.mapOfIsOpenImmersion_injective j) D' = 0 := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsNoetherian U := isNoetherian_of_isOpenImmersion j
  have := uniqueFactorizationMonoid_stalk_of_isOpenImmersion j
  obtain ⟨c₀, hc₀⟩ :=
    (classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid
      X).surjective (Additive.ofMul a)
  obtain ⟨D, rfl⟩ := (WeilDivisor.OrderSystem.ofScheme X).divisorClass_surjective c₀
  have hpull :=
    toAdditive_pullbackHom_classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass
      j D
  have hDU : (WeilDivisor.OrderSystem.ofScheme U).divisorClass
      (WeilDivisor.pullback (CodimensionOnePoint.mapOfIsOpenImmersion_injective j) D) = 0 := by
    apply (classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid U).injective
    rw [map_zero, ← hpull, hc₀, MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul,
      ha, ofMul_one]
  rw [WeilDivisor.OrderSystem.divisorClass_eq_zero_iff,
    WeilDivisor.OrderSystem.mem_principalSubgroup] at hDU
  obtain ⟨g, hg⟩ := hDU
  let f : Additive X.functionFieldˣ :=
    Additive.ofMul (Units.map (inv j.functionFieldMap).hom.toMonoidHom g.toMul)
  have hmap : Units.map j.functionFieldMap.hom.toMonoidHom f.toMul = g.toMul :=
    Units.ext <|
      RingHom.congr_fun (congrArg CommRingCat.Hom.hom (IsIso.inv_hom_id j.functionFieldMap)) _
  refine ⟨D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor f, ?_, ?_⟩
  · rw [map_sub, WeilDivisor.OrderSystem.divisorClass_principalDivisor, sub_zero, hc₀]
  · rw [map_sub, SchemeWeilDivisor.pullback_principalDivisor_of_isOpenImmersion j f, hmap,
      ofMul_toMul, hg, sub_self]

/-- **Kernel of Picard restriction to a dense open.** On a Noetherian locally factorial integral
scheme `X`, for any nonempty open immersion `j : U ⟶ X` and finite set `F` of codimension-one
points equal to `{η | (η : X) ∉ Set.range j}`, a line-bundle class `a` on `X` pulls back to `1` on
`U` if and only if it is an integer-power product of `[𝒪_X(closure {η})]` for `η ∈ F`.
Hartshorne, Proposition II.6.5(c). -/
theorem pullback_eq_one_iff_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    {F : Finset (CodimensionOnePoint X)}
    (hF : (F : Set (CodimensionOnePoint X)) =
      {η : CodimensionOnePoint X | (η : X) ∉ Set.range j})
    {a : LineBundleClass X} :
    pullback j a = 1 ↔
      ∃ c : F → ℤ, a = ∏ η : F,
        (mk (isEffectiveCartier_vanishingIdeal_closure_singleton
          η.1.2).toInvertibleSheaf)⁻¹ ^ c η := by
  refine ⟨fun ha ↦ ?_, ?_⟩
  · obtain ⟨D', hc₀, hD'pull⟩ := exists_divisor_pullback_eq_zero_of_pullback_eq_one j ha
    have hsupp : (D'.support : Set (CodimensionOnePoint X)) ⊆ F := by
      rw [hF]
      intro η hη hmem
      obtain ⟨u, rfl⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion_iff j).mpr hmem
      have h0 : WeilDivisor.coeff (WeilDivisor.pullback
          (CodimensionOnePoint.mapOfIsOpenImmersion_injective j) D') u = 0 := by
        rw [hD'pull, WeilDivisor.coeff_zero]
      rw [WeilDivisor.coeff_pullback] at h0
      exact Finsupp.mem_support_iff.mp hη h0
    refine ⟨fun η ↦ WeilDivisor.coeff D' η.1, ?_⟩
    rw [← toMul_classGroupAddEquiv_of_support_subset hsupp, hc₀, toMul_ofMul]
  · rintro ⟨c, rfl⟩
    rw [← pullbackHom_apply, map_prod]
    refine Finset.prod_eq_one fun η _ ↦ ?_
    have hnot : (η.1 : X) ∉ Set.range j := by
      have hmem : η.1 ∈ (F : Set (CodimensionOnePoint X)) := η.2
      rwa [hF] at hmem
    rw [pullbackHom_apply, pullback_zpow, pullback_inv,
      pullback_mk_toInvertibleSheaf_vanishingIdeal_closure_singleton_eq_one_of_notMem_range j hnot
        (isEffectiveCartier_vanishingIdeal_closure_singleton η.1.2),
      inv_one, one_zpow]

end Factorial

section Regular

variable {U X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsRegular X]

/-- **Surjectivity of Picard restriction on regular schemes of codimension at most two.** On a
regular Noetherian integral scheme `X` all of whose points have codimension at most two, pullback of
line-bundle classes along any nonempty open immersion `j : U ⟶ X` is surjective. Hartshorne,
Proposition II.6.5(a) and Corollary II.6.16. -/
theorem pullback_surjective_of_isRegular (hX : ∀ x : X, coheight x ≤ 2) (j : U ⟶ X)
    [IsOpenImmersion j] [Nonempty U] :
    Function.Surjective (pullback j) :=
  let := fun x ↦ IsRegular.uniqueFactorizationMonoid_stalk x (hX x)
  pullback_surjective_of_isOpenImmersion j

/-- **Kernel of Picard restriction on regular schemes of codimension at most two.** On a regular
Noetherian integral scheme `X` all of whose points have codimension at most two, for any nonempty
open immersion `j : U ⟶ X` and finite set `F` of codimension-one points equal to
`{η | (η : X) ∉ Set.range j}`, a line-bundle class `a` on `X` pulls back to `1` on `U` if and only
if it is an integer-power product of `[𝒪_X(closure {η})]` for `η ∈ F`. Hartshorne, Proposition
II.6.5(c) and Corollary II.6.16. -/
theorem pullback_eq_one_iff_of_isRegular (hX : ∀ x : X, coheight x ≤ 2) (j : U ⟶ X)
    [IsOpenImmersion j] [Nonempty U] {F : Finset (CodimensionOnePoint X)}
    (hF : (F : Set (CodimensionOnePoint X)) =
      {η : CodimensionOnePoint X | (η : X) ∉ Set.range j})
    {a : LineBundleClass X} :
    pullback j a = 1 ↔
      ∃ c : F → ℤ, a = ∏ η : F,
        (mk (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
          η.1.2).toInvertibleSheaf)⁻¹ ^ c η :=
  let := fun x ↦ IsRegular.uniqueFactorizationMonoid_stalk x (hX x)
  pullback_eq_one_iff_of_isOpenImmersion j hF

end Regular

end LineBundleClass

end TauCeti.AlgebraicGeometry
