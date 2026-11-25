/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.ClassGroup
public import TauCeti.AlgebraicGeometry.CartierDivisor.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effectivity
public import TauCeti.AlgebraicGeometry.LineBundle.Affine.Picard
public import TauCeti.AlgebraicGeometry.StructureSheaf.Stalk.Basic

/-!
# Divisors on normal and locally factorial schemes

Algebraic Hartogs' principle, through
`SchemeWeilDivisor.rationalUnitClass_eq_of_forall_orderAt_eq`, implies that
`CartierDivisor X →+ SchemeWeilDivisor X` is injective (`CartierDivisor.toWeilDivisorHom_injective`)
on any Noetherian normal integral scheme.

When `X` is additionally locally factorial (e.g. regular), every prime divisor `closure {η}` is an
effective Cartier ideal sheaf whose Cartier divisor `CartierDivisor.ofEffectiveCartier` has Weil
divisor `Finsupp.single η 1`, giving canonical equivalences
`CartierDivisor.toWeilDivisorAddEquiv : CartierDivisor X ≃+ SchemeWeilDivisor X` and
`CartierDivisor.weilClassGroupAddEquivLineBundleClass : Cl(X) ≃+ Additive (LineBundleClass X)`
via `CartierDivisor.weilToLineBundleClassHom` in arbitrary dimension. Open-immersion Picard
excision built on this equivalence is in `TauCeti.AlgebraicGeometry.CartierDivisor.Excision`.
Since the Picard group of a unique factorization domain is trivial, so is the divisor class group
of its spectrum (`SchemeWeilDivisor.subsingleton_classGroup_of_uniqueFactorizationMonoid`).

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.2, Proposition 6.3A,
  Proposition 6.11, and Corollary 6.16.
* [The Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.AlgebraicGeometry.Scheme

universe u

noncomputable section

namespace CartierDivisor

/-! ### Injectivity of `toWeilDivisorHom` on Noetherian normal schemes -/

section NormalNoetherian

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

/-- **Cartier divisors embed into Weil divisors on a Noetherian normal scheme.** Two Cartier
divisors with the same associated Weil divisor are equal: locally their equations have the same
orders at every codimension-one point, hence differ by a regular unit. -/
theorem toWeilDivisorHom_injective : Function.Injective (toWeilDivisorHom (X := X)) := by
  refine (injective_iff_map_eq_zero _).mpr fun D hD ↦ ?_
  choose U _ hxU f hf using fun x : X ↦ exists_local_equation X D x (Opens.mem_top x)
  refine (cartierDivisorSheaf X).eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) D 0 fun x ↦ ?_
  have : Nonempty (U x) := ⟨⟨x, hxU x⟩⟩
  let g := rationalUnitSectionsEquiv X (U x) (f x)
  have hDg : D |_ (U x) = rationalUnitClass X (U x) g := by
    rw [rationalUnitClass_apply]
    simpa only [g, AddEquiv.symm_apply_apply] using (hf x).symm
  have hD0 : D.toWeilDivisor = 0 := (toWeilDivisorHom_apply D).symm.trans hD
  have hord : ∀ y : CodimensionOnePoint X, (y : X) ∈ U x →
      SchemeWeilDivisor.orderAt y g = SchemeWeilDivisor.orderAt y 0 := fun y hy ↦ by
    rw [map_zero, ← orderAt_eq_of_restrict_eq_rationalUnitClass D y (U x) hy g hDg,
      ← coeff_toWeilDivisor, hD0, WeilDivisor.coeff_zero]
  have hres : D |_ U x = 0 := by
    rw [hDg, SchemeWeilDivisor.rationalUnitClass_eq_of_forall_orderAt_eq (fun _ _ ↦ inferInstance)
      hord, map_zero]
  simpa only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_zero] using hres

/-- On a Noetherian normal integral scheme, a Cartier divisor with zero Weil divisor is zero.
Hartshorne, *Algebraic Geometry*, Remark II.6.11.2. -/
@[simp]
theorem toWeilDivisor_eq_zero_iff {D : CartierDivisor X} : D.toWeilDivisor = 0 ↔ D = 0 := by
  rw [← toWeilDivisorHom_apply, map_eq_zero_iff _ toWeilDivisorHom_injective]

/-- On a Noetherian normal integral scheme, a Cartier divisor is principal if and only if its
associated Weil divisor is principal. -/
theorem mem_principalSubgroup_iff_toWeilDivisor_mem {D : CartierDivisor X} :
    D ∈ principalSubgroup X ↔
      D.toWeilDivisor ∈ (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup := by
  rw [mem_principalSubgroup, WeilDivisor.OrderSystem.mem_principalSubgroup]
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨Additive.ofMul f, by
      rw [← hf, ← toWeilDivisor_principalCartierDivisor, toMul_ofMul]⟩,
    fun ⟨g, hg⟩ ↦ ⟨g.toMul, toWeilDivisorHom_injective <| by
      rw [toWeilDivisorHom_apply, toWeilDivisorHom_apply, toWeilDivisor_principalCartierDivisor,
        hg]⟩⟩

end NormalNoetherian

/-! ### Weil–Cartier–Picard equivalence on Noetherian locally factorial schemes -/

section Factorial

open _root_.AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal
  isEffectiveCartier_vanishingIdeal_closure_singleton
  map_ideal_vanishingIdeal_closure_singleton_of_specializes
  map_ideal_vanishingIdeal_closure_singleton_of_not_specializes)

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- **The Weil divisor of a prime effective Cartier divisor.** On a Noetherian locally factorial
integral scheme, the Cartier divisor of `closure {η}` has associated Weil divisor `1 · [η]`. -/
@[simp]
theorem toWeilDivisor_ofEffectiveCartier_vanishingIdeal_closure_singleton
    (η : CodimensionOnePoint X) :
    (ofEffectiveCartier (isEffectiveCartier_vanishingIdeal_closure_singleton
        η.property)).toWeilDivisor =
      Finsupp.single η 1 := by
  set hη := isEffectiveCartier_vanishingIdeal_closure_singleton η.property
  refine WeilDivisor.ext fun y ↦ ?_
  obtain ⟨U, hyU, a, ha, hIa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff _).mp hη y
  have : Nonempty U.val := ⟨⟨y, hyU⟩⟩
  have hfnz := isSMulRegular_iff_germToFunctionField_ne_zero.mp ha
  let f : X.functionFieldˣ := Units.mk0 (X.germToFunctionField U.val a) hfnz
  rw [coeff_toWeilDivisor_eq_ord _ y hyU f (ofEffectiveCartier_restrict hη U ha hIa rfl).symm]
  have hgerm_ne : X.presheaf.germ U.val y hyU a ≠ 0 := fun h0 ↦
    hfnz (by rw [← X.algebraMap_germ_eq_germToFunctionField hyU, h0, map_zero])
  have hmap : ((vanishingIdeal ⟨closure {(η : X)}, isClosed_closure⟩).ideal U).map
      (X.presheaf.germ U.val y hyU).hom = Ideal.span {X.presheaf.germ U.val y hyU a} := by
    rw [hIa, Ideal.map_span, Set.image_singleton]
  rw [Units.val_mk0, ← X.algebraMap_germ_eq_germToFunctionField hyU a]
  by_cases hyeq : η = y
  · subst hyeq
    rw [WeilDivisor.coeff, Finsupp.single_eq_same]
    rw [map_ideal_vanishingIdeal_closure_singleton_of_specializes hyU specializes_rfl] at hmap
    exact ord_algebraMap_stalk_eq_one η.property specializes_rfl hmap
  · rw [WeilDivisor.coeff, Finsupp.single_eq_of_ne (Ne.symm hyeq)]
    have hnotsp : ¬ (η : X) ⤳ (y : X) := fun hsp ↦ hyeq (CodimensionOnePoint.eq_of_specializes hsp)
    rw [map_ideal_vanishingIdeal_closure_singleton_of_not_specializes hyU hnotsp] at hmap
    exact (ord_algebraMap_stalk_eq_zero_iff y.property specializes_rfl hgerm_ne).mpr fun hmem ↦
      (Ideal.comap_isPrime _ _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ hmem (Ideal.span_singleton_eq_top.mp hmap.symm))

/-- **Every Weil divisor on a Noetherian locally factorial integral scheme comes from a Cartier
divisor.** -/
theorem toWeilDivisorHom_surjective : Function.Surjective (toWeilDivisorHom (X := X)) := fun D ↦ by
  induction D using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add _ _ h₁ h₂ =>
    obtain ⟨C₁, hC₁⟩ := h₁; obtain ⟨C₂, hC₂⟩ := h₂
    exact ⟨C₁ + C₂, by rw [map_add, hC₁, hC₂]⟩
  | single η n =>
    exact ⟨n • ofEffectiveCartier (isEffectiveCartier_vanishingIdeal_closure_singleton η.property),
        by
      rw [map_zsmul, toWeilDivisorHom_apply,
        toWeilDivisor_ofEffectiveCartier_vanishingIdeal_closure_singleton, Finsupp.smul_single,
        smul_eq_mul, mul_one]⟩

/-- **The Weil–Cartier divisor equivalence (Hartshorne, Proposition II.6.11).** On a Noetherian
integral scheme with factorial local rings, Cartier and Weil divisors are canonically isomorphic,
in arbitrary dimension. -/
def toWeilDivisorAddEquiv (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    CartierDivisor X ≃+ SchemeWeilDivisor X :=
  have := IsNormalScheme.of_uniqueFactorizationMonoid_stalk (X := X)
  AddEquiv.ofBijective (toWeilDivisorHom (X := X))
    ⟨toWeilDivisorHom_injective, toWeilDivisorHom_surjective⟩

/-- Applying `toWeilDivisorAddEquiv` gives `D.toWeilDivisor`. -/
@[simp]
lemma toWeilDivisorAddEquiv_apply (D : CartierDivisor X) :
    toWeilDivisorAddEquiv X D = D.toWeilDivisor :=
  toWeilDivisorHom_apply D

/-- Applying `toWeilDivisorAddEquiv.symm` to `D.toWeilDivisor` recovers `D`. -/
@[simp]
lemma toWeilDivisorAddEquiv_symm_toWeilDivisor (D : CartierDivisor X) :
    (toWeilDivisorAddEquiv X).symm D.toWeilDivisor = D := by
  rw [← toWeilDivisorAddEquiv_apply, AddEquiv.symm_apply_apply]

/-- Applying `toWeilDivisorAddEquiv.symm` to `n · [η]` gives `n` times the Cartier divisor of
`closure {η}`. -/
@[simp]
lemma toWeilDivisorAddEquiv_symm_single (η : CodimensionOnePoint X) (n : ℤ) :
    (toWeilDivisorAddEquiv X).symm (Finsupp.single η n) =
      n • ofEffectiveCartier (isEffectiveCartier_vanishingIdeal_closure_singleton η.property) :=
  (toWeilDivisorAddEquiv X).injective <| by
    rw [AddEquiv.apply_symm_apply, toWeilDivisorAddEquiv_apply, ← toWeilDivisorHom_apply,
      map_zsmul, toWeilDivisorHom_apply,
      toWeilDivisor_ofEffectiveCartier_vanishingIdeal_closure_singleton, Finsupp.smul_single,
      smul_eq_mul, mul_one]

/-- Applying `toWeilDivisorAddEquiv.symm` to `1 · [η]` gives the Cartier divisor of
`closure {η}`. -/
lemma toWeilDivisorAddEquiv_symm_single_one (η : CodimensionOnePoint X) :
    (toWeilDivisorAddEquiv X).symm (Finsupp.single η 1) =
      ofEffectiveCartier (isEffectiveCartier_vanishingIdeal_closure_singleton η.property) := by
  rw [toWeilDivisorAddEquiv_symm_single, one_zsmul]

/-- Applying `toWeilDivisorAddEquiv.symm` to a principal Weil divisor gives the corresponding
principal Cartier divisor. -/
@[simp]
lemma toWeilDivisorAddEquiv_symm_principalDivisor (g : Additive X.functionFieldˣ) :
    (toWeilDivisorAddEquiv X).symm ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) =
      principalCartierDivisor X g.toMul :=
  (toWeilDivisorAddEquiv X).injective <| by
    rw [AddEquiv.apply_symm_apply, toWeilDivisorAddEquiv_apply,
      toWeilDivisor_principalCartierDivisor]

/-- The homomorphism `SchemeWeilDivisor X →+ Additive (LineBundleClass X)` sending a Weil divisor
to the class of its associated Cartier line bundle on a Noetherian locally factorial integral
scheme. -/
def weilToLineBundleClassHom (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    SchemeWeilDivisor X →+ Additive (LineBundleClass X) :=
  (toLineBundleClassHom (X := X)).comp (toWeilDivisorAddEquiv X).symm.toAddMonoidHom

/-- Unfolding `weilToLineBundleClassHom` through `toWeilDivisorAddEquiv.symm`. -/
lemma weilToLineBundleClassHom_apply (D : SchemeWeilDivisor X) :
    weilToLineBundleClassHom X D =
      Additive.ofMul ((toWeilDivisorAddEquiv X).symm D).toLineBundleClass := by
  rw [weilToLineBundleClassHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    toLineBundleClassHom_apply]

/-- Evaluating `weilToLineBundleClassHom` on `D.toWeilDivisor` gives the line-bundle class of
`D`. -/
@[simp]
lemma weilToLineBundleClassHom_toWeilDivisor (D : CartierDivisor X) :
    weilToLineBundleClassHom X D.toWeilDivisor = Additive.ofMul D.toLineBundleClass := by
  rw [weilToLineBundleClassHom_apply, toWeilDivisorAddEquiv_symm_toWeilDivisor]

/-- Principal Weil divisors map to `0` under `weilToLineBundleClassHom`. -/
@[simp]
lemma weilToLineBundleClassHom_principalDivisor (g : Additive X.functionFieldˣ) :
    weilToLineBundleClassHom X ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) = 0 := by
  rw [weilToLineBundleClassHom_apply, toWeilDivisorAddEquiv_symm_principalDivisor,
    toLineBundleClass_principalCartierDivisor, ofMul_one]

/-- `weilToLineBundleClassHom` sends `n · [η]` to `n • [𝒪_X(closure {η})]`. -/
@[simp]
theorem weilToLineBundleClassHom_single (η : CodimensionOnePoint X) (n : ℤ) :
    weilToLineBundleClassHom X (Finsupp.single η n) =
      n • Additive.ofMul (LineBundleClass.mk
        (isEffectiveCartier_vanishingIdeal_closure_singleton η.property).toInvertibleSheaf)⁻¹ := by
  rw [weilToLineBundleClassHom_apply, toWeilDivisorAddEquiv_symm_single,
    ← toLineBundleClassHom_apply, map_zsmul, toLineBundleClassHom_apply,
    toLineBundleClass_ofEffectiveCartier]

/-- `weilToLineBundleClassHom` is surjective onto `Additive (LineBundleClass X)`. -/
theorem weilToLineBundleClassHom_surjective :
    Function.Surjective (weilToLineBundleClassHom X) := fun a ↦ by
  obtain ⟨D, hD⟩ := toLineBundleClass_surjective a.toMul
  exact ⟨D.toWeilDivisor, by rw [weilToLineBundleClassHom_toWeilDivisor, hD, ofMul_toMul]⟩

/-- The kernel of `weilToLineBundleClassHom` is the subgroup of principal Weil divisors. -/
theorem ker_weilToLineBundleClassHom :
    (weilToLineBundleClassHom X).ker = (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup := by
  have := IsNormalScheme.of_uniqueFactorizationMonoid_stalk (X := X)
  ext D
  rw [AddMonoidHom.mem_ker, weilToLineBundleClassHom, AddMonoidHom.comp_apply,
    ← AddMonoidHom.mem_ker, ← principalSubgroup_eq_ker, mem_principalSubgroup_iff_toWeilDivisor_mem,
    AddEquiv.coe_toAddMonoidHom, ← toWeilDivisorAddEquiv_apply, AddEquiv.apply_symm_apply]

/-- **The Weil divisor class group is the Picard group (Hartshorne, Corollary II.6.16).** On any
Noetherian integral scheme with factorial local rings, `Cl(X) ≃+ Additive (LineBundleClass X)` in
arbitrary dimension. -/
def weilClassGroupAddEquivLineBundleClass (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup ≃+ Additive (LineBundleClass X) :=
  QuotientAddGroup.liftEquiv _ weilToLineBundleClassHom_surjective
    ker_weilToLineBundleClassHom.symm

/-- `weilClassGroupAddEquivLineBundleClass` evaluates on `divisorClass D` as
`weilToLineBundleClassHom X D`. -/
@[simp]
lemma weilClassGroupAddEquivLineBundleClass_divisorClass (D : SchemeWeilDivisor X) :
    weilClassGroupAddEquivLineBundleClass X
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D) =
      weilToLineBundleClassHom X D := by
  rw [WeilDivisor.OrderSystem.divisorClass_eq_mk']
  exact QuotientAddGroup.liftEquiv_mk _ weilToLineBundleClassHom_surjective
    ker_weilToLineBundleClassHom.symm D

/-- Evaluating `weilClassGroupAddEquivLineBundleClass.symm` on `weilToLineBundleClassHom X D`
returns the divisor class of `D`. -/
@[simp]
lemma weilClassGroupAddEquivLineBundleClass_symm_weilToLineBundleClassHom
    (D : SchemeWeilDivisor X) :
    (weilClassGroupAddEquivLineBundleClass X).symm (weilToLineBundleClassHom X D) =
      (WeilDivisor.OrderSystem.ofScheme X).divisorClass D := by
  rw [← weilClassGroupAddEquivLineBundleClass_divisorClass, AddEquiv.symm_apply_apply]

/-- Evaluating `weilClassGroupAddEquivLineBundleClass.symm` on the line-bundle class of `D` returns
the divisor class of `D.toWeilDivisor`. -/
@[simp]
lemma weilClassGroupAddEquivLineBundleClass_symm_toLineBundleClass (D : CartierDivisor X) :
    (weilClassGroupAddEquivLineBundleClass X).symm (Additive.ofMul D.toLineBundleClass) =
      (WeilDivisor.OrderSystem.ofScheme X).divisorClass D.toWeilDivisor := by
  rw [← weilToLineBundleClassHom_toWeilDivisor,
    weilClassGroupAddEquivLineBundleClass_symm_weilToLineBundleClassHom]

end Factorial

end CartierDivisor

end

end TauCeti.AlgebraicGeometry.Scheme

/-! ### Further results -/

public section

open _root_.AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

section LocallyFactorial

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

attribute [local instance] IsNormalScheme.of_uniqueFactorizationMonoid_stalk

/-- **The Weil divisor of a prime effective Cartier divisor.** On a Noetherian integral scheme with
factorial local rings, the Cartier divisor of the prime closed subscheme `closure {η}` has Weil
divisor `ofPoint η`. -/
@[simp]
theorem toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton [IsNoetherian X]
    (η : CodimensionOnePoint X) :
    (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
      η.property).toCartierDivisor.toWeilDivisor = WeilDivisor.ofPoint η := by
  apply WeilDivisor.ext
  intro ξ
  set hη := Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton η.property
  obtain ⟨U, hξU, a, ha, hUa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff _).mp hη (ξ : X)
  have : Nonempty U.val := ⟨⟨ξ, hξU⟩⟩
  have ha0 : a ≠ 0 := ha.isLeftRegular.ne_zero
  rw [hη.toCartierDivisor.coeff_toWeilDivisor_eq_ord ξ hξU _
      (hη.toCartierDivisor_restrict U ha0 hUa).symm,
    Units.val_mk0, ← X.algebraMap_germ_eq_germToFunctionField hξU a]
  set b := X.presheaf.germ U.val ξ hξU a
  have hspan : ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {(η : X)}, isClosed_closure⟩).ideal U).map (X.presheaf.germ U.val ξ hξU).hom =
      Ideal.span {b} := by
    rw [hUa, Ideal.map_span, Set.image_singleton]
  rcases eq_or_ne ξ η with rfl | hne
  · rw [WeilDivisor.coeff_ofPoint_self]
    rw [Scheme.IdealSheafData.map_ideal_vanishingIdeal_closure_singleton_of_specializes hξU
      specializes_rfl] at hspan
    exact Scheme.ord_algebraMap_stalk_eq_one ξ.property specializes_rfl hspan
  · rw [WeilDivisor.coeff_ofPoint_of_ne hne]
    have hnot : ¬ (η : X) ⤳ (ξ : X) := fun hsp ↦
      hne (CodimensionOnePoint.eq_of_specializes hsp).symm
    rw [Scheme.IdealSheafData.map_ideal_vanishingIdeal_closure_singleton_of_not_specializes hξU
      hnot] at hspan
    have hu : IsUnit b := Ideal.span_singleton_eq_top.mp hspan.symm
    exact (Scheme.ord_algebraMap_stalk_eq_zero_iff ξ.property specializes_rfl hu.ne_zero).mpr
      fun hm ↦ (IsLocalRing.mem_maximalIdeal _).mp (by simpa using hm) hu

namespace SchemeWeilDivisor

/-- Auxiliary homomorphism sending a finitely supported Weil divisor on a locally Noetherian
locally factorial integral scheme to its Cartier divisor. -/
private def toCartierDivisorOfUniqueFactorizationMonoid [IsLocallyNoetherian X] :
    SchemeWeilDivisor X →+ Scheme.CartierDivisor X :=
  (Finsupp.linearCombination ℤ fun η : CodimensionOnePoint X ↦
    (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
      η.property).toCartierDivisor).toAddMonoidHom

private lemma toCartierDivisorOfUniqueFactorizationMonoid_ofPoint [IsLocallyNoetherian X]
    (η : CodimensionOnePoint X) :
    toCartierDivisorOfUniqueFactorizationMonoid (WeilDivisor.ofPoint η) =
      (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
        η.property).toCartierDivisor := by
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
        η.property).toCartierDivisor :=
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
          η.property).toInvertibleSheaf)⁻¹ := by
  rw [classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass,
    equivCartierDivisorOfUniqueFactorizationMonoid_ofPoint,
    Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor]

/-- On a Noetherian integral scheme of dimension at most one whose codimension-one local rings are
discrete valuation rings, the one-dimensional Weil–Cartier equivalence `equivCartierDivisor` agrees
with `equivCartierDivisorOfUniqueFactorizationMonoid`. -/
theorem equivCartierDivisor_eq_equivCartierDivisorOfUniqueFactorizationMonoid
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hX : ∀ x : X, coheight x ≤ 1) :
    equivCartierDivisor hX = equivCartierDivisorOfUniqueFactorizationMonoid := by
  ext D
  apply Scheme.CartierDivisor.toWeilDivisor_injective
  rw [toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid,
    ← equivCartierDivisor_symm_apply hX, AddEquiv.symm_apply_apply]

end SchemeWeilDivisor

end LocallyFactorial

section UniqueFactorizationDomain

variable {R : CommRingCat.{u}} [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]

/-- **The divisor class group of a unique factorization domain is trivial.** On the spectrum of a
Noetherian unique factorization domain `R`, `Cl(Spec R) ≃ Pic(Spec R) ≃ Pic R` is trivial, as the
Picard group of a unique factorization domain is. Hartshorne, Proposition II.6.2. -/
instance SchemeWeilDivisor.subsingleton_classGroup_of_uniqueFactorizationMonoid :
    Subsingleton (WeilDivisor.OrderSystem.ofScheme (Spec R)).ClassGroup :=
  have : Subsingleton (LineBundleClass (Spec R)) := LineBundleClass.subsingleton_spec (R := R)
  (SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid
    (Spec R)).toEquiv.subsingleton

end UniqueFactorizationDomain

end

end TauCeti.AlgebraicGeometry
