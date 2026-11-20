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

/-!
# Divisors on normal and locally factorial schemes

On a locally Noetherian normal integral scheme, algebraic Hartogs' principle
(`exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme`) implies that
`CartierDivisor X →+ SchemeWeilDivisor X` is injective (`CartierDivisor.toWeilDivisorHom_injective`)
on any Noetherian normal integral scheme.

When `X` is additionally locally factorial (e.g. regular), every prime divisor `closure {η}` is an
effective Cartier ideal sheaf whose Cartier divisor `CartierDivisor.ofEffectiveCartier` has Weil
divisor `Finsupp.single η 1`, giving canonical equivalences
`CartierDivisor.toWeilDivisorAddEquiv : CartierDivisor X ≃+ SchemeWeilDivisor X` and
`CartierDivisor.weilClassGroupAddEquivLineBundleClass : Cl(X) ≃+ Additive (LineBundleClass X)`
via `CartierDivisor.weilToLineBundleClassHom` in arbitrary dimension. Open-immersion Picard
excision built on this equivalence is in `TauCeti.AlgebraicGeometry.CartierDivisor.Excision`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.3A, Proposition 6.11, and
  Corollary 6.16.
* [The Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.AlgebraicGeometry.Scheme

universe u

noncomputable section

section Normal

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

/-- On a locally Noetherian normal integral scheme, two nonzero rational functions with the same
orders at all codimension-one points of a nonempty open `U` represent the same Cartier divisor
section over `U`. -/
theorem rationalUnitClass_eq_of_forall_orderAt_eq_of_isNormalScheme {U : X.Opens} [Nonempty U]
    {g h : Additive X.functionFieldˣ}
    (hord : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      SchemeWeilDivisor.orderAt y g = SchemeWeilDivisor.orderAt y h) :
    rationalUnitClass X U g = rationalUnitClass X U h := by
  have hzero : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      X.ord ((Additive.toMul (g - h) : X.functionFieldˣ) : X.functionField) y = 0 := fun y hy ↦ by
    rw [← SchemeWeilDivisor.orderAt_apply y (g - h), map_sub, hord y hy, sub_self]
  obtain ⟨u, hu⟩ := exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme hzero
  have hunit : Units.map (X.germToFunctionField U).hom u = Additive.toMul (g - h) := Units.ext hu
  have hcl := rationalUnitClass_germToFunctionField_eq_zero X U u
  rw [hunit, ofMul_toMul, map_sub] at hcl
  exact sub_eq_zero.mp hcl

end Normal

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
    rw [hDg, rationalUnitClass_eq_of_forall_orderAt_eq_of_isNormalScheme hord, map_zero]
  simpa only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_zero] using hres

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
