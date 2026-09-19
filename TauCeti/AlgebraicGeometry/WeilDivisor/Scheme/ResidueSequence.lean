/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Modules.Skyscraper
public import TauCeti.AlgebraicGeometry.Scheme.Regular
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Germ

/-!
# The residue sequence `0 ⟶ 𝒪_X(D) ⟶ 𝒪_X(D + y) ⟶ κ(y)_y ⟶ 0`

Let `X` be a Noetherian integral scheme whose codimension-one local rings are discrete valuation
rings, `D` a Weil divisor on `X` and `y` a codimension-one point. Near `y` a section `f` of
`𝒪_X(D + y)` has order at least `-D(y) - 1` at `y`, so for a rational function `g` of order
`D(y) + 1` at `y` the product `g f` lies in the local ring `𝒪_{X,y}`, and `f` is a section of
`𝒪_X(D)` exactly when `g f` vanishes at `y`. Taking the residue of `g f` at `y` therefore defines
a morphism from `𝒪_X(D + y)` to the skyscraper sheaf `κ(y)_y` with kernel `𝒪_X(D)`. When `y` is a
closed point, as every codimension-one point of a curve is, this morphism is an epimorphism and
gives a short exact sequence

`0 ⟶ 𝒪_X(D) ⟶ 𝒪_X(D + y) ⟶ κ(y)_y ⟶ 0`.

The morphism depends on the choice of `g`, through multiplication by a unit of `κ(y)`; its kernel
and its image do not.

## Main declarations

* `SchemeWeilDivisor.toSkyscraperResidueField g hg`, the morphism `𝒪_X(D + y) ⟶ κ(y)_y`, described
  on sections by `SchemeWeilDivisor.skyscraperResidueFieldEquiv_toSkyscraperResidueField_app`;
* `SchemeWeilDivisor.toSkyscraperResidueField_app_eq_zero_iff`: its kernel on sections is
  `𝒪_X(D)`;
* `SchemeWeilDivisor.residueShortComplex g hg`, the sequence
  `𝒪_X(D) ⟶ 𝒪_X(D + y) ⟶ κ(y)_y`, exact in the middle (`residueShortComplex_exact`), and short
  exact when `y` is closed (`residueShortComplex_shortExact`), since `toSkyscraperResidueField` is
  then an epimorphism (`epi_toSkyscraperResidueField`).

Over a base field `k`, the long exact cohomology sequence of the residue sequence gives

* `SchemeWeilDivisor.finiteDimensional_cohomology_sheaf_add_ofPoint`: `Hⁱ(X, 𝒪_X(D + y))` is
  finite-dimensional when `Hⁱ(X, 𝒪_X(D))` is and `[κ(y) : k]` is finite, and
* `SchemeWeilDivisor.eulerCharBelow_sheaf_add_ofPoint`: `χ(𝒪_X(D + y)) = χ(𝒪_X(D)) + [κ(y) : k]`,
  the induction step of the Riemann–Roch formula `χ(𝒪_X(D)) = deg D + χ(𝒪_X)`.

## References

* R. Hartshorne, *Algebraic Geometry*, IV, proof of Theorem 1.3.
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §3.
-/

public section

open CategoryTheory Limits Order TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

noncomputable section

section LocallyNoetherian

variable [IsLocallyNoetherian X] {D : SchemeWeilDivisor X} {y : CodimensionOnePoint X}
  {g : X.functionFieldˣ}

/-- If `g` has order `D(y) + 1` at `y`, then `g` times a section of `𝒪_X(D + y)` over an open
subset containing `y` lies in the local ring at `y`. -/
private lemma exists_algebraMap_eq_mul
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) {U : X.Opens} [Nonempty U]
    (hy : (y : X) ∈ U) {s : Γ(Scheme.rationalFunctions X, U)}
    (hs : s ∈ sections (D + WeilDivisor.ofPoint y) U) :
    ∃ r : X.presheaf.stalk (y : X),
      algebraMap _ X.functionField r = g * Scheme.rationalFunctionsEquiv U s := by
  refine Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg y.property ?_
  rcases eq_or_ne (Scheme.rationalFunctionsEquiv U s) 0 with hf | hf
  · simp [hf]
  · have h := (mem_sections_iff.mp hs).resolve_left hf y hy
    rw [Scheme.ord_mul g.ne_zero hf, hg]
    simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self] at h
    omega

/-- A section `s` of `𝒪_X(D + y)` over an open subset containing `y` is a section of `𝒪_X(D)`
exactly when the regular function `g s` at `y` vanishes at `y`, where `g` has order `D(y) + 1`
at `y`. -/
private lemma mem_sections_iff_mem_maximalIdeal
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) {U : X.Opens} [Nonempty U]
    (hy : (y : X) ∈ U) {s : Γ(Scheme.rationalFunctions X, U)}
    (hs : s ∈ sections (D + WeilDivisor.ofPoint y) U) {r : X.presheaf.stalk (y : X)}
    (hr : algebraMap _ X.functionField r = g * Scheme.rationalFunctionsEquiv U s) :
    s ∈ sections D U ↔ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (y : X)) := by
  rw [mem_sections_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (Scheme.rationalFunctionsEquiv U s) 0 with hf | hf
  · have : r = 0 :=
      IsFractionRing.injective _ X.functionField (by rw [hr, hf, mul_zero, map_zero])
    simp [hf, this]
  have hr0 : algebraMap _ X.functionField r ≠ 0 := by
    rw [hr]
    exact mul_ne_zero g.ne_zero hf
  -- In a discrete valuation ring the units are the elements of order zero.
  have hunit : IsUnit r ↔ X.ord (algebraMap _ X.functionField r) y = 0 := by
    rw [Scheme.ord_eq_iff y.property hr0, ofAdd_zero]
    exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing
  rw [hunit, hr, Scheme.ord_mul g.ne_zero hf, hg]
  have hs' := (mem_sections_iff.mp hs).resolve_left hf
  have hy' := hs' y hy
  simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self] at hy'
  simp only [hf, false_or]
  refine ⟨fun h ↦ by have := h y hy; omega, fun h z hz ↦ ?_⟩
  by_cases hzy : z = y
  · subst hzy
    omega
  · simpa [WeilDivisor.coeff_ofPoint_of_ne hzy] using hs' z hz

/-- The residue at `y` of `g` times a section of `𝒪_X(D + y)` over an open subset containing
`y`. -/
private def localResidueFun (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1)
    (U : X.Opens) [Nonempty U] (hy : (y : X) ∈ U) (t : Γ(sheaf (D + WeilDivisor.ofPoint y), U)) :
    X.residueField y :=
  X.residue y (exists_algebraMap_eq_mul hg hy (sheafι_app_mem _ U t)).choose

private lemma localResidueFun_eq (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1)
    (U : X.Opens) [Nonempty U] (hy : (y : X) ∈ U) (t : Γ(sheaf (D + WeilDivisor.ofPoint y), U))
    {r : X.presheaf.stalk (y : X)}
    (hr : algebraMap _ X.functionField r =
      g * Scheme.rationalFunctionsEquiv U (Scheme.Modules.Hom.app (sheafι _) U t)) :
    localResidueFun hg U hy t = X.residue y r := by
  rw [localResidueFun]
  congr 1
  exact IsFractionRing.injective _ X.functionField
    ((exists_algebraMap_eq_mul hg hy (sheafι_app_mem _ U t)).choose_spec.trans hr.symm)

/-- `localResidueFun` as an additive map. -/
private def localResidue (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1)
    (U : X.Opens) [Nonempty U] (hy : (y : X) ∈ U) :
    Γ(sheaf (D + WeilDivisor.ofPoint y), U) →+ X.residueField y where
  toFun := localResidueFun hg U hy
  map_zero' := by
    rw [localResidueFun_eq hg U hy 0 (r := 0) (by simp), map_zero]
  map_add' s t := by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_mul hg hy (sheafι_app_mem _ U s)
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_mul hg hy (sheafι_app_mem _ U t)
    rw [localResidueFun_eq hg U hy s ha, localResidueFun_eq hg U hy t hb,
      localResidueFun_eq hg U hy (s + t) (r := a + b) (by simp [ha, hb, mul_add]), map_add]

open Classical in
/-- The morphism `𝒪_X(D + y) ⟶ κ(y)_y` on sections over `U`: the residue at `y` of `g` times a
section when `y ∈ U`, and zero otherwise. -/
private def residueApp (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1)
    (U : X.Opens) :
    Γ(sheaf (D + WeilDivisor.ofPoint y), U) →+ Γ(Scheme.skyscraperResidueField (y : X), U) :=
  if hy : (y : X) ∈ U then
    haveI : Nonempty U := ⟨⟨y, hy⟩⟩
    (Scheme.skyscraperResidueFieldEquiv (y : X) hy).symm.toAddMonoidHom.comp
      (localResidue hg U hy)
  else 0

private lemma skyscraperResidueFieldEquiv_residueApp
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) {U : X.Opens} [Nonempty U]
    (hy : (y : X) ∈ U) (t : Γ(sheaf (D + WeilDivisor.ofPoint y), U))
    {r : X.presheaf.stalk (y : X)}
    (hr : algebraMap _ X.functionField r =
      g * Scheme.rationalFunctionsEquiv U (Scheme.Modules.Hom.app (sheafι _) U t)) :
    Scheme.skyscraperResidueFieldEquiv (y : X) hy (residueApp hg U t) = X.residue y r := by
  simp only [residueApp, hy, ↓reduceDIte, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.apply_symm_apply]
  exact localResidueFun_eq hg U hy t hr

private lemma residueApp_naturality
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) {U V : X.Opens}
    (i : V ⟶ U) (t : Γ(sheaf (D + WeilDivisor.ofPoint y), U)) :
    residueApp hg V ((sheaf (D + WeilDivisor.ofPoint y)).presheaf.map i.op t) =
      (Scheme.skyscraperResidueField (y : X)).presheaf.map i.op (residueApp hg U t) := by
  by_cases hyV : (y : X) ∈ V
  · have hyU : (y : X) ∈ U := i.le hyV
    have : Nonempty V := ⟨⟨y, hyV⟩⟩
    have : Nonempty U := ⟨⟨y, hyU⟩⟩
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_mul hg hyU (sheafι_app_mem _ U t)
    refine (Scheme.skyscraperResidueFieldEquiv (y : X) hyV).injective ?_
    rw [Scheme.skyscraperResidueFieldEquiv_map, skyscraperResidueFieldEquiv_residueApp hg hyU t hr,
      skyscraperResidueFieldEquiv_residueApp hg hyV _ (r := r)]
    have hnat : Scheme.Modules.Hom.app (sheafι _) V
        ((sheaf (D + WeilDivisor.ofPoint y)).presheaf.map i.op t) =
          (Scheme.rationalFunctions X).presheaf.map i.op
            (Scheme.Modules.Hom.app (sheafι _) U t) :=
      (sheafι _).mapPresheaf.naturality_apply i.op t
    rw [hr, hnat, Scheme.rationalFunctionsEquiv_map]
  · have := Scheme.subsingleton_skyscraperResidueField (y : X) hyV
    exact Subsingleton.elim _ _

private lemma residueApp_smul
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) {U : X.Opens}
    (a : Γ(X, U)) (t : Γ(sheaf (D + WeilDivisor.ofPoint y), U)) :
    residueApp hg U (a • t) = a • residueApp hg U t := by
  by_cases hy : (y : X) ∈ U
  · have : Nonempty U := ⟨⟨y, hy⟩⟩
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_mul hg hy (sheafι_app_mem _ U t)
    refine (Scheme.skyscraperResidueFieldEquiv (y : X) hy).injective ?_
    rw [Scheme.skyscraperResidueFieldEquiv_smul, skyscraperResidueFieldEquiv_residueApp hg hy t hr,
      skyscraperResidueFieldEquiv_residueApp hg hy _ (r := X.presheaf.germ U y hy a * r),
      map_mul]
    · -- `X.evaluation U y hy` is by definition the germ at `y` followed by the residue map.
      exact congrArg (· * X.residue y r) (ConcreteCategory.congr_hom (X.germ_residue y hy) a)
    · rw [map_mul, X.algebraMap_germ_eq_germToFunctionField hy, hr, Scheme.Modules.Hom.app_smul,
        map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      ring
  · have := Scheme.subsingleton_skyscraperResidueField (y : X) hy
    exact Subsingleton.elim _ _

variable (g) in
/-- The morphism `𝒪_X(D + y) ⟶ κ(y)_y` sending a section `f` near `y` to the residue at `y` of
`g f`, for a rational function `g` of order `D(y) + 1` at `y`. Its kernel is `𝒪_X(D)`
(`toSkyscraperResidueField_app_eq_zero_iff`), and it is an epimorphism when `y` is closed
(`epi_toSkyscraperResidueField`). -/
def toSkyscraperResidueField (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    sheaf (D + WeilDivisor.ofPoint y) ⟶ Scheme.skyscraperResidueField (y : X) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (residueApp hg U.unop)
      naturality {U V} i := by
        ext t
        exact residueApp_naturality hg i.unop t }
    (fun U a t ↦ residueApp_smul hg a t)⟩

/-- **The morphism to the skyscraper sheaf on sections.** Over an open subset `U` containing `y`,
`toSkyscraperResidueField g hg` sends a section `t` of `𝒪_X(D + y)` to the residue at `y` of the
element `r` of the local ring at `y` which is `g t` as a rational function. -/
lemma skyscraperResidueFieldEquiv_toSkyscraperResidueField_app
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) {U : X.Opens} [Nonempty U]
    (hy : (y : X) ∈ U) (t : Γ(sheaf (D + WeilDivisor.ofPoint y), U))
    {r : X.presheaf.stalk (y : X)}
    (hr : algebraMap _ X.functionField r =
      g * Scheme.rationalFunctionsEquiv U (Scheme.Modules.Hom.app (sheafι _) U t)) :
    Scheme.skyscraperResidueFieldEquiv (y : X) hy
        (Scheme.Modules.Hom.app (toSkyscraperResidueField g hg) U t) =
      X.residue y r :=
  skyscraperResidueFieldEquiv_residueApp hg hy t hr

/-- **The kernel of `𝒪_X(D + y) ⟶ κ(y)_y` is `𝒪_X(D)`**, on sections: a section of
`𝒪_X(D + y)` is sent to zero exactly when it is a section of `𝒪_X(D)`. -/
lemma toSkyscraperResidueField_app_eq_zero_iff
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) (U : X.Opens)
    (t : Γ(sheaf (D + WeilDivisor.ofPoint y), U)) :
    Scheme.Modules.Hom.app (toSkyscraperResidueField g hg) U t = 0 ↔
      Scheme.Modules.Hom.app (sheafι _) U t ∈ sections D U := by
  by_cases hy : (y : X) ∈ U
  · have : Nonempty U := ⟨⟨y, hy⟩⟩
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_mul hg hy (sheafι_app_mem _ U t)
    rw [mem_sections_iff_mem_maximalIdeal hg hy (sheafι_app_mem _ U t) hr,
      ← IsLocalRing.residue_eq_zero_iff,
      ← (Scheme.skyscraperResidueFieldEquiv (y : X) hy).map_eq_zero_iff,
      skyscraperResidueFieldEquiv_toSkyscraperResidueField_app hg hy t hr]
    -- `X.residue y` is by definition the residue map of the local ring `𝒪_{X,y}`.
    rfl
  · have := Scheme.subsingleton_skyscraperResidueField (y : X) hy
    have hDU := sections_add_zsmul_ofPoint_eq D y 1 hy
    rw [one_zsmul] at hDU
    simp only [Subsingleton.elim _ (0 : Γ(Scheme.skyscraperResidueField (y : X), U)), true_iff]
    exact hDU ▸ sheafι_app_mem _ U t

@[reassoc (attr := simp)]
lemma sheafHomOfLE_toSkyscraperResidueField
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    sheafHomOfLE (WeilDivisor.le_add_ofPoint D y) ≫ toSkyscraperResidueField g hg = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext t
  refine (toSkyscraperResidueField_app_eq_zero_iff hg U
    (Scheme.Modules.Hom.app (sheafHomOfLE (WeilDivisor.le_add_ofPoint D y)) U t)).mpr ?_
  have h := ConcreteCategory.congr_hom (congrArg (fun η ↦ Scheme.Modules.Hom.app η U)
    (sheafHomOfLE_ι (WeilDivisor.le_add_ofPoint D y))) t
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  rw [h]
  exact sheafι_app_mem D U t

variable (g) in
/-- The sequence `𝒪_X(D) ⟶ 𝒪_X(D + y) ⟶ κ(y)_y` of `𝒪_X`-modules. It is exact in the middle
(`residueShortComplex_exact`), and short exact when `y` is a closed point
(`residueShortComplex_shortExact`). -/
def residueShortComplex (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    ShortComplex X.Modules :=
  ShortComplex.mk (sheafHomOfLE (WeilDivisor.le_add_ofPoint D y)) (toSkyscraperResidueField g hg)
    (sheafHomOfLE_toSkyscraperResidueField hg)

@[simp]
lemma residueShortComplex_X₁
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    (residueShortComplex g hg).X₁ = sheaf D := (rfl)

@[simp]
lemma residueShortComplex_X₂
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    (residueShortComplex g hg).X₂ = sheaf (D + WeilDivisor.ofPoint y) := (rfl)

@[simp]
lemma residueShortComplex_X₃
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    (residueShortComplex g hg).X₃ = Scheme.skyscraperResidueField (y : X) := (rfl)

@[simp]
lemma residueShortComplex_f
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    HEq (residueShortComplex g hg).f
      (sheafHomOfLE (WeilDivisor.le_add_ofPoint D y)) := (HEq.rfl)

@[simp]
lemma residueShortComplex_g
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    HEq (residueShortComplex g hg).g (toSkyscraperResidueField g hg) := (HEq.rfl)

/-- `𝒪_X(D)` is the kernel of `𝒪_X(D + y) ⟶ κ(y)_y`. -/
def isLimitKernelForkSheafHomOfLE
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    IsLimit (KernelFork.ofι (sheafHomOfLE (WeilDivisor.le_add_ofPoint D y))
      (sheafHomOfLE_toSkyscraperResidueField hg)) :=
  KernelFork.IsLimit.ofι _ _
    (fun φ hφ ↦ sheafLift D (φ ≫ sheafι _) fun U s ↦ by
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
      refine (toSkyscraperResidueField_app_eq_zero_iff hg U _).mp ?_
      simpa using ConcreteCategory.congr_hom
        (congrArg (fun η ↦ Scheme.Modules.Hom.app η U) hφ) s)
    (fun φ hφ ↦ by
      rw [← cancel_mono (sheafι _), Category.assoc, sheafHomOfLE_ι, sheafLift_ι])
    (fun φ hφ m hm ↦ by
      rw [← cancel_mono (sheafι D), sheafLift_ι, ← hm, Category.assoc, sheafHomOfLE_ι])

/-- The sequence `𝒪_X(D) ⟶ 𝒪_X(D + y) ⟶ κ(y)_y` is exact in the middle. -/
lemma residueShortComplex_exact
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    (residueShortComplex g hg).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelForkSheafHomOfLE hg)

end LocallyNoetherian

section Noetherian

variable [IsNoetherian X] {D : SchemeWeilDivisor X} {y : CodimensionOnePoint X}
  {g : X.functionFieldˣ}

/-- **Sections of `κ(y)_y` lift near `y`.** An element of `κ(y)` is, near `y`, the image of a
section of `𝒪_X(D + y)`: lift it to the local ring at `y` and divide by `g`. -/
private lemma exists_toSkyscraperResidueField_app_eq_of_mem
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) {U : X.Opens}
    (t : Γ(Scheme.skyscraperResidueField (y : X), U)) (hy : (y : X) ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U), (y : X) ∈ V ∧ ∃ s : Γ(sheaf (D + WeilDivisor.ofPoint y), V),
      Scheme.Modules.Hom.app (toSkyscraperResidueField g hg) V s =
        (Scheme.skyscraperResidueField (y : X)).presheaf.map i.op t := by
  have : Nonempty U := ⟨⟨y, hy⟩⟩
  obtain ⟨a, ha⟩ := X.residue_surjective y (Scheme.skyscraperResidueFieldEquiv (y : X) hy t)
  -- The rational function `g⁻¹ a` has order at least `-D(y) - 1` at `y`.
  set f : X.functionField := (g⁻¹ : X.functionFieldˣ) * algebraMap _ X.functionField a with hf
  have hord : f = 0 ∨ -WeilDivisor.coeff (D + WeilDivisor.ofPoint y) y ≤ X.ord f y := by
    rcases eq_or_ne (algebraMap _ X.functionField a) 0 with ha0 | ha0
    · exact Or.inl (by rw [hf, ha0, mul_zero])
    refine Or.inr ?_
    obtain ⟨W, hyW, b, rfl⟩ := X.presheaf.exists_germ_eq a
    have : Nonempty W := ⟨⟨y, hyW⟩⟩
    have hb := Scheme.ord_germToFunctionField_nonneg b hyW
    rw [X.algebraMap_germ_eq_germToFunctionField hyW] at ha0
    rw [hf, X.algebraMap_germ_eq_germToFunctionField hyW, Scheme.ord_mul (Units.ne_zero _) ha0,
      Units.val_inv_eq_inv_val, Scheme.ord_inv, hg, WeilDivisor.coeff_add,
      WeilDivisor.coeff_ofPoint_self]
    omega
  obtain ⟨V, i, hyV, hV⟩ := (exists_map_mem_sections_iff_codimensionOne (D + WeilDivisor.ofPoint y)
    y hy ((Scheme.rationalFunctionsEquiv U).symm f)).mpr (by rwa [LinearEquiv.apply_symm_apply])
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, i, hyV, sectionMk _ hV, (Scheme.skyscraperResidueFieldEquiv (y : X) hyV).injective ?_⟩
  rw [Scheme.skyscraperResidueFieldEquiv_map, ← ha]
  refine skyscraperResidueFieldEquiv_toSkyscraperResidueField_app hg hyV _ ?_
  rw [sheafι_app_sectionMk, Scheme.rationalFunctionsEquiv_map, LinearEquiv.apply_symm_apply, hf,
    ← mul_assoc, Units.mul_inv, one_mul]

/-- **`𝒪_X(D + y) ⟶ κ(y)_y` is an epimorphism** when `y` is a closed point. -/
theorem epi_toSkyscraperResidueField (hclosed : IsClosed ({(y : X)} : Set X))
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    Epi (toSkyscraperResidueField g hg) := by
  have hepi : Epi ((Scheme.Modules.toSheaf X).map (toSkyscraperResidueField g hg)) := by
    refine (TopCat.Sheaf.isLocallySurjective_iff_epi
      ((Scheme.Modules.toSheaf X).map (toSkyscraperResidueField g hg))).mp ?_
    refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun U t z hz ↦ ?_
    by_cases hzy : z = y
    · subst hzy
      obtain ⟨V, i, hyV, s, hs⟩ := exists_toSkyscraperResidueField_app_eq_of_mem hg t hz
      exact ⟨V, i.le, ⟨s, hs⟩, hyV⟩
    · -- Away from the closed point `y` the skyscraper sheaf has no nonzero sections.
      let V : X.Opens := U ⊓ ⟨({(y : X)} : Set X)ᶜ, hclosed.isOpen_compl⟩
      have hyV : (y : X) ∉ V := fun h ↦ (Opens.mem_inf.mp h).2 rfl
      have := Scheme.subsingleton_skyscraperResidueField (y : X) hyV
      exact ⟨V, inf_le_left, ⟨0, @Subsingleton.elim _ this _ _⟩, ⟨hz, hzy⟩⟩
  have : (Scheme.Modules.toSheaf X).Faithful :=
    inferInstanceAs (_root_.SheafOfModules.toSheaf X.ringCatSheaf).Faithful
  exact (Scheme.Modules.toSheaf X).epi_of_epi_map hepi

/-- **The residue sequence** `0 ⟶ 𝒪_X(D) ⟶ 𝒪_X(D + y) ⟶ κ(y)_y ⟶ 0` at a closed codimension-one
point `y`, on a Noetherian integral scheme whose codimension-one local rings are discrete
valuation rings. -/
theorem residueShortComplex_shortExact (hclosed : IsClosed ({(y : X)} : Set X))
    (hg : X.ord (g : X.functionField) y = WeilDivisor.coeff D y + 1) :
    (residueShortComplex g hg).ShortExact :=
  have : Epi (residueShortComplex g hg).g := by
    have h := residueShortComplex_g hg
    cases h
    exact epi_toSkyscraperResidueField hclosed hg
  have : Mono (residueShortComplex g hg).f := by
    have h := residueShortComplex_f hg
    cases h
    have : Mono (sheafHomOfLE (WeilDivisor.le_add_ofPoint D y) ≫ sheafι _) := by
      rw [sheafHomOfLE_ι]
      infer_instance
    exact mono_of_mono (sheafHomOfLE (WeilDivisor.le_add_ofPoint D y)) (sheafι _)
  ⟨residueShortComplex_exact hg⟩

section Cohomology

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] {D : SchemeWeilDivisor X}
  {y : CodimensionOnePoint X}

/-- **Adding a point preserves finite-dimensionality of cohomology.** If `y` is a closed
codimension-one point with finite residue field over `k`, and `Hⁱ(X, 𝒪_X(D))` is
finite-dimensional, then so is `Hⁱ(X, 𝒪_X(D + y))`. -/
theorem finiteDimensional_cohomology_sheaf_add_ofPoint (hclosed : IsClosed ({(y : X)} : Set X))
    (hy : (X ↘ Spec (.of k)).residueDegree y ≠ 0) (i : ℕ)
    [hD : FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) i)] :
    FiniteDimensional k
      (Scheme.Modules.Cohomology (sheaf (D + WeilDivisor.ofPoint y)) i) := by
  obtain ⟨g, hg⟩ := exists_orderAt_eq y (WeilDivisor.coeff D y + 1)
  rw [orderAt_apply] at hg
  let S := residueShortComplex (Additive.toMul g) hg
  have : FiniteDimensional k (Scheme.Modules.Cohomology S.X₁ i) := by
    dsimp only [S]
    rw [residueShortComplex_X₁]
    exact hD
  have : FiniteDimensional k (Scheme.Modules.Cohomology S.X₃ i) := by
    dsimp only [S]
    rw [residueShortComplex_X₃]
    exact Scheme.finiteDimensional_cohomology_skyscraperResidueField k hy i
  rw [← residueShortComplex_X₂ (g := Additive.toMul g) hg]
  exact Scheme.Modules.finiteDimensional_cohomology_X₂ k X
    (residueShortComplex_shortExact (g := Additive.toMul g) hclosed hg) i

/-- **The Euler characteristic of `𝒪_X(D + y)`.** If `y` is a closed codimension-one point with
residue degree `[κ(y) : k]` finite and nonzero, and `H⁰(X, 𝒪_X(D))` and `H¹(X, 𝒪_X(D))` are
finite-dimensional, then

`χ(𝒪_X(D + y)) = χ(𝒪_X(D)) + [κ(y) : k]`,

where `χ(M) = dim H⁰(X, M) - dim H¹(X, M)` is the Euler characteristic truncated at degree `2`
(the full Euler characteristic on a curve). No vanishing of `H²` is needed: the skyscraper sheaf
has no `H¹`, so the connecting map into `H²(X, 𝒪_X(D))` vanishes. -/
theorem eulerCharBelow_sheaf_add_ofPoint (hclosed : IsClosed ({(y : X)} : Set X))
    (hy : (X ↘ Spec (.of k)).residueDegree y ≠ 0)
    [hD₀ : FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) 0)]
    [hD₁ : FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) 1)] :
    Scheme.Modules.eulerCharBelow k X (sheaf (D + WeilDivisor.ofPoint y)) 2 =
      Scheme.Modules.eulerCharBelow k X (sheaf D) 2 + (X ↘ Spec (.of k)).residueDegree y := by
  obtain ⟨g, hg⟩ := exists_orderAt_eq y (WeilDivisor.coeff D y + 1)
  rw [orderAt_apply] at hg
  let S := residueShortComplex (Additive.toMul g) hg
  have hS : S.ShortExact := residueShortComplex_shortExact hclosed hg
  have hS₃ : Subsingleton (Scheme.Modules.Cohomology S.X₃ 1) := by
    dsimp only [S]
    rw [residueShortComplex_X₃]
    infer_instance
  have h : Scheme.Modules.eulerCharBelow k X S.X₂ 2 =
      Scheme.Modules.eulerCharBelow k X S.X₁ 2 + Scheme.Modules.eulerCharBelow k X S.X₃ 2 :=
    Scheme.Modules.eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1
      (fun i hi hi₀ ↦ by
        obtain rfl : i = 1 := by omega
        exact hD₁)
      (fun i _ ↦ finiteDimensional_cohomology_sheaf_add_ofPoint k hclosed hy i
        (hD := by interval_cases i <;> assumption))
      (LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply])
  refine h.trans ?_
  rw [Scheme.Modules.eulerCharBelow_two k S.X₃]
  have h₀ : Module.finrank k (Scheme.Modules.Cohomology S.X₃ 0) =
      (X ↘ Spec (.of k)).residueDegree y := by
    dsimp only [S]
    rw [residueShortComplex_X₃]
    exact Scheme.finrank_cohomology_zero_skyscraperResidueField k (y : X)
  rw [h₀, Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_zero]
  dsimp only [S]
  rw [residueShortComplex_X₁]

end Cohomology

end Noetherian

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
