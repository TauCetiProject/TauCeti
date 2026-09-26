/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Tensor products of Cartier divisor line bundles

Multiplication of rational functions sends sections of `𝒪_X(D)` and `𝒪_X(E)` to sections of
`𝒪_X(D + E)`. On an integral scheme this gives the tensor product isomorphism
`𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)`, and hence makes the Cartier divisor map to line-bundle classes
additive. A local equation of `E` trivializes the multiplication map: multiplication by the
equation and its inverse give its local inverse.

The resulting map `D ↦ [𝒪_X(D)]` is an additive homomorphism into the Picard group. Its
surjectivity, proved in `CartierDivisor/Picard.lean`, shows that every line-bundle class on an
integral scheme has an inverse.

## Main declarations

* `Scheme.CartierDivisor.tensorProductSheafIso`: `𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)`;
* `Scheme.CartierDivisor.toLineBundleClass_add` and `toLineBundleClassHom`: the additive
  comparison from Cartier divisors to line-bundle classes;
* `LineBundleClass.isUnit` and its `CommGroup` instance: the Picard group of an integral scheme.

This is the Cartier divisor version of Hartshorne, *Algebraic Geometry*, II.6.13. The
construction of the multiplication map follows the Weil divisor construction in
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/TensorProduct.lean`.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TensorProduct TopologicalSpace

namespace TauCeti
namespace AlgebraicGeometry
namespace Scheme.CartierDivisor

universe u

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

/-- Products of sections of two Cartier divisor sheaves are sections of their sum. -/
theorem rationalFunctionsMulBilin_mem_sections {D E : CartierDivisor X} {U : X.Opens}
    {s t : Γ(Scheme.rationalFunctions X, U)}
    (hs : s ∈ D.sections U) (ht : t ∈ E.sections U) :
    Scheme.rationalFunctionsMulBilin X U s t ∈ (D + E).sections U := by
  refine mem_sections_iff_exists.mpr fun x hx ↦ ?_
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt x
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  refine ⟨f * g, hf.mul hg, ?_⟩
  have hfs := (mem_sections.mp hs) x hx f hf
  have hgt := (mem_sections.mp ht) x hx g hg
  rw [Scheme.rationalFunctionsEquiv_mulBilin]
  convert Subring.mul_mem (algebraMap (X.presheaf.stalk x) X.functionField).range hfs hgt using 1
  simp only [Units.val_mul]
  ac_rfl

variable (D E : CartierDivisor X) (U : X.Opens)

/-- Multiplication inside the rational functions, as a section of `𝒪_X(D + E)`. -/
def sectionsMul (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) : Γ((D + E).sheaf, U) :=
  sectionMk _ (rationalFunctionsMulBilin_mem_sections (sheafι_app_mem D U s)
    (sheafι_app_mem E U t))

/-- The image of the product in the rational-function sheaf is the product of the images. -/
@[simp]
lemma sheafι_app_sectionsMul (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    Scheme.Modules.Hom.app (sheafι (D + E)) U (sectionsMul D E U s t) =
      Scheme.rationalFunctionsMulBilin X U
        (Scheme.Modules.Hom.app (sheafι D) U s)
        (Scheme.Modules.Hom.app (sheafι E) U t) :=
  sheafι_app_sectionMk _ _

variable {D E U}

@[simp]
lemma sectionsMul_add_left (s s' : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E U (s + s') t = sectionsMul D E U s t + sectionsMul D E U s' t :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_add_right (s : Γ(D.sheaf, U)) (t t' : Γ(E.sheaf, U)) :
    sectionsMul D E U s (t + t') = sectionsMul D E U s t + sectionsMul D E U s t' :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_smul_left (r : Γ(X, U)) (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E U (r • s) t = r • sectionsMul D E U s t :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_smul_right (r : Γ(X, U)) (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E U s (r • t) = r • sectionsMul D E U s t :=
  sheafι_app_injective _ U (by simp)

/-- Restriction commutes with multiplication of sections. -/
@[simp]
lemma sectionsMul_map {V : X.Opens} (i : V ⟶ U) (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E V (D.sheaf.presheaf.map i.op s) (E.sheaf.presheaf.map i.op t) =
      (D + E).sheaf.presheaf.map i.op (sectionsMul D E U s t) := by
  refine sheafι_app_injective _ V ?_
  have h {F : CartierDivisor X} (s : Γ(F.sheaf, U)) :=
    NatTrans.naturality_apply (sheafι F).mapPresheaf i.op s
  simp only [Scheme.Modules.mapPresheaf_app] at h
  rw [h, sheafι_app_sectionsMul, sheafι_app_sectionsMul, h, h,
    Scheme.rationalFunctionsMulBilin_map]

variable (D E U)

/-- Multiplication, linear on the tensor product of the sections. -/
def sectionsMulLift :
    TensorProduct Γ(X, U) Γ(D.sheaf, U) Γ(E.sheaf, U) →ₗ[Γ(X, U)] Γ((D + E).sheaf, U) :=
  TensorProduct.lift <| LinearMap.mk₂ Γ(X, U) (sectionsMul D E U)
    (fun s s' t ↦ sectionsMul_add_left s s' t)
    (fun r s t ↦ sectionsMul_smul_left r s t)
    (fun s t t' ↦ sectionsMul_add_right s t t')
    (fun r s t ↦ sectionsMul_smul_right r s t)

@[simp]
lemma sectionsMulLift_tmul (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMulLift D E U (s ⊗ₜ t) = sectionsMul D E U s t :=
  (rfl)

/-- The multiplication morphism of presheaves of modules. -/
def tensorPresheafHom :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) D.sheaf.val
      E.sheaf.val ⟶ (D + E).sheaf.val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ sectionsMul D E U.unop s t)
    (fun s s' t ↦ sectionsMul_add_left s s' t)
    (fun r s t ↦ sectionsMul_smul_left r s t)
    (fun s t t' ↦ sectionsMul_add_right s t t')
    (fun r s t ↦ sectionsMul_smul_right r s t)
  naturality f := ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ sectionsMul_map f.unop s t

/-- The morphism on an open subset is the multiplication map on tensor products of sections. -/
@[simp]
lemma tensorPresheafHom_app :
    ModuleCat.Hom.hom (R := X.sheaf.obj.obj (op U)) ((tensorPresheafHom D E).app (op U)) =
      sectionsMulLift D E U :=
  TensorProduct.ext' fun s t ↦ (sectionsMulLift_tmul D E U s t).symm

section LocalEquation

variable {E : CartierDivisor X} {V : X.Opens} [Nonempty V] {g : X.functionFieldˣ}
  (hg : Scheme.rationalUnitClass X V (Additive.ofMul g) = E |_ V)

include hg

/-- The inverse of an equation of `E` is a section of `𝒪_X(E)` on its domain. -/
lemma inv_localEquation_mem_sections :
    (Scheme.rationalFunctionsEquiv V).symm (g⁻¹ : X.functionField) ∈ E.sections V := by
  refine (mem_sections_iff_of_rationalUnitClass_eq le_rfl hg).mpr ⟨1, ?_⟩
  simp

/-- An equation of `E` is a section of `𝒪_X(-E)` on its domain. -/
lemma localEquation_mem_sections_neg :
    (Scheme.rationalFunctionsEquiv V).symm (g : X.functionField) ∈ (-E).sections V := by
  have hneg : Scheme.rationalUnitClass X V (Additive.ofMul g⁻¹) = (-E) |_ V := by
    rw [ofMul_inv, map_neg, hg]
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_neg]
  refine (mem_sections_iff_of_rationalUnitClass_eq le_rfl hneg).mpr ⟨1, ?_⟩
  simp

variable (D : CartierDivisor X)

/-- Multiplying a section of `𝒪_X(D+E)` by an equation of `E` produces a section of
`𝒪_X(D)`. -/
lemma mul_localEquation_mem_sections (s : Γ((D + E).sheaf, V)) :
    Scheme.rationalFunctionsMulBilin X V
      (Scheme.Modules.Hom.app (sheafι (D + E)) V s)
      ((Scheme.rationalFunctionsEquiv V).symm (g : X.functionField)) ∈ D.sections V := by
  simpa only [add_assoc, add_neg_cancel, add_zero] using
    rationalFunctionsMulBilin_mem_sections (sheafι_app_mem (D + E) V s)
      (localEquation_mem_sections_neg hg)

/-- Multiplication of divisor sheaf sections is locally surjective. -/
theorem exists_sectionsMul_eq (s : Γ((D + E).sheaf, V)) :
    ∃ (a : Γ(D.sheaf, V)) (b : Γ(E.sheaf, V)), sectionsMul D E V a b = s := by
  refine ⟨sectionMk _ (mul_localEquation_mem_sections hg D s),
    sectionMk _ (inv_localEquation_mem_sections hg), ?_⟩
  refine sheafι_app_injective _ V ((Scheme.rationalFunctionsEquiv V).injective ?_)
  simp

/-- Division by a local equation gives a linear retraction of section multiplication. -/
def sectionsMulRetraction :
    Γ((D + E).sheaf, V) →ₗ[Γ(X, V)]
      TensorProduct Γ(X, V) Γ(D.sheaf, V) Γ(E.sheaf, V) where
  toFun s := sectionMk _ (mul_localEquation_mem_sections hg D s) ⊗ₜ
    sectionMk _ (inv_localEquation_mem_sections hg)
  map_add' s s' := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact sheafι_app_injective D V (by simp)
  map_smul' r s := by
    rw [RingHom.id_apply, TensorProduct.smul_tmul']
    congr 1
    exact sheafι_app_injective D V (by simp)

/-- The retraction sends `s` to `(s·g) ⊗ g⁻¹`. -/
@[simp]
lemma sectionsMulRetraction_apply (s : Γ((D + E).sheaf, V)) :
    sectionsMulRetraction hg D s =
      sectionMk _ (mul_localEquation_mem_sections hg D s) ⊗ₜ
        sectionMk _ (inv_localEquation_mem_sections hg) :=
  (rfl)

/-- Division by the local equation retracts multiplication. -/
theorem sectionsMulRetraction_sectionsMul (a : Γ(D.sheaf, V)) (b : Γ(E.sheaf, V)) :
    sectionsMulRetraction hg D (sectionsMul D E V a b) = a ⊗ₜ b := by
  obtain ⟨r, hr⟩ : ∃ r : Γ(X, V), Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) V r =
      Scheme.rationalFunctionsMulBilin X V (Scheme.Modules.Hom.app (sheafι E) V b)
        ((Scheme.rationalFunctionsEquiv V).symm (g : X.functionField)) := by
    obtain ⟨r, hr⟩ := exists_regular_of_mem_sections_zero
      (show Scheme.rationalFunctionsMulBilin X V
        (Scheme.Modules.Hom.app (sheafι E) V b)
        ((Scheme.rationalFunctionsEquiv V).symm (g : X.functionField)) ∈
        (0 : CartierDivisor X).sections V from by
          simpa only [add_neg_cancel] using
            rationalFunctionsMulBilin_mem_sections (sheafι_app_mem E V b)
              (localEquation_mem_sections_neg hg))
    exact ⟨r, (Scheme.rationalFunctionsEquiv V).injective
      (by rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app]; exact hr)⟩
  have h1 : sectionMk _ (mul_localEquation_mem_sections hg D (sectionsMul D E V a b)) =
      r • a := by
    refine sheafι_app_injective D V ?_
    rw [sheafι_app_sectionMk, Scheme.Modules.Hom.app_smul,
      ← Scheme.rationalFunctionsMulBilin_toRationalFunctions_app, hr, sheafι_app_sectionsMul]
    refine (Scheme.rationalFunctionsEquiv V).injective ?_
    simp
    ring
  have h2 : r • sectionMk _ (inv_localEquation_mem_sections hg) = b := by
    refine sheafι_app_injective E V ?_
    rw [Scheme.Modules.Hom.app_smul,
      ← Scheme.rationalFunctionsMulBilin_toRationalFunctions_app, hr, sheafι_app_sectionMk]
    exact (Scheme.rationalFunctionsEquiv V).injective (by simp)
  rw [sectionsMulRetraction_apply, h1, TensorProduct.smul_tmul, h2]

/-- Multiplication is injective on a domain with a local equation of `E`. -/
theorem sectionsMulLift_injective : Function.Injective (sectionsMulLift D E V) := by
  have key : Function.LeftInverse (sectionsMulRetraction hg D) (sectionsMulLift D E V) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      rw [sectionsMulLift_tmul]
      exact sectionsMulRetraction_sectionsMul hg D a b
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  exact key.injective

end LocalEquation

section TensorProduct

variable (D E : CartierDivisor X)

/-- Multiplication is locally surjective on tensor products of sections. -/
theorem isLocallySurjective_tensorPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (tensorPresheafHom D E)) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_localEquation_le E U hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    obtain ⟨a, b, hab⟩ := exists_sectionsMul_eq hg D
      ((D + E).sheaf.presheaf.map (homOfLE hVU).op s)
    exact ⟨V, homOfLE hVU, ⟨a ⊗ₜ b, hab⟩, hxV⟩

/-- Multiplication is locally injective on tensor products of sections. -/
theorem isLocallyInjective_tensorPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (tensorPresheafHom D E)) where
  equalizerSieve_mem {U} z z' h x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_localEquation_le E U.unop hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    refine ⟨V, homOfLE hVU, sectionsMulLift_injective hg D ?_, hxV⟩
    exact (PresheafOfModules.naturality_apply (tensorPresheafHom D E) (homOfLE hVU).op z).trans
      ((congrArg ((D + E).sheaf.val.map (homOfLE hVU).op) h).trans
        (PresheafOfModules.naturality_apply (tensorPresheafHom D E) (homOfLE hVU).op z').symm)

/-- Sheafification of multiplication is an isomorphism since it is locally bijective. -/
theorem isIso_sheafification_map_tensorPresheafHom :
    IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (tensorPresheafHom D E)) := by
  have := isLocallySurjective_tensorPresheafHom D E
  have := isLocallyInjective_tensorPresheafHom D E
  -- Mathlib identifies local bijectivity with the inverse image of isomorphisms under
  -- sheafification; the two sides have different categorical wrappers.
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (tensorPresheafHom D E)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective _

/-- The tensor product of the line bundles of two Cartier divisors is the line bundle of their
sum. -/
def tensorProductSheafIso :
    TauCeti.SheafOfModules.tensorProduct X.sheaf D.sheaf E.sheaf ≅ (D + E).sheaf :=
  TauCeti.SheafOfModules.tensorProductIso X.sheaf D.sheaf E.sheaf ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_tensorPresheafHom D E) ≪≫
    TauCeti.SheafOfModules.sheafificationIso X.ringCatSheaf (D + E).sheaf

/-- The forward tensor product isomorphism is sheafified multiplication of sections. -/
theorem tensorProductSheafIso_hom :
    (tensorProductSheafIso D E).hom =
      (TauCeti.SheafOfModules.tensorProductIso X.sheaf D.sheaf E.sheaf).hom ≫
        (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
          (tensorPresheafHom D E) ≫
        (TauCeti.SheafOfModules.sheafificationIso X.ringCatSheaf (D + E).sheaf).hom :=
  (rfl)

/-- The class of the sheaf of `D + E` is the tensor product of the two divisor classes. -/
@[simp]
theorem toLineBundleClass_add :
    (D + E).toLineBundleClass = D.toLineBundleClass * E.toLineBundleClass := by
  have h (F : CartierDivisor X) :
      F.toLineBundleClass = LineBundleClass.mk F.toInvertibleSheaf := by
    apply toLineBundleClass_eq_mk_iff.mpr
    simpa only [toInvertibleSheaf_obj] using
      (show Nonempty (F.sheaf ≅ F.sheaf) from ⟨Iso.refl _⟩)
  rw [h (D + E), h D, h E, ← LineBundleClass.mk_tensorProduct,
    LineBundleClass.mk_eq_mk_iff]
  refine ⟨?_⟩
  simp only [toInvertibleSheaf_obj, InvertibleSheaf.tensorProduct_obj]
  exact (tensorProductSheafIso D E).symm

/-- The line-bundle class of `-D` inverts the class of `D`. -/
theorem isUnit_toLineBundleClass : IsUnit D.toLineBundleClass :=
  ⟨⟨D.toLineBundleClass, (-D).toLineBundleClass,
    by rw [← toLineBundleClass_add, add_neg_cancel, toLineBundleClass_zero],
    by rw [← toLineBundleClass_add, neg_add_cancel, toLineBundleClass_zero]⟩, rfl⟩

end TensorProduct

end
end CartierDivisor
end Scheme

namespace LineBundleClass

variable {X : Scheme.{u}} [IsIntegral X]

/-- Every line-bundle class on an integral scheme is invertible under tensor product. -/
theorem isUnit (a : LineBundleClass X) : IsUnit a := by
  obtain ⟨D, rfl⟩ := Scheme.CartierDivisor.toLineBundleClass_surjective a
  exact Scheme.CartierDivisor.isUnit_toLineBundleClass D

/-- Tensor product gives the Picard group of any integral scheme. -/
noncomputable instance : CommGroup (LineBundleClass X) :=
  commGroupOfIsUnit isUnit

end LineBundleClass

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- Negating a Cartier divisor gives the inverse line-bundle class. -/
@[simp]
theorem toLineBundleClass_neg (D : CartierDivisor X) :
    (-D).toLineBundleClass = D.toLineBundleClass⁻¹ := by
  apply mul_eq_one_iff_eq_inv'.mp
  rw [← toLineBundleClass_add, add_neg_cancel, toLineBundleClass_zero]

/-- The Cartier divisor map to the tensor-product Picard group, as an additive homomorphism. -/
noncomputable def toLineBundleClassHom : CartierDivisor X →+ Additive (LineBundleClass X) where
  toFun D := Additive.ofMul D.toLineBundleClass
  map_zero' := congrArg Additive.ofMul toLineBundleClass_zero
  map_add' D E := congrArg Additive.ofMul (toLineBundleClass_add D E)

/-- The bundled Cartier divisor comparison sends `D` to the class of `𝒪_X(D)`. -/
@[simp]
lemma toLineBundleClassHom_apply (D : CartierDivisor X) :
    toLineBundleClassHom D = Additive.ofMul D.toLineBundleClass := by
  rw [toLineBundleClassHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

end Scheme.CartierDivisor

end AlgebraicGeometry
end TauCeti
