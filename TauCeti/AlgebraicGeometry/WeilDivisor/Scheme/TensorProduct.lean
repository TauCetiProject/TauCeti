/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.LineBundle

/-!
# The sheaf of a sum of Weil divisors

Sections of `𝒪_X(D)` and of `𝒪_X(E)` multiply inside the sheaf `𝒦_X` of rational functions, and
their product satisfies the order bound imposed by `D + E`, because orders of vanishing add. This
file assembles those products into a morphism from the sectionwise tensor product of `𝒪_X(D)` and
`𝒪_X(E)` to `𝒪_X(D + E)`, and shows that on an integral Noetherian curve whose codimension-one
local rings are discrete valuation rings it becomes an isomorphism after sheafification:
`𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)`.

What makes multiplication locally bijective is a local equation: over an open subset on which `E`
is cut out by a single rational function `g`, multiplying by `g` and by `g⁻¹` inverts it.

## Main declarations

* `SchemeWeilDivisor.sectionsMul`, the product of a section of `𝒪_X(D)` and a section of
  `𝒪_X(E)`, with `SchemeWeilDivisor.sectionsMulLift` its linear form on the tensor product of
  sections and `SchemeWeilDivisor.tensorPresheafHom` the resulting morphism of presheaves of
  modules;
* `SchemeWeilDivisor.exists_sectionsMul_eq` and `SchemeWeilDivisor.injective_sectionsMulLift`,
  the surjectivity and injectivity of multiplication over an open subset on which `E` has a local
  equation, the latter through the explicit retraction
  `SchemeWeilDivisor.sectionsMulRetraction`;
* `SchemeWeilDivisor.tensorProductSheafIso`, the isomorphism `𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)`;
* `SchemeWeilDivisor.toLineBundleClass_add` and
  `SchemeWeilDivisor.classGroupToLineBundleClass_add`, saying that `D ↦ [𝒪_X(D)]` carries
  addition of divisors, and of divisor classes, to tensor product of line bundles;
* `SchemeWeilDivisor.isUnit_toLineBundleClass`: the class of `𝒪_X(D)` is invertible, with inverse
  the class of `𝒪_X(-D)`.

The construction follows Hartshorne, *Algebraic Geometry*, II.6.13, and the Stacks Project,
*Divisors*, Tag 0BE0.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TensorProduct TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

namespace SchemeWeilDivisor

universe u

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

noncomputable section

section LocallyNoetherian

variable [IsLocallyNoetherian X]

/-- **Orders of vanishing add.** The product inside `𝒦_X` of a section of `𝒪_X(D)` and a section
of `𝒪_X(E)` is a section of `𝒪_X(D + E)`. -/
lemma rationalFunctionsMulBilin_mem_sections {D E : SchemeWeilDivisor X} {U : X.Opens}
    {s t : Γ(Scheme.rationalFunctions X, U)} (hs : s ∈ sections D U) (ht : t ∈ sections E U) :
    Scheme.rationalFunctionsMulBilin X U s t ∈ sections (D + E) U := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := by
      ext x
      simpa using fun hx ↦ hU.elim ⟨x, hx⟩
    rw [sections_eq_top_of_eq_bot _ hbot]
    trivial
  rw [mem_sections_iff]
  by_cases hs0 : Scheme.rationalFunctionsEquiv U s = 0
  · exact Or.inl (by simp [hs0])
  by_cases ht0 : Scheme.rationalFunctionsEquiv U t = 0
  · exact Or.inl (by simp [ht0])
  refine Or.inr fun y hy ↦ ?_
  have hD := ((mem_sections_iff.mp hs).resolve_left hs0) y hy
  have hE := ((mem_sections_iff.mp ht).resolve_left ht0) y hy
  rw [Scheme.rationalFunctionsEquiv_mulBilin, Scheme.ord_mul hs0 ht0, WeilDivisor.coeff_add]
  omega

section Multiplication

variable (D E : SchemeWeilDivisor X) (U : X.Opens)

/-- The product inside `𝒦_X` of a section of `𝒪_X(D)` and a section of `𝒪_X(E)`, as a section of
`𝒪_X(D + E)`. -/
def sectionsMul (s : Γ(sheaf D, U)) (t : Γ(sheaf E, U)) : Γ(sheaf (D + E), U) :=
  sectionMk (Scheme.rationalFunctionsMulBilin X U
      (Scheme.Modules.Hom.app (sheafι D) U s) (Scheme.Modules.Hom.app (sheafι E) U t))
    (rationalFunctionsMulBilin_mem_sections (sheafι_app_mem D U s) (sheafι_app_mem E U t))

/-- The product of two sections, read inside `𝒦_X`, is the product of the two rational
functions. -/
@[simp]
lemma sheafι_app_sectionsMul (s : Γ(sheaf D, U)) (t : Γ(sheaf E, U)) :
    Scheme.Modules.Hom.app (sheafι (D + E)) U (sectionsMul D E U s t) =
      Scheme.rationalFunctionsMulBilin X U
        (Scheme.Modules.Hom.app (sheafι D) U s) (Scheme.Modules.Hom.app (sheafι E) U t) :=
  sheafι_app_sectionMk _ _

variable {D E U}

@[simp]
lemma sectionsMul_add_left (s s' : Γ(sheaf D, U)) (t : Γ(sheaf E, U)) :
    sectionsMul D E U (s + s') t = sectionsMul D E U s t + sectionsMul D E U s' t :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_add_right (s : Γ(sheaf D, U)) (t t' : Γ(sheaf E, U)) :
    sectionsMul D E U s (t + t') = sectionsMul D E U s t + sectionsMul D E U s t' :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_smul_left (r : Γ(X, U)) (s : Γ(sheaf D, U)) (t : Γ(sheaf E, U)) :
    sectionsMul D E U (r • s) t = r • sectionsMul D E U s t :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_smul_right (r : Γ(X, U)) (s : Γ(sheaf D, U)) (t : Γ(sheaf E, U)) :
    sectionsMul D E U s (r • t) = r • sectionsMul D E U s t :=
  sheafι_app_injective _ U (by simp)

/-- Multiplying two sections of divisor sheaves commutes with restriction. -/
@[simp]
lemma sectionsMul_map {V : X.Opens} (i : V ⟶ U) (s : Γ(sheaf D, U)) (t : Γ(sheaf E, U)) :
    sectionsMul D E V ((sheaf D).presheaf.map i.op s) ((sheaf E).presheaf.map i.op t) =
      (sheaf (D + E)).presheaf.map i.op (sectionsMul D E U s t) :=
  sheafι_app_injective _ V (by simp)

variable (D E U)

/-- Multiplication inside `𝒦_X`, as a linear map on the tensor product of the sections of
`𝒪_X(D)` and `𝒪_X(E)` over `U`. -/
def sectionsMulLift :
    TensorProduct Γ(X, U) Γ(sheaf D, U) Γ(sheaf E, U) →ₗ[Γ(X, U)] Γ(sheaf (D + E), U) :=
  TensorProduct.lift <| LinearMap.mk₂ Γ(X, U) (sectionsMul D E U)
    (fun s s' t ↦ sectionsMul_add_left s s' t)
    (fun r s t ↦ sectionsMul_smul_left r s t)
    (fun s t t' ↦ sectionsMul_add_right s t t')
    (fun r s t ↦ sectionsMul_smul_right r s t)

@[simp]
lemma sectionsMulLift_tmul (s : Γ(sheaf D, U)) (t : Γ(sheaf E, U)) :
    sectionsMulLift D E U (s ⊗ₜ t) = sectionsMul D E U s t :=
  (rfl)

/-- Multiplication inside `𝒦_X`, as a morphism from the sectionwise tensor product of the
presheaves of modules underlying `𝒪_X(D)` and `𝒪_X(E)` to the one underlying `𝒪_X(D + E)`. -/
def tensorPresheafHom :
    PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) (sheaf D).val (sheaf E).val ⟶
      (sheaf (D + E)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ sectionsMul D E U.unop s t)
    (fun s s' t ↦ sectionsMul_add_left s s' t)
    (fun r s t ↦ sectionsMul_smul_left r s t)
    (fun s t t' ↦ sectionsMul_add_right s t t')
    (fun r s t ↦ sectionsMul_smul_right r s t)
  naturality f :=
    -- Both sides evaluate on an elementary tensor to a product of restricted sections, so the
    -- naturality square is `sectionsMul_map`; no rewriting is needed to see it.
    ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ sectionsMul_map f.unop s t

/-- The multiplication morphism acts on the sections over `U` as `sectionsMulLift`. -/
@[simp]
lemma tensorPresheafHom_app :
    ModuleCat.Hom.hom (R := X.sheaf.obj.obj (op U)) ((tensorPresheafHom D E).app (op U)) =
      sectionsMulLift D E U :=
  (rfl)

end Multiplication

end LocallyNoetherian

section LocalEquation

variable [IsNoetherian X]
variable {E : SchemeWeilDivisor X} {V : X.Opens} [Nonempty V] {g : Additive X.functionFieldˣ}
  (hg : ∀ y : CodimensionOnePoint X, (y : X) ∈ V → WeilDivisor.coeff E y = orderAt y g)

include hg

/-- A local equation for `E` over `V` is a section of `𝒪_X(-E)` there. -/
lemma localEquation_mem_sections_neg :
    (Scheme.rationalFunctionsEquiv V).symm
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) ∈ sections (-E) V := by
  refine rationalFunctionsEquiv_symm_mem_sections fun y hy ↦ ?_
  rw [WeilDivisor.coeff_neg, neg_neg, ← orderAt_apply]
  exact le_of_eq (hg y hy)

variable (D : SchemeWeilDivisor X)

/-- Multiplying a section of `𝒪_X(D + E)` by a local equation for `E` gives a section of
`𝒪_X(D)`. -/
lemma mul_localEquation_mem_sections (s : Γ(sheaf (D + E), V)) :
    Scheme.rationalFunctionsMulBilin X V
      (Scheme.Modules.Hom.app (sheafι (D + E)) V s)
      ((Scheme.rationalFunctionsEquiv V).symm
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField)) ∈ sections D V := by
  have h : sections (D + E + -E) V = sections D V := by rw [show D + E + -E = D by abel]
  exact h ▸ rationalFunctionsMulBilin_mem_sections (sheafι_app_mem (D + E) V s)
    (localEquation_mem_sections_neg hg)

/-- **Local surjectivity of multiplication.** Where `E` has a local equation `g`, every section
of `𝒪_X(D + E)` over `V` is the product of a section of `𝒪_X(D)` and a section of `𝒪_X(E)`:
multiply by `g` and by `g⁻¹`. -/
theorem exists_sectionsMul_eq (s : Γ(sheaf (D + E), V)) :
    ∃ (a : Γ(sheaf D, V)) (b : Γ(sheaf E, V)), sectionsMul D E V a b = s := by
  refine ⟨sectionMk _ (mul_localEquation_mem_sections hg D s),
    sectionMk _ (inv_localEquation_mem_sections hg), ?_⟩
  refine sheafι_app_injective _ V ((Scheme.rationalFunctionsEquiv V).injective ?_)
  simp

/-- Division by a local equation `g` for `E`, as a map from the sections of `𝒪_X(D + E)` over `V`
to the sectionwise tensor product of the sections of `𝒪_X(D)` and of `𝒪_X(E)`: it sends `s` to
`(s · g) ⊗ g⁻¹`.

It retracts multiplication (`sectionsMulRetraction_sectionsMul`), which is why multiplication is
injective on sections over `V`. -/
def sectionsMulRetraction :
    Γ(sheaf (D + E), V) →ₗ[Γ(X, V)] TensorProduct Γ(X, V) Γ(sheaf D, V) Γ(sheaf E, V) where
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

/-- Dividing by a local equation sends `s` to `(s · g) ⊗ g⁻¹`. -/
@[simp]
lemma sectionsMulRetraction_apply (s : Γ(sheaf (D + E), V)) :
    sectionsMulRetraction hg D s = sectionMk _ (mul_localEquation_mem_sections hg D s) ⊗ₜ
      sectionMk _ (inv_localEquation_mem_sections hg) :=
  (rfl)

/-- Dividing by a local equation retracts multiplication of sections. -/
theorem sectionsMulRetraction_sectionsMul (hX : ∀ y : X, coheight y ≤ 1)
    (a : Γ(sheaf D, V)) (b : Γ(sheaf E, V)) :
    sectionsMulRetraction hg D (sectionsMul D E V a b) = a ⊗ₜ b := by
  obtain ⟨r, hr⟩ : ∃ r : Γ(X, V), Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) V r =
      Scheme.rationalFunctionsMulBilin X V (Scheme.Modules.Hom.app (sheafι E) V b)
        ((Scheme.rationalFunctionsEquiv V).symm
          ((Additive.toMul g : X.functionFieldˣ) : X.functionField)) := by
    refine (mem_sections_zero_iff (fun y _ ↦ hX y) _).mp ?_
    have h : sections (E + -E) V = sections (0 : SchemeWeilDivisor X) V := by
      rw [show E + -E = (0 : SchemeWeilDivisor X) by abel]
    exact h ▸ rationalFunctionsMulBilin_mem_sections (sheafι_app_mem E V b)
      (localEquation_mem_sections_neg hg)
  have h1 : sectionMk _ (mul_localEquation_mem_sections hg D (sectionsMul D E V a b)) = r • a := by
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

/-- **Local injectivity of multiplication.** Where `E` has a local equation, multiplication is
injective on the sectionwise tensor product over `V`, because dividing by that equation retracts
it. -/
theorem injective_sectionsMulLift (hX : ∀ y : X, coheight y ≤ 1) :
    Function.Injective (sectionsMulLift D E V) := by
  have key : Function.LeftInverse (sectionsMulRetraction hg D) (sectionsMulLift D E V) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      rw [sectionsMulLift_tmul]
      exact sectionsMulRetraction_sectionsMul hg D hX a b
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  exact key.injective

end LocalEquation

section Curve

variable [IsNoetherian X] (hX : ∀ y : X, coheight y ≤ 1) (D E : SchemeWeilDivisor X)

include hX

/-- On a curve, a Weil divisor has a local equation on an arbitrarily small neighbourhood of any
point. -/
lemma exists_localEquation_le (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧ ∃ g : Additive X.functionFieldˣ,
      ∀ y : CodimensionOnePoint X, (y : X) ∈ V → WeilDivisor.coeff E y = orderAt y g := by
  obtain ⟨W, hxW, g, hg⟩ :=
    isLocallyPrincipal_iff.mp (isLocallyPrincipal_of_forall_coheight_le_one hX E) x
  exact ⟨U ⊓ W, inf_le_left, ⟨hx, hxW⟩, g, fun y hy ↦ hg y hy.2⟩

theorem isLocallySurjective_tensorPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (tensorPresheafHom D E)) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_localEquation_le hX E U hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    obtain ⟨a, b, hab⟩ := exists_sectionsMul_eq hg D
      ((sheaf (D + E)).presheaf.map (homOfLE hVU).op s)
    -- Forgetting the module structures leaves the action on sections untouched, so the section
    -- to exhibit over `V` is the elementary tensor `a ⊗ₜ b`.
    refine ⟨V, homOfLE hVU, ⟨a ⊗ₜ b, ?_⟩, hxV⟩
    exact hab

theorem isLocallyInjective_tensorPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (tensorPresheafHom D E)) where
  equalizerSieve_mem {U} z z' h x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_localEquation_le hX E U.unop hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    -- Forgetting the module structures leaves the action on sections untouched, so the two
    -- restricted sections are compared by `sectionsMulLift` over `V`, where it is injective.
    refine ⟨V, homOfLE hVU, injective_sectionsMulLift hg D hX ?_, hxV⟩
    exact (PresheafOfModules.naturality_apply (tensorPresheafHom D E) (homOfLE hVU).op z).trans
      ((congrArg ((sheaf (D + E)).val.map (homOfLE hVU).op) h).trans
        (PresheafOfModules.naturality_apply (tensorPresheafHom D E) (homOfLE hVU).op z').symm)

/-- Multiplication becomes an isomorphism after sheafification: it is locally bijective. -/
theorem isIso_sheafification_map_tensorPresheafHom :
    IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (tensorPresheafHom D E)) := by
  have := isLocallySurjective_tensorPresheafHom hX D E
  have := isLocallyInjective_tensorPresheafHom hX D E
  -- `IsIso` after sheafification is the inverse image of the isomorphisms under sheafification,
  -- which Mathlib identifies with local bijectivity of the underlying morphism of presheaves.
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (tensorPresheafHom D E)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective _

/-- **The sheaf of a sum of Weil divisors is the tensor product of their sheaves.** On a curve
whose codimension-one local rings are discrete valuation rings, multiplication inside `𝒦_X`
identifies `𝒪_X(D) ⊗ 𝒪_X(E)` with `𝒪_X(D + E)`. -/
def tensorProductSheafIso :
    Scheme.Modules.tensorProduct X (sheaf D) (sheaf E) ≅ sheaf (D + E) :=
  -- The instance argument of `asIso` is supplied by hand: the tensor product is presented here
  -- through `SheafOfModules.tensorProduct`, so instance search does not see the sheafified
  -- multiplication morphism in the shape of `isIso_sheafification_map_tensorPresheafHom`.
  TauCeti.SheafOfModules.tensorProductIso X.sheaf (sheaf D) (sheaf E) ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_tensorPresheafHom hX D E) ≪≫
    TauCeti.SheafOfModules.sheafificationIso X.ringCatSheaf (sheaf (D + E))

/-- **The divisor-to-line-bundle map is multiplicative.** The class of `𝒪_X(D + E)` is the
product of the classes of `𝒪_X(D)` and `𝒪_X(E)`. -/
theorem toLineBundleClass_add :
    toLineBundleClass hX (D + E) = toLineBundleClass hX D * toLineBundleClass hX E := by
  rw [toLineBundleClass_eq_mk, toLineBundleClass_eq_mk, toLineBundleClass_eq_mk,
    ← LineBundleClass.mk_tensorProduct, LineBundleClass.mk_eq_mk_iff]
  refine ⟨?_⟩
  simpa only [toInvertibleSheaf_obj, InvertibleSheaf.tensorProduct_obj] using
    (tensorProductSheafIso hX D E).symm

/-- Every divisorial line-bundle class is invertible, `𝒪_X(-D)` inverting `𝒪_X(D)`. -/
theorem isUnit_toLineBundleClass : IsUnit (toLineBundleClass hX D) :=
  ⟨⟨toLineBundleClass hX D, toLineBundleClass hX (-D),
    by rw [← toLineBundleClass_add, add_neg_cancel, toLineBundleClass_zero],
    by rw [← toLineBundleClass_add, neg_add_cancel, toLineBundleClass_zero]⟩, rfl⟩

/-- The comparison from the divisor class group to line-bundle classes turns addition of divisor
classes into tensor product of line bundles. -/
theorem classGroupToLineBundleClass_add
    (c c' : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) :
    classGroupToLineBundleClass hX (c + c') =
      classGroupToLineBundleClass hX c * classGroupToLineBundleClass hX c' := by
  obtain ⟨D, rfl⟩ := (WeilDivisor.OrderSystem.ofScheme X).divisorClass_surjective c
  obtain ⟨E, rfl⟩ := (WeilDivisor.OrderSystem.ofScheme X).divisorClass_surjective c'
  rw [← map_add, classGroupToLineBundleClass_divisorClass,
    classGroupToLineBundleClass_divisorClass, classGroupToLineBundleClass_divisorClass,
    toLineBundleClass_add]

end Curve

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
