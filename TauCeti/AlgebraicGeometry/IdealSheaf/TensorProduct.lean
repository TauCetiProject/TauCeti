/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Multiplication of ideal sheaves

For ideal sheaves `I` and `J` on a scheme `X`, products of local functions in `I` and `J` are
local functions in the product ideal sheaf `I * J`. This file packages that multiplication, first
on sections and then as a morphism `I ⊗ J ⟶ I * J` of `𝒪_X`-modules out of the tensor product.
It is the restriction of the multiplication `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X` of the structure sheaf along the
inclusions of `I`, `J` and `I * J` into `𝒪_X`. No hypothesis is placed on `I` or `J`; when `J` is
the ideal sheaf of an effective Cartier divisor the multiplication is an isomorphism
(`Scheme.IdealSheafData.tensorProductSheafIso`).

## Main declarations

* `Scheme.IdealSheafData.mul_mem_sections_mul`: products of sections of `I` and `J` are sections
  of `I * J`, and `Scheme.IdealSheafData.sectionsMul` is the resulting multiplication map
  `Γ(I, U) × Γ(J, U) → Γ(I * J, U)`;
* `Scheme.IdealSheafData.tensorPresheafHom`: the multiplication `I ⊗ J ⟶ I * J` on the
  sectionwise tensor product of presheaves of modules;
* `Scheme.IdealSheafData.sheafMul`: the multiplication morphism `I ⊗ J ⟶ I * J` of
  `𝒪_X`-modules, characterized by `sheafMul_sheafι` as the restriction of the multiplication of
  `𝒪_X`.

## References

* The construction of the multiplication map follows the Cartier divisor version
  `Scheme.CartierDivisor.tensorProductSheafIso` in
  `TauCeti/AlgebraicGeometry/CartierDivisor/TensorProduct.lean`.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}}

/-- Products of sections of two ideal sheaves are sections of their product. -/
theorem mul_mem_sections_mul {I J : X.IdealSheafData} {U : X.Opens} {s t : Γ(X, U)}
    (hs : s ∈ I.sections U) (ht : t ∈ J.sections U) : s * t ∈ (I * J).sections U := by
  refine (I * J).mem_sections_of_forall_exists fun x hx ↦ ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨W, homOfLE hWU, hxW, ?_⟩
  have hsW := I.map_mem_sections (homOfLE hWU) hs
  have htW := J.map_mem_sections (homOfLE hWU) ht
  rw [I.sections_eq_ideal ⟨W, hW⟩] at hsW
  rw [J.sections_eq_ideal ⟨W, hW⟩] at htW
  rw [map_mul, (I * J).sections_eq_ideal ⟨W, hW⟩, ideal_mul]
  exact Ideal.mul_mem_mul hsW htW

variable (I J : X.IdealSheafData) (U : X.Opens)

/-- Multiplication of local functions, as a map from sections of `I` and `J` to sections of
`I * J`. -/
def sectionsMul (s : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) : Γ((I * J).sheaf, U) :=
  (I * J).sectionMk _ (mul_mem_sections_mul (I.sheafι_app_mem U s) (J.sheafι_app_mem U t))

/-- `sectionsMul` multiplies the underlying local functions. -/
@[simp]
lemma sheafι_app_sectionsMul (s : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) :
    Scheme.Modules.Hom.app (I * J).sheafι U (sectionsMul I J U s t) =
      HMul.hMul (α := Γ(X, U)) (β := Γ(X, U)) (Scheme.Modules.Hom.app I.sheafι U s)
        (Scheme.Modules.Hom.app J.sheafι U t) :=
  sheafι_app_sectionMk _ _ _

/-- On sections built from local functions `a` and `b`, `sectionsMul` is the product `a * b`. -/
@[simp]
lemma sectionsMul_sectionMk {a b : Γ(X, U)} (ha : a ∈ I.sections U) (hb : b ∈ J.sections U) :
    sectionsMul I J U (I.sectionMk a ha) (J.sectionMk b hb) =
      (I * J).sectionMk (a * b) (mul_mem_sections_mul ha hb) :=
  (I * J).sheafι_app_injective U <| by
    simp only [sectionsMul, sheafι_app_sectionMk]
    -- The two products agree up to the identification of the sections of `𝒪_X` over `U`, as a
    -- module over itself, with the ring `Γ(X, U)`.
    rfl

variable {I J U}

/-- `sectionsMul` is additive in its first argument. -/
@[simp]
lemma sectionsMul_add_left (s s' : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) :
    sectionsMul I J U (s + s') t = sectionsMul I J U s t + sectionsMul I J U s' t :=
  (I * J).sheafι_app_injective U <| by
    simp only [sectionsMul, map_add, sheafι_app_sectionMk]
    exact add_mul (R := Γ(X, U)) _ _ _

/-- `sectionsMul` is additive in its second argument. -/
@[simp]
lemma sectionsMul_add_right (s : Γ(I.sheaf, U)) (t t' : Γ(J.sheaf, U)) :
    sectionsMul I J U s (t + t') = sectionsMul I J U s t + sectionsMul I J U s t' :=
  (I * J).sheafι_app_injective U <| by
    simp only [sectionsMul, map_add, sheafι_app_sectionMk]
    exact mul_add (R := Γ(X, U)) _ _ _

/-- `sectionsMul` is `Γ(X, U)`-linear in its first argument. -/
@[simp]
lemma sectionsMul_smul_left (r : Γ(X, U)) (s : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) :
    sectionsMul I J U (r • s) t = r • sectionsMul I J U s t :=
  (I * J).sheafι_app_injective U <| by
    refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul (I * J).sheafι r _).symm
    simp only [sectionsMul, sheafι_app_sectionMk]
    refine (congrArg (fun x : Γ(X, U) ↦ x * _)
      (Scheme.Modules.Hom.app_smul I.sheafι r s)).trans ?_
    exact mul_assoc (G := Γ(X, U)) _ _ _

/-- `sectionsMul` is `Γ(X, U)`-linear in its second argument. -/
@[simp]
lemma sectionsMul_smul_right (r : Γ(X, U)) (s : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) :
    sectionsMul I J U s (r • t) = r • sectionsMul I J U s t :=
  (I * J).sheafι_app_injective U <| by
    refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul (I * J).sheafι r _).symm
    simp only [sectionsMul, sheafι_app_sectionMk]
    refine (congrArg (fun x : Γ(X, U) ↦ _ * x)
      (Scheme.Modules.Hom.app_smul J.sheafι r t)).trans ?_
    exact mul_left_comm (G := Γ(X, U)) _ _ _

/-- Restriction commutes with multiplication of sections. -/
@[simp]
lemma sectionsMul_map {V : X.Opens} (i : V ⟶ U) (s : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) :
    sectionsMul I J V (I.sheaf.presheaf.map i.op s) (J.sheaf.presheaf.map i.op t) =
      (I * J).sheaf.presheaf.map i.op (sectionsMul I J U s t) :=
  (I * J).sheafι_app_injective V <| by
    simp only [sectionsMul, sheafι_app_sectionMk, sheafι_app_map]
    exact (map_mul (X.presheaf.map i.op).hom _ _).symm

variable (I J U)

/-- The multiplication morphism of presheaves of modules `I ⊗ J ⟶ I * J`. -/
def tensorPresheafHom :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) I.sheaf.val
      J.sheaf.val ⟶ (I * J).sheaf.val where
  app U := ModuleCat.MonoidalCategory.tensorLift (fun s t ↦ sectionsMul I J U.unop s t)
    sectionsMul_add_left sectionsMul_smul_left sectionsMul_add_right sectionsMul_smul_right
  naturality f := ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ sectionsMul_map f.unop s t

/-- On a pure tensor of sections over `U`, `tensorPresheafHom` is `sectionsMul`. -/
lemma tensorPresheafHom_app_tmul (s : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) :
    (tensorPresheafHom I J).app (op U) (s ⊗ₜ t) = sectionsMul I J U s t :=
  (rfl)

section SheafMul

open MonoidalCategory

/-- The sectionwise monoidal structure on presheaves of modules over the ring sheaf of `X`.
Instance search does not find it, nor the two instances below, as it cannot unify the topological
sheaf `X.sheaf` with a sheaf on a site; they are supplied here. -/
local instance : MonoidalCategory
    (_root_.PresheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf X.sheaf).obj) :=
  TauCeti.SheafOfModules.instMonoidalPresheafOfModulesRingCatSheaf X.sheaf

/-- The monoidal structure on sheaves of modules over the ring sheaf of `X`, as on `X.Modules`. -/
local instance : MonoidalCategory
    (SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf X.sheaf)) :=
  TauCeti.SheafOfModules.monoidalCategory X.sheaf

/-- The inclusion of sheaves of modules into presheaves of modules is lax monoidal. -/
local instance :
    (SheafOfModules.forget.{u} (TauCeti.SheafOfModules.ringCatSheaf X.sheaf)).LaxMonoidal :=
  TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf

/-- On presheaves, multiplication of local functions `I ⊗ J ⟶ I * J` followed by the inclusion
into `𝒪_X` is the inclusion `I ⊗ J ⟶ 𝒪_X ⊗ 𝒪_X` followed by the multiplication of `𝒪_X`. -/
private lemma tensorPresheafHom_comp_sheafι :
    tensorPresheafHom I J ≫ (I * J).sheafι.val =
      (I.sheafι.val ⊗ₘ J.sheafι.val) ≫
        (λ_ (𝟙_ (_root_.PresheafOfModules.{u}
          (TauCeti.SheafOfModules.ringCatSheaf X.sheaf).obj))).hom := by
  ext1 U
  refine ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_
  -- Both sides are the product of the two local functions: on the left by
  -- `sheafι_app_sectionMk`, on the right because the left unitor of `𝒪_X(U)` is its
  -- multiplication.
  exact (sheafι_app_sectionMk _ _ _).trans rfl

/-- Multiplication of local functions `I ⊗ J ⟶ I * J`, as a morphism of `𝒪_X`-modules out of the
tensor product. It is the restriction of the multiplication of `𝒪_X` (`sheafMul_sheafι`). -/
def sheafMul : I.sheaf ⊗ J.sheaf ⟶ (I * J).sheaf :=
  (SheafOfModules.tensorUnderlyingIso (R := X.sheaf) I.sheaf J.sheaf).hom ≫
    ((TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf).homEquiv _ _).symm
      (tensorPresheafHom I J)

/-- On underlying presheaves, `sheafMul` is the sectionwise multiplication `tensorPresheafHom`. -/
private lemma forget_μ_comp_sheafMul :
    Functor.LaxMonoidal.μ (SheafOfModules.forget (TauCeti.SheafOfModules.ringCatSheaf X.sheaf))
        I.sheaf J.sheaf ≫
      (SheafOfModules.forget (TauCeti.SheafOfModules.ringCatSheaf X.sheaf)).map (sheafMul I J) =
    tensorPresheafHom I J :=
  (TauCeti.SheafOfModules.forget_μ_comp_map (R := X.sheaf) (sheafMul I J)).trans
    ((congrArg _ (Iso.inv_hom_id_assoc _ _)).trans (Equiv.apply_symm_apply _ _))

/-- Multiplication `I ⊗ J ⟶ I * J`, followed by the inclusion `I * J ⟶ 𝒪_X`, is the inclusion
`I ⊗ J ⟶ 𝒪_X ⊗ 𝒪_X` followed by the multiplication `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`. As the inclusion is a
monomorphism, this characterizes `sheafMul`. -/
@[reassoc]
theorem sheafMul_sheafι :
    sheafMul I J ≫ (I * J).sheafι = (I.sheafι ⊗ₘ J.sheafι) ≫ (λ_ (𝟙_ X.Modules)).hom := by
  refine TauCeti.SheafOfModules.tensor_hom_ext (R := X.sheaf) ?_
  -- The composites are taken in `X.Modules` and in the category of sheaves of modules over
  -- `ringCatSheaf X.sheaf`, which agree only up to unfolding, so they are rewritten with `erw`.
  erw [Functor.map_comp, reassoc_of% forget_μ_comp_sheafMul I J, Functor.map_comp,
    ← Functor.LaxMonoidal.μ_natural_assoc]
  -- The inclusion of sheaves of modules has identity unit map, so its left unitality reads
  -- `μ ≫ forget.map λ = λ` on `𝒪_X`.
  have h := Functor.LaxMonoidal.left_unitality
    (F := SheafOfModules.forget (TauCeti.SheafOfModules.ringCatSheaf X.sheaf)) (𝟙_ _)
  have hε : Functor.LaxMonoidal.ε
      (SheafOfModules.forget (TauCeti.SheafOfModules.ringCatSheaf X.sheaf)) = 𝟙 _ :=
    TauCeti.SheafOfModules.forget_ε X.sheaf
  rw [hε] at h
  erw [id_whiskerRight, Category.id_comp] at h
  erw [← h]
  exact tensorPresheafHom_comp_sheafι I J

end SheafMul

end

end AlgebraicGeometry.Scheme.IdealSheafData
