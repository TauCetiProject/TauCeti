/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import TauCeti.CategoryTheory.Exact.KernelCokernelPair
public import TauCeti.CategoryTheory.Sites.Whiskering

/-!
# Short exact sequences of abelian sheaves without sheafification

Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a complex of sheaves of abelian groups on a site `(C, J)` in
which `F₁ ⟶ F₂` is a kernel of `F₂ ⟶ F₃` and `F₂ ⟶ F₃` is locally surjective. This file shows
that it is a short exact sequence of sheaves.

When `J`-sheafification of abelian presheaves exists, the category of sheaves is abelian and this
is standard. The point here is that no sheafification is needed: `F₂ ⟶ F₃` is a cokernel of
`F₁ ⟶ F₂` in sheaves because a morphism `F₂ ⟶ G` to a sheaf killing `F₁` descends to `F₃` by
gluing its values on local preimages, which are well defined because the kernel of `F₂ ⟶ F₃` is
computed objectwise. This applies to large sites such as the big étale site of a scheme, where
sheafification into abelian groups of the same universe is not available and the category of
sheaves is not known to be abelian.

## Main declarations

* `CategoryTheory.ShortComplex.gIsCokernelOfIsLocallySurjective`: a locally surjective morphism
  `F₂ ⟶ F₃` of abelian sheaves whose kernel is, on sections, the image of `F₁ ⟶ F₂` is a
  cokernel of `F₁ ⟶ F₂`.
* `CategoryTheory.ShortComplex.shortExact_of_isLocallySurjective`: a complex of abelian sheaves
  whose first map is a kernel of the second and whose second map is locally surjective is short
  exact.
-/

public section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- If `S.f` is a kernel of `S.g` in sheaves, then on the sections over every object, every
section killed by `S.g` comes from `S.X₁`: kernels of sheaves are computed objectwise. -/
theorem exists_app_eq_of_isLimit (hS : IsLimit (KernelFork.ofι S.f S.zero)) (U : Cᵒᵖ)
    (x : S.X₂.obj.obj U) (hx : S.g.hom.app U x = 0) : ∃ y, S.f.hom.app U y = x := by
  let F := sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  have hSU : IsLimit (KernelFork.ofι (F.map S.f) (S.map F).zero) := KernelFork.mapIsLimit _ hS F
  exact ((S.map F).ab_exact_iff.1 ((S.map F).exact_of_f_is_kernel hSU)) x hx

section Cokernel

variable (hS : ∀ (U : Cᵒᵖ) (x : S.X₂.obj.obj U), S.g.hom.app U x = 0 → ∃ y, S.f.hom.app U y = x)
  {G : Sheaf J AddCommGrpCat.{w}} (h : S.X₂ ⟶ G) (hh : S.f ≫ h = 0)

include hS hh in
/-- A morphism `h : S.X₂ ⟶ G` killing `S.X₁` takes the same value on two sections with the same
image under `S.g`. -/
private lemma app_eq_of_app_eq {U : Cᵒᵖ} {a b : S.X₂.obj.obj U}
    (hab : S.g.hom.app U a = S.g.hom.app U b) : h.hom.app U a = h.hom.app U b := by
  obtain ⟨y, hy⟩ := hS U (a - b) (by rw [map_sub, hab, sub_self])
  rw [← sub_eq_zero, ← map_sub, ← hy]
  simpa using congr(($hh).hom.app U y)

variable [Sheaf.IsLocallySurjective S.g]

include hS hh in
/-- A section `s` of `S.X₃` has an image in `G`: a section `d` of `G` whose restriction along
every `φ : V ⟶ U` is the value of `h` on any local preimage of `s|_V` under `S.g`. -/
private lemma exists_section (U : Cᵒᵖ) (s : S.X₃.obj.obj U) :
    ∃ d : G.obj.obj U, ∀ ⦃V : C⦄ (φ : V ⟶ U.unop) (t : S.X₂.obj.obj (Opposite.op V)),
      S.g.hom.app _ t = S.X₃.obj.map φ.op s → G.obj.map φ.op d = h.hom.app _ t := by
  -- The values of `h` on the chosen local preimages of `s` form a compatible family.
  let x : Presieve.FamilyOfElements (G.obj ⋙ forget AddCommGrpCat.{w})
      (Presheaf.imageSieve S.g.hom s).arrows :=
    fun _ φ hφ ↦ h.hom.app _ (Presheaf.localPreimage S.g.hom s φ hφ)
  have hx : x.Compatible := by
    intro V₁ V₂ W ψ₁ ψ₂ φ₁ φ₂ hφ₁ hφ₂ hw
    simp only [x, Functor.comp_map, TypeCat.ofHom_apply]
    rw [← NatTrans.naturality_apply h.hom, ← NatTrans.naturality_apply h.hom]
    refine app_eq_of_app_eq hS h hh ?_
    simpa [NatTrans.naturality_apply, Presheaf.app_localPreimage] using
      congr(S.X₃.obj.map (Quiver.Hom.op $hw) s)
  obtain ⟨d, hd, -⟩ := Sheaf.isSheaf_obj_comp G (forget AddCommGrpCat.{w}) _
    (Presheaf.imageSieve_mem J S.g.hom s) x hx
  exact ⟨d, fun V φ t ht ↦ (hd φ ⟨t, ht⟩).trans
    (app_eq_of_app_eq hS h hh ((Presheaf.app_localPreimage _ _ _ _).trans ht.symm))⟩

/-- The section of `G` obtained by gluing the values of `h` on local preimages of `s`. -/
private noncomputable def descSection (U : Cᵒᵖ) (s : S.X₃.obj.obj U) : G.obj.obj U :=
  (exists_section hS h hh U s).choose

private lemma map_descSection {U : Cᵒᵖ} (s : S.X₃.obj.obj U) {V : C} (φ : V ⟶ U.unop)
    (t : S.X₂.obj.obj (Opposite.op V)) (ht : S.g.hom.app _ t = S.X₃.obj.map φ.op s) :
    G.obj.map φ.op (descSection hS h hh U s) = h.hom.app _ t :=
  (exists_section hS h hh U s).choose_spec φ t ht

/-- The factorization of `h : S.X₂ ⟶ G` through the locally surjective `S.g`, defined by gluing
the values of `h` on local preimages. -/
private noncomputable def desc : S.X₃ ⟶ G where
  hom :=
    { app U := AddCommGrpCat.ofHom
        { toFun := descSection hS h hh U
          map_zero' := by
            refine G.isSeparated _ _
              (Presheaf.imageSieve_mem J S.g.hom (0 : S.X₃.obj.obj U)) _ _ ?_
            rintro V φ ⟨t, ht⟩
            rw [map_descSection hS h hh _ φ t ht, map_zero,
              app_eq_of_app_eq hS h hh (b := 0) (by rw [ht, map_zero, map_zero]), map_zero]
          map_add' s s' := by
            refine G.isSeparated _ _ (J.intersection_covering
              (Presheaf.imageSieve_mem J S.g.hom s) (Presheaf.imageSieve_mem J S.g.hom s')) _ _ ?_
            rintro V φ ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
            rw [map_add, map_descSection hS h hh _ φ t ht, map_descSection hS h hh _ φ t' ht',
              map_descSection hS h hh _ φ (t + t') (by rw [map_add, map_add, ht, ht']), map_add] }
      naturality U U' ψ := by
        ext s
        refine G.isSeparated _ _ (Presheaf.imageSieve_mem J S.g.hom (S.X₃.obj.map ψ s)) _ _ ?_
        rintro V φ ⟨t, ht⟩
        have hd := map_descSection hS h hh s (φ ≫ ψ.unop) t (by simp [ht])
        simpa [map_descSection hS h hh _ φ t ht] using hd.symm }

private lemma desc_hom_app_apply (U : Cᵒᵖ) (s : S.X₃.obj.obj U) :
    (desc hS h hh).hom.app U s = descSection hS h hh U s :=
  rfl

private lemma g_desc : S.g ≫ desc hS h hh = h := by
  ext U a
  simpa [desc_hom_app_apply] using map_descSection hS h hh (S.g.hom.app U a) (𝟙 U.unop) a (by simp)

/-- **A locally surjective morphism of abelian sheaves is the cokernel of its kernel.** If
`S.g : S.X₂ ⟶ S.X₃` is a locally surjective morphism of sheaves of abelian groups and every
section of `S.X₂` killed by `S.g` comes from `S.X₁`, then `S.g` is a cokernel of `S.f`. No
sheafification is needed. -/
noncomputable def gIsCokernelOfIsLocallySurjective
    (hS : ∀ (U : Cᵒᵖ) (x : S.X₂.obj.obj U), S.g.hom.app U x = 0 → ∃ y, S.f.hom.app U y = x) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun h hh ↦ desc hS h hh) (fun h hh ↦ g_desc hS h hh)
    fun h hh _ hm ↦ (cancel_epi S.g).1 (hm.trans (g_desc hS h hh).symm)

end Cokernel

/-- **Short exactness from local surjectivity.** A complex `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of
abelian groups whose first map is a kernel of the second and whose second map is locally
surjective is short exact. This holds on every site, without any sheafification. -/
theorem shortExact_of_isLocallySurjective (hS : IsLimit (KernelFork.ofι S.f S.zero))
    [Sheaf.IsLocallySurjective S.g] : S.ShortExact := by
  have : HasZeroObject (Sheaf J AddCommGrpCat.{w}) := hasZeroObject_of_hasTerminal_object
  have hS' : TauCeti.IsKernelCokernelPair S :=
    ⟨⟨hS⟩, ⟨gIsCokernelOfIsLocallySurjective (exists_app_eq_of_isLimit hS)⟩⟩
  have := hS'.hasHomology
  exact hS'.shortExact

end CategoryTheory.ShortComplex
