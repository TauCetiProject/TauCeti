/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Category.ModuleCat.ForgetCorepresentable
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.Grothendieck
public import TauCeti.CategoryTheory.Sites.Limits
public import TauCeti.CategoryTheory.Sites.LocallyBijective
public import TauCeti.CategoryTheory.Sites.LocallyConstant.Basic

/-!
# Kernels and cokernels of locally constant sheaves of modules

Let `(C, J)` be a site and `Λ` a ring. A sheaf of `Λ`-modules is locally constant of finite type
if it is locally isomorphic to the constant sheaf on a finitely generated `Λ`-module
(`CategoryTheory.Sheaf.IsLocallyConstantIn J fun M ↦ Module.Finite Λ M`).

The key point is that a morphism between such sheaves is locally constant as well: locally, up to
isomorphisms of its source and target, it is the constant morphism on a linear map of finitely
generated modules (`CategoryTheory.Sheaf.locallyConstantMapSieve`,
`CategoryTheory.Sheaf.IsLocallyConstantIn.locallyConstantMapSieve_mem`). Indeed, a morphism `ψ`
out of a sheaf that is locally constant on `M` is determined, over an object `Y`, by the images of
the constant sections `m : M` over `Y` (`CategoryTheory.Sheaf.hom_app_eq_of_comp_app_eq`); since
`M` is finitely generated, these images are locally constant sections, given by a linear map
`M ⟶ N` (`CategoryTheory.Presheaf.exists_mem_comp_app_eq`).

Consequently kernels and cokernels of morphisms of sheaves of `Λ`-modules that are locally
constant of finite type are again locally constant of finite type, for kernels when `Λ` is
Noetherian (`CategoryTheory.Sheaf.IsLocallyConstantIn.kernel`,
`CategoryTheory.Sheaf.IsLocallyConstantIn.cokernel`). The cokernel statement assumes that
restricting sheaves to the slices `Over Y` preserves cokernels, which holds on the small étale site
of a scheme.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Λ : Type w} [Ring Λ]

namespace Presheaf

/-- **Morphisms between locally constant presheaves are locally constant.** Let `p : M ⟶ F` and
`q : N ⟶ G` be morphisms from constant presheaves of `Λ`-modules, with `M` finitely generated and
`q` locally bijective. Then every morphism `ψ : F ⟶ G` is locally, over the members of a covering
sieve of `Y`, given on the sections `p m` by a linear map `g : M ⟶ N`. -/
theorem exists_mem_comp_app_eq {M N : ModuleCat.{w} Λ} [Module.Finite Λ M]
    {F G : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (p : (Functor.const Cᵒᵖ).obj M ⟶ F)
    (q : (Functor.const Cᵒᵖ).obj N ⟶ G) [Presheaf.IsLocallySurjective J q]
    [Presheaf.IsLocallyInjective J q] (ψ : F ⟶ G) (Y : C) :
    ∃ R ∈ J Y, ∀ ⦃Z : C⦄ (f : Z ⟶ Y), R f →
      ∃ g : M ⟶ N, p.app (op Z) ≫ ψ.app (op Z) = g ≫ q.app (op Z) := by
  -- `p` composed with `ψ`, as a linear map over every object.
  let L (Z : C) : M →ₗ[Λ] G.obj (op Z) := (p.app (op Z) ≫ ψ.app (op Z)).hom
  have hL {Z : C} (f : Z ⟶ Y) (m : M) : L Z m = G.map f.op (L Y m) := by
    simp only [L, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← NatTrans.naturality_apply ψ, ← NatTrans.naturality_apply p]
    -- The constant presheaf on `M` maps `f.op` to the identity of `M`.
    simp
  let R : Sieve Y :=
    { arrows Z _ := ∃ g : M ⟶ N, p.app (op Z) ≫ ψ.app (op Z) = g ≫ q.app (op Z)
      downward_closed := by
        rintro Z W - ⟨g, hg⟩ f
        refine ⟨g, ?_⟩
        have h₁ : p.app (op W) = p.app (op Z) ≫ F.map f.op := by simpa using p.naturality f.op
        have h₂ : q.app (op W) = q.app (op Z) ≫ G.map f.op := by simpa using q.naturality f.op
        rw [h₁, Category.assoc, ψ.naturality, reassoc_of% hg, h₂] }
  classical
  refine ⟨R, ?_, fun Z f hf ↦ hf⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  -- A covering sieve over which the images of the generators are constant sections.
  let S : Sieve Y := s.inf fun m ↦ Presheaf.imageSieve q (L Y m)
  have hS : S ∈ J Y := J.finset_inf_mem fun m _ ↦ Presheaf.imageSieve_mem J q (L Y m)
  refine J.transitive hS R fun Z f hf ↦ ?_
  by_cases hbot : ⊥ ∈ J Z
  · exact J.superset_covering bot_le hbot
  refine J.covering_of_eq_top (Sieve.pullback_eq_top_of_mem R ?_)
  have hinj : Function.Injective (q.app (op Z)).hom :=
    Presheaf.injective_app_of_isLocallyInjective_const J q hbot
  have hrange : LinearMap.range (L Z) ≤ LinearMap.range (q.app (op Z)).hom := by
    rw [LinearMap.range_eq_map, ← hs, Submodule.map_span_le]
    intro m hm
    obtain ⟨n, hn⟩ := Finset.inf_le (f := fun m ↦ Presheaf.imageSieve q (L Y m)) hm f hf
    exact ⟨n, hn.trans (hL f m).symm⟩
  let e := LinearEquiv.ofInjective (q.app (op Z)).hom hinj
  refine ⟨ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ (L Z).codRestrict _ fun m ↦ hrange ⟨m, rfl⟩), ?_⟩
  ext m
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  exact (congrArg Subtype.val (e.apply_symm_apply ⟨L Z m, hrange ⟨m, rfl⟩⟩)).symm

end Presheaf

namespace Sheaf

section Local

/-- **Morphisms out of locally constant sheaves are determined by constant sections.** Let
`p : M ⟶ F` be a locally surjective morphism from the constant presheaf on a `Λ`-module `M` to a
sheaf `F`, and let `a b : F ⟶ H` be morphisms of sheaves that agree on the sections `p m` over `Y`.
Then `a` and `b` agree over every object mapping to `Y`. -/
theorem hom_app_eq_of_comp_app_eq {M : ModuleCat.{w} Λ} {F H : Sheaf J (ModuleCat.{w} Λ)}
    (p : (Functor.const Cᵒᵖ).obj M ⟶ F.obj) [Presheaf.IsLocallySurjective J p] {a b : F ⟶ H}
    {Y : C} (h : p.app (op Y) ≫ a.hom.app (op Y) = p.app (op Y) ≫ b.hom.app (op Y))
    {W : C} (g : W ⟶ Y) : a.hom.app (op W) = b.hom.app (op W) := by
  ext s
  have := (Presheaf.isLocallySurjective_iff_whisker_forget J p).1 inferInstance
  refine Presheaf.ext_of_isLocallySurjective J (Functor.whiskerRight p (forget _))
    (Z := (sheafCompose J (forget _)).obj H) s fun V f t ht ↦ ?_
  have key (c : F ⟶ H) : H.obj.map f.op (c.hom.app (op W) s) =
      H.obj.map (f ≫ g).op (c.hom.app (op Y) (p.app (op Y) t)) := by
    rw [← NatTrans.naturality_apply c.hom, ← NatTrans.naturality_apply c.hom]
    congr 1
    exact ht.symm.trans (NatTrans.naturality_apply p (f ≫ g).op t)
  have := congr($h t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact (key a).trans ((congrArg _ this).trans (key b).symm)

end Local

section Constant

variable [HasWeakSheafify J (ModuleCat.{w} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]

/-- **Morphisms between constant sheaves are locally constant.** Let `φ : F ⟶ G` be a morphism of
sheaves of `Λ`-modules whose restrictions to `Over Y` are isomorphic to the restrictions of the
constant sheaves on `M` and `N`, with `M` finitely generated. Over the members of a covering sieve
of `Y`, `φ` is, up to these isomorphisms, the constant morphism on a linear map `g : M ⟶ N`. -/
theorem exists_mem_overPullback_map_eq_of_iso {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G)
    {Y : C} {M N : ModuleCat.{w} Λ} [Module.Finite Λ M]
    (eF : F.over Y ≅ ((constantSheaf J (ModuleCat.{w} Λ)).obj M).over Y)
    (eG : G.over Y ≅ ((constantSheaf J (ModuleCat.{w} Λ)).obj N).over Y) :
    ∃ R ∈ J Y, ∀ ⦃Z : C⦄ (f : Z ⟶ Y), R f → ∃ g : M ⟶ N,
      (J.overPullback (ModuleCat.{w} Λ) Z).map φ ≫ (overIsoRestrict eG f).hom =
        (overIsoRestrict eF f).hom ≫
          (J.overPullback (ModuleCat.{w} Λ) Z).map ((constantSheaf J (ModuleCat.{w} Λ)).map g) := by
  -- Over `Y`, `F` and `G` receive locally bijective maps from the constant presheaves.
  obtain ⟨R, hR, hRg⟩ := Presheaf.exists_mem_comp_app_eq (J := J.over Y) (constToOver eF)
    (constToOver eG) ((J.overPullback (ModuleCat.{w} Λ) Y).map φ).hom (Over.mk (𝟙 Y))
  refine ⟨Sieve.overEquiv _ R, hR, fun Z f hf ↦ ?_⟩
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨g, hg⟩ := hRg _ hf
  refine ⟨g, ?_⟩
  ext W : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    overIsoRestrict_hom_hom_app]
  -- Both sides are determined by their values on the constant sections over `f`.
  refine hom_app_eq_of_comp_app_eq (J := J.over Y) (constToOver eF)
    (a := (J.overPullback (ModuleCat.{w} Λ) Y).map φ ≫ eG.hom)
    (b := eF.hom ≫ (J.overPullback (ModuleCat.{w} Λ) Y).map
      ((constantSheaf J (ModuleCat.{w} Λ)).map g)) ?_
    (Over.homMk W.unop.hom (by simp) : (Over.map f).obj W.unop ⟶ Over.mk (f ≫ 𝟙 Y))
  simp only [Over.mk_hom] at hg
  -- `hg` must rewrite before `constantSheaf` and `Sheaf.over` are unfolded.
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, reassoc_of% hg,
    constToOver_comp_hom_app, constToOver_comp_hom_app_assoc]
  have hη := congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map g)) (op Z)
  simp only [constantSheaf, Functor.comp_map, Over.mk_left,
    Functor.sheafPushforwardContinuous_map_hom_app, Over.forget_obj, NatTrans.comp_app,
    Functor.const_map_app] at hη ⊢
  -- The terms now agree; the stated objects differ by unfolding `Functor.const` and `Sheaf.over`.
  exact hη

/-- The sieve of morphisms `Y ⟶ X` over which a morphism `φ : F ⟶ G` of sheaves of `Λ`-modules is,
up to isomorphisms of its source and target, the constant morphism on a linear map of finitely
generated `Λ`-modules. -/
def locallyConstantMapSieve {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G) (X : C) : Sieve X where
  arrows Y _ := ∃ (M N : ModuleCat.{w} Λ) (_ : Module.Finite Λ M) (_ : Module.Finite Λ N)
    (g : M ⟶ N) (eF : F.over Y ≅ ((constantSheaf J (ModuleCat.{w} Λ)).obj M).over Y)
    (eG : G.over Y ≅ ((constantSheaf J (ModuleCat.{w} Λ)).obj N).over Y),
    (J.overPullback (ModuleCat.{w} Λ) Y).map φ ≫ eG.hom =
      eF.hom ≫ (J.overPullback (ModuleCat.{w} Λ) Y).map ((constantSheaf J (ModuleCat.{w} Λ)).map g)
  downward_closed := by
    rintro Y Z - ⟨M, N, hM, hN, g, eF, eG, w⟩ h
    refine ⟨M, N, hM, hN, g, overIsoRestrict eF h, overIsoRestrict eG h, ?_⟩
    ext W : 3
    have := congr_app congr($(w).hom) (op ((Over.map h).obj W.unop))
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      overIsoRestrict_hom_hom_app, Functor.sheafPushforwardContinuous_map_hom_app,
      Over.forget_obj, Over.map_obj_left] at this ⊢
    -- The terms now agree; the stated objects differ by unfolding `Over.map` and `Sheaf.over`.
    exact this

omit [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)] in
@[simp]
lemma locallyConstantMapSieve_apply {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G) {X Y : C}
    (f : Y ⟶ X) :
    locallyConstantMapSieve φ X f ↔ ∃ (M N : ModuleCat.{w} Λ) (_ : Module.Finite Λ M)
      (_ : Module.Finite Λ N) (g : M ⟶ N)
      (eF : F.over Y ≅ ((constantSheaf J (ModuleCat.{w} Λ)).obj M).over Y)
      (eG : G.over Y ≅ ((constantSheaf J (ModuleCat.{w} Λ)).obj N).over Y),
      (J.overPullback (ModuleCat.{w} Λ) Y).map φ ≫ eG.hom =
        eF.hom ≫ (J.overPullback (ModuleCat.{w} Λ) Y).map
          ((constantSheaf J (ModuleCat.{w} Λ)).map g) :=
  Iff.rfl

omit [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)] in
/-- Whether a morphism is constant over `Y ⟶ X` does not depend on `X`, so these sieves are
stable under pullback. -/
@[simp]
lemma pullback_locallyConstantMapSieve {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G) {X Z : C}
    (g : Z ⟶ X) : (locallyConstantMapSieve φ X).pullback g = locallyConstantMapSieve φ Z :=
  Sieve.ext fun _ _ ↦ Iff.rfl

/-- **Morphisms of locally constant sheaves are locally constant.** A morphism between sheaves of
`Λ`-modules that are locally constant of finite type is, locally on the site and up to
isomorphisms of its source and target, the constant morphism on a linear map of finitely
generated `Λ`-modules. -/
theorem IsLocallyConstantIn.locallyConstantMapSieve_mem {F G : Sheaf J (ModuleCat.{w} Λ)}
    (hF : F.IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M)
    (hG : G.IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M) (φ : F ⟶ G)
    (X : C) : locallyConstantMapSieve φ X ∈ J X := by
  refine J.transitive (J.intersection_covering ((isLocallyConstantIn_iff _ F).1 hF X)
    ((isLocallyConstantIn_iff _ G).1 hG X)) _ fun Y f hf ↦ ?_
  obtain ⟨M, hM, ⟨eF⟩⟩ := (locallyConstantSieve_apply _ F f).1 hf.1
  obtain ⟨N, hN, ⟨eG⟩⟩ := (locallyConstantSieve_apply _ G f).1 hf.2
  obtain ⟨R, hR, hRg⟩ := exists_mem_overPullback_map_eq_of_iso φ eF eG
  refine J.superset_covering (fun Z h hh ↦ ?_) hR
  obtain ⟨g, hg⟩ := hRg h hh
  exact ⟨M, N, hM, hN, g, overIsoRestrict eF h, overIsoRestrict eG h, hg⟩

end Constant

section Closure

variable [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]

/-- **Kernels of locally constant sheaves.** Over a Noetherian ring `Λ`, the kernel of a morphism
between sheaves of `Λ`-modules that are locally constant of finite type is locally constant of
finite type. -/
theorem IsLocallyConstantIn.kernel [HasSheafify J (ModuleCat.{w} Λ)] [IsNoetherianRing Λ]
    {F G : Sheaf J (ModuleCat.{w} Λ)}
    (hF : F.IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M)
    (hG : G.IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M) (φ : F ⟶ G) :
    (kernel φ).IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M := by
  refine (isLocallyConstantIn_iff _ _).2 fun X ↦
    J.superset_covering (fun Y f hf ↦ ?_) (hF.locallyConstantMapSieve_mem hG φ X)
  obtain ⟨M, N, hM, -, g, eF, eG, w⟩ := hf
  refine (locallyConstantSieve_apply _ _ f).2 ⟨Limits.kernel g,
    Module.Finite.equiv (ModuleCat.kernelIsoKer g).symm.toLinearEquiv,
    ⟨PreservesKernel.iso (J.overPullback (ModuleCat.{w} Λ) Y) φ ≪≫ kernel.mapIso _ _ eF eG w ≪≫
      (PreservesKernel.iso (J.overPullback (ModuleCat.{w} Λ) Y) _).symm ≪≫
      (J.overPullback (ModuleCat.{w} Λ) Y).mapIso
        (PreservesKernel.iso (constantSheaf J (ModuleCat.{w} Λ)) g).symm⟩⟩

/-- **Cokernels of locally constant sheaves.** If restricting sheaves to the slices `Over Y`
preserves cokernels, the cokernel of a morphism between sheaves of `Λ`-modules that are locally
constant of finite type is locally constant of finite type. -/
theorem IsLocallyConstantIn.cokernel [HasWeakSheafify J (ModuleCat.{w} Λ)]
    [∀ Y : C, PreservesColimitsOfShape WalkingParallelPair (J.overPullback (ModuleCat.{w} Λ) Y)]
    {F G : Sheaf J (ModuleCat.{w} Λ)}
    (hF : F.IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M)
    (hG : G.IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M) (φ : F ⟶ G) :
    (cokernel φ).IsLocallyConstantIn J fun M : ModuleCat.{w} Λ ↦ Module.Finite Λ M := by
  -- `constantSheaf` is the constant presheaf functor followed by sheafification, a left adjoint.
  have : (constantSheaf J (ModuleCat.{w} Λ)).PreservesZeroMorphisms :=
    inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J _).PreservesZeroMorphisms
  refine (isLocallyConstantIn_iff _ _).2 fun X ↦
    J.superset_covering (fun Y f hf ↦ ?_) (hF.locallyConstantMapSieve_mem hG φ X)
  obtain ⟨M, N, -, hN, g, eF, eG, w⟩ := hf
  refine (locallyConstantSieve_apply _ _ f).2 ⟨Limits.cokernel g,
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient g).symm.toLinearEquiv,
    ⟨PreservesCokernel.iso (J.overPullback (ModuleCat.{w} Λ) Y) φ ≪≫ cokernel.mapIso _ _ eF eG w ≪≫
      (PreservesCokernel.iso (J.overPullback (ModuleCat.{w} Λ) Y) _).symm ≪≫
      (J.overPullback (ModuleCat.{w} Λ) Y).mapIso
        (PreservesCokernel.iso (constantSheaf J (ModuleCat.{w} Λ)) g).symm⟩⟩

end Closure

end Sheaf

end CategoryTheory
