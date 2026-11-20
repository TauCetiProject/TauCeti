/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Prestack
public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.PullHom
public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Separated
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Sites.Big.GmGrp
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian.Basic

/-!
# The frame torsor of an invertible sheaf

Let `S` be a scheme and `M` an `𝒪_S`-module. Its *sheaf of frames* is the presheaf on the big
site `Over S` whose sections over an `S`-scheme `h : T ⟶ S` are the isomorphisms
`h^* 𝒪_S ≅ h^* M`, that is, the isomorphisms `𝒪_T ≅ h^* M`
(`AlgebraicGeometry.Scheme.Modules.frameSheafObjEquiv`). It is the subpresheaf of isomorphisms
in Mathlib's presheaf of morphisms `Pseudofunctor.presheafHom 𝒪_S M` of the pullback
pseudofunctor of modules. For quasi-coherent `M` it is a sheaf for every topology `J` coarser than
the fpqc topology: the presheaf of morphisms is the sheaf `T ↦ Γ(T, h^* M)` (Stacks, Lemma 35.8.1),
and being an isomorphism of quasi-coherent modules is fpqc local
(`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_fpqc`).

The units `Γ(T, 𝒪_T)ˣ`, the sections of the sheaf of groups `𝔾_m`
(`AlgebraicGeometry.Scheme.GmGrp`), act on the frames by `g • φ = φ ∘ g⁻¹`, where a unit acts on
`h^* 𝒪_S` by multiplication. This action is simply transitive, because the automorphisms of the
invertible sheaf `h^* 𝒪_S ≅ 𝒪_T` are the global units
(`AlgebraicGeometry.Scheme.Modules.unitsGlobalSectionsMulEquivAut`). When `M` is invertible it
has frames on an open cover of `S`, so for every topology `J` between the Zariski and the fpqc
topology, the frames form a `𝔾_m`-torsor on the big `J`-site of `S`, the *frame torsor*
`Isom(𝒪_S, M)`.

Isomorphic invertible sheaves have isomorphic frame torsors, so taking the class of the frame
torsor defines a map from the isomorphism classes of line bundles to the torsor classes of `𝔾_m`.
This map is injective: a morphism of frame torsors `α` gives, on every `S`-scheme `T` with a frame
`φ`, the isomorphism `α(φ) ∘ φ⁻¹ : h^* M ⟶ h^* N`, which does not depend on `φ`; these glue by fpqc
descent of morphisms of quasi-coherent modules
(`TauCeti.AlgebraicGeometry.Descent.existsUnique_pullback_map_eq_of_mem_fpqcTopology`) to an
isomorphism `M ≅ N`. It sends the trivial line bundle to the base point, and the class of `M` is
the base point exactly when `M` is isomorphic to `𝒪_S`. Surjectivity, every `𝔾_m`-torsor being
the frame torsor of a line bundle, needs effective descent of invertible sheaves and is not proved
here.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.frameSheaf M hJ`: the sheaf of frames of a quasi-coherent
  module.
* `AlgebraicGeometry.Scheme.Modules.frameTorsor M hJ hZ`: the frame torsor of an invertible sheaf,
  a torsor under `GmGrp S J hJ`.
* `AlgebraicGeometry.Scheme.Modules.frameTorsorIsoOfIso`: isomorphic sheaves have isomorphic frame
  torsors.
* `AlgebraicGeometry.Scheme.Modules.exists_pullback_map_eq_of_frameTorsor_hom`: a morphism of
  frame torsors comes from a morphism of the sheaves, glued from the isomorphisms `α(φ) ∘ φ⁻¹`.
* `AlgebraicGeometry.Scheme.Modules.nonempty_frameTorsor_iso_iff`: two invertible sheaves are
  isomorphic exactly when their frame torsors are.
* `AlgebraicGeometry.Scheme.Modules.mk_frameTorsor_eq_one_iff`: the frame torsor of `M` is trivial
  exactly when `M` is isomorphic to `𝒪_S`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.frameTorsorClass`: the injective map from line
  bundle classes to torsor classes of `𝔾_m`, with `frameTorsorClass_one` and
  `frameTorsorClass_injective`.

## References

* [Stacks Project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG), torsors
  under a sheaf of groups.
* [Stacks Project, Theorem 59.24.1 (03P8)](https://stacks.math.columbia.edu/tag/03P8), the
  identification of `Pic(S)` with the classes of `𝔾_m`-torsors, of which the injectivity of the
  frame-torsor class map is the half proved here.
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

open Pseudofunctor.LocallyDiscreteOpToCat TauCeti.AlgebraicGeometry.Descent
  TauCeti.AlgebraicGeometry.SheafOfModules

namespace Modules

variable {S : Scheme.{u}} {J : GrothendieckTopology Scheme.{u}}

variable (M : S.Modules)

/-- The frames of an `𝒪_S`-module `M`: the subpresheaf of the presheaf of morphisms
`T ↦ (h^* 𝒪_S ⟶ h^* M)` on the big site of `S` given by the isomorphisms. -/
def frameSubfunctor : Subfunctor (modulesPseudofunctor.presheafHom (𝟙_ S.Modules) M) where
  obj _ := {e | IsIso e}
  map f e he := by
    have : IsIso e := he
    exact Pseudofunctor.isIso_pullHom e f.unop.left _ _ (Over.w f.unop) (Over.w f.unop)

@[simp]
lemma mem_frameSubfunctor_iff {T : (Over S)ᵒᵖ}
    (e : (modulesPseudofunctor.presheafHom (𝟙_ S.Modules) M).obj T) :
    e ∈ (frameSubfunctor M).obj T ↔ IsIso e :=
  Iff.rfl

variable {M} in
/-- Being an isomorphism of quasi-coherent modules on the big site is local for every topology
coarser than the fpqc topology: a morphism `h^* 𝒪_S ⟶ h^* M` whose restrictions along a covering
sieve are isomorphisms is an isomorphism. -/
lemma isIso_of_mem_sieveOfSection [M.IsQuasicoherent] (hJ : J ≤ fpqcTopology) {T : Over S}
    (e : (modulesPseudofunctor.presheafHom (𝟙_ S.Modules) M).obj (op T))
    (he : (frameSubfunctor M).sieveOfSection e ∈ (J.over S) T) : IsIso e := by
  rw [GrothendieckTopology.mem_over_iff] at he
  let R := Sieve.overEquiv T ((frameSubfunctor M).sieveOfSection e)
  refine Hom.isIso_of_fpqc (M := (pullback T.hom).obj (𝟙_ S.Modules))
    (N := (pullback T.hom).obj M) e (X := fun i : Σ Y : Scheme.{u}, {g : Y ⟶ T.left // R g} ↦ i.1)
    (fun i ↦ i.2.val) (fpqcTopology.superset_covering (fun Y g hg ↦ ?_) (hJ _ he)) fun i ↦ ?_
  · exact Sieve.ofArrows_mk _ _ (⟨Y, ⟨g, hg⟩⟩ : Σ Y : Scheme.{u}, {g : Y ⟶ T.left // R g})
  · have hi : IsIso (pullHom (F := modulesPseudofunctor) e i.2.val (i.2.val ≫ T.hom)
        (i.2.val ≫ T.hom) rfl rfl) := (Sieve.overEquiv_iff _ i.2.val).mp i.2.property
    exact (Pseudofunctor.isIso_pullHom_iff e i.2.val _ _ rfl rfl).mp hi

/-- **The frames of a quasi-coherent module form a sheaf.** For a quasi-coherent `𝒪_S`-module `M`,
the presheaf of isomorphisms `h^* 𝒪_S ≅ h^* M` is a sheaf for every topology coarser than the fpqc
topology. -/
theorem isSheaf_frameSubfunctor [M.IsQuasicoherent] (hJ : J ≤ fpqcTopology) :
    Presieve.IsSheaf (J.over S) (frameSubfunctor M).toFunctor := by
  have h : Presieve.IsSheaf (J.over S) (modulesPseudofunctor.presheafHom (𝟙_ S.Modules) M) :=
    Presieve.isSheaf_iso _ (bigPresheafCompForgetIso M) (Presieve.isSheaf_of_le _
      (fun _ _ hR ↦ hJ _ hR) (isSheaf_bigPresheaf_comp_forget_fpqcTopology M))
  exact ((frameSubfunctor M).isSheaf_iff h).2 fun _ e he ↦ isIso_of_mem_sieveOfSection hJ e he

/-- The sheaf of frames of a quasi-coherent `𝒪_S`-module `M` on the big site of `S`, for a topology
`J` coarser than the fpqc topology: its sections over `h : T ⟶ S` are the isomorphisms
`h^* 𝒪_S ⟶ h^* M` (`frameSheafObjEquiv`). -/
noncomputable def frameSheaf [M.IsQuasicoherent] (hJ : J ≤ fpqcTopology) :
    Sheaf (J.over S) (Type u) :=
  ⟨(frameSubfunctor M).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_frameSubfunctor M hJ)⟩

section Quasicoherent

variable [M.IsQuasicoherent] {hJ : J ≤ fpqcTopology}

/-- The frames of `M` over an `S`-scheme `h : T ⟶ S` are the isomorphisms `h^* 𝒪_S ≅ h^* M`. -/
noncomputable def frameSheafObjEquiv (T : Over S) :
    (frameSheaf M hJ).obj.obj (op T) ≃
      ((pullback T.hom).obj (𝟙_ S.Modules) ≅ (pullback T.hom).obj M) where
  toFun e := @asIso T.left.Modules _ ((pullback T.hom).obj (𝟙_ S.Modules)) ((pullback T.hom).obj M)
    e.val e.property
  invFun i := ⟨i.hom, i.isIso_hom⟩
  left_inv _ := rfl
  right_inv _ := by ext1; rfl

/-- An `S`-scheme `h : T ⟶ S` carries a frame of `M` exactly when `h^* M` is isomorphic to `𝒪_T`. -/
lemma nonempty_frameSheaf_obj_iff (T : Over S) :
    Nonempty ((frameSheaf M hJ).obj.obj (op T)) ↔
      Nonempty (𝟙_ T.left.Modules ≅ (pullback T.hom).obj M) :=
  (frameSheafObjEquiv M T).nonempty_congr.trans
    ⟨fun ⟨i⟩ ↦ ⟨(pullbackObjUnitIso T.hom).symm ≪≫ i⟩, fun ⟨i⟩ ↦ ⟨pullbackObjUnitIso T.hom ≪≫ i⟩⟩

/-- A unit `g` of `Γ(T, 𝒪_T)` acts on the frames of `M` over `T` by `φ ↦ φ ∘ g⁻¹`, where `g⁻¹`
acts on `h^* 𝒪_S` by multiplication. -/
noncomputable instance (T : (Over S)ᵒᵖ) :
    SMul ((GmGrp S J hJ).obj.obj T) ((frameSheaf M hJ).obj.obj T) where
  smul g e := (frameSheafObjEquiv M T.unop).symm (asIso (globalSectionsSmul
    ((pullback T.unop.hom).obj (𝟙_ S.Modules)) ↑((GmGrpObjEquiv T.unop).symm g)⁻¹) ≪≫
      frameSheafObjEquiv M T.unop e)

/-- The action of a section `g` of `𝔾_m` on a frame `φ` is `φ ∘ g⁻¹`. -/
lemma frameSheafObjEquiv_smul (T : (Over S)ᵒᵖ) (g : (GmGrp S J hJ).obj.obj T)
    (e : (frameSheaf M hJ).obj.obj T) :
    frameSheafObjEquiv M T.unop (g • e) =
      asIso (globalSectionsSmul ((pullback T.unop.hom).obj (𝟙_ S.Modules))
        ↑((GmGrpObjEquiv T.unop).symm g)⁻¹) ≪≫ frameSheafObjEquiv M T.unop e :=
  Equiv.apply_symm_apply _ _

/-- The action of `𝔾_m` on frames is a group action. -/
noncomputable instance (T : (Over S)ᵒᵖ) :
    MulAction ((GmGrp S J hJ).obj.obj T) ((frameSheaf M hJ).obj.obj T) where
  one_smul e := (frameSheafObjEquiv M T.unop).injective (by
    ext1
    rw [frameSheafObjEquiv_smul]
    simp)
  mul_smul g g' e := (frameSheafObjEquiv M T.unop).injective (by
    ext1
    rw [frameSheafObjEquiv_smul, frameSheafObjEquiv_smul, frameSheafObjEquiv_smul]
    simp [globalSectionsSmul_mul])

/-- The action of a unit `u` on a frame `φ` is `φ ∘ u⁻¹`. -/
@[simp]
lemma frameSheafObjEquiv_GmGrpObjEquiv_smul (T : Over S) (u : Γ(T.left, ⊤)ˣ)
    (e : (frameSheaf M hJ).obj.obj (op T)) :
    frameSheafObjEquiv M T (GmGrpObjEquiv (hJ := hJ) T u • e) =
      asIso (globalSectionsSmul ((pullback T.hom).obj (𝟙_ S.Modules)) ↑u⁻¹) ≪≫
        frameSheafObjEquiv M T e := by
  simp only [frameSheafObjEquiv_smul M (op T), unop_op, MulEquiv.symm_apply_apply]

/-- The restriction maps of the sheaf of frames, read on isomorphisms. -/
@[simp]
lemma frameSheafObjEquiv_map_hom {T T' : Over S} (f : T ⟶ T')
    (e : (frameSheaf M hJ).obj.obj (op T')) :
    (frameSheafObjEquiv M T ((frameSheaf M hJ).obj.map f.op e)).hom =
      pullHom (F := modulesPseudofunctor) (M₁ := 𝟙_ S.Modules) (M₂ := M) (f₁ := T'.hom)
        (f₂ := T'.hom) (frameSheafObjEquiv M T' e).hom f.left T.hom T.hom (Over.w f) (Over.w f) :=
  (rfl)

/-- The action of `𝔾_m` on frames commutes with restriction. -/
lemma frameSheaf_map_smul {T T' : Over S} (f : T ⟶ T') (g : (GmGrp S J hJ).obj.obj (op T'))
    (e : (frameSheaf M hJ).obj.obj (op T')) :
    (frameSheaf M hJ).obj.map f.op (g • e) =
      (GmGrp S J hJ).obj.map f.op g • (frameSheaf M hJ).obj.map f.op e := by
  obtain ⟨u, rfl⟩ := (GmGrpObjEquiv T').surjective g
  refine (frameSheafObjEquiv M T).injective (Iso.ext ?_)
  rw [GmGrp_map_GmGrpObjEquiv]
  simp only [frameSheafObjEquiv_GmGrpObjEquiv_smul, frameSheafObjEquiv_map_hom, Iso.trans_hom,
    asIso_hom, Units.coe_map_inv]
  -- The substantive step: restriction commutes with multiplication by a unit.
  exact pullHom_globalSectionsSmul_comp _ _ _ _ _ _ _

/-- **The action of `𝔾_m` on frames is simply transitive.** Two frames `φ, φ'` of `M` over `T`
differ by a unique unit `g` of `Γ(T, 𝒪_T)`, because the automorphisms of the invertible sheaf
`h^* 𝒪_S ≅ 𝒪_T` are the global units. -/
lemma existsUnique_smul_eq (T : Over S) (e e' : (frameSheaf M hJ).obj.obj (op T)) :
    ∃! g : (GmGrp S J hJ).obj.obj (op T), g • e = e' := by
  let A := (pullback T.hom).obj (𝟙_ S.Modules)
  let v := (unitsGlobalSectionsMulEquivAut A).symm
    (Aut.of (frameSheafObjEquiv M T e' ≪≫ (frameSheafObjEquiv M T e).symm))
  have hv : globalSectionsSmul A v =
      (frameSheafObjEquiv M T e').hom ≫ (frameSheafObjEquiv M T e).inv := by
    rw [globalSectionsSmul_unitsGlobalSectionsMulEquivAut_symm]
    rfl
  refine ⟨GmGrpObjEquiv T v⁻¹, (frameSheafObjEquiv M T).injective (Iso.ext ?_), fun g hg ↦ ?_⟩
  · rw [frameSheafObjEquiv_GmGrpObjEquiv_smul]
    simpa using hv =≫ (frameSheafObjEquiv M T e).hom
  · obtain ⟨w, rfl⟩ := (GmGrpObjEquiv T).surjective g
    have hw : globalSectionsSmul A ↑w⁻¹ =
        (frameSheafObjEquiv M T e').hom ≫ (frameSheafObjEquiv M T e).inv := by
      rw [Iso.eq_comp_inv, ← hg, frameSheafObjEquiv_GmGrpObjEquiv_smul, Iso.trans_hom, asIso_hom]
    refine congrArg _ (inv_eq_iff_eq_inv.mp (Units.ext (globalSectionsAction_injective A ?_)))
    rw [globalSectionsAction_apply, globalSectionsAction_apply, hw, hv]

/-- The inverse of a restricted frame is the restriction of the inverse. -/
@[simp]
lemma frameSheafObjEquiv_map_inv {T T' : Over S} (f : T ⟶ T')
    (e : (frameSheaf M hJ).obj.obj (op T')) :
    (frameSheafObjEquiv M T ((frameSheaf M hJ).obj.map f.op e)).inv =
      pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := 𝟙_ S.Modules) (f₁ := T'.hom)
        (f₂ := T'.hom) (frameSheafObjEquiv M T' e).inv f.left T.hom T.hom (Over.w f)
        (Over.w f) := by
  simp only [← IsIso.Iso.inv_hom, frameSheafObjEquiv_map_hom]
  -- The instance is passed explicitly: the frame lives in `T'.left.Modules`, while `pullHom` is
  -- stated in the categories of `modulesPseudofunctor`, where instance search does not find it.
  exact @Pseudofunctor.inv_pullHom _ _ _ _ _ _ _ _ _ _ _ (frameSheafObjEquiv M T' e).isIso_hom
    _ _ _ _ _ _

variable {M} {N : S.Modules} [N.IsQuasicoherent]

/-- An isomorphism `ι : M ≅ N` sends a frame `φ` of `M` over `h : T ⟶ S` to the frame `h^* ι ∘ φ`
of `N`. -/
noncomputable def frameMapOfIso (ι : M ≅ N) (T : Over S) :
    (frameSheaf M hJ).obj.obj (op T) → (frameSheaf N hJ).obj.obj (op T) :=
  fun e ↦ (frameSheafObjEquiv N T).symm (frameSheafObjEquiv M T e ≪≫ (pullback T.hom).mapIso ι)

@[simp]
lemma frameSheafObjEquiv_frameMapOfIso (ι : M ≅ N) (T : Over S)
    (e : (frameSheaf M hJ).obj.obj (op T)) :
    frameSheafObjEquiv N T (frameMapOfIso ι T e) =
      frameSheafObjEquiv M T e ≪≫ (pullback T.hom).mapIso ι :=
  Equiv.apply_symm_apply _ _

/-- The map of frames induced by an isomorphism commutes with restriction. -/
lemma frameSheaf_map_frameMapOfIso (ι : M ≅ N) {T T' : Over S} (f : T ⟶ T')
    (e : (frameSheaf M hJ).obj.obj (op T')) :
    (frameSheaf N hJ).obj.map f.op (frameMapOfIso ι T' e) =
      frameMapOfIso ι T ((frameSheaf M hJ).obj.map f.op e) := by
  refine (frameSheafObjEquiv N T).injective (Iso.ext ?_)
  rw [frameSheafObjEquiv_map_hom, frameSheafObjEquiv_frameMapOfIso,
    frameSheafObjEquiv_frameMapOfIso, Iso.trans_hom, Iso.trans_hom, frameSheafObjEquiv_map_hom]
  exact pullHom_comp_pullback_map _ ι.hom _ _ _ _ _

/-- The map of frames induced by an isomorphism is `𝔾_m`-equivariant. -/
lemma frameMapOfIso_smul (ι : M ≅ N) (T : Over S) (g : (GmGrp S J hJ).obj.obj (op T))
    (e : (frameSheaf M hJ).obj.obj (op T)) :
    frameMapOfIso ι T (g • e) = g • frameMapOfIso ι T e := by
  refine (frameSheafObjEquiv N T).injective ?_
  rw [frameSheafObjEquiv_frameMapOfIso, frameSheafObjEquiv_smul M (op T),
    frameSheafObjEquiv_smul N (op T), frameSheafObjEquiv_frameMapOfIso, Iso.trans_assoc]

end Quasicoherent

section Invertible

variable {hJ : J ≤ fpqcTopology} [isInvertible S M]

/-- An invertible sheaf has frames locally for every topology `J` finer than the Zariski topology:
the `S`-schemes carrying a frame of `M` cover the big site. -/
lemma coversTop_frameSheaf (hZ : zariskiTopology ≤ J) :
    (J.over S).CoversTop
      fun T : {T : Over S // Nonempty ((frameSheaf M hJ).obj.obj (op T))} ↦ T.val := by
  obtain ⟨ι, W, hW, e⟩ := isInvertible_iff_exists_isOpenCover.mp ‹isInvertible S M›
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ Over.mkIdTerminal,
    GrothendieckTopology.mem_over_iff]
  refine hZ _ (zariskiTopology.superset_covering ?_
    (S.openCoverOfIsOpenCover W hW).mem_grothendieckTopology)
  rintro Y _ ⟨Z, a, _, ⟨i⟩, rfl⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨⟨Over.mk (W i).ι, (nonempty_frameSheaf_obj_iff M _).2
    ⟨(e i).some ≪≫ (restrictFunctorIsoPullback (W i).ι).app M⟩⟩, ⟨Over.homMk a rfl⟩⟩

variable (hJ) (hZ : zariskiTopology ≤ J)

/-- **The frame torsor of an invertible sheaf.** For an invertible `𝒪_S`-module `M` and a topology
`J` between the Zariski and the fpqc topology, the sheaf of frames `Isom(𝒪_S, M)`,
`(h : T ⟶ S) ↦ Isom(h^* 𝒪_S, h^* M)`, with the action `g • φ = φ ∘ g⁻¹` of `𝔾_m`, is a
`𝔾_m`-torsor on the big `J`-site of `S`. -/
-- An abbreviation, so that the sections of the frame torsor are, even for rewriting, those of
-- `frameSheaf`.
noncomputable abbrev frameTorsor : Sheaf.Torsor (GmGrp S J hJ) where
  sheaf := frameSheaf M hJ
  map_smul _ _ f g e := frameSheaf_map_smul M f.unop g e
  coversTop := coversTop_frameSheaf M hZ
  bijective T := by
    refine ⟨fun ⟨g, e⟩ ⟨g', e'⟩ h ↦ ?_, fun x ↦ ?_⟩
    · obtain ⟨h₁, rfl : e = e'⟩ := Prod.ext_iff.1 h
      exact Prod.ext ((existsUnique_smul_eq M T.unop e _).unique h₁ rfl) rfl
    · obtain ⟨g, hg, -⟩ := existsUnique_smul_eq M T.unop x.2 x.1
      exact ⟨(g, x.2), Prod.ext hg rfl⟩

@[simp]
lemma frameTorsor_sheaf : (frameTorsor M hJ hZ).sheaf = frameSheaf M hJ :=
  rfl

variable {M} {N : S.Modules} [isInvertible S N]

/-- An isomorphism `ι : M ≅ N` sends a frame `φ` of `M` to the frame `h^* ι ∘ φ` of `N`. -/
private noncomputable def frameTorsorHomOfIso (ι : M ≅ N) :
    frameTorsor M hJ hZ ⟶ frameTorsor N hJ hZ where
  hom := ObjectProperty.homMk
    { app T := ↾frameMapOfIso ι T.unop
      naturality T T' f := by
        ext e
        exact (frameSheaf_map_frameMapOfIso ι f.unop e).symm }
  map_smul T g e := frameMapOfIso_smul ι T.unop g e

/-- **Isomorphic invertible sheaves have isomorphic frame torsors**: an isomorphism `ι : M ≅ N`
sends a frame `φ` of `M` to the frame `h^* ι ∘ φ` of `N`. -/
noncomputable def frameTorsorIsoOfIso (ι : M ≅ N) : frameTorsor M hJ hZ ≅ frameTorsor N hJ hZ :=
  asIso (frameTorsorHomOfIso hJ hZ ι)

@[simp]
lemma frameTorsorIsoOfIso_hom_hom_hom_app (ι : M ≅ N) (T : Over S)
    (e : (frameSheaf M hJ).obj.obj (op T)) :
    (frameTorsorIsoOfIso hJ hZ ι).hom.hom.hom.app (op T) e = frameMapOfIso ι T e :=
  (rfl)

/-- For a morphism of frame torsors `α`, the isomorphism `α(φ) ∘ φ⁻¹ : h^* M ⟶ h^* N` does not
depend on the frame `φ` of `M` over `T`. -/
lemma frameSheafObjEquiv_inv_comp_hom_app (α : frameTorsor M hJ hZ ⟶ frameTorsor N hJ hZ)
    (T : Over S) (e e' : (frameSheaf M hJ).obj.obj (op T)) :
    (frameSheafObjEquiv M T e).inv ≫
        (frameSheafObjEquiv (hJ := hJ) N T (α.hom.hom.app (op T) e)).hom =
      (frameSheafObjEquiv M T e').inv ≫
        (frameSheafObjEquiv (hJ := hJ) N T (α.hom.hom.app (op T) e')).hom := by
  obtain ⟨g, rfl, -⟩ := existsUnique_smul_eq M T e e'
  rw [α.map_smul]
  simp [frameSheafObjEquiv_smul M (op T), frameSheafObjEquiv_smul N (op T)]

/-- **Morphisms of frame torsors come from morphisms of sheaves.** For a morphism `α` of frame
torsors, the isomorphisms `α(φ) ∘ φ⁻¹ : h^* M ⟶ h^* N`, over the `S`-schemes `T` carrying a frame
`φ` of `M`, glue by fpqc descent to a morphism `M ⟶ N`. -/
theorem exists_pullback_map_eq_of_frameTorsor_hom
    (α : frameTorsor M hJ hZ ⟶ frameTorsor N hJ hZ) :
    ∃ φ : M ⟶ N, ∀ (T : Over S) (e : (frameSheaf M hJ).obj.obj (op T)),
      (pullback T.hom).map φ =
        (frameSheafObjEquiv M T e).inv ≫
          (frameSheafObjEquiv (hJ := hJ) N T (α.hom.hom.app (op T) e)).hom := by
  let R := Sieve.ofObjects
    (fun T : {T : Over S // Nonempty ((frameSheaf M hJ).obj.obj (op T))} ↦ T.val) (Over.mk (𝟙 S))
  have hR : R ∈ (fpqcTopology.over S) (Over.mk (𝟙 S)) :=
    hJ _ ((frameTorsor M hJ hZ).coversTop (Over.mk (𝟙 S)))
  have frame {Z : Over S} (g : Z ⟶ Over.mk (𝟙 S)) (hg : R g) :
      Nonempty ((frameSheaf M hJ).obj.obj (op Z)) := by
    obtain ⟨⟨T, ⟨e⟩⟩, ⟨b⟩⟩ := hg
    exact ⟨(frameSheaf M hJ).obj.map b.op e⟩
  let m : ∀ ⦃Z : Over S⦄ (g : Z ⟶ Over.mk (𝟙 S)), R g →
      ((pullback Z.hom).obj M ⟶ (pullback Z.hom).obj N) := fun Z g hg ↦
    (frameSheafObjEquiv M Z (frame g hg).some).inv ≫
      (frameSheafObjEquiv (hJ := hJ) N Z (α.hom.hom.app (op Z) (frame g hg).some)).hom
  obtain ⟨φ, hφ, -⟩ := existsUnique_pullback_map_eq_of_mem_fpqcTopology hR m
    (fun Z Z' f g hg ↦ by
      -- Compute both sides with the restriction of the frame chosen over `Z`.
      dsimp only [m]
      rw [frameSheafObjEquiv_inv_comp_hom_app hJ hZ α Z' _ ((frameSheaf M hJ).obj.map f.op
        (frame g hg).some)]
      have hα := NatTrans.naturality_apply α.hom.hom f.op (frame g hg).some
      rw [hα, frameSheafObjEquiv_map_inv, frameSheafObjEquiv_map_hom]
      exact (Pseudofunctor.pullHom_comp (F := modulesPseudofunctor) (M₁ := M)
        (M₂ := 𝟙_ S.Modules) (M₃ := N) (f₁ := Z.hom) (f₂ := Z.hom) (f₃ := Z.hom) _ _ f.left Z'.hom
        Z'.hom Z'.hom (Over.w f) (Over.w f) (Over.w f)).symm)
  exact ⟨φ, fun T e ↦ (hφ (Over.mkIdTerminal.from T) ⟨⟨T, ⟨e⟩⟩, ⟨𝟙 T⟩⟩).trans
    (frameSheafObjEquiv_inv_comp_hom_app hJ hZ α T _ e)⟩

/-- **Two invertible sheaves are isomorphic exactly when their frame torsors are.** -/
theorem nonempty_frameTorsor_iso_iff :
    Nonempty (frameTorsor M hJ hZ ≅ frameTorsor N hJ hZ) ↔ Nonempty (M ≅ N) := by
  refine ⟨fun ⟨α⟩ ↦ ?_, fun ⟨ι⟩ ↦ ⟨frameTorsorIsoOfIso hJ hZ ι⟩⟩
  obtain ⟨φ, hφ⟩ := exists_pullback_map_eq_of_frameTorsor_hom hJ hZ α.hom
  obtain ⟨ψ, hψ⟩ := exists_pullback_map_eq_of_frameTorsor_hom hJ hZ α.inv
  have hα (T : Over S) (e : (frameSheaf M hJ).obj.obj (op T)) :
      α.inv.hom.hom.app (op T) (α.hom.hom.hom.app (op T) e) = e := by
    exact congrArg (fun k ↦ k.hom.hom.app (op T) e) α.hom_inv_id
  have hα' (T : Over S) (e : (frameSheaf N hJ).obj.obj (op T)) :
      α.hom.hom.hom.app (op T) (α.inv.hom.hom.app (op T) e) = e := by
    exact congrArg (fun k ↦ k.hom.hom.app (op T) e) α.inv_hom_id
  refine ⟨⟨φ, ψ, ?_, ?_⟩⟩
  · refine Hom.ext_of_coversTop hJ _ _ (coversTop_frameSheaf (hJ := hJ) M hZ) fun ⟨T, ⟨e⟩⟩ ↦ ?_
    rw [CategoryTheory.Functor.map_comp, hφ T e, hψ T (α.hom.hom.hom.app (op T) e), hα]
    simp
  · refine Hom.ext_of_coversTop hJ _ _ (coversTop_frameSheaf (hJ := hJ) N hZ) fun ⟨T, ⟨e⟩⟩ ↦ ?_
    rw [CategoryTheory.Functor.map_comp, hψ T e, hφ T (α.inv.hom.hom.app (op T) e), hα']
    simp

end Invertible

section Trivial

variable (hJ : J ≤ fpqcTopology) (hZ : zariskiTopology ≤ J)

/-- The frame torsor of the structure sheaf is trivial: the identities of the `h^* 𝒪_S` form a
global frame. -/
@[simp]
lemma mk_frameTorsor_tensorUnit :
    Sheaf.NonabelianH1.mk (frameTorsor (𝟙_ S.Modules) hJ hZ) = 1 := by
  refine (Sheaf.NonabelianH1.mk_eq_one_iff _).2
    ⟨fun T ↦ (frameSheafObjEquiv (hJ := hJ) _ T.unop).symm (Iso.refl _), fun {T T'} f ↦ ?_⟩
  refine (frameSheafObjEquiv (hJ := hJ) _ T'.unop).injective (Iso.ext ?_)
  exact (frameSheafObjEquiv_map_hom _ f.unop _).trans (Pseudofunctor.pullHom_id_self _ _ _ _)

variable {M} [isInvertible S M]

/-- **The frame torsor of `M` is trivial exactly when `M` is isomorphic to `𝒪_S`.** -/
theorem mk_frameTorsor_eq_one_iff :
    Sheaf.NonabelianH1.mk (frameTorsor M hJ hZ) = 1 ↔ Nonempty (M ≅ 𝟙_ S.Modules) := by
  rw [← mk_frameTorsor_tensorUnit hJ hZ, Sheaf.NonabelianH1.mk_eq_mk_iff,
    nonempty_frameTorsor_iso_iff]

end Trivial

end Modules

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry Scheme Modules

variable {S : Scheme.{u}} {J : GrothendieckTopology Scheme.{u}} (hJ : J ≤ fpqcTopology)
  (hZ : zariskiTopology ≤ J)

/-- The class of the frame torsor `Isom(𝒪_S, L)` of a line bundle `L`, as a map from line bundle
classes to the torsor classes of `𝔾_m` on the big `J`-site of `S`. It is injective
(`frameTorsorClass_injective`) and sends the trivial class to the base point. -/
noncomputable def frameTorsorClass :
    LineBundleClass S → Sheaf.NonabelianH1 (GmGrp S J hJ) :=
  lift (fun L ↦ Sheaf.NonabelianH1.mk (frameTorsor L.obj hJ hZ)) fun _ _ ⟨ι⟩ ↦
    Sheaf.NonabelianH1.mk_eq_mk_iff.2 ⟨frameTorsorIsoOfIso hJ hZ ι⟩

@[simp]
lemma frameTorsorClass_mk (L : InvertibleSheaf S) :
    frameTorsorClass hJ hZ (mk L) = Sheaf.NonabelianH1.mk (frameTorsor L.obj hJ hZ) :=
  lift_mk L

/-- A line bundle class has trivial frame torsor exactly when it is the trivial class. -/
@[simp]
lemma frameTorsorClass_eq_one_iff {x : LineBundleClass S} :
    frameTorsorClass hJ hZ x = 1 ↔ x = 1 := by
  obtain ⟨L, rfl⟩ := mk_surjective x
  rw [frameTorsorClass_mk, mk_frameTorsor_eq_one_iff, mk_eq_one_iff]

/-- The trivial line bundle has the trivial frame torsor. -/
@[simp]
lemma frameTorsorClass_one : frameTorsorClass hJ hZ (1 : LineBundleClass S) = 1 :=
  (frameTorsorClass_eq_one_iff hJ hZ).2 rfl

/-- **Line bundles are determined by their frame torsors.** -/
theorem frameTorsorClass_injective : Function.Injective (frameTorsorClass (S := S) hJ hZ) := by
  intro x y h
  obtain ⟨L, rfl⟩ := mk_surjective x
  obtain ⟨L', rfl⟩ := mk_surjective y
  rw [frameTorsorClass_mk, frameTorsorClass_mk, Sheaf.NonabelianH1.mk_eq_mk_iff,
    nonempty_frameTorsor_iso_iff] at h
  exact mk_eq_mk_iff.2 h

end TauCeti.AlgebraicGeometry.LineBundleClass
