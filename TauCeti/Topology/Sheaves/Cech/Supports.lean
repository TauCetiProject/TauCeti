/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sets.Compacts
public import TauCeti.Topology.Sheaves.Cech.Colimit
public import TauCeti.Topology.Sheaves.InfFunctor
public import TauCeti.Topology.Sheaves.SupportedCohomology

/-!
# Čech cohomology with supports

Let `P` be a presheaf on a topological space `X` with values in a preadditive category `A` with
kernels, and let `S` be a closed subset of `X`. A section of `P` over an open `W` is *supported in
`S`* when its restriction to `W ∖ S` vanishes. These sections are the kernels

`Γ_S(W, P) = ker (P(W) ⟶ P(W ∖ S))`,

and they form a presheaf `Γ_S P` (`TauCeti.Topology.supportedSections A S`). The kernel is taken in
the category of functors of the presheaf, so `Γ_S P` is functorial in `P`, and its value at `W` is
the kernel of the restriction (`TauCeti.Topology.isLimitSupportedSectionsObjObj`,
`TauCeti.Topology.supportedSectionsObjObjIso`). Enlarging the support is a map
`Γ_S P ⟶ Γ_S' P` for `S ≤ S'`, compatible with the inclusions into `P`, which makes `Γ_S` a
functor of the closed subset `S` (`TauCeti.Topology.supportedSectionsClosedsFunctor`). The
sections of a sheaf supported in `S` form a sheaf
(`TauCeti.Topology.isSheaf_supportedSections_obj`): they are the kernel of a map from `F` to the
sheaf `W ↦ F(W ∖ S)` (`TopCat.Presheaf.isSheaf_infFunctor_op_comp`).

The **Čech cohomology with supports in `S`** is the open-cover Čech cohomology
(`TauCeti.Topology.cechCohomology`) of this presheaf,

`Hⁿ_S(X; P) = Hⁿ(X; Γ_S P)`

(`TauCeti.Topology.supportedCechCohomology`), and on a Hausdorff space the **Čech cohomology with
compact supports** is the colimit over the compact subsets `K`, ordered by inclusion,

`Hⁿ_c(X; P) = colim_K Hⁿ_K(X; P)`

(`TauCeti.Topology.compactSupportCechCohomology`), every compact subset being closed. Both are
functors of the presheaf, and forgetting the supports gives natural maps
`Hⁿ_S(X; P) ⟶ Hⁿ(X; P)` and `Hⁿ_c(X; P) ⟶ Hⁿ(X; P)`. Throughout, `H` denotes open-cover Čech
cohomology.

## Main definitions

* `TauCeti.Topology.supportedSections A S`: the presheaf `Γ_S P` of sections supported in `S`, as
  a functor of `P`, with its inclusion `TauCeti.Topology.supportedSectionsι A S` into `P`.
* `TauCeti.Topology.supportedSectionsMap`: the enlargement of supports `Γ_S P ⟶ Γ_S' P`.
* `TauCeti.Topology.supportedCechCohomology X A n`: `Hⁿ_S(X; P)`, as a functor of `S` and `P`.
* `TauCeti.Topology.supportedCechCohomologyToCech X A n`: forgetting supports,
  `Hⁿ_S(X; P) ⟶ Hⁿ(X; P)`.
* `TauCeti.Topology.compactSupportCechCohomology X A n`: `Hⁿ_c(X; P)`, with its structure maps
  `TauCeti.Topology.compactSupportCechCohomologyι X A n K` from `Hⁿ_K(X; P)`, and the map
  `TauCeti.Topology.compactSupportCechCohomologyDesc X A n f hf` out of it induced by compatible
  maps `f K` out of the `Hⁿ_K(X; P)`.
* `TauCeti.Topology.compactSupportCechCohomologyToCech X A n`: forgetting compact supports,
  `Hⁿ_c(X; P) ⟶ Hⁿ(X; P)`.

## Main results

* `TauCeti.Topology.isZero_supportedSections_obj_obj`: over an open disjoint from `S`, no section
  is supported in `S`; in particular `Γ_∅ P = 0`
  (`TauCeti.Topology.isZero_supportedSections_bot_obj`) and `Hⁿ_∅(X; P) = 0`
  (`TauCeti.Topology.isZero_supportedCechCohomology_obj_bot_obj`).
* `TauCeti.Topology.isIso_supportedSectionsι_app_app`: over an open contained in `S`,
  every section of a presheaf vanishing on the empty set is supported in `S`; in particular
  `Γ_X P = P` (`TauCeti.Topology.isIso_supportedSectionsι_top_app`) and
  `Hⁿ_X(X; P) = Hⁿ(X; P)`
  (`TauCeti.Topology.isIso_supportedCechCohomologyToCech_app_top_app`).
* `TauCeti.Topology.supportedCechCohomologyZeroIso`: for a sheaf `F`, in degree `0`,
  `H⁰_S(X; F) ≅ ker (F(X) ⟶ F(X ∖ S))`, the global sections supported in `S`; forgetting supports
  is then the inclusion into `F(X) ≅ H⁰(X; F)`
  (`supportedCechCohomologyZeroIso_inv_comp_supportedCechCohomologyToCech_app_app`).
* `TauCeti.Topology.isIso_compactSupportCechCohomologyToCech_app`: on a compact Hausdorff space,
  `Hⁿ_c(X; P) ⟶ Hⁿ(X; P)` is an isomorphism for every presheaf vanishing on the empty set, and
  so for every sheaf (`TauCeti.Topology.isIso_compactSupportCechCohomologyToCech_app_sheaf`):
  the whole space is the largest compact subset.

The condition that `P` vanish on the empty set cannot be dropped from
`TauCeti.Topology.isIso_supportedSectionsι_top_app`,
`TauCeti.Topology.isIso_supportedCechCohomologyToCech_app_top_app` and
`TauCeti.Topology.isIso_compactSupportCechCohomologyToCech_app`: `Γ_X P` vanishes on the empty set
even when `P` does not.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, arXiv:1309.2370v6, Appendix A, Definition A.4.3 (Čech cohomology
  with supports in a compact subset and with compact supports) and Lemma A.4.5.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe v' u u'

namespace TauCeti.Topology

variable {X : TopCat.{u}} {A : Type u'} [Category.{v'} A]

variable (A) in
/-- Restriction from an open `W` to `W ∖ S`, natural in `W` and in the presheaf. -/
@[expose, simps!]
def complRestriction (S : Closeds X) :
    𝟭 ((Opens X)ᵒᵖ ⥤ A) ⟶ (Functor.whiskeringLeft _ _ A).obj (Opens.infFunctor S.compl).op where
  app P :=
    { app W := P.map (S.complInclusion W.unop).op
      naturality _ _ _ := by
        simp only [Functor.id_obj, Functor.whiskeringLeft_obj_obj, Functor.comp_map,
          Functor.op_map, ← P.map_comp]
        exact congrArg P.map (Subsingleton.elim _ _) }
  naturality P Q f := NatTrans.ext <| funext fun _ ↦ (f.naturality _).symm

variable (A) in
/-- For closed subsets `S ≤ S'`, restriction from `W ∖ S` to `W ∖ S'`. -/
@[simps!]
private def complRestrictionMap {S S' : Closeds X} (h : S ≤ S') :
    (Functor.whiskeringLeft _ _ A).obj (Opens.infFunctor S.compl).op ⟶
      (Functor.whiskeringLeft _ _ A).obj (Opens.infFunctor S'.compl).op :=
  (Functor.whiskeringLeft _ _ A).map
    (NatTrans.op { app W := homOfLE (inf_le_inf_left W (Set.compl_subset_compl.2 h)) })

private theorem complRestriction_comp_complRestrictionMap {S S' : Closeds X} (h : S ≤ S') :
    complRestriction A S ≫ complRestrictionMap A h = complRestriction A S' := by
  ext P W
  simp only [NatTrans.comp_app, complRestriction_app_app, complRestrictionMap_app_app]
  exact (P.map_comp _ _).symm

section Supported

variable [Preadditive A] [HasKernels A]

attribute [local instance] Preadditive.hasEqualizers_of_hasKernels

variable (A) in
/-- The presheaf of sections supported in a closed subset `S`: its value on `W` is the kernel of
the restriction from `W` to `W ∖ S`. -/
def supportedSections (S : Closeds X) : ((Opens X)ᵒᵖ ⥤ A) ⥤ (Opens X)ᵒᵖ ⥤ A :=
  kernel (complRestriction A S)

variable (A) in
/-- The inclusion of the sections supported in `S` into all sections. -/
def supportedSectionsι (S : Closeds X) : supportedSections A S ⟶ 𝟭 _ :=
  kernel.ι _

@[reassoc (attr := simp)]
theorem supportedSectionsι_comp_complRestriction (S : Closeds X) :
    supportedSectionsι A S ≫ complRestriction A S = 0 :=
  kernel.condition _

@[reassoc (attr := simp)]
theorem supportedSectionsι_app_comp_complRestriction_app (S : Closeds X)
    (P : (Opens X)ᵒᵖ ⥤ A) :
    (supportedSectionsι A S).app P ≫ (complRestriction A S).app P = 0 := by
  rw [← NatTrans.comp_app, supportedSectionsι_comp_complRestriction, NatTrans.app_zero]

@[reassoc (attr := simp)]
theorem supportedSectionsι_app_app_comp_map (S : Closeds X) (P : (Opens X)ᵒᵖ ⥤ A)
    (W : Opens X) :
    ((supportedSectionsι A S).app P).app (op W) ≫
      P.map (S.complInclusion W).op = 0 := by
  have := congr_app
    (congr_app (supportedSectionsι_comp_complRestriction (A := A) S) P) (op W)
  simp only [NatTrans.comp_app, complRestriction_app_app, NatTrans.app_zero] at this
  exact this

/-- The presheaf of sections of `P` supported in `S` is the kernel of the restriction of `P` to
the complements `W ∖ S`. -/
def isLimitSupportedSectionsObj (S : Closeds X) (P : (Opens X)ᵒᵖ ⥤ A) :
    IsLimit (KernelFork.ofι _ (supportedSectionsι_app_comp_complRestriction_app S P)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (complRestriction A S))
    ((evaluation _ ((Opens X)ᵒᵖ ⥤ A)).obj P)

/-- The sections over `W` supported in `S` are the kernel of the restriction from `W` to
`W ∖ S`. -/
def isLimitSupportedSectionsObjObj (S : Closeds X) (P : (Opens X)ᵒᵖ ⥤ A) (W : Opens X) :
    IsLimit (KernelFork.ofι _ (supportedSectionsι_app_app_comp_map S P W)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (complRestriction A S))
    ((evaluation _ ((Opens X)ᵒᵖ ⥤ A)).obj P ⋙ (evaluation _ A).obj (op W))

variable (S : Closeds X) (P : (Opens X)ᵒᵖ ⥤ A) (W : Opens X)

/-- The sections over `W` supported in `S` are the kernel of the restriction from `W` to
`W ∖ S`. -/
def supportedSectionsObjObjIso :
    ((supportedSections A S).obj P).obj (op W) ≅
      kernel (P.map (S.complInclusion W).op) :=
  (isLimitSupportedSectionsObjObj S P W).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
theorem supportedSectionsObjObjIso_hom_ι :
    (supportedSectionsObjObjIso S P W).hom ≫ kernel.ι _ =
      ((supportedSectionsι A S).app P).app (op W) :=
  (isLimitSupportedSectionsObjObj S P W).conePointUniqueUpToIso_hom_comp (limit.isLimit _)
    WalkingParallelPair.zero

instance : Mono (supportedSectionsι A S) :=
  inferInstanceAs (Mono (kernel.ι _))

instance : Mono (((supportedSectionsι A S).app P).app (op W)) := by
  rw [← supportedSectionsObjObjIso_hom_ι]
  infer_instance

/-- **Sections over an open disjoint from the support vanish.** -/
theorem isZero_supportedSections_obj_obj (hW : Disjoint (W : Set X) S) :
    IsZero (((supportedSections A S).obj P).obj (op W)) := by
  have hle : W ≤ W ⊓ S.compl := le_inf le_rfl fun x hx hxS ↦ hW.ne_of_mem hx hxS rfl
  have : IsIso (S.complInclusion W) :=
    (iso_of_both_ways _ (homOfLE hle)).isIso_hom
  exact (isZero_kernel_of_mono _).of_iso (supportedSectionsObjObjIso S P W)

/-- **Sections over an open contained in the support are unrestricted**, when the presheaf
vanishes on the empty set: the inclusion of the sections supported in `S` is then an isomorphism
over every open `W ⊆ S`. -/
theorem isIso_supportedSectionsι_app_app (hW : (W : Set X) ⊆ S)
    (hP : IsZero (P.obj (op ⊥))) :
    IsIso (((supportedSectionsι A S).app P).app (op W)) := by
  have hbot : W ⊓ S.compl = ⊥ :=
    le_bot_iff.1 fun x hx ↦ hx.2 (hW hx.1)
  have hz : IsZero (P.obj (op (W ⊓ S.compl))) :=
    hP.of_iso (P.mapIso (eqToIso (congrArg op hbot)))
  exact KernelFork.IsLimit.isIso_ι _ (isLimitSupportedSectionsObjObj S P W) (hz.eq_of_tgt _ _)

/-- Supports in the empty set: no section is supported in `∅`. -/
theorem isZero_supportedSections_bot_obj : IsZero ((supportedSections A ⊥).obj P) :=
  Functor.isZero _ fun W ↦ isZero_supportedSections_obj_obj ⊥ P W.unop (by simp)

/-- Supports in the whole space: every section of a presheaf vanishing on the empty set is
supported in `X`. -/
theorem isIso_supportedSectionsι_top_app (hP : IsZero (P.obj (op ⊥))) :
    IsIso ((supportedSectionsι A ⊤).app P) :=
  have := fun W : (Opens X)ᵒᵖ ↦ isIso_supportedSectionsι_app_app ⊤ P W.unop (by simp) hP
  NatIso.isIso_of_isIso_app _

variable {S} in
variable (A) in
/-- **Support enlargement.** For closed subsets `S ≤ S'`, a section supported in `S` is supported
in `S'`. -/
def supportedSectionsMap {S' : Closeds X} (h : S ≤ S') :
    supportedSections A S ⟶ supportedSections A S' :=
  kernel.lift _ (supportedSectionsι A S) (by
    rw [← complRestriction_comp_complRestrictionMap h,
      supportedSectionsι_comp_complRestriction_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem supportedSectionsMap_comp_supportedSectionsι {S S' : Closeds X} (h : S ≤ S') :
    supportedSectionsMap A h ≫ supportedSectionsι A S' = supportedSectionsι A S :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
theorem supportedSectionsMap_app_app_comp_supportedSectionsι_app_app {S S' : Closeds X}
    (h : S ≤ S') (P : (Opens X)ᵒᵖ ⥤ A) (W : (Opens X)ᵒᵖ) :
    ((supportedSectionsMap A h).app P).app W ≫ ((supportedSectionsι A S').app P).app W =
      ((supportedSectionsι A S).app P).app W :=
  congr_app (congr_app (supportedSectionsMap_comp_supportedSectionsι h) P) W

variable (A) in
/-- The presheaves of sections with supports, as a functor of the closed support, whose maps are
the support enlargements. -/
@[expose, simps]
def supportedSectionsClosedsFunctor : Closeds X ⥤ ((Opens X)ᵒᵖ ⥤ A) ⥤ (Opens X)ᵒᵖ ⥤ A where
  obj := supportedSections A
  map f := supportedSectionsMap A (leOfHom f)
  map_id S := by simp [← cancel_mono (supportedSectionsι A S)]
  map_comp {_ _ S''} _ _ := by simp [← cancel_mono (supportedSectionsι A S'')]

end Supported

/-! ### Sheaves -/

section

variable [Preadditive A] [HasKernels A]

attribute [local instance] Preadditive.hasEqualizers_of_hasKernels

/-- The sections of a sheaf supported in a closed subset form a sheaf. -/
theorem isSheaf_supportedSections_obj {F : (Opens X)ᵒᵖ ⥤ A}
    (hF : Presheaf.IsSheaf (Opens.grothendieckTopology X) F) (S : Closeds X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) ((supportedSections A S).obj F) := by
  let f : (⟨F, hF⟩ : Sheaf (Opens.grothendieckTopology X) A) ⟶
      ⟨_, TopCat.Presheaf.isSheaf_infFunctor_op_comp hF S.compl⟩ :=
    ⟨(complRestriction A S).app F⟩
  refine (Presheaf.isSheaf_of_iso_iff ((isLimitSupportedSectionsObj S F).conePointUniqueUpToIso
    (limit.isLimit _) ≪≫ (PreservesKernel.iso (sheafToPresheaf _ A) f).symm)).2 (kernel f).property

end

section Cohomology

variable [Preadditive A] [HasKernels A] [HasProducts.{u} A] [CategoryWithHomology A]
  [HasColimitsOfShape (PointOpenCover X) A] (n : ℕ)

attribute [local instance] Preadditive.hasEqualizers_of_hasKernels

variable (X A) in
/-- The degree `n` Čech cohomology `Hⁿ_S(X; P)` with supports in a closed subset `S`: the Čech
cohomology of the presheaf of sections supported in `S`, as a functor of `S` (by support
enlargement) and of the presheaf. -/
@[expose]
def supportedCechCohomology : Closeds X ⥤ ((Opens X)ᵒᵖ ⥤ A) ⥤ A :=
  supportedSectionsClosedsFunctor A ⋙ (Functor.whiskeringRight _ _ _).obj (cechCohomology X A n)

@[simp]
theorem supportedCechCohomology_obj (S : Closeds X) :
    (supportedCechCohomology X A n).obj S = supportedSections A S ⋙ cechCohomology X A n :=
  (rfl)

@[simp]
theorem supportedCechCohomology_map {S S' : Closeds X} (f : S ⟶ S') :
    (supportedCechCohomology X A n).map f =
      Functor.whiskerRight (supportedSectionsMap A (leOfHom f)) (cechCohomology X A n) :=
  (rfl)

/-- There is no cohomology with supports in the empty set. -/
theorem isZero_supportedCechCohomology_obj_bot_obj (P : (Opens X)ᵒᵖ ⥤ A) :
    IsZero (((supportedCechCohomology X A n).obj ⊥).obj P) :=
  isZero_cechCohomology_obj_of_isZero X A n _ fun W ↦
    isZero_supportedSections_obj_obj ⊥ P W.unop (by simp)

variable (X A) in
/-- Forgetting supports: the map `Hⁿ_S(X; P) ⟶ Hⁿ(X; P)` induced by the inclusion of the
sections supported in `S`, compatible with support enlargement. -/
@[expose, simps!]
def supportedCechCohomologyToCech :
    supportedCechCohomology X A n ⟶ (Functor.const _).obj (cechCohomology X A n) where
  app S :=
    { app P := (cechCohomology X A n).map ((supportedSectionsι A S).app P)
      naturality P Q α := by
        have := congrArg (cechCohomology X A n).map ((supportedSectionsι A S).naturality α)
        simp only [Functor.map_comp, Functor.id_map] at this
        exact this }
  naturality S S' f := by
    -- the constant functor sends `f` to the identity
    rw [Functor.const_obj_map]
    refine Eq.trans ?_ (Category.comp_id _).symm
    ext P
    -- the component at `P` of the left side is `Hⁿ` applied to a composite, by
    -- `NatTrans.comp_app`, `supportedCechCohomology_map` and `Functor.whiskerRight_app` (all `rfl`)
    exact ((cechCohomology X A n).map_comp _ _).symm.trans
      (congrArg _ (congr_app (supportedSectionsMap_comp_supportedSectionsι (leOfHom f)) P))

/-- Cohomology with supports in the whole space is ordinary Čech cohomology, for presheaves
vanishing on the empty set. -/
theorem isIso_supportedCechCohomologyToCech_app_top_app (P : (Opens X)ᵒᵖ ⥤ A)
    (hP : IsZero (P.obj (op ⊥))) :
    IsIso (((supportedCechCohomologyToCech X A n).app ⊤).app P) := by
  have := isIso_supportedSectionsι_top_app P hP
  rw [supportedCechCohomologyToCech_app_app]
  exact Functor.map_isIso _ _

section ZeroIso

variable [HasZeroObject A] (F : Sheaf (Opens.grothendieckTopology X) A) (S : Closeds X)

/-- **Degree zero.** For a sheaf `F`, the Čech cohomology with supports in `S` in degree `0` is
the group of global sections supported in `S`, `H⁰_S(X; F) ≅ ker (F(X) ⟶ F(X ∖ S))`. -/
def supportedCechCohomologyZeroIso :
    ((supportedCechCohomology X A 0).obj S).obj F.obj ≅
      kernel (F.obj.map (S.complInclusion ⊤).op) :=
  ((cechCohomologyZeroIso ⟨_, isSheaf_supportedSections_obj F.property S⟩).symm ≪≫
    supportedSectionsObjObjIso S F.obj ⊤ :)

/-- In degree `0`, forgetting supports is the inclusion of the global sections supported in `S`
into all global sections. -/
@[reassoc]
theorem supportedCechCohomologyZeroIso_inv_comp_supportedCechCohomologyToCech_app_app :
    (supportedCechCohomologyZeroIso F S).inv ≫
        ((supportedCechCohomologyToCech X A 0).app S).app F.obj =
      kernel.ι _ ≫ (cechCohomologyZeroIso F).hom := by
  have h := cechCohomologyZeroIso_hom_naturality
    ⟨_, isSheaf_supportedSections_obj F.property S⟩ (G := F)
    ⟨(supportedSectionsι A S).app F.obj⟩
  dsimp only at h
  simp only [supportedCechCohomologyZeroIso, Iso.trans_inv, Iso.symm_inv,
    supportedCechCohomologyToCech_app_app]
  -- reassociate, writing the middle object `H⁰_S(X; F)` as `H⁰(X; Γ_S F)`, as `h` does
  calc _ = (supportedSectionsObjObjIso S F.obj ⊤).inv ≫
        ((cechCohomologyZeroIso ⟨_, isSheaf_supportedSections_obj F.property S⟩).hom ≫
          (cechCohomology X A 0).map ((supportedSectionsι A S).app F.obj)) :=
        Category.assoc _ _ _
    _ = _ := by rw [← h, ← supportedSectionsObjObjIso_hom_ι_assoc, Iso.inv_hom_id_assoc]

end ZeroIso

/-! ### Compact supports -/

variable [T2Space X] [HasColimitsOfShape (Compacts X) A]

variable (X A) in
/-- The degree `n` Čech cohomology `Hⁿ_c(X; P)` with compact supports: the colimit, over the
compact subsets `K` of `X` ordered by inclusion, of the Čech cohomologies `Hⁿ_K(X; P)` with
supports in `K`, along the support enlargements. -/
def compactSupportCechCohomology : ((Opens X)ᵒᵖ ⥤ A) ⥤ A :=
  (Compacts.toClosedsFunctor X ⋙ supportedCechCohomology X A n).flip ⋙ colim

variable (X A) in
/-- The structure map `Hⁿ_K(X; P) ⟶ Hⁿ_c(X; P)` for a compact subset `K`, natural in `P`. -/
def compactSupportCechCohomologyι (K : Compacts X) :
    (supportedCechCohomology X A n).obj K.toCloseds ⟶ compactSupportCechCohomology X A n where
  app P := colimit.ι ((Compacts.toClosedsFunctor X ⋙ supportedCechCohomology X A n).flip.obj P) K
  naturality _ _ α := (colimit.ι_map
    ((Compacts.toClosedsFunctor X ⋙ supportedCechCohomology X A n).flip.map α) K).symm

@[reassoc]
theorem supportedCechCohomology_map_comp_compactSupportCechCohomologyι {K K' : Compacts X}
    (f : K ⟶ K') :
    (supportedCechCohomology X A n).map ((Compacts.toClosedsFunctor X).map f) ≫
        compactSupportCechCohomologyι X A n K' =
      compactSupportCechCohomologyι X A n K := by
  ext P
  exact colimit.w ((Compacts.toClosedsFunctor X ⋙ supportedCechCohomology X A n).flip.obj P) f

@[reassoc]
theorem supportedCechCohomology_map_app_comp_compactSupportCechCohomologyι_app {K K' : Compacts X}
    (f : K ⟶ K') (P : (Opens X)ᵒᵖ ⥤ A) :
    ((supportedCechCohomology X A n).map ((Compacts.toClosedsFunctor X).map f)).app P ≫
        (compactSupportCechCohomologyι X A n K').app P =
      (compactSupportCechCohomologyι X A n K).app P :=
  congr_app (supportedCechCohomology_map_comp_compactSupportCechCohomologyι n f) P

variable (X A) in
/-- A map out of `Hⁿ_c(X; P)`, induced by maps out of the `Hⁿ_K(X; P)` for the compact subsets `K`
that are compatible with the support enlargements. -/
def compactSupportCechCohomologyDesc {P : (Opens X)ᵒᵖ ⥤ A} {Y : A}
    (f : ∀ K : Compacts X, ((supportedCechCohomology X A n).obj K.toCloseds).obj P ⟶ Y)
    (hf : ∀ ⦃K K' : Compacts X⦄ (h : K ⟶ K'),
      ((supportedCechCohomology X A n).map ((Compacts.toClosedsFunctor X).map h)).app P ≫ f K' =
        f K) :
    (compactSupportCechCohomology X A n).obj P ⟶ Y :=
  colimit.desc _ ⟨Y, { app := f, naturality _ _ h := (hf h).trans (Category.comp_id _).symm }⟩

@[reassoc (attr := simp)]
theorem compactSupportCechCohomologyι_app_comp_compactSupportCechCohomologyDesc
    {P : (Opens X)ᵒᵖ ⥤ A} {Y : A}
    (f : ∀ K : Compacts X, ((supportedCechCohomology X A n).obj K.toCloseds).obj P ⟶ Y)
    (hf : ∀ ⦃K K' : Compacts X⦄ (h : K ⟶ K'),
      ((supportedCechCohomology X A n).map ((Compacts.toClosedsFunctor X).map h)).app P ≫ f K' =
        f K) (K : Compacts X) :
    (compactSupportCechCohomologyι X A n K).app P ≫ compactSupportCechCohomologyDesc X A n f hf =
      f K :=
  colimit.ι_desc _ _

/-- Two maps out of `Hⁿ_c(X; P)` agree as soon as they agree on `Hⁿ_K(X; P)` for every compact
subset `K`. -/
theorem compactSupportCechCohomology_hom_ext {P : (Opens X)ᵒᵖ ⥤ A} {Y : A}
    {f g : (compactSupportCechCohomology X A n).obj P ⟶ Y}
    (h : ∀ K : Compacts X, (compactSupportCechCohomologyι X A n K).app P ≫ f =
      (compactSupportCechCohomologyι X A n K).app P ≫ g) : f = g :=
  colimit.hom_ext h

variable (X A) in
/-- Forgetting compact supports: the map `Hⁿ_c(X; P) ⟶ Hⁿ(X; P)` induced by the maps forgetting
the supports `K`. -/
def compactSupportCechCohomologyToCech :
    compactSupportCechCohomology X A n ⟶ cechCohomology X A n where
  app P := colimit.desc _
    { pt := (cechCohomology X A n).obj P
      ι :=
        { app K := ((supportedCechCohomologyToCech X A n).app K.toCloseds).app P
          naturality K K' f := by
            have := congr_app ((supportedCechCohomologyToCech X A n).naturality
              ((Compacts.toClosedsFunctor X).map f)) P
            simp only [NatTrans.comp_app, Functor.const_obj_map, NatTrans.id_app,
              supportedCechCohomologyToCech_app_app] at this ⊢
            exact this } }
  naturality P Q α := by
    dsimp only [compactSupportCechCohomology, Functor.comp_obj, Functor.comp_map, colim_obj,
      colim_map]
    refine colimit.hom_ext fun K ↦ ?_
    rw [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact ((supportedCechCohomologyToCech X A n).app K.toCloseds).naturality α

@[reassoc (attr := simp)]
theorem compactSupportCechCohomologyι_app_comp_compactSupportCechCohomologyToCech_app
    (K : Compacts X) (P : (Opens X)ᵒᵖ ⥤ A) :
    (compactSupportCechCohomologyι X A n K).app P ≫
        (compactSupportCechCohomologyToCech X A n).app P =
      ((supportedCechCohomologyToCech X A n).app K.toCloseds).app P :=
  colimit.ι_desc _ _

/-- **On a compact space, compact supports are no restriction**: for a presheaf vanishing on the
empty set, such as a sheaf, forgetting compact supports is an isomorphism
`Hⁿ_c(X; P) ≅ Hⁿ(X; P)`. The whole space is the largest compact subset, so the colimit defining
`Hⁿ_c(X; P)` is `Hⁿ_X(X; P)`, and every section is supported in `X`. -/
theorem isIso_compactSupportCechCohomologyToCech_app [CompactSpace X] (P : (Opens X)ᵒᵖ ⥤ A)
    (hP : IsZero (P.obj (op ⊥))) : IsIso ((compactSupportCechCohomologyToCech X A n).app P) := by
  have : IsIso ((compactSupportCechCohomologyι X A n ⊤).app P) :=
    isIso_ι_of_isTerminal isTerminalTop _
  have : IsIso ((compactSupportCechCohomologyι X A n ⊤).app P ≫
      (compactSupportCechCohomologyToCech X A n).app P) := by
    rw [compactSupportCechCohomologyι_app_comp_compactSupportCechCohomologyToCech_app,
      Compacts.toCloseds_top]
    exact isIso_supportedCechCohomologyToCech_app_top_app n P hP
  exact IsIso.of_isIso_comp_left ((compactSupportCechCohomologyι X A n ⊤).app P) _

/-- On a compact space, the Čech cohomology of a sheaf with compact supports is its Čech
cohomology. -/
theorem isIso_compactSupportCechCohomologyToCech_app_sheaf [CompactSpace X]
    (F : TopCat.Sheaf A X) :
    IsIso ((compactSupportCechCohomologyToCech X A n).app F.obj) :=
  isIso_compactSupportCechCohomologyToCech_app n F.obj
    ((IsZero.iff_id_eq_zero _).2 (F.isTerminalOfEmpty.hom_ext _ _))

end Cohomology

end TauCeti.Topology
