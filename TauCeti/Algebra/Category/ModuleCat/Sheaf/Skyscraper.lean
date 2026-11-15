/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
import Mathlib.Algebra.Module.Pi
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Skyscraper sheaves of modules at a point

Constructs `SheafOfModules.skyscraper` and `skyscraperCommRing`, proves the stalk-Hom adjunctions
`skyscraperHomEquiv` and `skyscraperCommRingHomEquiv`, and identifies pushforwards (Tag 0098).
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
open TauCeti.SheafOfModules (ringCatSheaf)
universe u
noncomputable section
namespace SheafOfModules
variable {X : TopCat.{u}}
private abbrev SkyscraperIndex (x : X) (U : Opens X) : Type u := ULift.{u} (PLift (x ∈ U))
private def skyscraperAddPresheaf (x : X) (T : Type u) [AddCommGroup T] :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (SkyscraperIndex x U.unop → T)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s k ↦ s ⟨⟨i.unop.le k.down.down⟩⟩, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  map_id _ := AddCommGrpCat.ext fun _ ↦ funext fun ⟨⟨_⟩⟩ ↦ rfl
  map_comp _ _ := AddCommGrpCat.ext fun _ ↦ funext fun ⟨⟨_⟩⟩ ↦ rfl
private theorem isSheaf_skyscraperAddPresheaf (x : X) (T : Type u) [AddCommGroup T] :
    TopCat.Presheaf.IsSheaf (skyscraperAddPresheaf x T) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  refine fun ι U sf hcompat ↦ ⟨fun k ↦ sf (Classical.choose (Opens.mem_iSup.mp k.down.down))
    ⟨⟨Classical.choose_spec (Opens.mem_iSup.mp k.down.down)⟩⟩, fun j ↦ ?_, fun t ht ↦ ?_⟩
  · funext ⟨⟨hxj⟩⟩
    exact congrFun (hcompat _ j)
      ⟨⟨⟨Classical.choose_spec (Opens.mem_iSup.mp ((Opens.leSupr U j).le hxj)), hxj⟩⟩⟩
  · exact funext fun ⟨⟨hx⟩⟩ ↦ congrFun (ht _) ⟨⟨Classical.choose_spec (Opens.mem_iSup.mp hx)⟩⟩
section RingCat
variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)
  (T : Type u) [AddCommGroup T] [Module ↑(stalk R.obj x) T]
@[instance_reducible] private def skyscraperModule (U : (Opens X)ᵒᵖ) :
    Module (R.obj.obj U) ((skyscraperAddPresheaf x T).obj U) :=
  letI : SkyscraperIndex x U.unop → Module (R.obj.obj U) T :=
    fun k ↦ Module.compHom T (germ R.obj U.unop x k.down.down).hom
  inferInstanceAs (Module (R.obj.obj U) (SkyscraperIndex x U.unop → T))

/-- The skyscraper sheaf of `R`-modules at `x` with fiber `T`. -/
def skyscraper : SheafOfModules.{u} R where
  val :=
    letI := skyscraperModule R x T
    PresheafOfModules.ofPresheaf (skyscraperAddPresheaf x T) fun {_ _} i r s ↦
      funext fun k ↦ congrArg (· • s ⟨⟨i.unop.le k.down.down⟩⟩)
        (germ_res_apply R.obj i.unop x k.down.down r).symm
  isSheaf := isSheaf_skyscraperAddPresheaf x T

/-- Evaluation of sections of `skyscraper R x T` over an open set `U` containing `x`. -/
def skyscraperEval {U : Opens X} (hx : x ∈ U) :
    ((skyscraper R x T).val.obj (op U) : Type u) →+ T :=
  { toFun := fun s ↦ s ⟨⟨hx⟩⟩, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
@[simp] theorem skyscraperEval_smul {U : Opens X} (hx : x ∈ U) (r : R.obj.obj (op U))
    (s : (skyscraper R x T).val.obj (op U)) :
    skyscraperEval R x T hx (r • s) = germ R.obj U x hx r • skyscraperEval R x T hx s := (rfl)
@[simp] theorem skyscraperEval_map {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (s : (skyscraper R x T).val.obj (op V)) :
    skyscraperEval R x T hx ((skyscraper R x T).val.map i.op s) =
      skyscraperEval R x T (i.le hx) s := (rfl)

/-- Over an open set not containing `x`, `skyscraper R x T` has trivial sections. -/
theorem subsingleton_skyscraper_obj {U : Opens X} (hx : x ∉ U) :
    Subsingleton ((skyscraper R x T).val.obj (op U)) :=
  ⟨fun _ _ ↦ funext fun k ↦ False.elim (hx k.down.down)⟩
@[ext] theorem skyscraper_section_ext {U : Opens X} {s t : (skyscraper R x T).val.obj (op U)}
    (h : ∀ hx : x ∈ U, skyscraperEval R x T hx s = skyscraperEval R x T hx t) : s = t :=
  funext fun k ↦ h k.down.down
private def toSkyscraperAddNatTrans {M : SheafOfModules.{u} R}
    (α : ↑(stalk M.val.presheaf x) →ₗ[↑(stalk R.obj x)] T) :
    M.val.presheaf ⟶ (skyscraper R x T).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun m k ↦ α (germ M.val.presheaf U.unop x k.down.down m)
      map_zero' := funext fun k ↦ (congrArg α (map_zero (germ M.val.presheaf U.unop x
        k.down.down).hom)).trans (map_zero α)
      map_add' := fun a b ↦ funext fun k ↦ (congrArg α (map_add (germ M.val.presheaf U.unop x
        k.down.down).hom a b)).trans (map_add α _ _) }
  naturality {_ _} i := AddCommGrpCat.ext fun m ↦ funext fun ⟨⟨hx⟩⟩ ↦
    congrArg α (germ_res_apply M.val.presheaf i.unop x hx m)
private def toSkyscraper {M : SheafOfModules.{u} R}
    (α : ↑(stalk M.val.presheaf x) →ₗ[↑(stalk R.obj x)] T) : M ⟶ skyscraper R x T where
  val := PresheafOfModules.homMk (toSkyscraperAddNatTrans R x T α) fun U r m ↦ funext fun k ↦
    (congrArg α (M.val.germ_ringCat_smul (R := R.obj) x U.unop k.down.down r m)).trans
      (α.map_smul (germ R.obj U.unop x k.down.down r) _)
private theorem fromSkyscraper_res {M : SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T)
    {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : M.val.obj (op V)) :
    (skyscraperEval R x T hx).comp (φ.val.app (op U)).hom.toAddMonoidHom (M.val.map i.op m) =
      (skyscraperEval R x T (i.le hx)).comp (φ.val.app (op V)).hom.toAddMonoidHom m :=
  (congrArg (skyscraperEval R x T hx) (PresheafOfModules.naturality_apply φ.val i.op m)).trans
    (skyscraperEval_map R x T i hx (φ.val.app _ m))
private def fromSkyscraper {M : SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T) :
    ↑(stalk M.val.presheaf x) →ₗ[↑(stalk R.obj x)] T :=
  M.val.stalkLift (R := R.obj) x
    (fun U hx ↦ (skyscraperEval R x T hx).comp (φ.val.app (op U)).hom.toAddMonoidHom)
    (fromSkyscraper_res R x T φ)
    (fun U hx r m ↦ (congrArg (skyscraperEval R x T hx)
      ((φ.val.app (op U)).hom.map_smul r m)).trans (skyscraperEval_smul R x T hx r _))
private theorem fromSkyscraper_germ {M : SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (fromSkyscraper R x T φ (germ M.val.presheaf U x hx m) =
      skyscraperEval R x T hx (φ.val.app (op U) m)) := by
  unfold fromSkyscraper; apply PresheafOfModules.stalkLift_germ

/-- Morphisms `M ⟶ skyscraper R x T` correspond additively to `R_x`-linear maps `M_x →ₗ[R_x] T`. -/
def skyscraperHomEquiv (M : SheafOfModules.{u} R) :
    (M ⟶ skyscraper R x T) ≃+ (↑(stalk M.val.presheaf x) →ₗ[↑(stalk R.obj x)] T) where
  toFun := fromSkyscraper R x T
  invFun := toSkyscraper R x T
  left_inv φ := by ext ⟨U⟩ m hx; exact fromSkyscraper_germ R x T φ U hx m
  right_inv α := LinearMap.ext fun s ↦ by
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq M.val.presheaf s
    exact fromSkyscraper_germ R x T (toSkyscraper R x T α) U hx m
  map_add' φ ψ := LinearMap.ext fun s ↦ by
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq M.val.presheaf s
    exact (fromSkyscraper_germ R x T (φ + ψ) U hx m).trans
      (congrArg₂ (· + ·) (fromSkyscraper_germ R x T φ U hx m).symm
        (fromSkyscraper_germ R x T ψ U hx m).symm)
@[simp] theorem skyscraperHomEquiv_germ {M : SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperHomEquiv R x T M φ (germ M.val.presheaf U x hx m) =
      skyscraperEval R x T hx (φ.val.app (op U) m)) :=
  fromSkyscraper_germ R x T φ U hx m
@[simp] theorem skyscraperEval_skyscraperHomEquiv_symm_app {M : SheafOfModules.{u} R}
    (α : ↑(stalk M.val.presheaf x) →ₗ[↑(stalk R.obj x)] T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperEval R x T hx (((skyscraperHomEquiv R x T M).symm α).val.app (op U) m) =
      α (germ M.val.presheaf U x hx m)) := (rfl)
end RingCat
section PushforwardRingCat
variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {Y : TopCat.{u}} (f : Y ⟶ X)
  (R' : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  (φ : R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj R')
  (y : Y) (ρ : stalk R.obj (f y) ⟶ stalk R'.obj y)
  (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : R.obj.obj (op U)),
    ρ (germ R.obj U (f y) hy r) = germ R'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
  (T' : Type u) [AddCommGroup T'] [Module ↑(stalk R'.obj y) T']

/-- Pushforward of `skyscraper R' y T'` along `(f, φ)` is `skyscraper R (f y) T'` along `ρ`. -/
def pushforwardSkyscraperIso :
    letI : Module ↑(stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
    (pushforward.{u} φ).obj (skyscraper R' y T') ≅ skyscraper R (f y) T' :=
  letI : Module ↑(stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
  { hom.val := PresheafOfModules.homMk (𝟙 _) fun U r s ↦
      funext fun k ↦ congrArg (· • s k) (hρ U.unop k.down.down r).symm
    inv.val := PresheafOfModules.homMk (𝟙 _) fun U r s ↦
      funext fun k ↦ congrArg (· • s k) (hρ U.unop k.down.down r)
    hom_inv_id := by ext _ _; rfl
    inv_hom_id := by ext _ _; rfl }
@[simp] theorem skyscraperEval_pushforwardSkyscraperIso_hom_app (U : Opens X) (hy : f y ∈ U)
    (s : ((pushforward.{u} φ).obj (skyscraper R' y T')).val.obj (op U)) :
    letI : Module ↑(stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
    skyscraperEval R (f y) T' hy
        ((pushforwardSkyscraperIso R f R' φ y ρ hρ T').hom.val.app (op U) s) =
      skyscraperEval R' y T' hy s := (rfl)
@[simp] theorem skyscraperEval_pushforwardSkyscraperIso_inv_app (U : Opens X) (hy : f y ∈ U) :
    letI : Module ↑(stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
    ∀ s : (skyscraper R (f y) T').val.obj (op U),
      skyscraperEval R' y T' hy
          ((pushforwardSkyscraperIso R f R' φ y ρ hρ T').inv.val.app (op U) s) =
        skyscraperEval R (f y) T' hy s := fun _ ↦ (rfl)
end PushforwardRingCat
private def ringCatStalkToCommRingStalk (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) : stalk (ringCatSheaf S).obj x ⟶ RingCat.of ↑(stalk S.obj x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (ringCatSheaf S).obj)
    ((forget₂ CommRingCat.{u} RingCat.{u}).mapCocone
      (colimit.cocone ((OpenNhds.inclusion x).op ⋙ S.obj)))
private theorem ringCatStalkToCommRingStalk_germ
    (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X) (U : Opens X) (hx : x ∈ U)
    (r : S.obj.obj (op U)) :
    ringCatStalkToCommRingStalk S x (germ (ringCatSheaf S).obj U x hx r) = germ S.obj U x hx r :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ (ringCatSheaf S).obj)
      ((forget₂ CommRingCat.{u} RingCat.{u}).mapCocone
        (colimit.cocone ((OpenNhds.inclusion x).op ⋙ S.obj))) (op ⟨U, hx⟩)) r
section CommRingCat
variable (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)
  (T : Type u) [AddCommGroup T] [Module ↑(stalk S.obj x) T]

/-- The skyscraper sheaf of modules over a sheaf of commutative rings `S` at `x` with fiber `T`. -/
def skyscraperCommRing : SheafOfModules.{u} (ringCatSheaf S) :=
  letI : Module ↑(stalk (ringCatSheaf S).obj x) T :=
    Module.compHom T (ringCatStalkToCommRingStalk S x).hom
  skyscraper (ringCatSheaf S) x T

/-- Evaluation of sections of `skyscraperCommRing S x T` over an open `U` containing `x`. -/
def skyscraperCommRingEval {U : Opens X} (hx : x ∈ U) :
    ((skyscraperCommRing S x T).val.obj (op U) : Type u) →+ T :=
  letI : Module ↑(stalk (ringCatSheaf S).obj x) T :=
    Module.compHom T (ringCatStalkToCommRingStalk S x).hom
  skyscraperEval (ringCatSheaf S) x T hx
@[simp] theorem skyscraperCommRingEval_smul {U : Opens X} (hx : x ∈ U) (r : S.obj.obj (op U))
    (s : (skyscraperCommRing S x T).val.obj (op U)) :
    skyscraperCommRingEval S x T hx (r • s) =
      germ S.obj U x hx r • skyscraperCommRingEval S x T hx s := by
  let _ : Module ↑(stalk (ringCatSheaf S).obj x) T :=
    Module.compHom T (ringCatStalkToCommRingStalk S x).hom
  exact (skyscraperEval_smul (ringCatSheaf S) x T hx r s).trans
    (congrArg (· • skyscraperCommRingEval S x T hx s) (ringCatStalkToCommRingStalk_germ S x U hx r))
@[simp] theorem skyscraperCommRingEval_map {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (s : (skyscraperCommRing S x T).val.obj (op V)) :
    skyscraperCommRingEval S x T hx ((skyscraperCommRing S x T).val.map i.op s) =
      skyscraperCommRingEval S x T (i.le hx) s := (rfl)
@[ext] theorem skyscraperCommRing_section_ext {U : Opens X}
    {s t : (skyscraperCommRing S x T).val.obj (op U)}
    (h : ∀ hx : x ∈ U, skyscraperCommRingEval S x T hx s = skyscraperCommRingEval S x T hx t) :
    s = t := funext fun k ↦ h k.down.down
private def toSkyscraperCommRingAddNatTrans {M : SheafOfModules.{u} (ringCatSheaf S)}
    (α : ↑(stalk M.val.presheaf x) →ₗ[↑(stalk S.obj x)] T) :
    M.val.presheaf ⟶ (skyscraperCommRing S x T).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun m k ↦ α (germ M.val.presheaf U.unop x k.down.down m)
      map_zero' := funext fun k ↦ (congrArg α (map_zero (germ M.val.presheaf U.unop x
        k.down.down).hom)).trans (map_zero α)
      map_add' := fun a b ↦ funext fun k ↦ (congrArg α (map_add (germ M.val.presheaf U.unop x
        k.down.down).hom a b)).trans (map_add α _ _) }
  naturality {_ _} i := AddCommGrpCat.ext fun m ↦ funext fun ⟨⟨hx⟩⟩ ↦
    congrArg α (germ_res_apply M.val.presheaf i.unop x hx m)
private def toSkyscraperCommRing {M : SheafOfModules.{u} (ringCatSheaf S)}
    (α : ↑(stalk M.val.presheaf x) →ₗ[↑(stalk S.obj x)] T) : M ⟶ skyscraperCommRing S x T where
  val := PresheafOfModules.homMk (toSkyscraperCommRingAddNatTrans S x T α) fun U r m ↦
    funext fun k ↦ (congrArg α (M.val.germ_smul (R := S.obj) x U.unop k.down.down r m)).trans
      ((α.map_smul (germ S.obj U.unop x k.down.down r) _).trans
        (congrArg (· • α (germ M.val.presheaf U.unop x k.down.down m))
          (ringCatStalkToCommRingStalk_germ S x U.unop k.down.down r).symm))
private theorem fromSkyscraperCommRing_res {M : SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (m : M.val.obj (op V)) :
    (skyscraperCommRingEval S x T hx).comp (φ.val.app (op U)).hom.toAddMonoidHom
        (M.val.map i.op m) =
      (skyscraperCommRingEval S x T (i.le hx)).comp (φ.val.app (op V)).hom.toAddMonoidHom m :=
  (congrArg (skyscraperCommRingEval S x T hx) (PresheafOfModules.naturality_apply φ.val i.op
    m)).trans (skyscraperCommRingEval_map S x T i hx (φ.val.app _ m))
private def fromSkyscraperCommRing {M : SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) : ↑(stalk M.val.presheaf x) →ₗ[↑(stalk S.obj x)] T :=
  M.val.stalkLiftCommRing (S := S.obj) x
    (fun U hx ↦ (skyscraperCommRingEval S x T hx).comp (φ.val.app (op U)).hom.toAddMonoidHom)
    (fromSkyscraperCommRing_res S x T φ)
    (fun U hx r m ↦ (congrArg (skyscraperCommRingEval S x T hx)
      ((φ.val.app (op U)).hom.map_smul r m)).trans (skyscraperCommRingEval_smul S x T hx r _))
private theorem fromSkyscraperCommRing_germ {M : SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (fromSkyscraperCommRing S x T φ (germ M.val.presheaf U x hx m) =
      skyscraperCommRingEval S x T hx (φ.val.app (op U) m)) := by
  unfold fromSkyscraperCommRing; apply PresheafOfModules.stalkLiftCommRing_germ

/-- Morphisms `M ⟶ skyscraperCommRing S x T` correspond additively to `M_x →ₗ[S_x] T`. -/
def skyscraperCommRingHomEquiv (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (M ⟶ skyscraperCommRing S x T) ≃+ (↑(stalk M.val.presheaf x) →ₗ[↑(stalk S.obj x)] T) where
  toFun := fromSkyscraperCommRing S x T
  invFun := toSkyscraperCommRing S x T
  left_inv φ := by ext ⟨U⟩ m hx; exact fromSkyscraperCommRing_germ S x T φ U hx m
  right_inv α := LinearMap.ext fun s ↦ by
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq M.val.presheaf s
    exact fromSkyscraperCommRing_germ S x T (toSkyscraperCommRing S x T α) U hx m
  map_add' φ ψ := LinearMap.ext fun s ↦ by
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq M.val.presheaf s
    exact (fromSkyscraperCommRing_germ S x T (φ + ψ) U hx m).trans
      (congrArg₂ (· + ·) (fromSkyscraperCommRing_germ S x T φ U hx m).symm
        (fromSkyscraperCommRing_germ S x T ψ U hx m).symm)
@[simp] theorem skyscraperCommRingHomEquiv_germ {M : SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperCommRingHomEquiv S x T M φ (germ M.val.presheaf U x hx m) =
      skyscraperCommRingEval S x T hx (φ.val.app (op U) m)) :=
  fromSkyscraperCommRing_germ S x T φ U hx m
@[simp] theorem skyscraperCommRingEval_skyscraperCommRingHomEquiv_symm_app
    {M : SheafOfModules.{u} (ringCatSheaf S)} (α : ↑(stalk M.val.presheaf x) →ₗ[↑(stalk S.obj x)] T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperCommRingEval S x T hx
        (((skyscraperCommRingHomEquiv S x T M).symm α).val.app (op U) m) =
      α (germ M.val.presheaf U x hx m)) := (rfl)

/-- Naturality of `skyscraperCommRingHomEquiv` in the source sheaf of modules. -/
theorem skyscraperCommRingHomEquiv_comp {L M : SheafOfModules.{u} (ringCatSheaf S)}
    (f : L ⟶ M) (φ : M ⟶ skyscraperCommRing S x T) :
    skyscraperCommRingHomEquiv S x T L (f ≫ φ) =
      (skyscraperCommRingHomEquiv S x T M φ).comp (stalkMap f x) :=
  LinearMap.ext fun s ↦ by
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq L.val.presheaf s
    exact (skyscraperCommRingHomEquiv_germ S x T (f ≫ φ) U hx m).trans
      ((skyscraperCommRingHomEquiv_germ S x T φ U hx (f.val.app (op U) m)).symm.trans
        (congrArg (skyscraperCommRingHomEquiv S x T M φ) (stalkMap_germ f x U hx m).symm))
end CommRingCat
section PushforwardCommRingCat
variable (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) {Y : TopCat.{u}} (f : Y ⟶ X)
  (S' : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
  (φ : ringCatSheaf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf S'))
  (y : Y) (ρ : stalk S.obj (f y) ⟶ stalk S'.obj y)
  (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)),
    ρ (germ S.obj U (f y) hy r) = germ S'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
  (T' : Type u) [AddCommGroup T'] [Module ↑(stalk S'.obj y) T']

/-- Pushforward of `skyscraperCommRing S' y T'` along `(f, φ)` is `skyscraperCommRing S (f y) T'`
with fiber `T'` restricted along `ρ`. -/
def pushforwardSkyscraperCommRingIso :
    letI : Module ↑(stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
    (pushforward.{u} φ).obj (skyscraperCommRing S' y T') ≅ skyscraperCommRing S (f y) T' :=
  letI : Module ↑(stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
  { hom.val := PresheafOfModules.homMk (𝟙 _) fun U r s ↦ funext fun k ↦ congrArg (· • s k)
      ((ringCatStalkToCommRingStalk_germ S' y _ k.down.down _).trans
        ((hρ U.unop k.down.down r).symm.trans
          (congrArg ρ (ringCatStalkToCommRingStalk_germ S (f y) U.unop k.down.down r).symm)))
    inv.val := PresheafOfModules.homMk (𝟙 _) fun U r s ↦ funext fun k ↦ congrArg (· • s k)
      ((congrArg ρ (ringCatStalkToCommRingStalk_germ S (f y) U.unop k.down.down r)).trans
        ((hρ U.unop k.down.down r).trans
          (ringCatStalkToCommRingStalk_germ S' y _ k.down.down _).symm))
    hom_inv_id := by ext _ _; rfl
    inv_hom_id := by ext _ _; rfl }
@[simp]
theorem skyscraperCommRingEval_pushforwardSkyscraperCommRingIso_hom_app (U : Opens X) (hy : f y ∈ U)
    (s : ((pushforward.{u} φ).obj (skyscraperCommRing S' y T')).val.obj (op U)) :
    letI : Module ↑(stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
    skyscraperCommRingEval S (f y) T' hy
        ((pushforwardSkyscraperCommRingIso S f S' φ y ρ hρ T').hom.val.app (op U) s) =
      skyscraperCommRingEval S' y T' hy s := (rfl)
@[simp] theorem skyscraperCommRingEval_pushforwardSkyscraperCommRingIso_inv_app (U : Opens X)
    (hy : f y ∈ U) :
    letI : Module ↑(stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
    ∀ s : (skyscraperCommRing S (f y) T').val.obj (op U),
      skyscraperCommRingEval S' y T' hy
          ((pushforwardSkyscraperCommRingIso S f S' φ y ρ hρ T').inv.val.app (op U) s) =
        skyscraperCommRingEval S (f y) T' hy s := fun _ ↦ (rfl)
end PushforwardCommRingCat
end SheafOfModules
end
