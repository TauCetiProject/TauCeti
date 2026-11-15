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

Let `X` be a topological space, `R` a sheaf of rings on `X`, `x` a point of `X`, and `T` a module
over the ring stalk `TopCat.Presheaf.stalk R.obj x`. This file constructs the skyscraper sheaf of
modules `TauCeti.SheafOfModules.skyscraper R x T` at `x` with fiber `T` and establishes its
universal property: morphisms `M ⟶ skyscraper R x T` of sheaves of `R`-modules correspond
bijectively and additively to `TopCat.Presheaf.stalk R.obj x`-linear maps out of the stalk of `M`
at `x` (`TauCeti.SheafOfModules.skyscraperHomEquiv`), naturally in `M`.

Following the point-of-a-site formulation in `Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean`,
the sections over an open set `U` are represented as functions indexed by proofs of `x ∈ U` into
`T`, with `R(U)` acting through the ring germ `R(U) ⟶ R_x` and restriction given by restricting
the membership proof. This avoids decidability assumptions on `x ∈ U` and makes the functoriality
and pushforward laws definitional on underlying sections.

For a sheaf `S` of commutative rings, `TauCeti.SheafOfModules.skyscraperCommRing S x T` and
`TauCeti.SheafOfModules.skyscraperCommRingHomEquiv` provide the corresponding construction and
universal property directly for modules over the commutative-ring stalk
`TopCat.Presheaf.stalk S.obj x`, without changing scalar ring carrier when forgetting
commutativity, together with the pushforward identification
`TauCeti.SheafOfModules.pushforwardSkyscraperCommRingIso` along any morphism of ringed spaces.

## Main declarations

* `TauCeti.SheafOfModules.skyscraper`: the skyscraper sheaf of `R`-modules at `x` attached to a
  module `T` over `TopCat.Presheaf.stalk R.obj x`;
* `TauCeti.SheafOfModules.skyscraperEval`: evaluation of sections of `skyscraper R x T` over `U`
  when `x ∈ U`, together with `TauCeti.SheafOfModules.subsingleton_skyscraper_obj` when `x ∉ U`;
* `TauCeti.SheafOfModules.skyscraperHomEquiv`: the additive equivalence between morphisms
  `M ⟶ skyscraper R x T` and linear maps out of the stalk of `M` at `x`;
* `TauCeti.SheafOfModules.pushforwardSkyscraperIso`: the pushforward of a skyscraper sheaf of
  modules along a continuous map `(f, φ)` is isomorphic to the skyscraper sheaf at `f y`;
* `TauCeti.SheafOfModules.skyscraperCommRing`, `TauCeti.SheafOfModules.skyscraperCommRingHomEquiv`,
  and `TauCeti.SheafOfModules.pushforwardSkyscraperCommRingIso`: the specialization to sheaves of
  commutative rings retaining the `TopCat.Presheaf.stalk S.obj x` module structure.

## References

* [The Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098).
* `Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean` (Joël Riou, Brian Nugent) for the
  membership-indexed product presentation of skyscraper presheaves.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe u

noncomputable section

namespace TauCeti.SheafOfModules

open _root_.SheafOfModules

variable {X : TopCat.{u}}

/-- Universe-lifted type of membership proofs `x ∈ U`, used so `Pi.addCommGroup` and `Pi.module`
apply in universe `u`. -/
private abbrev SkyscraperIndex (x : X) (U : Opens X) : Type u :=
  ULift.{u} (PLift (x ∈ U))

/-- Underlying additive presheaf of the skyscraper sheaf at `x` with fiber `T`. -/
private def skyscraperAddPresheaf (x : X) (T : Type u) [AddCommGroup T] :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (SkyscraperIndex x U.unop → T)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s k ↦ s ⟨⟨i.unop.le k.down.down⟩⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := AddCommGrpCat.ext fun _ ↦ funext fun ⟨⟨_⟩⟩ ↦ rfl
  map_comp _ _ := AddCommGrpCat.ext fun _ ↦ funext fun ⟨⟨_⟩⟩ ↦ rfl

private theorem isSheaf_skyscraperAddPresheaf (x : X) (T : Type u) [AddCommGroup T] :
    TopCat.Presheaf.IsSheaf (skyscraperAddPresheaf x T) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  refine ⟨fun k ↦
    sf (Classical.choose (Opens.mem_iSup.mp k.down.down))
      ⟨⟨Classical.choose_spec (Opens.mem_iSup.mp k.down.down)⟩⟩, ?_, ?_⟩
  · intro j
    funext ⟨⟨hxj⟩⟩
    have hsup : x ∈ ⨆ i, U i := (Opens.leSupr U j).le hxj
    let i := Classical.choose (Opens.mem_iSup.mp hsup)
    let hxi : x ∈ U i := Classical.choose_spec (Opens.mem_iSup.mp hsup)
    exact congrFun (hcompat i j) ⟨⟨⟨hxi, hxj⟩⟩⟩
  · intro t ht
    funext ⟨⟨hx⟩⟩
    let i := Classical.choose (Opens.mem_iSup.mp hx)
    let hxi : x ∈ U i := Classical.choose_spec (Opens.mem_iSup.mp hx)
    exact congrFun (ht i) ⟨⟨hxi⟩⟩

section RingCat

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)
  (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk R.obj x) T]

@[instance_reducible]
private def skyscraperModule (U : (Opens X)ᵒᵖ) :
    Module (R.obj.obj U) ((skyscraperAddPresheaf x T).obj U) :=
  letI : SkyscraperIndex x U.unop → Module (R.obj.obj U) T :=
    fun k ↦ Module.compHom T (TopCat.Presheaf.germ R.obj U.unop x k.down.down).hom
  inferInstanceAs (Module (R.obj.obj U) (SkyscraperIndex x U.unop → T))

private def skyscraperPresheaf : PresheafOfModules.{u} R.obj :=
  letI : ∀ U, Module (R.obj.obj U) ((skyscraperAddPresheaf x T).obj U) := skyscraperModule R x T
  PresheafOfModules.ofPresheaf (skyscraperAddPresheaf x T) fun {_ _} i r s ↦
    funext fun k ↦ congrArg (· • s ⟨⟨i.unop.le k.down.down⟩⟩)
      (TopCat.Presheaf.germ_res_apply R.obj i.unop x k.down.down r).symm

/-- The skyscraper sheaf of `R`-modules at `x` with fiber `T`, where `T` is a module over the ring
stalk `TopCat.Presheaf.stalk R.obj x`. -/
def skyscraper : _root_.SheafOfModules.{u} R where
  val := skyscraperPresheaf R x T
  isSheaf := isSheaf_skyscraperAddPresheaf x T

/-- Evaluation of sections of `skyscraper R x T` over an open set `U` containing `x`. -/
def skyscraperEval {U : Opens X} (hx : x ∈ U) :
    ((skyscraper R x T).val.obj (op U) : Type u) →+ T where
  toFun s := s ⟨⟨hx⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem skyscraperEval_smul {U : Opens X} (hx : x ∈ U) (r : R.obj.obj (op U))
    (s : (skyscraper R x T).val.obj (op U)) :
    skyscraperEval R x T hx (r • s) =
      TopCat.Presheaf.germ R.obj U x hx r • skyscraperEval R x T hx s :=
  (rfl)

@[simp]
theorem skyscraperEval_map {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (s : (skyscraper R x T).val.obj (op V)) :
    skyscraperEval R x T hx ((skyscraper R x T).val.map i.op s) =
      skyscraperEval R x T (i.le hx) s :=
  (rfl)

/-- Over an open set not containing `x`, the skyscraper sheaf of modules has trivial sections. -/
theorem subsingleton_skyscraper_obj {U : Opens X} (hx : x ∉ U) :
    Subsingleton ((skyscraper R x T).val.obj (op U)) :=
  ⟨fun _ _ ↦ funext fun k ↦ False.elim (hx k.down.down)⟩

@[ext]
theorem skyscraper_section_ext {U : Opens X} {s t : (skyscraper R x T).val.obj (op U)}
    (h : ∀ hx : x ∈ U, skyscraperEval R x T hx s = skyscraperEval R x T hx t) : s = t :=
  funext fun k ↦ h k.down.down

private def toSkyscraperAddNatTrans {M : _root_.SheafOfModules.{u} R}
    (α : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T) :
    M.val.presheaf ⟶ (skyscraper R x T).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun m k ↦ α (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down m)
      map_zero' := funext fun k ↦
        (congrArg α (map_zero (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down).hom)).trans
          (map_zero α)
      map_add' := fun a b ↦ funext fun k ↦
        (congrArg α
          (map_add (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down).hom a b)).trans
          (map_add α _ _) }
  naturality {_ _} i := AddCommGrpCat.ext fun m ↦ funext fun ⟨⟨hx⟩⟩ ↦
    congrArg α (TopCat.Presheaf.germ_res_apply M.val.presheaf i.unop x hx m)

private def toSkyscraper {M : _root_.SheafOfModules.{u} R}
    (α : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T) :
    M ⟶ skyscraper R x T where
  val := PresheafOfModules.homMk (toSkyscraperAddNatTrans R x T α) fun U r m ↦
    funext fun k ↦
      (congrArg α (M.val.germ_ringCat_smul (R := R.obj) x U.unop k.down.down r m)).trans
        (α.map_smul (TopCat.Presheaf.germ R.obj U.unop x k.down.down r) _)

private def fromSkyscraperSection {M : _root_.SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T)
    (U : Opens X) (hx : x ∈ U) : M.val.obj (op U) →+ T :=
  (skyscraperEval R x T hx).comp (φ.val.app (op U)).hom.toAddMonoidHom

private theorem fromSkyscraperSection_res {M : _root_.SheafOfModules.{u} R}
    (φ : M ⟶ skyscraper R x T) {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : M.val.obj (op V)) :
    fromSkyscraperSection R x T φ U hx (M.val.map i.op m) =
      fromSkyscraperSection R x T φ V (i.le hx) m :=
  (congrArg (skyscraperEval R x T hx)
    (PresheafOfModules.naturality_apply φ.val i.op m)).trans
      (skyscraperEval_map R x T i hx (φ.val.app (op V) m))

private theorem fromSkyscraperSection_smul {M : _root_.SheafOfModules.{u} R}
    (φ : M ⟶ skyscraper R x T) (U : Opens X) (hx : x ∈ U) (r : R.obj.obj (op U))
    (m : M.val.obj (op U)) :
    fromSkyscraperSection R x T φ U hx (r • m) =
      TopCat.Presheaf.germ R.obj U x hx r • fromSkyscraperSection R x T φ U hx m :=
  (congrArg (skyscraperEval R x T hx) ((φ.val.app (op U)).hom.map_smul r m)).trans
    (skyscraperEval_smul R x T hx r (φ.val.app (op U) m))

private def fromSkyscraper {M : _root_.SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T :=
  M.val.stalkLift (R := R.obj) x (fromSkyscraperSection R x T φ)
    (fromSkyscraperSection_res R x T φ) (fromSkyscraperSection_smul R x T φ)

private theorem fromSkyscraper_germ {M : _root_.SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (fromSkyscraper R x T φ (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperEval R x T hx (φ.val.app (op U) m)) :=
  M.val.stalkLift_germ (R := R.obj) x (fromSkyscraperSection R x T φ)
    (fromSkyscraperSection_res R x T φ) (fromSkyscraperSection_smul R x T φ) U hx m

/-- Morphisms from a sheaf of `R`-modules `M` to the skyscraper sheaf `skyscraper R x T` are in
canonical additive bijection with `TopCat.Presheaf.stalk R.obj x`-linear maps from the stalk of `M`
at `x` to `T`. -/
def skyscraperHomEquiv (M : _root_.SheafOfModules.{u} R) :
    (M ⟶ skyscraper R x T) ≃+
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T) where
  toFun := fromSkyscraper R x T
  invFun := toSkyscraper R x T
  left_inv φ := by
    ext ⟨U⟩ m hx
    exact fromSkyscraper_germ R x T φ U hx m
  right_inv α := by
    ext s
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
    exact fromSkyscraper_germ R x T (toSkyscraper R x T α) U hx m
  map_add' φ ψ := by
    ext s
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
    rw [LinearMap.add_apply]
    exact (fromSkyscraper_germ R x T (φ + ψ) U hx m).trans
      (congrArg₂ (· + ·) (fromSkyscraper_germ R x T φ U hx m).symm
        (fromSkyscraper_germ R x T ψ U hx m).symm)

@[simp]
theorem skyscraperHomEquiv_germ {M : _root_.SheafOfModules.{u} R} (φ : M ⟶ skyscraper R x T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperHomEquiv R x T M φ (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperEval R x T hx (φ.val.app (op U) m)) :=
  fromSkyscraper_germ R x T φ U hx m

@[simp]
theorem skyscraperEval_skyscraperHomEquiv_symm_app {M : _root_.SheafOfModules.{u} R}
    (α : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperEval R x T hx (((skyscraperHomEquiv R x T M).symm α).val.app (op U) m) =
      α (TopCat.Presheaf.germ M.val.presheaf U x hx m)) :=
  (rfl)

/-- Pushing forward a skyscraper sheaf of modules along a continuous map `(f, φ) : (Y, R') → (X, R)`
identifies it with the skyscraper sheaf at `f y` with the same fiber `T` restricted along the
compatible ring stalk homomorphism `ρ`. -/
def pushforwardSkyscraperIso {Y : TopCat.{u}} (f : Y ⟶ X)
    (R' : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
    (φ : R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj R')
    (y : Y)
    (ρ : TopCat.Presheaf.stalk R.obj (f y) ⟶ TopCat.Presheaf.stalk R'.obj y)
    (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : R.obj.obj (op U)),
      ρ (TopCat.Presheaf.germ R.obj U (f y) hy r) =
        TopCat.Presheaf.germ R'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
    (T' : Type u) [AddCommGroup T'] [Module ↑(TopCat.Presheaf.stalk R'.obj y) T'] :
    letI : Module ↑(TopCat.Presheaf.stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
    (_root_.SheafOfModules.pushforward.{u} φ).obj (skyscraper R' y T') ≅
      skyscraper R (f y) T' :=
  letI : Module ↑(TopCat.Presheaf.stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
  { hom :=
      { val := PresheafOfModules.homMk
          { app := fun _ ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
            naturality := fun {_ _} _ ↦ AddCommGrpCat.ext fun _ ↦ rfl }
          fun U r s ↦ funext fun k ↦
            congrArg (· • s k) (hρ U.unop k.down.down r).symm }
    inv :=
      { val := PresheafOfModules.homMk
          { app := fun _ ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
            naturality := fun {_ _} _ ↦ AddCommGrpCat.ext fun _ ↦ rfl }
          fun U r s ↦ funext fun k ↦
            congrArg (· • s k) (hρ U.unop k.down.down r) }
    hom_inv_id := by ext _ _; rfl
    inv_hom_id := by ext _ _; rfl }

@[simp]
theorem skyscraperEval_pushforwardSkyscraperIso_hom_app {Y : TopCat.{u}} (f : Y ⟶ X)
    (R' : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
    (φ : R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj R')
    (y : Y)
    (ρ : TopCat.Presheaf.stalk R.obj (f y) ⟶ TopCat.Presheaf.stalk R'.obj y)
    (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : R.obj.obj (op U)),
      ρ (TopCat.Presheaf.germ R.obj U (f y) hy r) =
        TopCat.Presheaf.germ R'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
    (T' : Type u) [AddCommGroup T'] [Module ↑(TopCat.Presheaf.stalk R'.obj y) T']
    (U : Opens X) (hy : f y ∈ U)
    (s : (((_root_.SheafOfModules.pushforward.{u} φ).obj (skyscraper R' y T')).val.obj (op U))) :
    letI : Module ↑(TopCat.Presheaf.stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
    skyscraperEval R (f y) T' hy
        ((pushforwardSkyscraperIso R f R' φ y ρ hρ T').hom.val.app (op U) s) =
      skyscraperEval R' y T' hy s :=
  (rfl)

@[simp]
theorem skyscraperEval_pushforwardSkyscraperIso_inv_app {Y : TopCat.{u}} (f : Y ⟶ X)
    (R' : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
    (φ : R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj R')
    (y : Y)
    (ρ : TopCat.Presheaf.stalk R.obj (f y) ⟶ TopCat.Presheaf.stalk R'.obj y)
    (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : R.obj.obj (op U)),
      ρ (TopCat.Presheaf.germ R.obj U (f y) hy r) =
        TopCat.Presheaf.germ R'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
    (T' : Type u) [AddCommGroup T'] [Module ↑(TopCat.Presheaf.stalk R'.obj y) T']
    (U : Opens X) (hy : f y ∈ U) :
    letI : Module ↑(TopCat.Presheaf.stalk R.obj (f y)) T' := Module.compHom T' ρ.hom
    ∀ (s : (skyscraper R (f y) T').val.obj (op U)),
      skyscraperEval R' y T' hy
          ((pushforwardSkyscraperIso R f R' φ y ρ hρ T').inv.val.app (op U) s) =
        skyscraperEval R (f y) T' hy s :=
  fun _ ↦ (rfl)

end RingCat

section CommRingCat

variable (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)
  (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk S.obj x) T]

/-- Canonical ring homomorphism from the forgotten `RingCat` stalk of `S` at `x` to the underlying
ring of the `CommRingCat` stalk `TopCat.Presheaf.stalk S.obj x`, induced by the germ cocone. -/
private def ringCatStalkToCommRingStalk :
    TopCat.Presheaf.stalk (ringCatSheaf S).obj x ⟶
      RingCat.of ↑(TopCat.Presheaf.stalk S.obj x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (ringCatSheaf S).obj)
    ((forget₂ CommRingCat.{u} RingCat.{u}).mapCocone
      (colimit.cocone ((OpenNhds.inclusion x).op ⋙ S.obj)))

private theorem ringCatStalkToCommRingStalk_germ (U : Opens X) (hx : x ∈ U)
    (r : S.obj.obj (op U)) :
    ringCatStalkToCommRingStalk S x
        (TopCat.Presheaf.germ (ringCatSheaf S).obj U x hx r) =
      TopCat.Presheaf.germ S.obj U x hx r :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ (ringCatSheaf S).obj)
      ((forget₂ CommRingCat.{u} RingCat.{u}).mapCocone
        (colimit.cocone ((OpenNhds.inclusion x).op ⋙ S.obj))) (op ⟨U, hx⟩)) r

/-- The skyscraper sheaf of modules over a sheaf of commutative rings `S` attached to a module `T`
over the commutative-ring stalk `TopCat.Presheaf.stalk S.obj x`. -/
def skyscraperCommRing : _root_.SheafOfModules.{u} (ringCatSheaf S) :=
  letI : Module ↑(TopCat.Presheaf.stalk (ringCatSheaf S).obj x) T :=
    Module.compHom T (ringCatStalkToCommRingStalk S x).hom
  skyscraper (ringCatSheaf S) x T

/-- Evaluation of sections of `skyscraperCommRing S x T` over an open set `U` containing `x`. -/
def skyscraperCommRingEval {U : Opens X} (hx : x ∈ U) :
    ((skyscraperCommRing S x T).val.obj (op U) : Type u) →+ T :=
  letI : Module ↑(TopCat.Presheaf.stalk (ringCatSheaf S).obj x) T :=
    Module.compHom T (ringCatStalkToCommRingStalk S x).hom
  skyscraperEval (ringCatSheaf S) x T hx

@[simp]
theorem skyscraperCommRingEval_smul {U : Opens X} (hx : x ∈ U) (r : S.obj.obj (op U))
    (s : (skyscraperCommRing S x T).val.obj (op U)) :
    skyscraperCommRingEval S x T hx (r • s) =
      TopCat.Presheaf.germ S.obj U x hx r • skyscraperCommRingEval S x T hx s := by
  have h : skyscraperCommRingEval S x T hx (r • s) =
      ringCatStalkToCommRingStalk S x
        (TopCat.Presheaf.germ (ringCatSheaf S).obj U x hx r) •
          skyscraperCommRingEval S x T hx s := rfl
  rw [h, ringCatStalkToCommRingStalk_germ]

@[simp]
theorem skyscraperCommRingEval_map {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (s : (skyscraperCommRing S x T).val.obj (op V)) :
    skyscraperCommRingEval S x T hx ((skyscraperCommRing S x T).val.map i.op s) =
      skyscraperCommRingEval S x T (i.le hx) s :=
  (rfl)

@[ext]
theorem skyscraperCommRing_section_ext {U : Opens X}
    {s t : (skyscraperCommRing S x T).val.obj (op U)}
    (h : ∀ hx : x ∈ U, skyscraperCommRingEval S x T hx s = skyscraperCommRingEval S x T hx t) :
    s = t :=
  funext fun k ↦ h k.down.down

private def toSkyscraperCommRingAddNatTrans
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (α : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk S.obj x)] T) :
    M.val.presheaf ⟶ (skyscraperCommRing S x T).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun m k ↦ α (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down m)
      map_zero' := funext fun k ↦
        (congrArg α (map_zero (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down).hom)).trans
          (map_zero α)
      map_add' := fun a b ↦ funext fun k ↦
        (congrArg α
          (map_add (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down).hom a b)).trans
          (map_add α _ _) }
  naturality {_ _} i := AddCommGrpCat.ext fun m ↦ funext fun ⟨⟨hx⟩⟩ ↦
    congrArg α (TopCat.Presheaf.germ_res_apply M.val.presheaf i.unop x hx m)

private def toSkyscraperCommRing
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (α : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk S.obj x)] T) :
    M ⟶ skyscraperCommRing S x T where
  val := PresheafOfModules.homMk (toSkyscraperCommRingAddNatTrans S x T α) fun U r m ↦
    funext fun k ↦ by
      have h₁ := congrArg α (M.val.germ_smul (R := S.obj) x U.unop k.down.down r m)
      have h₂ := α.map_smul (TopCat.Presheaf.germ S.obj U.unop x k.down.down r)
        (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down m)
      have h₃ := congrArg (· • α (TopCat.Presheaf.germ M.val.presheaf U.unop x k.down.down m))
        (ringCatStalkToCommRingStalk_germ S x U.unop k.down.down r).symm
      exact h₁.trans (h₂.trans h₃)

private def fromSkyscraperCommRingSection
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) (U : Opens X) (hx : x ∈ U) : M.val.obj (op U) →+ T :=
  (skyscraperCommRingEval S x T hx).comp (φ.val.app (op U)).hom.toAddMonoidHom

private theorem fromSkyscraperCommRingSection_res
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (m : M.val.obj (op V)) :
    fromSkyscraperCommRingSection S x T φ U hx (M.val.map i.op m) =
      fromSkyscraperCommRingSection S x T φ V (i.le hx) m :=
  (congrArg (skyscraperCommRingEval S x T hx)
    (PresheafOfModules.naturality_apply φ.val i.op m)).trans
      (skyscraperCommRingEval_map S x T i hx (φ.val.app (op V) m))

private theorem fromSkyscraperCommRingSection_smul
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) (U : Opens X) (hx : x ∈ U)
    (r : S.obj.obj (op U)) (m : M.val.obj (op U)) :
    fromSkyscraperCommRingSection S x T φ U hx (r • m) =
      TopCat.Presheaf.germ S.obj U x hx r • fromSkyscraperCommRingSection S x T φ U hx m :=
  (congrArg (skyscraperCommRingEval S x T hx) ((φ.val.app (op U)).hom.map_smul r m)).trans
    (skyscraperCommRingEval_smul S x T hx r (φ.val.app (op U) m))

private def fromSkyscraperCommRing
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk S.obj x)] T :=
  M.val.stalkLiftCommRing (S := S.obj) x (fromSkyscraperCommRingSection S x T φ)
    (fromSkyscraperCommRingSection_res S x T φ) (fromSkyscraperCommRingSection_smul S x T φ)

private theorem fromSkyscraperCommRing_germ
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (fromSkyscraperCommRing S x T φ (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperCommRingEval S x T hx (φ.val.app (op U) m)) :=
  M.val.stalkLiftCommRing_germ (S := S.obj) x (fromSkyscraperCommRingSection S x T φ)
    (fromSkyscraperCommRingSection_res S x T φ)
    (fromSkyscraperCommRingSection_smul S x T φ) U hx m

/-- Morphisms from a sheaf of modules `M` over a sheaf of commutative rings `S` to
`skyscraperCommRing S x T` are in canonical additive bijection with
`TopCat.Presheaf.stalk S.obj x`-linear maps from the stalk of `M` at `x` to `T`. -/
def skyscraperCommRingHomEquiv
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (M ⟶ skyscraperCommRing S x T) ≃+
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk S.obj x)] T) where
  toFun := fromSkyscraperCommRing S x T
  invFun := toSkyscraperCommRing S x T
  left_inv φ := by
    ext ⟨U⟩ m hx
    exact fromSkyscraperCommRing_germ S x T φ U hx m
  right_inv α := by
    ext s
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
    exact fromSkyscraperCommRing_germ S x T (toSkyscraperCommRing S x T α) U hx m
  map_add' φ ψ := by
    ext s
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
    rw [LinearMap.add_apply]
    exact (fromSkyscraperCommRing_germ S x T (φ + ψ) U hx m).trans
      (congrArg₂ (· + ·) (fromSkyscraperCommRing_germ S x T φ U hx m).symm
        (fromSkyscraperCommRing_germ S x T ψ U hx m).symm)

@[simp]
theorem skyscraperCommRingHomEquiv_germ
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (φ : M ⟶ skyscraperCommRing S x T) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperCommRingHomEquiv S x T M φ (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperCommRingEval S x T hx (φ.val.app (op U) m)) :=
  fromSkyscraperCommRing_germ S x T φ U hx m

@[simp]
theorem skyscraperCommRingEval_skyscraperCommRingHomEquiv_symm_app
    {M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (α : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk S.obj x)] T)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (skyscraperCommRingEval S x T hx
        (((skyscraperCommRingHomEquiv S x T M).symm α).val.app (op U) m) =
      α (TopCat.Presheaf.germ M.val.presheaf U x hx m)) :=
  (rfl)

/-- Naturality of `skyscraperCommRingHomEquiv` in the source sheaf of modules. -/
theorem skyscraperCommRingHomEquiv_comp
    {L M : _root_.SheafOfModules.{u} (ringCatSheaf S)}
    (f : L ⟶ M) (φ : M ⟶ skyscraperCommRing S x T) :
    skyscraperCommRingHomEquiv S x T L (f ≫ φ) =
      (skyscraperCommRingHomEquiv S x T M φ).comp (stalkMap f x) := by
  ext s
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq L.val.presheaf s
  exact (skyscraperCommRingHomEquiv_germ S x T (f ≫ φ) U hx m).trans
    ((skyscraperCommRingHomEquiv_germ S x T φ U hx (f.val.app (op U) m)).symm.trans
      (congrArg (skyscraperCommRingHomEquiv S x T M φ) (stalkMap_germ f x U hx m).symm))

/-- Pushing forward a skyscraper sheaf of modules over a sheaf of commutative rings along `(f, φ)`
identifies it with the skyscraper sheaf at `f y` with fiber `T` restricted along `ρ`. -/
def pushforwardSkyscraperCommRingIso {Y : TopCat.{u}} (f : Y ⟶ X)
    (S' : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (φ : ringCatSheaf S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj
      (ringCatSheaf S'))
    (y : Y)
    (ρ : TopCat.Presheaf.stalk S.obj (f y) ⟶ TopCat.Presheaf.stalk S'.obj y)
    (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)),
      ρ (TopCat.Presheaf.germ S.obj U (f y) hy r) =
        TopCat.Presheaf.germ S'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
    (T' : Type u) [AddCommGroup T'] [Module ↑(TopCat.Presheaf.stalk S'.obj y) T'] :
    letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
    (_root_.SheafOfModules.pushforward.{u} φ).obj (skyscraperCommRing S' y T') ≅
      skyscraperCommRing S (f y) T' :=
  letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
  { hom :=
      { val := PresheafOfModules.homMk
          { app := fun _ ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
            naturality := fun {_ _} _ ↦ AddCommGrpCat.ext fun _ ↦ rfl }
          fun U r s ↦ funext fun k ↦ by
            have h₁ := ringCatStalkToCommRingStalk_germ S' y ((Opens.map f).obj U.unop)
              k.down.down (φ.hom.app U r)
            have h₂ := (hρ U.unop k.down.down r).symm
            have h₃ := congrArg ρ (ringCatStalkToCommRingStalk_germ S (f y) U.unop
              k.down.down r).symm
            exact congrArg (· • s k) (h₁.trans (h₂.trans h₃)) }
    inv :=
      { val := PresheafOfModules.homMk
          { app := fun _ ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
            naturality := fun {_ _} _ ↦ AddCommGrpCat.ext fun _ ↦ rfl }
          fun U r s ↦ funext fun k ↦ by
            have h₁ := congrArg ρ (ringCatStalkToCommRingStalk_germ S (f y) U.unop
              k.down.down r)
            have h₂ := hρ U.unop k.down.down r
            have h₃ := (ringCatStalkToCommRingStalk_germ S' y ((Opens.map f).obj U.unop)
              k.down.down (φ.hom.app U r)).symm
            exact congrArg (· • s k) (h₁.trans (h₂.trans h₃)) }
    hom_inv_id := by ext _ _; rfl
    inv_hom_id := by ext _ _; rfl }

@[simp]
theorem skyscraperCommRingEval_pushforwardSkyscraperCommRingIso_hom_app {Y : TopCat.{u}}
    (f : Y ⟶ X) (S' : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (φ : ringCatSheaf S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj
      (ringCatSheaf S'))
    (y : Y)
    (ρ : TopCat.Presheaf.stalk S.obj (f y) ⟶ TopCat.Presheaf.stalk S'.obj y)
    (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)),
      ρ (TopCat.Presheaf.germ S.obj U (f y) hy r) =
        TopCat.Presheaf.germ S'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
    (T' : Type u) [AddCommGroup T'] [Module ↑(TopCat.Presheaf.stalk S'.obj y) T']
    (U : Opens X) (hy : f y ∈ U)
    (s : (((_root_.SheafOfModules.pushforward.{u} φ).obj (skyscraperCommRing S' y T')).val.obj
      (op U))) :
    letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
    skyscraperCommRingEval S (f y) T' hy
        ((pushforwardSkyscraperCommRingIso S f S' φ y ρ hρ T').hom.val.app (op U) s) =
      skyscraperCommRingEval S' y T' hy s :=
  (rfl)

@[simp]
theorem skyscraperCommRingEval_pushforwardSkyscraperCommRingIso_inv_app {Y : TopCat.{u}}
    (f : Y ⟶ X) (S' : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (φ : ringCatSheaf S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj
      (ringCatSheaf S'))
    (y : Y)
    (ρ : TopCat.Presheaf.stalk S.obj (f y) ⟶ TopCat.Presheaf.stalk S'.obj y)
    (hρ : ∀ (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)),
      ρ (TopCat.Presheaf.germ S.obj U (f y) hy r) =
        TopCat.Presheaf.germ S'.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r))
    (T' : Type u) [AddCommGroup T'] [Module ↑(TopCat.Presheaf.stalk S'.obj y) T']
    (U : Opens X) (hy : f y ∈ U) :
    letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y)) T' := Module.compHom T' ρ.hom
    ∀ (s : (skyscraperCommRing S (f y) T').val.obj (op U)),
      skyscraperCommRingEval S' y T' hy
          ((pushforwardSkyscraperCommRingIso S f S' φ y ρ hρ T').inv.val.app (op U) s) =
        skyscraperCommRingEval S (f y) T' hy s :=
  fun _ ↦ (rfl)

end CommRingCat

end TauCeti.SheafOfModules

end
