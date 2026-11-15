/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.GeneratingSections
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Module structures on stalks of sheaves of modules

The stalk of a sheaf of modules over a sheaf of rings is a module over the ring stalk.
For commutative coefficient rings, it also retains the module action
of the original commutative ring stalk when the coefficient sheaf forgets commutativity.
The instance `SheafOfModules.stalkModule` exposes Mathlib's commutative presheaf stalk module
structure independently of the internal Hom construction. For ordinary ring coefficients,
Mathlib's presheaf stalk instance applies directly to the underlying presheaf of modules.

The linear equivalence `PresheafOfModules.sheafificationStalkEquiv` identifies a module
presheaf stalk with its sheafification stalk, preserving the original commutative-ring
stalk as coefficient ring. Its forward and inverse maps are characterized on germs.

If finitely many sections generate the restriction of a sheaf of modules to a neighbourhood of
`x`, their germs span the stalk at `x` over the ring stalk
(`SheafOfModules.GeneratingSections.span_germ_eq_top`). Thus a linear map out of the stalk of a
sheaf of finite type is determined by its values on the germs of local generators.

Finally, `SheafOfModules.stalkMap` packages the linear map on stalks induced by a morphism of
sheaves of modules over a sheaf of commutative rings, and
`SheafOfModules.isIso_iff_stalkFunctor_map_isIso` and `SheafOfModules.isIso_iff_stalkMap_bijective`
show that a morphism of sheaves of modules on a topological space is an isomorphism if and only if
it induces isomorphisms on all stalks.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe u

noncomputable section

namespace SheafOfModules
open TauCeti.SheafOfModules (ringCatSheaf)
variable {X : TopCat.{u}}
section RingCat
variable {S : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A morphism of sheaves of modules on a topological space is an isomorphism if and only if the
induced map on stalks is an isomorphism in `AddCommGrpCat` at every point. -/
theorem isIso_iff_stalkFunctor_map_isIso {M N : SheafOfModules.{u} S} (f : M ⟶ N) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf S.obj).map f.val)) :=
  ⟨fun _ ↦ (isIso_iff_stalkFunctor_map_iso ((toSheaf S).map f)).mp inferInstance, fun hf ↦ by
    have : IsIso ((toSheaf S).map f) := (isIso_iff_stalkFunctor_map_iso ((toSheaf S).map f)).mpr hf
    exact isIso_of_reflects_iso f (toSheaf S)⟩
end RingCat
variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The stalk of a sheaf of modules carries Mathlib's module structure over the stalk of
the original commutative-ring sheaf. The carrier and action are unchanged by forgetting
commutativity in the coefficient sheaf. -/
instance stalkModule (P : SheafOfModules.{u} (ringCatSheaf R)) (x : X) :
    Module ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk P.val.presheaf x) :=
  let Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) := P.val
  inferInstanceAs (Module ↑(TopCat.Presheaf.stalk R.obj x)
    ↑(TopCat.Presheaf.stalk Q.presheaf x))

/-- The linear map on stalks induced by a morphism of sheaves of modules over a sheaf of
commutative rings. -/
def stalkMap {M N : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) (x : X) :
    ↑(stalk M.val.presheaf x) →ₗ[↑(stalk R.obj x)] ↑(stalk N.val.presheaf x) :=
  PresheafOfModules.stalkMapCommRing (S := R.obj) x f.val

/-- `SheafOfModules.stalkMap` sends the germ of a section to the germ of its image. -/
@[simp] theorem stalkMap_germ {M N : SheafOfModules.{u} (ringCatSheaf R)}
    (f : M ⟶ N) (x : X) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (stalkMap f x (germ M.val.presheaf U x hx m) =
      germ N.val.presheaf U x hx (f.val.app (op U) m)) :=
  PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x f.val U hx m

/-- As a function between stalks, `SheafOfModules.stalkMap` agrees with the additive stalk functor
applied to the underlying presheaf morphism. -/
theorem coe_stalkMap {M N : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) (x : X) :
    (stalkMap f x : ↑(stalk M.val.presheaf x) → ↑(stalk N.val.presheaf x)) =
      (stalkFunctor AddCommGrpCat.{u} x).map ((PresheafOfModules.toPresheaf _).map f.val) := by
  funext m; obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq M.val.presheaf m
  erw [stalkMap_germ, stalkFunctor_map_germ_apply]; rfl
@[simp] theorem stalkMap_id (M : SheafOfModules.{u} (ringCatSheaf R)) (x : X) :
    stalkMap (𝟙 M) x = LinearMap.id := by
  ext m; obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq M.val.presheaf m
  exact stalkMap_germ (𝟙 M) x U hx m
@[simp] theorem stalkMap_comp {L M N : SheafOfModules.{u} (ringCatSheaf R)}
    (f : L ⟶ M) (g : M ⟶ N) (x : X) :
    stalkMap (f ≫ g) x = (stalkMap g x).comp (stalkMap f x) := by
  ext m; obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq L.val.presheaf m
  exact (stalkMap_germ (f ≫ g) x U hx m).trans
    ((stalkMap_germ g x U hx (f.val.app (op U) m)).symm.trans
      (congrArg (stalkMap g x) (stalkMap_germ f x U hx m).symm))

/-- An isomorphism of sheaves of modules induces a linear equivalence on stalks. -/
def stalkLinearEquivOfIso {M N : SheafOfModules.{u} (ringCatSheaf R)} (e : M ≅ N) (x : X) :
    ↑(stalk M.val.presheaf x) ≃ₗ[↑(stalk R.obj x)] ↑(stalk N.val.presheaf x) :=
  LinearEquiv.ofLinearMap (stalkMap e.hom x) (stalkMap e.inv x)
    ((stalkMap_comp e.inv e.hom x).symm.trans
      ((congrArg (stalkMap · x) e.inv_hom_id).trans (stalkMap_id N x)))
    ((stalkMap_comp e.hom e.inv x).symm.trans
      ((congrArg (stalkMap · x) e.hom_inv_id).trans (stalkMap_id M x)))
@[simp] theorem stalkLinearEquivOfIso_apply {M N : SheafOfModules.{u} (ringCatSheaf R)}
    (e : M ≅ N) (x : X) (m : ↑(stalk M.val.presheaf x)) :
    stalkLinearEquivOfIso e x m = stalkMap e.hom x m := (rfl)
@[simp] theorem stalkLinearEquivOfIso_symm {M N : SheafOfModules.{u} (ringCatSheaf R)}
    (e : M ≅ N) (x : X) : (stalkLinearEquivOfIso e x).symm = stalkLinearEquivOfIso e.symm x := (rfl)

/-- A morphism of sheaves of modules over a sheaf of commutative rings on a topological space is an
isomorphism if and only if the induced linear map on stalks is bijective at every point. -/
theorem isIso_iff_stalkMap_bijective {M N : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) :
    IsIso f ↔ ∀ x : X, Function.Bijective (stalkMap f x) := by
  rw [isIso_iff_stalkFunctor_map_isIso]; refine forall_congr' fun x ↦ ?_
  rw [coe_stalkMap, ConcreteCategory.isIso_iff_bijective]; exact Iff.rfl
end SheafOfModules

namespace PresheafOfModules

variable {X : TopCat.{u}} (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (P : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u})) (x : X)

private abbrev sheafified :=
  (sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P

private def sheafificationUnit : P ⟶ (sheafified S P).val :=
  (sheafificationAdjunction (R := TauCeti.SheafOfModules.ringCatSheaf S)
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).unit.app P

private def sheafificationStalkMap :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) P.presheaf x) →ₗ[
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) S.obj x]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        (sheafified S P).val.presheaf x) :=
  stalkMapCommRing (S := S.obj) x (sheafificationUnit S P)

private lemma sheafificationStalkMap_germ (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    sheafificationStalkMap S P x (TopCat.Presheaf.germ P.presheaf U x hx m) =
      TopCat.Presheaf.germ (sheafified S P).val.presheaf U x hx
        ((sheafificationUnit S P).app (op U) m) :=
  stalkMapCommRing_germ (S := S.obj) x (sheafificationUnit S P) U hx m

private lemma sheafificationStalkMap_bijective :
    Function.Bijective (sheafificationStalkMap S P x) := by
  have h : (sheafificationStalkMap S P x :
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) P.presheaf x) →
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
          (sheafified S P).val.presheaf x)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toPresheaf _).map (sheafificationUnit S P)) := by
    funext m
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf m
    erw [sheafificationStalkMap_germ, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  rw [h]
  have hunit : (toPresheaf _).map (sheafificationUnit S P) =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    exact toPresheaf_map_sheafificationAdjunction_unit_app
      (R := TauCeti.SheafOfModules.ringCatSheaf S)
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj) P
  erw [hunit]
  have hIso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    P.presheaf
  exact (ConcreteCategory.isIso_iff_bijective _).mp hIso

/-- Sheafification preserves module stalks, linearly over the original commutative-ring stalk.
The equivalence is induced by the unit of the sheafification adjunction. -/
def sheafificationStalkEquiv :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) P.presheaf x) ≃ₗ[
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) S.obj x]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        ((sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
          (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P).val.presheaf x) :=
  LinearEquiv.ofBijective (sheafificationStalkMap S P x)
    (sheafificationStalkMap_bijective S P x)

/-- The sheafification stalk equivalence sends a germ to the germ of its unit image. -/
@[simp]
theorem sheafificationStalkEquiv_germ (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    dsimp% only [presheaf_obj_coe, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (P.sheafificationStalkEquiv S x (TopCat.Presheaf.germ P.presheaf U x hx m) =
      TopCat.Presheaf.germ
        ((sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
          (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P).val.presheaf U x hx
          (((sheafificationAdjunction
            (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).unit.app P).app (op U) m)) :=
  sheafificationStalkMap_germ S P x U hx m

/-- The inverse equivalence sends the germ of a unit image back to its original germ. -/
@[simp]
theorem sheafificationStalkEquiv_symm_germ_unit
    (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    dsimp% only [presheaf_obj_coe, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((P.sheafificationStalkEquiv S x).symm
      (TopCat.Presheaf.germ
        ((sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
          (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P).val.presheaf U x hx
          (((sheafificationAdjunction
            (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).unit.app P).app (op U) m)) =
      TopCat.Presheaf.germ P.presheaf U x hx m) := by
  exact (P.sheafificationStalkEquiv S x).symm_apply_eq.mpr
    (P.sheafificationStalkEquiv_germ S x U hx m).symm

end PresheafOfModules

namespace SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R)}

/-- If finitely many sections generate the restriction of `M` to a neighbourhood `U` of `x`,
their germs span the stalk of `M` at `x` over the ring stalk. -/
theorem GeneratingSections.span_germ_eq_top {U : Opens X} (G : (M.over U).GeneratingSections)
    [Finite G.I] {x : X} (hx : x ∈ U) :
    Submodule.span ↑(TopCat.Presheaf.stalk R.obj x) (Set.range fun k ↦
      germ M.val.presheaf U x hx ((G.s k).val (op (Over.mk (𝟙 U))))) = ⊤ := by
  have : Fintype G.I := Fintype.ofFinite _
  refine Submodule.eq_top_iff'.mpr fun y ↦ ?_
  obtain ⟨W, hWU, hxW, m, rfl⟩ := exists_le_germ_eq M.val.presheaf y hx
  -- Near `x`, the section `m` is a linear combination of the restricted generators.
  obtain ⟨S, hS, hSm⟩ := G.exists_sieve_sum_smul_eq (Y := Over.mk (homOfLE hWU)) m
  obtain ⟨V, f, hf, hxV⟩ := hS x hxW
  obtain ⟨a, ha⟩ := hSm _ ((Sieve.overEquiv_iff S f).mp hf)
  have hy : germ M.val.presheaf V x hxV
      (∑ k, a k • (G.s k).eval (op (Over.mk (f ≫ homOfLE hWU)))) =
        germ M.val.presheaf W x hxW m :=
    (congrArg (germ M.val.presheaf V x hxV) ha).trans (germ_res_apply M.val.presheaf f x hxV m)
  rw [← hy]
  -- The sum lives in the sections of the restriction to the slice, which are only
  -- definitionally the sections of `M` over `V`.
  erw [map_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  have he : (G.s k).eval (op (Over.mk (f ≫ homOfLE hWU))) =
      M.val.map (f ≫ homOfLE hWU).op ((G.s k).val (op (Over.mk (𝟙 U)))) :=
    ((G.s k).property
      (Over.homMk (f ≫ homOfLE hWU) : Over.mk (f ≫ homOfLE hWU) ⟶ Over.mk (𝟙 U)).op).symm
  -- As above, the scalar `a k` is a section of the restricted ring sheaf, which is only
  -- definitionally a section of `R` over `V`.
  erw [M.val.germ_smul (R := R.obj) x V hxV (a k), he,
    germ_res_apply M.val.presheaf (f ≫ homOfLE hWU) x hxV]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end SheafOfModules
