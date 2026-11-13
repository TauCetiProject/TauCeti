/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
public import TauCeti.Topology.Sheaves.Stalks.FiniteFamilies

/-!
# Exterior powers commute with stalks

For a presheaf of modules over a presheaf of commutative rings, taking the stalk of its
sectionwise exterior power agrees with taking the exterior power over the ring stalk.
The comparison sends the germ of a wedge to the wedge of the germs. Its inverse wedges
representatives on a common neighbourhood; finiteness of the degree makes this possible.
No sheaf condition or finite generation hypothesis is needed.

The argument follows the filtered-colimit calculation in the Stacks Project, Tag 01CH,
with varying coefficient rings, as in `PresheafOfModules.tensorStalkEquiv`.
-/

public section

open CategoryTheory Opposite TopologicalSpace TopCat.Presheaf

universe u

noncomputable section

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) (x : X) (n : ℕ)

private abbrev E := (PresheafOfModulesOfCommRing.exteriorPower n).obj M

private def sectionMap (U : Opens X) (hx : x ∈ U) :
    (PresheafOfModulesOfCommRing.obj M (op U)).exteriorPower n ⟶
      (ModuleCat.restrictScalars (R.germ U x hx).hom).obj
        ((ModuleCat.of (R.stalk x) ↑(stalk M.presheaf x)).exteriorPower n) := by
  let N := ModuleCat.of (R.stalk x) ↑(stalk M.presheaf x)
  let g := ModuleCat.semilinearMapAddEquiv (R.germ U x hx).hom
    (PresheafOfModulesOfCommRing.obj M (op U)) N (M.germSemilinear x U hx)
  exact ModuleCat.exteriorPower.map g n ≫
    (TauCeti.ModuleCat.restrictScalarsExteriorPowerComparison (R.germ U x hx).hom n).app N

private theorem sectionMap_mk (U : Opens X) (hx : x ∈ U) (m : Fin n → M.obj (op U)) :
    sectionMap M x n U hx (ModuleCat.exteriorPower.mk m) =
      exteriorPower.ιMulti (R.stalk x) n (fun i ↦ germ M.presheaf U x hx (m i)) := by
  erw [sectionMap, ModuleCat.comp_apply, ModuleCat.exteriorPower.map_mk,
    TauCeti.ModuleCat.restrictScalarsExteriorPowerComparison_app_mk]
  congr 1
  funext i
  rw [ModuleCat.semilinearMapAddEquiv_apply]
  exact M.germSemilinear_apply x U hx (m i)

private theorem sectionMap_res {U V : Opens X} (f : U ⟶ V) (hx : x ∈ U)
    (t : (E M n).obj (op V)) :
    sectionMap M x n U hx ((E M n).map f.op t) =
      sectionMap M x n V (f.le hx) t := by
  -- To compare semilinear maps along different section rings, use the span of wedges.
  have ht : t ∈ Submodule.span (R.obj (op V))
      (Set.range (exteriorPower.ιMulti (R.obj (op V)) n (M := M.obj (op V)))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨m, rfl⟩ := ht
      erw [PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk, sectionMap_mk,
        sectionMap_mk]
      congr 1
      funext i
      exact TopCat.Presheaf.germ_res_apply M.presheaf f x hx (m i)
  | zero => erw [map_zero, map_zero, map_zero]; rfl
  | add a b _ _ ha hb =>
      erw [map_add, map_add, map_add]
      exact congrArg₂ (· + ·) ha hb
  | smul r a _ ha =>
      erw [PresheafOfModules.map_smul, map_smul, map_smul, ha]
      exact congrArg (fun r ↦ r • sectionMap M x n V (f.le hx) a)
        (R.germ_res_apply f x hx r)

/-- The canonical linear map from the stalk of a sectionwise exterior power to the exterior
power of the stalk, over the ring stalk. -/
def exteriorPowerStalkComparison :
    ↑(stalk ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf x) →ₗ[R.stalk x]
      ⋀[R.stalk x]^n ↑(stalk M.presheaf x) :=
  (E M n).stalkLiftCommRing x
    (fun U hx ↦ (sectionMap M x n U hx).hom.toAddMonoidHom)
    (sectionMap_res M x n)
    (fun U hx r t ↦ (sectionMap M x n U hx).hom.map_smul r t)

/-- The exterior stalk comparison carries the germ of a wedge to the wedge of its germs. -/
@[simp]
theorem exteriorPowerStalkComparison_germ_mk (U : Opens X) (hx : x ∈ U)
    (m : Fin n → M.obj (op U)) :
    dsimp% only [presheaf_obj_coe, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (exteriorPowerStalkComparison M x n
        (germ ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf U x hx
          (ModuleCat.exteriorPower.mk m)) =
      exteriorPower.ιMulti (R.stalk x) n (fun i ↦ germ M.presheaf U x hx (m i))) := by
  exact ((E M n).stalkLiftCommRing_germ x _ _ _ U hx _).trans
    (sectionMap_mk M x n U hx m)

private theorem wedgeGerm_congr {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : Fin n → M.obj (op U)) (t : Fin n → M.obj (op V))
    (h : ∀ i, germ M.presheaf U x hxU (s i) = germ M.presheaf V x hxV (t i)) :
    germ (E M n).presheaf U x hxU (ModuleCat.exteriorPower.mk s) =
      germ (E M n).presheaf V x hxV (ModuleCat.exteriorPower.mk t) := by
  obtain ⟨W, hxW, a, b, hab⟩ := TopCat.Presheaf.germ_eq_family M.presheaf hxU hxV s t h
  -- The germ formulas are stated on additive-presheaf carriers, not module exterior powers.
  erw [← germ_res_apply (E M n).presheaf a x hxW,
    ← germ_res_apply (E M n).presheaf b x hxW]
  -- The underlying additive restriction is the semilinear module restriction.
  erw [PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk,
    PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk]
  exact congrArg (fun s ↦ germ (E M n).presheaf W x hxW (ModuleCat.exteriorPower.mk s))
    (funext hab)

private theorem exists_wedge (v : Fin n → ↑(stalk M.presheaf x)) :
    ∃ t : ↑(stalk (E M n).presheaf x), ∀ (U : Opens X) (hx : x ∈ U)
      (s : Fin n → M.obj (op U)), (∀ i, germ M.presheaf U x hx (s i) = v i) →
        t = germ (E M n).presheaf U x hx (ModuleCat.exteriorPower.mk s) := by
  obtain ⟨V, _, hxV, s, hs⟩ :=
    TopCat.Presheaf.exists_le_germ_eq_family M.presheaf v (V := ⊤) (by trivial)
  exact ⟨germ (E M n).presheaf V x hxV (ModuleCat.exteriorPower.mk s),
    fun U hx t ht ↦ wedgeGerm_congr M x n hxV hx s t (fun i ↦ (hs i).trans (ht i).symm)⟩

private def wedge (v : Fin n → ↑(stalk M.presheaf x)) : ↑(stalk (E M n).presheaf x) :=
  (exists_wedge M x n v).choose

private theorem wedge_germ (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (op U)) :
    wedge M x n (fun i ↦ germ M.presheaf U x hx (s i)) =
      germ (E M n).presheaf U x hx (ModuleCat.exteriorPower.mk s) :=
  (exists_wedge M x n _).choose_spec U hx s (fun _ ↦ rfl)

private theorem wedge_update_germ [DecidableEq (Fin n)]
    (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (op U)) (i : Fin n) (a : M.obj (op U)) :
    wedge M x n (Function.update (fun j ↦ germ M.presheaf U x hx (s j)) i
      (germ M.presheaf U x hx a)) =
      germ (E M n).presheaf U x hx (ModuleCat.exteriorPower.mk (Function.update s i a)) :=
  (congrArg (wedge M x n) (Function.comp_update (germ M.presheaf U x hx) s i a).symm).trans
    (wedge_germ M x n U hx _)

private theorem wedge_add [DecidableEq (Fin n)] (v : Fin n → ↑(stalk M.presheaf x)) (i : Fin n)
    (a b : ↑(stalk M.presheaf x)) :
    wedge M x n (Function.update v i (a + b)) =
      wedge M x n (Function.update v i a) + wedge M x n (Function.update v i b) := by
  classical
  let t : Fin n ⊕ Fin 2 → ↑(stalk M.presheaf x) := Sum.elim v ![a, b]
  obtain ⟨U, _, hx, s, hs⟩ :=
    TopCat.Presheaf.exists_le_germ_eq_family M.presheaf t (V := ⊤) (by trivial)
  have hv : v = fun j ↦ germ M.presheaf U x hx (s (Sum.inl j)) :=
    funext fun j ↦ (hs (Sum.inl j)).symm
  have ha : a = germ M.presheaf U x hx (s (Sum.inr 0)) := (hs (Sum.inr 0)).symm
  have hb : b = germ M.presheaf U x hx (s (Sum.inr 1)) := (hs (Sum.inr 1)).symm
  rw [hv, ha, hb]
  erw [← map_add]
  -- The representatives returned by the stalk lemma use additive-presheaf carriers.
  erw [wedge_update_germ, wedge_update_germ, wedge_update_germ]
  erw [ModuleCat.exteriorPower.mk.map_update_add, map_add]
  rfl

private theorem wedge_smul [DecidableEq (Fin n)] (v : Fin n → ↑(stalk M.presheaf x)) (i : Fin n)
    (r : R.stalk x) (a : ↑(stalk M.presheaf x)) :
    wedge M x n (Function.update v i (r • a)) = r • wedge M x n (Function.update v i a) := by
  classical
  obtain ⟨V, hxV, r, rfl⟩ := R.exists_germ_eq r
  obtain ⟨U, hUV, hx, s, hs⟩ := TopCat.Presheaf.exists_le_germ_eq_family M.presheaf
    (Sum.elim v (fun _ : Unit ↦ a)) hxV
  rw [← R.germ_res_apply (homOfLE hUV) x hx r]
  have hv : v = fun j ↦ germ M.presheaf U x hx (s (Sum.inl j)) :=
    funext fun j ↦ (hs (Sum.inl j)).symm
  have ha : a = germ M.presheaf U x hx (s (Sum.inr ())) := (hs (Sum.inr ())).symm
  rw [hv, ha]
  -- The representatives use the underlying additive presheaf, so unfold its carrier wrappers.
  erw [← M.germ_smul (R := R) x U hx, wedge_update_germ, wedge_update_germ]
  erw [ModuleCat.exteriorPower.mk.map_update_smul, (E M n).germ_smul (R := R) x U hx]
  rfl

private theorem wedge_eq_zero (v : Fin n → ↑(stalk M.presheaf x))
    (i j : Fin n) (h : v i = v j) (hij : i ≠ j) : wedge M x n v = 0 := by
  classical
  obtain ⟨U, _, hx, s, hs⟩ :=
    TopCat.Presheaf.exists_le_germ_eq_family M.presheaf v (V := ⊤) (by trivial)
  obtain ⟨V, hxV, a, b, hab⟩ := TopCat.Presheaf.germ_eq M.presheaf x hx hx (s i) (s j)
    ((hs i).trans (h.trans (hs j).symm))
  have hv : v = fun k ↦ germ M.presheaf V x hxV (M.map a.op (s k)) := by
    funext k
    exact ((germ_res_apply M.presheaf a x hxV (s k)).trans (hs k)).symm
  rw [hv]
  -- Again identify the underlying additive-presheaf sections with module sections.
  erw [wedge_germ]
  have he : M.map a.op (s i) = M.map a.op (s j) := by
    -- The equality is on the underlying additive restrictions, whose carriers are module
    -- sections. There is only one inclusion of `V` into `U`.
    change M.map a.op (s i) = M.map b.op (s j) at hab
    rw [Subsingleton.elim b a] at hab
    exact hab
  erw [ModuleCat.exteriorPower.mk.map_eq_zero_of_eq _ he hij, map_zero]

private def wedgeAlternating :
    ↑(stalk M.presheaf x) [⋀^Fin n]→ₗ[R.stalk x] ↑(stalk (E M n).presheaf x) where
  toFun := wedge M x n
  map_update_add' := wedge_add M x n
  map_update_smul' := wedge_smul M x n
  map_eq_zero_of_eq' v i j h hij := wedge_eq_zero M x n v i j h hij

private def inverse :
    (⋀[R.stalk x]^n ↑(stalk M.presheaf x)) →ₗ[R.stalk x] ↑(stalk (E M n).presheaf x) :=
  exteriorPower.alternatingMapLinearEquiv (wedgeAlternating M x n)

private theorem inverse_mk_germ (U : Opens X) (hx : x ∈ U)
    (s : Fin n → M.obj (op U)) :
    inverse M x n (exteriorPower.ιMulti (R.stalk x) n
      (fun i ↦ germ M.presheaf U x hx (s i))) =
      germ (E M n).presheaf U x hx (ModuleCat.exteriorPower.mk s) := by
  rw [inverse, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact wedge_germ M x n U hx s

/-- Linear maps out of an exterior-power stalk are determined on germs of wedges. -/
theorem exteriorPowerStalk_hom_ext {T : Type*} [AddCommGroup T] [Module (R.stalk x) T]
    {f g : ↑(stalk ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf x)
      →ₗ[R.stalk x] T}
    (h : ∀ (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (op U)),
      f (germ ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf U x hx
        (ModuleCat.exteriorPower.mk s)) =
      g (germ ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf U x hx
        (ModuleCat.exteriorPower.mk s))) : f = g := by
  apply LinearMap.ext
  intro t
  obtain ⟨U, hx, t, rfl⟩ := exists_germ_eq (E M n).presheaf t
  have ht : t ∈ Submodule.span (R.obj (op U))
      (Set.range (exteriorPower.ιMulti (R.obj (op U)) n (M := M.obj (op U)))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨s, rfl⟩ := ht
      exact h U hx s
  | zero => erw [map_zero, map_zero, map_zero]
  | add a b _ _ ha hb =>
      erw [map_add, map_add, map_add]
      exact congrArg₂ (· + ·) ha hb
  | smul r a _ ha =>
      erw [(E M n).germ_smul (R := R) x U hx, map_smul, map_smul]
      exact congrArg (fun t ↦ R.germ U x hx r • t) ha

/-- Exterior powers commute with stalks, without a finite generation or sheaf hypothesis. -/
def exteriorPowerStalkEquiv :
    ↑(stalk ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf x) ≃ₗ[R.stalk x]
      ⋀[R.stalk x]^n ↑(stalk M.presheaf x) :=
  LinearEquiv.ofLinearMap (exteriorPowerStalkComparison M x n) (inverse M x n)
    (by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      obtain ⟨U, _, hx, s, hs⟩ :=
        TopCat.Presheaf.exists_le_germ_eq_family M.presheaf v (V := ⊤) (by trivial)
      rw [← funext hs]
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.id_apply]
      erw [inverse_mk_germ, exteriorPowerStalkComparison_germ_mk]
      rfl)
    (by
      apply exteriorPowerStalk_hom_ext M x n
      intro U hx s
      erw [LinearMap.comp_apply, exteriorPowerStalkComparison_germ_mk, inverse_mk_germ]
      rfl)

/-- The exterior stalk equivalence is the canonical comparison. -/
@[simp]
theorem exteriorPowerStalkEquiv_apply
    (t : ↑(stalk ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf x)) :
    exteriorPowerStalkEquiv M x n t = exteriorPowerStalkComparison M x n t := (rfl)

/-- The inverse exterior stalk equivalence wedges representatives on a common neighbourhood. -/
@[simp]
theorem exteriorPowerStalkEquiv_symm_mk_germ (U : Opens X) (hx : x ∈ U)
    (s : Fin n → M.obj (op U)) :
    dsimp% only [presheaf_obj_coe, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((exteriorPowerStalkEquiv M x n).symm (exteriorPower.ιMulti (R.stalk x) n
      (fun i ↦ germ M.presheaf U x hx (s i))) =
      germ ((PresheafOfModulesOfCommRing.exteriorPower n).obj M).presheaf U x hx
        (ModuleCat.exteriorPower.mk s)) :=
  inverse_mk_germ M x n U hx s

/-- The exterior stalk equivalence is natural in the module presheaf. -/
theorem exteriorPowerStalkEquiv_naturality
    {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})} (f : M ⟶ N) :
    (exteriorPowerStalkEquiv N x n).toLinearMap.comp
        (stalkMapCommRing x ((PresheafOfModulesOfCommRing.exteriorPower n).map f)) =
      (exteriorPower.map n (stalkMapCommRing x f)).comp
        (exteriorPowerStalkEquiv M x n).toLinearMap := by
  apply exteriorPowerStalk_hom_ext M x n
  intro U hx s
  -- Germ computations retain explicit module carriers, while the stalk uses additive carriers.
  erw [LinearMap.comp_apply, stalkMapCommRing_germ,
    PresheafOfModulesOfCommRing.exteriorPower_map_app, ModuleCat.exteriorPower.map_mk]
  simp only [LinearEquiv.coe_coe, exteriorPowerStalkEquiv_apply, LinearMap.comp_apply]
  erw [exteriorPowerStalkComparison_germ_mk, exteriorPowerStalkComparison_germ_mk,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact (stalkMapCommRing_germ x f U hx (s i)).symm

end PresheafOfModules
