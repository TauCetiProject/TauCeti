/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.InternalHom.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.GeneratingSections

/-!
# Injectivity of the internal-Hom stalk comparison

For a sheaf of modules of finite type, a germ of a local morphism is determined by its action
on the source stalk. Thus the canonical map from the stalk of the internal Hom to linear maps
between stalks is injective. The target sheaf is arbitrary, and the ringed space need not be a
scheme. The theorem `SheafOfModules.ihomStalkComparison_injective` applies in particular
to finitely presented source sheaves.

Finite generation lets finitely many neighborhoods on which generator images agree be replaced
by one common neighborhood. Finite presentation is needed only for the separate surjectivity
assertion: arbitrary maps of stalks must also lift compatibly with the relations.

## References

* [The Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP).
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite TopologicalSpace

universe u

noncomputable section

namespace TauCeti

namespace SheafOfModules

open _root_.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R))

private theorem ihom_map_eq_of_generators {U W : Opens X} (f : W ⟶ U)
    (G : (M.over U).GeneratingSections) (s t : ((ihom M).obj N).val.obj (op U))
    (h : ∀ i, (M.ihomObjEquiv N U s).val.app (op (Over.mk f))
        ((G.s i).val (op (Over.mk f))) =
      (M.ihomObjEquiv N U t).val.app (op (Over.mk f))
        ((G.s i).val (op (Over.mk f)))) :
    ((ihom M).obj N).val.map f.op s = ((ihom M).obj N).val.map f.op t := by
  let F := overMap (TauCeti.SheafOfModules.ringCatSheaf R) f
  let α := M.ihomObjEquiv N U s
  let β := M.ihomObjEquiv N U t
  have hab : F.map α = F.map β := by
    apply (cancel_epi (F.map G.π)).mp
    apply (isColimitOfPreserves F (isColimitFreeCofan G.I)).hom_ext
    rintro ⟨i⟩
    -- Normalize the cofan's point before rewriting its mapped injections.
    dsimp only [freeCofan, Cofan.mk_pt, Discrete.functor_obj]
    simp only [Functor.mapCocone_ι_app, ← Cofan.inj.eq_def, cofan_mk_inj]
    simp only [← Functor.map_comp, ← unitHomEquiv_symm_freeHomEquiv_apply,
      freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    apply Hom.ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    -- Here `overMap` is pushforward along `Over.map f`, and `Sheaf.pushforwardOverMapIso`
    -- is componentwise `Iso.refl`, so restriction of scalars and morphism components
    -- identify definitionally. The inverse of `PresheafOfModules.unitHomEquiv` uses
    -- `LinearMap.ringLmapEquivSelf.symm`, sending `a` to `a • s`.
    -- `pushforward_map_app_apply` expects an explicitly restricted-scalar source;
    -- rewriting it here fails on the module instance of `r`, typed via `F.obj`.
    -- `unitHomEquiv_apply_coe` only evaluates the forward map at `1`; no sheaf-level
    -- API lemma combines restriction with inverse-unit-Hom evaluation at a scalar.
    let a : ((TauCeti.SheafOfModules.ringCatSheaf R).over U).obj.obj
        (op ((Over.map f).obj V.unop)) := r
    change a • (α.val.app (op ((Over.map f).obj V.unop))
        ((G.s i).val (op ((Over.map f).obj V.unop)))) =
      a • (β.val.app (op ((Over.map f).obj V.unop))
        ((G.s i).val (op ((Over.map f).obj V.unop))))
    apply congrArg (a • ·)
    have hi := h i
    let j : (Over.map f).obj V.unop ⟶ Over.mk f :=
      Over.homMk V.unop.hom (by simp)
    have hs (p : (N.over U).sections) :
        (N.over U).val.map j.op (p.val (op (Over.mk f))) =
          p.val (op ((Over.map f).obj V.unop)) := p.property _
    exact (hs (sectionsMap α (G.s i))).symm.trans
      ((congrArg ((N.over U).val.map j.op) hi).trans
        (hs (sectionsMap β (G.s i))))
  apply (M.ihomObjEquiv N W).injective
  ext ⟨V⟩ m
  obtain ⟨V, ⟨⟨⟩⟩, g⟩ := V
  exact (M.ihomObjEquiv_map_app N s f g m).trans
    ((congrArg (fun p ↦ p.val.app (op (Over.mk g)) m) hab).trans
      (M.ihomObjEquiv_map_app N t f g m).symm)

private theorem exists_ihom_restrict_eq_of_germ_comparison_eq
    {U : Opens X} {x : X} (hx : x ∈ U) (G : (M.over U).GeneratingSections)
    [Finite G.I] (s t : ((ihom M).obj N).val.obj (op U))
    (h : M.ihomStalkComparison N x
        (TopCat.Presheaf.germ ((ihom M).obj N).val.presheaf U x hx s) =
      M.ihomStalkComparison N x
        (TopCat.Presheaf.germ ((ihom M).obj N).val.presheaf U x hx t)) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (f : W ⟶ U),
      ((ihom M).obj N).val.map f.op s = ((ihom M).obj N).val.map f.op t := by
  classical
  let α := M.ihomObjEquiv N U s
  let β := M.ihomObjEquiv N U t
  have hi (i : G.I) :
      TopCat.Presheaf.germ N.val.presheaf U x hx
          (α.val.app (op (Over.mk (𝟙 U))) ((G.s i).val (op (Over.mk (𝟙 U))))) =
        TopCat.Presheaf.germ N.val.presheaf U x hx
          (β.val.app (op (Over.mk (𝟙 U))) ((G.s i).val (op (Over.mk (𝟙 U))))) :=
    (M.ihomStalkComparison_germ_apply N x U hx s U (𝟙 U) hx _).symm.trans
      ((congrArg (fun φ ↦ φ (TopCat.Presheaf.germ M.val.presheaf U x hx
        ((G.s i).val (op (Over.mk (𝟙 U)))))) h).trans
        (M.ihomStalkComparison_germ_apply N x U hx t U (𝟙 U) hx _))
  choose W hxW iU jU heq using fun i ↦ TopCat.Presheaf.germ_eq N.val.presheaf x hx hx _ _ (hi i)
  -- Include `U` in the intersection, so the same construction covers an empty generator family.
  let V : Opens X := U ⊓ ⨅ i, W i
  have hxV : x ∈ V := by
    refine ⟨hx, ?_⟩
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun i ↦ hxW i
  let f : V ⟶ U := homOfLE inf_le_left
  refine ⟨V, hxV, f, ihom_map_eq_of_generators M N f G s t fun i ↦ ?_⟩
  let k : V ⟶ W i := homOfLE (inf_le_right.trans (iInf_le W i))
  let j : Over.mk (iU i) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (iU i) (by simp)
  have hs (p : (N.over U).sections) :
      N.val.map (iU i).op (p.val (op (Over.mk (𝟙 U)))) =
        p.val (op (Over.mk (iU i))) :=
    p.property j.op
  have he : (sectionsMap α (G.s i)).val (op (Over.mk (iU i))) =
      (sectionsMap β (G.s i)).val (op (Over.mk (iU i))) := by
    have heq' := heq i
    rw [Subsingleton.elim (jU i) (iU i)] at heq'
    exact (hs (sectionsMap α (G.s i))).symm.trans
      (heq'.trans (hs (sectionsMap β (G.s i))))
  let l : Over.mk f ⟶ Over.mk (iU i) := Over.homMk k (Subsingleton.elim _ _)
  have hr (p : (N.over U).sections) :
      N.val.map k.op (p.val (op (Over.mk (iU i)))) = p.val (op (Over.mk f)) :=
    p.property l.op
  exact (hr (sectionsMap α (G.s i))).symm.trans
    ((congrArg (N.val.map k.op) he).trans (hr (sectionsMap β (G.s i))))

/-- For a source sheaf of finite type, germs of local morphisms are determined by their maps
on stalks. No finiteness or quasi-coherence condition is required of the target. -/
theorem _root_.SheafOfModules.ihomStalkComparison_injective [M.IsFiniteType] (x : X) :
    Function.Injective (M.ihomStalkComparison N x) := by
  intro s t h
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff _ _).mp q.coversTop).exists_mem x
  let P := (ihom M).obj N
  obtain ⟨U, hUi, hxU, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq P.val.presheaf s hxi
  obtain ⟨V, hVU, hxV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq P.val.presheaf t hxU
  let f : V ⟶ U := homOfLE hVU
  let G := (q.generators i).restrict (homOfLE (hVU.trans hUi))
  have : (q.generators i).IsFiniteType := hq.isFiniteType i
  have : G.IsFiniteType := inferInstanceAs
    ((q.generators i).restrict (homOfLE (hVU.trans hUi))).IsFiniteType
  have hs := TopCat.Presheaf.germ_res_apply P.val.presheaf f x hxV s
  have h' : M.ihomStalkComparison N x
      (TopCat.Presheaf.germ P.val.presheaf V x hxV (P.val.map f.op s)) =
        M.ihomStalkComparison N x (TopCat.Presheaf.germ P.val.presheaf V x hxV t) :=
    (congrArg (M.ihomStalkComparison N x) hs).trans h
  obtain ⟨W, hxW, g, heq⟩ :=
    exists_ihom_restrict_eq_of_germ_comparison_eq M N hxV G (P.val.map f.op s) t h'
  have he := congrArg (TopCat.Presheaf.germ P.val.presheaf W x hxW) heq
  exact hs.symm.trans
    ((TopCat.Presheaf.germ_res_apply P.val.presheaf g x hxW (P.val.map f.op s)).symm.trans
      (he.trans (TopCat.Presheaf.germ_res_apply P.val.presheaf g x hxW t)))

end SheafOfModules

end TauCeti
