/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.InternalHom.FiniteType
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Over
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# The internal-Hom stalk comparison for finitely presented sources

Let `M` and `N` be sheaves of modules over a sheaf of commutative rings on a topological space.
If `M` is finitely presented, the canonical comparison `𝓗om(M, N)ₓ ⟶ Hom(Mₓ, Nₓ)` from
the stalk of the internal Hom to linear maps between the stalks is bijective, for an arbitrary
target `N`. Injectivity only needs `M` to be of finite type and is
`SheafOfModules.ihomStalkComparison_injective`; this file supplies surjectivity and packages the
comparison as a linear equivalence.

For surjectivity, let `φ : Mₓ → Nₓ` be linear and choose a finite presentation of `M` on a
neighbourhood `U` of `x`. The images under `φ` of the germs of the generators are germs of
sections of `N` on a smaller neighbourhood. The relations hold among these sections at the level
of germs, hence on a still smaller neighbourhood `V`, so the sections define a morphism
`M|_V ⟶ N|_V` through the cokernel description of the restricted presentation. Its germ maps to
`φ`, because both agree on the germs of the generators, which span `Mₓ`.

Without finite presentation the comparison need not be surjective, so no such statement is made
for sources that are only of finite type.

## Main declarations

* `SheafOfModules.ihomStalkComparison_surjective`: surjectivity for finitely presented sources;
* `SheafOfModules.ihomStalkComparison_bijective`: bijectivity for finitely presented sources;
* `SheafOfModules.ihomStalkEquiv`: the comparison as a linear equivalence
  `𝓗om(M, N)ₓ ≃ Hom(Mₓ, Nₓ)`.

## References

* [The Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP).
-/

public section

open CategoryTheory Limits MonoidalClosed Opposite TopologicalSpace

universe u

noncomputable section

namespace TauCeti

namespace SheafOfModules

open _root_.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)}

/- Given a presentation of `M` on `U` whose relations have coefficients `a`, sections `n` of `N`
over `V ⊆ U` satisfying the restricted relations are the images of the restricted generators
under a morphism `M|_V ⟶ N|_V`. The morphism is obtained from the cokernel description of the
presentation restricted along `V ⟶ U`. -/
private theorem exists_hom_of_presentation {U V : Opens X} (f : V ⟶ U)
    (P : (M.over U).Presentation) [Fintype P.generators.I]
    (a : P.relations.I → P.generators.I →
      ((ringCatSheaf R).over U).obj.obj (op (Over.mk (𝟙 U))))
    (ha : ∀ j, (sectionsMap (kernel.ι P.generators.π) (P.relations.s j)).val
        (op (Over.mk (𝟙 U))) = ∑ k, a j k • (freeSection k).eval (op (Over.mk (𝟙 U))))
    (n : P.generators.I → N.val.obj (op V))
    (hn : ∀ j, ∑ k, (ringCatSheaf R).obj.map f.op (a j k) • n k = 0) :
    ∃ ψ : M.over V ⟶ N.over V, ∀ k, ψ.val.app (op (Over.mk (𝟙 V)))
      (M.val.map f.op ((P.generators.s k).val (op (Over.mk (𝟙 U))))) = n k := by
  -- Restriction `F` from the slice over `U` to the slice over `V` preserves colimits, so it
  -- carries the cokernel presentation `free J ⟶ free I ⟶ M|_U` to one of `F (M|_U) ≅ M|_V`.
  -- We define `g' : F (free I) ⟶ N|_V` sending the `k`-th basis section to `n k`, check that
  -- it kills the restricted relations, and descend it along the restricted cokernel.
  -- Throughout, sections of the restricted sheaves over the terminal object `top` of the slice
  -- over `V` are, definitionally, sections of the original sheaves over `V`.
  let F := overMap (ringCatSheaf R) f
  let G := P.generators
  let η : unit _ ≅ F.obj (unit _) := (overMapUnitIso f).symm
  let ρ : free P.relations.I ⟶ free G.I :=
    (freeHomEquiv _).symm P.relations.s ≫ kernel.ι G.π
  have hc := CokernelCofork.mapIsColimit _ P.isColimit F
  let g' : F.obj (free G.I) ⟶ N.over V :=
    (mapFreeIso F G.I η).inv ≫
      (freeHomEquiv _).symm (fun k ↦ (N.overSectionsEquiv V).symm (n k))
  let top : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))
  -- `g'` sends the restricted `k`-th basis section to `n k`.
  have hg'k (k : G.I) :
      g'.val.app top ((freeSection (R := (ringCatSheaf R).over U) k).eval
        (op (Over.mk f))) = n k := by
    have h1 : η.hom ≫ F.map (ιFree k) ≫ (mapFreeIso F G.I η).inv = ιFree k := by simp
    let d := (N.over V).freeHomEquiv.symm fun k ↦ (N.overSectionsEquiv V).symm (n k)
    have := calc g'.val.app top ((freeSection k).eval (op (Over.mk f)))
        = d.val.app top ((η.hom ≫ F.map (ιFree k) ≫ (mapFreeIso F G.I η).inv).val.app top
          (1 : ((ringCatSheaf R).over V).obj.obj top)) :=
          -- `η` is the identity and `F.map (ιFree k)` evaluates `ιFree k` over `Over.mk f`.
          rfl
      _ = (sectionsMap d (freeSection k)).eval top := by rw [h1]; rfl
    refine this.trans ?_
    rw [sectionsMap_freeHomEquiv_symm_freeSection]
    exact (N.overSectionsEquiv_apply V _).symm.trans ((N.overSectionsEquiv V).apply_symm_apply _)
  -- `g'` kills the restricted relations: the `j`-th relation is sent to `∑ₖ aⱼₖ • n k`, which
  -- vanishes by `hn`. It suffices to check this over `top`.
  have hg' : F.map ρ ≫ g' = 0 := by
    -- Rewriting with `comp_zero` here is very slow, so the zero morphisms are compared
    -- through an explicit term.
    refine (cancel_epi (mapFreeIso F P.relations.I η).hom).mp
      ((?_ : (mapFreeIso F P.relations.I η).hom ≫ F.map ρ ≫ g' = 0).trans
        (Limits.comp_zero (f := (mapFreeIso F P.relations.I η).hom)).symm)
    apply (freeHomEquiv _).injective
    funext j
    have hιj := congrArg (fun φ : unit _ ⟶ F.obj (free P.relations.I) ↦ φ.val.app top
        (1 : ((ringCatSheaf R).over V).obj.obj top))
      (ιFree_mapFreeIso_hom F P.relations.I η j)
    have htop : ((N.over V).freeHomEquiv
        ((mapFreeIso F P.relations.I η).hom ≫ F.map ρ ≫ g') j).eval top = 0 := by
      have e1 : ((N.over V).freeHomEquiv
          ((mapFreeIso F P.relations.I η).hom ≫ F.map ρ ≫ g') j).eval top =
          g'.val.app top ((F.map ρ).val.app top
            ((mapFreeIso F P.relations.I η).hom.val.app top ((ιFree j).val.app top
              (1 : ((ringCatSheaf R).over V).obj.obj top)))) :=
        -- Evaluation of `freeHomEquiv` at `j` is evaluation of `ιFree j ≫ -` at `1`.
        rfl
      refine e1.trans
        ((congrArg (fun y ↦ g'.val.app top ((F.map ρ).val.app top y)) hιj).trans ?_)
      let Y' : (Over U)ᵒᵖ := op (Over.mk f)
      let i' : op (Over.mk (𝟙 U)) ⟶ Y' := (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)).op
      have e2 : (free G.I).val.map i'
            (∑ k, a j k • (freeSection k).eval (op (Over.mk (𝟙 U)))) =
          (F.map ρ).val.app top ((η.hom ≫ F.map (ιFree j)).val.app top
            (1 : ((ringCatSheaf R).over V).obj.obj top)) := by
        refine (congrArg ((free G.I).val.map i') (ha j)).symm.trans ?_
        refine ((sectionsMap (kernel.ι G.π) (P.relations.s j)).property i').trans ?_
        have : (free G.I).freeHomEquiv ρ j = sectionsMap (kernel.ι G.π) (P.relations.s j) :=
          (freeHomEquiv_comp_apply _ (kernel.ι G.π) j).trans (congrArg (sectionsMap _)
            (congrFun ((kernel G.π).freeHomEquiv.apply_symm_apply P.relations.s) j))
        exact congrArg (fun s : (free G.I).sections ↦ s.eval Y') this.symm
      refine (congrArg (g'.val.app top) e2.symm).trans ?_
      let r : G.I → ((ringCatSheaf R).over V).obj.obj top :=
        fun k ↦ (ringCatSheaf R).obj.map f.op (a j k)
      let e : G.I → (F.obj (free G.I)).val.obj top := fun k ↦ (freeSection k).eval Y'
      have e3 (k : G.I) :
          (free G.I).val.map i' (a j k • (freeSection k).eval (op (Over.mk (𝟙 U)))) =
          ((ringCatSheaf R).over U).obj.map i' (a j k) •
            (freeSection k).eval Y' :=
        (PresheafOfModules.map_smul _ _ _ _).trans (congrArg _ ((freeSection k).property i'))
      -- The restricted relation, read in the sections of `F (free I)` over `top`.
      have hsum : (show (F.obj (free G.I)).val.obj top from (free G.I).val.map i'
          (∑ k, a j k • (freeSection k).eval (op (Over.mk (𝟙 U))))) = ∑ k, r k • e k :=
        (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ e3 k)
      refine (congrArg (g'.val.app top) hsum).trans ?_
      refine (map_sum _ _ _).trans ((Finset.sum_congr rfl fun k _ ↦ ?_).trans (hn j))
      exact ((g'.val.app top).hom.map_smul (r k) (e k)).trans (congrArg (r k • ·) (hg'k k))
    ext Y
    let iY : top ⟶ Y := (Over.homMk Y.unop.hom : Y.unop ⟶ Over.mk (𝟙 V)).op
    refine (((N.over V).freeHomEquiv
        ((mapFreeIso F P.relations.I η).hom ≫ F.map ρ ≫ g') j).property iY).symm.trans ?_
    refine (congrArg ((N.over V).val.map iY) htop).trans ?_
    -- The value of the zero morphism on `1` is `0`.
    exact (map_zero _).trans rfl
  obtain ⟨ψ', hψ'⟩ := CokernelCofork.IsColimit.desc' hc g' hg'
  -- The comparison `F (M|_U) ≅ M|_V` is the identity on sections, and the restricted
  -- generators are images of the restricted basis sections.
  refine ⟨((overFunctorMap _ f).app M).inv ≫ ψ', fun k ↦ ?_⟩
  let i' : op (Over.mk (𝟙 U)) ⟶ op (Over.mk f) :=
    (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)).op
  have hx : (F.map G.π).val.app top ((freeSection k).eval (op (Over.mk f))) =
      M.val.map f.op ((G.s k).val (op (Over.mk (𝟙 U)))) :=
    (congrArg (fun s : (M.over U).sections ↦ s.eval (op (Over.mk f)))
      (sectionsMap_freeHomEquiv_symm_freeSection G.s k)).trans ((G.s k).property i').symm
  have hψk := congrArg (fun φ : F.obj (free G.I) ⟶ N.over V ↦
    φ.val.app top ((freeSection k).eval (op (Over.mk f)))) hψ'
  exact (congrArg (ψ'.val.app top) hx).symm.trans (hψk.trans (hg'k k))

/- A linear map between stalks at a point of `U` lifts to a germ of a local morphism, given a
finite presentation of `M` on `U`. -/
private theorem ihomStalkComparison_surjective_of_presentation {U : Opens X}
    (P : (M.over U).Presentation) [P.IsFinite] {x : X} (hx : x ∈ U)
    (φ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    ∃ s, M.ihomStalkComparison N x s = φ := by
  have : Fintype P.generators.I := Fintype.ofFinite _
  -- Lift the images of the germs of the generators to sections `n k` near `x`.
  choose W _ hxW n hn using fun k ↦ TopCat.Presheaf.exists_le_germ_eq N.val.presheaf
    (φ (TopCat.Presheaf.germ M.val.presheaf U x hx
      ((P.generators.s k).eval (op (Over.mk (𝟙 U)))))) hx
  -- Write each relation as a combination `∑ₖ aⱼₖ • eₖ` of the basis sections over `U`.
  choose a ha using fun j ↦ TauCeti.SheafOfModules.exists_eq_sum_smul_freeSection
    ((sectionsMap (kernel.ι P.generators.π) (P.relations.s j)).val (op (Over.mk (𝟙 U))))
  -- The relations of the presentation hold among the generators over `U`.
  have hrel (j : P.relations.I) :
      ∑ k, a j k • (P.generators.s k).eval (op (Over.mk (𝟙 U))) = 0 := by
    refine (freeHomEquiv_symm_val_app_sum_smul P.generators.s _ (a j)).symm.trans ?_
    refine (congrArg (P.generators.π.val.app _) (ha j).symm).trans ?_
    have h0 : (kernel.ι P.generators.π ≫ P.generators.π).val = 0 :=
      (congrArg (fun f ↦ f.val) (kernel.condition P.generators.π)).trans
        ((_root_.SheafOfModules.forget _).map_zero _ _)
    exact congrArg (fun f : PresheafOfModules.Hom _ _ ↦
      f.app (op (Over.mk (𝟙 U))) ((P.relations.s j).eval (op (Over.mk (𝟙 U))))) h0
  -- On the common neighbourhood `V₀` of the `W k`, let `t j` be the `j`-th relation evaluated on
  -- the sections `n k`. Its germ is `φ` applied to the germ of the `j`-th relation, so vanishes.
  let V₀ : Opens X := U ⊓ ⨅ k, W k
  have hxV₀ : x ∈ V₀ := ⟨hx, by rw [Opens.coe_iInf]; exact Set.mem_iInter.mpr hxW⟩
  let f₀ : V₀ ⟶ U := homOfLE inf_le_left
  let g₀ (k : P.generators.I) : V₀ ⟶ W k := homOfLE (inf_le_right.trans (iInf_le W k))
  let t (j : P.relations.I) : N.val.obj (op V₀) :=
    ∑ k, (ringCatSheaf R).obj.map f₀.op (a j k) • N.val.map (g₀ k).op (n k)
  have ht (j : P.relations.I) : TopCat.Presheaf.germ N.val.presheaf V₀ x hxV₀ (t j) = 0 := by
    have e1 (k : P.generators.I) : TopCat.Presheaf.germ N.val.presheaf V₀ x hxV₀
        ((ringCatSheaf R).obj.map f₀.op (a j k) •
          N.val.map (g₀ k).op (n k)) =
        TopCat.Presheaf.germ R.obj U x hx (a j k) •
          φ (TopCat.Presheaf.germ M.val.presheaf U x hx
            ((P.generators.s k).eval (op (Over.mk (𝟙 U))))) := by
      have hr : TopCat.Presheaf.germ R.obj V₀ x hxV₀
          ((ringCatSheaf R).obj.map f₀.op (a j k)) =
          TopCat.Presheaf.germ R.obj U x hx (a j k) :=
        TopCat.Presheaf.germ_res_apply R.obj f₀ x hxV₀ (a j k)
      have hm : TopCat.Presheaf.germ N.val.presheaf V₀ x hxV₀ (N.val.map (g₀ k).op (n k)) =
          TopCat.Presheaf.germ N.val.presheaf (W k) x (hxW k) (n k) :=
        TopCat.Presheaf.germ_res_apply N.val.presheaf (g₀ k) x hxV₀ (n k)
      refine (N.val.germ_smul (R := R.obj) x V₀ hxV₀ _ _).trans ?_
      rw [hr]
      exact congrArg (fun y : ↑(TopCat.Presheaf.stalk N.val.presheaf x) ↦
        TopCat.Presheaf.germ R.obj U x hx (a j k) • y) (hm.trans (hn k))
    have hg : TopCat.Presheaf.germ M.val.presheaf U x hx
        (∑ k, a j k • (P.generators.s k).eval (op (Over.mk (𝟙 U)))) =
        ∑ k, TopCat.Presheaf.germ R.obj U x hx (a j k) •
          TopCat.Presheaf.germ M.val.presheaf U x hx
            ((P.generators.s k).eval (op (Over.mk (𝟙 U)))) :=
      (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ ↦
        M.val.germ_smul (R := R.obj) x U hx _ _)
    refine (map_sum _ _ _).trans ((Finset.sum_congr rfl fun k _ ↦ e1 k).trans ?_)
    refine (Finset.sum_congr rfl fun k _ ↦ (φ.map_smul _ _).symm).trans ?_
    refine (map_sum φ _ _).symm.trans ((congrArg φ hg.symm).trans ?_)
    exact (congrArg (fun y ↦ φ (TopCat.Presheaf.germ M.val.presheaf U x hx y)) (hrel j)).trans
      ((congrArg φ (map_zero _)).trans (map_zero φ))
  -- Hence the finitely many `t j` vanish on a smaller neighbourhood `V`, where the restricted
  -- sections `n k` satisfy the restricted relations.
  choose W' hxW' i₁ i₂ heq using fun j ↦
    TopCat.Presheaf.germ_eq N.val.presheaf x hxV₀ hxV₀ (t j) 0 ((ht j).trans (map_zero _).symm)
  let V : Opens X := V₀ ⊓ ⨅ j, W' j
  have hxV : x ∈ V := ⟨hxV₀, by rw [Opens.coe_iInf]; exact Set.mem_iInter.mpr hxW'⟩
  let h₀ : V ⟶ V₀ := homOfLE inf_le_left
  let f : V ⟶ U := h₀ ≫ f₀
  have hn' (j : P.relations.I) : ∑ k, (ringCatSheaf R).obj.map f.op (a j k) •
      N.val.map (h₀ ≫ g₀ k).op (n k) = 0 := by
    have h2 : N.val.map h₀.op (t j) = 0 := by
      let k₁ : V ⟶ W' j := homOfLE (inf_le_right.trans (iInf_le W' j))
      refine (PresheafOfModules.map_comp_apply N.val (i₁ j).op k₁.op (t j)).trans ?_
      exact (congrArg (fun y ↦ N.val.map k₁.op y) (heq j)).trans
        ((congrArg (fun y ↦ N.val.map k₁.op y) (map_zero _)).trans (map_zero _))
    refine Eq.trans ?_ h2
    refine Eq.trans ?_ (map_sum _ _ _).symm
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    refine Eq.trans ?_ (PresheafOfModules.map_smul N.val h₀.op
      ((ringCatSheaf R).obj.map f₀.op (a j k)) (N.val.map (g₀ k).op (n k))).symm
    have er : (ringCatSheaf R).obj.map f.op (a j k) =
        (ringCatSheaf R).obj.map h₀.op
          ((ringCatSheaf R).obj.map f₀.op (a j k)) := by
      rw [show f.op = f₀.op ≫ h₀.op from rfl, Functor.map_comp]
      -- A composite of ring maps applied to `a j k` is the iterated application.
      rfl
    have en := PresheafOfModules.map_comp_apply N.val (g₀ k).op h₀.op (n k)
    rw [er]
    exact congrArg _ en
  -- These sections define a morphism `ψ : M|_V ⟶ N|_V`. Its germ agrees with `φ` on the germs
  -- of the generators, which span the stalk of `M`.
  obtain ⟨ψ, hψ⟩ := exists_hom_of_presentation f P a ha _ hn'
  refine ⟨TopCat.Presheaf.germ ((ihom M).obj N).val.presheaf V x hxV
    ((M.ihomObjEquiv N V).symm ψ), ?_⟩
  refine LinearMap.ext_on_range (GeneratingSections.span_germ_eq_top P.generators hx) fun k ↦ ?_
  have h1 := TopCat.Presheaf.germ_res_apply M.val.presheaf f x hxV
    ((P.generators.s k).eval (op (Over.mk (𝟙 U))))
  have h2 := M.ihomStalkComparison_germ_apply N x V hxV ((M.ihomObjEquiv N V).symm ψ) V (𝟙 V)
    hxV (M.val.map f.op ((P.generators.s k).eval (op (Over.mk (𝟙 U)))))
  rw [Equiv.apply_symm_apply] at h2
  refine (congrArg _ h1.symm).trans (h2.trans ?_)
  refine (congrArg (TopCat.Presheaf.germ N.val.presheaf V x hxV) (hψ k)).trans ?_
  exact (TopCat.Presheaf.germ_res_apply N.val.presheaf (h₀ ≫ g₀ k) x hxV (n k)).trans (hn k)

variable (M N)

/-- For a finitely presented source sheaf, every linear map between stalks is the image of a germ
of a local morphism. No condition is imposed on the target. -/
theorem _root_.SheafOfModules.ihomStalkComparison_surjective [M.IsFinitePresentation] (x : X) :
    Function.Surjective (M.ihomStalkComparison N x) := by
  intro φ
  obtain ⟨q, hq⟩ := IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff _ _).mp q.coversTop).exists_mem x
  exact ihomStalkComparison_surjective_of_presentation (q.presentation i) hxi φ

/-- For a finitely presented source sheaf, the comparison from the stalk of the internal Hom to
linear maps between the stalks is bijective. -/
theorem _root_.SheafOfModules.ihomStalkComparison_bijective [M.IsFinitePresentation] (x : X) :
    Function.Bijective (M.ihomStalkComparison N x) :=
  ⟨M.ihomStalkComparison_injective N x, M.ihomStalkComparison_surjective N x⟩

/-- For a finitely presented source sheaf `M`, the stalk at `x` of the internal Hom `𝓗om(M, N)`
is the module of linear maps from the stalk of `M` to the stalk of `N`, through the canonical
comparison `SheafOfModules.ihomStalkComparison`. -/
def _root_.SheafOfModules.ihomStalkEquiv [M.IsFinitePresentation] (x : X) :
    ↑(TopCat.Presheaf.stalk ((ihom M).obj N).val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :=
  LinearEquiv.ofBijective (M.ihomStalkComparison N x) (M.ihomStalkComparison_bijective N x)

/-- The stalk equivalence is the canonical comparison. -/
-- This is not a simp lemma: `SheafOfModules.ihom_obj` rewrites the internal Hom in its left-hand
-- side.
theorem _root_.SheafOfModules.ihomStalkEquiv_apply [M.IsFinitePresentation] (x : X)
    (s : ↑(TopCat.Presheaf.stalk ((ihom M).obj N).val.presheaf x)) :
    M.ihomStalkEquiv N x s = M.ihomStalkComparison N x s :=
  (rfl)

end SheafOfModules

end TauCeti
