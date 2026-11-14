/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import TauCeti.Topology.Sheaves.Cohomology.Forget
public import TauCeti.Topology.Sheaves.Godement
import Mathlib.Algebra.Category.Grp.Zero
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence
import TauCeti.Topology.Sheaves.Cohomology.Restriction
import TauCeti.Topology.Sheaves.Exact
import TauCeti.Topology.Sheaves.Flasque.Basic

/-!
# Fine sheaves are acyclic

A sheaf `F` on a topological space `X`, valued in a preadditive category, is *fine*
(`TopCat.Sheaf.IsFine`) if every open cover `U` of `X` admits a *sheaf partition of unity*
(`TopCat.Sheaf.IsPartitionOfUnity`): a family of sheaf endomorphisms `η i : F ⟶ F` such that each
`η i` vanishes on all opens inside an open `complSupport i` satisfying `U i ⊔ complSupport i = ⊤`,
and every point of `X` has an open neighbourhood `N` on which all `η i` outside a finite set `s`
vanish while `∑ i ∈ s, η i` acts as the identity on all opens inside `N`.

For sheaves of abelian groups on any topological space `X` (with no separation or paracompactness
assumptions on `X`), every fine sheaf has vanishing sheaf cohomology `CategoryTheory.Sheaf.H` in
every positive degree (`TopCat.Sheaf.subsingleton_H_succ_of_isFine`,
`TopCat.Sheaf.IsFine.subsingleton_H_of_pos`). For sheaves of modules over a commutative ring `R`,
fineness likewise forces the right derived global-section functors `RⁿΓ(F)` to vanish in every
positive degree (`TopCat.Sheaf.IsFine.isZero_rightDerived_Γ_succ`,
`TopCat.Sheaf.IsFine.isZero_rightDerived_Γ_of_pos`).

## Mathematical overview

Embed an abelian sheaf `F` into its Godement sheaf `G⁰(F) = (godement AddCommGrpCat X).obj F`
(`TauCeti.Topology.toGodement`), with cokernel sheaf `Z¹(F)`. The Godement functor is additive
(`TauCeti.Topology.additive_godement`) and local
(`TauCeti.Topology.godement_map_app_eq_zero_of_app_eq_zero`), so any sheaf partition of unity on
`F` pushes forward to `G⁰(F)` (`TauCeti.Topology.isPartitionOfUnity_godement_map`) and hence to
`Z¹(F)` (`TopCat.Sheaf.app_eq_zero_of_epi_comp`). In particular `Z¹(F)` is again fine when `F` is
(`TauCeti.Topology.isFine_cokernel_toGodement_app`).

Moreover, global sections `G⁰(F)(⊤) ⟶ Z¹(F)(⊤)` are surjective whenever `F` is fine: any global
section `z` of `Z¹(F)` lifts locally to `G⁰(F)`, extends from each local neighbourhood to `⊤`
because `G⁰(F)` is flasque (`TauCeti.Topology.isFlasque_godement_obj`), and is reassembled by the
induced partition of unity on `G⁰(F)` (`TauCeti.Topology.surjective_cokernel_π_toGodement_top`).
Since `G⁰(F)` has no higher cohomology (`TauCeti.Topology.subsingleton_H_succ_of_isFlasque`),
dimension shifting along `0 ⟶ F ⟶ G⁰(F) ⟶ Z¹(F) ⟶ 0` proves `H¹(X, F) = 0` and inductively
`Hⁿ⁺²(X, F) ≅ Hⁿ⁺¹(X, Z¹(F)) = 0`.

## Main definitions

* `TopCat.Sheaf.IsPartitionOfUnity`: a sheaf partition of unity on `F` subordinate to an open
  cover `U`.
* `TopCat.Sheaf.IsFine`: class asserting that `F` admits a sheaf partition of unity subordinate to
  every open cover of `X`.

## Main results

* `TopCat.Sheaf.IsFine.of_retract`, `TopCat.Sheaf.IsFine.of_iso`, and
  `TopCat.Sheaf.IsFine.of_isZero`: fineness is preserved by retracts and isomorphisms and holds for
  zero sheaves.
* `TopCat.Sheaf.isFine_sheafCompose`: postcomposing with an additive sheaf-preserving functor (such
  as forgetting an `R`-module structure) preserves fineness.
* `TauCeti.Topology.isFine_godement_obj` and `TauCeti.Topology.isFine_cokernel_toGodement_app`:
  for a fine sheaf `F`, both `G⁰(F)` and `Z¹(F)` are fine.
* `TopCat.Sheaf.subsingleton_H_succ_of_isFine` and `TopCat.Sheaf.IsFine.subsingleton_H_of_pos`:
  every fine abelian sheaf has vanishing cohomology `Sheaf.H` in positive degrees.
* `TopCat.Sheaf.IsFine.g_hom_app_top_surjective` and
  `TopCat.Sheaf.IsFine.shortExact_map_sheafSections_top`: global sections are exact on short exact
  sequences with fine kernel.
* `TopCat.Sheaf.IsFine.subsingleton_H'_of_sheafRestrict_of_pos`: positive-degree cohomology over an
  open subset `U` vanishes when `U.sheafRestrict.obj F` is fine.
* `TopCat.Sheaf.IsFine.isZero_rightDerived_Γ_succ` and
  `TopCat.Sheaf.IsFine.isZero_rightDerived_Γ_of_pos`: every fine sheaf of `R`-modules has vanishing
  derived global sections in positive degrees.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Hermann, 1958, §3.7 and §4.4.
* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Graduate Texts in
  Mathematics 65, Springer, 2008, Chapter II, §3.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2021,
  Example 7.5.31 and Proposition 7.5.32, p. 327.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u

namespace TopCat.Sheaf

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] {X : TopCat.{w}}

/-- A family of endomorphisms `η : ι → (F ⟶ F)` of a sheaf `F` on `X` is a *sheaf partition of
unity* subordinate to an indexed family of opens `U : ι → Opens X` if each `η i` vanishes on all
opens contained in an open `complSupport i` satisfying `U i ⊔ complSupport i = ⊤`, and every point
`x : X` has an open neighbourhood `N` on which all `η i` outside a finite set `s` vanish while
`∑ i ∈ s, η i` restricts to the identity on all opens contained in `N`. -/
def IsPartitionOfUnity (F : X.Sheaf C) {ι : Type*} (U : ι → Opens X) (η : ι → (F ⟶ F)) : Prop :=
  ∃ complSupport : ι → Opens X,
    (∀ i, U i ⊔ complSupport i = ⊤) ∧
    (∀ i ⦃W : Opens X⦄, W ≤ complSupport i → (η i).hom.app (op W) = 0) ∧
    ∀ x : X, ∃ N : Opens X, x ∈ N ∧ ∃ s : Finset ι,
      (∀ i, i ∉ s → N ≤ complSupport i) ∧
      ∀ ⦃W : Opens X⦄, W ≤ N → ∑ i ∈ s, (η i).hom.app (op W) = 𝟙 (F.obj.obj (op W))

/-- Unfolding `TopCat.Sheaf.IsPartitionOfUnity`. -/
theorem isPartitionOfUnity_iff {F : X.Sheaf C} {ι : Type*} {U : ι → Opens X}
    {η : ι → (F ⟶ F)} :
    F.IsPartitionOfUnity U η ↔
      ∃ complSupport : ι → Opens X,
        (∀ i, U i ⊔ complSupport i = ⊤) ∧
        (∀ i ⦃W : Opens X⦄, W ≤ complSupport i → (η i).hom.app (op W) = 0) ∧
        ∀ x : X, ∃ N : Opens X, x ∈ N ∧ ∃ s : Finset ι,
          (∀ i, i ∉ s → N ≤ complSupport i) ∧
          ∀ ⦃W : Opens X⦄, W ≤ N → ∑ i ∈ s, (η i).hom.app (op W) = 𝟙 (F.obj.obj (op W)) :=
  Iff.rfl

/-- A *fine sheaf* on a topological space `X` is a sheaf admitting a sheaf partition of unity
subordinate to every open cover of `X`. -/
class IsFine (F : X.Sheaf C) : Prop where
  exists_isPartitionOfUnity :
    ∀ ⦃ι : Type w⦄ (U : ι → Opens X), ⨆ i, U i = ⊤ →
      ∃ η : ι → (F ⟶ F), F.IsPartitionOfUnity U η

/-- Unfolding `TopCat.Sheaf.IsFine`. -/
theorem isFine_iff (F : X.Sheaf C) :
    F.IsFine ↔ ∀ ⦃ι : Type w⦄ (U : ι → Opens X), ⨆ i, U i = ⊤ →
      ∃ η : ι → (F ⟶ F), F.IsPartitionOfUnity U η :=
  ⟨fun h ↦ h.exists_isPartitionOfUnity, fun h ↦ ⟨h⟩⟩

namespace IsPartitionOfUnity

/-- Enlarging the members of the cover preserves subordination of a sheaf partition of unity. -/
theorem mono {F : X.Sheaf C} {ι : Type*} {U U' : ι → Opens X} (hUU' : ∀ i, U i ≤ U' i)
    {η : ι → (F ⟶ F)} (hη : F.IsPartitionOfUnity U η) :
    F.IsPartitionOfUnity U' η := by
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  refine ⟨V, fun i ↦ eq_top_iff.2 ?_, hzero, hloc⟩
  calc (⊤ : Opens X) = U i ⊔ V i := (htop i).symm
    _ ≤ U' i ⊔ V i := sup_le_sup_right (hUU' i) _

/-- Reindexing a sheaf partition of unity along an equivalence of index types. -/
theorem reindex {F : X.Sheaf C} {ι κ : Type*} (e : ι ≃ κ) {U : κ → Opens X}
    {η : ι → (F ⟶ F)} (hη : F.IsPartitionOfUnity (U ∘ e) η) :
    F.IsPartitionOfUnity U (η ∘ e.symm) := by
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  refine ⟨V ∘ e.symm, fun k ↦ by simpa [Function.comp_apply] using htop (e.symm k),
    fun k W hW ↦ hzero (e.symm k) hW, fun x ↦ ?_⟩
  obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
  refine ⟨N, hxN, s.map e.toEmbedding, fun k hk ↦ ?_, fun W hW ↦ ?_⟩
  · refine hsV (e.symm k) fun hmem ↦ hk ?_
    exact Finset.mem_map.2 ⟨e.symm k, hmem, by simp⟩
  · rw [Finset.sum_map]
    simpa [Function.comp_apply] using hsum hW

/-- Conjugating a sheaf partition of unity along a retraction gives a sheaf partition of unity on
the retract. -/
theorem retract {F G : X.Sheaf C} (r : Retract F G) {ι : Type*} {U : ι → Opens X}
    {η : ι → (G ⟶ G)} (hη : G.IsPartitionOfUnity U η) :
    F.IsPartitionOfUnity U (fun i ↦ r.i ≫ η i ≫ r.r) := by
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  refine ⟨V, htop, fun i W hW ↦ ?_, fun x ↦ ?_⟩
  · rw [TopCat.Sheaf.comp_app, TopCat.Sheaf.comp_app, hzero i hW, zero_comp, comp_zero]
  · obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
    refine ⟨N, hxN, s, hsV, fun W hW ↦ ?_⟩
    simp_rw [TopCat.Sheaf.comp_app, ← Preadditive.comp_sum, ← Preadditive.sum_comp, hsum hW,
      Category.id_comp, ← TopCat.Sheaf.comp_app, r.retract, TopCat.Sheaf.id_app]

/-- Transporting a sheaf partition of unity across a sheaf isomorphism. -/
theorem of_iso {F G : X.Sheaf C} (e : F ≅ G) {ι : Type*} {U : ι → Opens X}
    {η : ι → (F ⟶ F)} (hη : F.IsPartitionOfUnity U η) :
    G.IsPartitionOfUnity U (fun i ↦ e.inv ≫ η i ≫ e.hom) :=
  hη.retract ⟨e.inv, e.hom, e.inv_hom_id⟩

/-- Applying an additive sheaf-preserving functor carries a sheaf partition of unity to a sheaf
partition of unity. -/
theorem sheafCompose {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    [(Opens.grothendieckTopology X).HasSheafCompose G] {F : X.Sheaf C} {ι : Type*}
    {U : ι → Opens X} {η : ι → (F ⟶ F)} (hη : F.IsPartitionOfUnity U η) :
    TopCat.Sheaf.IsPartitionOfUnity
      ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X) G).obj F) U
      (fun i ↦ (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) G).map (η i)) := by
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  -- `sheafCompose` is `ObjectProperty.lift` of postcomposition by `G`, so it acts sectionwise by
  -- `G.map`.
  have happ (i : ι) (W : Opens X) :
      ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X) G).map (η i)).hom.app (op W) =
        G.map ((η i).hom.app (op W)) := rfl
  refine ⟨V, htop, fun i W hW ↦
    (happ i W).trans ((congrArg G.map (hzero i hW)).trans (G.map_zero _ _)), fun x ↦ ?_⟩
  obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
  refine ⟨N, hxN, s, hsV, fun W hW ↦ ?_⟩
  have hsum' : ∑ i ∈ s, G.map ((η i).hom.app (op W)) = 𝟙 (G.obj (F.obj.obj (op W))) := by
    rw [← G.map_sum, hsum hW, CategoryTheory.Functor.map_id]
  exact (Finset.sum_congr rfl fun i _ ↦ happ i W).trans hsum'

end IsPartitionOfUnity

/-- A retract of a fine sheaf is fine. -/
theorem IsFine.of_retract {F G : X.Sheaf C} (r : Retract F G) [G.IsFine] : F.IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨η, hη⟩ := IsFine.exists_isPartitionOfUnity (F := G) U hU
    exact ⟨fun i ↦ r.i ≫ η i ≫ r.r, hη.retract r⟩

/-- Fineness is invariant under isomorphism of sheaves. -/
theorem IsFine.of_iso {F G : X.Sheaf C} (e : F ≅ G) [F.IsFine] : G.IsFine :=
  IsFine.of_retract ⟨e.inv, e.hom, e.inv_hom_id⟩

/-- A zero sheaf is fine: the zero endomorphisms form a partition of unity for every cover. -/
theorem IsFine.of_isZero {F : X.Sheaf C} (hF : IsZero F) : F.IsFine where
  exists_isPartitionOfUnity _ _ _ :=
    ⟨fun _ ↦ 0, fun _ ↦ ⊤, fun _ ↦ sup_top_eq _,
      fun _ W _ ↦ (sheafToPresheaf (Opens.grothendieckTopology X) C ⋙
        (evaluation (Opens X)ᵒᵖ C).obj (op W)).map_zero _ _,
      fun x ↦ ⟨⊤, Set.mem_univ x, ∅, fun _ _ ↦ le_top, fun W _ ↦ by
        let evW : X.Sheaf C ⥤ C :=
          sheafToPresheaf (Opens.grothendieckTopology X) C ⋙ (evaluation (Opens X)ᵒᵖ C).obj (op W)
        simp only [Finset.sum_empty]
        exact ((evW.map_zero F F).symm.trans
          (congrArg evW.map (hF.eq_of_src (0 : F ⟶ F) (𝟙 F)))).trans
          (evW.map_id F)⟩⟩

/-- Postcomposing a fine sheaf with an additive sheaf-preserving functor produces a fine sheaf. -/
instance isFine_sheafCompose {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    [(Opens.grothendieckTopology X).HasSheafCompose G] (F : X.Sheaf C) [F.IsFine] :
    TopCat.Sheaf.IsFine ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X) G).obj F) where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨η, hη⟩ := IsFine.exists_isPartitionOfUnity (F := F) U hU
    exact ⟨_, hη.sheafCompose G⟩

end Preadditive

end TopCat.Sheaf

/-! ### Godement functor, dimension shifting, and acyclicity -/

namespace TauCeti.Topology

section Abelian

variable {C : Type*} [Category.{u} C] [Abelian C] [HasColimits C] [HasProducts.{u} C]
  {X : TopCat.{u}}

/-- The Godement functor carries any sheaf partition of unity on `F` to a sheaf partition of unity
on `(godement C X).obj F`. -/
theorem isPartitionOfUnity_godement_map {F : X.Sheaf C} {ι : Type*}
    {U : ι → Opens X} {η : ι → (F ⟶ F)} (hη : F.IsPartitionOfUnity U η) :
    ((godement C X).obj F).IsPartitionOfUnity U
      (fun i ↦ (godement C X).map (η i)) := by
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  refine ⟨V, htop, fun i W hW ↦ godement_map_app_eq_zero_of_app_eq_zero (η i) (hzero i) hW,
    fun x ↦ ?_⟩
  obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
  refine ⟨N, hxN, s, hsV, fun W hW ↦ (TopCat.Sheaf.sum_sub_id_app_eq_zero_iff s _ W).1 ?_⟩
  have hδ : ∀ ⦃W' : Opens X⦄, W' ≤ N → ((∑ i ∈ s, η i) - 𝟙 F).hom.app (op W') = 0 :=
    fun W' hW' ↦ (TopCat.Sheaf.sum_sub_id_app_eq_zero_iff s η W').2 (hsum hW')
  have hGδ := godement_map_app_eq_zero_of_app_eq_zero ((∑ i ∈ s, η i) - 𝟙 F) hδ hW
  have hGmap : (godement C X).map ((∑ i ∈ s, η i) - 𝟙 F) =
      (∑ i ∈ s, (godement C X).map (η i)) - 𝟙 ((godement C X).obj F) := by
    rw [Functor.map_sub, Functor.map_sum, CategoryTheory.Functor.map_id]
  exact hGmap ▸ hGδ

/-- The Godement sheaf of a fine sheaf valued in an abelian category is fine. -/
instance isFine_godement_obj (F : X.Sheaf C) [F.IsFine] :
    ((godement C X).obj F).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨η, hη⟩ := TopCat.Sheaf.IsFine.exists_isPartitionOfUnity (F := F) U hU
    exact ⟨_, isPartitionOfUnity_godement_map hη⟩

end Abelian

variable {X : TopCat.{u}}

/-- Given a sheaf partition of unity on `F`, its induced endomorphisms on the cokernel sheaf
`Z¹(F) = cokernel ((toGodement AddCommGrpCat X).app F)` form a sheaf partition of unity with the
same support complements and local neighbourhoods, compatible with the Godement partition of
unity. -/
private theorem exists_cokernel_toGodement_partitionOfUnity
    {F : X.Sheaf AddCommGrpCat.{u}} {ι : Type*} {U : ι → Opens X} {η : ι → (F ⟶ F)}
    (hη : F.IsPartitionOfUnity U η) :
    let G := (godement AddCommGrpCat.{u} X).obj F
    let ιG := (toGodement AddCommGrpCat.{u} X).app F
    let Z := cokernel ιG
    let π := cokernel.π ιG
    let η' : ι → (G ⟶ G) := fun i ↦ (godement AddCommGrpCat.{u} X).map (η i)
    ∃ (ζ : ι → (Z ⟶ Z)) (V : ι → Opens X),
      (∀ i, π ≫ ζ i = η' i ≫ π) ∧
      (∀ i, U i ⊔ V i = ⊤) ∧
      (∀ i ⦃W : Opens X⦄, W ≤ V i → (η' i).hom.app (op W) = 0) ∧
      (∀ i ⦃W : Opens X⦄, W ≤ V i → (ζ i).hom.app (op W) = 0) ∧
      ∀ x : X, ∃ N : Opens X, x ∈ N ∧ ∃ s : Finset ι,
        (∀ i, i ∉ s → N ≤ V i) ∧
        (∀ ⦃W : Opens X⦄, W ≤ N → ∑ i ∈ s, (η' i).hom.app (op W) = 𝟙 (G.obj.obj (op W))) ∧
        ∀ ⦃W : Opens X⦄, W ≤ N → ∑ i ∈ s, (ζ i).hom.app (op W) = 𝟙 (Z.obj.obj (op W)) := by
  intro G ιG Z π η'
  obtain ⟨V, htop, hzero', hlocG⟩ := isPartitionOfUnity_godement_map hη
  let ζ : ι → (Z ⟶ Z) := fun i ↦ cokernel.desc ιG (η' i ≫ π) (by
    have hnat : ιG ≫ η' i = η i ≫ ιG :=
      ((toGodement AddCommGrpCat.{u} X).naturality (η i)).symm
    rw [← Category.assoc, hnat, Category.assoc, cokernel.condition, comp_zero])
  have hcomm (i : ι) : π ≫ ζ i = η' i ≫ π := cokernel.π_desc _ _ _
  have hzeroZ (i : ι) : ∀ ⦃W : Opens X⦄, W ≤ V i → (ζ i).hom.app (op W) = 0 :=
    TopCat.Sheaf.app_eq_zero_of_epi_comp π π (η' i) (ζ i) (hcomm i) (hzero' i)
  refine ⟨ζ, V, hcomm, htop, hzero', hzeroZ, fun x ↦ ?_⟩
  obtain ⟨N, hxN, s, hsV, hsumG⟩ := hlocG x
  have hδG : ∀ ⦃W : Opens X⦄, W ≤ N → ((∑ i ∈ s, η' i) - 𝟙 G).hom.app (op W) = 0 :=
    fun W hW ↦ (TopCat.Sheaf.sum_sub_id_app_eq_zero_iff s η' W).2 (hsumG hW)
  have hcommδ : π ≫ ((∑ i ∈ s, ζ i) - 𝟙 Z) = ((∑ i ∈ s, η' i) - 𝟙 G) ≫ π := by
    rw [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_sum, Preadditive.sum_comp,
      Category.comp_id, Category.id_comp]
    exact congrArg (· - π) (Finset.sum_congr rfl fun i _ ↦ hcomm i)
  have hδZ : ∀ ⦃W : Opens X⦄, W ≤ N → ((∑ i ∈ s, ζ i) - 𝟙 Z).hom.app (op W) = 0 :=
    TopCat.Sheaf.app_eq_zero_of_epi_comp π π _ _ hcommδ hδG
  exact ⟨N, hxN, s, hsV, hsumG,
    fun W hW ↦ (TopCat.Sheaf.sum_sub_id_app_eq_zero_iff s ζ W).1 (hδZ hW)⟩

/-- The cokernel `Z¹(F)` of the canonical embedding `F ⟶ G⁰(F)` of a fine abelian sheaf into its
Godement sheaf is again fine. -/
instance isFine_cokernel_toGodement_app (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] :
    (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨η, hη⟩ := TopCat.Sheaf.IsFine.exists_isPartitionOfUnity (F := F) U hU
    obtain ⟨ζ, V, -, htop, -, hzeroZ, hloc⟩ := exists_cokernel_toGodement_partitionOfUnity hη
    exact ⟨ζ, V, htop, hzeroZ, fun x ↦ by
      obtain ⟨N, hxN, s, hsV, -, hsumZ⟩ := hloc x
      exact ⟨N, hxN, s, hsV, hsumZ⟩⟩

/-- If `π ≫ ζ = φ ≫ π` for morphisms of abelian sheaves, `U ⊔ V = ⊤`, both `φ` and `ζ` vanish on
`V`, and a global section `g` of `G` lifts `z|_U` along `π` after restriction to `U`, then
`π(φ(g)) = ζ(z)` globally. -/
private theorem app_top_apply_eq_of_sup_eq_top {G Z : X.Sheaf AddCommGrpCat.{u}}
    (π : G ⟶ Z) (φ : G ⟶ G) (ζ : Z ⟶ Z) (hcomm : π ≫ ζ = φ ≫ π)
    {U V : Opens X} (htop : U ⊔ V = ⊤)
    (hφ : φ.hom.app (op V) = 0) (hζ : ζ.hom.app (op V) = 0)
    (g : G.obj.obj (op ⊤)) (g₀ : G.obj.obj (op U)) (z : Z.obj.obj (op ⊤))
    (hg : G.obj.map (homOfLE (le_top : U ≤ ⊤)).op g = g₀)
    (hg₀ : π.hom.app (op U) g₀ = Z.obj.map (homOfLE (le_top : U ≤ ⊤)).op z) :
    π.hom.app (op ⊤) (φ.hom.app (op ⊤) g) = ζ.hom.app (op ⊤) z := by
  refine Z.eq_of_locally_eq₂ (homOfLE (le_top : U ≤ ⊤)) (homOfLE (le_top : V ≤ ⊤))
    htop.ge _ _ ?_ ?_
  · rw [← NatTrans.naturality_apply π.hom, ← NatTrans.naturality_apply φ.hom, hg,
      ← ConcreteCategory.comp_apply, ← TopCat.Sheaf.comp_app, ← hcomm,
      TopCat.Sheaf.comp_app, ConcreteCategory.comp_apply, hg₀,
      NatTrans.naturality_apply ζ.hom]
  · simp [← NatTrans.naturality_apply π.hom, ← NatTrans.naturality_apply φ.hom,
      ← NatTrans.naturality_apply ζ.hom, hφ, hζ]

/-- When `F` is a fine abelian sheaf, global sections of `G⁰(F)` map onto global sections of
`Z¹(F) = cokernel ((toGodement AddCommGrpCat X).app F)`. -/
theorem surjective_cokernel_π_toGodement_top (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] :
    Function.Surjective
      ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤)) := by
  let G := (godement AddCommGrpCat.{u} X).obj F
  let ιG := (toGodement AddCommGrpCat.{u} X).app F
  let Z := cokernel ιG
  let π := cokernel.π ιG
  intro z
  -- Lift `z` locally near every point `x : X`, then extend each local lift to `⊤` by flasqueness.
  choose U _ hxU _ g₀ hg₀ using fun x : X ↦
    TopCat.Sheaf.exists_mem_lift_of_epi (B := Set.univ)
      (fun _ _ V _ y hy ↦ ⟨V, Set.mem_univ _, hy, le_rfl⟩)
      π (Set.mem_univ (⊤ : Opens X)) z x (Set.mem_univ x)
  have hflasque : G.IsFlasque := isFlasque_godement_obj AddCommGrpCat.{u} X F
  choose g hg using fun x : X ↦
    (AddCommGrpCat.epi_iff_surjective (G.obj.map (homOfLE (le_top : U x ≤ ⊤)).op)).1
      inferInstance (g₀ x)
  have hU_top : ⨆ x : X, U x = ⊤ :=
    eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxU x⟩
  obtain ⟨η, hη⟩ := TopCat.Sheaf.IsFine.exists_isPartitionOfUnity (F := F) U hU_top
  obtain ⟨ζ, V, hcomm, htop, hzeroG, hzeroZ, hloc⟩ := exists_cokernel_toGodement_partitionOfUnity hη
  let η' : X → (G ⟶ G) := fun x ↦ (godement AddCommGrpCat.{u} X).map (η x)
  let a : X → G.obj.obj (op ⊤) := fun x ↦ (η' x).hom.app (op ⊤) (g x)
  have hπa (x : X) : π.hom.app (op ⊤) (a x) = (ζ x).hom.app (op ⊤) z :=
    app_top_apply_eq_of_sup_eq_top π (η' x) (ζ x) (hcomm x) (htop x)
      (hzeroG x le_rfl) (hzeroZ x le_rfl) (g x) (g₀ x) z (hg x) (hg₀ x)
  choose N hyN S hSV _ hsumZ using hloc
  have hN_top : ⨆ y : X, N y = ⊤ := eq_top_iff.2 fun y _ ↦ Opens.mem_iSup.2 ⟨y, hyN y⟩
  obtain ⟨b, hb⟩ := TopCat.Sheaf.exists_gluing_finset_sum G V a
    (fun x W _ hWV ↦ by
      dsimp only [a]
      rw [← NatTrans.naturality_apply (η' x).hom, hzeroG x hWV]
      simp)
    N (fun _ ↦ le_top) hN_top.ge S hSV
  refine ⟨b, Z.eq_of_locally_eq' N ⊤ (fun y ↦ homOfLE le_top) hN_top.ge _ _ fun y ↦ ?_⟩
  rw [← NatTrans.naturality_apply π.hom, hb y, map_sum]
  have hterm (x : X) :
      π.hom.app (op (N y)) (G.obj.map (homOfLE le_top).op (a x)) =
        (ζ x).hom.app (op (N y)) (Z.obj.map (homOfLE le_top).op z) := by
    rw [NatTrans.naturality_apply π.hom, hπa x, ← NatTrans.naturality_apply (ζ x).hom]
  simp_rw [hterm]
  have hsum_apply :
      ∑ x ∈ S y, (ζ x).hom.app (op (N y)) (Z.obj.map (homOfLE le_top).op z) =
        (∑ x ∈ S y, (ζ x).hom.app (op (N y))) (Z.obj.map (homOfLE le_top).op z) :=
    (map_sum ((AddMonoidHom.eval (Z.obj.map (homOfLE le_top).op z)).comp
        AddCommGrpCat.homAddEquiv.toAddMonoidHom)
      (fun x ↦ (ζ x).hom.app (op (N y))) (S y)).symm
  rw [hsum_apply, hsumZ y le_rfl, AddCommGrpCat.id_apply]

/-- Dimension-shifting induction along `0 ⟶ F ⟶ G⁰(F) ⟶ Z¹(F) ⟶ 0`: every fine abelian sheaf has
vanishing cohomology `Sheaf.H` in positive degrees. -/
private theorem subsingleton_H_succ_of_isFine_aux (n : ℕ) :
    ∀ (F : X.Sheaf AddCommGrpCat.{u}), F.IsFine →
      Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  induction n with
  | zero =>
    intro F _
    let ιG := (toGodement AddCommGrpCat.{u} X).app F
    have hflasque : ((godement AddCommGrpCat.{u} X).obj F).IsFlasque :=
      isFlasque_godement_obj AddCommGrpCat.{u} X F
    have hS := TauCeti.cokernelSequence_shortExact ιG
    have : Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F 1 (⊤ : Opens X)) :=
      Sheaf.H'.subsingleton_X₁_one hS (⊤ : Opens X)
        (surjective_cokernel_π_toGodement_top F)
        (subsingleton_H'_succ_of_isFlasque ((godement AddCommGrpCat.{u} X).obj F) 0 (⊤ : Opens X))
    exact (F.cohomologyPresheafObjIsoH 1 isTerminalTop).symm.addCommGroupIsoToAddEquiv
      |>.toEquiv.subsingleton
  | succ n ih =>
    intro F _
    let ιG := (toGodement AddCommGrpCat.{u} X).app F
    have hflasque : ((godement AddCommGrpCat.{u} X).obj F).IsFlasque :=
      isFlasque_godement_obj AddCommGrpCat.{u} X F
    have hS := TauCeti.cokernelSequence_shortExact ιG
    exact Sheaf.H.subsingleton_X₁ hS (n + 1) (n + 2) rfl
      (ih (cokernel ιG) inferInstance)
      (subsingleton_H_succ_of_isFlasque ((godement AddCommGrpCat.{u} X).obj F) (n + 1))

end TauCeti.Topology

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- Every fine sheaf of abelian groups has vanishing cohomology `Sheaf.H` in every positive degree
`n + 1`. -/
instance subsingleton_H_succ_of_isFine (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) :=
  TauCeti.Topology.subsingleton_H_succ_of_isFine_aux n F inferInstance

namespace IsFine

/-- Every fine sheaf of abelian groups has vanishing cohomology `Sheaf.H` in every positive degree
`0 < n`. -/
theorem subsingleton_H_of_pos {F : X.Sheaf AddCommGrpCat.{u}} (hF : F.IsFine) (n : ℕ)
    (hn : 0 < n) : Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have : F.IsFine := hF
  exact subsingleton_H_succ_of_isFine F k

/-- Every fine sheaf of abelian groups has vanishing cohomology `Sheaf.H' _ _ ⊤` over the whole
space in every positive degree `0 < n`. -/
theorem subsingleton_H'_top_of_pos {F : X.Sheaf AddCommGrpCat.{u}} (hF : F.IsFine) (n : ℕ)
    (hn : 0 < n) : Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F n (⊤ : Opens X)) := by
  have := hF.subsingleton_H_of_pos n hn
  exact (F.cohomologyPresheafObjIsoH n isTerminalTop).addCommGroupIsoToAddEquiv
    |>.toEquiv.subsingleton

/-- In a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of abelian sheaves with `F₁` fine, every
global section of `F₃` lifts to a global section of `F₂`. -/
theorem g_hom_app_top_surjective
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hF₁ : IsFine S.X₁) :
    Function.Surjective (S.g.hom.app (op (⊤ : Opens X))) :=
  Sheaf.H'.g_hom_app_surjective hS (⊤ : Opens X) (hF₁.subsingleton_H'_top_of_pos 1 Nat.zero_lt_one)

/-- In a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of abelian sheaves with `F₁` fine, the
sequence of global sections `0 ⟶ F₁(⊤) ⟶ F₂(⊤) ⟶ F₃(⊤) ⟶ 0` is short exact. -/
theorem shortExact_map_sheafSections_top
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hF₁ : IsFine S.X₁) :
    (S.map (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))).ShortExact :=
  Sheaf.H'.shortExact_map_sheafSections hS (⊤ : Opens X)
    (hF₁.subsingleton_H'_top_of_pos 1 Nat.zero_lt_one)

/-- If the restriction `U.sheafRestrict.obj F` of an abelian sheaf `F` to an open subset `U` is
fine (an open subset of a space with partitions of unity need not inherit paracompactness unless
assumed separately), then `F` has vanishing cohomology over `U` in every positive degree. -/
theorem subsingleton_H'_of_sheafRestrict_of_pos {F : X.Sheaf AddCommGrpCat.{u}} {U : Opens X}
    (hFU : IsFine (X := TopCat.of U) (U.sheafRestrict.obj F)) (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F n U) := by
  have := hFU.subsingleton_H_of_pos n hn
  exact (U.cohomologyPresheafObjIsoSheafRestrictH F n).addCommGroupIsoToAddEquiv
    |>.toEquiv.subsingleton

/-- Every fine sheaf of `R`-modules has vanishing right derived global sections in degree
`n + 1`. -/
theorem isZero_rightDerived_Γ_succ {R : Type u} [CommRing R]
    {F : X.Sheaf (ModuleCat.{u} R)} (hF : F.IsFine) (n : ℕ) :
    IsZero (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived (n + 1)).obj
      F) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let FAb := (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) G).obj F
  have : F.IsFine := hF
  have hAb : IsZero (G.obj (((Sheaf.Γ _ (ModuleCat.{u} R)).rightDerived (n + 1)).obj F)) :=
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (Sheaf.H FAb (n + 1)))).of_iso
      ((TauCeti.Topology.moduleCohomologyForgetComparison X R (n + 1)).app F)
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact hAb.eq_of_src _ _

/-- Every fine sheaf of `R`-modules has vanishing right derived global sections in every positive
degree `0 < n`. -/
theorem isZero_rightDerived_Γ_of_pos {R : Type u} [CommRing R]
    {F : X.Sheaf (ModuleCat.{u} R)} (hF : F.IsFine) (n : ℕ) (hn : 0 < n) :
    IsZero (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).obj F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact hF.isZero_rightDerived_Γ_succ k

end IsFine

/-- If the restriction `U.sheafRestrict.obj F` of an abelian sheaf `F` to an open subset `U` is
fine, then `F` has vanishing cohomology over `U` in degree `n + 1`. -/
instance subsingleton_H'_succ_of_isFine_sheafRestrict (F : X.Sheaf AddCommGrpCat.{u})
    (U : Opens X) [IsFine (X := TopCat.of U) (U.sheafRestrict.obj F)] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) :=
  IsFine.subsingleton_H'_of_sheafRestrict_of_pos (F := F) (U := U) inferInstance (n + 1)
    (Nat.succ_pos n)

end TopCat.Sheaf
