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
import TauCeti.Topology.Sheaves.ClosedEmbedding
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
every positive degree (`TopCat.Sheaf.IsFine.subsingleton_H_succ`,
`TopCat.Sheaf.IsFine.subsingleton_H_of_pos`). For sheaves of modules over a commutative ring `R`,
fineness likewise forces the right derived global-section functors `RⁿΓ(F)` to vanish in every
positive degree (`TauCeti.Topology.isZero_rightDerived_Γ_succ_of_isFine`).

## Mathematical overview

Embed an abelian sheaf `F` into its Godement sheaf `G⁰(F) = (godement AddCommGrpCat X).obj F`
(`TauCeti.Topology.toGodement`), with cokernel sheaf `Z¹(F)`. The Godement functor is additive and
local, so any sheaf partition of unity on `F` pushes forward to `G⁰(F)` and hence, because open
restriction of sheaves preserves cokernels, to `Z¹(F)`. In particular `Z¹(F)` is again fine when
`F` is (`TauCeti.Topology.isFine_cokernel_toGodement_app`).

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

* `TopCat.Sheaf.IsFine.of_retract`, `TopCat.Sheaf.IsFine.of_iso`, `TopCat.Sheaf.isFine_biprod`:
  fineness is preserved by retracts, isomorphisms, and binary biproducts.
* `TopCat.Sheaf.isFine_sheafCompose`: postcomposing with an additive sheaf-preserving functor (such
  as forgetting an `R`-module structure) preserves fineness.
* `TopCat.Sheaf.isFine_pushforward_of_isClosedEmbedding` and
  `TopCat.Sheaf.isFine_skyscraperSheaf`: pushforward of abelian sheaves along a closed embedding
  preserves fineness, and skyscraper sheaves on `T₁` spaces are fine.
* `TauCeti.Topology.isFine_godement_obj` and `TauCeti.Topology.isFine_cokernel_toGodement_app`:
  for a fine abelian sheaf `F`, both `G⁰(F)` and `Z¹(F)` are fine.
* `TopCat.Sheaf.IsFine.subsingleton_H_succ` and `TopCat.Sheaf.IsFine.subsingleton_H_of_pos`:
  every fine abelian sheaf has vanishing cohomology `Sheaf.H` in positive degrees.
* `TopCat.Sheaf.IsFine.g_hom_app_top_surjective` and
  `TopCat.Sheaf.IsFine.shortExact_map_sheafSections_top`: global sections are exact on short exact
  sequences with fine kernel.
* `TauCeti.Topology.isZero_rightDerived_Γ_succ_of_isFine`: every fine sheaf of `R`-modules has
  vanishing derived global sections in positive degrees.

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
  · have hcomp : (r.i ≫ η i ≫ r.r).hom.app (op W) =
        r.i.hom.app (op W) ≫ (η i).hom.app (op W) ≫ r.r.hom.app (op W) := rfl
    rw [hcomp, hzero i hW, zero_comp, comp_zero]
  · obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
    refine ⟨N, hxN, s, hsV, fun W hW ↦ ?_⟩
    have hcomp (i : ι) : (r.i ≫ η i ≫ r.r).hom.app (op W) =
        r.i.hom.app (op W) ≫ (η i).hom.app (op W) ≫ r.r.hom.app (op W) := rfl
    simp_rw [hcomp, ← Preadditive.comp_sum, ← Preadditive.sum_comp, hsum hW, Category.id_comp]
    exact (NatTrans.comp_app r.i.hom r.r.hom (op W)).symm.trans
      (congrArg (fun φ : F ⟶ F ↦ φ.hom.app (op W)) r.retract)

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

/-- Diagonal action of two sheaf partitions of unity gives a sheaf partition of unity on the binary
biproduct `F ⊞ G`. -/
theorem biprod [HasBinaryBiproducts (X.Sheaf C)] {F G : X.Sheaf C} {ι : Type*}
    {U : ι → Opens X} {η₁ : ι → (F ⟶ F)} {η₂ : ι → (G ⟶ G)}
    (h₁ : F.IsPartitionOfUnity U η₁) (h₂ : G.IsPartitionOfUnity U η₂) :
    (F ⊞ G).IsPartitionOfUnity U (fun i ↦ Limits.biprod.map (η₁ i) (η₂ i)) := by
  classical
  obtain ⟨V₁, htop₁, hzero₁, hloc₁⟩ := h₁
  obtain ⟨V₂, htop₂, hzero₂, hloc₂⟩ := h₂
  have hmap (i : ι) : Limits.biprod.map (η₁ i) (η₂ i) =
      Limits.biprod.fst ≫ η₁ i ≫ Limits.biprod.inl +
        Limits.biprod.snd ≫ η₂ i ≫ Limits.biprod.inr := by
    apply Limits.biprod.hom_ext' <;> simp
  have happ (i : ι) (W : Opens X) : (Limits.biprod.map (η₁ i) (η₂ i)).hom.app (op W) =
      (Limits.biprod.fst : F ⊞ G ⟶ F).hom.app (op W) ≫ (η₁ i).hom.app (op W) ≫
          (Limits.biprod.inl : F ⟶ F ⊞ G).hom.app (op W) +
        (Limits.biprod.snd : F ⊞ G ⟶ G).hom.app (op W) ≫ (η₂ i).hom.app (op W) ≫
          (Limits.biprod.inr : G ⟶ F ⊞ G).hom.app (op W) := by
    rw [hmap]
    rfl
  refine ⟨fun i ↦ V₁ i ⊓ V₂ i, fun i ↦ ?_, fun i W hW ↦ ?_, fun x ↦ ?_⟩
  · rw [sup_inf_left, htop₁ i, htop₂ i, top_inf_eq]
  · rw [happ, hzero₁ i (hW.trans inf_le_left), hzero₂ i (hW.trans inf_le_right)]
    simp
  · obtain ⟨N₁, hxN₁, s₁, hsV₁, hsum₁⟩ := hloc₁ x
    obtain ⟨N₂, hxN₂, s₂, hsV₂, hsum₂⟩ := hloc₂ x
    refine ⟨N₁ ⊓ N₂, ⟨hxN₁, hxN₂⟩, s₁ ∪ s₂, fun i hi ↦ ?_, fun W hW ↦ ?_⟩
    · exact le_inf (inf_le_left.trans (hsV₁ i fun h ↦ hi (Finset.mem_union_left _ h)))
        (inf_le_right.trans (hsV₂ i fun h ↦ hi (Finset.mem_union_right _ h)))
    · have hsum₁' : ∑ i ∈ s₁ ∪ s₂, (η₁ i).hom.app (op W) = 𝟙 (F.obj.obj (op W)) := by
        rw [← Finset.sum_subset Finset.subset_union_left fun i _ hi ↦
          hzero₁ i (hW.trans (inf_le_left.trans (hsV₁ i hi)))]
        exact hsum₁ (hW.trans inf_le_left)
      have hsum₂' : ∑ i ∈ s₁ ∪ s₂, (η₂ i).hom.app (op W) = 𝟙 (G.obj.obj (op W)) := by
        rw [← Finset.sum_subset Finset.subset_union_right fun i _ hi ↦
          hzero₂ i (hW.trans (inf_le_right.trans (hsV₂ i hi)))]
        exact hsum₂ (hW.trans inf_le_right)
      simp_rw [happ, Finset.sum_add_distrib, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
        hsum₁', hsum₂', Category.id_comp]
      exact congrArg (fun φ : F ⊞ G ⟶ F ⊞ G ↦ φ.hom.app (op W)) Limits.biprod.total

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
    ⟨fun _ ↦ 0, fun _ ↦ ⊤, fun _ ↦ sup_top_eq _, fun _ _ _ ↦ rfl,
      fun x ↦ ⟨⊤, Set.mem_univ x, ∅, fun _ _ ↦ le_top, fun W _ ↦ by
        simp only [Finset.sum_empty]
        exact congrArg (fun φ : F ⟶ F ↦ φ.hom.app (op W)) (hF.eq_of_src (0 : F ⟶ F) (𝟙 F))⟩⟩

/-- Postcomposing a fine sheaf with an additive sheaf-preserving functor produces a fine sheaf. -/
instance isFine_sheafCompose {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    [(Opens.grothendieckTopology X).HasSheafCompose G] (F : X.Sheaf C) [F.IsFine] :
    TopCat.Sheaf.IsFine ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X) G).obj F) where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨η, hη⟩ := IsFine.exists_isPartitionOfUnity (F := F) U hU
    exact ⟨_, hη.sheafCompose G⟩

/-- A binary biproduct of fine sheaves is fine. -/
instance isFine_biprod [HasBinaryBiproducts (X.Sheaf C)] (F G : X.Sheaf C)
    [F.IsFine] [G.IsFine] : (F ⊞ G).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨η₁, h₁⟩ := IsFine.exists_isPartitionOfUnity (F := F) U hU
    obtain ⟨η₂, h₂⟩ := IsFine.exists_isPartitionOfUnity (F := G) U hU
    exact ⟨_, h₁.biprod h₂⟩

end Preadditive

/-! ### Closed embeddings and skyscraper sheaves -/

section AddCommGrpCat

variable {X Y : TopCat.{u}}

/-- Pushforward of a sheaf partition of unity along a closed embedding. Outside the closed image,
the pushed-forward abelian sheaf vanishes, so the empty sum acts as the identity there. -/
theorem IsPartitionOfUnity.pushforward_of_isClosedEmbedding (f : X ⟶ Y)
    (hf : _root_.Topology.IsClosedEmbedding f) {F : X.Sheaf AddCommGrpCat.{u}} {ι : Type*}
    {U : ι → Opens Y} {η : ι → (F ⟶ F)}
    (hη : F.IsPartitionOfUnity (fun i ↦ (Opens.map f).obj (U i)) η) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).IsPartitionOfUnity U
      (fun i ↦ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (η i)) := by
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  let VY : ι → Opens Y := fun i ↦
    ⟨(f '' (V i : Set X)ᶜ)ᶜ, (hf.isClosedMap _ (V i).isOpen.isClosed_compl).isOpen_compl⟩
  have hmap_le (i : ι) : (Opens.map f).obj (VY i) ≤ V i := fun x hx ↦
    Set.notMem_compl_iff.1 fun hxV ↦ hx ⟨x, hxV, rfl⟩
  refine ⟨VY, fun i ↦ eq_top_iff.2 fun y _ ↦ ?_, fun i W hW ↦ ?_, fun y ↦ ?_⟩
  · by_cases hy : y ∈ VY i
    · exact Or.inr hy
    · obtain ⟨x, hxV, rfl⟩ := Set.notMem_compl_iff.1 hy
      have hx : x ∈ (Opens.map f).obj (U i) ⊔ V i := (htop i).symm ▸ Set.mem_univ x
      exact Or.inl (hx.resolve_right hxV)
  · exact hzero i (((Opens.map f).monotone hW).trans (hmap_le i))
  · by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
      obtain ⟨M₀, hM₀_open, hM₀_eq⟩ := hf.isInducing.isOpen_iff.1 N.isOpen
      let NY : Opens Y := ⟨M₀, hM₀_open⟩
      have hNY : (Opens.map f).obj NY = N := Opens.ext hM₀_eq
      have hxNY : f x ∈ NY := Set.mem_preimage.1 (hM₀_eq.symm ▸ hxN)
      refine ⟨NY, hxNY, s, fun i hi z hz ↦ ?_, fun W hW ↦ ?_⟩
      · rintro ⟨x', hx'V, rfl⟩
        have hx'N : x' ∈ (N : Set X) := hM₀_eq ▸ hz
        exact hx'V (hsV i hi hx'N)
      · exact hsum (hNY ▸ (Opens.map f).monotone hW)
    · let NY : Opens Y := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
      refine ⟨NY, hy, ∅, fun i _ z hz ↦ ?_, fun W hW ↦ ?_⟩
      · rintro ⟨x', _, rfl⟩
        exact hz ⟨x', rfl⟩
      · have hW_bot : (Opens.map f).obj W = ⊥ :=
          eq_bot_iff.2 fun x hx ↦ False.elim (hW hx ⟨x, rfl⟩)
        simp only [Finset.sum_empty]
        exact (F.isTerminalOfEqEmpty hW_bot).isZero.eq_of_src _ _

/-- Pushforward of abelian sheaves along a closed embedding preserves fineness. -/
theorem isFine_pushforward_of_isClosedEmbedding (f : X ⟶ Y)
    (hf : _root_.Topology.IsClosedEmbedding f) (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    have hU' : ⨆ i, (Opens.map f).obj (U i) = ⊤ := eq_top_iff.2 fun x _ ↦ by
      have hx : f x ∈ ⨆ i, U i := hU.symm ▸ Set.mem_univ (f x)
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
      exact Opens.mem_iSup.2 ⟨i, hi⟩
    obtain ⟨η, hη⟩ := IsFine.exists_isPartitionOfUnity (F := F) _ hU'
    exact ⟨_, hη.pushforward_of_isClosedEmbedding f hf⟩

/-- On a `T₁` space, every skyscraper sheaf of abelian groups is fine. -/
instance isFine_skyscraperSheaf [T1Space X] (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]
    (A : AddCommGrpCat.{u}) : (skyscraperSheaf p₀ A).IsFine where
  exists_isPartitionOfUnity ι U hU := by
    classical
    have hp₀_top : p₀ ∈ ⨆ i, U i := hU.symm ▸ Set.mem_univ p₀
    obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 hp₀_top
    let η : ι → (skyscraperSheaf p₀ A ⟶ skyscraperSheaf p₀ A) :=
      fun i ↦ if i = i₀ then 𝟙 _ else 0
    let V : ι → Opens X :=
      fun i ↦ if i = i₀ then ⟨{p₀}ᶜ, isClosed_singleton.isOpen_compl⟩ else ⊤
    refine ⟨η, V, fun i ↦ ?_, fun i W hW ↦ ?_, fun x ↦ ⟨⊤, Set.mem_univ x, {i₀}, ?_, ?_⟩⟩
    · by_cases hi : i = i₀
      · subst hi
        refine eq_top_iff.2 fun x _ ↦ ?_
        by_cases hx : x = p₀
        · exact Or.inl (hx ▸ hi₀)
        · exact Or.inr (by simpa [V] using hx)
      · simp [V, hi]
    · by_cases hi : i = i₀
      · subst hi
        have hp₀ : p₀ ∉ W := fun hp ↦ by
          have : p₀ ∈ ({p₀}ᶜ : Set X) := by simpa [V] using hW hp
          exact this rfl
        have hzeroW : IsZero ((skyscraperSheaf p₀ A).obj.obj (op W)) :=
          (isZero_zero AddCommGrpCat.{u}).of_iso
            ((eqToIso ((skyscraperSheaf_obj_obj p₀ A (op W)).trans (ite_eq_right hp₀))).trans
              HasZeroObject.zeroIsoTerminal.symm)
        exact hzeroW.eq_of_src _ _
      · simp [η, hi]
    · intro i hi
      simp [V, Finset.mem_singleton.not.1 hi]
    · intro W _
      simp [η]

end AddCommGrpCat

end TopCat.Sheaf

/-! ### Godement functor, dimension shifting, and acyclicity -/

namespace TopCat.Presheaf

/-- A morphism of presheaves valued in a preadditive category that vanishes on all opens inside `V`
induces the zero map on stalks at every point of `V`. -/
theorem stalkFunctor_map_eq_zero_of_app_eq_zero
    {C : Type*} [Category.{v} C] [Preadditive C] [HasColimits.{v} C]
    {X : TopCat.{v}} {F G : X.Presheaf C} (α : F ⟶ G) {V : Opens X}
    (hα : ∀ ⦃W : Opens X⦄, W ≤ V → α.app (op W) = 0) {x : X} (hx : x ∈ V) :
    (TopCat.Presheaf.stalkFunctor C x).map α = 0 := by
  refine F.stalk_hom_ext fun U hxU ↦ ?_
  have hxUV : x ∈ U ⊓ V := ⟨hxU, hx⟩
  have hUV : F.germ (U ⊓ V) x hxUV ≫ (TopCat.Presheaf.stalkFunctor C x).map α = 0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ (U ⊓ V) x hxUV α).trans
      ((congrArg (· ≫ G.germ (U ⊓ V) x hxUV) (hα inf_le_right)).trans zero_comp)
  have hres := F.germ_res_assoc (homOfLE inf_le_left : U ⊓ V ⟶ U) x hxUV
    ((TopCat.Presheaf.stalkFunctor C x).map α)
  exact (hres.symm.trans ((congrArg (_ ≫ ·) hUV).trans comp_zero)).trans comp_zero.symm

end TopCat.Presheaf

namespace TauCeti.Topology

variable {X : TopCat.{u}}

/-- Each skyscraper-sheaf functor valued in abelian groups is additive, being a right adjoint. -/
instance additive_skyscraperSheafFunctor (x : X) [∀ U : Opens X, Decidable (x ∈ U)] :
    (skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The Godement functor on sheaves of abelian groups is additive. -/
instance additive_godement : (godement AddCommGrpCat.{u} X).Additive where
  map_add {F G} α β := by
    classical
    let πG (x : X) : (godement AddCommGrpCat.{u} X).obj G ⟶
        (skyscraperSheafFunctor x).obj (G.presheaf.stalk x) :=
      Pi.π (fun y ↦ (skyscraperSheafFunctor y).obj (G.presheaf.stalk y)) x
    let πF (x : X) : (godement AddCommGrpCat.{u} X).obj F ⟶
        (skyscraperSheafFunctor x).obj (F.presheaf.stalk x) :=
      Pi.π (fun y ↦ (skyscraperSheafFunctor y).obj (F.presheaf.stalk y)) x
    refine Pi.hom_ext _ _ fun x ↦ ?_
    have hstalk : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (α + β).hom =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α.hom +
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map β.hom :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_add
    have hsky : (skyscraperSheafFunctor x).map
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (α + β).hom) =
        (skyscraperSheafFunctor x).map
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α.hom) +
        (skyscraperSheafFunctor x).map
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map β.hom) :=
      (congrArg (skyscraperSheafFunctor x).map hstalk).trans
        (skyscraperSheafFunctor x).map_add
    have hlhs := (godement_map_π AddCommGrpCat.{u} X (α + β) x).trans
      ((congrArg (πF x ≫ ·) hsky).trans (Preadditive.comp_add _ _ _ _ _ _))
    have hrhs := (Preadditive.add_comp _ _ _
        ((godement AddCommGrpCat.{u} X).map α)
        ((godement AddCommGrpCat.{u} X).map β) (πG x)).trans
      (congrArg₂ (· + ·) (godement_map_π AddCommGrpCat.{u} X α x)
        (godement_map_π AddCommGrpCat.{u} X β x))
    exact hlhs.trans hrhs.symm

/-- Locality of the Godement functor: if `α : F ⟶ G` vanishes on all opens inside `V`, then so
does `(godement AddCommGrpCat X).map α`. -/
theorem godement_map_app_eq_zero_of_app_eq_zero
    {F G : X.Sheaf AddCommGrpCat.{u}} (α : F ⟶ G) {V : Opens X}
    (hα : ∀ ⦃W : Opens X⦄, W ≤ V → α.hom.app (op W) = 0) ⦃W : Opens X⦄ (hW : W ≤ V) :
    ((godement AddCommGrpCat.{u} X).map α).hom.app (op W) = 0 := by
  classical
  let fam : X → X.Sheaf AddCommGrpCat.{u} :=
    fun y ↦ (skyscraperSheafFunctor y).obj (G.presheaf.stalk y)
  let hlim₁ := isLimitOfPreserves (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
    (limit.isLimit (Discrete.functor fam))
  let hlim₂ := isLimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W)) hlim₁
  refine hlim₂.hom_ext fun ⟨y⟩ ↦ ?_
  let πW := (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W)).mapCone
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapCone
      (limit.cone (Discrete.functor fam)))).π.app ⟨y⟩
  have hzero_rhs :
      (0 : ((godement AddCommGrpCat.{u} X).obj F).obj.obj (op W) ⟶
        ((godement AddCommGrpCat.{u} X).obj G).obj.obj (op W)) ≫ πW = 0 := zero_comp
  have hlhs : ((godement AddCommGrpCat.{u} X).map α).hom.app (op W) ≫ πW =
      ((godement AddCommGrpCat.{u} X).map α ≫ Pi.π fam y).hom.app (op W) := rfl
  refine (hlhs.trans ?_).trans hzero_rhs.symm
  by_cases hyW : y ∈ W
  · have hstalk := TopCat.Presheaf.stalkFunctor_map_eq_zero_of_app_eq_zero α.hom hα (hW hyW)
    have hsky : (skyscraperSheafFunctor y).map
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map α.hom) = 0 :=
      (congrArg (skyscraperSheafFunctor y).map hstalk).trans
        ((skyscraperSheafFunctor y).map_zero _ _)
    have hπ : (godement AddCommGrpCat.{u} X).map α ≫ Pi.π fam y = 0 :=
      (godement_map_π AddCommGrpCat.{u} X α y).trans ((congrArg (_ ≫ ·) hsky).trans comp_zero)
    rw [hπ]
    rfl
  · have hzeroW : IsZero ((fam y).obj.obj (op W)) :=
      (isZero_zero AddCommGrpCat.{u}).of_iso
        ((eqToIso ((skyscraperSheaf_obj_obj y (G.presheaf.stalk y) (op W)).trans
          (ite_eq_right hyW))).trans HasZeroObject.zeroIsoTerminal.symm)
    exact hzeroW.eq_of_tgt _ _

/-- For a finite family of sheaf endomorphisms `η`, `(∑ i ∈ s, η i - 𝟙 F)` vanishes at `W` iff
`∑ i ∈ s, (η i).hom.app (op W) = 𝟙 _`. -/
private theorem sum_sub_id_app_eq_zero_iff {F : X.Sheaf AddCommGrpCat.{u}} {ι : Type*}
    (s : Finset ι) (η : ι → (F ⟶ F)) (W : Opens X) :
    ((∑ i ∈ s, η i) - 𝟙 F).hom.app (op W) = 0 ↔
      ∑ i ∈ s, (η i).hom.app (op W) = 𝟙 (F.obj.obj (op W)) := by
  let ev : (F ⟶ F) →+ (F.obj.obj (op W) ⟶ F.obj.obj (op W)) :=
    AddMonoidHom.mk' (fun φ ↦ φ.hom.app (op W)) fun _ _ ↦ rfl
  have happ : ((∑ i ∈ s, η i) - 𝟙 F).hom.app (op W) =
      (∑ i ∈ s, (η i).hom.app (op W)) - 𝟙 (F.obj.obj (op W)) := by
    have h := ev.map_sub (∑ i ∈ s, η i) (𝟙 F)
    rw [map_sum] at h
    exact h
  rw [happ, sub_eq_zero]

/-- The Godement functor carries any sheaf partition of unity on `F` to a sheaf partition of unity
on `(godement AddCommGrpCat X).obj F`. -/
theorem isPartitionOfUnity_godement_map {F : X.Sheaf AddCommGrpCat.{u}} {ι : Type*}
    {U : ι → Opens X} {η : ι → (F ⟶ F)} (hη : F.IsPartitionOfUnity U η) :
    ((godement AddCommGrpCat.{u} X).obj F).IsPartitionOfUnity U
      (fun i ↦ (godement AddCommGrpCat.{u} X).map (η i)) := by
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  refine ⟨V, htop, fun i W hW ↦ godement_map_app_eq_zero_of_app_eq_zero (η i) (hzero i) hW,
    fun x ↦ ?_⟩
  obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
  refine ⟨N, hxN, s, hsV, fun W hW ↦ (sum_sub_id_app_eq_zero_iff s _ W).1 ?_⟩
  have hδ : ∀ ⦃W' : Opens X⦄, W' ≤ N → ((∑ i ∈ s, η i) - 𝟙 F).hom.app (op W') = 0 :=
    fun W' hW' ↦ (sum_sub_id_app_eq_zero_iff s η W').2 (hsum hW')
  have hGδ := godement_map_app_eq_zero_of_app_eq_zero ((∑ i ∈ s, η i) - 𝟙 F) hδ hW
  have hGmap : (godement AddCommGrpCat.{u} X).map ((∑ i ∈ s, η i) - 𝟙 F) =
      (∑ i ∈ s, (godement AddCommGrpCat.{u} X).map (η i)) -
        𝟙 ((godement AddCommGrpCat.{u} X).obj F) := by
    rw [Functor.map_sub, Functor.map_sum, CategoryTheory.Functor.map_id]
  exact hGmap ▸ hGδ

/-- The Godement sheaf of a fine abelian sheaf is fine. -/
instance isFine_godement_obj (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] :
    ((godement AddCommGrpCat.{u} X).obj F).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨η, hη⟩ := TopCat.Sheaf.IsFine.exists_isPartitionOfUnity (F := F) U hU
    exact ⟨_, isPartitionOfUnity_godement_map hη⟩

/-- If `π : G ⟶ Z` is an epimorphism of abelian sheaves and `π ≫ ζ = φ ≫ π`, where `φ : G ⟶ G`
vanishes on all opens inside `V`, then `ζ : Z ⟶ Z` also vanishes on all opens inside `V`. This uses
that `V.sheafRestrict` preserves epimorphisms. -/
private theorem app_eq_zero_of_epi_comp {G Z : X.Sheaf AddCommGrpCat.{u}} (π : G ⟶ Z) [Epi π]
    (φ : G ⟶ G) (ζ : Z ⟶ Z) (hcomm : π ≫ ζ = φ ≫ π) {V : Opens X}
    (hφ : ∀ ⦃W : Opens X⦄, W ≤ V → φ.hom.app (op W) = 0) ⦃W : Opens X⦄ (hW : W ≤ V) :
    ζ.hom.app (op W) = 0 := by
  have hφV : V.sheafRestrict.map φ = 0 :=
    Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨U⟩ ↦ hφ fun x ⟨y, _, hxy⟩ ↦ hxy ▸ y.2
  have hζV : V.sheafRestrict.map ζ = 0 := by
    have : Epi (V.sheafRestrict.map π) := inferInstance
    rw [← cancel_epi (V.sheafRestrict.map π), comp_zero, ← Functor.map_comp, hcomm,
      Functor.map_comp, hφV, zero_comp]
  let W' : Opens V := ⟨Subtype.val ⁻¹' (W : Set X), W.isOpen.preimage continuous_subtype_val⟩
  have hW' : V.isOpenEmbedding.isOpenMap.functor.obj W' = W := by
    ext x
    refine ⟨fun ⟨_, hy, hxy⟩ ↦ hxy ▸ hy, fun hx ↦ ⟨⟨x, hW hx⟩, hx, rfl⟩⟩
  have happ : (V.sheafRestrict.map ζ).hom.app (op W') = 0 := by
    rw [hζV]
    rfl
  rw [← hW']
  exact happ

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
  obtain ⟨V, htop, hzero, hloc⟩ := hη
  have hzero' (i : ι) : ∀ ⦃W : Opens X⦄, W ≤ V i → (η' i).hom.app (op W) = 0 :=
    godement_map_app_eq_zero_of_app_eq_zero (η i) (hzero i)
  let ζ : ι → (Z ⟶ Z) := fun i ↦ cokernel.desc ιG (η' i ≫ π) (by
    have hnat : ιG ≫ η' i = η i ≫ ιG :=
      ((toGodement AddCommGrpCat.{u} X).naturality (η i)).symm
    rw [← Category.assoc, hnat, Category.assoc, cokernel.condition, comp_zero])
  have hcomm (i : ι) : π ≫ ζ i = η' i ≫ π := cokernel.π_desc _ _ _
  have hzeroZ (i : ι) : ∀ ⦃W : Opens X⦄, W ≤ V i → (ζ i).hom.app (op W) = 0 :=
    app_eq_zero_of_epi_comp π (η' i) (ζ i) (hcomm i) (hzero' i)
  refine ⟨ζ, V, hcomm, htop, hzero', hzeroZ, fun x ↦ ?_⟩
  obtain ⟨N, hxN, s, hsV, hsum⟩ := hloc x
  have hδF : ∀ ⦃W : Opens X⦄, W ≤ N → ((∑ i ∈ s, η i) - 𝟙 F).hom.app (op W) = 0 :=
    fun W hW ↦ (sum_sub_id_app_eq_zero_iff s η W).2 (hsum hW)
  have hδG : ∀ ⦃W : Opens X⦄, W ≤ N → ((∑ i ∈ s, η' i) - 𝟙 G).hom.app (op W) = 0 := fun W hW ↦ by
    have hmap : (godement AddCommGrpCat.{u} X).map ((∑ i ∈ s, η i) - 𝟙 F) =
        (∑ i ∈ s, η' i) - 𝟙 G := by
      rw [Functor.map_sub, Functor.map_sum, CategoryTheory.Functor.map_id]
    exact hmap ▸ godement_map_app_eq_zero_of_app_eq_zero _ hδF hW
  have hsumG : ∀ ⦃W : Opens X⦄, W ≤ N → ∑ i ∈ s, (η' i).hom.app (op W) = 𝟙 _ :=
    fun W hW ↦ (sum_sub_id_app_eq_zero_iff s η' W).1 (hδG hW)
  have hcommδ : π ≫ ((∑ i ∈ s, ζ i) - 𝟙 Z) = ((∑ i ∈ s, η' i) - 𝟙 G) ≫ π := by
    rw [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_sum, Preadditive.sum_comp,
      Category.comp_id, Category.id_comp]
    exact congrArg (· - π) (Finset.sum_congr rfl fun i _ ↦ hcomm i)
  have hδZ : ∀ ⦃W : Opens X⦄, W ≤ N → ((∑ i ∈ s, ζ i) - 𝟙 Z).hom.app (op W) = 0 :=
    app_eq_zero_of_epi_comp π _ _ hcommδ hδG
  have hsumZ : ∀ ⦃W : Opens X⦄, W ≤ N → ∑ i ∈ s, (ζ i).hom.app (op W) = 𝟙 _ :=
    fun W hW ↦ (sum_sub_id_app_eq_zero_iff s ζ W).1 (hδZ hW)
  exact ⟨N, hxN, s, hsV, hsumG, hsumZ⟩

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

/-- Gluing a locally finite sum of global sections of an abelian sheaf `G`: if each `a i` vanishes
on `V i` and on each member `N k` of an open cover all indices outside `S k` satisfy `N k ≤ V i`,
then the finite sums `∑ i ∈ S k, a i|_{N k}` glue to a global section `b`. -/
private theorem exists_gluing_finset_sum (G : X.Sheaf AddCommGrpCat.{u}) {ι κ : Type*}
    (V : ι → Opens X) (a : ι → G.obj.obj (op ⊤))
    (ha : ∀ i ⦃W : Opens X⦄, W ≤ V i → G.obj.map (homOfLE (le_top : W ≤ ⊤)).op (a i) = 0)
    (N : κ → Opens X) (hN : ⨆ k, N k = ⊤) (S : κ → Finset ι)
    (hSV : ∀ k i, i ∉ S k → N k ≤ V i) :
    ∃ b : G.obj.obj (op ⊤), ∀ k,
      G.obj.map (homOfLE (le_top : N k ≤ ⊤)).op b =
        ∑ i ∈ S k, G.obj.map (homOfLE (le_top : N k ≤ ⊤)).op (a i) := by
  classical
  let sf : ∀ k : κ, G.obj.obj (op (N k)) :=
    fun k ↦ ∑ i ∈ S k, G.obj.map (homOfLE le_top).op (a i)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj N sf := by
    intro k₁ k₂
    let W := N k₁ ⊓ N k₂
    have hrestrict (k : κ) (hWN : W ≤ N k) (hs : S k ⊆ S k₁ ∪ S k₂) :
        G.obj.map (homOfLE hWN).op (sf k) =
          ∑ i ∈ S k₁ ∪ S k₂, G.obj.map (homOfLE (le_top : W ≤ ⊤)).op (a i) := by
      simp only [sf, map_sum]
      have hterm (i : ι) :
          G.obj.map (homOfLE hWN).op (G.obj.map (homOfLE le_top).op (a i)) =
            G.obj.map (homOfLE (le_top : W ≤ ⊤)).op (a i) := by
        rw [← Functor.map_comp_apply]
        exact congrArg (fun f : W ⟶ ⊤ ↦ G.obj.map f.op (a i)) (Subsingleton.elim _ _)
      simp_rw [hterm]
      exact Finset.sum_subset hs fun i _ hi ↦ ha i (hWN.trans (hSV k i hi))
    exact (hrestrict k₁ inf_le_left Finset.subset_union_left).trans
      (hrestrict k₂ inf_le_right Finset.subset_union_right).symm
  obtain ⟨b, hb, -⟩ := G.existsUnique_gluing' N ⊤ (fun k ↦ homOfLE le_top) hN.ge sf hcompat
  exact ⟨b, hb⟩

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
  have hzero_apply {A B : AddCommGrpCat.{u}} (v : A) : (0 : A ⟶ B) v = 0 := rfl
  refine Z.eq_of_locally_eq₂ (homOfLE (le_top : U ≤ ⊤)) (homOfLE (le_top : V ≤ ⊤))
    htop.ge _ _ ?_ ?_
  · rw [← NatTrans.naturality_apply π.hom, ← NatTrans.naturality_apply φ.hom, hg,
      ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, ← hcomm,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply, hg₀, NatTrans.naturality_apply ζ.hom]
  · rw [← NatTrans.naturality_apply π.hom, ← NatTrans.naturality_apply φ.hom,
      hφ, hzero_apply, map_zero, ← NatTrans.naturality_apply ζ.hom, hζ, hzero_apply]

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
  have hzero_apply {A B : AddCommGrpCat.{u}} (v : A) : (0 : A ⟶ B) v = 0 := rfl
  have hπa (x : X) : π.hom.app (op ⊤) (a x) = (ζ x).hom.app (op ⊤) z :=
    app_top_apply_eq_of_sup_eq_top π (η' x) (ζ x) (hcomm x) (htop x)
      (hzeroG x le_rfl) (hzeroZ x le_rfl) (g x) (g₀ x) z (hg x) (hg₀ x)
  choose N hyN S hSV _ hsumZ using hloc
  have hN_top : ⨆ y : X, N y = ⊤ := eq_top_iff.2 fun y _ ↦ Opens.mem_iSup.2 ⟨y, hyN y⟩
  obtain ⟨b, hb⟩ := exists_gluing_finset_sum G V a
    (fun x W hWV ↦ by
      rw [← NatTrans.naturality_apply (η' x).hom, hzeroG x hWV, hzero_apply])
    N hN_top S hSV
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
    (map_sum (AddMonoidHom.mk'
      (fun f : Z.obj.obj (op (N y)) ⟶ Z.obj.obj (op (N y)) ↦
        f (Z.obj.map (homOfLE le_top).op z)) fun _ _ ↦ rfl)
      (fun x ↦ (ζ x).hom.app (op (N y))) (S y)).symm
  rw [hsum_apply, hsumZ y le_rfl]
  rfl

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
    exact Function.Injective.subsingleton
      (f := ConcreteCategory.hom (F.cohomologyPresheafObjIsoH 1 isTerminalTop).inv)
      (ConcreteCategory.bijective_of_isIso _).injective
  | succ n ih =>
    intro F _
    let ιG := (toGodement AddCommGrpCat.{u} X).app F
    have hflasque : ((godement AddCommGrpCat.{u} X).obj F).IsFlasque :=
      isFlasque_godement_obj AddCommGrpCat.{u} X F
    have hS := TauCeti.cokernelSequence_shortExact ιG
    exact Sheaf.H.subsingleton_X₁ hS (n + 1) (n + 2) rfl
      (ih (cokernel ιG) inferInstance)
      (subsingleton_H_succ_of_isFlasque ((godement AddCommGrpCat.{u} X).obj F) (n + 1))

/-- Global sections of sheaves of `R`-modules on any topological space form an additive functor. -/
instance additive_sheafΓ_moduleCat {Y : Type u} [TopologicalSpace Y] {R : Type u} [Ring R] :
    (Sheaf.Γ (Opens.grothendieckTopology Y) (ModuleCat.{u} R)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Every fine sheaf of `R`-modules has vanishing right derived global sections in positive
degrees. -/
theorem isZero_rightDerived_Γ_succ_of_isFine {R : Type u} [CommRing R]
    (F : X.Sheaf (ModuleCat.{u} R)) [F.IsFine] (n : ℕ) :
    IsZero (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived (n + 1)).obj
      F) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let FAb := (sheafCompose (Opens.grothendieckTopology X) G).obj F
  have : Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} FAb (n + 1)) :=
    subsingleton_H_succ_of_isFine_aux n FAb inferInstance
  have hAb : IsZero (G.obj (((Sheaf.Γ _ (ModuleCat.{u} R)).rightDerived (n + 1)).obj F)) :=
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (Sheaf.H FAb (n + 1)))).of_iso
      ((moduleCohomologyForgetComparison X R (n + 1)).app F)
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact hAb.eq_of_src _ _

/-- Every fine sheaf of `R`-modules has vanishing right derived global sections in every positive
degree `0 < n`. -/
theorem isZero_rightDerived_Γ_of_isFine_of_pos {R : Type u} [CommRing R]
    (F : X.Sheaf (ModuleCat.{u} R)) [F.IsFine] (n : ℕ) (hn : 0 < n) :
    IsZero (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).obj F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact isZero_rightDerived_Γ_succ_of_isFine F k

end TauCeti.Topology

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- Every fine sheaf of abelian groups has vanishing cohomology `Sheaf.H` in every positive degree
`n + 1`. -/
instance subsingleton_H_succ_of_isFine (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) :=
  TauCeti.Topology.subsingleton_H_succ_of_isFine_aux n F inferInstance

namespace IsFine

/-- Every fine sheaf of abelian groups has vanishing cohomology `Sheaf.H` in degree `n + 1`. -/
theorem subsingleton_H_succ {F : X.Sheaf AddCommGrpCat.{u}} (hF : F.IsFine) (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) :=
  TauCeti.Topology.subsingleton_H_succ_of_isFine_aux n F hF

/-- Every fine sheaf of abelian groups has vanishing cohomology `Sheaf.H` in every positive degree
`0 < n`. -/
theorem subsingleton_H_of_pos {F : X.Sheaf AddCommGrpCat.{u}} (hF : F.IsFine) (n : ℕ)
    (hn : 0 < n) : Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact hF.subsingleton_H_succ k

/-- Every fine sheaf of abelian groups has vanishing cohomology `Sheaf.H' _ _ ⊤` over the whole
space in every positive degree `0 < n`. -/
theorem subsingleton_H'_top_of_pos {F : X.Sheaf AddCommGrpCat.{u}} (hF : F.IsFine) (n : ℕ)
    (hn : 0 < n) : Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F n (⊤ : Opens X)) := by
  have := hF.subsingleton_H_of_pos n hn
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom (F.cohomologyPresheafObjIsoH n isTerminalTop).hom)
    (ConcreteCategory.bijective_of_isIso _).injective

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
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom (U.cohomologyPresheafObjIsoSheafRestrictH F n).hom)
    (ConcreteCategory.bijective_of_isIso _).injective

end IsFine

/-- If the restriction `U.sheafRestrict.obj F` of an abelian sheaf `F` to an open subset `U` is
fine, then `F` has vanishing cohomology over `U` in degree `n + 1`. -/
instance subsingleton_H'_succ_of_isFine_sheafRestrict (F : X.Sheaf AddCommGrpCat.{u})
    (U : Opens X) [IsFine (X := TopCat.of U) (U.sheafRestrict.obj F)] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) :=
  IsFine.subsingleton_H'_of_sheafRestrict_of_pos (F := F) (U := U) inferInstance (n + 1)
    (Nat.succ_pos n)

end TopCat.Sheaf
