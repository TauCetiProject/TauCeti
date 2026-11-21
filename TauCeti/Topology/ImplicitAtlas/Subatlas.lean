/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Pi.Finset
public import TauCeti.Topology.ImplicitAtlas.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Subatlases of implicit atlases

Pulling back the indices of an implicit atlas along an embedding keeps the original thickening
at the image of each finite index set. The action and the product charts are transported by the
bijections of coordinate sets. This gives an atlas on the same base precisely when the retained
regular footprints cover it. On a compact base finitely many indices suffice, so constructions
requiring a finite index type can be applied without changing the base or virtual dimension.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 3.1.1 and
  Lemma 5.2.1.
-/

public section

open Set Topology

namespace TauCeti.ImplicitAtlas

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
  {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

omit [DecidableEq A] [DecidableEq B] [∀ α, Finite (Γ α)] [∀ I, T2Space (T I)] in
/-- The action on the thickening indexed by `I.map f`, expressed in the coordinates of `I`. -/
noncomputable def reindexAction
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)) (f : B ↪ A) (I : Finset B) :
    ((β : I) → Γ (f β)) →* (T (I.map f) ≃ₜ T (I.map f)) :=
  (act (I.map f)).comp (I.mulEquivMap f Γ).symm.toMonoidHom

omit [DecidableEq A] [DecidableEq B] [∀ α, Finite (Γ α)] [∀ I, T2Space (T I)] in
@[simp]
theorem reindexAction_apply
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)) (f : B ↪ A) (I : Finset B)
    (g : (β : I) → Γ (f β)) :
    reindexAction act f I g = act (I.map f) ((I.mulEquivMap f Γ).symm g) :=
  (rfl)

omit [DecidableEq A] [DecidableEq B] in
private theorem kuranishiZeroSet_reindex {T : Finset A → Type*} {E : A → Type*} [∀ α, Zero (E α)]
    {s : ∀ (I : Finset A) (α : I), T I → E α}
    (f : B ↪ A) (I J : Finset B) :
    kuranishiZeroSet (T := fun K ↦ T (K.map f)) (E := fun β ↦ E (f β))
        (fun K β ↦ s (K.map f) ⟨f β, K.apply_coe_mem_map f β⟩) I J =
      kuranishiZeroSet s (I.map f) (J.map f) := by
  ext x
  simp only [mem_kuranishiZeroSet, Subtype.forall, Finset.forall_mem_map, Finset.mem_map']

private noncomputable def reindexZeroHomeomorph (f : B ↪ A) (I J : Finset B) :
    kuranishiZeroSet (T := fun K ↦ T (K.map f)) (E := fun β ↦ E (f β))
        (fun K β ↦ 𝒜.kuranishi (K.map f) ⟨f β, K.apply_coe_mem_map f β⟩) I J ≃ₜ
      kuranishiZeroSet 𝒜.kuranishi (I.map f) (J.map f) :=
  Homeomorph.setCongr (kuranishiZeroSet_reindex (s := 𝒜.kuranishi) f I J)

omit [DecidableEq B] in
@[simp]
private theorem coe_reindexZeroHomeomorph (f : B ↪ A) (I J : Finset B) (x : _) :
    (𝒜.reindexZeroHomeomorph f I J x).1 = x.1 := by
  simp [reindexZeroHomeomorph]

private theorem reindex_exists_openPartialHomeomorph (f : B ↪ A) {I J : Finset B} (h : I ⊆ J)
    (x : _) (hx : 𝒜.footprintMap (Finset.map_subset_map.2 h)
      (𝒜.reindexZeroHomeomorph f I J x) ∈ 𝒜.regLocus (I.map f)) :
    ∃ n : ℕ, (n : ℤ) = d + ∑ β ∈ I, (Module.finrank ℝ (E (f β)) : ℤ) ∧
      ∃ e : OpenPartialHomeomorph (T (J.map f))
        (EuclideanSpace ℝ (Fin n) × ((β : ↥(J \ I)) → E (f β))),
        x.1 ∈ e.source ∧ ∀ y ∈ e.source, (e y).2 = fun β : ↥(J \ I) ↦
          𝒜.kuranishi (J.map f) ⟨f β, Finset.mem_map_of_mem f (Finset.mem_sdiff.1 β.2).1⟩ y := by
  obtain ⟨n, hn, e, hxe, hes⟩ := 𝒜.exists_openPartialHomeomorph
    (Finset.map_subset_map.2 h) (𝒜.reindexZeroHomeomorph f I J x) hx
  let q : (J \ I : Finset B) ≃ (J.map f \ I.map f : Finset A) :=
    ((J \ I).equivMap f).trans (Equiv.subtypeEquivRight fun _ ↦ by rw [Finset.map_sdiff])
  let H := Homeomorph.piCongrLeft (Y := fun α : (J.map f \ I.map f : Finset A) ↦ E α) q
  refine ⟨n, by simpa only [Finset.sum_map] using hn,
    e.transHomeomorph ((Homeomorph.refl _).prodCongr H.symm), by simpa using hxe, ?_⟩
  intro y hy
  funext β
  exact congrFun (hes y hy) (q β)

/-- Pull back the finite index sets of an implicit atlas along `f`, keeping the same base and
virtual dimension. The covering condition is exactly that the footprints at the image index
sets cover the base. For an inclusion of a subtype this restricts to that subset of indices. -/
noncomputable def reindex (f : B ↪ A) (hcover : ⋃ I : Finset B, 𝒜.footprint (I.map f) = univ) :
    ImplicitAtlas (fun β ↦ Γ (f β)) (fun β ↦ E (f β)) (fun β ↦ ρ (f β)) (fun I ↦ T (I.map f))
      (reindexAction act f) X d := by
  let F := fun ⦃I J : Finset B⦄ (h : I ⊆ J) ↦
    𝒜.footprintMap (Finset.map_subset_map.2 h) ∘ 𝒜.reindexZeroHomeomorph f I J
  have hF : ∀ ⦃I J : Finset B⦄ (h : I ⊆ J), range (F h) =
      range (𝒜.footprintMap (Finset.map_subset_map.2 h)) := fun _ _ h ↦
    (𝒜.reindexZeroHomeomorph f _ _).surjective.range_comp _
  let M (I : Finset B) := (I.mulEquivMap f Γ).symm
  have hM {I J : Finset B} (h : I ⊆ J) (g : (β : J) → Γ (f β)) :
      Finset.restrict₂ (Finset.map_subset_map.2 h) (M J g) =
        M I (Finset.restrict₂ (π := fun β ↦ Γ (f β)) h g) :=
    Finset.restrict₂_mulEquivMap_symm f Γ h g
  refine
    { baseHomeomorph := 𝒜.baseHomeomorph
      kuranishi := fun I β ↦ 𝒜.kuranishi (I.map f) ⟨f β, I.apply_coe_mem_map f β⟩
      continuous_kuranishi := fun I β ↦
        𝒜.continuous_kuranishi (I.map f) ⟨f β, I.apply_coe_mem_map f β⟩
      kuranishi_act := ?_
      regLocus := fun I ↦ 𝒜.regLocus (I.map f)
      isOpen_regLocus := fun I ↦ 𝒜.isOpen_regLocus (I.map f)
      act_mem_regLocus := fun I g x hx ↦ 𝒜.act_mem_regLocus (I.map f) _ x hx
      footprintMap := F
      continuous_footprintMap := fun _ _ h ↦
        (𝒜.continuous_footprintMap (Finset.map_subset_map.2 h)).comp
          (𝒜.reindexZeroHomeomorph f _ _).continuous
      footprintMap_act := ?_
      footprintMap_self := ?_
      footprintMap_footprintMap := ?_
      kuranishi_footprintMap := fun I _ h x β ↦ by
        simpa only [F, Function.comp_apply, coe_reindexZeroHomeomorph] using
          𝒜.kuranishi_footprintMap (Finset.map_subset_map.2 h)
            (𝒜.reindexZeroHomeomorph f _ _ x) ⟨f β, I.apply_coe_mem_map f β⟩
      isOpen_range_footprintMap := fun _ _ h ↦ (hF h).symm ▸ 𝒜.isOpen_range_footprintMap _
      range_footprintMap_inter := ?_
      footprintMap_mem_range_iff := ?_
      isQuotientMap_footprintMap := ?_
      footprintMap_eq_footprintMap_iff := ?_
      mem_regLocus_of_footprintMap_mem := fun _ _ h x ↦ by
        simpa only [F, Function.comp_apply, coe_reindexZeroHomeomorph] using
          𝒜.mem_regLocus_of_footprintMap_mem (Finset.map_subset_map.2 h)
            (𝒜.reindexZeroHomeomorph f _ _ x)
      eq_one_of_act_eq := ?_
      exists_openPartialHomeomorph := fun _ _ h x hx ↦
        𝒜.reindex_exists_openPartialHomeomorph f h x hx
      exists_footprintMap_eq := ?_ }
  · intro I β g x
    rw [reindexAction_apply, 𝒜.kuranishi_act]
    have hg := congrFun ((I.mulEquivMap f Γ).apply_symm_apply g) β
    rw [Finset.mulEquivMap_apply] at hg
    exact congrArg (fun γ ↦ ρ (f β) γ (𝒜.kuranishi (I.map f) ⟨f β, _⟩ x)) hg
  · intro I J h g x hx
    have hact := 𝒜.footprintMap_act (Finset.map_subset_map.2 h) (M J g)
      (𝒜.reindexZeroHomeomorph f I J x)
      (𝒜.act_mem_kuranishiZeroSet (M J g) (𝒜.reindexZeroHomeomorph f I J x).2)
    rw [hM h g] at hact
    simpa only [F, Function.comp_apply, reindexAction_apply, reindexZeroHomeomorph,
      Homeomorph.setCongr_apply, M] using hact
  · intro I x
    simpa only [F, Function.comp_apply, reindexZeroHomeomorph, Homeomorph.setCongr_apply] using
      𝒜.footprintMap_self (I.map f) x
  · intro I J K hIJ hJK x hx hx'
    let y := 𝒜.reindexZeroHomeomorph f J K x
    have hy : y.1 ∈ kuranishiZeroSet 𝒜.kuranishi (I.map f) (K.map f) :=
      coe_reindexZeroHomeomorph 𝒜 f J K x ▸ (𝒜.reindexZeroHomeomorph f I K ⟨x, hx'⟩).2
    simpa only [F, Function.comp_apply, reindexZeroHomeomorph, Homeomorph.setCongr_apply, y] using
      𝒜.footprintMap_footprintMap_mk
        (Finset.map_subset_map.2 hIJ) (Finset.map_subset_map.2 hJK) y hy
  · intro I J₁ J₂ h₁ h₂
    simp only [hF]
    have h := 𝒜.range_footprintMap_inter ((Finset.map_subset_map (f := f)).2 h₁)
      ((Finset.map_subset_map (f := f)).2 h₂)
    -- Transport the inclusion proof along the equality of the upper index sets.
    have hr {K L : Finset A} (e : K = L) (hK : I.map f ⊆ K) (hL : I.map f ⊆ L) :
        range (𝒜.footprintMap hK) = range (𝒜.footprintMap hL) := by subst L; rfl
    exact h.trans (hr (Finset.map_union J₁ J₂).symm _ _)
  · intro I J K hIJ hJK x
    simp only [hF]
    simpa only [F, Function.comp_apply, coe_reindexZeroHomeomorph] using
      𝒜.footprintMap_mem_range_iff (Finset.map_subset_map.2 hIJ) (Finset.map_subset_map.2 hJK)
        (𝒜.reindexZeroHomeomorph f _ _ x)
  · intro I J h
    let e := 𝒜.reindexZeroHomeomorph f I J
    exact (Homeomorph.setCongr (hF h)).symm.isQuotientMap.comp
      ((𝒜.isQuotientMap_footprintMap (Finset.map_subset_map.2 h)).comp e.isQuotientMap)
  · intro I J h x y
    refine (𝒜.footprintMap_eq_footprintMap_iff (Finset.map_subset_map.2 h)
      (𝒜.reindexZeroHomeomorph f I J x) (𝒜.reindexZeroHomeomorph f I J y)).trans ?_
    refine (J.mulEquivMap f Γ).toEquiv.exists_congr_left.trans (exists_congr fun g ↦ ?_)
    simp only [coe_reindexZeroHomeomorph, reindexAction_apply]
    refine and_congr ?_ Iff.rfl
    exact (congrArg (· = 1) (hM h g)).to_iff.trans (map_eq_one_iff _ (M I).injective)
  · intro I J h x hx g hg hfix
    have hr : Finset.restrict₂ (Finset.map_subset_map.2 h) (M J g) = 1 := by
      rw [hM h g, hg, map_one]
    apply (M J).injective
    rw [map_one]
    exact 𝒜.eq_one_of_act_eq (Finset.map_subset_map.2 h)
      (𝒜.reindexZeroHomeomorph f _ _ x) hx (M J g) hr
      (by simpa only [coe_reindexZeroHomeomorph, M, reindexAction_apply] using hfix)
  · intro y
    obtain ⟨I, hy⟩ := mem_iUnion.1 (hcover ▸ mem_univ y)
    obtain ⟨x, hx, hxy⟩ := 𝒜.mem_footprint.1 hy
    refine ⟨I, (𝒜.reindexZeroHomeomorph f ∅ I).symm x, ?_, ?_⟩
    · have H := (𝒜.reindexZeroHomeomorph f ∅ I).apply_symm_apply x
      rw [← H] at hx
      simpa only [coe_reindexZeroHomeomorph] using hx
    · exact (congrArg (𝒜.baseHomeomorph ∘ 𝒜.footprintMap (Finset.empty_subset (I.map f)))
        ((𝒜.reindexZeroHomeomorph f ∅ I).apply_symm_apply x)).trans hxy

/-- The regular locus of a reindexed thickening is the original regular locus. -/
@[simp]
theorem regLocus_reindex (f : B ↪ A) (hcover) (I : Finset B) :
    (𝒜.reindex f hcover).regLocus I = 𝒜.regLocus (I.map f) :=
  (rfl)

/-- Reindexing reads the Kuranishi map in the corresponding original coordinate. -/
@[simp]
theorem kuranishi_reindex (f : B ↪ A) (hcover) (I : Finset B) (β : I) (x : T (I.map f)) :
    (𝒜.reindex f hcover).kuranishi I β x =
      𝒜.kuranishi (I.map f) ⟨f β, I.apply_coe_mem_map f β⟩ x :=
  (rfl)

/-- Reindexing does not change the base identification. -/
@[simp]
theorem baseHomeomorph_reindex (f : B ↪ A) (hcover) :
    (𝒜.reindex f hcover).baseHomeomorph = 𝒜.baseHomeomorph :=
  (rfl)

/-- Reindexing does not change the zero set inside the corresponding original thickening. -/
@[simp]
theorem kuranishiZeroSet_reindex_eq (f : B ↪ A) (hcover) (I J : Finset B) :
    kuranishiZeroSet (T := fun K ↦ T (K.map f)) (E := fun β ↦ E (f β))
        (𝒜.reindex f hcover).kuranishi I J =
      kuranishiZeroSet 𝒜.kuranishi (I.map f) (J.map f) :=
  kuranishiZeroSet_reindex (s := 𝒜.kuranishi) f I J

/-- The footprint map of the reindexed atlas is the original map on the identified zero set. -/
@[simp]
theorem footprintMap_reindex (f : B ↪ A) (hcover) {I J : Finset B} (h : I ⊆ J)
    (x : kuranishiZeroSet (T := fun K ↦ T (K.map f)) (E := fun β ↦ E (f β))
      (𝒜.reindex f hcover).kuranishi I J) :
    (𝒜.reindex f hcover).footprintMap h x =
      𝒜.footprintMap (Finset.map_subset_map.2 h)
        ⟨x.1, (𝒜.kuranishiZeroSet_reindex_eq f hcover I J).subset x.2⟩ := by
  -- The definition transports the subtype; the underlying point is unchanged.
  refine congrArg (𝒜.footprintMap (Finset.map_subset_map.2 h)) (Subtype.ext ?_)
  exact 𝒜.coe_reindexZeroHomeomorph f I J x

/-- A reindexed footprint has the same image as the footprint at the original index set. -/
@[simp]
theorem footprint_reindex (f : B ↪ A) (hcover) (I : Finset B) :
    (𝒜.reindex f hcover).footprint I = 𝒜.footprint (I.map f) := by
  ext y
  simp only [mem_footprint]
  refine Iff.trans (exists_congr fun x ↦ ?_)
    (𝒜.reindexZeroHomeomorph f ∅ I).toEquiv.exists_congr_right
  -- The reindexed footprint map is the original map composed with the zero-set identification.
  simp only [regLocus_reindex, baseHomeomorph_reindex]
  rfl

/-- Compactness supplies a finite set of indices whose retained footprints cover the base.
Restricting along the subtype inclusion gives an atlas on that finite index type. -/
theorem exists_finite_subatlas [CompactSpace X] :
    ∃ C : Finset A, ⋃ I : Finset C, 𝒜.footprint (I.map (Function.Embedding.subtype _)) = univ := by
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover 𝒜.footprint 𝒜.isOpen_footprint
    𝒜.iUnion_footprint.ge
  refine ⟨S.biUnion id, eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨I, hx⟩ := mem_iUnion.1 (hS (mem_univ x))
  obtain ⟨hI, hx⟩ := mem_iUnion.1 hx
  have hIC : I ⊆ S.biUnion id := Finset.subset_biUnion_of_mem id hI
  exact mem_iUnion.2 ⟨I.subtype _, by rwa [Finset.subtype_map_of_mem hIC]⟩

end TauCeti.ImplicitAtlas
