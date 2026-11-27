/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.CompStruct
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.Op
public import TauCeti.CategoryTheory.Core
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Equivalences and the core of a quasicategory

An edge `e : x₀ ⟶ x₁` of a simplicial set `X` is an *equivalence* when it admits an inverse up to
`2`-simplices, i.e. a structure `SSet.Edge.InvStruct e`. When `X` is a quasicategory this says
exactly that `e` becomes an isomorphism in the homotopy category of `X`.

The *core* `X.core` of `X` is the subcomplex of the simplices all of whose edges are equivalences.
Every edge of `X.core` is already an equivalence in `X.core` itself, so taking the core is
idempotent (`SSet.core_core`). When `X` is a quasicategory, its core is again a quasicategory: an
inner horn determines all edges of its filler except, for `Λ[2, 1]`, the long edge, which is a
composite of two equivalences. Every Kan complex contained in `X` lies in the core. That the core
of a quasicategory is itself a Kan complex, hence the largest Kan complex in `X`, follows from
Joyal's theorem on special outer horns and is proved in
`TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic` (`SSet.core.kanComplex`,
`SSet.isGreatest_core`). For the nerve of a category `C`, the core is the nerve of the groupoid
`Core C`.

## Main definitions

* `SSet.Edge.IsEquivalence`: an edge admitting an inverse up to `2`-simplices.
* `SSet.core`, `SSet.core.map`, `SSet.coreFunctor`: the subcomplex of simplices all of whose edges
  are equivalences, functorial in `X`.
* `SSet.coreHomEquiv`: maps from a Kan complex into `X.core` are maps into `X`.
* `SSet.stdSimplex.π₀CoreEquiv`: the connected components of `(Δ[n]).core` are `Fin (n + 1)`.
* `CategoryTheory.Core.nerveIso`: the nerve of `Core C` is the core of the nerve of `C`.

## Main results

* `SSet.Edge.isEquivalence_iff_isIso`: in a quasicategory, an edge is an equivalence exactly
  when its class in the homotopy category is an isomorphism.
* `SSet.Edge.CompStruct.isEquivalence₀₂`, `isEquivalence₀₁`, `isEquivalence₁₂`: equivalences in
  a quasicategory satisfy two-out-of-three.
* `SSet.Edge.isEquivalence_of_kanComplex`: every edge of a Kan complex is an equivalence. Hence
  every Kan complex contained in `X` lies in its core (`SSet.le_core_of_kanComplex`), maps from
  a Kan complex factor through the core (`SSet.range_le_core_of_kanComplex`), and two vertices of
  a Kan complex lie in the same connected component exactly when an edge joins them
  (`SSet.π₀.mk_eq_mk_iff_nonempty_edge`).
* `SSet.le_core_iff`: the core is the largest subcomplex all of whose edges are equivalences.
* `SSet.core.isEquivalence`, `SSet.core_core`: every edge of `X.core` is an equivalence in
  `X.core`, so the core of the core is everything.
* `SSet.Edge.isEquivalence_opEquiv_iff`, `SSet.op_core`, `SSet.core.opIso`: equivalences are
  invariant under reversing edges, and the opposite of the core is the core of the opposite.
* `SSet.Edge.isEquivalence_tensor_iff`, `SSet.core_tensor`: an edge of a product is an
  equivalence exactly when both of its projections are, so the core of a product is the product
  of the cores. This makes the cores of function complexes closed under composition. The same
  criterion holds for arbitrary products
  (`SSet.Edge.isEquivalence_iff_forall_isEquivalence_map_π`).
* `SSet.hasLiftingProperty_horn_ι_core_ι`: the inclusion of the core of a quasicategory is an
  inner fibration, so `SSet.core.quasicategory`: the core of a quasicategory is a quasicategory.
* `CategoryTheory.nerve.mem_core_iff`: a simplex of the nerve of a category lies in the core
  exactly when all its morphisms are isomorphisms.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.4 and §1.2.5 (Proposition 1.2.5.3).
* J. Lurie, *Kerodon*, Tag 01D7 (the core of an `∞`-category).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

universe u v

namespace SSet

variable {X Y : SSet.{u}}

namespace Edge

variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- An edge `e` of a simplicial set is an *equivalence* when it admits an inverse up to
`2`-simplices, that is, a structure `e.InvStruct`. In a quasicategory these are the edges that
become isomorphisms in the homotopy category (`SSet.Edge.isEquivalence_iff_isIso`). -/
def IsEquivalence (e : Edge x₀ x₁) : Prop := Nonempty e.InvStruct

lemma InvStruct.isEquivalence {e : Edge x₀ x₁} (I : e.InvStruct) : e.IsEquivalence := ⟨I⟩

/-- A choice of inverse structure for an equivalence. -/
noncomputable def IsEquivalence.invStruct {e : Edge x₀ x₁} (h : e.IsEquivalence) :
    e.InvStruct :=
  Classical.choice h

@[simp]
lemma isEquivalence_id (x : X _⦋0⦌) : (id x).IsEquivalence :=
  (InvStruct.invStructId x).isEquivalence

lemma IsEquivalence.map {e : Edge x₀ x₁} (h : e.IsEquivalence) (f : X ⟶ Y) :
    (e.map f).IsEquivalence :=
  (h.invStruct.map f).isEquivalence

/-- Being an equivalence only depends on the underlying `1`-simplex. -/
lemma isEquivalence_iff_of_edge_eq {y₀ y₁ : X _⦋0⦌} {e : Edge x₀ x₁} {e' : Edge y₀ y₁}
    (h : e.edge = e'.edge) : e.IsEquivalence ↔ e'.IsEquivalence :=
  ⟨fun he ↦ (he.invStruct.ofEq h).isEquivalence,
    fun he ↦ (he.invStruct.ofEq h.symm).isEquivalence⟩

/-- Transporting an edge along equalities of its endpoints does not change whether it is an
equivalence. -/
@[simp]
lemma isEquivalence_ofEq_iff {y₀ y₁ : X _⦋0⦌} {e : Edge x₀ x₁} (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    (e.ofEq h₀ h₁).IsEquivalence ↔ e.IsEquivalence :=
  isEquivalence_iff_of_edge_eq (ofEq_edge e h₀ h₁)

section Quasicategory

open Truncated.HomotopyCategory₂

variable [Quasicategory X]

/-- In a quasicategory, an edge is an equivalence exactly when its class in the homotopy category
is an isomorphism. -/
lemma isEquivalence_iff_isIso (e : Edge x₀ x₁) :
    e.IsEquivalence ↔ IsIso (homMk e.toTruncated) := by
  refine ⟨fun ⟨I⟩ ↦ ⟨homMk I.inv.toTruncated, I.homInvId.toTruncated.homotopyCategory₂_fac,
    I.invHomId.toTruncated.homotopyCategory₂_fac⟩, fun _ ↦ ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : Edge x₁ x₀, homMk g.toTruncated = inv (homMk e.toTruncated) :=
    ⟨ofTruncated _, (homMk_surjective _).choose_spec⟩
  exact ⟨{ inv := g
           homInvId := .ofTruncated (.ofHomotopyCategory₂Fac (by
             rw [hg, IsIso.hom_inv_id, toTruncated_id]
             exact (homMk_id (.mk _)).symm))
           invHomId := .ofTruncated (.ofHomotopyCategory₂Fac (by
             rw [hg, IsIso.inv_hom_id, toTruncated_id]
             exact (homMk_id (.mk _)).symm)) }⟩

namespace CompStruct

variable {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂} (h : CompStruct e₀₁ e₁₂ e₀₂)
include h

/-- In a quasicategory, a composite of equivalences is an equivalence. -/
lemma isEquivalence₀₂ (h₀₁ : e₀₁.IsEquivalence) (h₁₂ : e₁₂.IsEquivalence) :
    e₀₂.IsEquivalence := by
  rw [isEquivalence_iff_isIso] at h₀₁ h₁₂ ⊢
  rw [← h.toTruncated.homotopyCategory₂_fac]
  infer_instance

/-- In a quasicategory, if `e₀₁` and a composite `e₀₂` of `e₀₁` and `e₁₂` are equivalences, then
so is `e₁₂`. -/
lemma isEquivalence₁₂ (h₀₁ : e₀₁.IsEquivalence) (h₀₂ : e₀₂.IsEquivalence) :
    e₁₂.IsEquivalence := by
  rw [isEquivalence_iff_isIso] at h₀₁ h₀₂ ⊢
  rw [← h.toTruncated.homotopyCategory₂_fac] at h₀₂
  exact IsIso.of_isIso_comp_left (homMk e₀₁.toTruncated) _

/-- In a quasicategory, if `e₁₂` and a composite `e₀₂` of `e₀₁` and `e₁₂` are equivalences, then
so is `e₀₁`. -/
lemma isEquivalence₀₁ (h₁₂ : e₁₂.IsEquivalence) (h₀₂ : e₀₂.IsEquivalence) :
    e₀₁.IsEquivalence := by
  rw [isEquivalence_iff_isIso] at h₁₂ h₀₂ ⊢
  rw [← h.toTruncated.homotopyCategory₂_fac] at h₀₂
  exact IsIso.of_isIso_comp_right _ (homMk e₁₂.toTruncated)

end CompStruct

end Quasicategory

/-- Every edge of a Kan complex is an equivalence: filling the outer horns `Λ[2, 0]` and
`Λ[2, 2]` provides a right and a left inverse in the homotopy category. -/
lemma isEquivalence_of_kanComplex [KanComplex X] (e : Edge x₀ x₁) : e.IsEquivalence := by
  open Truncated.HomotopyCategory₂ in
  rw [isEquivalence_iff_isIso]
  -- A right inverse, from a filler of the horn `Λ[2, 0]` with edges `e` and `id x₀`.
  obtain ⟨σ, hσ₁, hσ₂⟩ := horn₂₀.isPushout.exists_desc (yonedaEquiv.symm e.edge)
    (yonedaEquiv.symm (id x₀).edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq,
        (id x₀).src_eq])
  obtain ⟨s, hs⟩ := KanComplex.hornFilling σ
  have hs₂ : stdSimplex.δ 2 ≫ s = yonedaEquiv.symm e.edge := by rw [← hσ₁, hs]; simp
  have hs₁ : stdSimplex.δ 1 ≫ s = yonedaEquiv.symm (id x₀).edge := by rw [← hσ₂, hs]; simp
  obtain ⟨s, rfl⟩ := yonedaEquiv.symm.surjective s
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, yonedaEquiv.symm.injective.eq_iff] at hs₂ hs₁
  let r : Edge x₁ x₀ := Edge.mk (X.δ 0 s)
    (by simpa [hs₂, e.tgt_eq] using (δ_comp_δ_apply (i := 0) (j := 1) (by simp) s).symm)
    (by
      rw [← (id x₀).tgt_eq, ← hs₁]
      exact (δ_comp_δ_apply (i := 0) (j := 0) le_rfl s).symm)
  have hr : homMk e.toTruncated ≫ homMk r.toTruncated = 𝟙 _ :=
    (CompStruct.mk (e₀₁ := e) (e₁₂ := r) (e₀₂ := id x₀) s hs₂ rfl
      hs₁).toTruncated.homotopyCategory₂_fac
  -- A left inverse, from a filler of the horn `Λ[2, 2]` with edges `id x₁` and `e`.
  obtain ⟨τ, hτ₁, hτ₂⟩ := horn₂₂.isPushout.exists_desc (yonedaEquiv.symm (id x₁).edge)
    (yonedaEquiv.symm e.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq,
        (id x₁).tgt_eq])
  obtain ⟨t, ht⟩ := KanComplex.hornFilling τ
  have ht₁ : stdSimplex.δ 1 ≫ t = yonedaEquiv.symm (id x₁).edge := by rw [← hτ₁, ht]; simp
  have ht₀ : stdSimplex.δ 0 ≫ t = yonedaEquiv.symm e.edge := by rw [← hτ₂, ht]; simp
  obtain ⟨t, rfl⟩ := yonedaEquiv.symm.surjective t
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, yonedaEquiv.symm.injective.eq_iff] at ht₁ ht₀
  let l : Edge x₁ x₀ := Edge.mk (X.δ 2 t)
    (by
      rw [← (id x₁).src_eq, ← ht₁]
      exact (δ_comp_δ_self_apply (i := 1) t).symm)
    (by simpa [ht₀, e.src_eq] using δ_comp_δ_apply (i := 0) (j := 1) (by simp) t)
  have hl : homMk l.toTruncated ≫ homMk e.toTruncated = 𝟙 _ :=
    (CompStruct.mk (e₀₁ := l) (e₁₂ := e) (e₀₂ := id x₁) t rfl ht₀
      ht₁).toTruncated.homotopyCategory₂_fac
  have hlr : homMk l.toTruncated = homMk r.toTruncated := by
    rw [← Category.comp_id (homMk l.toTruncated), ← hr, ← Category.assoc, hl, Category.id_comp]
  exact ⟨homMk r.toTruncated, hr, hlr ▸ hl⟩

/-- In a quasicategory, if two faces `δ 2 s` and `δ 0 s` of a `2`-simplex `s` are equivalences,
then so is the third face `δ 1 s`. -/
lemma isEquivalence_mk'_δ_one [Quasicategory X] (s : X _⦋2⦌)
    (h₂ : (mk' (X.δ 2 s)).IsEquivalence) (h₀ : (mk' (X.δ 0 s)).IsEquivalence) :
    (mk' (X.δ 1 s)).IsEquivalence := by
  obtain ⟨_, _, _, e₀₁, e₁₂, e₀₂, h, rfl⟩ := CompStruct.exists_of_simplex s
  rw [isEquivalence_iff_of_edge_eq (e' := e₀₁) (by rw [mk'_edge, h.d₂])] at h₂
  rw [isEquivalence_iff_of_edge_eq (e' := e₁₂) (by rw [mk'_edge, h.d₀])] at h₀
  rw [isEquivalence_iff_of_edge_eq (e' := e₀₂) (by rw [mk'_edge, h.d₁])]
  exact h.isEquivalence₀₂ h₂ h₀

/-- In a quasicategory, if the faces `δ 2 s` and `δ 1 s` of a `2`-simplex `s` are equivalences,
then so is the face `δ 0 s`. -/
lemma isEquivalence_mk'_δ_zero [Quasicategory X] (s : X _⦋2⦌)
    (h₂ : (mk' (X.δ 2 s)).IsEquivalence) (h₁ : (mk' (X.δ 1 s)).IsEquivalence) :
    (mk' (X.δ 0 s)).IsEquivalence := by
  obtain ⟨_, _, _, e₀₁, e₁₂, e₀₂, h, rfl⟩ := CompStruct.exists_of_simplex s
  rw [isEquivalence_iff_of_edge_eq (e' := e₀₁) (by rw [mk'_edge, h.d₂])] at h₂
  rw [isEquivalence_iff_of_edge_eq (e' := e₀₂) (by rw [mk'_edge, h.d₁])] at h₁
  rw [isEquivalence_iff_of_edge_eq (e' := e₁₂) (by rw [mk'_edge, h.d₀])]
  exact h.isEquivalence₁₂ h₂ h₁

/-- In a quasicategory, if the faces `δ 0 s` and `δ 1 s` of a `2`-simplex `s` are equivalences,
then so is the face `δ 2 s`. -/
lemma isEquivalence_mk'_δ_two [Quasicategory X] (s : X _⦋2⦌)
    (h₀ : (mk' (X.δ 0 s)).IsEquivalence) (h₁ : (mk' (X.δ 1 s)).IsEquivalence) :
    (mk' (X.δ 2 s)).IsEquivalence := by
  obtain ⟨_, _, _, e₀₁, e₁₂, e₀₂, h, rfl⟩ := CompStruct.exists_of_simplex s
  rw [isEquivalence_iff_of_edge_eq (e' := e₁₂) (by rw [mk'_edge, h.d₀])] at h₀
  rw [isEquivalence_iff_of_edge_eq (e' := e₀₂) (by rw [mk'_edge, h.d₁])] at h₁
  rw [isEquivalence_iff_of_edge_eq (e' := e₀₁) (by rw [mk'_edge, h.d₂])]
  exact h.isEquivalence₀₁ h₀ h₁

/-- The edge of a simplex `s` along a map `f : ⦋1⦌ ⟶ n` selecting the same vertex index twice is
degenerate, hence an equivalence. -/
lemma isEquivalence_mk'_map_of_eq {n : SimplexCategoryᵒᵖ} (s : X.obj n) (f : ⦋1⦌ ⟶ n.unop)
    (hf : f.toOrderHom 0 = f.toOrderHom 1) : (mk' (X.map f.op s)).IsEquivalence := by
  obtain ⟨i, hi⟩ : ∃ i, f.toOrderHom 0 = i := ⟨_, rfl⟩
  have : f = SimplexCategory.σ 0 ≫ SimplexCategory.const _ _ i := by
    ext k
    fin_cases k
    · exact congr_arg Fin.val hi
    · exact congr_arg Fin.val (hf.symm.trans hi)
  rw [isEquivalence_iff_of_edge_eq (e' := id (X.map (SimplexCategory.const _ _ i).op s))
    (by rw [mk'_edge, id_edge, this, op_comp, Functor.map_comp_apply, SimplicialObject.σ_def])]
  exact isEquivalence_id _

/-- An edge of `X` is an equivalence if and only if its opposite edge in `Xᵒᵖ` is an
equivalence. -/
@[simp]
lemma isEquivalence_opEquiv_iff (e : Edge x₀ x₁) :
    (Edge.opEquiv e).IsEquivalence ↔ e.IsEquivalence :=
  InvStruct.opEquiv.symm.nonempty_congr

/-- A `1`-simplex of `X`, read in `Xᵒᵖ`, is an equivalence if and only if it is an equivalence in
`X`. -/
@[simp]
lemma isEquivalence_mk'_opObjEquiv_symm_iff (s : X _⦋1⦌) :
    (mk' (X.opObjEquiv.symm s)).IsEquivalence ↔ (mk' s).IsEquivalence :=
  (isEquivalence_iff_of_edge_eq (e' := opEquiv (mk' s)) (by simp)).trans
    (isEquivalence_opEquiv_iff _)

/-- A `1`-simplex of `Xᵒᵖ`, read in `X`, is an equivalence if and only if it is an equivalence in
`Xᵒᵖ`. -/
@[simp]
lemma isEquivalence_mk'_opObjEquiv_iff (s : X.op _⦋1⦌) :
    (mk' (X.opObjEquiv s)).IsEquivalence ↔ (mk' s).IsEquivalence := by
  rw [← isEquivalence_mk'_opObjEquiv_symm_iff, Equiv.symm_apply_apply]

end Edge

/-- In a Kan complex, two vertices lie in the same connected component exactly when there is an
edge between them: edges compose, and they can be reversed since they are equivalences. -/
lemma π₀.mk_eq_mk_iff_nonempty_edge [KanComplex X] (x₀ x₁ : X _⦋0⦌) :
    π₀.mk x₀ = π₀.mk x₁ ↔ Nonempty (Edge x₀ x₁) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ π₀.sound e⟩
  rw [π₀.mk_eq_mk_iff] at h
  induction h with
  | rel _ _ h => exact h
  | refl x => exact ⟨Edge.id x⟩
  | symm _ _ _ ih => exact ⟨(Edge.isEquivalence_of_kanComplex ih.some).invStruct.inv⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some.comp ih₂.some⟩

open Edge

variable (X) in
/-- The core of a simplicial set `X`: the subcomplex of the simplices all of whose edges are
equivalences. When `X` is a quasicategory, it is the `∞`-groupoid of objects of `X` and
equivalences between them. -/
def core : X.Subcomplex where
  obj n := {s | ∀ f : ⦋1⦌ ⟶ n.unop, (mk' (X.map f.op s)).IsEquivalence}
  map g s hs f := (isEquivalence_iff_of_edge_eq (by simp)).1 (hs (f ≫ g.unop))

lemma mem_core_iff {n : SimplexCategoryᵒᵖ} (s : X.obj n) :
    s ∈ X.core.obj n ↔ ∀ f : ⦋1⦌ ⟶ n.unop, (mk' (X.map f.op s)).IsEquivalence :=
  Iff.rfl

/-- Every vertex of `X` lies in its core. -/
@[simp]
lemma mem_core_obj_zero (x : X _⦋0⦌) : x ∈ X.core.obj (op ⦋0⦌) :=
  fun _ ↦ isEquivalence_mk'_map_of_eq _ _ (Subsingleton.elim (α := Fin 1) _ _)

/-- An edge lies in the core exactly when it is an equivalence. -/
@[simp]
lemma Edge.edge_mem_core_iff {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    e.edge ∈ X.core.obj (Opposite.op ⦋1⦌) ↔ e.IsEquivalence := by
  refine ⟨fun h ↦ (isEquivalence_iff_of_edge_eq (by simp)).1 (h (𝟙 _)), fun h f ↦ ?_⟩
  obtain ⟨a, rfl⟩ | rfl := SimplexCategory.eq_of_one_to_one f
  · exact isEquivalence_mk'_map_of_eq _ _ rfl
  · exact (isEquivalence_iff_of_edge_eq (by simp)).2 h

/-- A subcomplex of `X` lies in the core exactly when all its edges are equivalences. -/
lemma le_core_iff (A : X.Subcomplex) :
    A ≤ X.core ↔ ∀ s ∈ A.obj (op ⦋1⦌), (mk' s).IsEquivalence := by
  refine ⟨fun h s hs ↦ (edge_mem_core_iff (mk' s)).1 (h _ hs), fun h n s hs f ↦ ?_⟩
  exact h _ (A.map f.op hs)

/-- A map of simplicial sets factors through the core exactly when it sends edges to
equivalences. -/
lemma range_le_core_iff (f : Y ⟶ X) :
    Subcomplex.range f ≤ X.core ↔ ∀ y : Y _⦋1⦌, (mk' (f.app _ y)).IsEquivalence := by
  rw [le_core_iff]
  exact ⟨fun h y ↦ h _ ⟨y, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact h y⟩

/-- Maps of simplicial sets send cores into cores. -/
lemma image_core_le (f : X ⟶ Y) : X.core.image f ≤ Y.core := by
  rw [le_core_iff]
  rintro _ ⟨s, hs, rfl⟩
  exact (isEquivalence_iff_of_edge_eq (by simp)).1 (((edge_mem_core_iff (mk' s)).1 hs).map f)

/-- The map `X.core ⟶ Y.core` induced by a map of simplicial sets `f : X ⟶ Y`. -/
def core.map (f : X ⟶ Y) : (X.core : SSet.{u}) ⟶ (Y.core : SSet.{u}) :=
  Subcomplex.lift (X.core.ι ≫ f) (by simpa [Subcomplex.range_comp] using image_core_le f)

@[reassoc (attr := simp)]
lemma core.map_ι (f : X ⟶ Y) : core.map f ≫ Y.core.ι = X.core.ι ≫ f :=
  (rfl)

@[simp]
lemma core.map_id (X : SSet.{u}) : core.map (𝟙 X) = 𝟙 (X.core : SSet.{u}) := by
  rw [← cancel_mono X.core.ι]
  simp

@[reassoc, simp]
lemma core.map_comp {Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    core.map (f ≫ g) = core.map f ≫ core.map g := by
  rw [← cancel_mono Z.core.ι]
  simp

/-- The isomorphism of cores induced by an isomorphism of simplicial sets. -/
def core.mapIso (e : X ≅ Y) : (X.core : SSet.{u}) ≅ (Y.core : SSet.{u}) where
  hom := core.map e.hom
  inv := core.map e.inv
  hom_inv_id := by rw [← core.map_comp, e.hom_inv_id, core.map_id]
  inv_hom_id := by rw [← core.map_comp, e.inv_hom_id, core.map_id]

@[simp]
lemma core.mapIso_hom (e : X ≅ Y) : (core.mapIso e).hom = core.map e.hom :=
  (rfl)

@[simp]
lemma core.mapIso_inv (e : X ≅ Y) : (core.mapIso e).inv = core.map e.inv :=
  (rfl)

/-- Sending a simplicial set to its core is an endofunctor of `SSet`. -/
-- Exposed so `coreFunctor.obj X` reduces to `X.core` in the generated `@[simps]` lemmas.
@[expose, simps]
def coreFunctor : SSet.{u} ⥤ SSet.{u} where
  obj X := X.core
  map := core.map

/-- The core of `X` is all of `X` exactly when every edge of `X` is an equivalence. -/
lemma core_eq_top_iff : X.core = ⊤ ↔ ∀ s : X _⦋1⦌, (mk' s).IsEquivalence := by
  rw [← top_le_iff, le_core_iff]
  simp

/-- The core of a Kan complex is everything. -/
@[simp]
lemma core_eq_top [KanComplex X] : X.core = ⊤ :=
  core_eq_top_iff.2 fun _ ↦ isEquivalence_of_kanComplex _

/-- Every map from a Kan complex into `X` factors through `X.core`. -/
lemma range_le_core_of_kanComplex [KanComplex Y] (f : Y ⟶ X) :
    Subcomplex.range f ≤ X.core :=
  (range_le_core_iff f).2 fun y ↦
    (isEquivalence_iff_of_edge_eq (by simp)).1 ((isEquivalence_of_kanComplex (mk' y)).map f)

/-- Every Kan complex contained in `X` lies in the core of `X`. -/
lemma le_core_of_kanComplex (A : X.Subcomplex) [KanComplex (A : SSet)] : A ≤ X.core := by
  simpa using range_le_core_of_kanComplex A.ι

/-- Maps from a Kan complex `Y` into the core of `X` are the same as maps from `Y` into `X`. -/
def coreHomEquiv (Y X : SSet.{u}) [KanComplex Y] : (Y ⟶ X.core) ≃ (Y ⟶ X) where
  toFun f := f ≫ X.core.ι
  invFun f := Subcomplex.lift f (range_le_core_of_kanComplex f)
  left_inv f := by rw [← cancel_mono X.core.ι, Subcomplex.lift_ι]
  right_inv f := Subcomplex.lift_ι _ _

@[simp]
lemma coreHomEquiv_apply [KanComplex Y] (f : Y ⟶ X.core) :
    coreHomEquiv Y X f = f ≫ X.core.ι :=
  (rfl)

@[reassoc (attr := simp)]
lemma coreHomEquiv_symm_apply_ι [KanComplex Y] (f : Y ⟶ X) :
    (coreHomEquiv Y X).symm f ≫ X.core.ι = f :=
  (rfl)

variable (X) in
/-- The opposite of the core of `X` is the core of `Xᵒᵖ`: reversing a simplex reverses each of its
edges, and an edge is an equivalence if and only if its opposite is. -/
@[simp]
lemma op_core : X.core.op = X.op.core := by
  ext n s
  simp only [Subcomplex.mem_op_obj_iff, mem_core_iff, op_map, Opposite.unop_op]
  exact ⟨fun h f ↦ (isEquivalence_mk'_opObjEquiv_symm_iff _).2 (h (SimplexCategory.rev.map f)),
    fun h f ↦ SimplexCategory.rev_map_rev_map f ▸
      (isEquivalence_mk'_opObjEquiv_symm_iff _).1 (h (SimplexCategory.rev.map f))⟩

/-- Reversing simplices identifies the opposite of `X.core` with `(Xᵒᵖ).core`. -/
def core.opIso (X : SSet.{u}) : (X.core : SSet.{u}).op ≅ (X.op.core : SSet.{u}) :=
  Subcomplex.opIso X.core ≪≫ Subcomplex.eqToIso (op_core X)

@[reassoc (attr := simp)]
lemma core.opIso_hom_ι (X : SSet.{u}) :
    (core.opIso X).hom ≫ X.op.core.ι = opFunctor.map X.core.ι := by
  simp [opIso]

@[reassoc (attr := simp)]
lemma core.opIso_inv_opFunctor_map_ι (X : SSet.{u}) :
    (core.opIso X).inv ≫ opFunctor.map X.core.ι = X.op.core.ι := by
  simp [opIso]

/-- An edge of a product `X ⊗ Y` is an equivalence exactly when both of its projections are. -/
lemma Edge.isEquivalence_tensor_iff {p₀ p₁ : (X ⊗ Y) _⦋0⦌} (e : Edge p₀ p₁) :
    e.IsEquivalence ↔ (e.map (fst X Y)).IsEquivalence ∧ (e.map (snd X Y)).IsEquivalence := by
  refine ⟨fun h ↦ ⟨h.map _, h.map _⟩, fun ⟨⟨I₁⟩, ⟨I₂⟩⟩ ↦ ⟨?_⟩⟩
  -- The simplices of `X ⊗ Y` are pairs of simplices, so the inverse and the `2`-simplices
  -- witnessing it are formed componentwise.
  exact
    { inv := Edge.mk (X := X ⊗ Y) (I₁.inv.edge, I₂.inv.edge)
        (Prod.ext I₁.inv.src_eq I₂.inv.src_eq) (Prod.ext I₁.inv.tgt_eq I₂.inv.tgt_eq)
      homInvId := CompStruct.mk (X := X ⊗ Y) (I₁.homInvId.simplex, I₂.homInvId.simplex)
        (Prod.ext I₁.homInvId.d₂ I₂.homInvId.d₂) (Prod.ext I₁.homInvId.d₀ I₂.homInvId.d₀)
        (Prod.ext I₁.homInvId.d₁ I₂.homInvId.d₁)
      invHomId := CompStruct.mk (X := X ⊗ Y) (I₁.invHomId.simplex, I₂.invHomId.simplex)
        (Prod.ext I₁.invHomId.d₂ I₂.invHomId.d₂) (Prod.ext I₁.invHomId.d₀ I₂.invHomId.d₀)
        (Prod.ext I₁.invHomId.d₁ I₂.invHomId.d₁) }

open Limits in
/-- An edge of a product `∏ᶜ B` of simplicial sets is an equivalence exactly when all of its
projections are. -/
lemma Edge.isEquivalence_iff_forall_isEquivalence_map_π {ι : Type*} {B : ι → SSet.{u}}
    [HasProduct B] {p₀ p₁ : (∏ᶜ B) _⦋0⦌} (e : Edge p₀ p₁) :
    e.IsEquivalence ↔ ∀ i, (e.map (Pi.π B i)).IsEquivalence := by
  refine ⟨fun h i ↦ h.map _, fun h ↦ ?_⟩
  let I := fun i ↦ (h i).invStruct
  -- A family of simplices of the factors is a simplex of the product, determined by its
  -- projections, so the inverse and the `2`-simplices witnessing it are formed componentwise.
  let mk {n : ℕ} (c : ∀ i, (B i) _⦋n⦌) : (∏ᶜ B) _⦋n⦌ :=
    yonedaEquiv (Pi.lift fun i ↦ yonedaEquiv.symm (c i))
  have hmk {n : ℕ} (c : ∀ i, (B i) _⦋n⦌) (i : ι) : (Pi.π B i).app _ (mk c) = c i := by
    rw [← yonedaEquiv_comp, limit.lift_π, Fan.mk_π_app, Equiv.apply_symm_apply]
  have hext {n : ℕ} {z z' : (∏ᶜ B) _⦋n⦌} (hz : ∀ i, (Pi.π B i).app _ z = (Pi.π B i).app _ z') :
      z = z' :=
    yonedaEquiv.symm.injective (Pi.hom_ext _ _ fun i ↦ by
      rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, hz])
  exact ⟨{ inv := Edge.mk (mk fun i ↦ (I i).inv.edge)
             (hext fun i ↦ by rw [δ_naturality_apply, hmk, (I i).inv.src_eq])
             (hext fun i ↦ by rw [δ_naturality_apply, hmk, (I i).inv.tgt_eq])
           homInvId := CompStruct.mk (mk fun i ↦ (I i).homInvId.simplex)
             (hext fun i ↦ by rw [δ_naturality_apply, hmk, (I i).homInvId.d₂, Edge.map_edge])
             (hext fun i ↦ by
               rw [δ_naturality_apply, hmk, (I i).homInvId.d₀]
               exact (hmk (fun i ↦ (I i).inv.edge) i).symm)
             (hext fun i ↦ by
               rw [δ_naturality_apply, hmk, (I i).homInvId.d₁]
               exact (σ_naturality_apply _ _ _).symm)
           invHomId := CompStruct.mk (mk fun i ↦ (I i).invHomId.simplex)
             (hext fun i ↦ by
               rw [δ_naturality_apply, hmk, (I i).invHomId.d₂]
               exact (hmk (fun i ↦ (I i).inv.edge) i).symm)
             (hext fun i ↦ by rw [δ_naturality_apply, hmk, (I i).invHomId.d₀, Edge.map_edge])
             (hext fun i ↦ by
               rw [δ_naturality_apply, hmk, (I i).invHomId.d₁]
               exact (σ_naturality_apply _ _ _).symm) }⟩

variable (X Y) in
/-- The core of a product is the product of the cores. -/
@[simp]
lemma core_tensor : (X ⊗ Y).core = X.core.prod Y.core := by
  ext n s
  rw [mem_core_iff, Subcomplex.prod_obj]
  exact (forall_congr' fun f ↦ (Edge.isEquivalence_tensor_iff _).trans (and_congr
    (isEquivalence_iff_of_edge_eq rfl) (isEquivalence_iff_of_edge_eq rfl))).trans forall_and

/-- The long edge of a filler of an inner horn `Λ[2, 1]` in the core of a quasicategory is an
equivalence, as a composite of the two equivalences of the horn. -/
private lemma isEquivalence_of_horn₂₁ [Quasicategory X] {a : (Λ[2, 1] : SSet) ⟶ X.core}
    {b : Δ[2] ⟶ X} (sq : CommSq a Λ[2, 1].ι X.core.ι b) (y : Δ[2] _⦋1⦌)
    (hy : y ∉ Λ[2, 1].obj (op ⦋1⦌)) : (mk' (b.app _ y)).IsEquivalence := by
  obtain ⟨s, rfl⟩ := yonedaEquiv.symm.surjective b
  -- The faces `δ 0` and `δ 2` of the filler are faces of the horn.
  have hface (j : Fin 3) (hj : j ≠ 1) : (mk' (X.δ j s)).IsEquivalence := by
    have h : yonedaEquiv.symm (X.δ j s) = horn.ι 1 j hj ≫ a ≫ X.core.ι := by
      rw [← stdSimplex.δ_comp_yonedaEquiv_symm, ← horn.ι_ι 1 j hj, Category.assoc, sq.w]
    rw [← edge_mem_core_iff, mk'_edge, ← yonedaEquiv.apply_symm_apply (X.δ j s), h,
      yonedaEquiv_comp]
    exact (a.app _ _).property
  -- The only edge of `Δ[2]` outside `Λ[2, 1]` is the long edge `δ 1`; constant edges are
  -- degenerate.
  obtain ⟨f, rfl⟩ : ∃ f : ⦋1⦌ ⟶ ⦋2⦌, stdSimplex.objEquiv.symm f = y :=
    stdSimplex.objEquiv.symm.surjective y
  rw [yonedaEquiv_symm_app_objEquiv_symm]
  obtain rfl | rfl | rfl | ⟨k, rfl⟩ := SimplexCategory.eq_of_one_to_two' f
  · exact absurd ((objEquiv_symm_δ_notMem_horn_iff _ _).1 hy) (by decide)
  · exact isEquivalence_mk'_δ_one s (hface 2 (by decide)) (hface 0 (by decide))
  · exact absurd ((objEquiv_symm_δ_notMem_horn_iff _ _).1 hy) (by decide)
  · exact isEquivalence_mk'_map_of_eq _ _ rfl

/-- The inclusion of the core of a quasicategory has the right lifting property against inner horn
inclusions. A filler in `X` of an inner horn in the core has all its edges in the horn, except for
the long edge of a filler of `Λ[2, 1]`, which is a composite of two equivalences. -/
lemma hasLiftingProperty_horn_ι_core_ι [Quasicategory X] {n : ℕ} (i : Fin (n + 3)) (h0 : 0 < i)
    (hn : i < Fin.last (n + 2)) : HasLiftingProperty Λ[n + 2, i].ι X.core.ι where
  sq_hasLift {a b} sq := by
    have hb : Subcomplex.range b ≤ X.core := by
      rw [range_le_core_iff]
      intro y
      by_cases hy : y ∈ Λ[_, i].obj (op ⦋1⦌)
      · have : b.app _ y = (a.app _ ⟨y, hy⟩).val := congr($(sq.w).app _ ⟨y, hy⟩).symm
        exact (edge_mem_core_iff (mk' _)).1 (this ▸ (a.app _ ⟨y, hy⟩).property)
      obtain _ | n := n
      · obtain rfl : i = 1 := by
          rw [Fin.lt_def] at h0 hn
          ext
          simp at h0 hn ⊢
          lia
        exact isEquivalence_of_horn₂₁ sq y hy
      -- In dimension at least `3`, every edge lies in the horn.
      · exact (hy (horn_obj_eq_univ i 1 (by lia) ▸ Set.mem_univ y)).elim
    exact ⟨⟨{ l := Subcomplex.lift b hb
              fac_left := by rw [← cancel_mono (Subcomplex.ι _)]; simp [sq.w] }⟩⟩

/-- The inclusion of the core of a quasicategory is an inner fibration. -/
instance [Quasicategory X] : InnerFibration X.core.ι where
  mem := by
    rintro _ _ _ ⟨i, h0, hn⟩
    exact hasLiftingProperty_horn_ι_core_ι i h0 hn

/-- The core of a quasicategory is a quasicategory. -/
instance core.quasicategory [Quasicategory X] : Quasicategory (X.core : SSet) :=
  quasicategory_of_innerFibration X.core.ι

/-- A `2`-simplex lies in the core if and only if its three faces are equivalences. -/
lemma mem_core_obj_two_iff (s : X _⦋2⦌) :
    s ∈ X.core.obj (op ⦋2⦌) ↔
      (mk' (X.δ 0 s)).IsEquivalence ∧ (mk' (X.δ 1 s)).IsEquivalence ∧
        (mk' (X.δ 2 s)).IsEquivalence := by
  rw [mem_core_iff]
  refine ⟨fun h ↦ ⟨h (SimplexCategory.δ 0), h (SimplexCategory.δ 1), h (SimplexCategory.δ 2)⟩, ?_⟩
  rintro ⟨h₀, h₁, h₂⟩ f
  obtain rfl | rfl | rfl | ⟨k, rfl⟩ := SimplexCategory.eq_of_one_to_two' f
  · exact h₀
  · exact h₁
  · exact h₂
  · exact isEquivalence_mk'_map_of_eq _ _ rfl

/-- A `2`-simplex witnessing a composition of equivalences as an equivalence lies in the core. -/
lemma Edge.CompStruct.simplex_mem_core {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂} (c : CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : e₀₁.IsEquivalence) (h₁₂ : e₁₂.IsEquivalence) (h₀₂ : e₀₂.IsEquivalence) :
    c.simplex ∈ X.core.obj (Opposite.op ⦋2⦌) :=
  (mem_core_obj_two_iff c.simplex).2
    ⟨(isEquivalence_iff_of_edge_eq (e := mk' (X.δ 0 c.simplex)) c.d₀).2 h₁₂,
      (isEquivalence_iff_of_edge_eq (e := mk' (X.δ 1 c.simplex)) c.d₁).2 h₀₂,
      (isEquivalence_iff_of_edge_eq (e := mk' (X.δ 2 c.simplex)) c.d₂).2 h₀₁⟩

/-- Every edge of `X.core` is an equivalence in `X.core` itself: an inverse structure in `X` has
all its edges invertible, so both the inverse edge and the `2`-simplices witnessing it already lie
in `X.core`. -/
lemma core.isEquivalence {x₀ x₁ : (X.core : SSet) _⦋0⦌} (e : Edge x₀ x₁) :
    e.IsEquivalence := by
  have he : (e.map X.core.ι).IsEquivalence :=
    (edge_mem_core_iff (e.map X.core.ι)).1 e.edge.property
  let I := he.invStruct
  have hinv_eq : I.inv.IsEquivalence := I.invStructInv.isEquivalence
  have hinv : I.inv.edge ∈ X.core.obj (op ⦋1⦌) := (edge_mem_core_iff I.inv).2 hinv_eq
  let g : Edge x₁ x₀ := Edge.mk ⟨I.inv.edge, hinv⟩ (Subtype.ext I.inv.src_eq)
    (Subtype.ext I.inv.tgt_eq)
  have h₁ : I.homInvId.simplex ∈ X.core.obj (op ⦋2⦌) :=
    I.homInvId.simplex_mem_core he hinv_eq (isEquivalence_id _)
  have h₂ : I.invHomId.simplex ∈ X.core.obj (op ⦋2⦌) :=
    I.invHomId.simplex_mem_core hinv_eq he (isEquivalence_id _)
  exact ⟨{ inv := g
           homInvId := CompStruct.mk ⟨I.homInvId.simplex, h₁⟩ (Subtype.ext I.homInvId.d₂)
             (Subtype.ext I.homInvId.d₀) (Subtype.ext I.homInvId.d₁)
           invHomId := CompStruct.mk ⟨I.invHomId.simplex, h₂⟩ (Subtype.ext I.invHomId.d₂)
             (Subtype.ext I.invHomId.d₀) (Subtype.ext I.invHomId.d₁) }⟩

/-- Taking the core of a simplicial set is idempotent: every edge of `X.core` is already an
equivalence in `X.core`. -/
@[simp]
lemma core_core (X : SSet.{u}) : (X.core : SSet).core = ⊤ :=
  core_eq_top_iff.2 fun _ ↦ core.isEquivalence _

/-- An edge of `Δ[n]` lies in its core if and only if its two endpoints coincide. -/
lemma stdSimplex.mem_core_obj_one_iff {n : ℕ} (s : Δ[n] _⦋1⦌) :
    s ∈ (Δ[n] : SSet.{u}).core.obj (op ⦋1⦌) ↔ s 0 = s 1 := by
  rw [← mk'_edge s, Edge.edge_mem_core_iff, mk'_edge]
  refine ⟨fun ⟨I⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hs : s 0 ≤ s 1 := (stdSimplex.objEquiv s).toOrderHom.monotone (Fin.zero_le 1)
    have hg : I.inv.edge 0 ≤ I.inv.edge 1 :=
      (stdSimplex.objEquiv I.inv.edge).toOrderHom.monotone (Fin.zero_le 1)
    exact le_antisymm hs (by simpa [stdSimplex.δ_apply] using hg)
  · have hs : s = (Δ[n] : SSet.{u}).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
        (stdSimplex.obj₀Equiv.symm (s 0)) := by
      refine stdSimplex.ext _ _ fun k ↦ ?_
      fin_cases k
      · simp [stdSimplex.obj₀Equiv_symm_apply]
      · simpa [stdSimplex.obj₀Equiv_symm_apply] using h.symm
    rw [hs]
    exact isEquivalence_mk'_map_of_eq _ _ rfl

/-- The connected components of the core of `Δ[n]` are the `n + 1` vertices of `Δ[n]`: every edge
in `(Δ[n]).core` has equal endpoints. -/
def stdSimplex.π₀CoreEquiv (n : ℕ) : π₀ ((Δ[n] : SSet.{u}).core : SSet.{u}) ≃ Fin (n + 1) where
  toFun := π₀.lift (fun x ↦ stdSimplex.obj₀Equiv x.val) fun x y e ↦ by
    have he : e.edge.val 0 = e.edge.val 1 := (stdSimplex.mem_core_obj_one_iff e.edge.val).1
        e.edge.property
    have hx : e.edge.val 0 = x.val 0 := stdSimplex.edge_edge_apply_zero (e.map (Δ[n]).core.ι)
    have hy : e.edge.val 1 = y.val 0 := stdSimplex.edge_edge_apply_one (e.map (Δ[n]).core.ι)
    exact congrArg stdSimplex.obj₀Equiv
      (stdSimplex.ext _ _ fun k ↦ by fin_cases k; exact hx.symm.trans (he.trans hy))
  invFun i :=
    π₀.mk (X := ((Δ[n] : SSet.{u}).core : SSet.{u}))
      ⟨stdSimplex.obj₀Equiv.symm i, mem_core_obj_zero _⟩
  left_inv c := by
    induction c using π₀.rec with | mk x =>
    exact congrArg π₀.mk (Subtype.ext (stdSimplex.obj₀Equiv.symm_apply_apply x.val))
  right_inv i := stdSimplex.obj₀Equiv.{u}.apply_symm_apply i

@[simp]
lemma stdSimplex.π₀CoreEquiv_mk {n : ℕ} (x : ((Δ[n] : SSet.{u}).core : SSet.{u}) _⦋0⦌) :
    stdSimplex.π₀CoreEquiv n (π₀.mk x) = stdSimplex.obj₀Equiv x.val :=
  (rfl)

@[simp]
lemma stdSimplex.π₀CoreEquiv_symm_apply {n : ℕ} (i : Fin (n + 1)) :
    (stdSimplex.π₀CoreEquiv.{u} n).symm i =
      π₀.mk (X := ((Δ[n] : SSet.{u}).core : SSet.{u}))
        ⟨stdSimplex.obj₀Equiv.symm i, mem_core_obj_zero _⟩ :=
  (rfl)

end SSet

namespace CategoryTheory.nerve

open SSet

variable {C : Type u} [Category.{v} C]

/-- An edge of the nerve of a category is an equivalence exactly when the corresponding morphism
is an isomorphism. -/
@[simp]
lemma isEquivalence_edgeMk_iff {x y : C} (f : x ⟶ y) : (edgeMk f).IsEquivalence ↔ IsIso f := by
  refine ⟨fun ⟨I⟩ ↦ ?_, fun _ ↦ ⟨?_⟩⟩
  · obtain ⟨g, hg⟩ := edgeMk_surjective I.inv
    have h₁ : f ≫ g = 𝟙 x :=
      (nonempty_compStruct_iff f g (𝟙 x)).1 ⟨by rw [hg, edgeMk_id]; exact I.homInvId⟩
    have h₂ : g ≫ f = 𝟙 y :=
      (nonempty_compStruct_iff g f (𝟙 y)).1 ⟨by rw [hg, edgeMk_id]; exact I.invHomId⟩
    exact ⟨g, h₁, h₂⟩
  · refine { inv := edgeMk (inv f), homInvId := ?_, invHomId := ?_ }
    · rw [← edgeMk_id]
      exact ((nonempty_compStruct_iff _ _ _).2 (by simp)).some
    · rw [← edgeMk_id]
      exact ((nonempty_compStruct_iff _ _ _).2 (by simp)).some

/-- A `1`-simplex of the nerve of a category is an equivalence exactly when the morphism it
represents is an isomorphism. -/
lemma isEquivalence_mk'_iff (s : (nerve C) _⦋1⦌) : (Edge.mk' s).IsEquivalence ↔ IsIso s.hom := by
  rw [Edge.isEquivalence_iff_of_edge_eq (e' := edgeMk s.hom)
    (by rw [Edge.mk'_edge, edgeMk_edge]; exact (ComposableArrows.mk₁_hom s).symm),
    isEquivalence_edgeMk_iff]

/-- A simplex of the nerve of a category lies in the core exactly when all the morphisms it
contains are isomorphisms. -/
lemma mem_core_iff {n : SimplexCategoryᵒᵖ} (s : (nerve C).obj n) :
    s ∈ (nerve C).core.obj n ↔ ∀ ⦃i j : Fin (n.unop.len + 1)⦄ (f : i ⟶ j), IsIso (s.map f) := by
  rw [SSet.mem_core_iff]
  -- The edge of `s` along `f : ⦋1⦌ ⟶ n.unop` is the morphism `s.map` of the arrow from `f 0` to
  -- `f 1` in the poset `Fin (n.unop.len + 1)`, whose morphisms are unique.
  refine ⟨fun h i j f ↦ (isEquivalence_mk'_iff _).1 (h (SimplexCategory.mkOfLe i j (leOfHom f))),
    fun h f ↦ (isEquivalence_mk'_iff _).2 (h (f.toOrderHom.monotone (Fin.zero_le 1)).hom)⟩

end CategoryTheory.nerve

namespace CategoryTheory.Core

variable (C : Type u) [Category.{v} C]

/-- The nerve of the core of a category is the core of its nerve. -/
noncomputable def nerveIso : nerve (Core C) ≅ ((nerve C).core : SSet) where
  hom := SSet.Subcomplex.lift (nerveMap (inclusion C)) <| by
    rw [SSet.range_le_core_iff]
    intro y
    rw [nerve.isEquivalence_mk'_iff]
    exact (ComposableArrows.hom y).iso.isIso_hom
  inv :=
    { app _ := ↾fun s ↦ functorToCoreOfIsIso s.val ((nerve.mem_core_iff s.val).1 s.property)
      naturality _ _ g := by
        ext s
        exact functorToCoreOfIsIso_comp_left (SimplexCategory.toCat.map g.unop).toFunctor s.val _ }
  hom_inv_id := by
    ext n y
    exact functorToCoreOfIsIso_comp_inclusion_self y
  inv_hom_id := rfl

/-- Under `nerveIso`, the inclusion of the core of the nerve corresponds to the nerve of the
inclusion of the core. -/
@[reassoc (attr := simp)]
lemma nerveIso_hom_ι : (nerveIso C).hom ≫ SSet.Subcomplex.ι _ = nerveMap (inclusion C) :=
  (rfl)

end CategoryTheory.Core
