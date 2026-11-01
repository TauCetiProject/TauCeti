/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Deformation retractions

Two successive strong deformation retractions compose: first deform onto the intermediate
space, then run its deformation after the first retraction. The resulting homotopy fixes
the image of the final inclusion throughout. Inclusions are expressed as continuous maps,
so the result also applies to subspaces represented by different but homeomorphic types; for
subsets of one space, `ContinuousMap.HomotopicRel.exists_inter_deformation_trans` states it with
set inclusions.

A strong deformation retraction of the part of a subspace `A` lying in an open subspace extends
by the identity to all of `A`, provided it already fixes every point of an open set covering the
rest of `A` (`ContinuousMap.HomotopicRel.exists_inter_deformation_of_isOpenEmbedding`). The open
subspace is given as the range of an open embedding `e : M → X`, so the deformation may be
constructed on a manifold `M` which is an open part of a space `X` that is not itself a manifold.

A deformation retraction in the weak sense of `B` onto `A ⊆ B` is a deformation of `B` within
itself, starting at the identity, ending inside `A`, and keeping `A` inside `A` at all times. The
inclusion of `A` is then a homotopy equivalence
(`ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction`). Unlike a strong deformation
retraction, the deformation need not fix `A`, which allows straight-line deformations that slide
points of `A` within `A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Exercise 4
  (deformation retractions in the weak sense).
-/

public section

open Set Function Topology

namespace ContinuousMap.HomotopicRel

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Compose the relative homotopies of two strong deformation retractions. The first
retraction must be a left inverse of its inclusion; no separation or closedness is needed. -/
theorem comp_retractions {i : C(Y, X)} {j : C(Z, Y)} {r : C(X, Y)} {s : C(Y, Z)}
    (hX : (ContinuousMap.id X).HomotopicRel (i.comp r) (range i))
    (hY : (ContinuousMap.id Y).HomotopicRel (j.comp s) (range j))
    (hr : LeftInverse r i) :
    (ContinuousMap.id X).HomotopicRel ((i.comp j).comp (s.comp r)) (range (i.comp j)) := by
  obtain ⟨H⟩ := hX
  obtain ⟨G⟩ := hY
  let H' : (ContinuousMap.id X).HomotopyRel (i.comp r) (range (i.comp j)) :=
    { H with prop' := fun t x hx => H.eq_fst t (by
        obtain ⟨z, rfl⟩ := hx
        exact mem_range_self (j z)) }
  let G' : (i.comp r).HomotopyRel ((i.comp j).comp (s.comp r))
      (range (i.comp j)) :=
    { toFun := fun p => i (G (p.1, r p.2))
      continuous_toFun := i.continuous.comp
        (G.continuous.comp (continuous_fst.prodMk (r.continuous.comp continuous_snd)))
      map_zero_left := fun x => by simp
      map_one_left := fun x => by simp
      prop' := by
        rintro t x ⟨z, rfl⟩
        simpa only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, hr (j z),
          ContinuousMap.id_apply] using congrArg i (G.eq_fst t (mem_range_self z)) }
  exact ⟨H'.trans G'⟩

variable {A B S : Set X} in
/-- **Strong deformation retractions of subspaces compose.** Let `B ⊆ A` be subspaces, and let
`S` be a set with `A ∩ S ⊆ B`. If `B` is a strong deformation retract of `A`, and `B ∩ S` is
one of `B`, then `A ∩ S` is a strong deformation retract of `A`. -/
theorem exists_inter_deformation_trans (hBA : B ⊆ A) (hSB : A ∩ S ⊆ B)
    (h₁ : ∃ r : C(A, B), (∀ b, r (ContinuousMap.inclusion hBA b) = b) ∧
      Nonempty (((ContinuousMap.inclusion hBA).comp r).HomotopyRel (.id A) {x | (x : X) ∈ B}))
    (h₂ : ∃ r : C(B, ↥(B ∩ S)), (∀ b, r (ContinuousMap.inclusion inter_subset_left b) = b) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel (.id B)
        {x | (x : X) ∈ S})) :
    ∃ r : C(A, ↥(A ∩ S)), (∀ a, r (ContinuousMap.inclusion inter_subset_left a) = a) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel (.id A)
        {x | (x : X) ∈ S}) := by
  obtain ⟨r₁, hr₁, ⟨H₁⟩⟩ := h₁
  obtain ⟨r₂, -, ⟨H₂⟩⟩ := h₂
  have e₁ : range (ContinuousMap.inclusion hBA) = {x : A | (x : X) ∈ B} := range_inclusion hBA
  have e₂ : range (ContinuousMap.inclusion (inter_subset_left : B ∩ S ⊆ B)) =
      {x : B | (x : X) ∈ S} :=
    Set.ext fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2.2, fun hx ↦ ⟨⟨x, x.2, hx⟩, rfl⟩⟩
  obtain ⟨H⟩ := comp_retractions (e₁ ▸ ⟨H₁.symm⟩) (by rw [e₂]; exact ⟨H₂.symm⟩) hr₁
  have e : range ((ContinuousMap.inclusion hBA).comp
      (ContinuousMap.inclusion (inter_subset_left : B ∩ S ⊆ B))) = {x : A | (x : X) ∈ S} :=
    Set.ext fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2.2, fun hx ↦ ⟨⟨x, hSB ⟨x.2, hx⟩, hx⟩, rfl⟩⟩
  rw [e] at H
  -- The retraction fixes `A ∩ S`, since the homotopy does.
  exact ⟨(ContinuousMap.inclusion (inter_subset_inter_left S hBA)).comp (r₂.comp r₁),
    fun a ↦ Subtype.ext congr(Subtype.val $(H.symm.fst_eq_snd (x := ⟨a, a.2.1⟩) a.2.2)),
    ⟨H.symm⟩⟩

open scoped unitInterval in
variable {M : Type*} [TopologicalSpace M] {e : M → X} {A S V : Set X} {B T : Set M} in
/-- **Strong deformation retractions extend by the identity across an open embedding.** Let
`e : M → X` be an open embedding, let `A, S ⊆ X`, and let `V ⊆ X` be an open set such that `A`
is covered by the range of `e` and `V`, and `A ∩ V ⊆ S`. If `B = e ⁻¹' A` strong deformation
retracts onto `B ∩ T`, where `T = e ⁻¹' S`, relative to `T`, then `A` strong deformation retracts
onto `A ∩ S` relative to `S`. The deformation of `A` is that of `B` on the range of `e` and the
identity off it. -/
theorem exists_inter_deformation_of_isOpenEmbedding (he : IsOpenEmbedding e) (hV : IsOpen V)
    (hA : A ⊆ range e ∪ V) (hAV : A ∩ V ⊆ S) (hB : e ⁻¹' A = B) (hT : e ⁻¹' S = T)
    (r : C(B, ↥(B ∩ T)))
    (H : ((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel (.id B)
      {x | (x : M) ∈ T}) :
    ∃ r : C(A, ↥(A ∩ S)), (∀ a, r (ContinuousMap.inclusion inter_subset_left a) = a) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel (.id A)
        {x | (x : X) ∈ S}) := by
  subst hB hT
  classical
  -- The point of `B` over a point of `A` in the range of `e`.
  let lift (a : A) (ha : (a : X) ∈ range e) : ↥(e ⁻¹' A) :=
    ⟨he.isEmbedding.toHomeomorph.symm ⟨a, ha⟩, by
      rw [mem_preimage, ← he.isEmbedding.toHomeomorph_apply_coe, Homeomorph.apply_symm_apply]
      exact a.2⟩
  have e_lift (a : A) (ha) : e (lift a ha) = a := by
    rw [← he.isEmbedding.toHomeomorph_apply_coe, Homeomorph.apply_symm_apply]
  let Φ (p : I × A) : A :=
    if hp : (p.2 : X) ∈ range e then ⟨e (H (p.1, lift p.2 hp)), (H (p.1, lift p.2 hp)).2⟩
    else p.2
  -- The deformation fixes `S`, hence also `A ∩ V`.
  have hfix (t : I) (a : A) (ha : (a : X) ∈ S) : Φ (t, a) = a := by
    simp only [Φ]
    split_ifs with h
    · refine Subtype.ext ?_
      simp only
      rw [H.eq_snd t (show ((lift a h : M)) ∈ e ⁻¹' S by
        rw [mem_preimage, e_lift]; exact ha)]
      exact e_lift a h
    · rfl
  have hΦ : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    rcases hA p.2.2 with hp | hp
    · -- On the open set of pairs over the range of `e`, `Φ` is the transported deformation.
      have hW : IsOpen {q : I × A | (q.2 : X) ∈ range e} :=
        he.isOpen_range.preimage (continuous_subtype_val.comp continuous_snd)
      refine (ContinuousOn.continuousAt ?_ (hW.mem_nhds hp))
      rw [continuousOn_iff_continuous_domRestrict]
      have : {q : I × A | (q.2 : X) ∈ range e}.domRestrict Φ =
          fun q ↦ ⟨e (H (q.1.1, lift q.1.2 q.2)), (H (q.1.1, lift q.1.2 q.2)).2⟩ :=
        funext fun q ↦ dite_eq_left q.2
      rw [this]
      refine Continuous.subtype_mk (he.continuous.comp (continuous_subtype_val.comp
        (H.continuous.comp (Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
          (Continuous.subtype_mk (he.isEmbedding.toHomeomorph.symm.continuous.comp
            (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).comp
              continuous_subtype_val) _)) _))))) _
    · -- Near a point over `V`, `Φ` is the identity.
      refine continuous_snd.continuousAt.congr ?_
      filter_upwards [(hV.preimage (continuous_subtype_val.comp continuous_snd)).mem_nhds hp]
        with q hq
      exact (hfix q.1 q.2 (hAV ⟨q.2.2, hq⟩)).symm
  have hS (a : A) : ((Φ (0, a) : A) : X) ∈ S := by
    by_cases h : (a : X) ∈ range e
    · simp only [Φ, h, dite_true, H.apply_zero]
      exact (r (lift a h)).2.2
    · have ha : (a : X) ∈ V := (hA a.2).resolve_left h
      rw [hfix 0 a (hAV ⟨a.2, ha⟩)]
      exact hAV ⟨a.2, ha⟩
  refine ⟨⟨fun a ↦ ⟨Φ (0, a), mem_inter (Φ (0, a)).2 (hS a)⟩, ?_⟩, fun a ↦ ?_, ⟨?_⟩⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp
      (hΦ.comp (continuous_const.prodMk continuous_id))) _
  · have := congrArg Subtype.val (hfix 0 (ContinuousMap.inclusion inter_subset_left a) a.2.2)
    exact Subtype.ext this
  · exact
      { toFun := Φ
        continuous_toFun := hΦ
        map_zero_left := fun a ↦ rfl
        map_one_left := fun a ↦ by
          by_cases h : (a : X) ∈ range e
          · refine Subtype.ext ?_
            simp only [Φ, h, dite_true, H.apply_one, ContinuousMap.id_apply, e_lift]
          · simp only [Φ, h, dite_false, ContinuousMap.id_apply]
        prop' := fun t a ha ↦ by
          have := congrArg Subtype.val (hfix 0 a ha)
          exact (hfix t a ha).trans (Subtype.ext this.symm) }

end ContinuousMap.HomotopicRel

namespace ContinuousMap.HomotopyEquiv

open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] {A B : Set X}

/-- **The inclusion of a weak deformation retract is a homotopy equivalence.** Let `A ⊆ B`, and
let `H : I × B → X` be a deformation of `B` within `B` which starts at the identity, ends inside
`A`, and keeps `A` inside `A` at all times. Then the inclusion `A → B` is a homotopy equivalence,
whose homotopy inverse is the end map of `H`. -/
def ofWeakDeformationRetraction (hAB : A ⊆ B) (H : I × B → X) (hH : Continuous H)
    (hHB : ∀ p, H p ∈ B) (h₀ : ∀ x, H (0, x) = x) (h₁ : ∀ x, H (1, x) ∈ A)
    (hHA : ∀ t (x : B), (x : X) ∈ A → H (t, x) ∈ A) : A ≃ₕ B where
  toFun := ContinuousMap.inclusion hAB
  invFun := ⟨fun x ↦ ⟨H (1, x), h₁ x⟩, by fun_prop⟩
  left_inv := ⟨ContinuousMap.Homotopy.symm
    { toFun := fun p ↦ ⟨H (p.1, ContinuousMap.inclusion hAB p.2), hHA p.1 _ p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun a ↦ Subtype.ext (h₀ _)
      map_one_left := fun _ ↦ rfl }⟩
  right_inv := ⟨ContinuousMap.Homotopy.symm
    { toFun := fun p ↦ ⟨H p, hHB p⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ Subtype.ext (h₀ x)
      map_one_left := fun _ ↦ rfl }⟩

/-- The homotopy equivalence `ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction` is the
inclusion. -/
@[simp]
theorem coe_ofWeakDeformationRetraction_apply (hAB : A ⊆ B) (H : I × B → X) (hH : Continuous H)
    (hHB : ∀ p, H p ∈ B) (h₀ : ∀ x, H (0, x) = x) (h₁ : ∀ x, H (1, x) ∈ A)
    (hHA : ∀ t (x : B), (x : X) ∈ A → H (t, x) ∈ A) (a : A) :
    (ofWeakDeformationRetraction hAB H hH hHB h₀ h₁ hHA a : X) = a :=
  (rfl)

/-- The homotopy inverse of `ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction` is the end
map of the deformation. -/
@[simp]
theorem coe_ofWeakDeformationRetraction_symm_apply (hAB : A ⊆ B) (H : I × B → X)
    (hH : Continuous H) (hHB : ∀ p, H p ∈ B) (h₀ : ∀ x, H (0, x) = x) (h₁ : ∀ x, H (1, x) ∈ A)
    (hHA : ∀ t (x : B), (x : X) ∈ A → H (t, x) ∈ A) (x : B) :
    ((ofWeakDeformationRetraction hAB H hH hHB h₀ h₁ hHA).symm x : X) = H (1, x) :=
  (rfl)

end ContinuousMap.HomotopyEquiv
