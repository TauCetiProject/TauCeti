/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.LocalAtTarget
public import TauCeti.Topology.Homeomorph.Extend

/-!
# Deformation retractions

Two successive strong deformation retractions compose: first deform onto the intermediate
space, then run its deformation after the first retraction. The resulting homotopy fixes
the image of the final inclusion throughout. Inclusions are expressed as continuous maps,
so the result also applies to subspaces represented by different but homeomorphic types; for
subsets of one space, `ContinuousMap.HomotopicRel.exists_inter_deformation_trans` states it with
set inclusions.
Strong deformation retractions of subsets also transport along homeomorphisms
(`Homeomorph.exists_deformation_of_image_eq`).

A deformation retraction — a map `i : Y → Z` with a continuous left inverse `r : Z → Y` such that
`i ∘ r` is homotopic to the identity — exhibits `i` as a homotopy equivalence `Y ≃ₕ Z`
(`ContinuousMap.HomotopyEquiv.ofDeformationRetraction`). More generally, a deformation retraction in
the weak sense of `B` onto `A ⊆ B` is a deformation of `B` within itself, starting at the identity,
ending inside `A`, and keeping `A` inside `A` at all times; the inclusion of `A` is then a homotopy
equivalence (`ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction`). Unlike a strong
deformation retraction, the deformation need not fix `A`, which allows straight-line deformations
that slide points of `A` within `A`.

Deformations of an open piece extend by the identity. Let `j : Y → X` be an open embedding. A
continuous family of self-maps of `Y` which fixes the points of `j ⁻¹' V`, for an open
neighbourhood `V` of the complement of the range of `j`, extends by the identity to a continuous
family of self-maps of `X` (`Topology.IsOpenEmbedding.exists_continuousMap_extend_id`). Hence a
strong deformation retraction of `j ⁻¹' S` onto `j ⁻¹' T` extends to one of `S` onto `T`,
provided the points of `S` outside the range of `j` have an open neighbourhood `V` with
`S ∩ V ⊆ T` (`Topology.IsOpenEmbedding.exists_deformation_of_preimage`). This is how deformations
of the smooth part `X \ A` of a space, built for instance from the flow of a function `F` that is
small near the closed set `A`, are turned into deformations of `X` fixing `A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Exercise 4
  (deformation retractions in the weak sense).
-/

public section

open Set Function

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

end ContinuousMap.HomotopicRel

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Strong deformation retractions transport along homeomorphisms.** If `B` is a strong
deformation retract of `A ⊇ B` and a homeomorphism `e` carries `A` onto `A'` and `B` onto `B'`,
then `B'` is a strong deformation retract of `A'`. The images are given as equations, so that
`A'` and `B'` may be described independently of `e`. -/
theorem exists_deformation_of_image_eq (e : X ≃ₜ Y) {A B : Set X} {A' B' : Set Y}
    (hBA : B ⊆ A) (hBA' : B' ⊆ A') (hA : e '' A = A') (hB : e '' B = B')
    (h : ∃ r : C(A, B), (∀ b, r (ContinuousMap.inclusion hBA b) = b) ∧
      Nonempty (((ContinuousMap.inclusion hBA).comp r).HomotopyRel (.id A) {x | (x : X) ∈ B})) :
    ∃ r : C(A', B'), (∀ b, r (ContinuousMap.inclusion hBA' b) = b) ∧
      Nonempty (((ContinuousMap.inclusion hBA').comp r).HomotopyRel (.id A')
        {y | (y : Y) ∈ B'}) := by
  subst hA hB
  obtain ⟨r, hr, ⟨H⟩⟩ := h
  -- Conjugate the retraction and the homotopy by the restrictions of `e`.
  have hsymm (b : e '' B) : (e.image A).symm (ContinuousMap.inclusion hBA' b) =
      ContinuousMap.inclusion hBA ((e.image B).symm b) :=
    (e.image A).symm_apply_eq.2 (Subtype.ext (by simp))
  refine ⟨((e.image B : C(B, e '' B))).comp (r.comp ((e.image A).symm : C(e '' A, A))),
    fun b => by simp [hsymm, hr], ⟨?_⟩⟩
  exact
    { toFun := fun p => e.image A (H (p.1, (e.image A).symm p.2))
      continuous_toFun := by fun_prop
      map_zero_left := fun a => Subtype.ext (by simp)
      map_one_left := fun a => by simp
      prop' := fun t a ha => by
        obtain ⟨b, rfl⟩ : ∃ b : e '' B, ContinuousMap.inclusion hBA' b = a := ⟨⟨a, ha⟩, rfl⟩
        have hb := H.eq_snd t (x := ContinuousMap.inclusion hBA ((e.image B).symm b))
          ((e.image B).symm b).2
        simp only [ContinuousMap.id_apply] at hb
        exact Subtype.ext (by simp [hsymm, hb, hr]) }

end Homeomorph

namespace ContinuousMap.HomotopyEquiv

open scoped unitInterval

/-- **A deformation retraction gives a homotopy equivalence.** If `r : C(Z, Y)` is a left inverse
of `i : C(Y, Z)` and `i ∘ r` is homotopic to the identity of `Z`, then `i` is a homotopy
equivalence `Y ≃ₕ Z` with homotopy inverse `r`. The definition is `@[expose]`d so that its forward
and backward continuous maps are `i` and `r` by `rfl` in downstream modules. -/
@[expose] def ofDeformationRetraction {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (i : C(Y, Z)) (r : C(Z, Y)) (hri : LeftInverse r i)
    (hir : (i.comp r).Homotopic (ContinuousMap.id Z)) : Y ≃ₕ Z where
  toFun := i
  invFun := r
  left_inv :=
    have h : r.comp i = ContinuousMap.id Y := ContinuousMap.ext hri
    h ▸ ContinuousMap.Homotopic.refl _
  right_inv := hir

/-- `ContinuousMap.HomotopyEquiv.ofDeformationRetraction` acts on points as `i`. -/
@[simp]
theorem ofDeformationRetraction_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (i : C(Y, Z)) (r : C(Z, Y)) (hri : LeftInverse r i)
    (hir : (i.comp r).Homotopic (ContinuousMap.id Z)) (y : Y) :
    ofDeformationRetraction i r hri hir y = i y :=
  (rfl)

/-- The homotopy inverse of `ContinuousMap.HomotopyEquiv.ofDeformationRetraction` acts on points
as `r`. -/
@[simp]
theorem ofDeformationRetraction_symm_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (i : C(Y, Z)) (r : C(Z, Y)) (hri : LeftInverse r i)
    (hir : (i.comp r).Homotopic (ContinuousMap.id Z)) (z : Z) :
    (ofDeformationRetraction i r hri hir).symm z = r z :=
  (rfl)

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

namespace Topology.IsOpenEmbedding

open unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {j : Y → X}

/-- **A strong deformation retraction extends by the identity off an open embedding.** Let
`j : Y → X` be an open embedding and `T ⊆ S` subsets of `X`, with preimages `t ⊆ s` in `Y`.
Suppose the points of `S` outside the range of `j` have an open neighbourhood `V` with
`S ∩ V ⊆ T`. If `H` is a strong deformation retraction of `s` onto `t`, then `T` is a strong
deformation retract of `S`: the deformation is `H` transported along `j` and extended by the
identity, which it already is on `j ⁻¹' V`. -/
theorem exists_deformation_of_preimage (hj : IsOpenEmbedding j) {S T V : Set X} {s t : Set Y}
    (hTS : T ⊆ S) (hts : t ⊆ s) (hs : j ⁻¹' S = s) (ht : j ⁻¹' T = t) (hV : IsOpen V)
    (hSV : S \ range j ⊆ V) (hVT : S ∩ V ⊆ T) (r : C(s, t))
    (H : ((ContinuousMap.inclusion hts).comp r).HomotopyRel (.id s) {y | (y : Y) ∈ t}) :
    ∃ r : C(S, T), (∀ x, r (ContinuousMap.inclusion hTS x) = x) ∧
      Nonempty (((ContinuousMap.inclusion hTS).comp r).HomotopyRel (.id S) {x | (x : X) ∈ T}) := by
  subst hs ht
  -- Restricted to `j ⁻¹' S`, `j` is an open embedding into `S`, along which `H` extends.
  let k : j ⁻¹' S → S := S.restrictPreimage j
  have hkS {x : S} (hx : x ∉ range k) : (x : X) ∈ V :=
    hSV ⟨x.2, fun ⟨y, hy⟩ ↦ hx ⟨⟨y, by simp [hy, x.2]⟩, Subtype.ext hy⟩⟩
  obtain ⟨G, hGk, hG⟩ := (S.restrictPreimage_isOpenEmbedding hj).exists_continuousMap_extend_id
    (hV.preimage continuous_subtype_val) (fun _ ↦ hkS) H.toContinuousMap
    fun t y hy ↦ H.eq_snd t (hVT ⟨y.2, hy⟩)
  -- The extended deformation fixes every point of `T` and starts inside `T`.
  have hGT (t : I) (x : S) (hx : (x : X) ∈ T) : G (t, x) = x := by
    by_cases hxk : x ∈ range k
    · obtain ⟨y, rfl⟩ := hxk
      exact (hGk t y).trans (congrArg k (H.eq_snd t hx))
    · exact hG t x hxk
  have hG₀ (x : S) : (G (0, x) : X) ∈ T := by
    by_cases hxk : x ∈ range k
    · obtain ⟨y, rfl⟩ := hxk
      rw [hGk, ContinuousMap.HomotopyWith.coe_toContinuousMap, H.apply_zero]
      exact (r y).2
    · rw [hG 0 x hxk]
      exact hVT ⟨x.2, hkS hxk⟩
  refine ⟨⟨fun x ↦ ⟨G (0, x), hG₀ x⟩, by fun_prop⟩,
    fun x ↦ Subtype.ext congr(Subtype.val $(hGT 0 (ContinuousMap.inclusion hTS x) x.2)), ⟨
      { toFun := G
        map_zero_left := fun _ ↦ rfl
        map_one_left := fun x ↦ ?_
        prop' := fun t x hx ↦ (hGT t x hx).trans (hGT 0 x hx).symm }⟩⟩
  by_cases hxk : x ∈ range k
  · obtain ⟨y, rfl⟩ := hxk
    exact (hGk 1 y).trans (congrArg k (H.apply_one y))
  · exact hG 1 x hxk

end Topology.IsOpenEmbedding
