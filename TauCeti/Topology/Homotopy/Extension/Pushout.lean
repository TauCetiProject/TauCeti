/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Pushout
public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Homotopy invariance of attaching along a cofibration

Let `i : B → Y` be an embedding whose image has the homotopy extension property, and let
`P = Z ∪_a Y` be the space obtained by attaching `Y` to `Z` along `a : B → Z`, given as a pushout
square in `TopCat` with maps `j : Y → P` and `k : Z → P`. This file shows that, up to homotopy
equivalence, `P` depends only on the homotopy class of the attaching map and on the homotopy type
of `Z`:

* if `K : a₀ ≃ a₁` is a homotopy, there are maps `φ : Z ∪_{a₀} Y → Z ∪_{a₁} Y` and
  `ψ : Z ∪_{a₁} Y → Z ∪_{a₀} Y` which are the identity on `Z` and are inverse to each other up to
  homotopies fixing `Z` (`CategoryTheory.IsPushout.exists_homotopicRel_id_of_homotopy`);
* if `f : Z → Z'` is a homotopy equivalence with homotopy inverse `g`, the map
  `Z ∪_a Y → Z' ∪_{a ≫ f} Y` which is `f` on `Z` and the identity on `Y` is a homotopy
  equivalence, with a homotopy inverse which is `g` on `Z'`
  (`CategoryTheory.IsPushout.exists_homotopic_id_of_homotopic_id`).

For instance, a cell attachment depends only on the homotopy classes of its attaching maps, and
attaching cells to homotopy equivalent spaces along corresponding maps gives homotopy equivalent
spaces. These are the steps by which a space built by successive cell attachments, such as a
sublevel of a Morse function, is compared with a CW complex.

The map `φ` is the identity on `Z`, and on `Y` it is the end of a homotopy starting at `j₁` which,
over `B`, runs backwards along `K`: such a homotopy is provided by the homotopy extension property
of `B`, and at its end it agrees on `B` with `k₁ ∘ a₀`, so it descends to the pushout
(`CategoryTheory.IsPushout.exists_homotopy_inl_comp`). Built from `K` reversed, `ψ` likewise.
On `Y`, the composite `ψ ∘ φ` is then joined to `j₀` by two homotopies, the second of which
retraces the first over `B`, so `TauCeti.HasHomotopyExtensionProperty.homotopicRel_of_retracing`
gives a homotopy fixing `B`. Such a homotopy, together with the constant homotopy on `Z`, descends
to a homotopy on the pushout fixing `Z`
(`CategoryTheory.IsPushout.homotopicRel_of_homotopicRel_comp_inl`), glued by
`CategoryTheory.IsPushout.homotopyDesc` since the product of the pushout with the locally compact
interval is again a pushout. The same descent shows that the
image of `Z` in `Z ∪_a Y` has the homotopy extension property
(`CategoryTheory.IsPushout.hasHomotopyExtensionProperty_range_inr`).

For the change of `Z`, let `F` and `F'` be the maps induced by `f` and `g`. Reattaching along the
homotopy `g ∘ f ∘ a ≃ a` gives a homotopy equivalence `E : Z ∪_{a ≫ f ≫ g} Y → Z ∪_a Y` with
`E ∘ F' ∘ F` homotopic to the identity, by the reattaching homotopy on `Y` and `g ∘ f ≃ id` on `Z`.
The same argument with the roles of `f` and `g` exchanged gives `F'` a left homotopy inverse, while
`F ∘ E` is a right homotopy inverse of `F'`; hence `F'` is a homotopy equivalence and `E ∘ F'` is
a two-sided homotopy inverse of `F`.

## Main declarations

* `CategoryTheory.IsPushout.hasHomotopyExtensionProperty_range_inr`: attaching along a cofibration
  gives a cofibration.
* `CategoryTheory.IsPushout.homotopicRel_of_homotopicRel_comp_inl`: two maps out of `Z ∪_a Y`
  which agree on `Z`, and whose restrictions to `Y` are homotopic relative to `B`, are homotopic
  relative to `Z`.
* `CategoryTheory.IsPushout.exists_homotopy_inl_comp`: the map `Z ∪_{a₀} Y → Z ∪_{a₁} Y` which
  is the identity on `Z` and deforms `Y` backwards along a homotopy `a₀ ≃ a₁`.
* `CategoryTheory.IsPushout.exists_homotopicRel_id_of_homotopy`: **attaching along homotopic maps
  gives spaces which are homotopy equivalent relative to `Z`.**
* `CategoryTheory.IsPushout.exists_homotopic_id_of_homotopic_id`: **a homotopy equivalence of the
  base induces a homotopy equivalence of attachments.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.18.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemmas 3.6 and 3.7, for cells attached to a space.
* R. Brown, *Topology and Groupoids*, 2006, Section 7.5, for the gluing theorem for homotopy
  equivalences.
-/

public section

noncomputable section

open Set Topology unitInterval ContinuousMap TauCeti CategoryTheory.Limits

namespace CategoryTheory.IsPushout

universe u

variable {B Y Z P : TopCat.{u}} {i : B ⟶ Y} {a : B ⟶ Z} {j : Y ⟶ P} {k : Z ⟶ P}

/-- A map out of `I × B`, read on `I × range i` through the inverse of an embedding `i`. -/
private def rangeLift (hi : IsEmbedding i) {W : Type u} [TopologicalSpace W] (G : C(I × B, W)) :
    C(I × range i, W) :=
  G.comp ⟨fun p ↦ (p.1, hi.toHomeomorph.symm p.2), by fun_prop⟩

private theorem rangeLift_apply (hi : IsEmbedding i) {W : Type u} [TopologicalSpace W]
    (G : C(I × B, W)) (t : I) (b : B) : rangeLift hi G (t, ⟨i b, mem_range_self b⟩) = G (t, b) := by
  simp [rangeLift]

/-- **Attaching along a cofibration gives a cofibration.** If `i : B → Y` is an embedding whose
image has the homotopy extension property, then so does the image of `Z` in the space
`P = Z ∪_a Y` obtained by attaching `Y` along `a : B → Z`. -/
theorem hasHomotopyExtensionProperty_range_inr (h : IsPushout i a j k) (hi : IsEmbedding i)
    (hA : HasHomotopyExtensionProperty (range i)) :
    HasHomotopyExtensionProperty (range k) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro W _ f H hH
  -- The homotopy on `Z` read off `H`, transported along `a` to the image of `B` and extended over
  -- `Y` from `f ∘ j`; it is then glued with the homotopy on `Z`.
  let HZ : C(I × Z, W) := H.comp ⟨fun p ↦ (p.1, ⟨k p.2, mem_range_self _⟩), by fun_prop⟩
  have hHZ (t : I) (z : Z) : HZ (t, z) = H (t, ⟨k z, mem_range_self _⟩) := rfl
  let HB : C(I × B, W) := HZ.comp ⟨fun p ↦ (p.1, a p.2), by fun_prop⟩
  obtain ⟨GY, hGY₀, hGY⟩ := hA.exists_extension (f.comp j.hom) (rangeLift hi HB) fun y ↦ by
    obtain ⟨_, b, rfl⟩ := y
    rw [rangeLift_apply]
    simp [HB, hHZ, hH, h.w_apply]
  have hcompat (t : I) (b : B) : GY (t, i b) = HZ (t, a b) :=
    (hGY t ⟨i b, mem_range_self b⟩).trans (rangeLift_apply hi HB t b)
  refine ⟨h.cylinderDesc GY HZ hcompat, fun p ↦ ?_, fun t q ↦ ?_⟩
  · exact h.cylinderDesc_apply_eq _ _ hcompat 0 (fun y ↦ by simpa using hGY₀ y)
      (fun z ↦ by simpa [hHZ] using hH ⟨k z, _⟩) p
  · obtain ⟨_, z, rfl⟩ := q
    simp [hHZ]

/-- **Homotopies on a pushout.** Let `f, g : Z ∪_a Y → W` agree on `Z`. If their restrictions to
`Y` are homotopic relative to the image of `B`, then `f` and `g` are homotopic relative to the
image of `Z`. -/
theorem homotopicRel_of_homotopicRel_comp_inl (h : IsPushout i a j k) {W : Type u}
    [TopologicalSpace W] {f g : C(P, W)} (hk : ∀ z, f (k z) = g (k z))
    (hj : (f.comp j.hom).HomotopicRel (g.comp j.hom) (range i)) :
    f.HomotopicRel g (range k) := by
  obtain ⟨L⟩ := hj
  let HZ : (f.comp k.hom).Homotopy (g.comp k.hom) :=
    (Homotopy.refl _).cast rfl (ContinuousMap.ext hk)
  let M := h.homotopyDesc L.toHomotopy HZ fun t b ↦ by
    simp [HZ, L.eq_fst t (mem_range_self b), h.w_apply]
  exact ⟨{ toHomotopy := M
           prop' := fun t p hp ↦ by
             obtain ⟨z, rfl⟩ := hp
             simp [M, HZ] }⟩

variable {a₀ a₁ : B ⟶ Z} {P₀ P₁ : TopCat.{u}} {j₀ : Y ⟶ P₀} {k₀ : Z ⟶ P₀} {j₁ : Y ⟶ P₁}
  {k₁ : Z ⟶ P₁}

/-- **Reattaching along a homotopy.** Let `K : a₀ ≃ a₁` be a homotopy of attaching maps along an
embedding `i : B → Y` whose image has the homotopy extension property. There is a map
`φ : Z ∪_{a₀} Y → Z ∪_{a₁} Y` which is the identity on `Z`, together with a homotopy from `j₁` to
`φ ∘ j₀` which over `B` runs backwards along `K`. -/
theorem exists_homotopy_inl_comp (h₀ : IsPushout i a₀ j₀ k₀) (h₁ : IsPushout i a₁ j₁ k₁)
    (hi : IsEmbedding i) (hA : HasHomotopyExtensionProperty (range i))
    (K : a₀.hom.Homotopy a₁.hom) :
    ∃ (φ : P₀ ⟶ P₁) (G : j₁.hom.Homotopy (j₀ ≫ φ).hom), k₀ ≫ φ = k₁ ∧
      ∀ t b, G (t, i b) = k₁ (K (σ t, b)) := by
  -- Extend `K`, run backwards and pushed into `Z ∪_{a₁} Y`, from the image of `B` over `Y`.
  let KB : C(I × B, P₁) :=
    k₁.hom.comp (K.toContinuousMap.comp ⟨fun p ↦ (σ p.1, p.2), by fun_prop⟩)
  obtain ⟨G, hG₀, hG⟩ := hA.exists_extension j₁.hom (rangeLift hi KB) fun y ↦ by
    obtain ⟨_, b, rfl⟩ := y
    rw [rangeLift_apply]
    simpa [KB] using (h₁.w_apply b).symm
  have hGi (t : I) (b : B) : G (t, i b) = k₁ (K (σ t, b)) :=
    (hG t ⟨i b, mem_range_self b⟩).trans (rangeLift_apply hi KB t b)
  -- The end of `G` agrees with `k₁ ∘ a₀` on `B`, so it descends to `Z ∪_{a₀} Y`.
  let g₁ : Y ⟶ P₁ := TopCat.ofHom ⟨fun y ↦ G (1, y), by fun_prop⟩
  let φ : P₀ ⟶ P₁ := h₀.desc g₁ k₁ (by ext b; simp [g₁, hGi])
  refine ⟨φ, { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun y ↦ ?_ },
    h₀.inr_desc _ _ _, hGi⟩
  exact (ConcreteCategory.congr_hom (h₀.inl_desc g₁ k₁ _) y).symm

/-- One composite of the two reattachment maps is homotopic to the identity relative to `Z`. -/
private theorem comp_homotopicRel_id (h₀ : IsPushout i a₀ j₀ k₀)
    (hA : HasHomotopyExtensionProperty (range i)) {K : a₀.hom.Homotopy a₁.hom}
    {φ : P₀ ⟶ P₁} {ψ : P₁ ⟶ P₀} (hφ : k₀ ≫ φ = k₁) (hψ : k₁ ≫ ψ = k₀)
    (G : j₁.hom.Homotopy (j₀ ≫ φ).hom) (G' : j₀.hom.Homotopy (j₁ ≫ ψ).hom)
    (hG : ∀ t b, G (t, i b) = k₁ (K (σ t, b))) (hG' : ∀ t b, G' (t, i b) = k₀ (K (t, b))) :
    (ContinuousMap.id P₀).HomotopicRel (φ ≫ ψ).hom (range k₀) := by
  refine h₀.homotopicRel_of_homotopicRel_comp_inl (fun z ↦ ?_) ?_
  · have : k₀ ≫ φ ≫ ψ = k₀ := by rw [reassoc_of% hφ, hψ]
    simpa using (ConcreteCategory.congr_hom this z).symm
  -- On `Y`, the composite is joined to `j₀` by `G'` followed by `ψ ∘ G`, and over `B` the second
  -- homotopy retraces the first.
  let F₁ : j₀.hom.Homotopy (ψ.hom.comp j₁.hom) := G'
  let F₂ : (ψ.hom.comp j₁.hom).Homotopy (ψ.hom.comp (j₀ ≫ φ).hom) :=
    (Homotopy.refl ψ.hom).comp G
  have := hA.homotopicRel_of_retracing F₁ F₂ fun t y hy ↦ by
    obtain ⟨b, rfl⟩ := hy
    simp only [F₁, F₂, Homotopy.comp_apply, Homotopy.refl_apply, hG, hG']
    rw [← ConcreteCategory.comp_apply, hψ]
  simpa using this

/-- **Attaching along homotopic maps.** Let `i : B → Y` be an embedding whose image has the
homotopy extension property, and let `K : a₀ ≃ a₁` be a homotopy of attaching maps `B → Z`. Then
the spaces `Z ∪_{a₀} Y` and `Z ∪_{a₁} Y` are homotopy equivalent relative to `Z`: there are maps
`φ` and `ψ` between them which are the identity on `Z` and whose composites are homotopic to the
identities relative to `Z`. -/
theorem exists_homotopicRel_id_of_homotopy (h₀ : IsPushout i a₀ j₀ k₀)
    (h₁ : IsPushout i a₁ j₁ k₁) (hi : IsEmbedding i)
    (hA : HasHomotopyExtensionProperty (range i)) (K : a₀.hom.Homotopy a₁.hom) :
    ∃ (φ : P₀ ⟶ P₁) (ψ : P₁ ⟶ P₀), k₀ ≫ φ = k₁ ∧ k₁ ≫ ψ = k₀ ∧
      (φ ≫ ψ).hom.HomotopicRel (ContinuousMap.id P₀) (range k₀) ∧
      (ψ ≫ φ).hom.HomotopicRel (ContinuousMap.id P₁) (range k₁) := by
  obtain ⟨φ, G, hφ, hG⟩ := exists_homotopy_inl_comp h₀ h₁ hi hA K
  obtain ⟨ψ, G', hψ, hG'⟩ := exists_homotopy_inl_comp h₁ h₀ hi hA K.symm
  refine ⟨φ, ψ, hφ, hψ, ?_, ?_⟩
  · exact (comp_homotopicRel_id h₀ hA hφ hψ G G' hG fun t b ↦ by simpa using hG' t b).symm
  · exact (comp_homotopicRel_id h₁ hA (K := K.symm) hψ hφ G' G hG'
      (fun t b ↦ by simpa using hG t b)).symm

section ChangeOfBase

variable {Z' P' P'' : TopCat.{u}} {a' : B ⟶ Z'} {a'' : B ⟶ Z} {j' : Y ⟶ P'}
  {k' : Z' ⟶ P'} {j'' : Y ⟶ P''} {k'' : Z ⟶ P''}

/-- If `F` and `F'` are the maps of attachments induced by `f : Z → Z'` and by a left homotopy
inverse `g` of `f`, there is a homotopy equivalence `E` from `Z ∪_{a ≫ f ≫ g} Y` back to
`Z ∪_a Y`, which is the identity on `Z`, with `E ∘ F' ∘ F` homotopic to the identity. -/
private theorem exists_comp_comp_homotopic_id (h : IsPushout i a j k)
    (h'' : IsPushout i a'' j'' k'') (hi : IsEmbedding i)
    (hA : HasHomotopyExtensionProperty (range i)) {f : Z ⟶ Z'} {g : Z' ⟶ Z}
    (ha : a'' = a ≫ f ≫ g) (H : (f ≫ g).hom.Homotopy (ContinuousMap.id Z))
    {F : P ⟶ P'} {F' : P' ⟶ P''} (hF : j ≫ F = j') (hkF : k ≫ F = f ≫ k') (hF' : j' ≫ F' = j'')
    (hkF' : k' ≫ F' = g ≫ k'') :
    ∃ (E : P'' ⟶ P) (ψ : P ⟶ P''), k'' ≫ E = k ∧
      (F ≫ F' ≫ E).hom.Homotopic (ContinuousMap.id P) ∧
      (E ≫ ψ).hom.Homotopic (ContinuousMap.id P'') ∧
      (ψ ≫ E).hom.Homotopic (ContinuousMap.id P) := by
  subst ha
  -- The homotopy `g ∘ f ∘ a ≃ a` of attaching maps, and its reattachment maps.
  let K : (a ≫ f ≫ g).hom.Homotopy a.hom :=
    (H.compContinuousMap a.hom).cast (by simp) (by simp)
  have hK (t : I) (b : B) : K (t, b) = H (t, a b) := rfl
  obtain ⟨E, G, hE, hG⟩ := exists_homotopy_inl_comp h'' h hi hA K
  obtain ⟨ψ, G', hψ, hG'⟩ := exists_homotopy_inl_comp h h'' hi hA K.symm
  refine ⟨E, ψ, hE, ?_, (comp_homotopicRel_id h'' hA hE hψ G G' hG
      fun t b ↦ by simpa using hG' t b).symm.homotopic,
    (comp_homotopicRel_id h hA (K := K.symm) hψ hE G' G hG'
      fun t b ↦ by simpa using hG t b).symm.homotopic⟩
  -- On `Y`, run the reattaching homotopy backwards; on `Z`, run `g ∘ f ≃ id`.
  have hY : (F ≫ F' ≫ E).hom.comp j.hom = (j'' ≫ E).hom := by
    rw [← TopCat.hom_comp, reassoc_of% hF, reassoc_of% hF']
  have hZ : (F ≫ F' ≫ E).hom.comp k.hom = k.hom.comp (f ≫ g).hom := by
    rw [← TopCat.hom_comp, reassoc_of% hkF, reassoc_of% hkF', hE, ← TopCat.hom_comp,
      Category.assoc]
  refine ⟨h.homotopyDesc (G.symm.cast hY.symm (ContinuousMap.id_comp _).symm)
    (((Homotopy.refl k.hom).comp H).cast hZ.symm (by simp)) fun t b ↦ ?_⟩
  simp only [Homotopy.cast_apply, Homotopy.symm_apply, hG, symm_symm, hK, Homotopy.comp_apply,
    Homotopy.refl_apply]

/-- **Changing the base of an attachment by a homotopy equivalence.** Let `i : B → Y` be an
embedding whose image has the homotopy extension property, let `a : B → Z` be an attaching map,
and let `f : Z → Z'` be a homotopy equivalence with homotopy inverse `g`. Then the map
`F : Z ∪_a Y → Z' ∪_{a ≫ f} Y` which is `f` on `Z` and the identity on `Y` is a homotopy
equivalence, with a homotopy inverse which is `g` on `Z'`. -/
theorem exists_homotopic_id_of_homotopic_id (h : IsPushout i a j k)
    (h' : IsPushout i a' j' k') (hi : IsEmbedding i)
    (hA : HasHomotopyExtensionProperty (range i)) {f : Z ⟶ Z'} {g : Z' ⟶ Z}
    (ha : a ≫ f = a') (hfg : (f ≫ g).hom.Homotopic (ContinuousMap.id Z))
    (hgf : (g ≫ f).hom.Homotopic (ContinuousMap.id Z')) {F : P ⟶ P'} (hF : j ≫ F = j')
    (hkF : k ≫ F = f ≫ k') :
    ∃ G : P' ⟶ P, k' ≫ G = g ≫ k ∧ (F ≫ G).hom.Homotopic (ContinuousMap.id P) ∧
      (G ≫ F).hom.Homotopic (ContinuousMap.id P') := by
  subst ha
  obtain ⟨H⟩ := hfg
  obtain ⟨H'⟩ := hgf
  -- The attachments along `a ≫ f ≫ g` and `a ≫ f ≫ g ≫ f`, and the maps induced by `g` and `f`.
  have h₂ := IsPushout.of_hasPushout i (a ≫ f ≫ g)
  have h₃ := IsPushout.of_hasPushout i ((a ≫ f) ≫ g ≫ f)
  let Fg : P' ⟶ pushout i (a ≫ f ≫ g) := h'.desc (pushout.inl _ _) (g ≫ pushout.inr _ _) (by
    simpa [Category.assoc] using h₂.w)
  let Ff : pushout i (a ≫ f ≫ g) ⟶ pushout i ((a ≫ f) ≫ g ≫ f) :=
    h₂.desc (pushout.inl _ _) (f ≫ pushout.inr _ _) (by simpa [Category.assoc] using h₃.w)
  obtain ⟨E, ψ, hk₂, hFE, hEψ, -⟩ := exists_comp_comp_homotopic_id h h₂ hi hA rfl H
    (F' := Fg) hF hkF (h'.inl_desc _ _ _) (h'.inr_desc _ _ _)
  obtain ⟨E', -, -, hFE', -, -⟩ := exists_comp_comp_homotopic_id h' h₃ hi hA rfl H'
    (F := Fg) (F' := Ff) (h'.inl_desc _ _ _) (h'.inr_desc _ _ _) (h₂.inl_desc _ _ _)
    (h₂.inr_desc _ _ _)
  -- `Fg ≫ E` is a left homotopy inverse of `F`; it remains to see that it is a right one.
  refine ⟨Fg ≫ E, by simp [Fg, hk₂], by simpa using hFE, ?_⟩
  simp only [TopCat.hom_comp] at hFE hEψ hFE' ⊢
  -- `ψ` is a left and `F ≫ Fg` a right homotopy inverse of `E`, so `F ≫ Fg` is a left one too.
  have hx : ((Fg.hom.comp F.hom).comp E.hom).Homotopic (ContinuousMap.id _) :=
    ((hEψ.homotopic_of_comp_homotopic_id (r := Fg.hom.comp F.hom) hFE).symm.comp
      (.refl E.hom)).trans hEψ
  -- `Ff ≫ E'` is a left and `E ≫ F` a right homotopy inverse of `Fg`, so `E ≫ F` is a left one too.
  exact ((hFE'.homotopic_of_comp_homotopic_id (r := F.hom.comp E.hom) hx).symm.comp
    (.refl Fg.hom)).trans hFE'

end ChangeOfBase

end CategoryTheory.IsPushout
