/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homotopy.Equiv
import TauCeti.Topology.Category.TopCat.Cylinder

/-!
# Homotopy invariance of attaching along a cofibration

Let `m : B → Y` be an embedding whose image has the homotopy extension property, and let
`a : B → Z` be continuous. The adjunction space `Z ∪_a Y` is the pushout in `TopCat` of `a` and
`m`. This file proves that, up to homotopy equivalence, it depends only on the homotopy class of
the attaching map `a` and on the homotopy type of `Z`.

* **Homotopic attaching maps.** If `a₀` and `a₁` are homotopic, then `Z ∪_{a₀} Y` and
  `Z ∪_{a₁} Y` are homotopy equivalent relative to `Z`: there are maps in both directions which
  are the identity on `Z`, and both composites are homotopic to the identity relative to `Z`
  (`TauCeti.HasHomotopyExtensionProperty.exists_homotopicRel_of_isPushout`). The comparison map
  `Z ∪_{a₀} Y → Z ∪_{a₁} Y` can be any map which is the identity on `Z` and whose restriction to
  `Y` is joined to the inclusion of `Y` by a homotopy reading the homotopy from `a₀` to `a₁` on
  `B` (`TauCeti.HasHomotopyExtensionProperty.exists_inverse_homotopicRel_of_isPushout`).
* **Changing the base.** If `e : Z ≃ₕ Z'` is a homotopy equivalence, the map
  `Z ∪_a Y → Z' ∪_{e ∘ a} Y` which is `e` on `Z` and the identity on `Y` is a homotopy
  equivalence (`TauCeti.HasHomotopyExtensionProperty.exists_homotopyEquiv_of_isPushout`).

These are the gluing comparisons used when the attaching maps of cells are changed within their
homotopy classes, for instance by cellular approximation, or when the space cells are attached
to is replaced by a homotopy equivalent one, such as a CW model.

The proofs extend homotopies from the image of `B` to `Y` using the homotopy extension property,
and glue homotopies on `Z` and on `Y` which agree on `B` into homotopies of the pushout
(`TauCeti.TopCat.cylinderDesc`). For homotopic attaching
maps, the homotopy relative to `Z` comes from a homotopy on `Y` which retraces itself on `B`
(`TauCeti.HasHomotopyExtensionProperty.homotopicRel_of_retracing`). For a change of base, the
comparison map has a left homotopy inverse, built from a homotopy inverse of `e` and the
comparison for homotopic attaching maps; this left inverse has a left homotopy inverse in turn,
so it is a two-sided homotopy inverse.

## Main results

* `TauCeti.HasHomotopyExtensionProperty.exists_inverse_homotopicRel_of_isPushout` and
  `TauCeti.HasHomotopyExtensionProperty.exists_homotopicRel_of_isPushout`: attaching along
  homotopic maps gives spaces which are homotopy equivalent relative to the base.
* `TauCeti.HasHomotopyExtensionProperty.exists_homotopyEquiv_of_isPushout`: a homotopy
  equivalence of the base induces a homotopy equivalence of adjunction spaces.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.18.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemmas 3.6 and 3.7.
* R. Brown, *Topology and Groupoids*, 2006, Section 7.5, for the gluing theorem for homotopy
  equivalences.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Set ContinuousMap unitInterval

universe u

namespace TauCeti

variable {B Y Z P : TopCat.{u}} {m : B ⟶ Y} {a : B ⟶ Z} {j : Z ⟶ P} {k : Y ⟶ P}

/-- A self-map `E` of the pushout which is the identity on `Z`, and whose restriction to `Y` is
homotopic to the inclusion relative to `B`, is homotopic to the identity relative to `Z`. -/
private theorem homotopicRel_id_of_isPushout (h : IsPushout a m j k) {E : P ⟶ P}
    (hE : j ≫ E = j) (hk : (k ≫ E).hom.HomotopicRel k.hom (range m)) :
    E.hom.HomotopicRel (ContinuousMap.id P) (range j) := by
  obtain ⟨H⟩ := hk
  have hEj (z : Z) : E.hom (j.hom z) = j.hom z := by
    simpa using ConcreteCategory.congr_hom hE z
  have hHm (t : I) (b : B) : j (a b) = H (t, m b) := by
    rw [H.eq_snd t ⟨b, rfl⟩]
    simpa using ConcreteCategory.congr_hom h.w b
  let D := TopCat.cylinderDesc h (j.hom.comp ContinuousMap.snd) H.toContinuousMap hHm
  refine ⟨{ toContinuousMap := D
            map_zero_left := fun p ↦ TopCat.cylinderDesc_apply_eq h _ _ hHm
              (fun z ↦ by simp [hEj]) (fun y ↦ by simp) p
            map_one_left := fun p ↦ TopCat.cylinderDesc_apply_eq h _ _ hHm
              (φ := id) (fun z ↦ by simp) (fun y ↦ by simp) p
            prop' := fun t p hp ↦ ?_ }⟩
  obtain ⟨z, rfl⟩ := hp
  exact (TopCat.cylinderDesc_inl h _ _ hHm t z).trans (hEj z).symm

variable {Z' P₀ P₁ : TopCat.{u}} {a₀ a₁ : B ⟶ Z} {j₀ : Z ⟶ P₀} {k₀ : Y ⟶ P₀} {j₁ : Z ⟶ P₁}
  {k₁ : Y ⟶ P₁}

/-- **Attaching along homotopic maps, for a given comparison map.** Let `m : B → Y` be an
embedding whose image has the homotopy extension property, let `F` be a homotopy from `a₀` to
`a₁ : B → Z`, and let `P₀` and `P₁` be the pushouts of `a₀` and of `a₁` along `m`. Let
`Φ : P₀ → P₁` be the identity on `Z`, with a homotopy `G` from its restriction to `Y` to the
inclusion of `Y` into `P₁` which follows `F` along `m`. Then `Φ` is a homotopy equivalence
relative to `Z`: it has a homotopy inverse `Ψ` which is the identity on `Z`, and both composites
are homotopic to the identity relative to `Z`. -/
theorem HasHomotopyExtensionProperty.exists_inverse_homotopicRel_of_isPushout
    (hm : IsEmbedding m) (hA : HasHomotopyExtensionProperty (range m))
    (F : a₀.hom.Homotopy a₁.hom) (h₀ : IsPushout a₀ m j₀ k₀) (h₁ : IsPushout a₁ m j₁ k₁)
    {Φ : P₀ ⟶ P₁} (hΦ : j₀ ≫ Φ = j₁) (G : (k₀ ≫ Φ).hom.Homotopy k₁.hom)
    (hG : ∀ t b, G (t, m b) = j₁ (F (t, b))) :
    ∃ Ψ : P₁ ⟶ P₀, j₁ ≫ Ψ = j₀ ∧
      (Φ ≫ Ψ).hom.HomotopicRel (ContinuousMap.id P₀) (range j₀) ∧
      (Ψ ≫ Φ).hom.HomotopicRel (ContinuousMap.id P₁) (range j₁) := by
  have hΦj (z : Z) : Φ.hom (j₀.hom z) = j₁.hom z := by
    simpa using ConcreteCategory.congr_hom hΦ z
  -- Extend the homotopy `j₀ ∘ F` from `B` to a homotopy `G₀` on `Y` starting at the inclusion.
  obtain ⟨G₀, hG₀, hG₀m⟩ := hA.exists_extension_of_isEmbedding hm k₀.hom
    (j₀.hom.comp F.toContinuousMap) fun b ↦ by
      simpa using ConcreteCategory.congr_hom h₀.w b
  -- Its end `ψ` attaches to `j₀` along `a₁`, giving `Ψ`.
  let ψ : C(Y, P₀) := ⟨fun y ↦ G₀ (1, y), by fun_prop⟩
  let Ψ : P₁ ⟶ P₀ := h₁.desc j₀ (TopCat.ofHom ψ) (by
    ext b
    simp [ψ, hG₀m])
  have hΨj (z : Z) : Ψ.hom (j₁.hom z) = j₀.hom z := by
    simpa using ConcreteCategory.congr_hom (h₁.inl_desc j₀ (TopCat.ofHom ψ) _) z
  have hΨk (y : Y) : Ψ.hom (k₁.hom y) = G₀ (1, y) := by
    simpa [ψ] using ConcreteCategory.congr_hom (h₁.inr_desc j₀ (TopCat.ofHom ψ) _) y
  refine ⟨Ψ, h₁.inl_desc _ _ _, ?_, ?_⟩
  · -- On `Y`, `Ψ ∘ G` runs from `Ψ ∘ Φ` to `ψ`, and `G₀` reversed runs back from `ψ` to the
    -- inclusion, retracing the first homotopy along `m`.
    refine homotopicRel_id_of_isPushout h₀ (by rw [← Category.assoc, hΦ, h₁.inl_desc]) ?_
    let L : (k₀ ≫ Φ ≫ Ψ).hom.Homotopy ψ :=
      { toFun := fun p ↦ Ψ.hom (G p)
        map_zero_left := fun y ↦ by simp
        map_one_left := fun y ↦ by simp [hΨk, ψ] }
    have hL (p : I × Y) : L p = Ψ.hom (G p) := rfl
    let M : ψ.Homotopy k₀.hom :=
      { toFun := fun p ↦ G₀ (σ p.1, p.2)
        map_zero_left := fun y ↦ by simp [ψ]
        map_one_left := fun y ↦ by simp [hG₀] }
    have hM (p : I × Y) : M p = G₀ (σ p.1, p.2) := rfl
    refine hA.homotopicRel_of_retracing L M fun t y hy ↦ ?_
    obtain ⟨b, rfl⟩ := hy
    simp [hL, hM, hG₀m, hG, hΨj]
  · -- On `Y`, `Φ ∘ G₀` reversed runs from `Φ ∘ ψ` to `Φ` on `Y`, and `G` runs on to the inclusion,
    -- retracing the first homotopy along `m`.
    refine homotopicRel_id_of_isPushout h₁ (by rw [← Category.assoc, h₁.inl_desc, hΦ]) ?_
    let L : (k₁ ≫ Ψ ≫ Φ).hom.Homotopy (k₀ ≫ Φ).hom :=
      { toFun := fun p ↦ Φ.hom (G₀ (σ p.1, p.2))
        map_zero_left := fun y ↦ by simp [hΨk]
        map_one_left := fun y ↦ by simp [hG₀] }
    have hL (p : I × Y) : L p = Φ.hom (G₀ (σ p.1, p.2)) := rfl
    refine hA.homotopicRel_of_retracing L G fun t y hy ↦ ?_
    obtain ⟨b, rfl⟩ := hy
    simp [hL, hG₀m, hG, hΦj]

/-- **Attaching along homotopic maps** (Hatcher, Proposition 0.18). Let `m : B → Y` be an
embedding whose image has the homotopy extension property, and let `a₀` and `a₁ : B → Z` be
homotopic. Then the pushouts `P₀ = Z ∪_{a₀} Y` and `P₁ = Z ∪_{a₁} Y` are homotopy equivalent
relative to `Z`: there are maps `Φ : P₀ → P₁` and `Ψ : P₁ → P₀` which are the identity on `Z`,
and both composites are homotopic to the identity relative to `Z`. -/
theorem HasHomotopyExtensionProperty.exists_homotopicRel_of_isPushout
    (hm : IsEmbedding m) (hA : HasHomotopyExtensionProperty (range m))
    (F : a₀.hom.Homotopy a₁.hom) (h₀ : IsPushout a₀ m j₀ k₀) (h₁ : IsPushout a₁ m j₁ k₁) :
    ∃ (Φ : P₀ ⟶ P₁) (Ψ : P₁ ⟶ P₀), j₀ ≫ Φ = j₁ ∧ j₁ ≫ Ψ = j₀ ∧
      (Φ ≫ Ψ).hom.HomotopicRel (ContinuousMap.id P₀) (range j₀) ∧
      (Ψ ≫ Φ).hom.HomotopicRel (ContinuousMap.id P₁) (range j₁) := by
  -- Extend the reversed homotopy `j₁ ∘ F` from `B` to a homotopy `G₁` on `Y` starting at the
  -- inclusion; its end `φ` attaches to `j₁` along `a₀`, giving `Φ`.
  obtain ⟨G₁, hG₁, hG₁m⟩ := hA.exists_extension_of_isEmbedding hm k₁.hom
    (j₁.hom.comp (F.toContinuousMap.comp ((ContinuousMap.mk σ).prodMap (ContinuousMap.id B))))
    fun b ↦ by
      simpa using ConcreteCategory.congr_hom h₁.w b
  let φ : C(Y, P₁) := ⟨fun y ↦ G₁ (1, y), by fun_prop⟩
  let Φ : P₀ ⟶ P₁ := h₀.desc j₁ (TopCat.ofHom φ) (by
    ext b
    simp [φ, hG₁m])
  have hΦk (y : Y) : Φ.hom (k₀.hom y) = G₁ (1, y) := by
    simpa [φ] using ConcreteCategory.congr_hom (h₀.inr_desc j₁ (TopCat.ofHom φ) _) y
  let G : (k₀ ≫ Φ).hom.Homotopy k₁.hom :=
    { toFun := fun p ↦ G₁ (σ p.1, p.2)
      map_zero_left := fun y ↦ by simp [hΦk]
      map_one_left := fun y ↦ by simp [hG₁] }
  have hG (p : I × Y) : G p = G₁ (σ p.1, p.2) := rfl
  obtain ⟨Ψ, hΨ, hΦΨ, hΨΦ⟩ := hA.exists_inverse_homotopicRel_of_isPushout hm F h₀ h₁
    (h₀.inl_desc _ _ _) G fun t b ↦ by simp [hG, hG₁m]
  exact ⟨Φ, Ψ, h₀.inl_desc _ _ _, hΨ, hΦΨ, hΨΦ⟩

/-- A change of base along a map `g : Z → Z'` with a left homotopy inverse `g'` has a left
homotopy inverse, which factors through the change of base along `g'` followed by a homotopy
equivalence. -/
private theorem exists_homotopyEquiv_comp_homotopic_id_of_isPushout (hm : IsEmbedding m)
    (hA : HasHomotopyExtensionProperty (range m)) {g : Z ⟶ Z'} {g' : Z' ⟶ Z}
    (K : (g ≫ g').hom.Homotopy (ContinuousMap.id Z)) {P' P'' : TopCat.{u}} {j' : Z' ⟶ P'}
    {k' : Y ⟶ P'} {j'' : Z ⟶ P''} {k'' : Y ⟶ P''} (h : IsPushout a m j k)
    (h'' : IsPushout (a ≫ g ≫ g') m j'' k'') {Φ : P ⟶ P'} (hΦj : j ≫ Φ = g ≫ j')
    (hΦk : k ≫ Φ = k') {Φ' : P' ⟶ P''} (hΦ'j : j' ≫ Φ' = g' ≫ j'') (hΦ'k : k' ≫ Φ' = k'') :
    ∃ Θ : P'' ⟶ P, (∃ Θ' : P ⟶ P'', (Θ ≫ Θ').hom.Homotopic (ContinuousMap.id P'') ∧
        (Θ' ≫ Θ).hom.Homotopic (ContinuousMap.id P)) ∧
      (Φ ≫ Φ' ≫ Θ).hom.Homotopic (ContinuousMap.id P) := by
  -- The homotopy `K` from `g' ∘ g` to the identity, read along `a`.
  let F : (a ≫ g ≫ g').hom.Homotopy a.hom :=
    { toFun := fun p ↦ K (p.1, a.hom p.2)
      map_zero_left := fun b ↦ by simp
      map_one_left := fun b ↦ by simp }
  have hF (p : I × B) : F p = K (p.1, a.hom p.2) := rfl
  -- Extend `j ∘ F` reversed from `B` to `G` on `Y` starting at the inclusion; its end `φ`
  -- attaches to `j` along `a ≫ g ≫ g'`, giving `Θ`.
  obtain ⟨G, hG₀, hGm⟩ := hA.exists_extension_of_isEmbedding hm k.hom
    (j.hom.comp (F.toContinuousMap.comp ((ContinuousMap.mk σ).prodMap (ContinuousMap.id B))))
    fun b ↦ by
      simpa [hF] using ConcreteCategory.congr_hom h.w b
  let φ : C(Y, P) := ⟨fun y ↦ G (1, y), by fun_prop⟩
  let Θ : P'' ⟶ P := h''.desc j (TopCat.ofHom φ) (by
    ext b
    simp [φ, hGm, hF])
  have hΘk (y : Y) : Θ.hom (k''.hom y) = G (1, y) := by
    simpa [φ] using ConcreteCategory.congr_hom (h''.inr_desc j (TopCat.ofHom φ) _) y
  refine ⟨Θ, ?_, ?_⟩
  · -- `Θ` is the comparison map for the homotopic attaching maps `a ≫ g ≫ g'` and `a`.
    let G' : (k'' ≫ Θ).hom.Homotopy k.hom :=
      { toFun := fun p ↦ G (σ p.1, p.2)
        map_zero_left := fun y ↦ by simp [hΘk]
        map_one_left := fun y ↦ by simp [hG₀] }
    have hG' (p : I × Y) : G' p = G (σ p.1, p.2) := rfl
    obtain ⟨Θ', -, hΘΘ', hΘ'Θ⟩ := hA.exists_inverse_homotopicRel_of_isPushout hm F h'' h
      (h''.inl_desc _ _ _) G' fun t b ↦ by simp [hG', hGm]
    exact ⟨Θ', hΘΘ'.homotopic, hΘ'Θ.homotopic⟩
  · -- Glue `j ∘ K` on `Z` and `G` reversed on `Y`.
    have hLC (t : I) (b : B) : (j.hom.comp K.toContinuousMap) (t, a b) =
        (G.comp ((ContinuousMap.mk σ).prodMap (ContinuousMap.id Y))) (t, m b) := by
      simp [hGm, hF]
    have hj : j ≫ Φ ≫ Φ' ≫ Θ = g ≫ g' ≫ j := by
      rw [reassoc_of% hΦj, reassoc_of% hΦ'j, h''.inl_desc]
    have hk : k ≫ Φ ≫ Φ' ≫ Θ = TopCat.ofHom φ := by
      rw [reassoc_of% hΦk, reassoc_of% hΦ'k, h''.inr_desc]
    exact ⟨{ toContinuousMap := TopCat.cylinderDesc h _ _ hLC
             map_zero_left := fun p ↦ TopCat.cylinderDesc_apply_eq h _ _ hLC
               (fun z ↦ by simpa using ConcreteCategory.congr_hom hj z)
               (fun y ↦ by simpa [φ] using ConcreteCategory.congr_hom hk y) p
             map_one_left := fun p ↦ TopCat.cylinderDesc_apply_eq h _ _ hLC
               (φ := id) (fun z ↦ by simp) (fun y ↦ by simp [hG₀]) p }⟩

/-- **Changing the base of an adjunction space by a homotopy equivalence** (Milnor, Lemma 3.7).
Let `m : B → Y` be an embedding whose image has the homotopy extension property, let
`a : B → Z`, and let `e : Z ≃ₕ Z'` be a homotopy equivalence. Let `P = Z ∪_a Y` and
`P' = Z' ∪_{e ∘ a} Y` be the pushouts along `m`. Then the map `Φ : P → P'` which is `e` on `Z` and
the identity on `Y` is a homotopy equivalence. -/
theorem HasHomotopyExtensionProperty.exists_homotopyEquiv_of_isPushout (hm : IsEmbedding m)
    (hA : HasHomotopyExtensionProperty (range m)) (e : Z ≃ₕ Z') {P' : TopCat.{u}}
    {j' : Z' ⟶ P'} {k' : Y ⟶ P'} (h : IsPushout a m j k)
    (h' : IsPushout (a ≫ TopCat.ofHom e.toFun) m j' k') {Φ : P ⟶ P'}
    (hΦj : j ≫ Φ = TopCat.ofHom e.toFun ≫ j') (hΦk : k ≫ Φ = k') :
    ∃ E : P ≃ₕ P', E.toFun = Φ.hom := by
  set g : Z ⟶ Z' := TopCat.ofHom e.toFun
  let g' : Z' ⟶ Z := TopCat.ofHom e.invFun
  obtain ⟨K⟩ : (g ≫ g').hom.Homotopic (ContinuousMap.id Z) := e.left_inv
  obtain ⟨K'⟩ : (g' ≫ g).hom.Homotopic (ContinuousMap.id Z') := e.right_inv
  -- The change of base `Φ'` along `g'`, and the change of base `Φ''` along `g` after it.
  have h₂ := IsPushout.of_hasPushout ((a ≫ g) ≫ g') m
  have h₃ := IsPushout.of_hasPushout (((a ≫ g) ≫ g') ≫ g) m
  let Φ' := h'.desc (g' ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← Category.assoc]
    exact pushout.condition)
  let Φ'' := h₂.desc (g ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← Category.assoc]
    exact pushout.condition)
  -- `Ψ = Φ' ≫ Θ` is a left homotopy inverse of `Φ`, with `Θ` a homotopy equivalence.
  obtain ⟨Θ, ⟨Θ', hΘΘ', -⟩, hΦΨ⟩ := exists_homotopyEquiv_comp_homotopic_id_of_isPushout hm hA K
    h (by simpa using h₂) hΦj hΦk (h'.inl_desc _ _ _) (h'.inr_desc _ _ _)
  -- `Λ = Φ'' ≫ Θ₁` is a left homotopy inverse of `Φ'`.
  obtain ⟨Θ₁, -, hΦ'Λ⟩ := exists_homotopyEquiv_comp_homotopic_id_of_isPushout hm hA K'
    h' (by simpa using h₃) (h'.inl_desc _ _ _) (h'.inr_desc _ _ _) (h₂.inl_desc _ _ _)
    (h₂.inr_desc _ _ _)
  -- So `Θ' ≫ Λ` is a left homotopy inverse of `Ψ`, and `Ψ` is also a right homotopy inverse.
  set Ψ := Φ' ≫ Θ
  have hΨ : (Ψ ≫ Θ' ≫ Φ'' ≫ Θ₁).hom.Homotopic (ContinuousMap.id P') := by
    have := ((Homotopic.refl (Φ'' ≫ Θ₁).hom).comp hΘΘ').comp (Homotopic.refl Φ'.hom)
    simp only [TopCat.hom_comp] at this hΦ'Λ ⊢
    exact this.trans hΦ'Λ
  have hΨΦ : (Ψ ≫ Φ).hom.Homotopic (ContinuousMap.id P') := by
    -- `Φ ∘ Ψ ≃ (Ψ' ∘ Ψ) ∘ (Φ ∘ Ψ) = Ψ' ∘ (Ψ ∘ Φ) ∘ Ψ ≃ Ψ' ∘ Ψ ≃ id`, with `Ψ' = Λ ∘ Θ'`.
    have hmid := ((Homotopic.refl (Θ' ≫ Φ'' ≫ Θ₁).hom).comp hΦΨ).comp (Homotopic.refl Ψ.hom)
    have hleft := hΨ.comp (Homotopic.refl (Ψ ≫ Φ).hom)
    simp only [TopCat.hom_comp, ContinuousMap.id_comp, ContinuousMap.comp_id,
      ContinuousMap.comp_assoc] at hmid hleft hΨ ⊢
    exact (hleft.symm.trans hmid).trans hΨ
  exact ⟨⟨Φ.hom, Ψ.hom, hΦΨ, hΨΦ⟩, rfl⟩

end TauCeti
