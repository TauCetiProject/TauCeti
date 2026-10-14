/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# Extending disjoint open sets along maps of `TopCat`

A map `f : X ⟶ Y` of topological spaces *extends disjoint open sets*
(`TauCeti.TopCat.extendsDisjointOpens`) if every pair of disjoint open subsets of `X` is the
preimage of a pair of disjoint open subsets of `Y` (`TauCeti.TopCat.extendsDisjointOpens_iff`).
A pair of disjoint open subsets of `X` is the same as a continuous map from `X` to the space
`TauCeti.TopCat.disjointOpensClassifier` of pairs of propositions which are not both true, a
subspace of the square of the Sierpiński space `Prop`. So these are the maps with the left lifting
property with respect to the map from that space to a point, and the general theory of lifting
properties shows that they are stable under cobase change, coproducts and transfinite composition.
In particular a relative cell complex in `TopCat` whose cells extend disjoint open sets extends
disjoint open sets.

The application is to Hausdorffness of cell complexes: two points separated by open sets stay
separated after a map which extends disjoint open sets.

* `TauCeti.TopCat.t2Space_of_isColimit`: the colimit of a directed diagram of Hausdorff spaces is
  Hausdorff if the maps to the colimit extend disjoint open sets.
* `TauCeti.TopCat.t2Space_of_isPushout`: attaching a regular Hausdorff space `B` to a Hausdorff
  space along a map `m : A ⟶ B` with closed range which extends disjoint open sets gives a
  Hausdorff space.

Both rest on the description of the open sets of a colimit in `TopCat` through their preimages:
in a pushout square, two compatible pairs of disjoint open sets of the two sides glue to a pair of
disjoint open sets of the corner (`TauCeti.TopCat.exists_disjoint_isOpen_of_isPushout`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix: the open neighbourhoods `N_ε(A)` of subsets of a cell complex, which are built cell by
  cell in the same way, and the proof of Proposition A.3 that cell complexes are normal.
-/

public section

open CategoryTheory Limits MorphismProperty Topology

universe w u

namespace TauCeti.TopCat

/-- The space classifying pairs of disjoint open sets: the pairs `(p, q)` of propositions which
are not both true, as a subspace of the square of the Sierpiński space `Prop`, lifted to universe
`u`. A pair `(U, V)` of disjoint open subsets of a space `X` corresponds to the continuous map
`x ↦ (x ∈ U, x ∈ V)`. -/
abbrev disjointOpensClassifier : TopCat.{u} :=
  TopCat.of (ULift.{u} {p : Prop × Prop // ¬(p.1 ∧ p.2)})

/-- The maps of `TopCat` which extend disjoint open sets: the maps with the left lifting property
with respect to the map from `TauCeti.TopCat.disjointOpensClassifier` to a point. By
`TauCeti.TopCat.extendsDisjointOpens_iff`, a map `f : X ⟶ Y` extends disjoint open sets if and
only if every pair of disjoint open subsets of `X` is the preimage under `f` of a pair of disjoint
open subsets of `Y`. -/
def extendsDisjointOpens : MorphismProperty TopCat.{u} :=
  (MorphismProperty.ofHoms fun _ : Unit ↦
    TopCat.isTerminalPUnit.from disjointOpensClassifier.{u}).llp

instance : extendsDisjointOpens.{u}.IsStableUnderCobaseChange :=
  inferInstanceAs (MorphismProperty.llp _).IsStableUnderCobaseChange

instance : IsStableUnderCoproducts.{w} extendsDisjointOpens.{u} :=
  inferInstanceAs (IsStableUnderCoproducts.{w} (MorphismProperty.llp _))

instance : extendsDisjointOpens.{u}.IsStableUnderTransfiniteComposition.{w} :=
  inferInstanceAs (MorphismProperty.llp _).IsStableUnderTransfiniteComposition

section Classifier

variable {X : TopCat.{u}}

/-- The map to `disjointOpensClassifier` classifying two disjoint open sets. -/
private def classify {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (h : Disjoint U V) :
    X ⟶ disjointOpensClassifier.{u} :=
  TopCat.ofHom ⟨fun x ↦ ULift.up ⟨(x ∈ U, x ∈ V), fun hx ↦ Set.disjoint_left.1 h hx.1 hx.2⟩,
    continuous_uliftUp.comp <|
      ((continuous_Prop.2 hU).prodMk (continuous_Prop.2 hV)).subtype_mk _⟩

private lemma setOf_classify_fst {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (h : Disjoint U V) : {x | (classify hU hV h x).down.1.1} = U :=
  rfl

private lemma setOf_classify_snd {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (h : Disjoint U V) : {x | (classify hU hV h x).down.1.2} = V :=
  rfl

private lemma preimage_setOf_fst {Y : TopCat.{u}} (f : X ⟶ Y)
    (σ : Y ⟶ disjointOpensClassifier.{u}) :
    f ⁻¹' {y | (σ y).down.1.1} = {x | ((f ≫ σ) x).down.1.1} :=
  rfl

private lemma preimage_setOf_snd {Y : TopCat.{u}} (f : X ⟶ Y)
    (σ : Y ⟶ disjointOpensClassifier.{u}) :
    f ⁻¹' {y | (σ y).down.1.2} = {x | ((f ≫ σ) x).down.1.2} :=
  rfl

private lemma isOpen_setOf_fst (σ : X ⟶ disjointOpensClassifier.{u}) :
    IsOpen {x | (σ x).down.1.1} :=
  continuous_Prop.1 <| continuous_fst.comp <| continuous_subtype_val.comp <|
    continuous_uliftDown.comp σ.hom.continuous

private lemma isOpen_setOf_snd (σ : X ⟶ disjointOpensClassifier.{u}) :
    IsOpen {x | (σ x).down.1.2} :=
  continuous_Prop.1 <| continuous_snd.comp <| continuous_subtype_val.comp <|
    continuous_uliftDown.comp σ.hom.continuous

private lemma disjoint_setOf (σ : X ⟶ disjointOpensClassifier.{u}) :
    Disjoint {x | (σ x).down.1.1} {x | (σ x).down.1.2} :=
  Set.disjoint_left.2 fun x h₁ h₂ ↦ (σ x).down.2 ⟨h₁, h₂⟩

/-- Two maps to `disjointOpensClassifier` agree if they classify the same pair of open sets. -/
private lemma hom_ext_classifier {σ τ : X ⟶ disjointOpensClassifier.{u}}
    (h₁ : {x | (σ x).down.1.1} = {x | (τ x).down.1.1})
    (h₂ : {x | (σ x).down.1.2} = {x | (τ x).down.1.2}) : σ = τ := by
  ext x
  exacts [Set.ext_iff.1 h₁ x, Set.ext_iff.1 h₂ x]

end Classifier

/-- A map `f : X ⟶ Y` of `TopCat` extends disjoint open sets if and only if every pair of disjoint
open subsets of `X` is the preimage under `f` of a pair of disjoint open subsets of `Y`. -/
theorem extendsDisjointOpens_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    extendsDisjointOpens f ↔ ∀ U V : Set X, IsOpen U → IsOpen V → Disjoint U V →
      ∃ U' V' : Set Y, IsOpen U' ∧ IsOpen V' ∧ Disjoint U' V' ∧ f ⁻¹' U' = U ∧ f ⁻¹' V' = V := by
  rw [extendsDisjointOpens, llp_ofHoms_iff_hasLiftingProperty]
  constructor
  · intro _ U V hU hV h
    have sq : CommSq (classify hU hV h) f (TopCat.isTerminalPUnit.from _)
        (TopCat.isTerminalPUnit.from Y) := ⟨TopCat.isTerminalPUnit.hom_ext _ _⟩
    exact ⟨_, _, isOpen_setOf_fst sq.lift, isOpen_setOf_snd sq.lift, disjoint_setOf sq.lift,
      by rw [preimage_setOf_fst, sq.fac_left, setOf_classify_fst],
      by rw [preimage_setOf_snd, sq.fac_left, setOf_classify_snd]⟩
  · intro h
    refine ⟨fun {σ _} sq ↦ ?_⟩
    obtain ⟨U', V', hU', hV', hUV', hU, hV⟩ :=
      h _ _ (isOpen_setOf_fst σ) (isOpen_setOf_snd σ) (disjoint_setOf σ)
    refine ⟨⟨⟨classify hU' hV' hUV', ?_, TopCat.isTerminalPUnit.hom_ext _ _⟩⟩⟩
    exact hom_ext_classifier (by rw [← preimage_setOf_fst, setOf_classify_fst, hU])
      (by rw [← preimage_setOf_snd, setOf_classify_snd, hV])

/-- If two points of a Hausdorff space `X` are mapped by `f : X ⟶ Y` to distinct points and `f`
extends disjoint open sets, then their images are separated by disjoint open sets of `Y`. -/
private lemma exists_disjoint_isOpen_apply {X Y : TopCat.{u}} [T2Space X] {f : X ⟶ Y}
    (hf : extendsDisjointOpens f) {x x' : X} (h : f x ≠ f x') :
    ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ f x ∈ U ∧ f x' ∈ V := by
  obtain ⟨U, V, hU, hV, hx, hx', hUV⟩ := t2_separation (ne_of_apply_ne f h)
  obtain ⟨U', V', hU', hV', hUV', rfl, rfl⟩ := (extendsDisjointOpens_iff f).1 hf U V hU hV hUV
  exact ⟨U', V', hU', hV', hUV', hx, hx'⟩

/-- The colimit of a directed diagram of Hausdorff spaces is Hausdorff if the maps from the
spaces of the diagram to the colimit extend disjoint open sets. -/
theorem t2Space_of_isColimit {J : Type w} [Preorder J] [IsDirectedOrder J] {F : J ⥤ TopCat.{u}}
    [∀ j, T2Space (F.obj j)] {c : Cocone F} (hc : IsColimit c)
    (h : ∀ j, extendsDisjointOpens (c.ι.app j)) : T2Space c.pt := by
  have hc' := isColimitOfPreserves (forget TopCat) hc
  refine t2Space_iff_disjoint_nhds.2 fun y y' hyy' ↦ ?_
  obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit hc' y
  obtain ⟨i', x', hx'⟩ := Types.jointly_surjective_of_isColimit hc' y'
  obtain ⟨k, hik, hi'k⟩ := exists_ge_ge i i'
  have hy : c.ι.app k (F.map (homOfLE hik) x) = y := by
    rw [← ConcreteCategory.comp_apply, c.w]
    exact hx
  have hy' : c.ι.app k (F.map (homOfLE hi'k) x') = y' := by
    rw [← ConcreteCategory.comp_apply, c.w]
    exact hx'
  rw [← hy, ← hy'] at hyy' ⊢
  obtain ⟨U, V, hU, hV, hUV, hxU, hxV⟩ := exists_disjoint_isOpen_apply (h k) hyy'
  exact Filter.disjoint_of_disjoint_of_mem hUV (hU.mem_nhds hxU) (hV.mem_nhds hxV)

section Pushout

variable {A B X P : TopCat.{u}} {g : A ⟶ X} {m : A ⟶ B} {f : X ⟶ P} {g₂ : B ⟶ P}

/-- In a pushout square in `TopCat`, compatible pairs of disjoint open sets of the two sides glue
to a pair of disjoint open sets of the corner. -/
theorem exists_disjoint_isOpen_of_isPushout (sq : IsPushout g m f g₂) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (h : Disjoint U V) {U' V' : Set B} (hU' : IsOpen U')
    (hV' : IsOpen V') (h' : Disjoint U' V') (hUU' : g ⁻¹' U = m ⁻¹' U')
    (hVV' : g ⁻¹' V = m ⁻¹' V') :
    ∃ W W' : Set P, IsOpen W ∧ IsOpen W' ∧ Disjoint W W' ∧ f ⁻¹' W = U ∧ f ⁻¹' W' = V ∧
      g₂ ⁻¹' W = U' ∧ g₂ ⁻¹' W' = V' := by
  have w : g ≫ classify hU hV h = m ≫ classify hU' hV' h' :=
    hom_ext_classifier
      (by rw [← preimage_setOf_fst, ← preimage_setOf_fst, setOf_classify_fst,
        setOf_classify_fst, hUU'])
      (by rw [← preimage_setOf_snd, ← preimage_setOf_snd, setOf_classify_snd,
        setOf_classify_snd, hVV'])
  let σ := sq.desc _ _ w
  exact ⟨_, _, isOpen_setOf_fst σ, isOpen_setOf_snd σ, disjoint_setOf σ,
    by rw [preimage_setOf_fst, sq.inl_desc, setOf_classify_fst],
    by rw [preimage_setOf_snd, sq.inl_desc, setOf_classify_snd],
    by rw [preimage_setOf_fst, sq.inr_desc, setOf_classify_fst],
    by rw [preimage_setOf_snd, sq.inr_desc, setOf_classify_snd]⟩

/-- In a pushout square in `TopCat` along a map `m : A ⟶ B` with closed range to a regular space,
a point coming from `B` but not from `A` is separated from every point coming from the other
side. -/
private lemma exists_disjoint_isOpen_of_isPushout_of_notMem [RegularSpace B]
    (sq : IsPushout g m f g₂) (hm : IsClosed (Set.range m)) {b : B} (hb : b ∉ Set.range m)
    (x : X) : ∃ W W' : Set P, IsOpen W ∧ IsOpen W' ∧ Disjoint W W' ∧ g₂ b ∈ W ∧ f x ∈ W' := by
  obtain ⟨t, ht, htc, htm⟩ := exists_mem_nhds_isClosed_subset (hm.isOpen_compl.mem_nhds hb)
  have hint : Disjoint (interior t) tᶜ := disjoint_compl_right.mono_left interior_subset
  obtain ⟨W, W', hW, hW', hWW', -, hfW', hg₂W, -⟩ := exists_disjoint_isOpen_of_isPushout sq
    isOpen_empty isOpen_univ (Set.empty_disjoint _) isOpen_interior htc.isOpen_compl hint
    (by
      ext a
      simpa using fun h ↦ htm (interior_subset h) ⟨a, rfl⟩)
    (by
      ext a
      simpa using fun h ↦ htm h ⟨a, rfl⟩)
  refine ⟨W, W', hW, hW', hWW', ?_, ?_⟩
  · rw [← Set.mem_preimage, hg₂W]
    exact mem_interior_iff_mem_nhds.2 ht
  · rw [← Set.mem_preimage, hfW']
    trivial

/-- Attaching a regular Hausdorff space `B` to a Hausdorff space `X` along a map `m : A ⟶ B`
with closed range which extends disjoint open sets gives a Hausdorff space: in a pushout square
in `TopCat` with sides `m : A ⟶ B` and `f : X ⟶ P`, the corner `P` is Hausdorff. -/
theorem t2Space_of_isPushout (sq : IsPushout g m f g₂) [T2Space X] [T2Space B] [RegularSpace B]
    (hm : extendsDisjointOpens m) (hm' : IsClosed (Set.range m)) : T2Space P := by
  have hf : extendsDisjointOpens f := MorphismProperty.of_isPushout sq hm
  have sq' := (forget TopCat).map_isPushout sq
  refine t2Space_iff_disjoint_nhds.2 fun p q hpq ↦ ?_
  suffices ∃ W W' : Set P, IsOpen W ∧ IsOpen W' ∧ Disjoint W W' ∧ p ∈ W ∧ q ∈ W' by
    obtain ⟨W, W', hW, hW', hWW', hp, hq⟩ := this
    exact Filter.disjoint_of_disjoint_of_mem hWW' (hW.mem_nhds hp) (hW'.mem_nhds hq)
  obtain ⟨x, rfl⟩ | ⟨b, rfl, hb⟩ := Types.eq_or_eq_of_isPushout' sq' p <;>
    obtain ⟨x', rfl⟩ | ⟨b', rfl, hb'⟩ := Types.eq_or_eq_of_isPushout' sq' q
  · exact exists_disjoint_isOpen_apply hf hpq
  · obtain ⟨W, W', hW, hW', hWW', hb', hx⟩ :=
      exists_disjoint_isOpen_of_isPushout_of_notMem sq hm' hb' x
    exact ⟨W', W, hW', hW, hWW'.symm, hx, hb'⟩
  · exact exists_disjoint_isOpen_of_isPushout_of_notMem sq hm' hb x'
  · obtain ⟨U, U', hU, hU', hbU, hbU', hUU'⟩ := t2_separation (ne_of_apply_ne g₂ hpq)
    obtain ⟨W, W', hW, hW', hWW', -, -, hg₂W, hg₂W'⟩ := exists_disjoint_isOpen_of_isPushout sq
      isOpen_empty isOpen_empty (Set.empty_disjoint _) (hU.inter hm'.isOpen_compl)
      (hU'.inter hm'.isOpen_compl) (hUU'.mono Set.inter_subset_left Set.inter_subset_left)
      (by ext a; simp) (by ext a; simp)
    exact ⟨W, W', hW, hW', hWW', (Set.ext_iff.1 hg₂W b).2 ⟨hbU, hb⟩,
      (Set.ext_iff.1 hg₂W' b').2 ⟨hbU', hb'⟩⟩

end Pushout

end TauCeti.TopCat
