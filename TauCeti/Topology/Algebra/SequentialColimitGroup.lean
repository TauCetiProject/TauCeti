/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.Topology.Category.CompactlyGenerated.GrpObj
public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.Category.TopCat.Compact
import TauCeti.Topology.Category.TopCat.Normal
import TauCeti.Topology.Homotopy.HomotopyGroup.SequentialColimit

/-!
# Sequential colimits of topological groups

Given a sequence `φ : ∀ n, G n →ₜ* G (n + 1)` of continuous monoid homomorphisms between
`w`-compactly generated topological groups in `Type w`, this file constructs their colimit
`TauCeti.SequentialColimitGroup φ` as a colimit in `Grp CompactlyGenerated.{w, w}`, using the
sifted-colimit creation machinery of `TauCeti.CategoryTheory.Monoidal.SiftedColimits` and
`TauCeti.Topology.Category.CompactlyGenerated.GrpObj`.

When every stage `G n` is compact Hausdorff and every transition `φ n` is a closed embedding,
`TauCeti.TopCat.uCompactlyGeneratedSpace_prod_of_isColimit` shows that the ordinary product
`SequentialColimitGroup φ × SequentialColimitGroup φ` is `w`-compactly generated, so
`SequentialColimitGroup φ` is a topological group (`IsTopologicalGroup`) and `T₄` (`T4Space`),
the finite-stage inclusions `TauCeti.SequentialColimitGroup.of φ n` are closed embeddings, and
compatible families of continuous maps or continuous homomorphisms descend to the colimit
(`liftContinuous`, `lift`). Furthermore, step connectivity of the maps `φ k` descends to `of φ n`
(`isNConnected_of`).

## Main definitions

* `TauCeti.SequentialColimitGroup`: the underlying type of the colimit in
  `Grp CompactlyGenerated.{w, w}` of a sequence of continuous group homomorphisms.
* `TauCeti.SequentialColimitGroup.transition`: the composite homomorphism `G m →ₜ* G n` for
  `m ≤ n`.
* `TauCeti.SequentialColimitGroup.of`: the canonical continuous inclusion `G n →ₜ* colimit`.
* `TauCeti.SequentialColimitGroup.liftContinuous`: universal property for continuous maps out of
  the sequential colimit.
* `TauCeti.SequentialColimitGroup.lift`: universal property for continuous homomorphisms out of the
  sequential colimit.

## Main results

* `TauCeti.SequentialColimitGroup.isTopologicalGroup`: when the stages are compact Hausdorff and
  the transition maps are closed embeddings, the colimit is a topological group
  (`IsTopologicalGroup`).
* `TauCeti.SequentialColimitGroup.isClosedEmbedding_of`: when the transition maps are closed
  embeddings, every stage inclusion `of φ n` is a closed embedding.
* `TauCeti.SequentialColimitGroup.coe_of`, `TauCeti.SequentialColimitGroup.toContinuousMap_of`,
  `TauCeti.SequentialColimitGroup.continuous_iff`: characterization of the colimit topology via
  stage inclusions and identification of `of φ n` with the underlying `topCocone` leg.
* `TauCeti.SequentialColimitGroup.isNConnected_of`: when the stages are `T₁` and the transition
  maps are closed embeddings, stagewise `d`-connectivity descends to `of φ n`.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Set

universe w

namespace TauCeti

attribute [local instance] IsFiltered.isSifted

section Diagram

variable {G : ℕ → Type w} [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
  [∀ n, UCompactlyGeneratedSpace.{w} (G n)] [∀ n, IsTopologicalGroup (G n)]
  (φ : ∀ n, G n →ₜ* G (n + 1))

/-- One step `G n ⟶ G (n + 1)` of the sequential diagram in `Grp CompactlyGenerated.{w, w}`. -/
@[expose]
def SequentialColimitGroup.grpStep (n : ℕ) :
    (⟨CompactlyGenerated.of.{w, w} (G n)⟩ : Grp CompactlyGenerated.{w, w}) ⟶
      ⟨CompactlyGenerated.of.{w, w} (G (n + 1))⟩ :=
  Grp.homMk (CompactlyGenerated.ofHom (φ n : C(G n, G (n + 1))))

/-- The sequential diagram `n ↦ G n` in `Grp CompactlyGenerated.{w, w}`. -/
@[expose]
def SequentialColimitGroup.grpDiagram : ℕ ⥤ Grp CompactlyGenerated.{w, w} :=
  Functor.ofSequence (SequentialColimitGroup.grpStep φ)

/-- The underlying diagram of topological spaces `n ↦ G n` in `TopCat.{w}`. -/
abbrev SequentialColimitGroup.topDiagram : ℕ ⥤ TopCat.{w} :=
  SequentialColimitGroup.grpDiagram φ ⋙ Grp.forget CompactlyGenerated.{w, w} ⋙
    CompactlyGenerated.compactlyGeneratedToTop.{w, w}

end Diagram

/-- **Sequential colimit of topological groups**: the colimit in `Grp CompactlyGenerated.{w, w}`
of a sequence `φ : ∀ n, G n →ₜ* G (n + 1)` of continuous homomorphisms between `w`-compactly
generated topological groups. -/
@[expose]
def SequentialColimitGroup {G : ℕ → Type w} [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
    [∀ n, UCompactlyGeneratedSpace.{w} (G n)] [∀ n, IsTopologicalGroup (G n)]
    (φ : ∀ n, G n →ₜ* G (n + 1)) : Type w :=
  (colimit (SequentialColimitGroup.grpDiagram φ)).X

namespace SequentialColimitGroup

section Transition

variable {G : ℕ → Type w} [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
  (φ : ∀ n, G n →ₜ* G (n + 1))

include φ

/-- The composite transition homomorphism `G m →ₜ* G n` for `m ≤ n`, obtained by iterating the
successor steps `φ`. -/
def transition {m n : ℕ} (h : m ≤ n) : G m →ₜ* G n :=
  Nat.leRec (ContinuousMonoidHom.id (G m)) (fun k _ f ↦ (φ k).comp f) h

/-- The identity transition `m ≤ m` is the identity continuous homomorphism. -/
@[simp]
theorem transition_refl (m : ℕ) :
    transition φ (le_refl m) = ContinuousMonoidHom.id (G m) :=
  Nat.leRec_self _ _

/-- Extending a transition by one step composes with `φ n`. -/
theorem transition_succ {m n : ℕ} (h : m ≤ n) :
    transition φ (Nat.le.step h) = (φ n).comp (transition φ h) :=
  Nat.leRec_succ _ _ h

/-- The one-step transition `n ≤ n + 1` is `φ n`. -/
@[simp]
theorem transition_le_succ (n : ℕ) : transition φ n.le_succ = φ n := by
  ext x
  rw [transition_succ φ (le_refl n), transition_refl φ n, ContinuousMonoidHom.coe_comp,
    Function.comp_apply, ContinuousMonoidHom.coe_id, id_eq]

private theorem apply_transition {Y : Type*} (f : ∀ n, G n → Y)
    (hf : ∀ n a, f (n + 1) (φ n a) = f n a) {m n : ℕ} (h : m ≤ n) (a : G m) :
    f n (transition φ h a) = f m a := by
  induction h with
  | refl => rw [transition_refl, ContinuousMonoidHom.coe_id, id_eq]
  | @step k h ih =>
    rw [transition_succ φ h, ContinuousMonoidHom.coe_comp, Function.comp_apply, hf, ih]

end Transition

section Basic

variable {G : ℕ → Type w} [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
  [∀ n, UCompactlyGeneratedSpace.{w} (G n)] [∀ n, IsTopologicalGroup (G n)]
  (φ : ∀ n, G n →ₜ* G (n + 1))

include φ

/-- The underlying space of stage `n` in `topDiagram φ` is `TopCat.of (G n)`. -/
theorem topDiagram_obj (n : ℕ) : (topDiagram φ).obj n = TopCat.of (G n) :=
  rfl

/-- Stage `n` of `topDiagram φ` inherits `CompactSpace` from `G n`. -/
instance instCompactSpaceTopDiagramObj (n : ℕ) [CompactSpace (G n)] :
    CompactSpace ((topDiagram φ).obj n) :=
  ‹CompactSpace (G n)›

/-- Stage `n` of `topDiagram φ` inherits `T2Space` from `G n`. -/
instance instT2SpaceTopDiagramObj (n : ℕ) [T2Space (G n)] :
    T2Space ((topDiagram φ).obj n) :=
  ‹T2Space (G n)›

/-- Stage `n` of `topDiagram φ` inherits `T1Space` from `G n`. -/
instance instT1SpaceTopDiagramObj (n : ℕ) [T1Space (G n)] :
    T1Space ((topDiagram φ).obj n) :=
  ‹T1Space (G n)›

/-- Stage `n` of `topDiagram φ` inherits `T4Space` from `G n`. -/
instance instT4SpaceTopDiagramObj (n : ℕ) [T4Space (G n)] :
    T4Space ((topDiagram φ).obj n) :=
  ‹T4Space (G n)›

/-- On successor steps `n ⟶ n + 1`, `topDiagram φ` acts as `φ n`. -/
theorem topDiagram_map_succ (n : ℕ) (x : G n) :
    (topDiagram φ).map (homOfLE n.le_succ) x = φ n x := by
  -- Unfold `topDiagram` and `grpDiagram` to rewrite the `Functor.ofSequence` successor step.
  change (Grp.forget CompactlyGenerated.{w, w} ⋙
    CompactlyGenerated.compactlyGeneratedToTop.{w, w}).map
      ((Functor.ofSequence (grpStep φ)).map (homOfLE (Nat.le_add_right n 1))) x = _
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- On arbitrary arrows `m ≤ n`, `topDiagram φ` acts as `transition φ h`. -/
theorem topDiagram_map_homOfLE {m n : ℕ} (h : m ≤ n) (x : G m) :
    (topDiagram φ).map (homOfLE h) x = transition φ h x := by
  induction h with
  | refl =>
    rw [Subsingleton.elim (homOfLE (le_refl m)) (𝟙 m), (topDiagram φ).map_id, transition_refl]
    rfl
  | @step k h ih =>
    rw [← homOfLE_comp h k.le_succ, (topDiagram φ).map_comp]
    -- Unfold `(topDiagram φ).obj` to `G` across `ConcreteCategory.comp_apply`.
    change ((topDiagram φ).map (homOfLE k.le_succ)) (((topDiagram φ).map (homOfLE h)) x) = _
    rw [ih, topDiagram_map_succ, transition_succ]
    rfl

/-- The colimit cocone in `TopCat.{w}` underlying `SequentialColimitGroup φ`. -/
@[expose]
def topCocone : Cocone (topDiagram φ) :=
  (Grp.forget CompactlyGenerated.{w, w} ⋙
    CompactlyGenerated.compactlyGeneratedToTop.{w, w}).mapCocone
      (colimit.cocone (grpDiagram φ))

/-- `topCocone φ` is a colimit cocone in `TopCat.{w}`. -/
def isColimitTopCocone : IsColimit (topCocone φ) :=
  isColimitOfPreserves
    (Grp.forget CompactlyGenerated.{w, w} ⋙ CompactlyGenerated.compactlyGeneratedToTop.{w, w})
    (colimit.isColimit (grpDiagram φ))

instance instTopologicalSpace : TopologicalSpace (SequentialColimitGroup φ) :=
  (colimit (grpDiagram φ)).X.toTop.str

instance instGroup : Group (SequentialColimitGroup φ) :=
  CompactlyGenerated.groupOfGrpObj (colimit (grpDiagram φ)).X

instance instUCompactlyGeneratedSpace :
    UCompactlyGeneratedSpace.{w} (SequentialColimitGroup φ) :=
  (colimit (grpDiagram φ)).X.is_compactly_generated

/-- Every successor transition map in `topDiagram φ` is a closed embedding when each `φ n` is. -/
theorem isClosedEmbedding_topDiagram_succ (hφ : ∀ n, IsClosedEmbedding (φ n)) (n : ℕ) :
    IsClosedEmbedding ((topDiagram φ).map (homOfLE n.le_succ)) := by
  have hfn : ((topDiagram φ).map (homOfLE n.le_succ) : G n → G (n + 1)) = φ n :=
    funext (topDiagram_map_succ φ n)
  exact hfn ▸ hφ n

private theorem uCompactlyGeneratedSpace_prod
    [∀ n, CompactSpace (G n)] [∀ n, T2Space (G n)]
    (hφ : ∀ n, IsClosedEmbedding (φ n)) :
    UCompactlyGeneratedSpace.{w} (SequentialColimitGroup φ × SequentialColimitGroup φ) :=
  TopCat.uCompactlyGeneratedSpace_prod_of_isColimit.{w, w}
    (isColimitTopCocone φ) (isColimitTopCocone φ)
    (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
      (isClosedEmbedding_topDiagram_succ φ hφ) (isColimitTopCocone φ) · |>.isEmbedding)
    (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
      (isClosedEmbedding_topDiagram_succ φ hφ) (isColimitTopCocone φ) · |>.isEmbedding)

/-- When the stages are compact Hausdorff and the transition maps are closed embeddings,
`SequentialColimitGroup φ` is a topological group. -/
theorem isTopologicalGroup [∀ n, CompactSpace (G n)] [∀ n, T2Space (G n)]
    (hφ : ∀ n, IsClosedEmbedding (φ n)) :
    IsTopologicalGroup (SequentialColimitGroup φ) :=
  CompactlyGenerated.isTopologicalGroup_of_grpObj (colimit (grpDiagram φ)).X
    (uCompactlyGeneratedSpace_prod φ hφ)

/-- When the stages are `T₄` and the transition maps are closed embeddings,
`SequentialColimitGroup φ` is `T₄`. -/
theorem t4Space [∀ n, T4Space (G n)] (hφ : ∀ n, IsClosedEmbedding (φ n)) :
    T4Space (SequentialColimitGroup φ) :=
  TopCat.t4Space_of_isColimit (isClosedEmbedding_topDiagram_succ φ hφ) (isColimitTopCocone φ)

/-- The canonical continuous inclusion `G n →ₜ* SequentialColimitGroup φ` from stage `n`. -/
def of (n : ℕ) : G n →ₜ* SequentialColimitGroup φ :=
  let ι : CompactlyGenerated.of.{w, w} (G n) ⟶ (colimit (grpDiagram φ)).X :=
    ((colimit.cocone (grpDiagram φ)).ι.app n).hom.hom
  letI : CategoryTheory.IsMonHom ι :=
    inferInstanceAs (CategoryTheory.IsMonHom ((colimit.cocone (grpDiagram φ)).ι.app n).hom.hom)
  { __ := CompactlyGenerated.monoidHomOfIsMonHom ι
    continuous_toFun := ((topCocone φ).ι.app n).hom.continuous.congr fun x ↦
      (CompactlyGenerated.monoidHomOfIsMonHom_apply ι x).symm }

/-- Evaluating `SequentialColimitGroup.of φ n` agrees with the `topCocone` leg. -/
theorem coe_of (n : ℕ) : ⇑(of φ n) = ⇑((topCocone φ).ι.app n) := by
  ext x
  exact CompactlyGenerated.monoidHomOfIsMonHom_apply
    ((colimit.cocone (grpDiagram φ)).ι.app n).hom.hom (x : CompactlyGenerated.of.{w, w} (G n))

/-- The underlying continuous map of `SequentialColimitGroup.of φ n` agrees with the
`topCocone` leg. -/
theorem toContinuousMap_of (n : ℕ) :
    (of φ n).toContinuousMap = ((topCocone φ).ι.app n).hom :=
  ContinuousMap.ext (congrFun (coe_of φ n))

/-- A subset of `SequentialColimitGroup φ` is closed if and only if its preimage under every
stage inclusion `of φ n` is closed. -/
theorem isClosed_iff {S : Set (SequentialColimitGroup φ)} :
    IsClosed S ↔ ∀ n, IsClosed (of φ n ⁻¹' S) := by
  simp only [coe_of]
  exact TopCat.isClosed_iff_of_isColimit _ (isColimitTopCocone φ) S

/-- A map out of `SequentialColimitGroup φ` is continuous if and only if its restriction to every
stage `G n` is continuous. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : SequentialColimitGroup φ → Y} :
    Continuous f ↔ ∀ n, Continuous (f ∘ of φ n) := by
  simp only [continuous_iff_isClosed, isClosed_iff, Set.preimage_comp]
  exact ⟨fun h n s hs ↦ h s hs n, fun h s hs n ↦ h n s hs⟩

/-- The stage inclusions are compatible with the successor step `φ n`. -/
@[simp]
theorem of_succ (n : ℕ) (x : G n) : of φ (n + 1) (φ n x) = of φ n x := by
  rw [coe_of, coe_of, ← topDiagram_map_succ φ n x]
  exact ConcreteCategory.congr_hom ((topCocone φ).w (homOfLE n.le_succ)) x

/-- Composing `of φ (n + 1)` with `φ n` gives `of φ n`. -/
@[simp]
theorem of_comp (n : ℕ) : (of φ (n + 1)).comp (φ n) = of φ n :=
  ContinuousMonoidHom.ext (of_succ φ n)

/-- The stage inclusions are compatible with all composite transition maps `m ≤ n`. -/
@[simp]
theorem of_le {m n : ℕ} (h : m ≤ n) (x : G m) : of φ n (transition φ h x) = of φ m x := by
  rw [coe_of, coe_of, ← topDiagram_map_homOfLE φ h x]
  exact ConcreteCategory.congr_hom ((topCocone φ).w (homOfLE h)) x

/-- When every transition `φ n` is a closed embedding, every stage inclusion `of φ n` is a closed
embedding. -/
theorem isClosedEmbedding_of (hφ : ∀ n, IsClosedEmbedding (φ n)) (n : ℕ) :
    IsClosedEmbedding (of φ n) := by
  rw [coe_of]
  exact TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
    (isClosedEmbedding_topDiagram_succ φ hφ) (isColimitTopCocone φ) n

/-- When every transition `φ n` is injective, every stage inclusion `of φ n` is injective. -/
theorem of_injective (hφ : ∀ n, Function.Injective (φ n)) (n : ℕ) :
    Function.Injective (of φ n) := by
  rw [coe_of]
  refine TopCat.injective_ι_of_isColimit (fun i j f x y hxy ↦ ?_) (isColimitTopCocone φ) n
  have htrans : ∀ ⦃a b : ℕ⦄ (hab : a ≤ b),
      Function.Injective ((topDiagram φ).map (homOfLE hab)).hom :=
    fun a b hab ↦ TopCat.homOfLE_induction a (fun _ g ↦ Function.Injective g)
      Function.injective_id
      (fun k _ ih ↦
        (show Function.Injective ((topDiagram φ).map (homOfLE k.le_succ)).hom from
          funext (topDiagram_map_succ φ k) ▸ hφ k).comp ih) hab
  rw [Subsingleton.elim f (homOfLE (leOfHom f))] at hxy
  exact htrans (leOfHom f) hxy

/-- Every element of `SequentialColimitGroup φ` lies in the image of some finite stage `G n`. -/
theorem exists_of (x : SequentialColimitGroup φ) : ∃ (n : ℕ) (a : G n), of φ n a = x := by
  simp only [coe_of]
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (isColimitTopCocone φ)) x

/-- Any two elements of `SequentialColimitGroup φ` lie in the image of a common finite stage
`G n`. -/
theorem exists_of₂ (x y : SequentialColimitGroup φ) :
    ∃ (n : ℕ) (a b : G n), of φ n a = x ∧ of φ n b = y := by
  simp only [coe_of]
  exact Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget TopCat) (isColimitTopCocone φ)) x y

/-- Two continuous homomorphisms out of `SequentialColimitGroup φ` agree when they agree on every
finite stage `G n`. -/
@[ext]
theorem hom_ext {H : Type*} [Group H] [TopologicalSpace H]
    {f g : SequentialColimitGroup φ →ₜ* H} (h : ∀ n, f.comp (of φ n) = g.comp (of φ n)) :
    f = g := by
  ext x
  obtain ⟨n, a, rfl⟩ := exists_of φ x
  exact DFunLike.congr_fun (h n) a

/-- Two continuous maps out of `SequentialColimitGroup φ` agree when they agree on every finite
stage `G n`. -/
@[ext]
theorem continuousMap_ext {Y : Type*} [TopologicalSpace Y]
    {f g : C(SequentialColimitGroup φ, Y)}
    (h : ∀ n, f.comp (of φ n : C(G n, SequentialColimitGroup φ)) =
      g.comp (of φ n : C(G n, SequentialColimitGroup φ))) :
    f = g := by
  ext x
  obtain ⟨n, a, rfl⟩ := exists_of φ x
  exact ContinuousMap.congr_fun (h n) a

private theorem of_eq_of_iff {m n : ℕ} {a : G m} {b : G n} :
    of φ m a = of φ n b ↔
      ∃ (k : ℕ) (hm : m ≤ k) (hn : n ≤ k), transition φ hm a = transition φ hn b := by
  simp only [coe_of]
  refine (Types.FilteredColimit.isColimit_eq_iff _
    (isColimitOfPreserves (forget TopCat) (isColimitTopCocone φ))
      (i := m) (j := n) (xi := a) (xj := b)).trans ?_
  constructor
  · rintro ⟨k, f₁, f₂, hk⟩
    refine ⟨k, leOfHom f₁, leOfHom f₂, ?_⟩
    rw [Subsingleton.elim f₁ (homOfLE (leOfHom f₁)),
      Subsingleton.elim f₂ (homOfLE (leOfHom f₂))] at hk
    -- Unfold `((topDiagram φ ⋙ forget TopCat).map ...)` to `(topDiagram φ).map ...`.
    change (topDiagram φ).map (homOfLE (leOfHom f₁)) a =
      (topDiagram φ).map (homOfLE (leOfHom f₂)) b at hk
    rwa [topDiagram_map_homOfLE, topDiagram_map_homOfLE] at hk
  · rintro ⟨k, hm, hn, hk⟩
    refine ⟨k, homOfLE hm, homOfLE hn, ?_⟩
    change (topDiagram φ).map (homOfLE hm) a = (topDiagram φ).map (homOfLE hn) b
    rwa [topDiagram_map_homOfLE, topDiagram_map_homOfLE]

private def liftFun {Y : Type*} (f : ∀ n, G n → Y) (x : SequentialColimitGroup φ) : Y :=
  let h := exists_of φ x
  f h.choose h.choose_spec.choose

private theorem liftFun_of {Y : Type*} (f : ∀ n, G n → Y)
    (hf : ∀ n a, f (n + 1) (φ n a) = f n a) (n : ℕ) (a : G n) :
    liftFun φ f (of φ n a) = f n a := by
  dsimp [liftFun]
  set h := exists_of φ (of φ n a)
  obtain ⟨k, hm, hn, hk⟩ := (of_eq_of_iff φ).1 h.choose_spec.choose_spec
  rw [← apply_transition φ f hf hm, hk, apply_transition φ f hf hn]

/-- **Universal property of `SequentialColimitGroup` as a topological space**: a family of
continuous maps out of `G n` into any space `Y` compatible with `φ` descends to a unique
continuous map `C(SequentialColimitGroup φ, Y)`. -/
def liftContinuous {Y : Type*} [TopologicalSpace Y]
    (f : ∀ n, C(G n, Y)) (hf : ∀ n a, f (n + 1) (φ n a) = f n a) :
    C(SequentialColimitGroup φ, Y) where
  toFun := liftFun φ (fun n ↦ f n)
  continuous_toFun := (continuous_iff φ).2 fun n ↦
    (show liftFun φ (fun k ↦ f k) ∘ of φ n = f n from
      funext (liftFun_of φ (fun k ↦ f k) hf n)) ▸ (f n).continuous

/-- Evaluating `liftContinuous f hf` at a stage element `of φ n a` gives `f n a`. -/
@[simp]
theorem liftContinuous_of {Y : Type*} [TopologicalSpace Y]
    (f : ∀ n, C(G n, Y)) (hf : ∀ n a, f (n + 1) (φ n a) = f n a) (n : ℕ) (a : G n) :
    liftContinuous φ f hf (of φ n a) = f n a :=
  liftFun_of φ (fun k ↦ f k) hf n a

/-- **Universal property of `SequentialColimitGroup` as a topological group**: a family of
continuous homomorphisms out of `G n` into any group `H` with a topology compatible with `φ`
descends to a unique continuous homomorphism `SequentialColimitGroup φ →ₜ* H`. -/
def lift {H : Type*} [Group H] [TopologicalSpace H]
    (f : ∀ n, G n →ₜ* H) (hf : ∀ n a, f (n + 1) (φ n a) = f n a) :
    SequentialColimitGroup φ →ₜ* H :=
  let g : C(SequentialColimitGroup φ, H) := liftContinuous φ (fun n ↦ (f n).toContinuousMap) hf
  { toFun := g
    map_one' := by
      -- Unfold the coerced continuous map `g` to rewrite `1` as `of φ 0 1`.
      change g 1 = 1
      rw [show (1 : SequentialColimitGroup φ) = of φ 0 1 from (map_one (of φ 0)).symm]
      exact (liftContinuous_of φ (fun n ↦ (f n).toContinuousMap) hf 0 1).trans (map_one (f 0))
    map_mul' x y := by
      obtain ⟨n, a, b, rfl, rfl⟩ := exists_of₂ φ x y
      rw [← map_mul (of φ n), liftContinuous_of, liftContinuous_of, liftContinuous_of]
      exact map_mul (f n) a b
    continuous_toFun := g.continuous }

/-- Evaluating `lift f hf` at a stage element `of φ n a` gives `f n a`. -/
@[simp]
theorem lift_of {H : Type*} [Group H] [TopologicalSpace H]
    (f : ∀ n, G n →ₜ* H) (hf : ∀ n a, f (n + 1) (φ n a) = f n a) (n : ℕ) (a : G n) :
    lift φ f hf (of φ n a) = f n a :=
  liftContinuous_of φ (fun n ↦ (f n).toContinuousMap) hf n a

/-- When the stages are `T₁` and the transition maps are closed embeddings, stagewise
`d`-connectivity from stage `n` onward descends to the stage inclusion `of φ n`. -/
theorem isNConnected_of [∀ n, T1Space (G n)] (hφ : ∀ n, IsClosedEmbedding (φ n))
    (n d : ℕ) (hd : ∀ k, n ≤ k → (φ k).toContinuousMap.IsNConnected d) :
    (of φ n).toContinuousMap.IsNConnected d := by
  rw [toContinuousMap_of]
  refine TopCat.isNConnected_ι_of_forall_succ (isColimitTopCocone φ)
    (fun m ↦ (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
      (isClosedEmbedding_topDiagram_succ φ hφ) (isColimitTopCocone φ) m).isEmbedding)
    n d fun k hnk ↦ ?_
  have hfn : ((topDiagram φ).map (homOfLE k.le_succ)).hom = (φ k).toContinuousMap :=
    ContinuousMap.ext (topDiagram_map_succ φ k)
  rw [hfn]
  exact hd k hnk

end Basic

end SequentialColimitGroup

end TauCeti
