/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CategoricalEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.Product

/-!
# Change of base for coCartesian transports

In a pullback square of simplicial sets, a chosen coCartesian transport along the image of
an edge of the new base pulls back to a transport along that edge. Its functor is conjugated
by the canonical isomorphisms of fibres, and its homotopy is the pullback lift of the original
homotopy and the base edge. These formulas also compare families of transports into products
of target fibres, as used by Segal conditions on categories of operators.

## Main declarations

* `SSet.CoCartesianTransport.baseChange`: pullback of a chosen transport.
* `SSet.CoCartesianTransport.baseChange_id` and `baseChange_paste_horiz`: compatibility
  with identity and iterated change of base.
* `SSet.CoCartesianTransport.piFunctor_baseChange`: comparison of the product maps.
* `SSet.CoCartesianTransport.isCategoricalEquivalence_piFunctor_baseChange_iff`:
  preservation and reflection of the categorical-equivalence condition on those products.

## References

* J. Lurie, *Higher Topos Theory*, Remark 2.4.1.9.
* J. Lurie, *Higher Algebra*, §§4.1.1 and 4.2.1.
-/

public section

universe u v

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial

namespace SSet.CoCartesianTransport

variable {X S X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S}
  {b : S' ⟶ S}

/-- Pull back a chosen coCartesian transport along a pullback square. -/
noncomputable def baseChange {s r : S' _⦋0⦌} {e : Edge s r}
    (T : CoCartesianTransport p (e.map b)) (sq : IsPullback t p' p b) :
    CoCartesianTransport p' e where
  functor := (fiber.isoOfIsPullback sq s).hom ≫ T.functor ≫ (fiber.isoOfIsPullback sq r).inv
  homotopy := sq.lift ((fiber.isoOfIsPullback sq s).hom ▷ Δ[1] ≫ T.homotopy)
    (snd _ _ ≫ yonedaEquiv.symm e.edge) (by
      simp [← yonedaEquiv_symm_comp])
  ι₀_homotopy := by
    apply sq.hom_ext
    · simp
    · rw [Category.assoc, sq.lift_snd, ι₀_snd_assoc, const_comp,
        Edge.yonedaEquiv_symm_edge_app_zero, fiber.ι_comp]
  ι₁_homotopy := by
    apply sq.hom_ext
    · simp
    · rw [Category.assoc, sq.lift_snd, ι₁_snd_assoc, const_comp,
        Edge.yonedaEquiv_symm_edge_app_one]
      simp
  homotopy_comp := by simp
  isCoCartesian x := by
    apply Edge.IsCoCartesian.of_isPullback sq
    apply (T.isCoCartesian ((fiber.isoOfIsPullback sq s).hom.app _ x)).of_edge_eq
    simp only [Edge.mk'_edge, Edge.map_edge, ← yonedaEquiv_comp, Category.assoc,
      IsPullback.lift_fst]
    rw [← Category.assoc, lift_whiskerRight]
    simp [const_comp]

/-- Change of base conjugates the functor by the fibre comparison isomorphisms. -/
lemma baseChange_functor {s r : S' _⦋0⦌} {e : Edge s r}
    (T : CoCartesianTransport p (e.map b)) (sq : IsPullback t p' p b) :
    (T.baseChange sq).functor =
      (fiber.isoOfIsPullback sq s).hom ≫ T.functor ≫ (fiber.isoOfIsPullback sq r).inv :=
  (rfl)

/-- The transported functor commutes with the fibre comparison isomorphisms. -/
@[reassoc (attr := simp)]
lemma baseChange_functor_hom {s r : S' _⦋0⦌} {e : Edge s r}
    (T : CoCartesianTransport p (e.map b)) (sq : IsPullback t p' p b) :
    (T.baseChange sq).functor ≫ (fiber.isoOfIsPullback sq r).hom =
      (fiber.isoOfIsPullback sq s).hom ≫ T.functor := by
  simp [baseChange_functor]

/-- The homotopy after change of base projects to the original transport homotopy. -/
@[reassoc (attr := simp)]
lemma baseChange_homotopy_comp {s r : S' _⦋0⦌} {e : Edge s r}
    (T : CoCartesianTransport p (e.map b)) (sq : IsPullback t p' p b) :
    (T.baseChange sq).homotopy ≫ t =
      (fiber.isoOfIsPullback sq s).hom ▷ Δ[1] ≫ T.homotopy := by
  simp [baseChange]

/-- Changing base along the identity square leaves a chosen transport unchanged. -/
@[simp]
lemma baseChange_id {s r : S _⦋0⦌} {e : Edge s r} (T : CoCartesianTransport p e) :
    T.baseChange (IsPullback.id_horiz p) = T := by
  apply CoCartesianTransport.ext
  simpa using T.baseChange_homotopy_comp (IsPullback.id_horiz p)

/-- Changing base twice agrees with changing base along the pasted pullback square. -/
lemma baseChange_paste_horiz {X'' S'' : SSet.{u}} {t' : X'' ⟶ X'} {p'' : X'' ⟶ S''}
    {b' : S'' ⟶ S'} {s r : S'' _⦋0⦌} {e : Edge s r}
    (T : CoCartesianTransport p ((e.map b').map b))
    (sq' : IsPullback t' p'' p' b') (sq : IsPullback t p' p b) :
    T.baseChange (e := e) (sq'.paste_horiz sq) =
      (T.baseChange (e := e.map b') sq).baseChange (e := e) sq' := by
  apply CoCartesianTransport.ext
  apply sq'.hom_ext
  · apply sq.hom_ext
    · simp only [Category.assoc, baseChange_homotopy_comp_assoc]
      rw [baseChange_homotopy_comp (e := e) T (sq'.paste_horiz sq)]
      rw [fiber.isoOfIsPullback_paste_horiz sq' sq s]
      simp [comp_whiskerRight]
    · simp only [Category.assoc, sq'.w, homotopy_comp_assoc]
  · simp

/-- The map to the product of target fibres defined by a family of chosen transports with
a common source, whenever that product exists. -/
noncomputable def piFunctor {ι : Type v} {s : S _⦋0⦌} {r : ι → S _⦋0⦌}
    {e : ∀ i, Edge s (r i)} (T : ∀ i, CoCartesianTransport p (e i))
    [HasProduct fun i ↦ (fiber p (r i) : SSet)] :
    (fiber p s : SSet) ⟶ ∏ᶜ fun i ↦ (fiber p (r i) : SSet) :=
  Pi.lift fun i ↦ (T i).functor

@[reassoc (attr := simp)]
lemma piFunctor_π {ι : Type v} {s : S _⦋0⦌} {r : ι → S _⦋0⦌}
    {e : ∀ i, Edge s (r i)} (T : ∀ i, CoCartesianTransport p (e i))
    [HasProduct fun i ↦ (fiber p (r i) : SSet)] (i : ι) :
    piFunctor T ≫ Pi.π _ i = (T i).functor := by
  simp [piFunctor]

/-- The product of the pulled-back transports agrees with the original product map under
the source and target fibre comparisons. -/
@[reassoc]
lemma piFunctor_baseChange_hom {ι : Type v} [HasProductsOfShape ι SSet.{u}]
    {s : S' _⦋0⦌} {r : ι → S' _⦋0⦌}
    {e : ∀ i, Edge s (r i)} (T : ∀ i, CoCartesianTransport p ((e i).map b))
    (sq : IsPullback t p' p b) :
    piFunctor (fun i ↦ (T i).baseChange sq) ≫
        (Pi.mapIso fun i ↦ fiber.isoOfIsPullback sq (r i)).hom =
      (fiber.isoOfIsPullback sq s).hom ≫ piFunctor T := by
  apply Pi.hom_ext
  intro i
  simp

/-- Equivalently, the pulled-back product map is conjugation by the fibre isomorphisms. -/
lemma piFunctor_baseChange {ι : Type v} [HasProductsOfShape ι SSet.{u}]
    {s : S' _⦋0⦌} {r : ι → S' _⦋0⦌}
    {e : ∀ i, Edge s (r i)} (T : ∀ i, CoCartesianTransport p ((e i).map b))
    (sq : IsPullback t p' p b) :
    piFunctor (fun i ↦ (T i).baseChange sq) =
      (fiber.isoOfIsPullback sq s).hom ≫ piFunctor T ≫
        (Pi.mapIso fun i ↦ fiber.isoOfIsPullback sq (r i)).inv := by
  rw [← cancel_mono (Pi.mapIso fun i ↦ fiber.isoOfIsPullback sq (r i)).hom]
  simp [piFunctor_baseChange_hom]

/-- For an inner fibration, change of base preserves and reflects the assertion that a
family of chosen transports gives a categorical equivalence to the product of its target
fibres. The pulled-back map is an inner fibration by stability under base change. -/
lemma isCategoricalEquivalence_piFunctor_baseChange_iff [InnerFibration p]
    {ι : Type v} [HasProductsOfShape ι SSet.{u}]
    {s : S' _⦋0⦌} {r : ι → S' _⦋0⦌} {e : ∀ i, Edge s (r i)}
    (T : ∀ i, CoCartesianTransport p ((e i).map b)) (sq : IsPullback t p' p b) :
    letI : InnerFibration p' := ⟨innerFibrations.of_isPullback sq (mem_innerFibrations p)⟩
    QCat.IsCategoricalEquivalence
        (X := ⟨fiber p' s, inferInstance⟩)
        (Y := ⟨∏ᶜ fun i ↦ (fiber p' (r i) : SSet), inferInstance⟩)
        (ObjectProperty.homMk (piFunctor (fun i ↦ (T i).baseChange sq))) ↔
      QCat.IsCategoricalEquivalence
        (X := ⟨fiber p (b.app _ s), inferInstance⟩)
        (Y := ⟨∏ᶜ fun i ↦ (fiber p (b.app _ (r i)) : SSet), inferInstance⟩)
        (ObjectProperty.homMk (piFunctor T)) := by
  let : InnerFibration p' := ⟨innerFibrations.of_isPullback sq (mem_innerFibrations p)⟩
  let a : (⟨fiber p' s, inferInstance⟩ : QCat) ≅ ⟨fiber p (b.app _ s), inferInstance⟩ :=
    ObjectProperty.isoMk _ (fiber.isoOfIsPullback sq s)
  let c : (⟨∏ᶜ fun i ↦ (fiber p' (r i) : SSet), inferInstance⟩ : QCat) ≅
      ⟨∏ᶜ fun i ↦ (fiber p (b.app _ (r i)) : SSet), inferInstance⟩ :=
    ObjectProperty.isoMk _ (Pi.mapIso fun i ↦ fiber.isoOfIsPullback sq (r i))
  let f := ObjectProperty.homMk (X := (⟨fiber p (b.app _ s), inferInstance⟩ : QCat))
    (Y := ⟨∏ᶜ fun i ↦ (fiber p (b.app _ (r i)) : SSet), inferInstance⟩) (piFunctor T)
  have hw : ObjectProperty.homMk (piFunctor (fun i ↦ (T i).baseChange sq)) =
      a.hom ≫ f ≫ c.inv :=
    ObjectProperty.hom_ext _ (piFunctor_baseChange T sq)
  constructor
  · intro h
    have h' := (QCat.IsCategoricalEquivalence.of_isIso a.inv).comp
      (h.comp (QCat.IsCategoricalEquivalence.of_isIso c.hom))
    rw [hw] at h'
    have he : a.inv ≫ (a.hom ≫ f ≫ c.inv) ≫ c.hom = f := by
      apply ObjectProperty.hom_ext
      -- The bicategory and full-subcategory category structures coincide only after
      -- unfolding; express their composite in simplicial sets before simplifying.
      change (fiber.isoOfIsPullback sq s).inv ≫
        ((fiber.isoOfIsPullback sq s).hom ≫ f.hom ≫
          (Pi.mapIso fun i ↦ fiber.isoOfIsPullback sq (r i)).inv) ≫
            (Pi.mapIso fun i ↦ fiber.isoOfIsPullback sq (r i)).hom = f.hom
      simp [Category.assoc]
    rw [he] at h'
    exact h'
  · intro h
    rw [hw]
    exact (QCat.IsCategoricalEquivalence.of_isIso a.hom).comp
      (h.comp (QCat.IsCategoricalEquivalence.of_isIso c.inv))

end SSet.CoCartesianTransport
