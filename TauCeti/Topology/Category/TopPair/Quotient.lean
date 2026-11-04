/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopPair
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# The pointed quotient of a topological pair

For a pair `(X, B)`, `TopPair.ordinaryPairQuotient` collapses `B` and a separately added point
in `X ⊔ *` to one basepoint. It is the topological pushout of `X ← B → *`, so its topology
is the quotient topology and its maps are determined by their values on `X` and the basepoint.
In particular, when `B` is empty the result is `X` with a disjoint basepoint.

The collapse map, its fibres, the universal mapping property, and functoriality in maps of
pairs are supplied here. These are the carrier and map interfaces used to compare relative
invariants with reduced invariants of a quotient, including pairs with empty subspace.

The construction uses Mathlib's topological pushouts and their preservation by the forgetful
functor to types.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0, quotient spaces and adjoining a basepoint.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe u v

namespace TopPair

private def quotientPointMap (P : TopPair.{u}) : P.snd ⟶ TopCat.of PUnit.{u + 1} :=
  TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩

/-- Collapse the subspace and an added point to a single basepoint. For an empty subspace,
this is the ambient space with a disjoint basepoint. -/
def ordinaryPairQuotient (P : TopPair.{u}) : TopCat.{u} :=
  pushout P.map (quotientPointMap P)

/-- The collapse map from the ambient space to the pointed quotient. -/
def ordinaryPairQuotientπ (P : TopPair.{u}) : P.fst ⟶ P.ordinaryPairQuotient :=
  pushout.inl _ _

private def quotientPointIncl (P : TopPair.{u}) :
    TopCat.of PUnit.{u + 1} ⟶ P.ordinaryPairQuotient :=
  pushout.inr _ _

/-- The distinguished point of the quotient, including when the subspace is empty. -/
def ordinaryPairQuotientBasepoint (P : TopPair.{u}) : P.ordinaryPairQuotient :=
  quotientPointIncl P PUnit.unit

/-- The collapse map sends every point of the subspace to the basepoint. -/
@[simp]
lemma ordinaryPairQuotientπ_map (P : TopPair.{u}) (b : P.snd) :
    P.ordinaryPairQuotientπ (P.map b) = P.ordinaryPairQuotientBasepoint :=
  ConcreteCategory.congr_hom (pushout.condition (f := P.map) (g := quotientPointMap P)) b

/-- Every point of the quotient is either the basepoint or the image of an ambient point. -/
lemma exists_ordinaryPairQuotientπ_or_eq_basepoint (P : TopPair.{u}) (z : P.ordinaryPairQuotient) :
    (∃ x, P.ordinaryPairQuotientπ x = z) ∨ z = P.ordinaryPairQuotientBasepoint := by
  have h := (forget TopCat).map_isPushout (IsPushout.of_hasPushout P.map (quotientPointMap P))
  obtain h | ⟨x, hx⟩ := Types.eq_or_eq_of_isPushout h z
  · exact Or.inl h
  · exact Or.inr hx.symm

/-- Exactly the subspace is collapsed to the basepoint. -/
@[simp]
lemma ordinaryPairQuotientπ_eq_basepoint_iff (P : TopPair.{u}) (x : P.fst) :
    P.ordinaryPairQuotientπ x = P.ordinaryPairQuotientBasepoint ↔ x ∈ Set.range P.map := by
  have sq := (forget TopCat).map_isPushout (IsPushout.of_hasPushout P.map (quotientPointMap P))
  constructor
  · intro h
    obtain ⟨b, hb, _⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      sq.isColimit P.isEmbedding_map.injective x PUnit.unit).1 h
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    exact P.ordinaryPairQuotientπ_map b

/-- Two ambient points have the same image exactly when they are equal or both belong to
the subspace. No separation or closedness hypothesis is needed. -/
lemma ordinaryPairQuotientπ_eq_iff (P : TopPair.{u}) (x y : P.fst) :
    P.ordinaryPairQuotientπ x = P.ordinaryPairQuotientπ y ↔
      x = y ∨ x ∈ Set.range P.map ∧ y ∈ Set.range P.map := by
  let f := (forget TopCat).map P.map
  let g := (forget TopCat).map (quotientPointMap P)
  have hf : Mono f := (mono_iff_injective _).2 P.isEmbedding_map.injective
  have sq := (forget TopCat).map_isPushout (IsPushout.of_hasPushout P.map (quotientPointMap P))
  let e := sq.isColimit.coconePointUniqueUpToIso (Types.Pushout.isColimitCocone f g)
  have he (z : P.fst) : e.hom (P.ordinaryPairQuotientπ z) = Types.Pushout.inl f g z :=
    ConcreteCategory.congr_hom (sq.isColimit.comp_coconePointUniqueUpToIso_hom
      (Types.Pushout.isColimitCocone f g) WalkingSpan.left) z
  have hinj : Function.Injective e.hom := (mono_iff_injective _).1 inferInstance
  have hxy : P.ordinaryPairQuotientπ x = P.ordinaryPairQuotientπ y ↔
      Types.Pushout.inl f g x = Types.Pushout.inl f g y := by
    constructor
    · intro h
      exact (he x).symm.trans ((congrArg (fun z ↦ e.hom z) h).trans (he y))
    · intro h
      exact hinj ((he x).trans (h.trans (he y).symm))
  -- The native inclusions are quotient constructors. Its equivalence relation is
  -- explicit when the subspace map is injective; the second leg here is constant.
  have hr : Types.Pushout.inl f g x = Types.Pushout.inl f g y ↔
      Types.Pushout.Rel' f g (Sum.inl x) (Sum.inl y) :=
    Types.Pushout.quot_mk_eq_iff f g (Sum.inl x) (Sum.inl y)
  rw [hxy, hr, Types.Pushout.inl_rel'_inl_iff]
  constructor
  · rintro (h | ⟨b, c, _, hb, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨b, hb.symm⟩, ⟨c, hc.symm⟩⟩
  · rintro (h | ⟨⟨b, hb⟩, ⟨c, hc⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, c, rfl, hb.symm, hc.symm⟩

/-- A function out of the pointed quotient is continuous exactly when its restriction along
the ambient collapse map is continuous. The other summand is a point. -/
lemma continuous_ordinaryPairQuotient_iff (P : TopPair.{u}) {Y : Type v}
    [TopologicalSpace Y] (f : P.ordinaryPairQuotient → Y) :
    Continuous f ↔ Continuous (f ∘ P.ordinaryPairQuotientπ) := by
  refine (TopCat.continuous_iff_of_isColimit _
    (pushoutIsPushout P.map (quotientPointMap P)) f).trans ?_
  constructor
  · intro h
    exact h WalkingSpan.left
  · intro h j
    cases j with
    | none => exact h.comp P.map.hom.continuous
    | some j =>
      cases j with
      | left => exact h
      | right =>
        -- The right summand is the added one-point space.
        exact continuous_of_discreteTopology
          (f := fun x : PUnit.{u + 1} ↦ f (quotientPointIncl P x))

/-- The ambient space and added point together map onto the quotient by a quotient map. -/
lemma isQuotientMap_ordinaryPairQuotient (P : TopPair.{u}) :
    IsQuotientMap (Sum.elim P.ordinaryPairQuotientπ
      (fun _ : PUnit.{u + 1} ↦ P.ordinaryPairQuotientBasepoint)) := by
  refine isQuotientMap_iff_isClosed.2 ⟨?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ | rfl := P.exists_ordinaryPairQuotientπ_or_eq_basepoint z
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr PUnit.unit, rfl⟩
  · intro s
    -- The colimit topology is final for the two inclusions (and their common source).
    refine (TopCat.isClosed_iff_of_isColimit _
      (pushoutIsPushout P.map (quotientPointMap P)) s).trans ?_
    simp only [isClosed_sum_iff]
    constructor
    · intro h
      exact ⟨h WalkingSpan.left, h WalkingSpan.right⟩
    · rintro ⟨h, hpoint⟩ j
      cases j with
      | none => exact h.preimage P.map.hom.continuous
      | some j => cases j <;> assumption

/-- Maps out of the quotient are determined by the ambient space and the basepoint. -/
@[ext]
lemma ordinaryPairQuotient_hom_ext {P : TopPair.{u}} {Y : TopCat.{u}}
    {f g : P.ordinaryPairQuotient ⟶ Y}
    (hπ : P.ordinaryPairQuotientπ ≫ f = P.ordinaryPairQuotientπ ≫ g)
    (hpoint : f P.ordinaryPairQuotientBasepoint = g P.ordinaryPairQuotientBasepoint) : f = g := by
  apply pushout.hom_ext hπ
  ext x
  exact hpoint

/-- Descend an ambient map constant on the subspace, with specified value at the added point.
The specified value is still needed when the subspace is empty. -/
def ordinaryPairQuotientDesc (P : TopPair.{u}) {Y : TopCat.{u}} (f : P.fst ⟶ Y) (y : Y)
    (h : ∀ b : P.snd, f (P.map b) = y) : P.ordinaryPairQuotient ⟶ Y :=
  pushout.desc f (TopCat.ofHom ⟨fun _ ↦ y, continuous_const⟩) (by ext b; exact h b)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma ordinaryPairQuotientπ_desc (P : TopPair.{u}) {Y : TopCat.{u}} (f : P.fst ⟶ Y)
    (y : Y) (h : ∀ b : P.snd, f (P.map b) = y) :
    P.ordinaryPairQuotientπ ≫ P.ordinaryPairQuotientDesc f y h = f :=
  pushout.inl_desc _ _ _

@[simp]
lemma ordinaryPairQuotientDesc_basepoint (P : TopPair.{u}) {Y : TopCat.{u}}
    (f : P.fst ⟶ Y) (y : Y) (h : ∀ b : P.snd, f (P.map b) = y) :
    P.ordinaryPairQuotientDesc f y h P.ordinaryPairQuotientBasepoint = y :=
  ConcreteCategory.congr_hom (pushout.inr_desc f
    (TopCat.ofHom ⟨fun _ : PUnit.{u + 1} ↦ y, continuous_const⟩) _) PUnit.unit

/-- An ambient map sending the subspace to a chosen point has a unique descent taking the
quotient basepoint to that point. -/
lemma existsUnique_ordinaryPairQuotientDesc (P : TopPair.{u}) {Y : TopCat.{u}}
    (f : P.fst ⟶ Y) (y : Y) (h : ∀ b : P.snd, f (P.map b) = y) :
    ∃! g : P.ordinaryPairQuotient ⟶ Y,
      P.ordinaryPairQuotientπ ≫ g = f ∧ g P.ordinaryPairQuotientBasepoint = y := by
  refine ⟨P.ordinaryPairQuotientDesc f y h, ⟨by simp, by simp⟩, ?_⟩
  intro g hg
  apply ordinaryPairQuotient_hom_ext
  · simpa using hg.1
  · simpa using hg.2

/-- For an empty subspace the quotient is the ambient space with an added disjoint point. -/
def ordinaryPairQuotientEmptyHomeomorph (P : TopPair.{u}) [IsEmpty P.snd] :
    P.ordinaryPairQuotient ≃ₜ P.fst ⊕ PUnit.{u + 1} := by
  let f : P.ordinaryPairQuotient ⟶ TopCat.of (P.fst ⊕ PUnit.{u + 1}) :=
    P.ordinaryPairQuotientDesc (TopCat.ofHom ⟨Sum.inl, continuous_inl⟩)
      (Sum.inr PUnit.unit) (fun b ↦ isEmptyElim b)
  let g : TopCat.of (P.fst ⊕ PUnit.{u + 1}) ⟶ P.ordinaryPairQuotient :=
    TopCat.ofHom ⟨Sum.elim P.ordinaryPairQuotientπ
      (fun _ ↦ P.ordinaryPairQuotientBasepoint),
      continuous_sum_dom.2 ⟨P.ordinaryPairQuotientπ.hom.continuous, continuous_const⟩⟩
  refine TopCat.homeoOfIso { hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply ordinaryPairQuotient_hom_ext
    · simp only [← Category.assoc]
      rw [ordinaryPairQuotientπ_desc]
      rfl
    · exact congrArg (fun z ↦ g z) (ordinaryPairQuotientDesc_basepoint _ _ _ _)
  · ext (x | x)
    · exact ordinaryPairQuotientπ_desc_apply _ _ _ _ x
    · exact ordinaryPairQuotientDesc_basepoint _ _ _ _

@[simp]
lemma ordinaryPairQuotientEmptyHomeomorph_π (P : TopPair.{u}) [IsEmpty P.snd] (x : P.fst) :
    P.ordinaryPairQuotientEmptyHomeomorph (P.ordinaryPairQuotientπ x) = Sum.inl x :=
  ordinaryPairQuotientπ_desc_apply _ _ _ (fun b ↦ isEmptyElim b) x

@[simp]
lemma ordinaryPairQuotientEmptyHomeomorph_basepoint (P : TopPair.{u}) [IsEmpty P.snd] :
    P.ordinaryPairQuotientEmptyHomeomorph P.ordinaryPairQuotientBasepoint = Sum.inr PUnit.unit :=
  ordinaryPairQuotientDesc_basepoint _ _ _ (fun b ↦ isEmptyElim b)

@[simp]
lemma ordinaryPairQuotientEmptyHomeomorph_symm_inl (P : TopPair.{u}) [IsEmpty P.snd] (x : P.fst) :
    P.ordinaryPairQuotientEmptyHomeomorph.symm (Sum.inl x) = P.ordinaryPairQuotientπ x := (rfl)

@[simp]
lemma ordinaryPairQuotientEmptyHomeomorph_symm_inr (P : TopPair.{u}) [IsEmpty P.snd]
    (x : PUnit.{u + 1}) :
    P.ordinaryPairQuotientEmptyHomeomorph.symm (Sum.inr x) =
      P.ordinaryPairQuotientBasepoint := (rfl)

/-- The induced based map of quotients for a map of topological pairs. -/
def ordinaryPairQuotientMap {P Q : TopPair.{u}} (f : P ⟶ Q) :
    P.ordinaryPairQuotient ⟶ Q.ordinaryPairQuotient :=
  P.ordinaryPairQuotientDesc (Hom.fst f ≫ Q.ordinaryPairQuotientπ)
    Q.ordinaryPairQuotientBasepoint (fun b ↦ by
      have h := ConcreteCategory.congr_hom (Hom.w f) b
      simp only [ConcreteCategory.comp_apply] at h
      simpa only [ConcreteCategory.comp_apply, h] using
        Q.ordinaryPairQuotientπ_map (Hom.snd f b))

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma ordinaryPairQuotientπ_naturality {P Q : TopPair.{u}} (f : P ⟶ Q) :
    P.ordinaryPairQuotientπ ≫ ordinaryPairQuotientMap f =
      Hom.fst f ≫ Q.ordinaryPairQuotientπ :=
  ordinaryPairQuotientπ_desc _ _ _ _

@[simp]
lemma ordinaryPairQuotientMap_basepoint {P Q : TopPair.{u}} (f : P ⟶ Q) :
    ordinaryPairQuotientMap f P.ordinaryPairQuotientBasepoint =
      Q.ordinaryPairQuotientBasepoint :=
  ordinaryPairQuotientDesc_basepoint _ _ _ _

@[simp]
lemma ordinaryPairQuotientMap_id (P : TopPair.{u}) :
    ordinaryPairQuotientMap (𝟙 P) = 𝟙 P.ordinaryPairQuotient := by
  apply ordinaryPairQuotient_hom_ext
  · rw [ordinaryPairQuotientπ_naturality]
    rfl
  · simp

@[simp]
lemma ordinaryPairQuotientMap_comp {P Q S : TopPair.{u}} (f : P ⟶ Q) (g : Q ⟶ S) :
    ordinaryPairQuotientMap (f ≫ g) = ordinaryPairQuotientMap f ≫ ordinaryPairQuotientMap g := by
  apply ordinaryPairQuotient_hom_ext
  · simp only [ordinaryPairQuotientπ_naturality, ordinaryPairQuotientπ_naturality_assoc]
    -- The ambient component of a composite of pair maps is its composite in TopCat.
    rfl
  · simp

/-- The pointed quotient construction, viewed as a functor to topological spaces. Its maps
also preserve the specified basepoints. -/
-- Expose the functor so its object fields compute in the types of induced morphisms.
@[expose]
def ordinaryPairQuotientFunctor : TopPair.{u} ⥤ TopCat.{u} where
  obj := ordinaryPairQuotient
  map := ordinaryPairQuotientMap
  map_id := ordinaryPairQuotientMap_id
  map_comp := ordinaryPairQuotientMap_comp

@[simp]
lemma ordinaryPairQuotientFunctor_obj (P : TopPair.{u}) :
    ordinaryPairQuotientFunctor.obj P = P.ordinaryPairQuotient := (rfl)

@[simp]
lemma ordinaryPairQuotientFunctor_map {P Q : TopPair.{u}} (f : P ⟶ Q) :
    ordinaryPairQuotientFunctor.map f = ordinaryPairQuotientMap f := (rfl)

end TopPair
