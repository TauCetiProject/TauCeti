/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding

/-!
# The pointed quotient of a topological pair

For a pair `(X, B)`, `TopPair.ordinaryPairQuotient` collapses `B` and a separately added point
in `X ⊔ *` to one basepoint. It is the topological pushout of `X ← B → *`, so its topology
is the quotient topology and its maps are determined by their values on `X` and the basepoint.
In particular, when `B` is empty the result is `X` with a disjoint basepoint, when `B = X` it
is a single point (`TopPair.subsingleton_ordinaryPairQuotient_iff`), and collapsing a singleton
`{x₀}` recovers `X` (`TopPair.ordinaryPairQuotientSingletonHomeomorph`).

The collapse map, its fibres, open and closed subsets, quotient-map criteria, compactness,
Hausdorff separation when `X` is `T₃` and `B` is closed, the universal mapping property, and
functoriality in maps of pairs are supplied here. These are the carrier and map interfaces used
to build pointed smash products and reduced suspensions and to compare relative invariants with
reduced invariants of a quotient, including pairs with empty subspace.

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
    have sq : IsPushout P.map (quotientPointMap P)
        P.ordinaryPairQuotientπ (quotientPointIncl P) := IsPushout.of_hasPushout _ _
    refine (TauCeti.TopCat.isClosed_iff_of_isPushout sq s).trans ?_
    simp only [isClosed_sum_iff]
    constructor <;> intro h <;> exact ⟨h.1, h.2⟩

/-- Maps out of the quotient are determined by the ambient space and the basepoint. -/
@[ext]
lemma ordinaryPairQuotient_hom_ext {P : TopPair.{u}} {Y : TopCat.{u}}
    {f g : P.ordinaryPairQuotient ⟶ Y}
    (hπ : P.ordinaryPairQuotientπ ≫ f = P.ordinaryPairQuotientπ ≫ g)
    (hpoint : f P.ordinaryPairQuotientBasepoint = g P.ordinaryPairQuotientBasepoint) : f = g := by
  apply pushout.hom_ext hπ
  ext _
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
  · ext (x | _)
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

instance instInhabitedOrdinaryPairQuotient (P : TopPair.{u}) :
    Inhabited P.ordinaryPairQuotient :=
  ⟨P.ordinaryPairQuotientBasepoint⟩

/-- Induction principle for the pointed quotient of a pair: it suffices to treat ambient
representatives and the basepoint. -/
@[elab_as_elim]
lemma ordinaryPairQuotient_ind {P : TopPair.{u}} {motive : P.ordinaryPairQuotient → Prop}
    (hπ : ∀ x, motive (P.ordinaryPairQuotientπ x))
    (hbase : motive P.ordinaryPairQuotientBasepoint) (z : P.ordinaryPairQuotient) : motive z := by
  obtain ⟨x, rfl⟩ | rfl := P.exists_ordinaryPairQuotientπ_or_eq_basepoint z
  · exact hπ x
  · exact hbase

/-- A subset of the pointed quotient is open exactly when its preimage in the ambient space is
open; the added one-point summand is discrete. -/
lemma isOpen_ordinaryPairQuotient_iff (P : TopPair.{u}) {s : Set P.ordinaryPairQuotient} :
    IsOpen s ↔ IsOpen (P.ordinaryPairQuotientπ ⁻¹' s) := by
  rw [← P.isQuotientMap_ordinaryPairQuotient.isOpen_preimage, isOpen_sum_iff]
  exact and_iff_left (isOpen_discrete _)

/-- A subset of the pointed quotient is closed exactly when its preimage in the ambient space is
closed. -/
lemma isClosed_ordinaryPairQuotient_iff (P : TopPair.{u}) {s : Set P.ordinaryPairQuotient} :
    IsClosed s ↔ IsClosed (P.ordinaryPairQuotientπ ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_ordinaryPairQuotient_iff, Set.preimage_compl]

/-- The collapse map from the ambient space onto the pointed quotient is surjective exactly when
the subspace is nonempty. -/
lemma surjective_ordinaryPairQuotientπ_iff (P : TopPair.{u}) :
    Function.Surjective P.ordinaryPairQuotientπ ↔ Nonempty P.snd := by
  refine ⟨fun h ↦ ?_, fun ⟨b⟩ z ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h P.ordinaryPairQuotientBasepoint
    obtain ⟨b, _⟩ := (P.ordinaryPairQuotientπ_eq_basepoint_iff x).1 hx
    exact ⟨b⟩
  · obtain ⟨x, rfl⟩ | rfl := P.exists_ordinaryPairQuotientπ_or_eq_basepoint z
    · exact ⟨x, rfl⟩
    · exact ⟨P.map b, P.ordinaryPairQuotientπ_map b⟩

/-- When the subspace is nonempty, the ambient collapse map is surjective. -/
lemma surjective_ordinaryPairQuotientπ (P : TopPair.{u}) [Nonempty P.snd] :
    Function.Surjective P.ordinaryPairQuotientπ :=
  P.surjective_ordinaryPairQuotientπ_iff.2 inferInstance

/-- When the subspace is nonempty, the ambient collapse map is a quotient map. -/
lemma isQuotientMap_ordinaryPairQuotientπ (P : TopPair.{u}) [Nonempty P.snd] :
    IsQuotientMap P.ordinaryPairQuotientπ :=
  isQuotientMap_iff_isClosed.2 ⟨P.surjective_ordinaryPairQuotientπ,
    fun _ ↦ P.isClosed_ordinaryPairQuotient_iff⟩

/-- The pointed quotient of `(X, B)` is a subsingleton exactly when `B = X`: collapsing the entire
ambient space identifies it with the added basepoint. -/
lemma subsingleton_ordinaryPairQuotient_iff (P : TopPair.{u}) :
    Subsingleton P.ordinaryPairQuotient ↔ Function.Surjective P.map := by
  refine ⟨fun _ y ↦ (P.ordinaryPairQuotientπ_eq_basepoint_iff y).1 (Subsingleton.elim _ _),
    fun h ↦ ⟨fun z₁ z₂ ↦ ?_⟩⟩
  have hbase (z : P.ordinaryPairQuotient) : z = P.ordinaryPairQuotientBasepoint := by
    induction z using ordinaryPairQuotient_ind with
    | hπ x =>
      obtain ⟨b, rfl⟩ := h x
      exact P.ordinaryPairQuotientπ_map b
    | hbase => rfl
  exact (hbase z₁).trans (hbase z₂).symm

/-- The pointed quotient of a pair with compact ambient space is compact. -/
instance compactSpace_ordinaryPairQuotient (P : TopPair.{u}) [CompactSpace P.fst] :
    CompactSpace P.ordinaryPairQuotient :=
  isCompact_univ_iff.1 <| by
    rw [← P.isQuotientMap_ordinaryPairQuotient.surjective.range_eq]
    exact isCompact_range P.isQuotientMap_ordinaryPairQuotient.continuous

private lemma preimage_image_ordinaryPairQuotientπ_of_disjoint (P : TopPair.{u}) {V : Set P.fst}
    (hV : Disjoint V (Set.range P.map)) :
    P.ordinaryPairQuotientπ ⁻¹' (P.ordinaryPairQuotientπ '' V) = V := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  refine ⟨?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hyx⟩
  rcases (P.ordinaryPairQuotientπ_eq_iff y x).1 hyx with rfl | ⟨hyB, _⟩
  · exact hy
  · exact (Set.disjoint_left.1 hV hy hyB).elim

private lemma preimage_insert_basepoint_image_ordinaryPairQuotientπ (P : TopPair.{u})
    {U : Set P.fst} (hU : Set.range P.map ⊆ U) :
    P.ordinaryPairQuotientπ ⁻¹'
      (insert P.ordinaryPairQuotientBasepoint (P.ordinaryPairQuotientπ '' U)) = U := by
  ext x
  simp only [Set.mem_preimage, Set.mem_insert_iff, P.ordinaryPairQuotientπ_eq_basepoint_iff,
    Set.mem_image]
  refine ⟨?_, fun hx ↦ Or.inr ⟨x, hx, rfl⟩⟩
  rintro (hxB | ⟨y, hy, hyx⟩)
  · exact hU hxB
  · rcases (P.ordinaryPairQuotientπ_eq_iff y x).1 hyx with rfl | ⟨_, hxB⟩
    · exact hy
    · exact hU hxB

private lemma exists_disjoint_isOpen_basepoint_ordinaryPairQuotient (P : TopPair.{u})
    [T3Space P.fst] (hP : IsClosed (Set.range P.map)) {x : P.fst}
    (hx : x ∉ Set.range P.map) :
    ∃ W₁ W₂ : Set P.ordinaryPairQuotient, IsOpen W₁ ∧ IsOpen W₂ ∧
      P.ordinaryPairQuotientBasepoint ∈ W₁ ∧ P.ordinaryPairQuotientπ x ∈ W₂ ∧
      Disjoint W₁ W₂ := by
  obtain ⟨U, ⟨hUo, hBU⟩, V, ⟨hxV, hVo⟩, hUV⟩ :=
    ((hasBasis_nhdsSet _).disjoint_iff (nhds_basis_opens x)).1 (RegularSpace.regular hP hx)
  have hVB : Disjoint V (Set.range P.map) := hUV.symm.mono_right hBU
  refine ⟨insert P.ordinaryPairQuotientBasepoint (P.ordinaryPairQuotientπ '' U),
    P.ordinaryPairQuotientπ '' V, ?_, ?_, Or.inl rfl, ⟨x, hxV, rfl⟩, ?_⟩
  · rw [P.isOpen_ordinaryPairQuotient_iff,
      P.preimage_insert_basepoint_image_ordinaryPairQuotientπ hBU]
    exact hUo
  · rw [P.isOpen_ordinaryPairQuotient_iff, P.preimage_image_ordinaryPairQuotientπ_of_disjoint hVB]
    exact hVo
  · refine Set.disjoint_left.2 fun _ hz₁ hz₂ ↦ ?_
    obtain ⟨v, hv, rfl⟩ := hz₂
    have hvU : v ∈ U :=
      (Set.ext_iff.1 (P.preimage_insert_basepoint_image_ordinaryPairQuotientπ hBU) v).1 hz₁
    exact Set.disjoint_left.1 hUV hvU hv

/-- The pointed quotient of a pair with `T₃` ambient space and closed subspace is Hausdorff. -/
lemma t2Space_ordinaryPairQuotient_of_isClosed (P : TopPair.{u}) [T3Space P.fst]
    (hP : IsClosed (Set.range P.map)) : T2Space P.ordinaryPairQuotient := by
  refine ⟨fun {z₁ z₂} hne ↦ ?_⟩
  by_cases hz₁ : z₁ = P.ordinaryPairQuotientBasepoint
  · subst hz₁
    obtain ⟨x, rfl⟩ | rfl := P.exists_ordinaryPairQuotientπ_or_eq_basepoint z₂
    · have hx : x ∉ Set.range P.map :=
        fun hx ↦ hne ((P.ordinaryPairQuotientπ_eq_basepoint_iff x).2 hx).symm
      obtain ⟨W₁, W₂, hW₁, hW₂, hz₁, hz₂, hdisj⟩ :=
        P.exists_disjoint_isOpen_basepoint_ordinaryPairQuotient hP hx
      exact ⟨W₁, W₂, hW₁, hW₂, hz₁, hz₂, hdisj⟩
    · exact (hne rfl).elim
  by_cases hz₂ : z₂ = P.ordinaryPairQuotientBasepoint
  · subst hz₂
    obtain ⟨x, rfl⟩ := (P.exists_ordinaryPairQuotientπ_or_eq_basepoint z₁).resolve_right hz₁
    have hx : x ∉ Set.range P.map :=
      fun hx ↦ hz₁ ((P.ordinaryPairQuotientπ_eq_basepoint_iff x).2 hx)
    obtain ⟨W₁, W₂, hW₁, hW₂, hb, hxW, hdisj⟩ :=
      P.exists_disjoint_isOpen_basepoint_ordinaryPairQuotient hP hx
    exact ⟨W₂, W₁, hW₂, hW₁, hxW, hb, hdisj.symm⟩
  obtain ⟨x₁, rfl⟩ := (P.exists_ordinaryPairQuotientπ_or_eq_basepoint z₁).resolve_right hz₁
  obtain ⟨x₂, rfl⟩ := (P.exists_ordinaryPairQuotientπ_or_eq_basepoint z₂).resolve_right hz₂
  have hx₁ : x₁ ∉ Set.range P.map :=
    fun hx ↦ hz₁ ((P.ordinaryPairQuotientπ_eq_basepoint_iff x₁).2 hx)
  have hx₂ : x₂ ∉ Set.range P.map :=
    fun hx ↦ hz₂ ((P.ordinaryPairQuotientπ_eq_basepoint_iff x₂).2 hx)
  obtain ⟨U₁, U₂, hU₁, hU₂, hx₁U, hx₂U, hdisj⟩ := t2_separation fun h : x₁ = x₂ ↦ hne (h ▸ rfl)
  let V₁ := U₁ ∩ (Set.range P.map)ᶜ
  let V₂ := U₂ ∩ (Set.range P.map)ᶜ
  have hV₁B : Disjoint V₁ (Set.range P.map) := disjoint_compl_left.mono_left Set.inter_subset_right
  have hV₂B : Disjoint V₂ (Set.range P.map) := disjoint_compl_left.mono_left Set.inter_subset_right
  refine ⟨P.ordinaryPairQuotientπ '' V₁, P.ordinaryPairQuotientπ '' V₂, ?_, ?_,
    ⟨x₁, ⟨hx₁U, hx₁⟩, rfl⟩, ⟨x₂, ⟨hx₂U, hx₂⟩, rfl⟩, ?_⟩
  · rw [P.isOpen_ordinaryPairQuotient_iff, P.preimage_image_ordinaryPairQuotientπ_of_disjoint hV₁B]
    exact hU₁.inter hP.isOpen_compl
  · rw [P.isOpen_ordinaryPairQuotient_iff, P.preimage_image_ordinaryPairQuotientπ_of_disjoint hV₂B]
    exact hU₂.inter hP.isOpen_compl
  · refine Set.disjoint_left.2 fun _ hz₁ hz₂ ↦ ?_
    obtain ⟨u, hu, rfl⟩ := hz₁
    have huV₂ : u ∈ V₂ :=
      (Set.ext_iff.1 (P.preimage_image_ordinaryPairQuotientπ_of_disjoint hV₂B) u).1 hz₂
    exact Set.disjoint_left.1 hdisj hu.1 huV₂.1

/-- The pointed quotient of a pair with `T₃` ambient space and compact subspace is Hausdorff,
including when the subspace is empty. -/
instance t2Space_ordinaryPairQuotient (P : TopPair.{u}) [T3Space P.fst] [CompactSpace P.snd] :
    T2Space P.ordinaryPairQuotient :=
  P.t2Space_ordinaryPairQuotient_of_isClosed (isCompact_range P.map.hom.continuous).isClosed

/-- Collapsing a singleton `{x₀}` in `X` together with the added basepoint recovers `X`,
with no separation assumption on `X`. -/
def ordinaryPairQuotientSingletonIso {X : TopCat.{u}} (x₀ : X) :
    (ofSubset ({x₀} : Set X)).ordinaryPairQuotient ≅ X where
  hom := (ofSubset ({x₀} : Set X)).ordinaryPairQuotientDesc
    (TopCat.ofHom (ContinuousMap.id X)) x₀ fun b ↦ b.2
  inv := (ofSubset ({x₀} : Set X)).ordinaryPairQuotientπ
  hom_inv_id := by
    apply ordinaryPairQuotient_hom_ext
    · ext x
      exact congrArg (ofSubset ({x₀} : Set X)).ordinaryPairQuotientπ
        (ordinaryPairQuotientπ_desc_apply (ofSubset ({x₀} : Set X))
          (TopCat.ofHom (ContinuousMap.id X)) x₀ (fun b ↦ b.2) x)
    · exact (congrArg (fun z ↦ (ofSubset ({x₀} : Set X)).ordinaryPairQuotientπ z)
        (ordinaryPairQuotientDesc_basepoint _ _ _ _)).trans
        ((ofSubset ({x₀} : Set X)).ordinaryPairQuotientπ_map ⟨x₀, rfl⟩)
  inv_hom_id := ordinaryPairQuotientπ_desc _ _ _ _

/-- Collapsing a singleton `{x₀}` in `X` together with the added basepoint is homeomorphic to `X`,
carrying the quotient basepoint to `x₀`. -/
def ordinaryPairQuotientSingletonHomeomorph {X : TopCat.{u}} (x₀ : X) :
    (ofSubset ({x₀} : Set X)).ordinaryPairQuotient ≃ₜ X :=
  TopCat.homeoOfIso (ordinaryPairQuotientSingletonIso x₀)

@[simp]
lemma ordinaryPairQuotientSingletonHomeomorph_π {X : TopCat.{u}} (x₀ x : X) :
    ordinaryPairQuotientSingletonHomeomorph x₀
      ((ofSubset ({x₀} : Set X)).ordinaryPairQuotientπ x) = x :=
  ordinaryPairQuotientπ_desc_apply (ofSubset ({x₀} : Set X))
    (TopCat.ofHom (ContinuousMap.id X)) x₀ (fun b ↦ b.2) x

@[simp]
lemma ordinaryPairQuotientSingletonHomeomorph_basepoint {X : TopCat.{u}} (x₀ : X) :
    ordinaryPairQuotientSingletonHomeomorph x₀
      (ofSubset ({x₀} : Set X)).ordinaryPairQuotientBasepoint = x₀ :=
  ordinaryPairQuotientDesc_basepoint (ofSubset ({x₀} : Set X))
    (TopCat.ofHom (ContinuousMap.id X)) x₀ (fun b ↦ b.2)

@[simp]
lemma ordinaryPairQuotientSingletonHomeomorph_symm_apply {X : TopCat.{u}} (x₀ x : X) :
    (ordinaryPairQuotientSingletonHomeomorph x₀).symm x =
      (ofSubset ({x₀} : Set X)).ordinaryPairQuotientπ x := (rfl)

/-- An isomorphism of topological pairs induces an isomorphism of their pointed quotients. -/
def ordinaryPairQuotientIso {P Q : TopPair.{u}} (e : P ≅ Q) :
    P.ordinaryPairQuotient ≅ Q.ordinaryPairQuotient where
  hom := ordinaryPairQuotientMap e.hom
  inv := ordinaryPairQuotientMap e.inv
  hom_inv_id := by rw [← ordinaryPairQuotientMap_comp, e.hom_inv_id, ordinaryPairQuotientMap_id]
  inv_hom_id := by rw [← ordinaryPairQuotientMap_comp, e.inv_hom_id, ordinaryPairQuotientMap_id]

/-- An isomorphism of topological pairs induces a pointed homeomorphism of their pointed
quotients. -/
def ordinaryPairQuotientHomeomorph {P Q : TopPair.{u}} (e : P ≅ Q) :
    P.ordinaryPairQuotient ≃ₜ Q.ordinaryPairQuotient :=
  TopCat.homeoOfIso (ordinaryPairQuotientIso e)

@[simp]
lemma ordinaryPairQuotientHomeomorph_π {P Q : TopPair.{u}} (e : P ≅ Q) (x : P.fst) :
    ordinaryPairQuotientHomeomorph e (P.ordinaryPairQuotientπ x) =
      Q.ordinaryPairQuotientπ (Hom.fst e.hom x) :=
  ordinaryPairQuotientπ_naturality_apply e.hom x

@[simp]
lemma ordinaryPairQuotientHomeomorph_basepoint {P Q : TopPair.{u}} (e : P ≅ Q) :
    ordinaryPairQuotientHomeomorph e P.ordinaryPairQuotientBasepoint =
      Q.ordinaryPairQuotientBasepoint :=
  ordinaryPairQuotientMap_basepoint e.hom

@[simp]
lemma ordinaryPairQuotientHomeomorph_symm {P Q : TopPair.{u}} (e : P ≅ Q) :
    (ordinaryPairQuotientHomeomorph e).symm = ordinaryPairQuotientHomeomorph e.symm := (rfl)

end TopPair
