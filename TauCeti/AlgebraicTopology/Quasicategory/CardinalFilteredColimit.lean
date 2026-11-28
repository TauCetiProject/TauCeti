/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Presentable.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.Limit
public import TauCeti.AlgebraicTopology.SimplicialSet.CardinalFiltered

/-!
# Cardinal filtered colimits in quasicategories

Let `κ` be a cardinal, typically an infinite regular cardinal. A simplicial set `C`, typically a
quasicategory, *has `κ`-filtered colimits* (`SSet.HasCardinalFilteredColimits`) if every diagram
`p : K ⟶ C` indexed by a `κ`-filtered simplicial set `K` (`SSet.IsCardinalFiltered`) has a colimit
cocone, an initial vertex of the coslice `C_{p/}` (`SSet.coslice.IsColimit`). A map `f : C ⟶ D`
*preserves `κ`-filtered colimits* (`SSet.PreservesCardinalFilteredColimits`) if pushing cocones
forward along `f` (`SSet.coslice.map`) sends the colimit cocones of such diagrams to colimit
cocones. For `κ : Cardinal.{w}`, the diagrams are indexed by `w`-small simplicial sets, those
whose simplices form a `w`-small type, as in Mathlib's `CategoryTheory.HasCardinalFilteredColimits`,
which quantifies over `κ`-filtered categories in `Type w`. These are the notions through which
`κ`-compact objects, accessible and presentable quasicategories are defined.

Isomorphisms, and in particular identities, preserve `κ`-filtered colimits, and so do composites
of maps preserving them. As a `κ'`-filtered simplicial set is `κ`-filtered for `κ ≤ κ'`, having and
preserving `κ`-filtered colimits imply having and preserving `κ'`-filtered colimits.

For the nerve of a preorder `P`, colimit cocones are least upper bounds
(`SSet.coslice.isColimit_iff_isLUB`), and the nerve of `P` has `κ`-filtered colimits exactly when
every `w`-small subset of `P` whose subsets with fewer than `κ` elements are bounded above in it
has a least upper bound (`SSet.hasCardinalFilteredColimits_nerve_iff`). For a regular cardinal `κ`
this is the existence of colimits of `κ`-filtered diagrams in `P` in the sense of Mathlib's
`CategoryTheory.HasCardinalFilteredColimits`
(`SSet.hasCardinalFilteredColimits_nerve_iff_hasCardinalFilteredColimits`).

## Main declarations

* `SSet.HasCardinalFilteredColimits C κ`: the simplicial set `C` has `κ`-filtered colimits.
* `SSet.PreservesCardinalFilteredColimits f κ`: the map `f` preserves `κ`-filtered colimits.
* `SSet.HasCardinalFilteredColimits.of_le`, `SSet.PreservesCardinalFilteredColimits.of_le`:
  monotonicity in `κ`.
* `SSet.HasCardinalFilteredColimits.of_iso`: invariance under isomorphism.
* `SSet.PreservesCardinalFilteredColimits.of_isIso`, `SSet.PreservesCardinalFilteredColimits.comp`:
  isomorphisms preserve `κ`-filtered colimits, and preservation is stable under composition.
* `SSet.hasCardinalFilteredColimits_of_isTerminal`: a terminal simplicial set, such as `Δ[0]`, has
  `κ`-filtered colimits for every `κ`.
* `SSet.hasCardinalFilteredColimits_nerve_iff`: the order-theoretic characterization for the nerve
  of a preorder.
* `SSet.hasCardinalFilteredColimits_nerve_iff_hasCardinalFilteredColimits`: the comparison with
  Mathlib's `κ`-filtered colimits for the nerve of a preorder.
* `SSet.hasCardinalFilteredColimits_nerve_discrete`: the nerve of a discrete category has
  `κ`-filtered colimits for `κ > 2`.

## References

* J. Lurie, *Higher Topos Theory*, Definition 5.3.1.7, Example 5.3.1.8 and §5.3.
-/

public section

open CategoryTheory Limits Opposite Simplicial

universe w u

namespace SSet

/-- A simplicial set `C` *has `κ`-filtered colimits* if every diagram `p : K ⟶ C` indexed by a
`κ`-filtered simplicial set `K` whose simplices form a `w`-small type has a colimit cocone. -/
class HasCardinalFilteredColimits (C : SSet.{u}) (κ : Cardinal.{w}) : Prop where
  exists_isColimit ⦃K : SSet.{u}⦄ [Small.{w} (Σ n : ℕ, K _⦋n⦌)] [K.IsCardinalFiltered κ]
    (p : K ⟶ C) :
    ∃ c : (coslice p) _⦋0⦌, coslice.IsColimit p c

/-- A map `f : C ⟶ D` *preserves `κ`-filtered colimits* if, for every diagram `p : K ⟶ C` indexed
by a `κ`-filtered simplicial set `K` whose simplices form a `w`-small type, pushing cocones forward
along `f` sends colimit cocones under `p` to colimit cocones under `p ≫ f`. The pushed-forward
cocone is the image under `SSet.coslice.map`, and the diagram `q = p ≫ f` is allowed up to
equality. -/
class PreservesCardinalFilteredColimits {C D : SSet.{u}} (f : C ⟶ D) (κ : Cardinal.{w}) :
    Prop where
  isColimit_map ⦃K : SSet.{u}⦄ [Small.{w} (Σ n : ℕ, K _⦋n⦌)] [K.IsCardinalFiltered κ]
    ⦃p : K ⟶ C⦄ ⦃q : K ⟶ D⦄ (h : 𝟙 K ≫ p ≫ f = q) ⦃c : (coslice p) _⦋0⦌⦄
    (hc : coslice.IsColimit p c) :
    coslice.IsColimit q ((coslice.map (𝟙 K) f h).app _ c)

variable {C D E : SSet.{u}} {κ κ' : Cardinal.{w}}

namespace HasCardinalFilteredColimits

variable (C) in
/-- Having `κ`-filtered colimits is monotone in `κ`: for `κ ≤ κ'`, every `κ'`-filtered simplicial
set is `κ`-filtered. -/
lemma of_le [C.HasCardinalFilteredColimits κ] (h : κ ≤ κ') : C.HasCardinalFilteredColimits κ' where
  exists_isColimit K _ _ p :=
    have := IsCardinalFiltered.of_le K h
    exists_isColimit κ p

/-- Having `κ`-filtered colimits is invariant under isomorphism. -/
lemma of_iso [C.HasCardinalFilteredColimits κ] (e : C ≅ D) : D.HasCardinalFilteredColimits κ where
  exists_isColimit _ _ _ p := by
    obtain ⟨c, hc⟩ := exists_isColimit (C := C) κ (p ≫ e.inv)
    exact ⟨_, (coslice.isColimit_map_iff_of_isIso (𝟙 _) e.hom (by simp) c).2 hc⟩

end HasCardinalFilteredColimits

namespace PreservesCardinalFilteredColimits

/-- Isomorphisms preserve `κ`-filtered colimits. -/
instance of_isIso (f : C ⟶ D) [IsIso f] : PreservesCardinalFilteredColimits f κ where
  isColimit_map _ _ _ _ _ h _ hc := (coslice.isColimit_map_iff_of_isIso (𝟙 _) f h _).2 hc

/-- The identity preserves `κ`-filtered colimits. -/
instance id : PreservesCardinalFilteredColimits (𝟙 C) κ :=
  of_isIso _

/-- A composite of maps preserving `κ`-filtered colimits preserves `κ`-filtered colimits. -/
instance comp (f : C ⟶ D) (g : D ⟶ E) [PreservesCardinalFilteredColimits f κ]
    [PreservesCardinalFilteredColimits g κ] : PreservesCardinalFilteredColimits (f ≫ g) κ where
  isColimit_map K _ _ p q h c hc := by
    have h' : 𝟙 K ≫ (p ≫ f) ≫ g = q := by simpa using h
    -- Pushing forward along `f ≫ g` is pushing forward along `f`, then along `g`.
    have e : coslice.map (𝟙 K) (f ≫ g) h =
        coslice.map (𝟙 K) f (Category.id_comp _) ≫ coslice.map (𝟙 K) g h' := by
      rw [coslice.map_comp]
      simp only [Category.comp_id]
    rw [e, comp_app, ConcreteCategory.comp_apply]
    exact isColimit_map κ h' (isColimit_map κ (Category.id_comp _) hc)

variable (f : C ⟶ D)

/-- Preserving `κ`-filtered colimits is monotone in `κ`. -/
lemma of_le [PreservesCardinalFilteredColimits f κ] (h : κ ≤ κ') :
    PreservesCardinalFilteredColimits f κ' where
  isColimit_map K _ _ _ _ hq _ hc :=
    have := IsCardinalFiltered.of_le K h
    isColimit_map κ hq hc

/-- Every map to a terminal simplicial set, such as `Δ[0]`, preserves `κ`-filtered colimits, since
every cocone in a terminal simplicial set is a colimit cocone. -/
lemma of_isTerminal (hD : IsTerminal D) : PreservesCardinalFilteredColimits f κ where
  isColimit_map _ _ _ _ q _ _ _ := coslice.isColimit_of_isTerminal q hD _

end PreservesCardinalFilteredColimits

/-- A terminal simplicial set, such as `Δ[0]`, has `κ`-filtered colimits for every `κ`: every
cocone in it is a colimit cocone. -/
lemma hasCardinalFilteredColimits_of_isTerminal (hC : IsTerminal C) :
    C.HasCardinalFilteredColimits κ where
  exists_isColimit _ _ _ p :=
    ⟨yonedaEquiv ((coslice.isTerminal p hC).from Δ[0]), coslice.isColimit_of_isTerminal p hC _⟩

/-- The standard `0`-simplex has `κ`-filtered colimits for every `κ`. -/
instance hasCardinalFilteredColimits_stdSimplex_zero :
    (Δ[0] : SSet.{u}).HasCardinalFilteredColimits κ :=
  hasCardinalFilteredColimits_of_isTerminal stdSimplex.isTerminalObj₀

section Preorder

variable {P : Type u} [Preorder P]

/-- The nerve of a preorder `P` has `κ`-filtered colimits exactly when every `w`-small subset `s`
of `P` that is `κ`-directed, in the sense that its subsets with fewer than `κ` elements are bounded
above in `s`, has a least upper bound. -/
theorem hasCardinalFilteredColimits_nerve_iff :
    (nerve P).HasCardinalFilteredColimits κ ↔
      ∀ s : Set P, Small.{w} s → (∀ t : Set s, HasCardinalLT t κ → BddAbove t) →
        ∃ b, IsLUB s b := by
  refine ⟨fun _ s _ hs ↦ ?_, fun h ↦ ⟨fun K _ _ p ↦ ?_⟩⟩
  · -- The inclusion of `s` is a diagram indexed by the nerve of `s`, which is `κ`-filtered and,
    -- as a simplex of the nerve of `s` is determined by its vertices, `w`-small.
    have := isCardinalFiltered_nerve_iff.2 hs
    have (n : ℕ) : Small.{w} ((nerve s) _⦋n⦌) :=
      small_of_injective (f := fun x : (nerve s) _⦋n⦌ ↦ x.obj) fun _ _ ↦ nerve.ext_of_isThin
    let ι : nerve s ⟶ nerve P :=
      nerve.homOfVertex (fun v ↦ (nerveEquiv v).val) fun _ _ e ↦ nerve.le_of_edge (𝟙 _) e
    have hι : (Set.range fun v : (nerve s) _⦋0⦌ ↦ nerveEquiv (ι.app _ v)) = s := by
      ext x
      simp only [ι, nerve.nerveEquiv_homOfVertex_app, Set.mem_range]
      exact ⟨fun ⟨v, hv⟩ ↦ hv ▸ (nerveEquiv v).property,
        fun hx ↦ ⟨nerveEquiv.symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩⟩
    rw [← hι]
    exact (coslice.exists_isColimit_iff_exists_isLUB ι).1
      (HasCardinalFilteredColimits.exists_isColimit κ ι)
  · -- The vertices of a `κ`-filtered diagram form a `κ`-directed subset: fewer than `κ` of them
    -- have edges to a common vertex.
    have : Small.{w} (K _⦋0⦌) := small_of_injective (sigma_mk_injective (β := fun n : ℕ ↦ K _⦋n⦌))
    refine (coslice.exists_isColimit_iff_exists_isLUB p).2 (h _ inferInstance fun t ht ↦ ?_)
    choose k hk using fun x : t ↦ x.val.property
    obtain ⟨z, hz⟩ := IsCardinalFiltered.exists_edge (K := K) ht k
    exact ⟨⟨_, z, rfl⟩, fun x hx ↦
      (hk ⟨x, hx⟩).symm.trans_le (nerve.le_of_edge p (hz ⟨x, hx⟩).some)⟩

/-- For a regular cardinal `κ`, the nerve of a preorder `P` has `κ`-filtered colimits exactly when
`P` has colimits of all `κ`-filtered diagrams in the sense of Mathlib's
`CategoryTheory.HasCardinalFilteredColimits`. -/
theorem hasCardinalFilteredColimits_nerve_iff_hasCardinalFilteredColimits (κ : Cardinal.{w})
    [Fact κ.IsRegular] :
    (nerve P).HasCardinalFilteredColimits κ ↔
      CategoryTheory.HasCardinalFilteredColimits.{w} P κ := by
  rw [hasCardinalFilteredColimits_nerve_iff]
  refine ⟨fun h ↦ ⟨fun J _ _ ↦ ⟨fun F ↦ ?_⟩⟩, fun h s _ hs ↦ ?_⟩
  · -- The objects of a `κ`-filtered diagram form a `w`-small `κ`-directed subset.
    rw [Preorder.hasColimit_iff_hasLUB]
    refine h _ inferInstance fun t ht ↦ ?_
    choose j hj using fun x : t ↦ x.val.property
    obtain ⟨m, ⟨a⟩⟩ := CategoryTheory.IsCardinalFiltered.exists_max j ht
    exact ⟨⟨_, m, rfl⟩, fun x hx ↦ (hj ⟨x, hx⟩).symm.trans_le (F.map (a ⟨x, hx⟩)).le⟩
  · -- A `w`-small `κ`-directed subset is a `κ`-filtered category equivalent to a small one, so
    -- its inclusion has a colimit.
    have := (isCardinalFiltered_preorder_iff s κ).2 hs
    let e := (orderIsoShrink.{w} s).equivalence
    have := IsCardinalFiltered.of_equivalence κ e
    have := CategoryTheory.HasCardinalFilteredColimits.hasColimitsOfShape P κ (Shrink.{w} s)
    have := hasColimitsOfShape_of_equivalence (C := P) e.symm
    simpa using (Preorder.hasColimit_iff_hasLUB (Subtype.mono_coe (· ∈ s)).functor).1 inferInstance

end Preorder

section Discrete

/-- A type with the discrete order, in which `a ≤ b` exactly when `a = b`. Its nerve is the nerve
of the discrete category. -/
private def DiscreteOrder (α : Type u) : Type u := α

private instance (α : Type u) : PartialOrder (DiscreteOrder α) :=
  PartialOrder.lift (fun a : α ↦ ({a} : Set α)) Set.singleton_injective

private lemma DiscreteOrder.le_iff {α : Type u} {a b : DiscreteOrder α} : a ≤ b ↔ a = b :=
  Set.singleton_subset_singleton

/-- The identification of the discrete category on `α` with the discrete order on `α`. -/
private def DiscreteOrder.functor (α : Type u) : DiscreteOrder α ⥤ Discrete α where
  obj a := ⟨a⟩
  map f := eqToHom (congrArg Discrete.mk (DiscreteOrder.le_iff.1 f.le))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The nerve of the discrete category on `α` is the nerve of the discrete order on `α`. -/
private def nerveDiscreteIso (α : Type u) : nerve (Discrete α) ≅ nerve (DiscreteOrder α) where
  hom := nerveMap (Discrete.functor fun a : α ↦ (a : DiscreteOrder α))
  inv := nerveMap (DiscreteOrder.functor α)
  hom_inv_id := by
    ext n s : 4
    exact nerve.ext_of_isThin rfl
  inv_hom_id := by
    ext n s : 4
    exact nerve.ext_of_isThin rfl

/-- The nerve of a discrete category has `κ`-filtered colimits for every `κ > 2`, for instance for
every infinite `κ`: a `κ`-filtered diagram in it is constant at a single object, which is its
colimit. For `κ ≤ 2` this fails when there are two objects, since two vertices of a `κ`-filtered
simplicial set then need not have a common cocone. -/
theorem hasCardinalFilteredColimits_nerve_discrete (α : Type u) (hκ : HasCardinalLT Bool κ) :
    (nerve (Discrete α)).HasCardinalFilteredColimits κ := by
  suffices (nerve (DiscreteOrder α)).HasCardinalFilteredColimits κ from
    .of_iso (nerveDiscreteIso α).symm
  refine hasCardinalFilteredColimits_nerve_iff.2 fun s _ hs ↦ ?_
  -- The empty subset of `s` is bounded above in `s`, so `s` has an element `a`.
  obtain ⟨⟨a, ha⟩, -⟩ := hs ∅ (hκ.of_injective (fun x ↦ (Set.notMem_empty _ x.property).elim)
    fun x ↦ (Set.notMem_empty _ x.property).elim)
  -- Any element `b` of `s` has a common upper bound with `a` in `s`, so it is `a`.
  refine ⟨a, fun b hb ↦ ?_, fun _ hx ↦ hx ha⟩
  obtain ⟨c, hc⟩ := hs (Set.range fun i : Bool ↦ if i then ⟨a, ha⟩ else ⟨b, hb⟩)
    (hκ.of_surjective _ Set.rangeFactorization_surjective)
  have hac := DiscreteOrder.le_iff.1 (hc ⟨true, rfl⟩)
  have hbc := DiscreteOrder.le_iff.1 (hc ⟨false, rfl⟩)
  exact (hbc.trans hac.symm).le

end Discrete

end SSet
