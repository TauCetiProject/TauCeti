/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.LocallyFinite

/-!
# Maps and homotopies out of pushouts in `TopCat`

Let `P = Z ∪_a Y` be a pushout square in `TopCat`, with maps `i : B → Y`, `a : B → Z`,
`j : Y → P` and `k : Z → P`. Continuous maps out of `P` are determined by their restrictions to
`Y` and to `Z`. Since the unit interval `I` is locally compact, the cylinder `I × P` is again a
pushout: a map out of `I × P` is glued from maps out of `I × Y` and `I × Z` which agree along `a`,
as the uncurried form of the map `P → C(I, W)` glued from the curried ones. In particular,
homotopies between maps out of `P` are glued from homotopies on `Y` and on `Z`.

Conversely, a space covered by a closed subspace `A` and finitely many closed pieces `B k`, any two
of which meet only inside `A`, is the pushout of `A` and the coproduct of the `B k` along the parts
`S k` where they meet `A`. This recognizes a space built by attaching finitely many closed pieces,
such as cells or handles, without passing through a quotient. Without the covering hypothesis, a
map out of such a pushout which restricts to closed embeddings on `A` and on finitely many pieces
`B k`, any two of which meet only inside `A`, and meeting `A` only along the `S k`, is still a
closed embedding.

## Main declarations

* `CategoryTheory.IsPushout.continuousMap_ext`: continuous maps out of a pushout agree when they
  agree on both legs.
* `CategoryTheory.IsPushout.cylinderDesc`: the map out of the cylinder `I × P` glued from
  compatible maps out of `I × Y` and `I × Z`.
* `CategoryTheory.IsPushout.homotopyDesc`: the homotopy between maps out of `P` glued from
  compatible homotopies of their restrictions to `Y` and to `Z`.
* `TopCat.sigmaCylinderDesc`: the map out of the cylinder `I × ∐ⱼ F j` glued from maps out of the
  cylinders `I × F j`.
* `TopCat.exists_glue_of_isClosedEmbedding`: maps out of the pieces of a finite closed cover which
  agree on the overlaps glue to a map out of the whole space.
* `CategoryTheory.IsPushout.of_isClosedEmbedding`: a cover by a closed subspace and finitely many
  closed pieces meeting it along prescribed subspaces is a pushout square.
* `TauCeti.TopCat.range_union_iUnion_range_of_isPushout_sigma`,
  `TauCeti.TopCat.exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma`: every point of a pushout of
  `L` and `⨆ᵢ D i` comes from `L` or from one of the `D i`.
* `TauCeti.TopCat.injective_of_isPushout_sigma_of_comp`,
  `TauCeti.TopCat.isClosedEmbedding_of_isPushout_sigma_of_comp`: a map out of the pushout of `L` and
  `⨆ᵢ D i` along `⨆ᵢ A i` restricting to injective maps (resp. closed embeddings) on `L` and on
  the `D i`, with the images of any two `D i` meeting only inside the image of `L` and each
  meeting it only along `A i`, is injective (resp. a closed embedding).
-/

public section

noncomputable section

open unitInterval ContinuousMap

namespace CategoryTheory.IsPushout

universe u

variable {B Y Z P : TopCat.{u}} {i : B ⟶ Y} {a : B ⟶ Z} {j : Y ⟶ P} {k : Z ⟶ P}
  {W : Type u} [TopologicalSpace W]

/-- The pointwise form of the commutativity of a pushout square in `TopCat`. -/
theorem w_apply (h : IsPushout i a j k) (b : B) : j (i b) = k (a b) := by
  simpa using ConcreteCategory.congr_hom h.w b

/-- Two continuous maps out of a pushout in `TopCat` agree as soon as they agree on both legs. -/
theorem continuousMap_ext (h : IsPushout i a j k) {f g : C(P, W)}
    (hj : ∀ y, f (j y) = g (j y)) (hk : ∀ z, f (k z) = g (k z)) : f = g := by
  have : TopCat.ofHom (X := P) (Y := TopCat.of W) f = TopCat.ofHom g :=
    h.hom_ext (by ext y; exact hj y) (by ext z; exact hk z)
  exact congrArg TopCat.Hom.hom this

/-- The map `P → C(I, W)` glued from the curried maps `F` and `G`. -/
private def cylinderCurry (h : IsPushout i a j k) (F : C(I × Y, W)) (G : C(I × Z, W))
    (hFG : ∀ t b, F (t, i b) = G (t, a b)) : P ⟶ TopCat.of C(I, W) :=
  h.desc (TopCat.ofHom (F.comp ContinuousMap.prodSwap).curry)
    (TopCat.ofHom (G.comp ContinuousMap.prodSwap).curry) (by ext b t; exact hFG t b)

/-- The map out of the cylinder `I × P` on a pushout `P = Z ∪_a Y` glued from maps
`F : I × Y → W` and `G : I × Z → W` which agree along the attaching map. Since `I` is locally
compact, it is the uncurried map out of `P` glued from the curried maps into `C(I, W)`; this is the
form in which homotopies are glued on `P`. -/
def cylinderDesc (h : IsPushout i a j k) (F : C(I × Y, W)) (G : C(I × Z, W))
    (hFG : ∀ t b, F (t, i b) = G (t, a b)) : C(I × P, W) :=
  (h.cylinderCurry F G hFG).hom.uncurry.comp ContinuousMap.prodSwap

variable (h : IsPushout i a j k) (F : C(I × Y, W)) (G : C(I × Z, W))
  (hFG : ∀ t b, F (t, i b) = G (t, a b))

/-- On the cylinder over `Y`, the glued map `CategoryTheory.IsPushout.cylinderDesc` is `F`. -/
@[simp]
theorem cylinderDesc_inl (t : I) (y : Y) : h.cylinderDesc F G hFG (t, j y) = F (t, y) := by
  have hy : h.cylinderCurry F G hFG (j y) = (F.comp ContinuousMap.prodSwap).curry y :=
    ConcreteCategory.congr_hom (h.inl_desc _ _ _) y
  exact congrArg (fun g : C(I, W) ↦ g t) hy

/-- On the cylinder over `Z`, the glued map `CategoryTheory.IsPushout.cylinderDesc` is `G`. -/
@[simp]
theorem cylinderDesc_inr (t : I) (z : Z) : h.cylinderDesc F G hFG (t, k z) = G (t, z) := by
  have hz : h.cylinderCurry F G hFG (k z) = (G.comp ContinuousMap.prodSwap).curry z :=
    ConcreteCategory.congr_hom (h.inr_desc _ _ _) z
  exact congrArg (fun g : C(I, W) ↦ g t) hz

/-- A slice of the glued map `CategoryTheory.IsPushout.cylinderDesc` is the map out of `P` which
agrees with the corresponding slices of `F` and `G` on both legs. -/
theorem cylinderDesc_apply_eq (t : I) {w : C(P, W)} (hY : ∀ y, F (t, y) = w (j y))
    (hZ : ∀ z, G (t, z) = w (k z)) (p : P) : h.cylinderDesc F G hFG (t, p) = w p :=
  congrArg (fun g : C(P, W) ↦ g p)
    (h.continuousMap_ext (f := ⟨fun p ↦ h.cylinderDesc F G hFG (t, p), by fun_prop⟩)
      (fun y ↦ by simpa using hY y) (fun z ↦ by simpa using hZ z))

omit hFG in
/-- The homotopy between two maps out of a pushout `P = Z ∪_a Y` glued from homotopies of their
restrictions to `Y` and to `Z` which agree along the attaching map. -/
def homotopyDesc {f g : C(P, W)} (HY : (f.comp j.hom).Homotopy (g.comp j.hom))
    (HZ : (f.comp k.hom).Homotopy (g.comp k.hom)) (hYZ : ∀ t b, HY (t, i b) = HZ (t, a b)) :
    f.Homotopy g where
  toContinuousMap := h.cylinderDesc HY.toContinuousMap HZ.toContinuousMap hYZ
  map_zero_left := h.cylinderDesc_apply_eq _ _ hYZ 0 (by simp) (by simp)
  map_one_left := h.cylinderDesc_apply_eq _ _ hYZ 1 (by simp) (by simp)

omit hFG in
/-- On `Y`, the glued homotopy `CategoryTheory.IsPushout.homotopyDesc` is `HY`. -/
@[simp]
theorem homotopyDesc_apply_inl {f g : C(P, W)} (HY : (f.comp j.hom).Homotopy (g.comp j.hom))
    (HZ : (f.comp k.hom).Homotopy (g.comp k.hom)) (hYZ : ∀ t b, HY (t, i b) = HZ (t, a b))
    (t : I) (y : Y) : h.homotopyDesc HY HZ hYZ (t, j y) = HY (t, y) :=
  h.cylinderDesc_inl _ _ hYZ t y

omit hFG in
/-- On `Z`, the glued homotopy `CategoryTheory.IsPushout.homotopyDesc` is `HZ`. -/
@[simp]
theorem homotopyDesc_apply_inr {f g : C(P, W)} (HY : (f.comp j.hom).Homotopy (g.comp j.hom))
    (HZ : (f.comp k.hom).Homotopy (g.comp k.hom)) (hYZ : ∀ t b, HY (t, i b) = HZ (t, a b))
    (t : I) (z : Z) : h.homotopyDesc HY HZ hYZ (t, k z) = HZ (t, z) :=
  h.cylinderDesc_inr _ _ hYZ t z

end CategoryTheory.IsPushout

namespace TopCat

open CategoryTheory Set Topology

universe u

section Sigma

open Limits

variable {J : Type u} (F : J → TopCat.{u})

/-- Every point of a coproduct in `TopCat` lies in the image of one of the coprojections. -/
theorem exists_sigma_ι_eq (z : (∐ F : TopCat.{u})) : ∃ j x, Sigma.ι F j x = z :=
  let ⟨⟨j⟩, x, hx⟩ := Concrete.colimit_exists_rep _ z; ⟨j, x, hx⟩

variable {W : Type u} [TopologicalSpace W] {F}

/-- The map `I × ∐ⱼ F j → W` which is `C j` on the cylinder `I × F j`: the uncurried form of the
map `∐ⱼ F j → C(I, W)` glued from the curried maps. -/
def sigmaCylinderDesc (C : ∀ j, C(I × F j, W)) : C(I × (∐ F : TopCat.{u}), W) :=
  (Sigma.desc fun j ↦ TopCat.ofHom ((C j).comp ContinuousMap.prodSwap).curry :
    (∐ F) ⟶ TopCat.of C(I, W)).hom.uncurry.comp ContinuousMap.prodSwap

@[simp]
theorem sigmaCylinderDesc_ι (C : ∀ j, C(I × F j, W)) (t : I) (j : J) (x : F j) :
    sigmaCylinderDesc C (t, Sigma.ι F j x) = C j (t, x) := by
  have hx := ConcreteCategory.congr_hom
    (Sigma.ι_comp_desc (fun j ↦ TopCat.ofHom ((C j).comp ContinuousMap.prodSwap).curry :
      ∀ j, F j ⟶ TopCat.of C(I, W)) j) x
  exact congrArg (fun g : C(I, W) ↦ g t) hx

end Sigma

/-- **Gluing along a finite closed cover.** Let `X` be covered by the ranges of a closed embedding
`i : A ⟶ X` and of finitely many closed embeddings `j k : B k ⟶ X`, any two of which meet only
inside the range of `i`. Maps `a : A ⟶ Y` and `b k : B k ⟶ Y` which agree wherever `i` meets
`j k` glue to a map `X ⟶ Y` restricting to `a` along `i` and to `b k` along `j k`. -/
theorem exists_glue_of_isClosedEmbedding {ι : Type*} [Finite ι] {A X Y : TopCat.{u}}
    {B : ι → TopCat.{u}} {i : A ⟶ X} {j : ∀ k, B k ⟶ X} (hi : IsClosedEmbedding i)
    (hj : ∀ k, IsClosedEmbedding (j k)) (hcover : range i ∪ ⋃ k, range (j k) = univ)
    (hjj : Pairwise fun k l ↦ range (j k) ∩ range (j l) ⊆ range i) (a : A ⟶ Y)
    (b : ∀ k, B k ⟶ Y) (hab : ∀ k x y, i x = j k y → a x = b k y) :
    ∃ d : X ⟶ Y, i ≫ d = a ∧ ∀ k, j k ≫ d = b k := by
  classical
  have hc (x : X) (hx : x ∉ range i) : ∃ p : Σ k, B k, j p.1 p.2 = x := by
    obtain hx' | hx' := hcover.symm ▸ mem_univ x
    · exact absurd hx' hx
    · obtain ⟨k, b, rfl⟩ := mem_iUnion.1 hx'
      exact ⟨⟨k, b⟩, rfl⟩
  -- Read a point on the range of `i` when it lies there, and on the range of some `j k` otherwise.
  let F : X → Y := fun x ↦
    if h : x ∈ range i then a h.choose else b (hc x h).choose.1 (hc x h).choose.2
  have hFi (x : A) : F (i x) = a x := by
    have h : i x ∈ range i := mem_range_self x
    simp only [F, h, ↓reduceDIte]
    exact congrArg a (hi.injective h.choose_spec)
  have hFj (k : ι) (y : B k) : F (j k y) = b k y := by
    by_cases h : j k y ∈ range i
    · simp only [F, h, ↓reduceDIte]
      exact hab k _ y h.choose_spec
    · simp only [F, h, ↓reduceDIte]
      have hspec := (hc _ h).choose_spec
      generalize (hc _ h).choose = p at hspec ⊢
      obtain ⟨l, z⟩ := p
      obtain rfl : l = k := by
        by_contra hlk
        exact h (hjj hlk ⟨⟨z, hspec⟩, ⟨y, rfl⟩⟩)
      rw [(hj l).injective hspec]
  have hF : Continuous F := by
    have h₁ : ContinuousOn F (range i) := by
      rw [← image_univ, hi.isInducing.continuousOn_image_iff]
      exact ((continuous_congr hFi).2 a.hom.continuous).continuousOn
    have h₂ : ContinuousOn F (⋃ k, range (j k)) :=
      (locallyFinite_of_finite _).continuousOn_iUnion (fun k ↦ (hj k).isClosed_range) fun k ↦ by
        rw [← image_univ, (hj k).isInducing.continuousOn_image_iff]
        exact ((continuous_congr (hFj k)).2 (b k).hom.continuous).continuousOn
    rw [← continuousOn_univ, ← hcover]
    exact h₁.union_of_isClosed h₂ hi.isClosed_range
      (isClosed_iUnion_of_finite fun k ↦ (hj k).isClosed_range)
  exact ⟨TopCat.ofHom ⟨F, hF⟩, by ext x; exact hFi x, fun k ↦ by ext y; exact hFj k y⟩

end TopCat

namespace CategoryTheory.IsPushout

section ClosedCover

open Set Topology Limits

universe u

variable {ι : Type u} [Finite ι] {S B : ι → TopCat.{u}} {A X : TopCat.{u}} {g : ∀ k, S k ⟶ A}
  {m : ∀ k, S k ⟶ B k} {i : A ⟶ X} {j : ∀ k, B k ⟶ X}

/-- **A finite closed cover is a pushout.** Let `X` be covered by the ranges of a closed embedding
`i : A ⟶ X` and of finitely many closed embeddings `j k : B k ⟶ X`, any two of which meet only
inside the range of `i`. Suppose that `i` meets each `j k` exactly along `S k`: the squares
`g k ≫ i = m k ≫ j k` commute, and every point `i a = j k b` comes from a point `s` of `S k` with
`g k s = a` and `m k s = b`. Then `X` is the pushout of `A` and `∐ₖ B k` along `∐ₖ S k`.

For instance, a space which is the union of a closed subspace and finitely many disjoint closed
handles, each meeting the subspace in its attaching region, is obtained by attaching the
handles. -/
theorem of_isClosedEmbedding (w : ∀ k, g k ≫ i = m k ≫ j k) (hi : IsClosedEmbedding i)
    (hj : ∀ k, IsClosedEmbedding (j k)) (hcover : range i ∪ ⋃ k, range (j k) = univ)
    (hjj : Pairwise fun k l ↦ range (j k) ∩ range (j l) ⊆ range i)
    (hij : ∀ k a b, i a = j k b → ∃ s, g k s = a ∧ m k s = b) :
    IsPushout (Sigma.desc g) (Limits.Sigma.map m) i (Sigma.desc j) := by
  have w' : Sigma.desc g ≫ i = Limits.Sigma.map m ≫ Sigma.desc j :=
    Sigma.hom_ext _ _ fun k ↦ by simp [w k]
  -- A pushout cocone restricts to compatible maps on `A` and on the pieces `B k`.
  have hs (s : PushoutCocone (Sigma.desc g) (Limits.Sigma.map m)) (k : ι) :
      g k ≫ s.inl = m k ≫ Sigma.ι B k ≫ s.inr := by
    simpa using Sigma.ι S k ≫= s.condition
  let desc (s : PushoutCocone (Sigma.desc g) (Limits.Sigma.map m)) :=
    TopCat.exists_glue_of_isClosedEmbedding hi hj hcover hjj s.inl (fun k ↦ Sigma.ι B k ≫ s.inr)
      fun k x y h ↦ by
        obtain ⟨t, rfl, rfl⟩ := hij k x y h
        exact ConcreteCategory.congr_hom (hs s k) t
  refine IsPushout.of_isColimit' ⟨w'⟩ (PushoutCocone.IsColimit.mk w' (fun s ↦ (desc s).choose)
    (fun s ↦ (desc s).choose_spec.1) (fun s ↦ Sigma.hom_ext _ _ fun k ↦ ?_) fun s d h₁ h₂ ↦ ?_)
  · rw [Sigma.ι_comp_desc_assoc]
    exact (desc s).choose_spec.2 k
  · ext x
    obtain ⟨a, rfl⟩ | hx := hcover.symm ▸ mem_univ x
    · rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, h₁,
        (desc s).choose_spec.1]
    · obtain ⟨k, y, rfl⟩ := mem_iUnion.1 hx
      have hk := Sigma.ι B k ≫= h₂
      rw [Sigma.ι_comp_desc_assoc] at hk
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hk,
        (desc s).choose_spec.2 k]

end ClosedCover

end CategoryTheory.IsPushout

namespace TauCeti.TopCat

section PushoutSigma

open CategoryTheory Limits Topology

universe u

variable {ι : Type u} {A D : ι → TopCat.{u}} {L X P : TopCat.{u}} {α : ∀ i, A i ⟶ L}
  {j : ∀ i, A i ⟶ D i} {g : L ⟶ X} {χ : ∀ i, D i ⟶ X} {inl : L ⟶ P} {inr : (∐ D) ⟶ P}
  {φ : P ⟶ X}

/-- Every point of a pushout of `L` and `⨆ᵢ D i` comes from `L` or from one of the `D i`. -/
theorem range_union_iUnion_range_of_isPushout_sigma {W : TopCat.{u}} {f : W ⟶ L} {h : W ⟶ ∐ D}
    (sq : IsPushout f h inl inr) :
    Set.range inl ∪ ⋃ i, Set.range (Sigma.ι D i ≫ inr) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ?_
  obtain ⟨x, hx⟩ | ⟨z, rfl⟩ := Types.eq_or_eq_of_isPushout ((forget TopCat).map_isPushout sq) y
  · exact Or.inl ⟨x, hx⟩
  · obtain ⟨⟨i⟩, d, rfl⟩ := Concrete.colimit_exists_rep (Discrete.functor D) z
    exact Or.inr (Set.mem_iUnion.2 ⟨i, d, rfl⟩)

/-- Every point of a pushout of `L` and `⨆ᵢ D i` is the image of a point of `L` or of one of the
`D i`. This is the pointwise form of
`TauCeti.TopCat.range_union_iUnion_range_of_isPushout_sigma`. -/
theorem exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma {W : TopCat.{u}} {f : W ⟶ L}
    {h : W ⟶ ∐ D} (sq : IsPushout f h inl inr) (y : P) :
    (∃ x, inl x = y) ∨ ∃ i d, inr (Sigma.ι D i d) = y := by
  rcases (range_union_iUnion_range_of_isPushout_sigma sq).symm ▸ Set.mem_univ y with hy | hy
  · exact Or.inl hy
  · obtain ⟨i, d, rfl⟩ := Set.mem_iUnion.1 hy
    exact Or.inr ⟨i, d, rfl⟩

/-- Let `P` be the pushout of `L` and `⨆ᵢ D i` along `⨆ᵢ A i`, and let `φ : P ⟶ X` restrict to
injective maps `g` on `L` and `χ i` on the `D i`, with the ranges of any two `χ i` meeting only
inside the range of `g`. If every point of `D i` carried by `χ i` into the range of `g` lies in the
range of `j i`, then `φ` is injective. -/
theorem injective_of_isPushout_sigma_of_comp (hg : Function.Injective g)
    (hχ : ∀ i, Function.Injective (χ i))
    (hχχ : Pairwise fun i i' ↦ Set.range (χ i) ∩ Set.range (χ i') ⊆ Set.range g)
    (hmeet : ∀ i d, χ i d ∈ Set.range g → d ∈ Set.range (j i))
    (sq : IsPushout (Sigma.desc α) (Limits.Sigma.map j) inl inr) (hinl : inl ≫ φ = g)
    (hinr : ∀ i, Sigma.ι D i ≫ inr ≫ φ = χ i) : Function.Injective φ := by
  have hinl' (x : L) : φ (inl x) = g x := by rw [← hinl, ConcreteCategory.comp_apply]
  have hinr' (i : ι) (d : D i) : φ (inr (Sigma.ι D i d)) = χ i d := by
    rw [← hinr, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  -- A point of `L` and a point of `D i` with the same image in `X` are identified in the pushout.
  have hglue (x : L) (i : ι) (d : D i) (h : g x = χ i d) : inl x = inr (Sigma.ι D i d) := by
    obtain ⟨a, rfl⟩ := hmeet i d ⟨x, h⟩
    have hsq : inl (α i a) = inr (Sigma.ι D i (j i a)) := by
      simpa [Sigma.ι_map_apply] using ConcreteCategory.congr_hom sq.w (Sigma.ι A i a)
    have ha : g (α i a) = g x := by rw [← hinl', hsq, hinr', h]
    rwa [← hg ha]
  intro a b hab
  rcases exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma sq a with ⟨x, rfl⟩ | ⟨i, d, rfl⟩ <;>
    rcases exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma sq b with
      ⟨x', rfl⟩ | ⟨i', d', rfl⟩
  · rw [hinl', hinl'] at hab
    rw [hg hab]
  · rw [hinl', hinr'] at hab
    exact hglue x i' d' hab
  · rw [hinl', hinr'] at hab
    exact (hglue x' i d hab.symm).symm
  · rw [hinr', hinr'] at hab
    rcases eq_or_ne i i' with rfl | hii'
    · rw [hχ i hab]
    -- Points of two different cells with the same image lie over a common point of `L`.
    obtain ⟨x, hx⟩ := hχχ hii' ⟨⟨d, rfl⟩, d', hab.symm⟩
    exact (hglue x i d hx).symm.trans (hglue x i' d' (hx.trans hab))

/-- Let `P` be the pushout of `L` and `⨆ᵢ D i` along `⨆ᵢ A i`, for finitely many `i`, and let
`φ : P ⟶ X` restrict to closed embeddings `g` on `L` and `χ i` on the `D i`, with the ranges of
any two `χ i` meeting only inside the range of `g`. If every point of `D i` carried by `χ i` into
the range of `g` lies in the range of `j i`, then `φ` is a closed embedding. -/
theorem isClosedEmbedding_of_isPushout_sigma_of_comp [Finite ι] (hg : IsClosedEmbedding g)
    (hχ : ∀ i, IsClosedEmbedding (χ i))
    (hχχ : Pairwise fun i i' ↦ Set.range (χ i) ∩ Set.range (χ i') ⊆ Set.range g)
    (hmeet : ∀ i d, χ i d ∈ Set.range g → d ∈ Set.range (j i))
    (sq : IsPushout (Sigma.desc α) (Limits.Sigma.map j) inl inr) (hinl : inl ≫ φ = g)
    (hinr : ∀ i, Sigma.ι D i ≫ inr ≫ φ = χ i) : IsClosedEmbedding φ := by
  have hinl' (x : L) : φ (inl x) = g x := by rw [← hinl, ConcreteCategory.comp_apply]
  have hinr' (i : ι) (d : D i) : φ (inr (Sigma.ι D i d)) = χ i d := by
    rw [← hinr, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine .of_continuous_injective_isClosedMap φ.hom.continuous
    (injective_of_isPushout_sigma_of_comp hg.injective (fun i ↦ (hχ i).injective) hχχ hmeet sq
      hinl hinr)
    fun C hC ↦ ?_
  -- A closed set of the pushout is carried onto the union of the images of its finitely many
  -- pieces in `L` and in the `D i`, each closed in `X`.
  have hC' : φ '' C = g '' (inl ⁻¹' C) ∪ ⋃ i, χ i '' ((inr ∘ Sigma.ι D i) ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases exists_eq_inl_or_exists_eq_inr_of_isPushout_sigma sq z with
        ⟨x, rfl⟩ | ⟨i, d, rfl⟩
      · exact Or.inl ⟨x, hz, (hinl' x).symm⟩
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, d, hz, (hinr' i d).symm⟩)
    · rintro (⟨x, hx, rfl⟩ | hy)
      · exact ⟨inl x, hx, hinl' x⟩
      · obtain ⟨i, d, hd, rfl⟩ := Set.mem_iUnion.1 hy
        exact ⟨inr (Sigma.ι D i d), hd, hinr' i d⟩
  rw [hC']
  exact (hg.isClosedMap _ (hC.preimage inl.hom.continuous)).union
    (isClosed_iUnion_of_finite fun i ↦ (hχ i).isClosedMap _
      (hC.preimage (inr.hom.continuous.comp (Sigma.ι D i).hom.continuous)))

end PushoutSigma

end TauCeti.TopCat
