/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homotopy.Basic
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
such as cells or handles, without passing through a quotient.

## Main declarations

* `CategoryTheory.IsPushout.continuousMap_ext`: continuous maps out of a pushout agree when they
  agree on both legs.
* `CategoryTheory.IsPushout.cylinderDesc`: the map out of the cylinder `I × P` glued from
  compatible maps out of `I × Y` and `I × Z`.
* `CategoryTheory.IsPushout.homotopyDesc`: the homotopy between maps out of `P` glued from
  compatible homotopies of their restrictions to `Y` and to `Z`.
* `TopCat.exists_glue_of_isClosedEmbedding`: maps out of the pieces of a finite closed cover which
  agree on the overlaps glue to a map out of the whole space.
* `CategoryTheory.IsPushout.of_isClosedEmbedding`: a cover by a closed subspace and finitely many
  closed pieces meeting it along prescribed subspaces is a pushout square.
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
