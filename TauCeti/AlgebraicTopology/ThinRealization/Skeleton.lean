/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import TauCeti.AlgebraicTopology.SimplicialObject.TopCat
public import TauCeti.AlgebraicTopology.ThinRealization.Basic
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.Lindelof
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.Category.TopCat.Paracompact
public import TauCeti.Topology.Compactness.Paracompact

/-!
# Skeletal filtration and paracompactness of thin geometric realizations

For a simplicial space `X : SimplicialObject TopCat`, the `k`-skeleton
`TauCeti.thinRealization.skeleton X k` is the quotient of `Σ m : Fin (k + 1), Xₘ × Δᵐ` by all
simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` among degrees `≤ k`. The zero-skeleton is
canonically homeomorphic to `X₀` (`skeletonZeroHomeomorph`), and the skeleta assemble into a
sequential diagram `skeletonFunctor X : ℕ ⥤ TopCat` whose colimit is `thinRealization X`
(`isColimitSkeletonCocone`).

In passing from `skeleton X k` to `skeleton X (k + 1)`, the cell `Xₖ₊₁ × Δᵏ⁺¹` is attached along
`attachingSet X k`, the union of `⋃ i, range (X.σ i) ×ˢ univ` (degenerate simplices) and
`⋃ j, univ ×ˢ range (toTop.map (δ j))` (the boundary `∂Δᵏ⁺¹`). Whenever each degeneracy image
`range (X.σ i)` is closed—in particular whenever `Xₖ₊₁` is Hausdorff
(`CategoryTheory.SimplicialObject.isClosedEmbedding_σ`)—this attaching locus is closed in
`Xₖ₊₁ × Δᵏ⁺¹`, the gluing map `attachingMap X k` is continuous, and `skeleton X (k + 1)` is the
pushout of `skeleton X k` and `Xₖ₊₁ × Δᵏ⁺¹` along `attachingSet X k` (`isPushout_skeleton_succ`).
Consequently each skeletal transition map and each inclusion `skeleton X k ⟶ thinRealization X` is
a closed embedding.

Combining the skeletal pushout and sequential colimit normality theorems from
`TauCeti.Topology.Category.TopCat.Normal` with the product and paracompactness theorems from
`TauCeti.Topology.Compactness.Lindelof` and `TauCeti.Topology.Compactness.Paracompact` shows that
whenever every `Xₙ × Δⁿ` is `T₄` (`t4Space_of_prod`)—and in particular as an instance whenever
every level `Xₙ` is `T₃` and Lindelöf (`instT4Space`)—`thinRealization X` is `T₄` (normal and
Hausdorff) and paracompact in its quotient topology.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics **271**, Section
  11.
-/

public noncomputable section

open CategoryTheory Convexity Limits Opposite Set Topology
open scoped Simplicial

universe u

namespace TauCeti.thinRealization

variable (X : SimplicialObject TopCat.{u})

/-- Simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` restricted to degrees `≤ k`. -/
private inductive SkeletonRel (k : ℕ) :
    (Σ m : Fin (k + 1), X _⦋(m : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) →
      (Σ m : Fin (k + 1), X _⦋(m : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) → Prop where
  | mk ⦃m n : Fin (k + 1)⦄ (f : ⦋(m : ℕ)⦌ ⟶ ⦋(n : ℕ)⦌) (x : X _⦋(n : ℕ)⦌)
      (t : SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) :
      SkeletonRel k ⟨m, X.map f.op x, t⟩ ⟨n, x, SimplexCategory.toTop.map f t⟩

/-- The `k`-skeleton of the thin realization of `X`: the quotient of `Σ m ≤ k, Xₘ × Δᵐ` by all
simplicial operators between degrees at most `k`. -/
def skeleton (k : ℕ) : TopCat.{u} :=
  TopCat.of (Quot (SkeletonRel X k))

namespace skeleton

/-- The characteristic map `Xₘ × Δᵐ → skeleton X k` in degree `m ≤ k`. -/
def ι (k : ℕ) (m : Fin (k + 1)) :
    C(X _⦋(m : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌, skeleton X k) :=
  ⟨fun p ↦ Quot.mk (SkeletonRel X k) ⟨m, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The skeletal characteristic maps respect all simplicial operators among degrees `≤ k`. -/
@[simp]
theorem ι_map (k : ℕ) {m n : Fin (k + 1)} (f : ⦋(m : ℕ)⦌ ⟶ ⦋(n : ℕ)⦌) (x : X _⦋(n : ℕ)⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) :
    ι X k m (X.map f.op x, t) = ι X k n (x, SimplexCategory.toTop.map f t) :=
  Quot.sound (SkeletonRel.mk f x t)

/-- Every point of the `k`-skeleton lies in the image of a characteristic map in degree `≤ k`. -/
theorem ι_jointly_surjective (k : ℕ) (p : skeleton X k) : ∃ m x t, ι X k m (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- The `k`-skeleton carries the quotient topology from `Σ m : Fin (k + 1), Xₘ × Δᵐ`. -/
theorem isQuotientMap_sigma (k : ℕ) :
    IsQuotientMap fun p :
        Σ m : Fin (k + 1), X _⦋(m : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌ ↦
      ι X k p.1 p.2 :=
  isQuotientMap_quot_mk

/-- Two morphisms out of `skeleton X k` agree when they agree on every characteristic map. -/
@[ext]
theorem hom_ext {k : ℕ} {Z : TopCat} {g h : skeleton X k ⟶ Z}
    (H : ∀ (m : Fin (k + 1)) x t, g (ι X k m (x, t)) = h (ι X k m (x, t))) : g = h := by
  ext p
  obtain ⟨m, x, t, rfl⟩ := ι_jointly_surjective X k p
  exact H m x t

section Desc

variable {X} {k : ℕ} {Z : Type*} [TopologicalSpace Z]
  (g : ∀ m : Fin (k + 1), C(X _⦋(m : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌, Z))
  (hg : ∀ ⦃m n : Fin (k + 1)⦄ (f : ⦋(m : ℕ)⦌ ⟶ ⦋(n : ℕ)⦌) (x : X _⦋(n : ℕ)⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌),
    g m (X.map f.op x, t) = g n (x, SimplexCategory.toTop.map f t))

/-- Universal property of `skeleton X k`: continuous maps `Xₘ × Δᵐ → Z` for `m ≤ k` compatible
with all simplicial operators among degrees `≤ k` descend to `skeleton X k → Z`. -/
def desc : C(skeleton X k, Z) where
  toFun := Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun m ↦ (g m).continuous)

@[simp]
theorem desc_ι (m : Fin (k + 1))
    (p : X _⦋(m : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) :
    desc g hg (ι X k m p) = g m p :=
  (rfl)

end Desc

/-- If every level `Xₙ` is Lindelöf, every skeleton `skeleton X k` is Lindelöf. -/
instance instLindelofSpace [∀ n : ℕ, LindelofSpace (X _⦋n⦌)] (k : ℕ) :
    LindelofSpace (skeleton X k) :=
  inferInstanceAs (LindelofSpace (Quot (SkeletonRel X k)))

end skeleton

/-- The zero-skeleton `skeleton X 0` is canonically homeomorphic to `X₀`. -/
def skeletonZeroHomeomorph : skeleton X 0 ≃ₜ X _⦋0⦌ where
  toFun := skeleton.desc
    (fun m ↦ (X.map (eqToHom (by simp [Fin.eq_zero m]))).hom.comp ContinuousMap.fst) <| by
      intro m n f x t
      obtain rfl := Fin.eq_zero m
      obtain rfl := Fin.eq_zero n
      rw [SimplexCategory.hom_zero_zero f]
      exact congrArg (X.map _) (ConcreteCategory.congr_hom (X.map_id _) x)
  invFun x := skeleton.ι X 0 0 (x, SimplexCategory.toTopInitialVertex ⦋0⦌)
  left_inv p := by
    obtain ⟨m, x, t, rfl⟩ := skeleton.ι_jointly_surjective X 0 p
    obtain rfl := Fin.eq_zero m
    have ht : t = SimplexCategory.toTopInitialVertex ⦋0⦌ :=
      ULift.ext (Subsingleton.elim (α := StdSimplex ℝ (Fin 1)) t.down _)
    rw [ht, skeleton.desc_ι]
    simp
  right_inv x := by
    rw [skeleton.desc_ι]
    simp
  continuous_toFun := ContinuousMap.continuous _
  continuous_invFun := (skeleton.ι X 0 0).continuous.comp (continuous_id.prodMk continuous_const)

/-- The isomorphism `skeleton X 0 ≅ X₀` in `TopCat`. -/
def skeletonZeroIso : skeleton X 0 ≅ X _⦋0⦌ :=
  TopCat.isoOfHomeo (skeletonZeroHomeomorph X)

/-- The sequential skeletal filtration `ℕ ⥤ TopCat` of `thinRealization X`. -/
@[expose]
def skeletonFunctor (X : SimplicialObject TopCat.{u}) : ℕ ⥤ TopCat.{u} where
  obj := skeleton X
  map {k l} h := TopCat.ofHom <| skeleton.desc
    (fun m ↦ skeleton.ι X l (Fin.castLE (Nat.add_le_add_right (leOfHom h) 1) m))
    (fun m n f x t ↦ skeleton.ι_map X l
      (m := Fin.castLE (Nat.add_le_add_right (leOfHom h) 1) m)
      (n := Fin.castLE (Nat.add_le_add_right (leOfHom h) 1) n) f x t)
  map_id _ := by apply skeleton.hom_ext; intro m x t; rfl
  map_comp _ _ := by apply skeleton.hom_ext; intro m x t; rfl

@[simp]
theorem skeletonFunctor_map_ι {k l : ℕ} (h : k ≤ l) (m : Fin (k + 1)) (x : X _⦋(m : ℕ)⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) :
    (skeletonFunctor X).map (homOfLE h) (skeleton.ι X k m (x, t)) =
      skeleton.ι X l (Fin.castLE (Nat.add_le_add_right h 1) m) (x, t) :=
  (rfl)

/-- The canonical cocone exhibiting `thinRealization X` over `skeletonFunctor X`. -/
@[expose]
def skeletonCocone : Cocone (skeletonFunctor X) where
  pt := thinRealization X
  ι :=
    { app k := TopCat.ofHom <| skeleton.desc
        (fun m ↦ ι X ⦋(m : ℕ)⦌) (fun _ _ f x t ↦ ι_map X f x t)
      naturality _ _ _ := by apply skeleton.hom_ext; intro m x t; rfl }

/-- Evaluation of the `k`-th leg of `skeletonCocone X` on a skeletal representative. -/
theorem skeletonCocone_ι_app_ι (k : ℕ) (m : Fin (k + 1)) (x : X _⦋(m : ℕ)⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) :
    (skeletonCocone X).ι.app k (skeleton.ι X k m (x, t)) = ι X ⦋(m : ℕ)⦌ (x, t) :=
  (rfl)

/-- `thinRealization X` is the colimit of its skeletal filtration `skeletonFunctor X` in
`TopCat`. -/
def isColimitSkeletonCocone : IsColimit (skeletonCocone X) where
  desc s := TopCat.ofHom <| desc
    (fun n ↦ (s.ι.app n.len).hom.comp (skeleton.ι X n.len (Fin.last n.len))) <| by
      intro m n f x t
      let N := max m.len n.len
      have hm : s.ι.app N (skeleton.ι X N ⟨m.len, Nat.lt_succ_of_le (le_max_left _ _)⟩
          (X.map f.op x, t)) =
          s.ι.app m.len (skeleton.ι X m.len (Fin.last m.len) (X.map f.op x, t)) :=
        ConcreteCategory.congr_hom (s.w (homOfLE (le_max_left m.len n.len)))
          (skeleton.ι X m.len (Fin.last m.len) (X.map f.op x, t))
      have hn : s.ι.app N (skeleton.ι X N ⟨n.len, Nat.lt_succ_of_le (le_max_right _ _)⟩
          (x, SimplexCategory.toTop.map f t)) =
          s.ι.app n.len (skeleton.ι X n.len (Fin.last n.len)
            (x, SimplexCategory.toTop.map f t)) :=
        ConcreteCategory.congr_hom (s.w (homOfLE (le_max_right m.len n.len)))
          (skeleton.ι X n.len (Fin.last n.len) (x, SimplexCategory.toTop.map f t))
      exact hm.symm.trans ((congrArg (s.ι.app N)
        (skeleton.ι_map X N (m := ⟨m.len, Nat.lt_succ_of_le (le_max_left _ _)⟩)
          (n := ⟨n.len, Nat.lt_succ_of_le (le_max_right _ _)⟩) f x t)).trans hn)
  fac s k := by
    apply skeleton.hom_ext
    rintro ⟨m, hm⟩ x t
    change desc
      (fun n ↦ (s.ι.app n.len).hom.comp (skeleton.ι X n.len (Fin.last n.len))) _
      (ι X ⦋m⦌ (x, t)) = s.ι.app k (skeleton.ι X k ⟨m, hm⟩ (x, t))
    rw [desc_ι]
    exact (ConcreteCategory.congr_hom (s.w (homOfLE (Nat.le_of_lt_succ hm)))
      (skeleton.ι X m (Fin.last m) (x, t))).symm
  uniq s g hg := by
    apply hom_ext
    intro n x t
    have hgn : g (ι X n (x, t)) = s.ι.app n.len (skeleton.ι X n.len (Fin.last n.len) (x, t)) :=
      ConcreteCategory.congr_hom (hg n.len) (skeleton.ι X n.len (Fin.last n.len) (x, t))
    change g (ι X n (x, t)) = desc
      (fun n ↦ (s.ι.app n.len).hom.comp (skeleton.ι X n.len (Fin.last n.len))) _
      (ι X n (x, t))
    rw [desc_ι]
    exact hgn

section Attaching

/-- The attaching subspace in `Xₖ₊₁ × Δᵏ⁺¹` consisting of pairs with a degenerate simplex or a
boundary point of `Δᵏ⁺¹`. -/
def attachingSet (k : ℕ) :
    Set (X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :=
  (⋃ i : Fin (k + 1), range (X.σ i) ×ˢ univ) ∪
    (⋃ j : Fin (k + 2), univ ×ˢ range (SimplexCategory.toTop.{u}.map (SimplexCategory.δ j)))

/-- Identification of `attachingSet X k` with `X.degenerate (k + 1) × Δᵏ⁺¹ ∪ Xₖ₊₁ × ∂Δᵏ⁺¹`. -/
theorem attachingSet_eq (k : ℕ) :
    attachingSet X k =
      SSet.degenerate (X ⋙ forget TopCat) (k + 1) ×ˢ univ ∪
        univ ×ˢ {t | ∃ j : Fin (k + 2), t.down.weights j = 0} := by
  simp only [attachingSet, SimplexCategory.range_toTop_map_δ]
  ext ⟨x, t⟩
  simp [SSet.degenerate_eq_iUnion_range_σ (X := X ⋙ forget TopCat)]

/-- The inclusion `attachingSet X k ↪ Xₖ₊₁ × Δᵏ⁺¹` as a morphism in `TopCat`. -/
def attachingIncl (k : ℕ) :
    TopCat.of (attachingSet X k) ⟶
      TopCat.of (X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Retraction `⦋k + 1⦌ ⟶ ⦋k⦌` left-inverse to `SimplexCategory.δ j`. -/
private def retractδ {k : ℕ} (j : Fin (k + 2)) : ⦋k + 1⦌ ⟶ ⦋k⦌ :=
  Fin.lastCases (SimplexCategory.σ (Fin.last k)) (fun i ↦ SimplexCategory.σ i) j

private theorem δ_comp_retractδ {k : ℕ} (j : Fin (k + 2)) :
    SimplexCategory.δ j ≫ retractδ j = 𝟙 ⦋k⦌ := by
  cases j using Fin.lastCases with
  | last =>
    rw [retractδ, Fin.lastCases_last, ← Fin.succ_last]
    exact SimplexCategory.δ_comp_σ_succ
  | cast i =>
    rw [retractδ, Fin.lastCases_castSucc]
    exact SimplexCategory.δ_comp_σ_self

private abbrev Piece (k : ℕ) : Type := Fin (k + 1) ⊕ Fin (k + 2)

private def pieceSet (X : SimplicialObject TopCat.{u}) (k : ℕ) :
    Piece k → Set (X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :=
  Sum.elim (fun i ↦ range (X.σ i) ×ˢ univ)
    (fun j ↦ univ ×ˢ range (SimplexCategory.toTop.{u}.map (SimplexCategory.δ j)))

private theorem iUnion_pieceSet (k : ℕ) : ⋃ p : Piece k, pieceSet X k p = attachingSet X k := by
  simp [Piece, pieceSet, attachingSet, iUnion_sum]

private theorem isClosed_pieceSet {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) (p : Piece k) :
    IsClosed (pieceSet X k p) := by
  cases p with
  | inl i => exact (hσ i).prod isClosed_univ
  | inr j =>
    exact isClosed_univ.prod (SimplexCategory.isClosedEmbedding_toTop_map_δ j).isClosed_range

/-- When each degeneracy `X.σ i` has closed range, `attachingSet X k` is closed in
`Xₖ₊₁ × Δᵏ⁺¹`. -/
theorem isClosed_attachingSet {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    IsClosed (attachingSet X k) := by
  rw [← iUnion_pieceSet]
  exact isClosed_iUnion_of_finite (isClosed_pieceSet X hσ)

/-- When each degeneracy `X.σ i` has closed range, `attachingIncl X k` is a closed embedding. -/
theorem isClosedEmbedding_attachingIncl {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    IsClosedEmbedding (attachingIncl X k) :=
  (isClosed_attachingSet X hσ).isClosedEmbedding_subtypeVal

private def pieceMap (X : SimplicialObject TopCat.{u}) (k : ℕ) :
    Piece k → C(X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌, skeleton X k) :=
  Sum.elim
    (fun i ↦ (skeleton.ι X k (Fin.last k)).comp
      ((X.δ i.castSucc).hom.prodMap (SimplexCategory.toTop.map (SimplexCategory.σ i)).hom))
    (fun j ↦ (skeleton.ι X k (Fin.last k)).comp
      ((X.δ j).hom.prodMap (SimplexCategory.toTop.map (retractδ j)).hom))

private theorem pieceMap_inl_apply {k : ℕ} (i : Fin (k + 1)) (y : X _⦋k⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :
    pieceMap X k (.inl i) (X.σ i y, t) =
      skeleton.ι X k (Fin.last k) (y, SimplexCategory.toTop.map (SimplexCategory.σ i) t) := by
  have hy : X.δ i.castSucc (X.σ i y) = y := ConcreteCategory.congr_hom (X.δ_comp_σ_self) y
  simp [pieceMap, hy]

private theorem pieceMap_inr_apply {k : ℕ} (j : Fin (k + 2)) (x : X _⦋k + 1⦌)
    (s : SimplexCategory.toTop.{u}.obj ⦋k⦌) :
    pieceMap X k (.inr j) (x, SimplexCategory.toTop.map (SimplexCategory.δ j) s) =
      skeleton.ι X k (Fin.last k) (X.δ j x, s) := by
  have hs : SimplexCategory.toTop.map (retractδ j)
      (SimplexCategory.toTop.map (SimplexCategory.δ j) s) = s := by
    rw [← CategoryTheory.comp_apply, ← SimplexCategory.toTop.map_comp, δ_comp_retractδ,
      SimplexCategory.toTop.map_id, CategoryTheory.id_apply]
  change skeleton.ι X k (Fin.last k)
    (X.δ j x, SimplexCategory.toTop.map (retractδ j)
      (SimplexCategory.toTop.map (SimplexCategory.δ j) s)) = _
  rw [hs]

private theorem pieceMap_inl_eq_inl_of_lt {k : ℕ} {i₁ i₂ : Fin (k + 1)} (h : i₁ < i₂)
    {z : X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌}
    (hz₁ : z ∈ pieceSet X k (.inl i₁)) (hz₂ : z ∈ pieceSet X k (.inl i₂)) :
    pieceMap X k (.inl i₁) z = pieceMap X k (.inl i₂) z := by
  cases k with
  | zero => exact absurd h (Fin.eq_zero i₁ ▸ Fin.eq_zero i₂ ▸ lt_irrefl _)
  | succ k =>
    rcases z with ⟨x, t⟩
    obtain ⟨⟨y₁, hy₁₀⟩, -⟩ := hz₁
    obtain ⟨⟨y₂, hy₂⟩, -⟩ := hz₂
    dsimp only at hy₁₀ hy₂
    let a : Fin (k + 1) := i₁.castPred (Fin.ne_last_of_lt h)
    let b : Fin (k + 1) := i₂.pred (Fin.ne_zero_of_lt h)
    have ha : a.castSucc = i₁ := Fin.castSucc_castPred _ _
    have hb : b.succ = i₂ := Fin.succ_pred _ _
    have hab : a ≤ b := Fin.castSucc_lt_succ_iff.1 (by rwa [ha, hb])
    rw [← ha] at hy₁₀
    rw [← hb] at hy₂
    have hy₁ : y₁ = X.σ b (X.δ a.castSucc y₂) := by
      calc y₁ = X.δ a.castSucc.castSucc (X.σ a.castSucc y₁) :=
            (ConcreteCategory.congr_hom X.δ_comp_σ_self y₁).symm
        _ = X.δ a.castSucc.castSucc (X.σ b.succ y₂) := by rw [hy₁₀, ← hy₂]
        _ = X.σ b (X.δ a.castSucc y₂) :=
            ConcreteCategory.congr_hom (X.δ_comp_σ_of_le (Fin.castSucc_le_castSucc_iff.2 hab)) y₂
    have hy₂' : y₂ = X.σ a (X.δ a.castSucc y₂) := by
      apply (X.isEmbedding_σ b.succ).injective
      rw [hy₂, ← hy₁₀, hy₁]
      exact ConcreteCategory.congr_hom (X.σ_comp_σ hab) (X.δ a.castSucc y₂)
    rw [← ha, ← hb, ← hy₁₀, pieceMap_inl_apply, hy₁₀, ← hy₂, pieceMap_inl_apply, hy₂', hy₁]
    let m₀ : Fin (k + 2) := (Fin.last k).castSucc
    calc skeleton.ι X (k + 1) (Fin.last (k + 1))
          (X.σ b (X.δ a.castSucc y₂), SimplexCategory.toTop.map (SimplexCategory.σ a.castSucc) t)
        = skeleton.ι X (k + 1) m₀ (X.δ a.castSucc y₂,
            SimplexCategory.toTop.map (SimplexCategory.σ a.castSucc ≫ SimplexCategory.σ b) t) := by
          rw [SimplexCategory.toTop.map_comp, CategoryTheory.comp_apply]
          exact skeleton.ι_map X (k + 1) (m := Fin.last (k + 1)) (n := m₀)
            (SimplexCategory.σ b) (X.δ a.castSucc y₂)
            (SimplexCategory.toTop.map (SimplexCategory.σ a.castSucc) t)
      _ = skeleton.ι X (k + 1) m₀ (X.δ a.castSucc y₂,
            SimplexCategory.toTop.map (SimplexCategory.σ b.succ ≫ SimplexCategory.σ a) t) := by
          rw [SimplexCategory.σ_comp_σ hab]
      _ = skeleton.ι X (k + 1) (Fin.last (k + 1))
          (X.σ a (X.δ a.castSucc y₂), SimplexCategory.toTop.map (SimplexCategory.σ b.succ) t) := by
          rw [SimplexCategory.toTop.map_comp, CategoryTheory.comp_apply]
          exact (skeleton.ι_map X (k + 1) (m := Fin.last (k + 1)) (n := m₀)
            (SimplexCategory.σ a) (X.δ a.castSucc y₂)
            (SimplexCategory.toTop.map (SimplexCategory.σ b.succ) t)).symm

private theorem pieceMap_inr_eq_inr_of_lt {k : ℕ} {j₁ j₂ : Fin (k + 2)} (h : j₁ < j₂)
    {z : X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌}
    (hz₁ : z ∈ pieceSet X k (.inr j₁)) (hz₂ : z ∈ pieceSet X k (.inr j₂)) :
    pieceMap X k (.inr j₁) z = pieceMap X k (.inr j₂) z := by
  obtain ⟨-, s₁, hs₁⟩ := hz₁
  obtain ⟨-, s₂, hs₂⟩ := hz₂
  obtain ⟨w₀, hw₁, hw₂⟩ := StdSimplex.exists_map_succAbove_of_map_succAbove_eq h
    (congrArg ULift.down (hs₁.trans hs₂.symm))
  cases k with
  | zero => exact w₀.nonempty.elim Fin.elim0
  | succ k =>
    let a : Fin (k + 2) := j₁.castPred (Fin.ne_last_of_lt h)
    let b : Fin (k + 2) := j₂.pred (Fin.ne_zero_of_lt h)
    have ha : a.castSucc = j₁ := Fin.castSucc_castPred _ _
    have hb : b.succ = j₂ := Fin.succ_pred _ _
    have hab : a ≤ b := Fin.castSucc_lt_succ_iff.1 (by rwa [ha, hb])
    let w : SimplexCategory.toTop.{u}.obj ⦋k⦌ := ULift.up w₀
    have hs₁' : s₁ = SimplexCategory.toTop.map (SimplexCategory.δ b) w := ULift.ext hw₁
    have hs₂' : s₂ = SimplexCategory.toTop.map (SimplexCategory.δ a) w := ULift.ext hw₂
    rw [show z = (z.1, z.2) from rfl, ← hs₁, pieceMap_inr_apply, hs₁, ← hs₂, pieceMap_inr_apply,
      hs₁', hs₂', ← ha, ← hb]
    let m₀ : Fin (k + 2) := (Fin.last k).castSucc
    calc skeleton.ι X (k + 1) (Fin.last (k + 1))
          (X.δ a.castSucc z.1, SimplexCategory.toTop.map (SimplexCategory.δ b) w)
        = skeleton.ι X (k + 1) m₀ (X.δ b (X.δ a.castSucc z.1), w) :=
          (skeleton.ι_map X (k + 1) (m := m₀) (n := Fin.last (k + 1))
            (SimplexCategory.δ b) (X.δ a.castSucc z.1) w).symm
      _ = skeleton.ι X (k + 1) m₀ (X.δ a (X.δ b.succ z.1), w) := by
          rw [← CategoryTheory.comp_apply, ← X.δ_comp_δ hab, CategoryTheory.comp_apply]
      _ = skeleton.ι X (k + 1) (Fin.last (k + 1))
          (X.δ b.succ z.1, SimplexCategory.toTop.map (SimplexCategory.δ a) w) :=
          skeleton.ι_map X (k + 1) (m := m₀) (n := Fin.last (k + 1))
            (SimplexCategory.δ a) (X.δ b.succ z.1) w

private theorem pieceMap_inl_eq_inr {k : ℕ} (i : Fin (k + 1)) (j : Fin (k + 2))
    {z : X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌}
    (hzi : z ∈ pieceSet X k (.inl i)) (hzj : z ∈ pieceSet X k (.inr j)) :
    pieceMap X k (.inl i) z = pieceMap X k (.inr j) z := by
  rcases z with ⟨x, t⟩
  obtain ⟨⟨y, rfl⟩, -⟩ := hzi
  obtain ⟨-, s, rfl⟩ := hzj
  rw [pieceMap_inl_apply, pieceMap_inr_apply, ← CategoryTheory.comp_apply,
    ← SimplexCategory.toTop.map_comp,
    ← skeleton.ι_map X k (m := Fin.last k) (n := Fin.last k)
      (SimplexCategory.δ j ≫ SimplexCategory.σ i) y s]
  simp [SimplicialObject.δ, SimplicialObject.σ]

private theorem pieceMap_eq_on_inter {k : ℕ} (p q : Piece k)
    {z : X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌}
    (hp : z ∈ pieceSet X k p) (hq : z ∈ pieceSet X k q) :
    pieceMap X k p z = pieceMap X k q z := by
  match p, q with
  | .inl i₁, .inl i₂ =>
    rcases lt_trichotomy i₁ i₂ with h | rfl | h
    · exact pieceMap_inl_eq_inl_of_lt X h hp hq
    · rfl
    · exact (pieceMap_inl_eq_inl_of_lt X h hq hp).symm
  | .inr j₁, .inr j₂ =>
    rcases lt_trichotomy j₁ j₂ with h | rfl | h
    · exact pieceMap_inr_eq_inr_of_lt X h hp hq
    · rfl
    · exact (pieceMap_inr_eq_inr_of_lt X h hq hp).symm
  | .inl i, .inr j => exact pieceMap_inl_eq_inr X i j hp hq
  | .inr j, .inl i => exact (pieceMap_inl_eq_inr X i j hq hp).symm

private theorem exists_pieceSet_mem {k : ℕ} (z : attachingSet X k) :
    ∃ p : Piece k, z.1 ∈ pieceSet X k p := by
  rcases z with ⟨w, hw⟩
  rw [← iUnion_pieceSet] at hw
  exact mem_iUnion.1 hw

private theorem continuous_attachingMapAux {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    Continuous (fun z : attachingSet X k ↦
      (pieceMap X k (exists_pieceSet_mem X z).choose z.1 : skeleton X k)) := by
  let S : Piece k → Set (attachingSet X k) := fun p ↦ Subtype.val ⁻¹' pieceSet X k p
  have hcover : ⋃ p, S p = univ := eq_univ_of_forall fun z ↦
    mem_iUnion.2 (exists_pieceSet_mem X z)
  refine continuousOn_univ.1 ?_
  rw [← hcover]
  refine (locallyFinite_of_finite S).continuousOn_iUnion
    (fun p ↦ (isClosed_pieceSet X hσ p).preimage continuous_subtype_val) fun p ↦ ?_
  refine ((pieceMap X k p).continuous.comp continuous_subtype_val).continuousOn.congr ?_
  intro z hz
  exact pieceMap_eq_on_inter X _ p (exists_pieceSet_mem X z).choose_spec hz

/-- The attaching map `attachingSet X k ⟶ skeleton X k` sending `(X.σ i y, t)` to `[y, σᵢ t]`
and `(x, δⱼ s)` to `[X.δ j x, s]`. -/
def attachingMap {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    TopCat.of (attachingSet X k) ⟶ skeleton X k :=
  TopCat.ofHom
    { toFun z := pieceMap X k (exists_pieceSet_mem X z).choose z.1
      continuous_toFun := continuous_attachingMapAux X hσ }

/-- Every pair with a degenerate simplex `X.σ i y` lies in `attachingSet X k`. -/
theorem mem_attachingSet_σ {k : ℕ} (i : Fin (k + 1)) (y : X _⦋k⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :
    (X.σ i y, t) ∈ attachingSet X k :=
  Or.inl (mem_iUnion.2 ⟨i, ⟨y, rfl⟩, trivial⟩)

/-- Every pair with a boundary point `δⱼ s` of `Δᵏ⁺¹` lies in `attachingSet X k`. -/
theorem mem_attachingSet_δ {k : ℕ} (j : Fin (k + 2)) (x : X _⦋k + 1⦌)
    (s : SimplexCategory.toTop.{u}.obj ⦋k⦌) :
    (x, SimplexCategory.toTop.map (SimplexCategory.δ j) s) ∈ attachingSet X k :=
  Or.inr (mem_iUnion.2 ⟨j, trivial, ⟨s, rfl⟩⟩)

/-- Evaluation of `attachingMap X hσ` on a degenerate simplex `(X.σ i y, t)`. -/
@[simp]
theorem attachingMap_σ {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (i : Fin (k + 1)) (y : X _⦋k⦌) (t : SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :
    attachingMap X hσ ⟨(X.σ i y, t), mem_attachingSet_σ X i y t⟩ =
      skeleton.ι X k (Fin.last k) (y, SimplexCategory.toTop.map (SimplexCategory.σ i) t) :=
  (pieceMap_eq_on_inter X _ (.inl i)
    (exists_pieceSet_mem X ⟨(X.σ i y, t), mem_attachingSet_σ X i y t⟩).choose_spec
    ⟨⟨y, rfl⟩, trivial⟩).trans (pieceMap_inl_apply X i y t)

/-- Evaluation of `attachingMap X hσ` on a boundary point `(x, δⱼ s)`. -/
theorem attachingMap_δ {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (j : Fin (k + 2)) (x : X _⦋k + 1⦌) (s : SimplexCategory.toTop.{u}.obj ⦋k⦌) :
    attachingMap X hσ
        ⟨(x, SimplexCategory.toTop.map (SimplexCategory.δ j) s), mem_attachingSet_δ X j x s⟩ =
      skeleton.ι X k (Fin.last k) (X.δ j x, s) :=
  (pieceMap_eq_on_inter X _ (.inr j)
    (exists_pieceSet_mem X _).choose_spec ⟨trivial, ⟨s, rfl⟩⟩).trans
    (pieceMap_inr_apply X j x s)

/-- The skeletal attaching square commutes. -/
theorem attachingMap_comp_skeletonFunctor_map {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    attachingMap X hσ ≫ (skeletonFunctor X).map (homOfLE k.le_succ) =
      attachingIncl X k ≫ TopCat.ofHom (skeleton.ι X (k + 1) (Fin.last (k + 1))) := by
  ext z
  change (skeletonFunctor X).map (homOfLE k.le_succ) (attachingMap X hσ z) =
    skeleton.ι X (k + 1) (Fin.last (k + 1)) z.1
  obtain ⟨p, hz⟩ := exists_pieceSet_mem X z
  cases p with
  | inl i =>
    obtain ⟨⟨y, hy⟩, -⟩ := hz
    have hz' : z = ⟨(X.σ i y, z.1.2), mem_attachingSet_σ X i y z.1.2⟩ :=
      Subtype.ext (Prod.ext hy.symm rfl)
    rw [hz', attachingMap_σ, skeletonFunctor_map_ι]
    exact (skeleton.ι_map X (k + 1) (m := Fin.last (k + 1)) (n := (Fin.last k).castSucc)
      (SimplexCategory.σ i) y z.1.2).symm
  | inr j =>
    obtain ⟨-, s, hs⟩ := hz
    have hz' : z = ⟨(z.1.1, SimplexCategory.toTop.map (SimplexCategory.δ j) s),
        mem_attachingSet_δ X j z.1.1 s⟩ := Subtype.ext (Prod.ext rfl hs.symm)
    rw [hz', attachingMap_δ, skeletonFunctor_map_ι]
    exact skeleton.ι_map X (k + 1) (m := (Fin.last k).castSucc) (n := Fin.last (k + 1))
      (SimplexCategory.δ j) z.1.1 s

/-- Helper: compatibility of a pushout cocone on `attachingMap X hσ` and `attachingIncl X k` with
operators `⦋k + 1⦌ ⟶ ⦋k + 1⦌`. -/
private theorem pushoutCocone_map_last_last {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k))
    (f : ⦋k + 1⦌ ⟶ ⦋k + 1⦌) (x : X _⦋k + 1⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :
    s.inr (X.map f.op x, t) = s.inr (x, SimplexCategory.toTop.map f t) := by
  by_cases hinj : Function.Injective f.toOrderHom
  · have : Mono f := (SimplexCategory.mono_iff_injective (f := f)).2 hinj
    rw [SimplexCategory.eq_id_of_mono f, op_id, X.map_id, SimplexCategory.toTop.map_id]
    rfl
  · obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hinj
    have hnsurj : ¬Function.Surjective f'.toOrderHom := by
      rw [← SimplexCategory.epi_iff_surjective]
      intro; exact absurd (SimplexCategory.len_le_of_epi f') (Nat.not_succ_le_self k)
    obtain ⟨j, f'', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f' hnsurj
    have hσeq : s.inr (X.σ i (X.map f''.op (X.δ j x)), t) =
        s.inl (skeleton.ι X k (Fin.last k)
          (X.map f''.op (X.δ j x), SimplexCategory.toTop.map (SimplexCategory.σ i) t)) :=
      (ConcreteCategory.congr_hom s.condition
        ⟨(X.σ i (X.map f''.op (X.δ j x)), t), mem_attachingSet_σ X i _ t⟩).symm.trans
        (congrArg s.inl (attachingMap_σ X hσ i _ t))
    have hδeq : s.inl (skeleton.ι X k (Fin.last k)
          (X.δ j x, SimplexCategory.toTop.map (SimplexCategory.σ i ≫ f'') t)) =
        s.inr (x, SimplexCategory.toTop.map (SimplexCategory.δ j)
          (SimplexCategory.toTop.map (SimplexCategory.σ i ≫ f'') t)) :=
      (congrArg s.inl (attachingMap_δ X hσ j x _)).symm.trans
        (ConcreteCategory.congr_hom s.condition
          ⟨(x, SimplexCategory.toTop.map (SimplexCategory.δ j)
            (SimplexCategory.toTop.map (SimplexCategory.σ i ≫ f'') t)),
            mem_attachingSet_δ X j x _⟩)
    calc s.inr (X.map (SimplexCategory.σ i ≫ f'' ≫ SimplexCategory.δ j).op x, t)
        = s.inr (X.σ i (X.map f''.op (X.δ j x)), t) := by
            simp [SimplicialObject.σ, SimplicialObject.δ]
      _ = s.inl (skeleton.ι X k (Fin.last k)
            (X.map f''.op (X.δ j x), SimplexCategory.toTop.map (SimplexCategory.σ i) t)) := hσeq
      _ = s.inl (skeleton.ι X k (Fin.last k)
            (X.δ j x, SimplexCategory.toTop.map (SimplexCategory.σ i ≫ f'') t)) := by
            rw [skeleton.ι_map X k (m := Fin.last k) (n := Fin.last k) f'',
              ← CategoryTheory.comp_apply, ← SimplexCategory.toTop.map_comp]
      _ = s.inr (x,
            SimplexCategory.toTop.map (SimplexCategory.σ i ≫ f'' ≫ SimplexCategory.δ j) t) :=
            hδeq.trans (congrArg (fun u ↦ s.inr (x, u))
              (by simp only [← Category.assoc, SimplexCategory.toTop.map_comp,
                CategoryTheory.comp_apply]))

private def pushoutPiece {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k)) (m : Fin (k + 2)) :
    C(X _⦋(m : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌, s.pt) :=
  Fin.lastCases s.inr.hom (fun m' ↦ s.inl.hom.comp (skeleton.ι X k m')) m

private theorem pushoutPiece_last {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k))
    (p : X _⦋k + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋k + 1⦌) :
    pushoutPiece X s (Fin.last (k + 1)) p = s.inr p := by
  simp [pushoutPiece]

private theorem pushoutPiece_castSucc {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k)) (m' : Fin (k + 1))
    (p : X _⦋(m' : ℕ)⦌ × SimplexCategory.toTop.{u}.obj ⦋(m' : ℕ)⦌) :
    pushoutPiece X s m'.castSucc p = s.inl (skeleton.ι X k m' p) := by
  simp [pushoutPiece]

/-- Compatibility of the glued skeletal map on `skeleton X (k + 1)` with all simplicial operators
among degrees `≤ k + 1`. -/
private theorem pushoutCocone_desc_compat {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k))
    ⦃m n : Fin (k + 2)⦄ (f : ⦋(m : ℕ)⦌ ⟶ ⦋(n : ℕ)⦌) (x : X _⦋(n : ℕ)⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋(m : ℕ)⦌) :
    pushoutPiece X s m (X.map f.op x, t) =
      pushoutPiece X s n (x, SimplexCategory.toTop.map f t) := by
  cases m using Fin.lastCases with
  | last =>
    cases n using Fin.lastCases with
    | last =>
      rw [pushoutPiece_last, pushoutPiece_last]
      exact pushoutCocone_map_last_last X hσ s f x t
    | cast n' =>
      have hninj : ¬Function.Injective f.toOrderHom := by
        rw [← SimplexCategory.mono_iff_injective]
        intro; exact absurd (SimplexCategory.len_le_of_mono f) (not_le_of_gt n'.isLt)
      obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hninj
      rw [pushoutPiece_last, pushoutPiece_castSucc]
      calc s.inr (X.map (SimplexCategory.σ i ≫ f').op x, t)
          = s.inr (X.σ i (X.map f'.op x), t) := by simp [SimplicialObject.σ]
        _ = s.inl (skeleton.ι X k (Fin.last k)
              (X.map f'.op x, SimplexCategory.toTop.map (SimplexCategory.σ i) t)) :=
            (ConcreteCategory.congr_hom s.condition
              ⟨(X.σ i (X.map f'.op x), t), mem_attachingSet_σ X i _ t⟩).symm.trans
              (congrArg s.inl (attachingMap_σ X hσ i (X.map f'.op x) t))
        _ = s.inl (skeleton.ι X k n'
              (x, SimplexCategory.toTop.map (SimplexCategory.σ i ≫ f') t)) := by
            rw [skeleton.ι_map X k (m := Fin.last k) (n := n') f', SimplexCategory.toTop.map_comp,
              CategoryTheory.comp_apply]
  | cast m' =>
    cases n using Fin.lastCases with
    | cast n' =>
      rw [pushoutPiece_castSucc, pushoutPiece_castSucc]
      exact congrArg s.inl (skeleton.ι_map X k f x t)
    | last =>
      have hnsurj : ¬Function.Surjective f.toOrderHom := by
        rw [← SimplexCategory.epi_iff_surjective]
        intro; exact absurd (SimplexCategory.len_le_of_epi f) (not_le_of_gt m'.isLt)
      obtain ⟨j, f', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f hnsurj
      rw [pushoutPiece_castSucc, pushoutPiece_last]
      calc s.inl (skeleton.ι X k m' (X.map (f' ≫ SimplexCategory.δ j).op x, t))
          = s.inl (skeleton.ι X k (Fin.last k) (X.δ j x, SimplexCategory.toTop.map f' t)) := by
            simpa [SimplicialObject.δ] using
              congrArg s.inl (skeleton.ι_map X k (m := m') (n := Fin.last k) f' (X.δ j x) t)
        _ = s.inr (x, SimplexCategory.toTop.map (f' ≫ SimplexCategory.δ j) t) := by
            rw [SimplexCategory.toTop.map_comp, CategoryTheory.comp_apply]
            exact (congrArg s.inl (attachingMap_δ X hσ j x _)).symm.trans
              (ConcreteCategory.congr_hom s.condition
                ⟨(x, SimplexCategory.toTop.map (SimplexCategory.δ j)
                  (SimplexCategory.toTop.map f' t)), mem_attachingSet_δ X j x _⟩)

/-- **Skeletal attaching pushout.** Whenever every degeneracy `X.σ i : Xₖ ⟶ Xₖ₊₁` has closed
range, `skeleton X (k + 1)` is the pushout in `TopCat` of `skeleton X k` and `Xₖ₊₁ × Δᵏ⁺¹` along
`attachingSet X k`. -/
theorem isPushout_skeleton_succ {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    IsPushout (attachingMap X hσ) (attachingIncl X k)
      ((skeletonFunctor X).map (homOfLE k.le_succ))
      (TopCat.ofHom (skeleton.ι X (k + 1) (Fin.last (k + 1)))) := by
  have w := attachingMap_comp_skeletonFunctor_map X hσ
  refine IsPushout.of_isColimit' ⟨w⟩
    (PushoutCocone.IsColimit.mk w (fun s ↦ TopCat.ofHom <| skeleton.desc
      (pushoutPiece X s) (pushoutCocone_desc_compat X hσ s)) ?_ ?_ ?_)
  · intro s; apply skeleton.hom_ext; intro m' x t
    change pushoutPiece X s m'.castSucc (x, t) = s.inl (skeleton.ι X k m' (x, t))
    exact pushoutPiece_castSucc X s m' (x, t)
  · intro s; ext ⟨x, t⟩
    exact pushoutPiece_last X s (x, t)
  · intro s d h₁ h₂; apply skeleton.hom_ext; intro m x t
    cases m using Fin.lastCases with
    | last =>
      exact (ConcreteCategory.congr_hom h₂ (x, t)).trans (pushoutPiece_last X s (x, t)).symm
    | cast m' =>
      exact (ConcreteCategory.congr_hom h₁ (skeleton.ι X k m' (x, t))).trans
        (pushoutPiece_castSucc X s m' (x, t)).symm

/-- Each skeletal transition map `skeleton X k ⟶ skeleton X (k + 1)` is a closed embedding when
the degeneracies into `Xₖ₊₁` have closed range. -/
theorem isClosedEmbedding_skeletonFunctor_map_succ {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    IsClosedEmbedding ((skeletonFunctor X).map (homOfLE k.le_succ)) :=
  TauCeti.TopCat.isClosedEmbedding_of_isPushout (isPushout_skeleton_succ X hσ)
    (isClosedEmbedding_attachingIncl X hσ)

/-- Every skeletal inclusion `skeleton X k ⟶ thinRealization X` is a closed embedding when all
degeneracies have closed range. -/
theorem isClosedEmbedding_skeletonCocone_ι
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i))) (k : ℕ) :
    IsClosedEmbedding ((skeletonCocone X).ι.app k) :=
  TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
    (fun n ↦ isClosedEmbedding_skeletonFunctor_map_succ X (hσ n))
    (isColimitSkeletonCocone X) k

end Attaching

section Separation

/-- If every product `Xₙ × Δⁿ` is `T₄`, then every skeleton `skeleton X k` is `T₄`. -/
theorem t4Space_skeleton [∀ n : ℕ, T4Space (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌)]
    (k : ℕ) : T4Space (skeleton X k) := by
  have hT2 (n : ℕ) : T2Space (X _⦋n⦌) :=
    (IsEmbedding.of_leftInverse (f := Prod.fst)
      (fun x : X _⦋n⦌ ↦ (rfl : (x, SimplexCategory.toTopInitialVertex ⦋n⦌).1 = x))
      continuous_fst (.prodMk_left _)).t2Space
  induction k with
  | zero =>
    have : T4Space (X _⦋0⦌) :=
      (Function.LeftInverse.isClosedEmbedding (f := Prod.fst)
        (fun x : X _⦋0⦌ ↦ (rfl : (x, SimplexCategory.toTopInitialVertex ⦋0⦌).1 = x))
        continuous_fst (.prodMk_left _)).t4Space
    exact (skeletonZeroHomeomorph X).symm.t4Space
  | succ k ih =>
    have hσ (i : Fin (k + 1)) : IsClosed (range (X.σ i)) :=
      (X.isClosedEmbedding_σ i).isClosed_range
    have sq := isPushout_skeleton_succ X hσ
    have hm := isClosedEmbedding_attachingIncl X hσ
    have : T1Space (skeleton X (k + 1)) := TauCeti.TopCat.t1Space_of_isPushout sq hm
    have : NormalSpace (skeleton X (k + 1)) := TauCeti.TopCat.normalSpace_of_isPushout sq hm
    exact ⟨⟩

/-- If every product `Xₙ × Δⁿ` is `T₄`, then `thinRealization X` is `T₄` (normal and Hausdorff). -/
theorem t4Space_of_prod [∀ n : ℕ, T4Space (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌)] :
    T4Space (thinRealization X) := by
  have hT2 (n : ℕ) : T2Space (X _⦋n⦌) :=
    (IsEmbedding.of_leftInverse (f := Prod.fst)
      (fun x : X _⦋n⦌ ↦ (rfl : (x, SimplexCategory.toTopInitialVertex ⦋n⦌).1 = x))
      continuous_fst (.prodMk_left _)).t2Space
  have (n : ℕ) : T4Space ((skeletonFunctor X).obj n) := t4Space_skeleton X n
  exact TauCeti.TopCat.t4Space_of_isColimit
    (fun k ↦ isClosedEmbedding_skeletonFunctor_map_succ X
      (fun i ↦ (X.isClosedEmbedding_σ i).isClosed_range))
    (isColimitSkeletonCocone X)

/-- Every simplicial space whose levels `Xₙ` are `T₃` (regular Hausdorff) and Lindelöf has a `T₄`
(normal Hausdorff), and hence paracompact, thin geometric realization. -/
instance instT4Space [∀ n : ℕ, T3Space (X _⦋n⦌)] [∀ n : ℕ, LindelofSpace (X _⦋n⦌)] :
    T4Space (thinRealization X) :=
  t4Space_of_prod X

end Separation

end TauCeti.thinRealization
