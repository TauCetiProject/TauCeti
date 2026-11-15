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
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.Compactness.Paracompact

/-!
# Skeletal filtration and paracompactness of thin geometric realizations

For a simplicial space `X : SimplicialObject TopCat`, the `k`-skeleton
`TauCeti.thinRealization.skeleton X k` is the functor tensor product of `SimplexCategory.toTop` and
`X` restricted to `SimplexCategory.Truncated k`: the quotient of `Σ m : Truncated k, Xₘ × Δᵐ` by all
simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` among degrees `≤ k`. The zero-skeleton is
canonically homeomorphic to `X₀` (`skeletonZeroHomeomorph`), and the skeleta assemble into a
sequential diagram `skeletonFunctor X : ℕ ⥤ TopCat` whose colimit is `thinRealization X`
(`isColimitSkeletonCocone`).

In passing from `skeleton X k` to `skeleton X (k + 1)`, the cell `Xₖ₊₁ × Δᵏ⁺¹` is attached along
`attachingSet X k`, the union of `⋃ i, range (X.σ i) ×ˢ univ` (degenerate simplices) and
`⋃ j, univ ×ˢ range (toTop.map (δ j))` (the boundary `∂Δᵏ⁺¹`). Whenever each degeneracy image
`range (X.σ i)` is closed—in particular whenever `Xₖ₊₁` is Hausdorff
(`CategoryTheory.SimplicialObject.isClosedEmbedding_σ`)—this attaching locus is closed in
`Xₖ₊₁ × Δᵏ⁺¹`, the gluing map `attachingMap X hσ` is continuous, and `skeleton X (k + 1)` is the
pushout of `skeleton X k` and `Xₖ₊₁ × Δᵏ⁺¹` along `attachingSet X k` (`isPushout_skeleton_succ`).
Consequently each skeletal transition map and each inclusion `skeleton X k ⟶ thinRealization X` is
a closed embedding.

Combining the skeletal pushout and sequential colimit normality theorems from
`TauCeti.Topology.Category.TopCat.Normal` shows that whenever every `Xₙ × Δⁿ` is `T₄`
(`t4Space_of_prod`), `thinRealization X` is `T₄` (normal and Hausdorff) in its quotient topology.
Together with the product and paracompactness theorems from
`TauCeti.Topology.Compactness.Lindelof` and `TauCeti.Topology.Compactness.Paracompact`, whenever
every level `Xₙ` is `T₃` and Lindelöf (`instT4Space` and `instLindelofSpace`), `thinRealization X`
is `T₄`, Lindelöf, and hence paracompact.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics **271**, Section
  11.
-/

public noncomputable section

open CategoryTheory Convexity Limits Opposite Set Topology
open SimplexCategory (Truncated toTop)
open scoped Simplicial

universe u

namespace TauCeti.thinRealization

variable (X : SimplicialObject TopCat.{u})

/-- The `k`-skeleton of the thin realization of `X`: the functor tensor product of
`SimplexCategory.toTop` and `X` restricted to `SimplexCategory.Truncated k` (degrees `≤ k`). -/
abbrev skeleton (k : ℕ) : TopCat.{u} :=
  functorTensor (Truncated.inclusion k ⋙ toTop) ((Truncated.inclusion k).op ⋙ X)

/-- If every level `Xₙ` is Lindelöf, every skeleton `skeleton X k` is Lindelöf. -/
instance skeleton.instLindelofSpace [hX : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] (k : ℕ) :
    LindelofSpace (skeleton X k) := by
  have (m : Truncated k) :
      LindelofSpace
        ((((Truncated.inclusion k).op ⋙ X).obj (op m)) ×
          ((Truncated.inclusion k ⋙ toTop.{u}).obj m)) := by
    have : LindelofSpace (X.obj (op ⦋m.obj.len⦌)) := hX m.obj.len
    exact inferInstanceAs (LindelofSpace (X.obj (op ⦋m.obj.len⦌) × toTop.{u}.obj m.obj))
  infer_instance

/-- The zero-skeleton `skeleton X 0` is canonically homeomorphic to `X₀`. -/
def skeletonZeroHomeomorph : skeleton X 0 ≃ₜ X _⦋0⦌ where
  toFun := functorTensor.desc
    (K := Truncated.inclusion 0 ⋙ toTop) (X := (Truncated.inclusion 0).op ⋙ X)
    (fun m : Truncated 0 ↦
      (X.map (eqToHom (congrArg op (SimplexCategory.ext
        (Nat.eq_zero_of_le_zero m.property))))).hom.comp ContinuousMap.fst) <| by
      rintro ⟨m, hm⟩ ⟨n, hn⟩ f x t
      have hm0 : m = ⦋0⦌ := SimplexCategory.ext (Nat.eq_zero_of_le_zero hm)
      have hn0 : n = ⦋0⦌ := SimplexCategory.ext (Nat.eq_zero_of_le_zero hn)
      subst hm0 hn0
      simp [SimplexCategory.hom_zero_zero f.hom]
  invFun x :=
    functorTensor.ι (Truncated.inclusion 0 ⋙ toTop) ((Truncated.inclusion 0).op ⋙ X)
      ⟨⦋0⦌, le_rfl⟩ (x, SimplexCategory.toTopInitialVertex ⦋0⦌)
  left_inv p := by
    obtain ⟨⟨m, hm⟩, x, t, rfl⟩ := functorTensor.ι_jointly_surjective _ _ p
    have hm0 : m = ⦋0⦌ := SimplexCategory.ext (Nat.eq_zero_of_le_zero hm)
    subst hm0
    have ht : t = SimplexCategory.toTopInitialVertex ⦋0⦌ :=
      ULift.ext (Subsingleton.elim (α := StdSimplex ℝ (Fin 1)) t.down _)
    rw [ht, functorTensor.desc_ι]
    simp
  right_inv x := by
    rw [functorTensor.desc_ι]
    simp
  continuous_toFun := ContinuousMap.continuous _
  continuous_invFun :=
    (functorTensor.ι (Truncated.inclusion 0 ⋙ toTop) ((Truncated.inclusion 0).op ⋙ X)
      ⟨⦋0⦌, le_rfl⟩).continuous.comp (continuous_id.prodMk continuous_const)

/-- The isomorphism `skeleton X 0 ≅ X₀` in `TopCat`. -/
def skeletonZeroIso : skeleton X 0 ≅ X _⦋0⦌ :=
  TopCat.isoOfHomeo (skeletonZeroHomeomorph X)

/-- The sequential skeletal filtration `ℕ ⥤ TopCat` of `thinRealization X`. -/
@[expose]
def skeletonFunctor (X : SimplicialObject TopCat.{u}) : ℕ ⥤ TopCat.{u} where
  obj := skeleton X
  map {_ l} h := functorTensor.reindex (Truncated.incl _ l (leOfHom h))
    (Truncated.inclusion l ⋙ toTop) ((Truncated.inclusion l).op ⋙ X)
  map_id k := functorTensor.reindex_id (Truncated.inclusion k ⋙ toTop)
    ((Truncated.inclusion k).op ⋙ X)
  map_comp {_ l n} f g :=
    functorTensor.reindex_comp (Truncated.incl l n (leOfHom g)) (Truncated.inclusion n ⋙ toTop)
      (Truncated.incl _ l (leOfHom f)) ((Truncated.inclusion n).op ⋙ X)

/-- Object evaluation of `skeletonFunctor X`. -/
@[simp]
theorem skeletonFunctor_obj (k : ℕ) :
    (skeletonFunctor X).obj k = skeleton X k :=
  (rfl)

/-- Transition map of `skeletonFunctor X` evaluated on a skeletal representative. -/
-- Simplify before functor-object carrier types inside `DFunLike.coe` are normalized.
@[simp↓]
theorem skeletonFunctor_map_ι {k l : ℕ} (h : k ≤ l) (m : Truncated k)
    (x : X.obj (op m.obj)) (t : toTop.{u}.obj m.obj) :
    (skeletonFunctor X).map (homOfLE h)
        (functorTensor.ι (Truncated.inclusion k ⋙ toTop)
          ((Truncated.inclusion k).op ⋙ X) m (x, t)) =
      functorTensor.ι (Truncated.inclusion l ⋙ toTop)
        ((Truncated.inclusion l).op ⋙ X) ((Truncated.incl k l h).obj m) (x, t) :=
  functorTensor.reindex_ι (Truncated.incl k l h) (Truncated.inclusion l ⋙ toTop)
    ((Truncated.inclusion l).op ⋙ X) m x t

/-- The canonical cocone exhibiting `thinRealization X` over `skeletonFunctor X`. -/
@[expose]
def skeletonCocone : Cocone (skeletonFunctor X) where
  pt := thinRealization X
  ι :=
    { app k := functorTensor.reindex (Truncated.inclusion k) toTop X
      naturality {k l} h :=
        (functorTensor.reindex_comp (Truncated.inclusion l) toTop
          (Truncated.incl k l (leOfHom h)) X).symm.trans (Category.comp_id _).symm }

/-- Point of `skeletonCocone X`. -/
@[simp]
theorem skeletonCocone_pt :
    (skeletonCocone X).pt = thinRealization X :=
  (rfl)

/-- Evaluation of the `k`-th leg of `skeletonCocone X` on a skeletal representative. -/
-- Simplify before `Functor.const_obj_obj` normalizes the cocone carrier inside `DFunLike.coe`.
@[simp↓]
theorem skeletonCocone_ι_app_ι (k : ℕ) (m : Truncated k)
    (x : X.obj (op m.obj)) (t : toTop.{u}.obj m.obj) :
    (skeletonCocone X).ι.app k
        (functorTensor.ι (Truncated.inclusion k ⋙ toTop)
          ((Truncated.inclusion k).op ⋙ X) m (x, t)) =
      functorTensor.ι toTop X m.obj (x, t) :=
  functorTensor.reindex_ι (Truncated.inclusion k) toTop X m x t

private def skeletonCoconeDesc (s : Cocone (skeletonFunctor X)) :
    thinRealization X ⟶ s.pt :=
  TopCat.ofHom <| functorTensor.desc (K := toTop) (X := X)
    (fun n ↦ (s.ι.app n.len).hom.comp
      (functorTensor.ι (Truncated.inclusion n.len ⋙ toTop)
        ((Truncated.inclusion n.len).op ⋙ X) ⟨n, le_rfl⟩)) <| by
      intro m n f x t
      let N := max m.len n.len
      let ym := functorTensor.ι (Truncated.inclusion m.len ⋙ toTop)
        ((Truncated.inclusion m.len).op ⋙ X) ⟨m, le_rfl⟩ (X.map f.op x, t)
      let yn := functorTensor.ι (Truncated.inclusion n.len ⋙ toTop)
        ((Truncated.inclusion n.len).op ⋙ X) ⟨n, le_rfl⟩ (x, toTop.map f t)
      have hm : s.ι.app N
          (functorTensor.ι (Truncated.inclusion N ⋙ toTop) ((Truncated.inclusion N).op ⋙ X)
            ⟨m, le_max_left m.len n.len⟩ (X.map f.op x, t)) = s.ι.app m.len ym :=
        (congrArg (s.ι.app N)
          (skeletonFunctor_map_ι X (le_max_left m.len n.len) ⟨m, le_rfl⟩
            (X.map f.op x) t)).symm.trans <|
          (CategoryTheory.comp_apply
            ((skeletonFunctor X).map (homOfLE (le_max_left m.len n.len)))
            (s.ι.app N) ym).symm.trans
            (ConcreteCategory.congr_hom (s.w (homOfLE (le_max_left m.len n.len))) ym)
      have hn : s.ι.app N
          (functorTensor.ι (Truncated.inclusion N ⋙ toTop) ((Truncated.inclusion N).op ⋙ X)
            ⟨n, le_max_right m.len n.len⟩ (x, toTop.map f t)) = s.ι.app n.len yn :=
        (congrArg (s.ι.app N)
          (skeletonFunctor_map_ι X (le_max_right m.len n.len) ⟨n, le_rfl⟩
            x (toTop.map f t))).symm.trans <|
          (CategoryTheory.comp_apply
            ((skeletonFunctor X).map (homOfLE (le_max_right m.len n.len)))
            (s.ι.app N) yn).symm.trans
            (ConcreteCategory.congr_hom (s.w (homOfLE (le_max_right m.len n.len))) yn)
      exact hm.symm.trans ((congrArg (s.ι.app N)
        (functorTensor.ι_map (Truncated.inclusion N ⋙ toTop) ((Truncated.inclusion N).op ⋙ X)
          (Truncated.Hom.tr f (le_max_left m.len n.len) (le_max_right m.len n.len)) x t)).trans hn)

@[simp]
private theorem skeletonCoconeDesc_ι (s : Cocone (skeletonFunctor X)) (n : SimplexCategory)
    (x : X.obj (op n)) (t : toTop.{u}.obj n) :
    skeletonCoconeDesc X s (functorTensor.ι toTop X n (x, t)) =
      s.ι.app n.len
        (functorTensor.ι (Truncated.inclusion n.len ⋙ toTop)
          ((Truncated.inclusion n.len).op ⋙ X) ⟨n, le_rfl⟩ (x, t)) :=
  functorTensor.desc_ι _ _ n (x, t)

/-- `thinRealization X` is the colimit of its skeletal filtration `skeletonFunctor X` in
`TopCat`. -/
def isColimitSkeletonCocone : IsColimit (skeletonCocone X) where
  desc := skeletonCoconeDesc X
  fac s k :=
    functorTensor.hom_ext fun ⟨m, hm⟩ x t ↦
      let z := functorTensor.ι (Truncated.inclusion k ⋙ toTop)
        ((Truncated.inclusion k).op ⋙ X) ⟨m, hm⟩ (x, t)
      let z₀ := functorTensor.ι (Truncated.inclusion m.len ⋙ toTop)
        ((Truncated.inclusion m.len).op ⋙ X) ⟨m, le_rfl⟩ (x, t)
      (CategoryTheory.comp_apply ((skeletonCocone X).ι.app k)
        (skeletonCoconeDesc X s) z).trans <|
        (congrArg (skeletonCoconeDesc X s)
          (skeletonCocone_ι_app_ι X k ⟨m, hm⟩ x t)).trans <|
          (skeletonCoconeDesc_ι X s m x t).trans <|
            (ConcreteCategory.congr_hom (s.w (homOfLE hm)) z₀).symm.trans <|
              (CategoryTheory.comp_apply ((skeletonFunctor X).map (homOfLE hm))
                (s.ι.app k) z₀).trans
                (congrArg (s.ι.app k) (skeletonFunctor_map_ι X hm ⟨m, le_rfl⟩ x t))
  uniq s g hg :=
    functorTensor.hom_ext fun n x t ↦
      let z₀ := functorTensor.ι (Truncated.inclusion n.len ⋙ toTop)
        ((Truncated.inclusion n.len).op ⋙ X) ⟨n, le_rfl⟩ (x, t)
      (congrArg g (skeletonCocone_ι_app_ι X n.len ⟨n, le_rfl⟩ x t).symm).trans <|
        (CategoryTheory.comp_apply ((skeletonCocone X).ι.app n.len) g z₀).symm.trans <|
          (ConcreteCategory.congr_hom (hg n.len) z₀).trans
            (skeletonCoconeDesc_ι X s n x t).symm

section Attaching

/-- The attaching subspace in `Xₖ₊₁ × Δᵏ⁺¹` consisting of pairs with a degenerate simplex or a
boundary point of `Δᵏ⁺¹`. -/
def attachingSet (k : ℕ) :
    Set (X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌) :=
  (⋃ i : Fin (k + 1), range (X.σ i) ×ˢ univ) ∪
    (⋃ j : Fin (k + 2), univ ×ˢ range (toTop.{u}.map (SimplexCategory.δ j)))

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
      TopCat.of (X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem attachingIncl_apply (k : ℕ) (z : attachingSet X k) :
    attachingIncl X k z = z.1 :=
  (rfl)

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

private theorem map_op_σ_comp_apply {n : ℕ} {d : SimplexCategory} (i : Fin (n + 1))
    (g : ⦋n⦌ ⟶ d) (x : X.obj (op d)) :
    X.map (SimplexCategory.σ i ≫ g).op x = X.σ i (X.map g.op x) := by
  rw [op_comp, X.map_comp, CategoryTheory.comp_apply, ← X.σ_def]

private theorem map_op_comp_δ_apply {n : ℕ} {c : SimplexCategory} (g : c ⟶ ⦋n⦌)
    (j : Fin (n + 2)) (x : X _⦋n + 1⦌) :
    X.map (g ≫ SimplexCategory.δ j).op x = X.map g.op (X.δ j x) := by
  rw [op_comp, X.map_comp, CategoryTheory.comp_apply, ← X.δ_def]

private abbrev Piece (k : ℕ) : Type := Fin (k + 1) ⊕ Fin (k + 2)

private def pieceSet (X : SimplicialObject TopCat.{u}) (k : ℕ) :
    Piece k → Set (X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌) :=
  Sum.elim (fun i ↦ range (X.σ i) ×ˢ univ)
    (fun j ↦ univ ×ˢ range (toTop.{u}.map (SimplexCategory.δ j)))

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
    Piece k → C(X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌, skeleton X k) :=
  Sum.elim
    (fun i ↦
      (functorTensor.ι (Truncated.inclusion k ⋙ toTop.{u})
        ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩).comp
        ((X.δ i.castSucc).hom.prodMap (toTop.{u}.map (SimplexCategory.σ i)).hom))
    (fun j ↦
      (functorTensor.ι (Truncated.inclusion k ⋙ toTop.{u})
        ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩).comp
        ((X.δ j).hom.prodMap (toTop.{u}.map (retractδ j)).hom))

private theorem pieceMap_inl_apply {k : ℕ} (i : Fin (k + 1)) (y : X _⦋k⦌)
    (t : toTop.{u}.obj ⦋k + 1⦌) :
    pieceMap X k (.inl i) (X.σ i y, t) =
      functorTensor.ι (Truncated.inclusion k ⋙ toTop)
        ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩
        (y, toTop.map (SimplexCategory.σ i) t) :=
  congrArg
    (functorTensor.ι (Truncated.inclusion k ⋙ toTop)
      ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩)
    (Prod.ext (ConcreteCategory.congr_hom X.δ_comp_σ_self y) rfl)

private theorem pieceMap_inr_apply {k : ℕ} (j : Fin (k + 2)) (x : X _⦋k + 1⦌)
    (s : toTop.{u}.obj ⦋k⦌) :
    pieceMap X k (.inr j) (x, toTop.map (SimplexCategory.δ j) s) =
      functorTensor.ι (Truncated.inclusion k ⋙ toTop)
        ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩ (X.δ j x, s) := by
  have hs : toTop.map (retractδ j) (toTop.map (SimplexCategory.δ j) s) = s := by
    rw [← CategoryTheory.comp_apply, ← toTop.map_comp, δ_comp_retractδ, toTop.map_id,
      CategoryTheory.id_apply]
  exact congrArg
    (functorTensor.ι (Truncated.inclusion k ⋙ toTop)
      ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩)
    (Prod.ext rfl hs)

private theorem pieceMap_inl_eq_inl_of_lt {k : ℕ} {i₁ i₂ : Fin (k + 1)} (h : i₁ < i₂)
    {z : X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌}
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
    let m₀ : Truncated (k + 1) := ⟨⦋k⦌, k.le_succ⟩
    let ιs := functorTensor.ι (Truncated.inclusion (k + 1) ⋙ toTop.{u})
      ((Truncated.inclusion (k + 1)).op ⋙ X)
    calc ιs ⟨⦋k + 1⦌, le_rfl⟩
          (X.σ b (X.δ a.castSucc y₂), toTop.{u}.map (SimplexCategory.σ a.castSucc) t)
        = ιs m₀ (X.δ a.castSucc y₂,
            toTop.{u}.map (SimplexCategory.σ a.castSucc ≫ SimplexCategory.σ b) t) := by
          rw [toTop.map_comp, CategoryTheory.comp_apply, X.σ_def]
          exact functorTensor.ι_map (Truncated.inclusion (k + 1) ⋙ toTop)
            ((Truncated.inclusion (k + 1)).op ⋙ X)
            (Truncated.Hom.tr (SimplexCategory.σ b) le_rfl k.le_succ) (X.δ a.castSucc y₂)
            (toTop.map (SimplexCategory.σ a.castSucc) t)
      _ = ιs m₀ (X.δ a.castSucc y₂,
            toTop.{u}.map (SimplexCategory.σ b.succ ≫ SimplexCategory.σ a) t) := by
          rw [SimplexCategory.σ_comp_σ hab]
      _ = ιs ⟨⦋k + 1⦌, le_rfl⟩
          (X.σ a (X.δ a.castSucc y₂), toTop.{u}.map (SimplexCategory.σ b.succ) t) := by
          rw [toTop.map_comp, CategoryTheory.comp_apply, X.σ_def]
          exact (functorTensor.ι_map (Truncated.inclusion (k + 1) ⋙ toTop)
            ((Truncated.inclusion (k + 1)).op ⋙ X)
            (Truncated.Hom.tr (SimplexCategory.σ a) le_rfl k.le_succ) (X.δ a.castSucc y₂)
            (toTop.map (SimplexCategory.σ b.succ) t)).symm

private theorem pieceMap_inr_eq_inr_of_lt {k : ℕ} {j₁ j₂ : Fin (k + 2)} (h : j₁ < j₂)
    {z : X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌}
    (hz₁ : z ∈ pieceSet X k (.inr j₁)) (hz₂ : z ∈ pieceSet X k (.inr j₂)) :
    pieceMap X k (.inr j₁) z = pieceMap X k (.inr j₂) z := by
  rcases z with ⟨x, t⟩
  obtain ⟨-, s₁, hs₁⟩ := hz₁
  obtain ⟨-, s₂, hs₂⟩ := hz₂
  dsimp only at hs₁ hs₂
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
    let w : toTop.{u}.obj ⦋k⦌ := ULift.up w₀
    have hs₁' : s₁ = toTop.map (SimplexCategory.δ b) w := ULift.ext hw₁
    have hs₂' : s₂ = toTop.map (SimplexCategory.δ a) w := ULift.ext hw₂
    rw [← hs₁, pieceMap_inr_apply, hs₁, ← hs₂, pieceMap_inr_apply, hs₁', hs₂', ← ha, ← hb]
    let m₀ : Truncated (k + 1) := ⟨⦋k⦌, k.le_succ⟩
    let ιs := functorTensor.ι (Truncated.inclusion (k + 1) ⋙ toTop.{u})
      ((Truncated.inclusion (k + 1)).op ⋙ X)
    calc ιs ⟨⦋k + 1⦌, le_rfl⟩ (X.δ a.castSucc x, toTop.{u}.map (SimplexCategory.δ b) w)
        = ιs m₀ (X.δ b (X.δ a.castSucc x), w) := by
          rw [X.δ_def b]
          exact (functorTensor.ι_map (Truncated.inclusion (k + 1) ⋙ toTop)
            ((Truncated.inclusion (k + 1)).op ⋙ X)
            (Truncated.Hom.tr (SimplexCategory.δ b) k.le_succ le_rfl) (X.δ a.castSucc x) w).symm
      _ = ιs m₀ (X.δ a (X.δ b.succ x), w) := by
          rw [← CategoryTheory.comp_apply, ← X.δ_comp_δ hab, CategoryTheory.comp_apply]
      _ = ιs ⟨⦋k + 1⦌, le_rfl⟩ (X.δ b.succ x, toTop.{u}.map (SimplexCategory.δ a) w) := by
          rw [X.δ_def a]
          exact functorTensor.ι_map (Truncated.inclusion (k + 1) ⋙ toTop)
            ((Truncated.inclusion (k + 1)).op ⋙ X)
            (Truncated.Hom.tr (SimplexCategory.δ a) k.le_succ le_rfl) (X.δ b.succ x) w

private theorem pieceMap_inl_eq_inr {k : ℕ} (i : Fin (k + 1)) (j : Fin (k + 2))
    {z : X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌}
    (hzi : z ∈ pieceSet X k (.inl i)) (hzj : z ∈ pieceSet X k (.inr j)) :
    pieceMap X k (.inl i) z = pieceMap X k (.inr j) z := by
  rcases z with ⟨x, t⟩
  obtain ⟨⟨y, rfl⟩, -⟩ := hzi
  obtain ⟨-, s, rfl⟩ := hzj
  rw [pieceMap_inl_apply, pieceMap_inr_apply, ← CategoryTheory.comp_apply, ← toTop.map_comp]
  refine (functorTensor.ι_map (Truncated.inclusion k ⋙ toTop) ((Truncated.inclusion k).op ⋙ X)
    (Truncated.Hom.tr (SimplexCategory.δ j ≫ SimplexCategory.σ i) le_rfl le_rfl) y s).symm.trans ?_
  exact congrArg
    (fun y' ↦ functorTensor.ι (Truncated.inclusion k ⋙ toTop)
      ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩ (y', s))
    (by
      rw [X.δ_def, X.σ_def, ← CategoryTheory.comp_apply, ← X.map_comp, ← op_comp]
      -- `Truncated.inclusion k` acts as the identity on underlying morphisms.
      rfl)

private theorem pieceMap_eq_on_inter {k : ℕ} (p q : Piece k)
    {z : X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌}
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
    (t : toTop.{u}.obj ⦋k + 1⦌) :
    (X.σ i y, t) ∈ attachingSet X k :=
  Or.inl (mem_iUnion.2 ⟨i, ⟨y, rfl⟩, trivial⟩)

/-- Every pair with a boundary point `δⱼ s` of `Δᵏ⁺¹` lies in `attachingSet X k`. -/
theorem mem_attachingSet_δ {k : ℕ} (j : Fin (k + 2)) (x : X _⦋k + 1⦌)
    (s : toTop.{u}.obj ⦋k⦌) :
    (x, toTop.map (SimplexCategory.δ j) s) ∈ attachingSet X k :=
  Or.inr (mem_iUnion.2 ⟨j, trivial, ⟨s, rfl⟩⟩)

/-- Evaluation of `attachingMap X hσ` on a degenerate simplex `(X.σ i y, t)`. -/
@[simp]
theorem attachingMap_σ {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (i : Fin (k + 1)) (y : X _⦋k⦌) (t : toTop.{u}.obj ⦋k + 1⦌) :
    attachingMap X hσ ⟨(X.σ i y, t), mem_attachingSet_σ X i y t⟩ =
      functorTensor.ι (Truncated.inclusion k ⋙ toTop)
        ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩ (y, toTop.map (SimplexCategory.σ i) t) :=
  (pieceMap_eq_on_inter X _ (.inl i)
    (exists_pieceSet_mem X ⟨(X.σ i y, t), mem_attachingSet_σ X i y t⟩).choose_spec
    ⟨⟨y, rfl⟩, trivial⟩).trans (pieceMap_inl_apply X i y t)

/-- Evaluation of `attachingMap X hσ` on a boundary point `(x, δⱼ s)`. -/
-- Simplify before `SimplexCategory.toTop_map` unfolds `toTop.map (SimplexCategory.δ j)`.
@[simp↓]
theorem attachingMap_δ {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (j : Fin (k + 2)) (x : X _⦋k + 1⦌) (s : toTop.{u}.obj ⦋k⦌) :
    attachingMap X hσ
        ⟨(x, toTop.map (SimplexCategory.δ j) s), mem_attachingSet_δ X j x s⟩ =
      functorTensor.ι (Truncated.inclusion k ⋙ toTop)
        ((Truncated.inclusion k).op ⋙ X) ⟨⦋k⦌, le_rfl⟩ (X.δ j x, s) :=
  (pieceMap_eq_on_inter X _ (.inr j)
    (exists_pieceSet_mem X _).choose_spec ⟨trivial, ⟨s, rfl⟩⟩).trans
    (pieceMap_inr_apply X j x s)

/-- The skeletal attaching square commutes. -/
theorem attachingMap_comp_skeletonFunctor_map {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    attachingMap X hσ ≫ (skeletonFunctor X).map (homOfLE k.le_succ) =
      attachingIncl X k ≫
        TopCat.ofHom
          (functorTensor.ι (Truncated.inclusion (k + 1) ⋙ toTop)
            ((Truncated.inclusion (k + 1)).op ⋙ X) ⟨⦋k + 1⦌, le_rfl⟩) := by
  ext z
  refine (CategoryTheory.comp_apply _ _ z).trans <|
    Eq.trans ?_ (CategoryTheory.comp_apply _ _ z).symm
  rcases z with ⟨⟨x, t⟩, hz₀⟩
  obtain ⟨p, hz⟩ := exists_pieceSet_mem X ⟨(x, t), hz₀⟩
  cases p with
  | inl i =>
    obtain ⟨⟨y, rfl⟩, -⟩ := hz
    exact (congrArg ((skeletonFunctor X).map (homOfLE k.le_succ))
      (attachingMap_σ X hσ i y t)).trans <|
      (skeletonFunctor_map_ι X k.le_succ ⟨⦋k⦌, le_rfl⟩ y
        (toTop.map (SimplexCategory.σ i) t)).trans <|
        (functorTensor.ι_map (Truncated.inclusion (k + 1) ⋙ toTop)
          ((Truncated.inclusion (k + 1)).op ⋙ X)
          (Truncated.Hom.tr (SimplexCategory.σ i) le_rfl k.le_succ) y t).symm.trans
          (congrArg (fun x' ↦ functorTensor.ι (Truncated.inclusion (k + 1) ⋙ toTop)
            ((Truncated.inclusion (k + 1)).op ⋙ X) ⟨⦋k + 1⦌, le_rfl⟩ (x', t))
            (ConcreteCategory.congr_hom (X.σ_def i).symm y))
  | inr j =>
    obtain ⟨-, s, rfl⟩ := hz
    exact (congrArg ((skeletonFunctor X).map (homOfLE k.le_succ))
      (attachingMap_δ X hσ j x s)).trans <|
      (skeletonFunctor_map_ι X k.le_succ ⟨⦋k⦌, le_rfl⟩ (X.δ j x) s).trans <|
        (congrArg (fun x' ↦ functorTensor.ι (Truncated.inclusion (k + 1) ⋙ toTop)
          ((Truncated.inclusion (k + 1)).op ⋙ X) ⟨⦋k⦌, k.le_succ⟩ (x', s))
          (ConcreteCategory.congr_hom (X.δ_def j) x)).trans
          (functorTensor.ι_map (Truncated.inclusion (k + 1) ⋙ toTop)
            ((Truncated.inclusion (k + 1)).op ⋙ X)
            (Truncated.Hom.tr (SimplexCategory.δ j) k.le_succ le_rfl) x s)

/-- Helper: compatibility of a pushout cocone on `attachingMap X hσ` and `attachingIncl X k` with
operators `⦋k + 1⦌ ⟶ ⦋k + 1⦌`. -/
private theorem pushoutCocone_map_last_last {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k))
    (f : ⦋k + 1⦌ ⟶ ⦋k + 1⦌) (x : X _⦋k + 1⦌)
    (t : toTop.{u}.obj ⦋k + 1⦌) :
    s.inr (X.map f.op x, t) = s.inr (x, toTop.map f t) := by
  by_cases hinj : Function.Injective f.toOrderHom
  · have : Mono f := (SimplexCategory.mono_iff_injective (f := f)).2 hinj
    rw [SimplexCategory.eq_id_of_mono f, op_id, X.map_id, toTop.map_id,
      CategoryTheory.id_apply, CategoryTheory.id_apply]
  · obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hinj
    have hnsurj : ¬Function.Surjective f'.toOrderHom := by
      rw [← SimplexCategory.epi_iff_surjective]
      intro; exact absurd (SimplexCategory.len_le_of_epi f') (Nat.not_succ_le_self k)
    obtain ⟨j, f'', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f' hnsurj
    let ιk := functorTensor.ι (Truncated.inclusion k ⋙ toTop.{u})
      ((Truncated.inclusion k).op ⋙ X)
    have hσeq : s.inr (X.σ i (X.map f''.op (X.δ j x)), t) =
        s.inl (ιk ⟨⦋k⦌, le_rfl⟩
          (X.map f''.op (X.δ j x), toTop.{u}.map (SimplexCategory.σ i) t)) :=
      (ConcreteCategory.congr_hom s.condition
        ⟨(X.σ i (X.map f''.op (X.δ j x)), t), mem_attachingSet_σ X i _ t⟩).symm.trans
        (congrArg s.inl (attachingMap_σ X hσ i _ t))
    have hδeq : s.inl (ιk ⟨⦋k⦌, le_rfl⟩
          (X.δ j x, toTop.{u}.map (SimplexCategory.σ i ≫ f'') t)) =
        s.inr (x, toTop.{u}.map (SimplexCategory.δ j)
          (toTop.{u}.map (SimplexCategory.σ i ≫ f'') t)) :=
      (congrArg s.inl (attachingMap_δ X hσ j x _)).symm.trans
        (ConcreteCategory.congr_hom s.condition
          ⟨(x, toTop.map (SimplexCategory.δ j)
            (toTop.map (SimplexCategory.σ i ≫ f'') t)),
            mem_attachingSet_δ X j x _⟩)
    calc s.inr (X.map (SimplexCategory.σ i ≫ f'' ≫ SimplexCategory.δ j).op x, t)
        = s.inr (X.σ i (X.map f''.op (X.δ j x)), t) := by
            rw [map_op_σ_comp_apply, map_op_comp_δ_apply]
      _ = s.inl (ιk ⟨⦋k⦌, le_rfl⟩
            (X.map f''.op (X.δ j x), toTop.{u}.map (SimplexCategory.σ i) t)) := hσeq
      _ = s.inl (ιk ⟨⦋k⦌, le_rfl⟩
            (X.δ j x, toTop.{u}.map (SimplexCategory.σ i ≫ f'') t)) := by
            rw [toTop.map_comp, CategoryTheory.comp_apply]
            exact congrArg s.inl
              (functorTensor.ι_map (Truncated.inclusion k ⋙ toTop)
                ((Truncated.inclusion k).op ⋙ X) (Truncated.Hom.tr f'' le_rfl le_rfl)
                (X.δ j x) (toTop.map (SimplexCategory.σ i) t))
      _ = s.inr (x, toTop.map (SimplexCategory.σ i ≫ f'' ≫ SimplexCategory.δ j) t) :=
            hδeq.trans (congrArg (fun u ↦ s.inr (x, u))
              (by simp only [← Category.assoc, toTop.map_comp, CategoryTheory.comp_apply]))

private def pushoutPiece {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k)) (m : Truncated (k + 1)) :
    C(((Truncated.inclusion (k + 1)).op ⋙ X).obj (op m) ×
      (Truncated.inclusion (k + 1) ⋙ toTop.{u}).obj m, s.pt) :=
  if hm : m.obj.len ≤ k then
    s.inl.hom.comp
      (functorTensor.ι (Truncated.inclusion k ⋙ toTop.{u})
        ((Truncated.inclusion k).op ⋙ X) ⟨m.obj, hm⟩)
  else
    have hmk : m.obj = ⦋k + 1⦌ :=
      SimplexCategory.ext (Nat.le_antisymm m.property (Nat.gt_of_not_le hm))
    s.inr.hom.comp
      ((X.map (eqToHom (congrArg op hmk))).hom.prodMap (toTop.{u}.map (eqToHom hmk)).hom)

private theorem pushoutPiece_of_le {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k)) {m : Truncated (k + 1)}
    (hm : m.obj.len ≤ k) (p : X.obj (op m.obj) × toTop.{u}.obj m.obj) :
    pushoutPiece X s m p =
      s.inl (functorTensor.ι (Truncated.inclusion k ⋙ toTop)
        ((Truncated.inclusion k).op ⋙ X) ⟨m.obj, hm⟩ p) := by
  simp [pushoutPiece, hm]

private theorem pushoutPiece_top {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k))
    (p : X _⦋k + 1⦌ × toTop.{u}.obj ⦋k + 1⦌) :
    pushoutPiece X s ⟨⦋k + 1⦌, le_rfl⟩ p = s.inr p := by
  rcases p with ⟨x, t⟩
  simp only [pushoutPiece, Nat.not_succ_le_self, ↓reduceDIte, eqToHom_refl, X.map_id, toTop.map_id,
    TopCat.hom_id, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply]
  -- `TopCat.Hom.hom s.inr` and `ConcreteCategory.hom s.inr` agree definitionally.
  rfl

/-- Compatibility of the glued skeletal map on `skeleton X (k + 1)` with all simplicial operators
among degrees `≤ k + 1`. -/
private theorem pushoutCocone_desc_compat {k : ℕ}
    (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i)))
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k))
    ⦃m n : Truncated (k + 1)⦄ (f : m ⟶ n) (x : X.obj (op n.obj))
    (t : toTop.{u}.obj m.obj) :
    pushoutPiece X s m (X.map f.hom.op x, t) =
      pushoutPiece X s n (x, toTop.map f.hom t) := by
  rcases m with ⟨c, hc⟩
  rcases n with ⟨d, hd⟩
  by_cases hck : c.len ≤ k
  · by_cases hdk : d.len ≤ k
    · rw [pushoutPiece_of_le X s hck, pushoutPiece_of_le X s hdk]
      exact congrArg s.inl
        (functorTensor.ι_map (Truncated.inclusion k ⋙ toTop) ((Truncated.inclusion k).op ⋙ X)
          (Truncated.Hom.tr f.hom hck hdk) x t)
    · have hd_eq : d = ⦋k + 1⦌ :=
        SimplexCategory.ext (Nat.le_antisymm hd (Nat.gt_of_not_le hdk))
      subst hd_eq
      have hnsurj : ¬Function.Surjective f.hom.toOrderHom := by
        rw [← SimplexCategory.epi_iff_surjective]
        intro
        exact Nat.not_succ_le_self k ((SimplexCategory.len_le_of_epi f.hom).trans hck)
      obtain ⟨j, f', hff'⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f.hom hnsurj
      rw [pushoutPiece_of_le X s hck, pushoutPiece_top, hff']
      let ιk := functorTensor.ι (Truncated.inclusion k ⋙ toTop.{u})
        ((Truncated.inclusion k).op ⋙ X)
      calc s.inl (ιk ⟨c, hck⟩ (X.map (f' ≫ SimplexCategory.δ j).op x, t))
          = s.inl (ιk ⟨⦋k⦌, le_rfl⟩ (X.δ j x, toTop.{u}.map f' t)) := by
            rw [map_op_comp_δ_apply]
            exact congrArg s.inl
              (functorTensor.ι_map (Truncated.inclusion k ⋙ toTop) ((Truncated.inclusion k).op ⋙ X)
                (Truncated.Hom.tr f' hck le_rfl) (X.δ j x) t)
        _ = s.inr (x, toTop.map (f' ≫ SimplexCategory.δ j) t) := by
            rw [toTop.map_comp, CategoryTheory.comp_apply]
            exact (congrArg s.inl (attachingMap_δ X hσ j x _)).symm.trans
              (ConcreteCategory.congr_hom s.condition
                ⟨(x, toTop.map (SimplexCategory.δ j) (toTop.map f' t)),
                  mem_attachingSet_δ X j x _⟩)
  · have hc_eq : c = ⦋k + 1⦌ :=
      SimplexCategory.ext (Nat.le_antisymm hc (Nat.gt_of_not_le hck))
    subst hc_eq
    by_cases hdk : d.len ≤ k
    · have hninj : ¬Function.Injective f.hom.toOrderHom := by
        rw [← SimplexCategory.mono_iff_injective]
        intro
        exact hck ((SimplexCategory.len_le_of_mono f.hom).trans hdk)
      obtain ⟨i, f', hff'⟩ := SimplexCategory.eq_σ_comp_of_not_injective f.hom hninj
      rw [pushoutPiece_top, pushoutPiece_of_le X s hdk, hff']
      let ιk := functorTensor.ι (Truncated.inclusion k ⋙ toTop.{u})
        ((Truncated.inclusion k).op ⋙ X)
      calc s.inr (X.map (SimplexCategory.σ i ≫ f').op x, t)
          = s.inr (X.σ i (X.map f'.op x), t) := by rw [map_op_σ_comp_apply]
        _ = s.inl (ιk ⟨⦋k⦌, le_rfl⟩
              (X.map f'.op x, toTop.{u}.map (SimplexCategory.σ i) t)) :=
            (ConcreteCategory.congr_hom s.condition
              ⟨(X.σ i (X.map f'.op x), t), mem_attachingSet_σ X i _ t⟩).symm.trans
              (congrArg s.inl (attachingMap_σ X hσ i (X.map f'.op x) t))
        _ = s.inl (ιk ⟨d, hdk⟩
              (x, toTop.{u}.map (SimplexCategory.σ i ≫ f') t)) := by
            rw [toTop.map_comp, CategoryTheory.comp_apply]
            exact congrArg s.inl
              (functorTensor.ι_map (Truncated.inclusion k ⋙ toTop) ((Truncated.inclusion k).op ⋙ X)
                (Truncated.Hom.tr f' le_rfl hdk) x (toTop.map (SimplexCategory.σ i) t))
    · have hd_eq : d = ⦋k + 1⦌ :=
        SimplexCategory.ext (Nat.le_antisymm hd (Nat.gt_of_not_le hdk))
      subst hd_eq
      rw [pushoutPiece_top, pushoutPiece_top]
      exact pushoutCocone_map_last_last X hσ s f.hom x t

private def pushoutCoconeDesc {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k)) :
    skeleton X (k + 1) ⟶ s.pt :=
  TopCat.ofHom <| functorTensor.desc (pushoutPiece X s) (pushoutCocone_desc_compat X hσ s)

-- Simplify before functor-object carrier types inside `DFunLike.coe` are normalized.
@[simp↓]
private theorem pushoutCoconeDesc_ι {k : ℕ} {hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))}
    (s : PushoutCocone (attachingMap X hσ) (attachingIncl X k))
    (m : Truncated (k + 1)) (p : X.obj (op m.obj) × toTop.{u}.obj m.obj) :
    pushoutCoconeDesc X s
        (functorTensor.ι (Truncated.inclusion (k + 1) ⋙ toTop)
          ((Truncated.inclusion (k + 1)).op ⋙ X) m p) =
      pushoutPiece X s m p :=
  functorTensor.desc_ι (pushoutPiece X s) (pushoutCocone_desc_compat X hσ s) m p

/-- **Skeletal attaching pushout.** Whenever every degeneracy `X.σ i : Xₖ ⟶ Xₖ₊₁` has closed
range, `skeleton X (k + 1)` is the pushout in `TopCat` of `skeleton X k` and `Xₖ₊₁ × Δᵏ⁺¹` along
`attachingSet X k`. -/
theorem isPushout_skeleton_succ {k : ℕ} (hσ : ∀ i : Fin (k + 1), IsClosed (range (X.σ i))) :
    IsPushout (attachingMap X hσ) (attachingIncl X k)
      ((skeletonFunctor X).map (homOfLE k.le_succ))
      (TopCat.ofHom
        (functorTensor.ι (Truncated.inclusion (k + 1) ⋙ toTop)
          ((Truncated.inclusion (k + 1)).op ⋙ X) ⟨⦋k + 1⦌, le_rfl⟩)) := by
  have w := attachingMap_comp_skeletonFunctor_map X hσ
  refine IsPushout.of_isColimit' ⟨w⟩
    (PushoutCocone.IsColimit.mk w (pushoutCoconeDesc X) ?_ ?_ ?_)
  · intro s
    exact functorTensor.hom_ext fun ⟨c, hc⟩ x t ↦
      (congrArg (pushoutCoconeDesc X s)
        (skeletonFunctor_map_ι X k.le_succ ⟨c, hc⟩ x t)).trans
        ((pushoutCoconeDesc_ι X s ⟨c, hc.trans k.le_succ⟩ (x, t)).trans
          (pushoutPiece_of_le X s (m := ⟨c, hc.trans k.le_succ⟩) hc (x, t)))
  · intro s
    ext ⟨x, t⟩
    exact (pushoutCoconeDesc_ι X s ⟨⦋k + 1⦌, le_rfl⟩ (x, t)).trans
      (pushoutPiece_top X s (x, t))
  · intro s g h₁ h₂
    refine functorTensor.hom_ext fun ⟨c, hc⟩ x t ↦ ?_
    rw [pushoutCoconeDesc_ι]
    by_cases hck : c.len ≤ k
    · have hg := ConcreteCategory.congr_hom h₁
        (functorTensor.ι (Truncated.inclusion k ⋙ toTop)
          ((Truncated.inclusion k).op ⋙ X) ⟨c, hck⟩ (x, t))
      exact (congrArg g (skeletonFunctor_map_ι X k.le_succ ⟨c, hck⟩ x t).symm).trans <|
        hg.trans (pushoutPiece_of_le X s (m := ⟨c, hc⟩) hck (x, t)).symm
    · have hc_eq : c = ⦋k + 1⦌ :=
        SimplexCategory.ext (Nat.le_antisymm hc (Nat.gt_of_not_le hck))
      subst hc_eq
      exact (ConcreteCategory.congr_hom h₂ (x, t)).trans (pushoutPiece_top X s (x, t)).symm

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

private theorem isClosedEmbedding_prodMk_initialVertex (n : ℕ) :
    IsClosedEmbedding fun x : X _⦋n⦌ ↦ (x, SimplexCategory.toTopInitialVertex ⦋n⦌) :=
  .of_continuous_injective_isClosedMap (.prodMk_left _) (Prod.mk_left_injective _)
    (isClosedMap_prodMk_right _)

/-- If every product `Xₙ × Δⁿ` is `T₄`, then every skeleton `skeleton X k` is `T₄`. -/
theorem t4Space_skeleton [∀ n : ℕ, T4Space (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)]
    (k : ℕ) : T4Space (skeleton X k) := by
  have (n : ℕ) : T2Space (X _⦋n⦌) := (isClosedEmbedding_prodMk_initialVertex X n).t2Space
  induction k with
  | zero =>
    have : T4Space (X _⦋0⦌) := (isClosedEmbedding_prodMk_initialVertex X 0).t4Space
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
theorem t4Space_of_prod [∀ n : ℕ, T4Space (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    T4Space (thinRealization X) := by
  have (n : ℕ) : T2Space (X _⦋n⦌) := (isClosedEmbedding_prodMk_initialVertex X n).t2Space
  have (n : ℕ) : T4Space ((skeletonFunctor X).obj n) := by
    rw [skeletonFunctor_obj]
    exact t4Space_skeleton X n
  rw [← skeletonCocone_pt]
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
