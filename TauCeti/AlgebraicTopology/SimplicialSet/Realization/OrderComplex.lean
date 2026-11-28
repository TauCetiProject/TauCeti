/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map

/-!
# Comparing the realization of a poset nerve with its order complex

A simplex of the nerve of a preorder is a monotone chain, possibly with repetitions.
Push its barycentric coordinates to the vertices of the chain, adding the weights at
repeated vertices. The resulting affine maps agree under all simplex operators and
therefore induce a continuous comparison with the weak realization of the order complex.
For a partial order this comparison is a homeomorphism. Its inverse enumerates a face
in increasing order and uses the resulting simplex of the nerve; the face formula proves
continuity for the weak topology without any finiteness hypothesis on the partial order.

The comparison commutes with arbitrary monotone maps, including maps identifying vertices.
This identifies the two realizations of face posets used in barycentric subdivision.

The public API consists of `TauCeti.orderComplexRealizationMap`, its simplex computation
and naturality, `TauCeti.orderComplexRealizationHomeomorph`, and the inverse computation
`TauCeti.orderComplexRealizationHomeomorph_symm_apply_of_weights`.

The forward construction uses Mathlib's realization adjunction and `StdSimplex.map`.
The inverse uses `orderIsoFinOfMemOrderComplex` and `Finset.standardSimplexHomeomorph`
to parameterize each closed face, and `continuous_iff_faceInclusion` to check continuity.

The construction follows the usual barycentric description of realization; see
Goerss and Jardine, *Simplicial Homotopy Theory*, Chapter I, §2.
-/

public section

noncomputable section

open CategoryTheory Opposite Convexity
open scoped Simplicial
open TauCeti.AbstractSimplicialComplex
open AbstractSimplicialComplex
open TauCeti.SetLike

universe u

namespace TauCeti

variable {P Q : Type u} [Preorder P] [Preorder Q]

private def chainFace {n : ℕ} (x : (nerve P) _⦋n⦌) : Face (orderComplex P) := by
  classical
  refine ⟨Finset.univ.image x.obj, mem_orderComplex_iff.mpr ⟨?_, ?_⟩⟩
  · exact Finset.univ_nonempty.image _
  · simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      using x.monotone.isChain_range

private def chainSimplex {n : ℕ} (x : (nerve P) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) : Realization (orderComplex P) := by
  classical
  refine faceInclusion (orderComplex P) (chainFace x) ⟨(w.map x.obj).weights, ?_⟩
  rw [Finset.coe_image, mem_standardSimplex_iff]
  refine ⟨(w.map x.obj).nonneg, (w.map x.obj).total, ?_⟩
  exact (Finsupp.mapDomain_support).trans (Finset.image_mono _ (Finset.subset_univ _))

private lemma chainSimplex_val {n : ℕ} (x : (nerve P) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (chainSimplex x w).val = (w.map x.obj).weights := by
  simp [chainSimplex, faceInclusion_val]

private lemma continuous_chainSimplex {n : ℕ} (x : (nerve P) _⦋n⦌) :
    Continuous (chainSimplex x) := by
  classical
  let g : Fin (n + 1) → (chainFace x).val :=
    fun i => ⟨x.obj i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  convert (continuous_faceInclusion (orderComplex P) (chainFace x)).comp
    ((Finset.standardSimplexHomeomorph _).symm.continuous.comp
      (StdSimplex.continuous_map ℝ g)) using 1
  funext w
  apply Subtype.ext
  simp [chainSimplex_val, Finset.standardSimplexHomeomorph_symm_val,
    StdSimplex.weights_map, ← Finsupp.mapDomain_comp, g]

private def nerveToSingularOrderComplex (P : Type u) [Preorder P] :
    nerve P ⟶ TopCat.toSSet.obj (TopCat.of (Realization (orderComplex P))) where
  app n := ↾fun x => (TopCat.toSSetObjEquiv _ _).symm
    ⟨chainSimplex x, continuous_chainSimplex x⟩
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro w
    -- Unpack the concrete-category wrappers and the singular simplex equivalence.
    change chainSimplex ((nerve P).map θ x) w = chainSimplex x (w.map θ.unop)
    apply Subtype.ext
    rw [chainSimplex_val, chainSimplex_val]
    exact congrArg StdSimplex.weights (StdSimplex.map_comp w θ.unop x.obj)

/-- The continuous barycentric comparison from the realization of the nerve of a preorder
to the weak realization of its order complex. Repeated vertices have their weights added. -/
def orderComplexRealizationMap (P : Type u) [Preorder P] :
    SSet.toTop.obj (nerve P) ⟶ TopCat.of (Realization (orderComplex P)) :=
  (sSetTopAdj.homEquiv _ _).symm (nerveToSingularOrderComplex P)

/-- On a monotone chain the comparison pushes weights forward along its vertex function. -/
@[simp]
theorem orderComplexRealizationMap_toTopObjMk {n : ℕ} (x : (nerve P) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (orderComplexRealizationMap P (SSet.toTopObjMk x w)).val = (w.map x.obj).weights := by
  rw [orderComplexRealizationMap, SSet.apply_toTopObjMk, Equiv.apply_symm_apply]
  exact chainSimplex_val x w

/-- The comparison sends every vertex of a chain to the corresponding order-complex vertex. -/
@[simp]
theorem orderComplexRealizationMap_toTopObjMk_single {n : ℕ} (x : (nerve P) _⦋n⦌)
    (i : Fin (n + 1)) :
    orderComplexRealizationMap P (SSet.toTopObjMk x (StdSimplex.single i)) =
      vertex (orderComplex P) (x.obj i) := by
  apply Subtype.ext
  rw [orderComplexRealizationMap_toTopObjMk, StdSimplex.map_single, vertex_val]
  exact StdSimplex.weights_single _

/-- The comparison is natural under monotone maps, including maps identifying vertices. -/
@[reassoc, elementwise]
theorem orderComplexRealizationMap_naturality [DecidableEq Q] (f : P →o Q) :
    SSet.toTop.map (nerveMap f.toFunctor) ≫ orderComplexRealizationMap Q =
      orderComplexRealizationMap P ≫
        TopCat.ofHom (orderComplexMap f).realizationMap := by
  classical
  apply SSet.toTop_hom_ext
  intro n x w
  -- Evaluate the composite TopCat morphisms before comparing their coordinate vectors.
  change orderComplexRealizationMap Q
    (SSet.toTop.map (nerveMap f.toFunctor) (SSet.toTopObjMk x w)) =
      (orderComplexMap f).realizationMap
        (orderComplexRealizationMap P (SSet.toTopObjMk x w))
  apply Subtype.ext
  rw [SSet.toTop_map_toTopObjMk,
    PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
    orderComplexRealizationMap_toTopObjMk, orderComplexRealizationMap_toTopObjMk]
  simp only [coe_orderComplexMap, StdSimplex.weights_map, ← Finsupp.mapDomain_comp]
  apply congrArg (fun g => Finsupp.mapDomain g w.weights)
  funext i
  rw [nerveMap_app]
  exact (Functor.mapComposableArrows_obj_obj f.toFunctor n x i).trans
    (congrFun f.monotone.functor_obj (x.obj i))

section PartialOrder

variable {A : Type u} [PartialOrder A]

private def faceOrderIso (σ : Face (orderComplex A)) :
    Fin (σ.val.card - 1 + 1) ≃o σ.val := by
  classical
  exact (Fin.castOrderIso (Nat.sub_add_cancel
    (mem_orderComplex_iff.mp σ.property).1.card_pos)).trans
      (orderIsoFinOfMemOrderComplex σ.property)

private def faceChain (σ : Face (orderComplex A)) :
    (nerve A) _⦋σ.val.card - 1⦌ :=
  ((OrderEmbedding.subtype _).monotone.comp (faceOrderIso σ).monotone).functor

private def faceLift (σ : Face (orderComplex A)) :
    C(StandardSimplex σ.val, SSet.toTop.obj (nerve A)) :=
  ⟨fun y => SSet.toTopObjMk (faceChain σ)
    ((Finset.standardSimplexHomeomorph σ.val y).map (faceOrderIso σ).symm),
    (SSet.continuous_toTopObjMk _).comp
      ((StdSimplex.continuous_map ℝ _).comp
        (Finset.standardSimplexHomeomorph σ.val).continuous)⟩

private lemma comparison_faceLift (σ : Face (orderComplex A)) (y : StandardSimplex σ.val) :
    orderComplexRealizationMap A (faceLift σ y) = faceInclusion (orderComplex A) σ y := by
  apply Subtype.ext
  simp only [faceLift, ContinuousMap.coe_mk, faceInclusion_val]
  rw [orderComplexRealizationMap_toTopObjMk, ← StdSimplex.map_comp]
  have h : (faceChain σ).obj ∘ (faceOrderIso σ).symm = Subtype.val := by
    funext i
    exact congrArg Subtype.val ((faceOrderIso σ).apply_symm_apply i)
  rw [h, StdSimplex.weights_map, ← Finset.standardSimplexHomeomorph_symm_val,
    Homeomorph.symm_apply_apply]

private lemma faceLift_eq_toTopObjMk {n : ℕ} (σ : Face (orderComplex A))
    (v : Fin (n + 1) →o σ.val)
    (w : StdSimplex ℝ (Fin (n + 1))) (y : StandardSimplex σ.val)
    (hy : y.val = (w.map (Subtype.val ∘ v)).weights) :
    faceLift σ y = SSet.toTopObjMk
      ((OrderEmbedding.subtype _).monotone.comp v.monotone).functor w := by
  classical
  let θ : ⦋n⦌ ⟶ ⦋σ.val.card - 1⦌ := SimplexCategory.mkHom
    ⟨(faceOrderIso σ).symm ∘ v, (faceOrderIso σ).symm.monotone.comp v.monotone⟩
  have hθ : (nerve A).map θ.op (faceChain σ) =
      ((OrderEmbedding.subtype _).monotone.comp v.monotone).functor := by
    apply nerve.ext_of_isThin
    funext i
    exact congrArg Subtype.val ((faceOrderIso σ).apply_symm_apply (v i))
  have hy' : Finset.standardSimplexHomeomorph σ.val y = w.map v := by
    apply StdSimplex.ext
    apply Finsupp.mapDomain_injective Subtype.val_injective
    rw [← Finset.standardSimplexHomeomorph_symm_val, Homeomorph.symm_apply_apply,
      StdSimplex.weights_map, ← Finsupp.mapDomain_comp]
    exact hy
  have hw : ((Finset.standardSimplexHomeomorph σ.val y).map (faceOrderIso σ).symm) =
      w.map θ := by
    rw [hy', StdSimplex.map_map]
    -- SimplexCategory.mkHom gives θ the underlying function (faceOrderIso σ).symm ∘ v.
    rfl
  exact (congrArg (SSet.toTopObjMk (faceChain σ)) hw).trans
    ((SSet.toTopObjMk_map θ (faceChain σ) w).symm.trans
      (congrArg (fun z => SSet.toTopObjMk z w) hθ))

private lemma faceLift_mono (σ τ : Face (orderComplex A)) (h : σ.val ⊆ τ.val)
    (y : StandardSimplex σ.val) :
    faceLift τ ⟨y.val, by
      classical
      exact convexHull_mono (Finset.coe_subset.mpr (Finset.image_mono _ h)) y.property⟩ =
        faceLift σ y := by
  have hy := congrArg Subtype.val (comparison_faceLift σ y)
  rw [faceInclusion_val] at hy
  have hw := hy.symm.trans (orderComplexRealizationMap_toTopObjMk (faceChain σ)
    ((Finset.standardSimplexHomeomorph σ.val y).map (faceOrderIso σ).symm))
  let v : Fin (σ.val.card - 1 + 1) →o τ.val :=
    ⟨fun i => ⟨faceOrderIso σ i, h (faceOrderIso σ i).property⟩,
      fun _ _ hij => (faceOrderIso σ).monotone hij⟩
  exact faceLift_eq_toTopObjMk τ v _ _ hw

private def inverseComparison (A : Type u) [PartialOrder A]
    (y : Realization (orderComplex A)) : SSet.toTop.obj (nerve A) :=
  faceLift (carrier (orderComplex A) y) ⟨y.val, mem_convexHull_carrier _ y⟩

private lemma inverseComparison_faceInclusion (σ : Face (orderComplex A))
    (y : StandardSimplex σ.val) :
    inverseComparison A (faceInclusion (orderComplex A) σ y) = faceLift σ y := by
  have h := faceLift_mono (carrier _ (faceInclusion _ σ y)) σ
    (by simpa only [carrier_val, faceInclusion_val] using StandardSimplex.support_subset y)
    ⟨(faceInclusion _ σ y).val, mem_convexHull_carrier _ _⟩
  simpa only [inverseComparison, faceInclusion_val] using h.symm

private lemma continuous_inverseComparison : Continuous (inverseComparison A) := by
  apply continuous_iff_faceInclusion.mpr
  intro σ
  exact (faceLift σ).continuous.congr (fun y => (inverseComparison_faceInclusion σ y).symm)

private lemma comparison_inverseComparison (y : Realization (orderComplex A)) :
    orderComplexRealizationMap A (inverseComparison A y) = y := by
  exact (comparison_faceLift _ _).trans (faceInclusion_mk_val _ _ _ _)

private lemma inverseComparison_chainSimplex {n : ℕ} (x : (nerve A) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    inverseComparison A (chainSimplex x w) = SSet.toTopObjMk x w := by
  classical
  rw [chainSimplex, inverseComparison_faceInclusion]
  let v : Fin (n + 1) →o (chainFace x).val :=
    ⟨fun i => ⟨x.obj i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩, x.monotone⟩
  have hx : ((OrderEmbedding.subtype _).monotone.comp v.monotone).functor = x := by
    apply nerve.ext_of_isThin (C := A) (n := op ⦋n⦌)
    rw [Monotone.functor_obj]
    exact congrArg (fun g => Subtype.val ∘ g) (OrderHom.coe_mk _ _)
  exact (faceLift_eq_toTopObjMk (chainFace x) v w _ rfl).trans
    (congrArg (fun z => SSet.toTopObjMk z w) hx)

/-- The realization of the nerve of a partial order is canonically homeomorphic to the
weak realization of its order complex. The inverse enumerates the finite support increasingly. -/
def orderComplexRealizationHomeomorph (A : Type u) [PartialOrder A] :
    SSet.toTop.obj (nerve A) ≃ₜ Realization (orderComplex A) where
  toFun := orderComplexRealizationMap A
  invFun := inverseComparison A
  left_inv := by
    have h : orderComplexRealizationMap A ≫
        TopCat.ofHom ⟨inverseComparison A, continuous_inverseComparison⟩ = 𝟙 _ := by
      apply SSet.toTop_hom_ext
      intro n x w
      -- Evaluate the TopCat composition to use the simplex formulas.
      change inverseComparison A (orderComplexRealizationMap A (SSet.toTopObjMk x w)) = _
      have hx : orderComplexRealizationMap A (SSet.toTopObjMk x w) = chainSimplex x w :=
        Subtype.ext ((orderComplexRealizationMap_toTopObjMk x w).trans
          (chainSimplex_val x w).symm)
      rw [hx]
      exact inverseComparison_chainSimplex x w
    exact fun y => ConcreteCategory.congr_hom h y
  right_inv := comparison_inverseComparison
  continuous_toFun := (orderComplexRealizationMap A).hom.continuous
  continuous_invFun := continuous_inverseComparison

/-- The homeomorphism has the canonical barycentric comparison as its forward map. -/
@[simp]
theorem orderComplexRealizationHomeomorph_apply (y : SSet.toTop.obj (nerve A)) :
    orderComplexRealizationHomeomorph A y = orderComplexRealizationMap A y := (rfl)

/-- A realization point with the weights of a chain is sent back to that chain's
realization point, regardless of repetitions or zero weights. -/
theorem orderComplexRealizationHomeomorph_symm_apply_of_weights {n : ℕ}
    (x : (nerve A) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1)))
    (y : Realization (orderComplex A)) (hy : y.val = (w.map x.obj).weights) :
    (orderComplexRealizationHomeomorph A).symm y = SSet.toTopObjMk x w := by
  apply (orderComplexRealizationHomeomorph A).injective
  rw [Homeomorph.apply_symm_apply, orderComplexRealizationHomeomorph_apply]
  exact Subtype.ext (hy.trans (orderComplexRealizationMap_toTopObjMk x w).symm)

end PartialOrder

end TauCeti
