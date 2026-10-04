/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Order.Fin.Tuple
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.TensorDifferential
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The shuffle map

Let `C` be a preadditive monoidal category with `w`-small coproducts, in which tensoring on either
side preserves `w`-small coproducts (for instance `ModuleCat k`).  For simplicial sets `K` and `L`
and objects `R` and `S` of `C`, the shuffle map of Eilenberg and Mac Lane is the morphism of chain
complexes `SSet.shuffle K L R S` from `K.chainComplex R ⊗ L.chainComplex S`, the tensor product of
the simplicial chains of the factors, to `(K ⊗ L).chainComplex (R ⊗ S)`, the simplicial chains of
the product `K × L`.  The tensor product of chain complexes is Mathlib's monoidal structure on
`ChainComplex C ℕ`, whose differential is `d (a ⊗ b) = d a ⊗ b + (-1)^p a ⊗ d b` for `a` of
degree `p`.  The shuffle map is the other half, besides the Alexander–Whitney map
`SSet.alexanderWhitney`, of the Eilenberg–Zilber comparison between chains on a product and tensor
products of chains.

The shuffle map is first constructed on the standard simplices.  The shuffle chain
`SSet.shuffleChain T p q (p + q)` is a `(p + q)`-chain of `Δ[p] ⊗ Δ[q]` with coefficients in `T`.
Unwinding its recursion, it is the signed sum of the nondegenerate `(p + q)`-simplices of
`Δ[p] ⊗ Δ[q]`: the monotone lattice paths from `(0, 0)` to `(p, q)`, each with the sign
`(-1)^N`, where `N` counts the pairs of a vertical step followed, later on the path, by a
horizontal step.  Here a path is built from its first step: either a horizontal step `(0, 0) →
(1, 0)` followed by a path from `(1, 0)`, or a vertical step `(0, 0) → (0, 1)` followed by a path
from `(0, 1)` with the sign `(-1)^p`.  The two cases are the cone from `(0, 0)`
(`SSet.stdSimplex.prodConeChain`) on the shuffle chains of `Δ[p - 1] ⊗ Δ[q]` and `Δ[p] ⊗ Δ[q - 1]`,
pushed along the zeroth face maps.  The shuffle map then sends the summand of a `p`-simplex `x` of
`K` and a `q`-simplex `y` of `L` to the image of the shuffle chain under the map
`Δ[p] ⊗ Δ[q] ⟶ K ⊗ L` classifying `(x, y)` (`SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f`).
This is the classical formula `x ⊗ y ↦ ∑ ± (s_ν x, s_μ y)` over the `(p, q)`-shuffles `(μ, ν)`,
although this file works with the recursion and does not state that closed formula.

The boundary of the cone is `∂ (c σ) = σ - c (∂ σ)` in positive degrees
(`SSet.stdSimplex.prodConeChain_d`).  An induction on the degree then shows that the boundary of
the shuffle chain is the alternating sum of its faces in the first factor plus `(-1)^p` times the
alternating sum of its faces in the second factor, which is exactly the statement that the shuffle
map is a morphism of chain complexes.

## Main definitions and results

* `SSet.stdSimplex.prodConeChain`: the cone from the vertex `(0, 0)` on the simplicial chains of
  `Δ[a] ⊗ Δ[b]`, with `SSet.stdSimplex.prodConeChain_d` its boundary formula.
* `SSet.shuffleChain`: the shuffle chain of `Δ[p] ⊗ Δ[q]`, with its defining recursion
  `SSet.shuffleChain_zero_zero`, `SSet.shuffleChain_succ_zero`, `SSet.shuffleChain_zero_succ` and
  `SSet.shuffleChain_succ_succ`, its boundary formula `SSet.shuffleChain_d_succ_succ`,
  `SSet.shuffleChain_d_succ_zero` and `SSet.shuffleChain_d_zero_succ`, and its naturality in the
  coefficient object.
* `SSet.shuffle`: the shuffle map, a morphism of chain complexes.
* `SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f`: its value on the summand of a pair of
  simplices, and `SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero` in degree zero.
* `SSet.shuffle_naturality`: it is natural in both simplicial sets.
* `SSet.shuffle_coefficient_naturality`: it is natural in both coefficient objects.

## References

* S. Eilenberg and S. Mac Lane, *On the groups `H(Π, n)`, I*, Ann. of Math. 58 (1953).
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex
open TauCeti.SSet (chainComplexMap_f_comp chainComplexMap_f_comp_assoc
  chainComplexMap_f_chainComplexFunctor_map_app_f
  chainComplexMap_f_chainComplexFunctor_map_app_f_assoc)

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

namespace stdSimplex

/-- The cone from the vertex `0` on a simplex `x` of the standard simplex `Δ[a]`: the simplex
whose vertices are `0, x 0, …, x m`. -/
def cone {a m : ℕ} (x : (Δ[a] : SSet.{w}) _⦋m⦌) : (Δ[a] : SSet.{w}) _⦋m + 1⦌ :=
  objMk ⟨Matrix.vecCons 0 x, (monotone_apply x).vecCons (Fin.zero_le _)⟩

@[simp]
lemma cone_apply_zero {a m : ℕ} (x : (Δ[a] : SSet.{w}) _⦋m⦌) : cone x 0 = 0 := (rfl)

@[simp]
lemma cone_apply_succ {a m : ℕ} (x : (Δ[a] : SSet.{w}) _⦋m⦌) (i : Fin (m + 1)) :
    cone x i.succ = x i := (rfl)

/-- The zeroth face of the cone on `x` is `x`. -/
@[simp]
lemma δ_zero_cone {a m : ℕ} (x : (Δ[a] : SSet.{w}) _⦋m⦌) : Δ[a].δ 0 (cone x) = x := by
  ext j
  simp [δ_apply]

/-- The `(i + 1)`-st face of the cone on `x` is the cone on the `i`-th face of `x`. -/
@[simp]
lemma δ_succ_cone {a m : ℕ} (x : (Δ[a] : SSet.{w}) _⦋m + 1⦌) (i : Fin (m + 2)) :
    Δ[a].δ i.succ (cone x) = cone (Δ[a].δ i x) := by
  ext j
  cases j using Fin.cases with
  | zero => simp [δ_apply]
  | succ j => simp [δ_apply, Fin.succ_succAbove_succ]

/-- A map of standard simplices which fixes the vertex `0` commutes with cones. -/
lemma map_cone {a b m : ℕ} (g : ⦋a⦌ ⟶ ⦋b⦌) (hg : g.toOrderHom 0 = 0)
    (x : (Δ[a] : SSet.{w}) _⦋m⦌) :
    (stdSimplex.map g).app _ (cone x) = cone ((stdSimplex.map g).app _ x) := by
  ext j
  cases j using Fin.cases with
  | zero => exact congrArg Fin.val hg
  -- both sides are `g` evaluated at the vertex `x j`
  | succ j => rfl

/-- The cone from the vertex `(0, 0)` on a simplex of the product `Δ[a] ⊗ Δ[b]`. -/
def prodCone {a b m : ℕ} (x : ((Δ[a] : SSet.{w}) ⊗ Δ[b]) _⦋m⦌) :
    ((Δ[a] : SSet.{w}) ⊗ Δ[b]) _⦋m + 1⦌ :=
  (cone x.1, cone x.2)

/-- The zeroth face of the cone on a simplex `x` of `Δ[a] ⊗ Δ[b]` is `x`. -/
lemma δ_zero_prodCone {a b m : ℕ} (x : ((Δ[a] : SSet.{w}) ⊗ Δ[b]) _⦋m⦌) :
    ((Δ[a] : SSet.{w}) ⊗ Δ[b]).δ 0 (prodCone x) = x :=
  Prod.ext (δ_zero_cone _) (δ_zero_cone _)

/-- The `(i + 1)`-st face of the cone on a simplex `x` of `Δ[a] ⊗ Δ[b]` is the cone on the `i`-th
face of `x`. -/
lemma δ_succ_prodCone {a b m : ℕ} (x : ((Δ[a] : SSet.{w}) ⊗ Δ[b]) _⦋m + 1⦌) (i : Fin (m + 2)) :
    ((Δ[a] : SSet.{w}) ⊗ Δ[b]).δ i.succ (prodCone x) =
      prodCone (((Δ[a] : SSet.{w}) ⊗ Δ[b]).δ i x) :=
  Prod.ext (δ_succ_cone _ _) (δ_succ_cone _ _)

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

variable (a b : ℕ) (T : C)

/-- The cone from the vertex `(0, 0)`, as a map raising the degree of the simplicial chains of
`Δ[a] ⊗ Δ[b]` by one.  It is a contracting homotopy in positive degrees
(`SSet.stdSimplex.prodConeChain_d`). -/
def prodConeChain (m : ℕ) :
    (((Δ[a] : SSet.{w}) ⊗ Δ[b]).chainComplex T).X m ⟶
      (((Δ[a] : SSet.{w}) ⊗ Δ[b]).chainComplex T).X (m + 1) :=
  Cofan.IsColimit.desc (isColimitChainComplexXCofan _ T m) fun x ↦
    ((Δ[a] : SSet.{w}) ⊗ Δ[b]).ιChainComplex (prodCone x)

@[reassoc (attr := simp)]
lemma ιChainComplex_prodConeChain {m : ℕ} (x : ((Δ[a] : SSet.{w}) ⊗ Δ[b]) _⦋m⦌) :
    ((Δ[a] : SSet.{w}) ⊗ Δ[b]).ιChainComplex (R := T) x ≫ prodConeChain a b T m =
      ((Δ[a] : SSet.{w}) ⊗ Δ[b]).ιChainComplex (prodCone x) :=
  Cofan.IsColimit.fac _ _ x

/-- The cone on the simplicial chains of `Δ[a] ⊗ Δ[b]` is a contracting homotopy in positive
degrees: `∂ (c ∘ σ) = σ - c ∘ ∂ σ` for a chain `σ` of positive degree. -/
lemma prodConeChain_d (m : ℕ) :
    prodConeChain a b T (m + 1) ≫
        (((Δ[a] : SSet.{w}) ⊗ Δ[b]).chainComplex T).d (m + 1 + 1) (m + 1) =
      𝟙 _ - (((Δ[a] : SSet.{w}) ⊗ Δ[b]).chainComplex T).d (m + 1) m ≫ prodConeChain a b T m := by
  ext x
  simp only [ιChainComplex_prodConeChain_assoc, ιChainComplex_d, Preadditive.comp_sub,
    Category.comp_id, ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ιChainComplex_prodConeChain]
  rw [Fin.sum_univ_succ, δ_zero_prodCone, Fin.val_zero, pow_zero, one_smul]
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    sub_eq_add_neg]
  refine congrArg (_ + ·) (congrArg Neg.neg (Finset.sum_congr rfl fun i _ ↦ ?_))
  rw [δ_succ_prodCone]

variable {a b} in
/-- A map of products of standard simplices which commutes with the cones commutes with the
cone on simplicial chains. -/
@[reassoc]
lemma chainComplexMap_f_prodConeChain {a' b' : ℕ}
    (f : (Δ[a] : SSet.{w}) ⊗ Δ[b] ⟶ (Δ[a'] : SSet.{w}) ⊗ Δ[b'])
    (hf : ∀ (m : ℕ) (x : ((Δ[a] : SSet.{w}) ⊗ Δ[b]) _⦋m⦌),
      f.app _ (prodCone x) = prodCone (f.app _ x)) (m : ℕ) :
    (chainComplexMap f T).f m ≫ prodConeChain a' b' T m =
      prodConeChain a b T m ≫ (chainComplexMap f T).f (m + 1) := by
  ext x
  simp only [ι_chainComplexMap_f_assoc]
  rw [ιChainComplex_prodConeChain, ιChainComplex_prodConeChain_assoc, ι_chainComplexMap_f, hf]

/-- The cone on simplicial chains of `Δ[a] ⊗ Δ[b]` is natural in the coefficient object. -/
@[reassoc]
lemma prodConeChain_chainComplexFunctor_map_app_f {T' : C} (u : T ⟶ T') (m : ℕ) :
    prodConeChain a b T m ≫
        (((chainComplexFunctor C).map u).app ((Δ[a] : SSet.{w}) ⊗ Δ[b])).f (m + 1) =
      (((chainComplexFunctor C).map u).app ((Δ[a] : SSet.{w}) ⊗ Δ[b])).f m ≫
        prodConeChain a b T' m := by
  ext x
  rw [ιChainComplex_prodConeChain_assoc,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc, ιChainComplex_prodConeChain]

end Chain

end stdSimplex

section ShuffleChain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (T : C)

open stdSimplex

private lemma whiskerRight_app_prodCone {p q : ℕ} (k : Fin (p + 1)) {m : ℕ}
    (x : ((Δ[p] : SSet.{w}) ⊗ Δ[q]) _⦋m⦌) :
    (stdSimplex.δ k.succ ▷ (Δ[q] : SSet.{w})).app _ (prodCone x) =
      prodCone ((stdSimplex.δ k.succ ▷ (Δ[q] : SSet.{w})).app _ x) :=
  -- a whiskered map acts on the components of a simplex of a product separately
  Prod.ext (map_cone (SimplexCategory.δ k.succ) (Fin.succ_succAbove_zero k) x.1) rfl

private lemma whiskerLeft_app_prodCone {p q : ℕ} (k : Fin (q + 1)) {m : ℕ}
    (x : ((Δ[p] : SSet.{w}) ⊗ Δ[q]) _⦋m⦌) :
    ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ k.succ).app _ (prodCone x) =
      prodCone (((Δ[p] : SSet.{w}) ◁ stdSimplex.δ k.succ).app _ x) :=
  -- a whiskered map acts on the components of a simplex of a product separately
  Prod.ext rfl (map_cone (SimplexCategory.δ k.succ) (Fin.succ_succAbove_zero k) x.2)

/-- The step adding a first horizontal edge: the face `δ 0` in the first factor followed by the
cone from `(0, 0)`. -/
private def hStep (p q n : ℕ) :
    (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n ⟶
      (((Δ[p + 1] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X (n + 1) :=
  (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q] : SSet.{w})) T).f n ≫ prodConeChain (p + 1) q T n

/-- The step adding a first vertical edge: the face `δ 0` in the second factor followed by the
cone from `(0, 0)`. -/
private def vStep (p q n : ℕ) :
    (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n ⟶
      (((Δ[p] : SSet.{w}) ⊗ Δ[q + 1]).chainComplex T).X (n + 1) :=
  (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ 0) T).f n ≫ prodConeChain p (q + 1) T n

/-- The alternating sum of the faces in the first factor. -/
private def xFaces (p q n : ℕ) :
    (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n ⟶
      (((Δ[p + 1] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    (chainComplexMap (stdSimplex.δ j ▷ (Δ[q] : SSet.{w})) T).f n

/-- The alternating sum of the faces in the second factor. -/
private def yFaces (p q n : ℕ) :
    (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n ⟶
      (((Δ[p] : SSet.{w}) ⊗ Δ[q + 1]).chainComplex T).X n :=
  ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
    (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ j) T).f n

private lemma hStep_d (p q n : ℕ) :
    hStep T p q (n + 1) ≫ (((Δ[p + 1] : SSet.{w}) ⊗ Δ[q]).chainComplex T).d (n + 1 + 1) (n + 1) =
      (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q] : SSet.{w})) T).f (n + 1) -
        (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).d (n + 1) n ≫ hStep T p q n := by
  rw [hStep, hStep, Category.assoc, prodConeChain_d, Preadditive.comp_sub, Category.comp_id,
    (chainComplexMap _ T).comm_assoc]

private lemma vStep_d (p q n : ℕ) :
    vStep T p q (n + 1) ≫ (((Δ[p] : SSet.{w}) ⊗ Δ[q + 1]).chainComplex T).d (n + 1 + 1) (n + 1) =
      (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ 0) T).f (n + 1) -
        (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).d (n + 1) n ≫ vStep T p q n := by
  rw [vStep, vStep, Category.assoc, prodConeChain_d, Preadditive.comp_sub, Category.comp_id,
    (chainComplexMap _ T).comm_assoc]

private lemma hStep_whiskerRight_succ (p q n : ℕ) (k : Fin (p + 2)) :
    hStep T p q n ≫ (chainComplexMap (stdSimplex.δ k.succ ▷ (Δ[q] : SSet.{w})) T).f (n + 1) =
      (chainComplexMap (stdSimplex.δ k ▷ (Δ[q] : SSet.{w})) T).f n ≫ hStep T (p + 1) q n := by
  rw [hStep, hStep, Category.assoc, ← chainComplexMap_f_prodConeChain _ _
      (fun _ x ↦ whiskerRight_app_prodCone k x),
    chainComplexMap_f_comp_assoc, chainComplexMap_f_comp_assoc, ← comp_whiskerRight,
    ← comp_whiskerRight, stdSimplex.δ_comp_δ (Fin.zero_le k), Fin.castSucc_zero]

private lemma hStep_whiskerLeft_succ (p q n : ℕ) (k : Fin (q + 1)) :
    hStep T p q n ≫ (chainComplexMap ((Δ[p + 1] : SSet.{w}) ◁ stdSimplex.δ k.succ) T).f (n + 1) =
      (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ k.succ) T).f n ≫
        hStep T p (q + 1) n := by
  rw [hStep, hStep, Category.assoc, ← chainComplexMap_f_prodConeChain _ _
      (fun _ x ↦ whiskerLeft_app_prodCone k x),
    chainComplexMap_f_comp_assoc, chainComplexMap_f_comp_assoc, whisker_exchange]

private lemma vStep_whiskerLeft_succ (p q n : ℕ) (k : Fin (q + 2)) :
    vStep T p q n ≫ (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ k.succ) T).f (n + 1) =
      (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ k) T).f n ≫ vStep T p (q + 1) n := by
  rw [vStep, vStep, Category.assoc, ← chainComplexMap_f_prodConeChain _ _
      (fun _ x ↦ whiskerLeft_app_prodCone k x),
    chainComplexMap_f_comp_assoc, chainComplexMap_f_comp_assoc, ← whiskerLeft_comp,
    ← whiskerLeft_comp, stdSimplex.δ_comp_δ (Fin.zero_le k), Fin.castSucc_zero]

private lemma vStep_whiskerRight_succ (p q n : ℕ) (k : Fin (p + 1)) :
    vStep T p q n ≫ (chainComplexMap (stdSimplex.δ k.succ ▷ (Δ[q + 1] : SSet.{w})) T).f (n + 1) =
      (chainComplexMap (stdSimplex.δ k.succ ▷ (Δ[q] : SSet.{w})) T).f n ≫
        vStep T (p + 1) q n := by
  rw [vStep, vStep, Category.assoc, ← chainComplexMap_f_prodConeChain _ _
      (fun _ x ↦ whiskerRight_app_prodCone k x),
    chainComplexMap_f_comp_assoc, chainComplexMap_f_comp_assoc, ← whisker_exchange]

/-- The first horizontal edge followed by the first vertical face is the first vertical edge
followed by the first horizontal face: both send a simplex `σ` to the cone on `σ` shifted
diagonally. -/
@[reassoc]
private lemma whiskerLeft_hStep (p q n : ℕ) :
    (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ 0) T).f n ≫ hStep T p (q + 1) n =
      (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q] : SSet.{w})) T).f n ≫ vStep T (p + 1) q n := by
  rw [hStep, vStep, chainComplexMap_f_comp_assoc, chainComplexMap_f_comp_assoc, whisker_exchange]

@[reassoc]
private lemma hStep_xFaces (p q n : ℕ) :
    hStep T p q n ≫ xFaces T (p + 1) q (n + 1) =
      hStep T p q n ≫ (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q] : SSet.{w})) T).f (n + 1) -
        xFaces T p q n ≫ hStep T (p + 1) q n := by
  rw [xFaces, xFaces, Fin.sum_univ_succ, Preadditive.comp_add, Preadditive.comp_sum,
    Preadditive.sum_comp]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Preadditive.comp_neg, Preadditive.comp_zsmul, Preadditive.zsmul_comp, hStep_whiskerRight_succ,
    Finset.sum_neg_distrib, sub_eq_add_neg]

@[reassoc]
private lemma vStep_yFaces (p q n : ℕ) :
    vStep T p q n ≫ yFaces T p (q + 1) (n + 1) =
      vStep T p q n ≫ (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ 0) T).f (n + 1) -
        yFaces T p q n ≫ vStep T p (q + 1) n := by
  rw [yFaces, yFaces, Fin.sum_univ_succ, Preadditive.comp_add, Preadditive.comp_sum,
    Preadditive.sum_comp]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Preadditive.comp_neg, Preadditive.comp_zsmul, Preadditive.zsmul_comp, vStep_whiskerLeft_succ,
    Finset.sum_neg_distrib, sub_eq_add_neg]

@[reassoc]
private lemma hStep_yFaces (p q n : ℕ) :
    hStep T p q n ≫ yFaces T (p + 1) q (n + 1) =
      hStep T p q n ≫ (chainComplexMap ((Δ[p + 1] : SSet.{w}) ◁ stdSimplex.δ 0) T).f (n + 1) +
        yFaces T p q n ≫ hStep T p (q + 1) n -
        (chainComplexMap ((Δ[p] : SSet.{w}) ◁ stdSimplex.δ 0) T).f n ≫ hStep T p (q + 1) n := by
  rw [yFaces, yFaces, Preadditive.comp_sum, Preadditive.sum_comp]
  simp only [Fin.sum_univ_succ (n := q + 1), Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, hStep_whiskerLeft_succ]
  abel

@[reassoc]
private lemma vStep_xFaces (p q n : ℕ) :
    vStep T p q n ≫ xFaces T p (q + 1) (n + 1) =
      vStep T p q n ≫ (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q + 1] : SSet.{w})) T).f (n + 1) +
        xFaces T p q n ≫ vStep T (p + 1) q n -
        (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q] : SSet.{w})) T).f n ≫ vStep T (p + 1) q n := by
  rw [xFaces, xFaces, Preadditive.comp_sum, Preadditive.sum_comp]
  simp only [Fin.sum_univ_succ (n := p + 1), Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, vStep_whiskerRight_succ]
  abel

/-- The unique vertex of `Δ[0] ⊗ Δ[0]`. -/
private def vertex : ((Δ[0] : SSet.{w}) ⊗ Δ[0]) _⦋0⦌ := (yonedaEquiv (𝟙 _), yonedaEquiv (𝟙 _))

private lemma eq_vertex (x : ((Δ[0] : SSet.{w}) ⊗ Δ[0]) _⦋0⦌) : x = vertex :=
  Prod.ext (stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)
    (stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)

/-- **The shuffle chain** of `Δ[p] ⊗ Δ[q]` with coefficients in `T`, a chain of degree
`n = p + q`.  It is defined by recursion on the first step of a lattice path from `(0, 0)` to
`(p, q)`: the shuffle chain of `Δ[0] ⊗ Δ[0]` is its unique vertex (`SSet.shuffleChain_zero_zero`),
and otherwise it is the cone from `(0, 0)` on the shuffle chain of `Δ[p - 1] ⊗ Δ[q]` pushed along
the zeroth face `Δ[p - 1] ⟶ Δ[p]`, plus `(-1)^p` times the cone on the shuffle chain of
`Δ[p] ⊗ Δ[q - 1]` pushed along the zeroth face `Δ[q - 1] ⟶ Δ[q]`, where a term is absent when the
corresponding index is zero (`SSet.shuffleChain_succ_zero`, `SSet.shuffleChain_zero_succ` and
`SSet.shuffleChain_succ_succ`). -/
def shuffleChain : (p q n : ℕ) → p + q = n →
    (T ⟶ (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n)
  | 0, 0, 0, _ => ((Δ[0] : SSet.{w}) ⊗ Δ[0]).ιChainComplex vertex
  | p + 1, 0, n + 1, _ => shuffleChain p 0 n (by omega) ≫
      (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[0] : SSet.{w})) T).f n ≫ prodConeChain (p + 1) 0 T n
  | 0, q + 1, n + 1, _ => shuffleChain 0 q n (by omega) ≫
      (chainComplexMap ((Δ[0] : SSet.{w}) ◁ stdSimplex.δ 0) T).f n ≫ prodConeChain 0 (q + 1) T n
  | p + 1, q + 1, n + 1, _ =>
      shuffleChain p (q + 1) n (by omega) ≫
          (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q + 1] : SSet.{w})) T).f n ≫
            prodConeChain (p + 1) (q + 1) T n +
        (-1 : ℤ) ^ (p + 1) • shuffleChain (p + 1) q n (by omega) ≫
          (chainComplexMap ((Δ[p + 1] : SSet.{w}) ◁ stdSimplex.δ 0) T).f n ≫
            prodConeChain (p + 1) (q + 1) T n
  | 0, 0, _ + 1, h | _ + 1, _, 0, h | 0, _ + 1, 0, h => absurd h (by omega)

variable {T} in
/-- The shuffle chain is natural in the coefficient object. -/
@[reassoc]
lemma shuffleChain_chainComplexFunctor_map_app_f {T' : C} (u : T ⟶ T') :
    ∀ (p q n : ℕ) (h : p + q = n), shuffleChain T p q n h ≫
        (((chainComplexFunctor C).map u).app ((Δ[p] : SSet.{w}) ⊗ Δ[q])).f n =
      u ≫ shuffleChain T' p q n h
  | 0, 0, 0, _ => by
    rw [shuffleChain, shuffleChain, TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f]
  | p + 1, 0, n + 1, _ => by
    simp only [shuffleChain, Category.assoc, prodConeChain_chainComplexFunctor_map_app_f,
      chainComplexMap_f_chainComplexFunctor_map_app_f_assoc,
      reassoc_of% (shuffleChain_chainComplexFunctor_map_app_f u p 0 n (by omega))]
  | 0, q + 1, n + 1, _ => by
    simp only [shuffleChain, Category.assoc, prodConeChain_chainComplexFunctor_map_app_f,
      chainComplexMap_f_chainComplexFunctor_map_app_f_assoc,
      reassoc_of% (shuffleChain_chainComplexFunctor_map_app_f u 0 q n (by omega))]
  | p + 1, q + 1, n + 1, _ => by
    simp only [shuffleChain, Category.assoc, Preadditive.add_comp, Preadditive.zsmul_comp,
      Preadditive.comp_add, Preadditive.comp_zsmul, prodConeChain_chainComplexFunctor_map_app_f,
      chainComplexMap_f_chainComplexFunctor_map_app_f_assoc,
      reassoc_of% (shuffleChain_chainComplexFunctor_map_app_f u p (q + 1) n (by omega)),
      reassoc_of% (shuffleChain_chainComplexFunctor_map_app_f u (p + 1) q n (by omega))]
  | 0, 0, _ + 1, h | _ + 1, _, 0, h | 0, _ + 1, 0, h => absurd h (by omega)

/-- The shuffle chain of `Δ[0] ⊗ Δ[0]` is its unique vertex. -/
lemma shuffleChain_zero_zero (h : 0 + 0 = 0) (x : ((Δ[0] : SSet.{w}) ⊗ Δ[0]) _⦋0⦌) :
    shuffleChain T 0 0 0 h = ((Δ[0] : SSet.{w}) ⊗ Δ[0]).ιChainComplex x := by
  rw [shuffleChain, eq_vertex x]

/-- The shuffle chain of `Δ[p + 1] ⊗ Δ[0]` is the cone on the shuffle chain of `Δ[p] ⊗ Δ[0]`,
pushed along the zeroth face of `Δ[p + 1]`. -/
lemma shuffleChain_succ_zero (p n : ℕ) (h : p + 1 + 0 = n + 1) :
    shuffleChain T (p + 1) 0 (n + 1) h = shuffleChain T p 0 n (by omega) ≫
      (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[0] : SSet.{w})) T).f n ≫
        prodConeChain (p + 1) 0 T n := by
  rw [shuffleChain]

/-- The shuffle chain of `Δ[0] ⊗ Δ[q + 1]` is the cone on the shuffle chain of `Δ[0] ⊗ Δ[q]`,
pushed along the zeroth face of `Δ[q + 1]`. -/
lemma shuffleChain_zero_succ (q n : ℕ) (h : 0 + (q + 1) = n + 1) :
    shuffleChain T 0 (q + 1) (n + 1) h = shuffleChain T 0 q n (by omega) ≫
      (chainComplexMap ((Δ[0] : SSet.{w}) ◁ stdSimplex.δ 0) T).f n ≫
        prodConeChain 0 (q + 1) T n := by
  rw [shuffleChain]

/-- The shuffle chain of `Δ[p + 1] ⊗ Δ[q + 1]` is the cone on the shuffle chain of
`Δ[p] ⊗ Δ[q + 1]` pushed along the zeroth face of `Δ[p + 1]`, plus `(-1)^(p + 1)` times the cone on
the shuffle chain of `Δ[p + 1] ⊗ Δ[q]` pushed along the zeroth face of `Δ[q + 1]`. -/
lemma shuffleChain_succ_succ (p q n : ℕ) (h : p + 1 + (q + 1) = n + 1) :
    shuffleChain T (p + 1) (q + 1) (n + 1) h =
      shuffleChain T p (q + 1) n (by omega) ≫
          (chainComplexMap (stdSimplex.δ 0 ▷ (Δ[q + 1] : SSet.{w})) T).f n ≫
            prodConeChain (p + 1) (q + 1) T n +
        (-1 : ℤ) ^ (p + 1) • shuffleChain T (p + 1) q n (by omega) ≫
          (chainComplexMap ((Δ[p + 1] : SSet.{w}) ◁ stdSimplex.δ 0) T).f n ≫
            prodConeChain (p + 1) (q + 1) T n := by
  rw [shuffleChain]

/-- The faces of the shuffle chain in the first factor. -/
private def xFace : (p q n : ℕ) → p + q = n + 1 →
    (T ⟶ (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n)
  | 0, _, _, _ => 0
  | p + 1, q, n, h => shuffleChain T p q n (by omega) ≫ xFaces T p q n

/-- The faces of the shuffle chain in the second factor. -/
private def yFace : (p q n : ℕ) → p + q = n + 1 →
    (T ⟶ (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).X n)
  | _, 0, _, _ => 0
  | p, q + 1, n, h => shuffleChain T p q n (by omega) ≫ yFaces T p q n

private lemma shuffleChain_d_zero_one (h : 0 + 1 = 0 + 1) :
    shuffleChain T 0 1 1 h ≫ (((Δ[0] : SSet.{w}) ⊗ Δ[1]).chainComplex T).d 1 0 =
      xFace T 0 1 0 h + (-1 : ℤ) ^ 0 • yFace T 0 1 0 h := by
  rw [shuffleChain_zero_succ, xFace, yFace, yFaces, shuffleChain]
  simp only [Category.assoc, ιChainComplex_prodConeChain_assoc, ι_chainComplexMap_f_assoc,
    ιChainComplex_d, Preadditive.comp_add, Preadditive.comp_zsmul, ι_chainComplexMap_f, zero_add,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, δ_zero_prodCone, pow_zero, one_smul]
  congr 3
  exact Prod.ext (stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)
    (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)

private lemma shuffleChain_d_one_zero (h : 1 + 0 = 0 + 1) :
    shuffleChain T 1 0 1 h ≫ (((Δ[1] : SSet.{w}) ⊗ Δ[0]).chainComplex T).d 1 0 =
      xFace T 1 0 0 h + (-1 : ℤ) ^ 1 • yFace T 1 0 0 h := by
  rw [shuffleChain_succ_zero, xFace, yFace, xFaces, shuffleChain]
  simp only [Category.assoc, ιChainComplex_prodConeChain_assoc, ι_chainComplexMap_f_assoc,
    ιChainComplex_d, Preadditive.comp_add, Preadditive.comp_zsmul, ι_chainComplexMap_f,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, δ_zero_prodCone, Fin.val_zero, pow_zero,
    one_smul, smul_zero]
  congr 3
  exact Prod.ext (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)
    (stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)

/-- The boundary of the shuffle chain: the alternating sum of its faces in the first factor plus
`(-1)^p` times the alternating sum of its faces in the second factor. -/
private lemma shuffleChain_d (n : ℕ) : ∀ (p q : ℕ) (h : p + q = n + 1),
    shuffleChain T p q (n + 1) h ≫ (((Δ[p] : SSet.{w}) ⊗ Δ[q]).chainComplex T).d (n + 1) n =
      xFace T p q n h + (-1 : ℤ) ^ p • yFace T p q n h := by
  -- Each shuffle chain is a sum of cones `hStep` and `vStep`, whose boundaries are given by the
  -- cone formula (`hStep_d`, `vStep_d`); the boundaries of the smaller shuffle chains are known by
  -- induction, and the face sums of the cones are computed by `hStep_xFaces` and its siblings.
  -- The terms left over cancel in pairs by `whiskerLeft_hStep`.
  induction n with
  | zero =>
    rintro (_ | _ | p) (_ | _ | q) h <;> try omega
    · exact shuffleChain_d_zero_one T h
    · exact shuffleChain_d_one_zero T h
  | succ n ih =>
    rintro (_ | p) (_ | q) h
    · omega
    · rcases q with _ | q
      · omega
      rw [shuffleChain_zero_succ, ← vStep, Category.assoc, vStep_d, Preadditive.comp_sub,
        reassoc_of% (ih 0 (q + 1) (by omega))]
      simp only [xFace, yFace, shuffleChain_zero_succ, ← vStep.eq_1, Category.assoc,
        vStep_yFaces, Preadditive.comp_sub, zero_add, pow_zero, one_smul]
    · rcases p with _ | p
      · omega
      rw [shuffleChain_succ_zero, ← hStep, Category.assoc, hStep_d, Preadditive.comp_sub,
        reassoc_of% (ih (p + 1) 0 (by omega))]
      simp only [xFace, yFace, shuffleChain_succ_zero, ← hStep.eq_1, Category.assoc,
        hStep_xFaces, Preadditive.comp_sub, smul_zero, add_zero]
    · rw [shuffleChain_succ_succ, ← hStep, ← vStep, Preadditive.add_comp, Preadditive.zsmul_comp,
        Category.assoc, Category.assoc, hStep_d, vStep_d, Preadditive.comp_sub,
        Preadditive.comp_sub, reassoc_of% (ih p (q + 1) (by omega)),
        reassoc_of% (ih (p + 1) q (by omega))]
      -- unfold the smaller shuffle chains one step, which depends on whether `p` and `q` vanish
      rcases p with _ | p <;> rcases q with _ | q
      all_goals
        simp only [xFace, yFace, shuffleChain_succ_succ, shuffleChain_succ_zero,
          shuffleChain_zero_succ, ← hStep.eq_1, ← vStep.eq_1, Category.assoc,
          Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_sub, Preadditive.zsmul_comp,
          smul_zero, zero_add, add_zero, hStep_xFaces, hStep_yFaces, vStep_xFaces, vStep_yFaces,
          whiskerLeft_hStep]
        module

/-- The boundary of the shuffle chain of `Δ[p + 1] ⊗ Δ[q + 1]`: the alternating sum of its faces
in the first factor plus `(-1)^(p + 1)` times the alternating sum of its faces in the second
factor, each face being the image of a smaller shuffle chain under a face map. -/
lemma shuffleChain_d_succ_succ (p q n : ℕ) (h : p + 1 + (q + 1) = n + 1) :
    shuffleChain T (p + 1) (q + 1) (n + 1) h ≫
        (((Δ[p + 1] : SSet.{w}) ⊗ Δ[q + 1]).chainComplex T).d (n + 1) n =
      shuffleChain T p (q + 1) n (by omega) ≫ ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          (chainComplexMap (stdSimplex.δ j ▷ (Δ[q + 1] : SSet.{w})) T).f n +
        (-1 : ℤ) ^ (p + 1) • shuffleChain T (p + 1) q n (by omega) ≫
          ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
            (chainComplexMap ((Δ[p + 1] : SSet.{w}) ◁ stdSimplex.δ j) T).f n :=
  shuffleChain_d T n (p + 1) (q + 1) h

/-- The boundary of the shuffle chain of `Δ[p + 1] ⊗ Δ[0]`: the alternating sum of its faces in
the first factor. -/
lemma shuffleChain_d_succ_zero (p n : ℕ) (h : p + 1 + 0 = n + 1) :
    shuffleChain T (p + 1) 0 (n + 1) h ≫
        (((Δ[p + 1] : SSet.{w}) ⊗ Δ[0]).chainComplex T).d (n + 1) n =
      shuffleChain T p 0 n (by omega) ≫ ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (chainComplexMap (stdSimplex.δ j ▷ (Δ[0] : SSet.{w})) T).f n := by
  rw [shuffleChain_d, yFace, smul_zero, add_zero, xFace, xFaces]

/-- The boundary of the shuffle chain of `Δ[0] ⊗ Δ[q + 1]`: the alternating sum of its faces in
the second factor. -/
lemma shuffleChain_d_zero_succ (q n : ℕ) (h : 0 + (q + 1) = n + 1) :
    shuffleChain T 0 (q + 1) (n + 1) h ≫
        (((Δ[0] : SSet.{w}) ⊗ Δ[q + 1]).chainComplex T).d (n + 1) n =
      shuffleChain T 0 q n (by omega) ≫ ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        (chainComplexMap ((Δ[0] : SSet.{w}) ◁ stdSimplex.δ j) T).f n := by
  rw [shuffleChain_d, xFace, pow_zero, one_smul, zero_add, yFace, yFaces]

end ShuffleChain

section Shuffle

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L : SSet.{w}) (R S : C)

/-- The degree-`n` component of the shuffle map. -/
private def shuffleX (n : ℕ) :
    (K.chainComplex R ⊗ L.chainComplex S).X n ⟶ ((K ⊗ L).chainComplex (R ⊗ S)).X n :=
  mapBifunctorDesc fun p q h ↦ tensorChainComplexXDesc fun x y ↦
    shuffleChain (R ⊗ S) p q n h ≫
      (chainComplexMap (yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) (R ⊗ S)).f n

@[reassoc]
private lemma ι_shuffleX {p q n : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫
        ιTensorObj (K.chainComplex R) (L.chainComplex S) p q n h ≫ shuffleX K L R S n =
      shuffleChain (R ⊗ S) p q n h ≫
        (chainComplexMap (yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) (R ⊗ S)).f n := by
  simp [shuffleX]

variable {K L R S} in
private lemma ι_D₁_shuffleX {p q n : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n + 1) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫
        ιTensorObj (K.chainComplex R) (L.chainComplex S) p q (n + 1) h ≫
          mapBifunctor.D₁ (K.chainComplex R) (L.chainComplex S) (curriedTensor C)
            (ComplexShape.down ℕ) (n + 1) n ≫ shuffleX K L R S n =
      xFace (R ⊗ S) p q n h ≫
        (chainComplexMap (yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) (R ⊗ S)).f n := by
  rcases p with _ | p
  · obtain rfl : q = n + 1 := by omega
    rw [ChainComplex.ιTensorObj_D₁_zero_assoc, zero_comp, comp_zero, xFace, zero_comp]
  · rw [ChainComplex.ιTensorObj_D₁_succ_assoc, tensorHom_comp_whiskerRight_assoc, ιChainComplex_d,
      sum_tensor, Preadditive.sum_comp, xFace, xFaces, Category.assoc, Preadditive.sum_comp,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [zsmul_tensorHom, Preadditive.zsmul_comp, ι_shuffleX, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, chainComplexMap_f_comp, whiskerRight_comp_tensorHom,
      stdSimplex.δ_comp_yonedaEquiv_symm]

variable {K L R S} in
private lemma ι_D₂_shuffleX {p q n : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n + 1) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫
        ιTensorObj (K.chainComplex R) (L.chainComplex S) p q (n + 1) h ≫
          mapBifunctor.D₂ (K.chainComplex R) (L.chainComplex S) (curriedTensor C)
            (ComplexShape.down ℕ) (n + 1) n ≫ shuffleX K L R S n =
      ((-1 : ℤ) ^ p • yFace (R ⊗ S) p q n h) ≫
        (chainComplexMap (yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) (R ⊗ S)).f n := by
  rcases q with _ | q
  · obtain rfl : p = n + 1 := by omega
    rw [ChainComplex.ιTensorObj_D₂_zero_assoc, zero_comp, comp_zero, yFace, smul_zero,
      zero_comp]
  · simp only [ChainComplex.ιTensorObj_D₂_succ_assoc, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc, tensorHom_comp_whiskerLeft_assoc, ιChainComplex_d,
      tensor_sum, Preadditive.sum_comp, yFace, yFaces, Preadditive.comp_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [tensorHom_zsmul, Preadditive.zsmul_comp, ι_shuffleX, chainComplexMap_f_comp,
      whiskerLeft_comp_tensorHom, stdSimplex.δ_comp_yonedaEquiv_symm]

/-- **The shuffle map** `C(K; R) ⊗ C(L; S) ⟶ C(K × L; R ⊗ S)` of Eilenberg and Mac Lane.  It sends
the summand of a `p`-simplex `x` of `K` and a `q`-simplex `y` of `L` to the image of the shuffle
chain `SSet.shuffleChain (R ⊗ S) p q (p + q)` under the map `Δ[p] ⊗ Δ[q] ⟶ K ⊗ L` classifying
`(x, y)` (`SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f`).  It is a morphism of chain
complexes for the Koszul sign rule on the tensor product. -/
def shuffle : K.chainComplex R ⊗ L.chainComplex S ⟶ (K ⊗ L).chainComplex (R ⊗ S) where
  f := shuffleX K L R S
  comm' := by
    rintro _ n rfl
    refine mapBifunctor.hom_ext fun p q h ↦ tensorChainComplexX_hom_ext fun x y ↦ ?_
    have hd : (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n =
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
          mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n :=
      mapBifunctor.d_eq _ _ _ _ _ _
    rw [ι_shuffleX_assoc, (chainComplexMap _ _).comm, ← Category.assoc, shuffleChain_d, hd]
    simp only [Preadditive.add_comp, Preadditive.comp_add]
    rw [ι_D₁_shuffleX, ι_D₂_shuffleX]

/-- The shuffle map on the summand of a `p`-simplex `x` of `K` and a `q`-simplex `y` of `L` is the
image of the shuffle chain of `Δ[p] ⊗ Δ[q]` under the map `Δ[p] ⊗ Δ[q] ⟶ K ⊗ L` classifying
`(x, y)`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_tensorHom_ιChainComplex_shuffle_f {p q n : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌)
    (h : p + q = n) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫
        ιTensorObj (K.chainComplex R) (L.chainComplex S) p q n h ≫ (shuffle K L R S).f n =
      shuffleChain (R ⊗ S) p q n h ≫
        (chainComplexMap (yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) (R ⊗ S)).f n :=
  ι_shuffleX K L R S x y h

/-- In degree zero, the shuffle map sends the summand of a pair of vertices `(x, y)` to the summand
of the vertex `(x, y)` of `K × L`. -/
lemma ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero (x : K _⦋0⦌) (y : L _⦋0⦌) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫
        ιTensorObj (K.chainComplex R) (L.chainComplex S) 0 0 0 rfl ≫ (shuffle K L R S).f 0 =
      (K ⊗ L).ιChainComplex (x, y) := by
  rw [ιChainComplex_tensorHom_ιChainComplex_shuffle_f,
    shuffleChain_zero_zero _ _ (yonedaEquiv (CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _))),
    ι_chainComplexMap_f]
  -- the two components of the image of the vertex `(𝟙, 𝟙)` are, by definition, the images of `𝟙`
  -- under the maps classifying `x` and `y`
  exact congrArg _ (Prod.ext (yonedaEquiv_symm_app_id x) (yonedaEquiv_symm_app_id y))

variable {K L} in
/-- The shuffle map is natural in both simplicial sets. -/
@[reassoc]
lemma shuffle_naturality {K' L' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L') :
    (chainComplexMap f R ⊗ₘ chainComplexMap g S) ≫ shuffle K' L' R S =
      shuffle K L R S ≫ chainComplexMap (f ⊗ₘ g) (R ⊗ S) := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q h ↦ tensorChainComplexX_hom_ext fun x y ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, tensorHom_eq_mapBifunctorMap,
    ι_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, ι_chainComplexMap_f, ι_chainComplexMap_f,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f_assoc, chainComplexMap_f_comp,
    tensorHom_comp_tensorHom, yonedaEquiv_symm_comp, yonedaEquiv_symm_comp]

variable {R S} in
/-- The shuffle map is natural in both coefficient objects. -/
@[reassoc]
lemma shuffle_coefficient_naturality {R' S' : C} (f : R ⟶ R') (g : S ⟶ S') :
    (((chainComplexFunctor C).map f).app K ⊗ₘ ((chainComplexFunctor C).map g).app L) ≫
        shuffle K L R' S' =
      shuffle K L R S ≫ ((chainComplexFunctor C).map (f ⊗ₘ g)).app (K ⊗ L) := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q h ↦ tensorChainComplexX_hom_ext fun x y ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, tensorHom_eq_mapBifunctorMap,
    ι_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f, ← tensorHom_comp_tensorHom_assoc,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f_assoc,
    chainComplexMap_f_chainComplexFunctor_map_app_f,
    shuffleChain_chainComplexFunctor_map_app_f_assoc]

end Shuffle

end SSet
