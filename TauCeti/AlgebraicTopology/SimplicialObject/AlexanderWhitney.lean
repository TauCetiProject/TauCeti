/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import TauCeti.AlgebraicTopology.SimplexCategory.Subinterval
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The Alexander–Whitney map of simplicial objects

Let `C` be a preadditive monoidal category with finite coproducts, and let `A` and `B` be
simplicial objects in `C`.  Their tensor product `A ⊗ B` is taken degreewise,
`(A ⊗ B)ₙ = Aₙ ⊗ Bₙ`, with the tensor product of the structure maps.  The Alexander–Whitney map
`CategoryTheory.SimplicialObject.alexanderWhitney A B` is the morphism of chain complexes from
the alternating face map complex of `A ⊗ B` to the tensor product of the alternating face map
complexes of `A` and of `B`.  In degree `n` it is
`∑_{p + q = n} A(front p-face) ⊗ B(back q-face)`,
where the front `p`-face of `⦋n⦌` is the inclusion of the vertices `0, …, p` and the back `q`-face
is the inclusion of the vertices `p, …, n`, both given by Mathlib's
`SimplexCategory.subinterval`.  The tensor product of chain complexes is Mathlib's monoidal
structure on `ChainComplex C ℕ`, whose differential is `d (a ⊗ b) = d a ⊗ b + (-1)^p a ⊗ d b`
for `a` of degree `p`.

The simplicial chains of a product of simplicial sets are the case where `A` and `B` are free on
the simplices of the factors (`SSet.alexanderWhitney`).  Singular chains with coefficients in a
local coefficient system form a simplicial module that is not free on the simplices with a fixed
coefficient object, which is why the construction is stated for arbitrary simplicial objects: the
Alexander–Whitney diagonal of chains with local coefficients, along which cup and cap products
with local coefficients are taken, is an instance of it.

## Main definitions and results

* `CategoryTheory.SimplicialObject.alexanderWhitney`: the Alexander–Whitney chain map.
* `CategoryTheory.SimplicialObject.alexanderWhitney_f`: its degree-`n` component.
* `CategoryTheory.SimplicialObject.alexanderWhitney_naturality`: it is natural in both simplicial
  objects.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Opposite HomologicalComplex

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C]

variable [Preadditive C]

variable [MonoidalCategory C] [MonoidalPreadditive C] [HasFiniteCoproducts C]
  (A B : SimplicialObject C)

/-- The summand of the Alexander–Whitney map in degree `n` and bidegree `(p, q)`: the front
`p`-face of `A` tensored with the back `q`-face of `B`, or zero if `p + q ≠ n`.  Indexing by an
arbitrary pair keeps the summands of all bidegrees in one type. -/
private def alexanderWhitneyTerm (n p q : ℕ) :
    A _⦋n⦌ ⊗ B _⦋n⦌ ⟶
      ((alternatingFaceMapComplex C).obj A ⊗ (alternatingFaceMapComplex C).obj B).X n :=
  if h : p + q = n then
    (A.map (SimplexCategory.subinterval 0 p (by omega)).op ⊗ₘ
      B.map (SimplexCategory.subinterval p q (by omega)).op) ≫
        ιTensorObj ((alternatingFaceMapComplex C).obj A) ((alternatingFaceMapComplex C).obj B)
          p q n h
  else 0

private lemma alexanderWhitneyTerm_of_eq (n p q : ℕ) (h : p + q = n) :
    alexanderWhitneyTerm A B n p q =
      (A.map (SimplexCategory.subinterval 0 p (by omega)).op ⊗ₘ
        B.map (SimplexCategory.subinterval p q (by omega)).op) ≫
          ιTensorObj ((alternatingFaceMapComplex C).obj A) ((alternatingFaceMapComplex C).obj B)
            p q n h := by
  simp only [alexanderWhitneyTerm, h, ↓reduceDIte]

/-- The boundary of the Alexander–Whitney map in the bidegree `(r, s)`: the part of `d ∘ AW` that
lands in bidegree `(r, s)` is `AW ∘ d`.  The last face of the front `(r + 1)`-face cancels against
the zeroth face of the back `(s + 1)`-face; every other face of a front or back face is the front
or back face of a face of the simplex. -/
private lemma alexanderWhitneyTerm_D (n r s : ℕ) (h : r + s = n) :
    alexanderWhitneyTerm A B (n + 1) (r + 1) s ≫
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
      alexanderWhitneyTerm A B (n + 1) r (s + 1) ≫
        mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((A.δ k ⊗ₘ B.δ k) ≫ alexanderWhitneyTerm A B n r s) := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ (by omega),
    alexanderWhitneyTerm_of_eq _ _ _ _ _ (by omega)]
  simp only [Category.assoc, ChainComplex.ιTensorObj_D₁_succ,
    ChainComplex.ιTensorObj_D₂_succ, Preadditive.comp_zsmul, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD]
  dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj]
  simp only [tensorHom_comp_whiskerRight_assoc, tensorHom_comp_whiskerLeft_assoc,
    Preadditive.comp_sum, Preadditive.comp_zsmul,
    sum_tensor, tensor_sum, zsmul_tensorHom, tensorHom_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  have hrs : r + 1 + (s + 1) = n + 2 := by omega
  conv_rhs =>
    rw [← Fin.sum_congr' _ hrs, Fin.sum_univ_add]
  rw [Fin.sum_univ_castSucc (n := r + 1), Fin.sum_univ_succ (n := s + 1)]
  simp only [alexanderWhitneyTerm_of_eq A B n r s h, tensorHom_comp_tensorHom_assoc]
  simp only [SimplicialObject.δ, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ_last_comp_subinterval_zero, SimplexCategory.δ_zero_comp_subinterval]
  rw [smul_add, Finset.smul_sum, add_add_add_comm]
  -- the two sums match termwise, and the two remaining terms cancel
  have key {M : Type _} [AddCommGroup M] {P P' a b Q Q' : M} (h₁ : P = P') (h₂ : Q = Q')
      (h₃ : a + b = 0) : P + b + (a + Q) = P' + Q' := by
    have hadd : P + b + (a + Q) = P + Q + (a + b) := by abel
    rw [← h₁, ← h₂, hadd, h₃, add_zero]
  refine key ?_ ?_ ?_
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := i.isLt
    rw [SimplexCategory.δ_comp_subinterval_zero i.castSucc
        (Fin.cast (by omega) (Fin.castAdd (s + 1) i)) (by simp),
      SimplexCategory.subinterval_comp_δ_of_le (j := r) _ (by simp; omega)]
    simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [SimplexCategory.δ_succ_comp_subinterval j (Fin.cast (by omega) (Fin.natAdd (r + 1) j))
        (by simp),
      SimplexCategory.subinterval_zero_comp_δ_of_lt (p := r) _ (by simp; omega), smul_smul]
    congr 1
    simp [pow_add]
  · rw [smul_smul, ← add_smul]
    simp [pow_succ]

/-- The degree-`n` component of the Alexander–Whitney map. -/
private def alexanderWhitneyX (n : ℕ) :
    A _⦋n⦌ ⊗ B _⦋n⦌ ⟶
      ((alternatingFaceMapComplex C).obj A ⊗ (alternatingFaceMapComplex C).obj B).X n :=
  ∑ pq ∈ Finset.antidiagonal n, alexanderWhitneyTerm A B n pq.1 pq.2

/-- **The Alexander–Whitney map** of two simplicial objects, from the alternating face map
complex of their degreewise tensor product to the tensor product of their alternating face map
complexes.  In degree `n` it is the sum over `p + q = n` of the front `p`-face of `A` tensored
with the back `q`-face of `B` (`CategoryTheory.SimplicialObject.alexanderWhitney_f`).  It is a
morphism of chain complexes for the Koszul sign convention on the tensor product. -/
def alexanderWhitney :
    (alternatingFaceMapComplex C).obj (A ⊗ B) ⟶
      (alternatingFaceMapComplex C).obj A ⊗ (alternatingFaceMapComplex C).obj B where
  f := alexanderWhitneyX A B
  comm' := by
    rintro _ n rfl
    have hd : ((alternatingFaceMapComplex C).obj A ⊗
        (alternatingFaceMapComplex C).obj B).d (n + 1) n =
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
          mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n :=
      mapBifunctor.d_eq _ _ _ _ _ _
    -- the faces of `A ⊗ B` are typed as morphisms of tensor products, so that the composites
    -- with the summands of the Alexander–Whitney map can be distributed
    rw [hd, show ((alternatingFaceMapComplex C).obj (A ⊗ B)).d (n + 1) n =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (A.δ i ⊗ₘ B.δ i) :
        A _⦋n + 1⦌ ⊗ B _⦋n + 1⦌ ⟶ A _⦋n⦌ ⊗ B _⦋n⦌) from
      AlternatingFaceMapComplex.obj_d_eq (A ⊗ B) n]
    dsimp only [alexanderWhitneyX, alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj]
    simp only [Preadditive.sum_comp, Preadditive.comp_add, Preadditive.zsmul_comp,
      Preadditive.comp_sum]
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ',
      alexanderWhitneyTerm_of_eq _ _ _ 0 (n + 1) (by omega),
      alexanderWhitneyTerm_of_eq _ _ _ (n + 1) 0 (by omega), Category.assoc, Category.assoc,
      ChainComplex.ιTensorObj_D₁_zero, ChainComplex.ιTensorObj_D₂_zero, comp_zero, comp_zero,
      zero_add, zero_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun pq hpq ↦ ?_
    exact alexanderWhitneyTerm_D A B n pq.1 pq.2 (Finset.mem_antidiagonal.mp hpq)

/-- The degree-`n` component of the Alexander–Whitney map: the sum over `p ≤ n` of the front
`p`-face of `A` tensored with the back `(n - p)`-face of `B`. -/
-- The sum is typed as a morphism out of `Aₙ ⊗ Bₙ` rather than out of the degree-`n` term of the
-- alternating face map complex, which is the same object only up to unfolding, so that composites
-- with the summands can be rewritten.
@[simp]
lemma alexanderWhitney_f (n : ℕ) :
    (alexanderWhitney A B).f n =
      (∑ p : Fin (n + 1),
        (A.map (SimplexCategory.subinterval 0 p (by omega)).op ⊗ₘ
          B.map (SimplexCategory.subinterval p (n - p) (by omega)).op) ≫
            ιTensorObj ((alternatingFaceMapComplex C).obj A)
              ((alternatingFaceMapComplex C).obj B) (p : ℕ) (n - p) n (by omega) :
        A _⦋n⦌ ⊗ B _⦋n⦌ ⟶ _) := by
  dsimp only [alexanderWhitney, alexanderWhitneyX]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (alexanderWhitneyTerm A B n),
    Finset.sum_range]
  exact Finset.sum_congr rfl fun p _ ↦ alexanderWhitneyTerm_of_eq _ _ _ _ _ (by omega)

variable {A B} in
/-- The Alexander–Whitney map is natural in both simplicial objects. -/
@[reassoc]
lemma alexanderWhitney_naturality {A' B' : SimplicialObject C} (f : A ⟶ A') (g : B ⟶ B') :
    (alternatingFaceMapComplex C).map (f ⊗ₘ g) ≫ alexanderWhitney A' B' =
      alexanderWhitney A B ≫
        ((alternatingFaceMapComplex C).map f ⊗ₘ (alternatingFaceMapComplex C).map g) := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, alexanderWhitney_f,
    alexanderWhitney_f]
  dsimp only [alternatingFaceMapComplex_obj_X, alternatingFaceMapComplex_map_f,
    Monoidal.tensorObj_obj, Monoidal.tensorHom_app]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [tensorHom_eq_mapBifunctorMap, ι_tensorHom]
  dsimp only [alternatingFaceMapComplex_obj_X, alternatingFaceMapComplex_map_f]
  simp only [tensorHom_comp_tensorHom_assoc, NatTrans.naturality]

end CategoryTheory.SimplicialObject
