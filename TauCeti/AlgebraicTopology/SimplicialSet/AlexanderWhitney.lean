/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.AlgebraicTopology.SimplexCategory.Subinterval
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The Alexander–Whitney map

Let `C` be a preadditive monoidal category with `w`-small coproducts, and let `R` and `S` be
objects of `C`.  For simplicial sets `K` and `L`, the Alexander–Whitney map is the morphism
of chain complexes `SSet.alexanderWhitney K L R S` from `(K ⊗ L).chainComplex (R ⊗ S)`, the
simplicial chains of the product `K × L`, to `K.chainComplex R ⊗ L.chainComplex S`, the tensor
product of the simplicial chains of the factors.  On an `n`-simplex `(x, y)` of `K × L` it is
`∑_{p + q = n} x|[0, …, p] ⊗ y|[p, …, n]`,
the front `p`-face of `x` tensored with the back `q`-face of `y`, the faces being Mathlib's
`SimplexCategory.subinterval`.  The tensor product of chain complexes is Mathlib's monoidal
structure on `ChainComplex C ℕ`, whose differential is `d (a ⊗ b) = d a ⊗ b + (-1)^p a ⊗ d b`
for `a` of degree `p`.

The Alexander–Whitney map is one half of the Eilenberg–Zilber comparison between chains on a
product and tensor products of chains, and composing it with the diagonal gives the cup product
of cochains.  For the usual coefficients take `C := ModuleCat k` and `R = S = k`.

## Main definitions and results

* `SSet.alexanderWhitney`: the Alexander–Whitney chain map.
* `SSet.ιChainComplex_alexanderWhitney_f`: its value on a simplex.
* `SSet.alexanderWhitney_naturality`: it is natural in both simplicial sets.
* `SSet.alexanderWhitney_coefficient_naturality`: it is natural in both coefficient objects.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]

section Tensor

variable (K₁ K₂ : ChainComplex C ℕ)

private lemma ιTensorObj_D₁_succ (r s n : ℕ) (h : r + 1 + s = n + 1) :
    ιTensorObj K₁ K₂ (r + 1) s (n + 1) h ≫
        mapBifunctor.D₁ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      (K₁.d (r + 1) r ▷ K₂.X s) ≫ ιTensorObj K₁ K₂ r s n (by omega) := by
  have hr : (ComplexShape.down ℕ).Rel (r + 1) r := by simp
  rw [mapBifunctor.ι_D₁, mapBifunctor.d₁_eq _ _ _ _
    hr _ _ (by simp; omega)]
  simp

private lemma ιTensorObj_D₁_zero (n : ℕ) :
    ιTensorObj K₁ K₂ 0 (n + 1) (n + 1) (by omega) ≫
        mapBifunctor.D₁ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n = 0 := by
  rw [mapBifunctor.ι_D₁, mapBifunctor.d₁_eq_zero]
  simp

private lemma ιTensorObj_D₂_succ (r s n : ℕ) (h : r + (s + 1) = n + 1) :
    ιTensorObj K₁ K₂ r (s + 1) (n + 1) h ≫
        mapBifunctor.D₂ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      ((-1 : ℤ) ^ r) •
        (K₁.X r ◁ K₂.d (s + 1) s) ≫ ιTensorObj K₁ K₂ r s n (by omega) := by
  have hs : (ComplexShape.down ℕ).Rel (s + 1) s := by simp
  rw [mapBifunctor.ι_D₂, mapBifunctor.d₂_eq _ _ _ _ _
    hs _ (by simp; omega)]
  simp [Units.smul_def]

private lemma ιTensorObj_D₂_zero (n : ℕ) :
    ιTensorObj K₁ K₂ (n + 1) 0 (n + 1) (by omega) ≫
        mapBifunctor.D₂ K₁ K₂ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n = 0 := by
  rw [mapBifunctor.ι_D₂, mapBifunctor.d₂_eq_zero]
  simp

end Tensor

section Faces

variable (K : SSet.{w})

private lemma δ_map_subinterval_zero {n p : ℕ} (a : K _⦋n + 1⦌) (i : Fin (p + 2))
    (k : Fin (n + 2)) (hik : (i : ℕ) = k) (h : 0 + (p + 1) ≤ n + 1) :
    K.δ i (K.map (SimplexCategory.subinterval 0 (p + 1) h).op a) =
      K.map (SimplexCategory.subinterval 0 p (by omega)).op (K.δ k a) := by
  simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp,
    SimplexCategory.δ_comp_subinterval_zero i k hik h]

private lemma δ_last_map_subinterval_zero {n p : ℕ} (a : K _⦋n⦌) (h : 0 + (p + 1) ≤ n) :
    K.δ (Fin.last (p + 1)) (K.map (SimplexCategory.subinterval 0 (p + 1) h).op a) =
      K.map (SimplexCategory.subinterval 0 p (by omega)).op a := by
  simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp,
    SimplexCategory.δ_last_comp_subinterval_zero h]

private lemma δ_zero_map_subinterval {n j q : ℕ} (a : K _⦋n⦌) (h : j + (q + 1) ≤ n) :
    K.δ 0 (K.map (SimplexCategory.subinterval j (q + 1) h).op a) =
      K.map (SimplexCategory.subinterval (j + 1) q (by omega)).op a := by
  simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp,
    SimplexCategory.δ_zero_comp_subinterval h]

private lemma δ_succ_map_subinterval {n j q : ℕ} (a : K _⦋n + 1⦌) (i : Fin (q + 1))
    (k : Fin (n + 2)) (hik : j + 1 + (i : ℕ) = k) (h : j + (q + 1) ≤ n + 1) :
    K.δ i.succ (K.map (SimplexCategory.subinterval j (q + 1) h).op a) =
      K.map (SimplexCategory.subinterval j q (by omega)).op (K.δ k a) := by
  simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp,
    SimplexCategory.δ_succ_comp_subinterval i k hik h]

private lemma map_subinterval_δ_of_le {n j q : ℕ} (a : K _⦋n + 1⦌) (k : Fin (n + 2))
    (hk : (k : ℕ) ≤ j) (h : j + q ≤ n) :
    K.map (SimplexCategory.subinterval j q h).op (K.δ k a) =
      K.map (SimplexCategory.subinterval (j + 1) q (by omega)).op a := by
  simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp,
    SimplexCategory.subinterval_comp_δ_of_le k hk h]

private lemma map_subinterval_zero_δ_of_lt {n p : ℕ} (a : K _⦋n + 1⦌) (k : Fin (n + 2))
    (hk : p < (k : ℕ)) (h : 0 + p ≤ n) :
    K.map (SimplexCategory.subinterval 0 p h).op (K.δ k a) =
      K.map (SimplexCategory.subinterval 0 p (by omega)).op a := by
  simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp,
    SimplexCategory.subinterval_zero_comp_δ_of_lt k hk h]

end Faces

variable (K L : SSet.{w}) (R S : C)

/-- The summand of the Alexander–Whitney map on the simplex `x` in bidegree `(p, q)`: the front
`p`-face of `x.1` tensored with the back `q`-face of `x.2`, or zero if `p + q` is not the degree
of `x`.  Indexing by an arbitrary pair keeps the summands of all bidegrees in one type. -/
private def alexanderWhitneyTerm {n : ℕ} (x : (K ⊗ L) _⦋n⦌) (p q : ℕ) :
    R ⊗ S ⟶ (K.chainComplex R ⊗ L.chainComplex S).X n :=
  if h : p + q = n then
    (K.ιChainComplex (K.map (SimplexCategory.subinterval 0 p (by omega)).op x.1) ⊗ₘ
      L.ιChainComplex (L.map (SimplexCategory.subinterval p q (by omega)).op x.2)) ≫
        ιTensorObj _ _ p q n h
  else 0

private lemma alexanderWhitneyTerm_of_eq {n : ℕ} (x : (K ⊗ L) _⦋n⦌) (p q : ℕ)
    (h : p + q = n) :
    alexanderWhitneyTerm K L R S x p q =
    (K.ιChainComplex (K.map (SimplexCategory.subinterval 0 p (by omega)).op x.1) ⊗ₘ
      L.ιChainComplex (L.map (SimplexCategory.subinterval p q (by omega)).op x.2)) ≫
        ιTensorObj _ _ p q n h := by
  simp only [alexanderWhitneyTerm, h, ↓reduceDIte]

/-- The boundary of the Alexander–Whitney map in the bidegree `(r, s)`: the part of `d ∘ AW` that
lands in bidegree `(r, s)` is `AW ∘ d`.  The last face of the front `(r + 1)`-face cancels against
the zeroth face of the back `(s + 1)`-face; every other face of a front or back face is the front
or back face of a face of the simplex. -/
private lemma alexanderWhitneyTerm_D {n : ℕ} (x : (K ⊗ L) _⦋n + 1⦌) (r s : ℕ)
    (h : r + s = n) :
    alexanderWhitneyTerm K L R S x (r + 1) s ≫
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
      alexanderWhitneyTerm K L R S x r (s + 1) ≫
        mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        alexanderWhitneyTerm K L R S ((K ⊗ L).δ k x) r s := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ _ _ (by omega),
    alexanderWhitneyTerm_of_eq _ _ _ _ _ _ _ (by omega)]
  simp only [Category.assoc, ιTensorObj_D₁_succ, ιTensorObj_D₂_succ, Preadditive.comp_zsmul,
    tensorHom_comp_whiskerRight_assoc, tensorHom_comp_whiskerLeft_assoc, SSet.ιChainComplex_d,
    sum_tensor, tensor_sum, zsmul_tensorHom, tensorHom_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  have hrs : r + 1 + (s + 1) = n + 2 := by omega
  conv_rhs =>
    rw [← Fin.sum_congr' _ hrs, Fin.sum_univ_add]
  rw [Fin.sum_univ_castSucc (n := r + 1), Fin.sum_univ_succ (n := s + 1)]
  simp only [alexanderWhitneyTerm_of_eq K L R S _ r s h]
  simp only [Monoidal.tensorObj_obj, prod_δ_fst, prod_δ_snd]
  rw [δ_last_map_subinterval_zero, δ_zero_map_subinterval, smul_add, Finset.smul_sum,
    add_add_add_comm]
  -- the two sums match termwise, and the two remaining terms cancel
  have key {M : Type _} [AddCommGroup M] {A A' a b B B' : M} (h₁ : A = A') (h₂ : B = B')
      (h₃ : a + b = 0) : A + b + (a + B) = A' + B' := by
    have hadd : A + b + (a + B) = A + B + (a + b) := by abel
    rw [← h₁, ← h₂, hadd, h₃, add_zero]
  refine key ?_ ?_ ?_
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := i.isLt
    rw [δ_map_subinterval_zero K x.1 i.castSucc
        (Fin.cast (by omega) (Fin.castAdd (s + 1) i)) (by simp),
      map_subinterval_δ_of_le L x.2 _ (by simp; omega)]
    simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [δ_succ_map_subinterval L x.2 j (Fin.cast (by omega) (Fin.natAdd (r + 1) j))
        (by simp),
      map_subinterval_zero_δ_of_lt K x.1 _ (by simp; omega), smul_smul]
    congr 1
    simp [pow_add]
  · rw [smul_smul, ← add_smul]
    simp [pow_succ]

/-- The degree-`n` component of the Alexander–Whitney map. -/
private def alexanderWhitneyX (n : ℕ) :
    ((K ⊗ L).chainComplex (R ⊗ S)).X n ⟶ (K.chainComplex R ⊗ L.chainComplex S).X n :=
  Cofan.IsColimit.desc ((K ⊗ L).isColimitChainComplexXCofan (R ⊗ S) n)
    fun x ↦ ∑ pq ∈ Finset.antidiagonal n, alexanderWhitneyTerm K L R S x pq.1 pq.2

@[reassoc]
private lemma ιChainComplex_alexanderWhitneyX {n : ℕ} (x : (K ⊗ L) _⦋n⦌) :
    (K ⊗ L).ιChainComplex x ≫ alexanderWhitneyX K L R S n =
      ∑ pq ∈ Finset.antidiagonal n, alexanderWhitneyTerm K L R S x pq.1 pq.2 :=
  Cofan.IsColimit.fac _ _ x

/-- The Alexander–Whitney map `C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)`, sending an `n`-simplex
`(x, y)` of `K × L` to `∑_{p + q = n} x|[0, …, p] ⊗ y|[p, …, n]`, the front `p`-face of `x`
tensored with the back `q`-face of `y` (`SSet.ιChainComplex_alexanderWhitney_f`).  It is a
morphism of chain complexes for the Koszul sign convention on the tensor product. -/
def alexanderWhitney :
    (K ⊗ L).chainComplex (R ⊗ S) ⟶ K.chainComplex R ⊗ L.chainComplex S where
  f := alexanderWhitneyX K L R S
  comm' := by
    rintro _ n rfl
    ext x
    have hd : (K.chainComplex R ⊗ L.chainComplex S).d (n + 1) n =
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
          mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n :=
      mapBifunctor.d_eq _ _ _ _ _ _
    rw [ιChainComplex_alexanderWhitneyX_assoc, ιChainComplex_d_assoc, hd]
    simp only [Preadditive.sum_comp, Preadditive.comp_add,
      Preadditive.zsmul_comp, ιChainComplex_alexanderWhitneyX]
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ',
      alexanderWhitneyTerm_of_eq _ _ _ _ _ 0 (n + 1) (by omega),
      alexanderWhitneyTerm_of_eq _ _ _ _ _ (n + 1) 0 (by omega), Category.assoc, Category.assoc,
      ιTensorObj_D₁_zero, ιTensorObj_D₂_zero, comp_zero, comp_zero,
      zero_add, zero_add, ← Finset.sum_add_distrib]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pq hpq ↦ ?_
    exact alexanderWhitneyTerm_D K L R S x pq.1 pq.2 (Finset.mem_antidiagonal.mp hpq)

/-- The Alexander–Whitney map on the summand of an `n`-simplex `x` of `K × L`: the sum over
`p ≤ n` of the front `p`-face of `x.1` tensored with the back `(n - p)`-face of `x.2`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_alexanderWhitney_f {n : ℕ} (x : (K ⊗ L) _⦋n⦌) :
    (K ⊗ L).ιChainComplex x ≫ (alexanderWhitney K L R S).f n =
      ∑ p : Fin (n + 1),
        (K.ιChainComplex (K.map (SimplexCategory.subinterval 0 p (by omega)).op x.1) ⊗ₘ
          L.ιChainComplex (L.map (SimplexCategory.subinterval p (n - p) (by omega)).op x.2)) ≫
            ιTensorObj _ _ (p : ℕ) (n - p) n (by omega) := by
  rw [alexanderWhitney, ιChainComplex_alexanderWhitneyX,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (alexanderWhitneyTerm K L R S x),
    Finset.sum_range]
  exact Finset.sum_congr rfl fun p _ ↦ alexanderWhitneyTerm_of_eq _ _ _ _ _ _ _ (by omega)

variable {K L} in
/-- The Alexander–Whitney map is natural in both simplicial sets. -/
@[reassoc]
lemma alexanderWhitney_naturality {K' L' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L') :
    chainComplexMap (f ⊗ₘ g) (R ⊗ S) ≫ alexanderWhitney K' L' R S =
      alexanderWhitney K L R S ≫ (chainComplexMap f R ⊗ₘ chainComplexMap g S) := by
  ext n x
  simp only [HomologicalComplex.comp_f, ι_chainComplexMap_f_assoc,
    ιChainComplex_alexanderWhitney_f_assoc, ιChainComplex_alexanderWhitney_f,
    Preadditive.sum_comp, Category.assoc]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [tensorHom_eq_mapBifunctorMap, ι_tensorHom, tensorHom_comp_tensorHom_assoc,
    ι_chainComplexMap_f, Monoidal.tensorHom_app, Monoidal.tensorObj_obj, tensorHom_app_apply,
    NatTrans.naturality_apply]

variable {R S} in
/-- The Alexander–Whitney map is natural in both coefficient objects. -/
@[reassoc]
lemma alexanderWhitney_coefficient_naturality {R' S' : C} (f : R ⟶ R') (g : S ⟶ S') :
    ((chainComplexFunctor C).map (f ⊗ₘ g)).app (K ⊗ L) ≫
        alexanderWhitney K L R' S' =
      alexanderWhitney K L R S ≫
        (((chainComplexFunctor C).map f).app K ⊗ₘ
          ((chainComplexFunctor C).map g).app L) := by
  ext n x
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    Category.assoc,
    ιChainComplex_alexanderWhitney_f, ιChainComplex_alexanderWhitney_f_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [tensorHom_eq_mapBifunctorMap, ← Category.assoc, tensorHom_comp_tensorHom, Category.assoc,
    ι_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f]

end SSet
