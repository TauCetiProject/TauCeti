/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import TauCeti.LowDimTopology.Bordered.TypeD
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The box tensor product of a type `A` module with a bounded type `D` structure

In bordered Heegaard Floer homology a three-manifold with one boundary component has two
invariants over the algebra `A` of its boundary: a type `A` module, an `A∞` module over `A`, and a
type `D` structure. The Floer complex of a closed manifold glued from two such pieces is the box
tensor product `M ⊠ N` of a type `A` module `M` of one piece with a type `D` structure `N` of the
other (Lipshitz, Ozsváth and Thurston, Theorem 1.3). This file constructs that box tensor product
and proves that its differential squares to zero, over an ungraded differential algebra `(A, d)`
over a ring of characteristic two, where no signs appear.

## Type `A` modules

A type `A` module (`TauCeti.TypeAModule`) has operations `m_{k+1} : M ⊗ A^{⊗k} → M` for all
`k ≥ 0`, multilinear in the algebra inputs. They are packaged as one linear map
`act : TensorAlgebra R A →ₗ[R] Module.End R M`, with
`m_{k+1}(x, a₁, …, a_k) = act (ι a₁ * ⋯ * ι a_k) x`, and satisfy the `A∞` relations
`∑ m(m(x, a₁, …, aᵢ), aᵢ₊₁, …, aₙ) + ∑ m(x, …, d aᵢ, …) + ∑ m(x, …, aᵢ aᵢ₊₁, …) = 0`. A
differential right module is the case where `m_{k+1} = 0` for `k ≥ 2`
(`TauCeti.TypeAModule.ofDGModule`). Tau Ceti's right `A∞` modules
(`TauCeti.AInfinityRightModule`) are `ℤ`-graded with Koszul signs; like the type `D` structures of
`TauCeti.LowDimTopology.Bordered.TypeD`, the modules here are ungraded, as the strands algebras are
graded by noncommutative groups rather than by `ℤ` (see `TauCeti.IsUngradedDGAlgebra`).

## Boundedness and the box tensor product

The `k`-fold iterate `δ^k : N → A^{⊗k} ⊗ N` of a type `D` structure with coefficient matrix `δ`
is recorded by the `k`-th power of the matrix `TauCeti.TypeDStructure.tensorCoeff` with entries
`ι (δ x y)` in the tensor algebra: its entry at `(x, y)` is the sum over the paths
`x = x₀, x₁, …, x_k = y` of `ι (δ x₀ x₁) * ⋯ * ι (δ x_{k-1} x_k)`, the coefficient of `y` in
`δ^k x`. The structure is *bounded* when `δ^k = 0` for `k` large (Lipshitz–Ozsváth–Thurston,
Definition 2.2.18); finiteness of the generators alone does not ensure this. Here the tensor
powers of `A` are taken over `R`. Since `δ x y` lies in the corner `ι (idem x) * A * ι (idem y)`,
when the `ι s` are orthogonal idempotents with sum one, as for the strands algebras, this is the
same condition as with tensor powers over the ring of idempotents. The differential of the box
tensor product (equation (2.29) of Lipshitz–Ozsváth–Thurston) is

`∂ (x ⊗ y) = ∑_k (m_{k+1} ⊗ 1) (x ⊗ δ^k y)`,

which on row vectors `φ : X → M` reads `(∂ φ) z = ∑_k ∑_x act ((δ^k) x z) (φ x)`
(`TauCeti.TypeAModule.boxDifferential`, summing over `k < K`). When `δ^K = 0` the sum is finite:
it does not change when `K` is increased (`TauCeti.TypeAModule.boxDifferential_eq_of_le`).
For a differential module it is the box differential `TauCeti.TypeDStructure.boxDifferential` for
every type `D` structure, bounded or not (`TauCeti.TypeAModule.boxDifferential_ofDGModule`).

## `∂ ∘ ∂ = 0`

Write a word `a₁ ⋯ aₙ` in the free algebra `FreeAlgebra R A`, a bookkeeping device in which
the letters are not yet multilinear, and let `Δ` split a word into a prefix and a suffix in all
ways. The `A∞` relations say that `∑ act (v) ∘ act (u)`, summed over the splittings `u ⊗ v` of a
word, is the action of the bar differential of the word: its letters differentiated one at a time
plus adjacent letters multiplied. For the matrix `δ'` with letter entries `ι (δ x y)`, splitting
`δ'^n` gives `∑_{j + k = n} δ'^j ⊗ δ'^k`, so `∂ ∘ ∂` is the action of the bar differential of
`∑_{n ≤ 2K} δ'^n`. In the tensor algebra the bar differential of `δ'^{n+1}` is
`Q_{n+1} + Q_n`, where `Q_n = ∑_{i < n} δ^i (d δ) δ^{n-1-i}`: the type `D` structure equation
`d δ = δ * δ` identifies the products of adjacent letters with differentiated letters. These terms
cancel in pairs in characteristic two, leaving `Q_{2K}`, which vanishes because `δ^K = 0`.

## Main definitions

* `TauCeti.TypeAModule`: a type `A` module over an ungraded differential algebra.
* `TauCeti.TypeAModule.ofDGModule`: the type `A` module of a differential right module.
* `TauCeti.TypeDStructure.tensorCoeff`: the coefficient matrix with entries in the tensor
  algebra, whose powers are the iterates `δ^k`.
* `TauCeti.TypeAModule.boxDifferential`: the differential of the box tensor product `M ⊠ N`.

## Main results

* `TauCeti.TypeAModule.boxDifferential_eq_of_le`: for a bounded `N` the defining sum is finite.
* `TauCeti.TypeAModule.boxDifferential_boxDifferential`: `∂ ∘ ∂ = 0` when `N` is bounded.
* `TauCeti.TypeAModule.boxDifferential_ofDGModule`: for a differential module the box
  differential is the one of `TauCeti.TypeDStructure.boxDifferential`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.1 (`A∞` modules), Definition 2.2.18 (boundedness), equation (2.29) and Proposition 2.3.10
  (the box tensor product).
-/

public section

noncomputable section

open Finset TensorProduct MulOpposite

namespace TauCeti

/-! ### Words in the free algebra -/

section Words

variable {R A : Type*} [CommRing R]

/-- The word `ι a₁ * ⋯ * ι aₙ` of the free algebra. -/
private def wordF (w : List A) : FreeAlgebra R A :=
  (w.map (FreeAlgebra.ι R)).prod

private theorem wordF_nil : (wordF [] : FreeAlgebra R A) = 1 := (rfl)

private theorem wordF_concat (w : List A) (a : A) :
    (wordF (w ++ [a]) : FreeAlgebra R A) = wordF w * FreeAlgebra.ι R a := by
  simp [wordF]

private theorem basisFreeMonoid_apply (w : FreeMonoid A) :
    FreeAlgebra.basisFreeMonoid R A w = wordF w.toList := by
  simp [FreeAlgebra.basisFreeMonoid, FreeAlgebra.equivMonoidAlgebraFreeMonoid,
    FreeMonoid.lift_apply, wordF]

/-- Linear maps out of the free algebra agree when they agree on words. -/
private theorem linearMap_ext_wordF {P : Type*} [AddCommGroup P] [Module R P]
    {f g : FreeAlgebra R A →ₗ[R] P} (h : ∀ w, f (wordF w) = g (wordF w)) : f = g :=
  (FreeAlgebra.basisFreeMonoid R A).ext fun w => by
    rw [basisFreeMonoid_apply]
    exact h _

/-- The linear map out of the free algebra with prescribed values on words. -/
private def ofWords {P : Type*} [AddCommGroup P] [Module R P] (f : List A → P) :
    FreeAlgebra R A →ₗ[R] P :=
  (FreeAlgebra.basisFreeMonoid R A).constr R fun w => f w.toList

private theorem ofWords_wordF {P : Type*} [AddCommGroup P] [Module R P] (f : List A → P)
    (w : List A) : ofWords (R := R) f (wordF w) = f w := by
  have h := (FreeAlgebra.basisFreeMonoid R A).constr_basis R (fun w => f w.toList)
    (FreeMonoid.ofList w)
  rwa [basisFreeMonoid_apply, FreeMonoid.toList_ofList] at h

end Words

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- A **type `A` module** over the ungraded differential algebra `(A, d)`: a right `A∞` module
with operations `m_{k+1}(x, a₁, …, a_k) = act (ι a₁ * ⋯ * ι a_k) x`, multilinear in the algebra
inputs, satisfying the `A∞` relations with no signs:

`∑ᵢ m(m(x, a₁, …, aᵢ), aᵢ₊₁, …, aₙ) + ∑ᵢ m(x, a₁, …, d aᵢ, …, aₙ) +`
`∑ᵢ m(x, a₁, …, aᵢ aᵢ₊₁, …, aₙ) = 0`

for every word `a₁ ⋯ aₙ`. Strict unitality, which Lipshitz, Ozsváth and Thurston include in the
definition, is not required here: the box tensor product does not use it. -/
@[ext]
structure TypeAModule (d : A →ₗ[R] A) (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The operations: `act (ι a₁ * ⋯ * ι a_k) x = m_{k+1}(x, a₁, …, a_k)`. -/
  act : TensorAlgebra R A →ₗ[R] Module.End R M
  /-- The `A∞` relation for the word `w`. -/
  relation (w : List A) (x : M) :
    ∑ i ∈ range (w.length + 1),
        act ((w.drop i).map (TensorAlgebra.ι R)).prod
          (act ((w.take i).map (TensorAlgebra.ι R)).prod x) +
      ∑ i ∈ range w.length,
        act (((w.take i).map (TensorAlgebra.ι R)).prod * TensorAlgebra.ι R (d (w.getD i 0)) *
          ((w.drop (i + 1)).map (TensorAlgebra.ι R)).prod) x +
      ∑ i ∈ range (w.length - 1),
        act (((w.take i).map (TensorAlgebra.ι R)).prod *
          TensorAlgebra.ι R (w.getD i 0 * w.getD (i + 1) 0) *
          ((w.drop (i + 2)).map (TensorAlgebra.ι R)).prod) x = 0

namespace TypeDStructure

variable {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*} [Fintype X]

/-- The coefficient matrix of a type `D` structure with entries `ι (δ x y)` in the tensor algebra
of `A` over `R`. The entry at `(x, y)` of its `k`-th power is the coefficient of `y` in the iterate
`δ^k x ∈ A^{⊗k} ⊗ N`, viewed in the tensor algebra, so `N` is bounded, `δ^k = 0` for large `k`,
exactly when some power of this matrix vanishes. -/
def tensorCoeff (N : TypeDStructure d ι X) : Matrix X X (TensorAlgebra R A) :=
  N.coeff.map (TensorAlgebra.ι R)

@[simp]
theorem tensorCoeff_apply (N : TypeDStructure d ι X) (x y : X) :
    N.tensorCoeff x y = TensorAlgebra.ι R (N.coeff x y) :=
  (rfl)

end TypeDStructure

/-! ### The bar operations on words -/

section Bar

variable (R) in
/-- The splitting of a word into a prefix and a suffix in all ways. -/
private def deconcat : FreeAlgebra R A →ₗ[R] FreeAlgebra R A ⊗[R] FreeAlgebra R A :=
  ofWords fun w => ∑ i ∈ range (w.length + 1), wordF (w.take i) ⊗ₜ[R] wordF (w.drop i)

/-- The letters of a word differentiated one at a time. -/
private def diffF (d : A →ₗ[R] A) : FreeAlgebra R A →ₗ[R] FreeAlgebra R A :=
  ofWords fun w => ∑ i ∈ range w.length,
    wordF (w.take i) * FreeAlgebra.ι R (d (w.getD i 0)) * wordF (w.drop (i + 1))

variable (R) in
/-- Adjacent letters of a word multiplied, one pair at a time. -/
private def mergeF : FreeAlgebra R A →ₗ[R] FreeAlgebra R A :=
  ofWords fun w => ∑ i ∈ range (w.length - 1),
    wordF (w.take i) * FreeAlgebra.ι R (w.getD i 0 * w.getD (i + 1) 0) * wordF (w.drop (i + 2))

variable (R A) in
/-- The quotient map from the free algebra to the tensor algebra, making the letters
multilinear. -/
private def toTensor : FreeAlgebra R A →ₐ[R] TensorAlgebra R A :=
  FreeAlgebra.lift R fun a => TensorAlgebra.ι R a

private theorem toTensor_ι (a : A) :
    toTensor R A (FreeAlgebra.ι R a) = TensorAlgebra.ι R a :=
  FreeAlgebra.lift_ι_apply _ _

private theorem toTensor_wordF (w : List A) :
    toTensor R A (wordF w) = (w.map (TensorAlgebra.ι R)).prod := by
  simp [wordF, map_list_prod, List.map_map, Function.comp_def, toTensor_ι]

omit [Ring A] [Algebra R A] in
private theorem deconcat_wordF_concat (w : List A) (a : A) :
    deconcat R (wordF (w ++ [a])) =
      deconcat R (wordF w) * (1 ⊗ₜ FreeAlgebra.ι R a) + wordF (w ++ [a]) ⊗ₜ[R] 1 := by
  simp only [deconcat, ofWords_wordF]
  rw [List.length_append, List.length_singleton, sum_range_succ, sum_mul]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi : i ≤ w.length := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [List.take_append_of_le_length hi, List.drop_append_of_le_length hi, wordF_concat,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp), wordF_nil]

omit [Ring A] [Algebra R A] in
/-- Splitting a word ending in `a`: the splittings of `w a` are those of `w` with `a` appended to
the suffix, and the splitting with empty suffix. -/
private theorem deconcat_mul_ι (s : FreeAlgebra R A) (a : A) :
    deconcat R (s * FreeAlgebra.ι R a) =
      deconcat R s * (1 ⊗ₜ FreeAlgebra.ι R a) + (s * FreeAlgebra.ι R a) ⊗ₜ 1 := by
  have h : (deconcat R).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)) =
      (LinearMap.mulRight R (1 ⊗ₜ[R] FreeAlgebra.ι R a)).comp (deconcat R) +
        ((TensorProduct.mk R _ _).flip 1).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)) := by
    refine linearMap_ext_wordF fun w => ?_
    simpa [← wordF_concat] using deconcat_wordF_concat (R := R) w a
  exact LinearMap.congr_fun h s

private theorem diffF_wordF_concat (d : A →ₗ[R] A) (w : List A) (a : A) :
    diffF d (wordF (w ++ [a])) =
      diffF d (wordF w) * FreeAlgebra.ι R a + wordF w * FreeAlgebra.ι R (d a) := by
  simp only [diffF, ofWords_wordF]
  rw [List.length_append, List.length_singleton, sum_range_succ, sum_mul]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi : i < w.length := mem_range.1 hi
    rw [List.take_append_of_le_length hi.le, List.getD_append _ _ _ _ hi,
      List.drop_append_of_le_length hi, wordF_concat, mul_assoc _ (wordF _)]
  · rw [List.take_append_of_le_length le_rfl, List.take_length,
      List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
      List.drop_of_length_le (by simp), wordF_nil, mul_one]

omit [Algebra R A] in
private theorem mergeF_wordF_concat_concat (w : List A) (a b : A) :
    mergeF R (wordF (w ++ [a] ++ [b])) =
      mergeF R (wordF (w ++ [a])) * FreeAlgebra.ι R b + wordF w * FreeAlgebra.ι R (a * b) := by
  simp only [mergeF, ofWords_wordF]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [sum_range_succ, sum_mul]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi : i < w.length := mem_range.1 hi
    have hi' : i + 1 < (w ++ [a]).length := by simp; omega
    rw [List.take_append_of_le_length (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ hi', List.drop_append_of_le_length (by simp; omega),
      wordF_concat, mul_assoc _ (wordF _)]
  · simp only [List.append_assoc, List.singleton_append]
    rw [List.take_append_of_le_length le_rfl, List.take_length,
      List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (Nat.le_succ _),
      Nat.sub_self, Nat.succ_sub (le_refl _), Nat.sub_self, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_cons_zero, List.drop_of_length_le (by simp), wordF_nil,
      mul_one]

/-- Differentiating the letters of a word ending in `a`. -/
private theorem diffF_mul_ι (d : A →ₗ[R] A) (s : FreeAlgebra R A) (a : A) :
    diffF d (s * FreeAlgebra.ι R a) =
      diffF d s * FreeAlgebra.ι R a + s * FreeAlgebra.ι R (d a) := by
  have h : (diffF d).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)) =
      (LinearMap.mulRight R (FreeAlgebra.ι R a)).comp (diffF d) +
        LinearMap.mulRight R (FreeAlgebra.ι R (d a)) := by
    refine linearMap_ext_wordF fun w => ?_
    simpa [← wordF_concat] using diffF_wordF_concat (R := R) d w a
  exact LinearMap.congr_fun h s

omit [Algebra R A] in
/-- Multiplying adjacent letters of a word ending in `a b`. -/
private theorem mergeF_mul_ι_mul_ι (s : FreeAlgebra R A) (a b : A) :
    mergeF R (s * FreeAlgebra.ι R a * FreeAlgebra.ι R b) =
      mergeF R (s * FreeAlgebra.ι R a) * FreeAlgebra.ι R b + s * FreeAlgebra.ι R (a * b) := by
  have h : (mergeF R).comp
        ((LinearMap.mulRight R (FreeAlgebra.ι R b)).comp
          (LinearMap.mulRight R (FreeAlgebra.ι R a))) =
      ((LinearMap.mulRight R (FreeAlgebra.ι R b)).comp
          ((mergeF R).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)))) +
        LinearMap.mulRight R (FreeAlgebra.ι R (a * b)) := by
    refine linearMap_ext_wordF fun w => ?_
    simpa [← wordF_concat] using mergeF_wordF_concat_concat (R := R) w a b
  exact LinearMap.congr_fun h s

omit [Ring A] [Algebra R A] in
private theorem deconcat_one :
    deconcat R (1 : FreeAlgebra R A) = (1 : FreeAlgebra R A ⊗[R] FreeAlgebra R A) := by
  rw [← wordF_nil, deconcat, ofWords_wordF]
  simp [wordF_nil, Algebra.TensorProduct.one_def]

private theorem diffF_one (d : A →ₗ[R] A) : diffF d (1 : FreeAlgebra R A) = 0 := by
  rw [← wordF_nil, diffF, ofWords_wordF]
  simp

omit [Algebra R A] in
private theorem mergeF_one : mergeF R (1 : FreeAlgebra R A) = 0 := by
  rw [← wordF_nil, mergeF, ofWords_wordF]
  simp

omit [Algebra R A] in
private theorem mergeF_ι (a : A) : mergeF R (FreeAlgebra.ι R a) = 0 := by
  have h : (FreeAlgebra.ι R a : FreeAlgebra R A) = wordF [a] := by simp [wordF]
  rw [h, mergeF, ofWords_wordF]
  simp

end Bar

/-! ### Iterates of a type `D` structure in the free algebra -/

section Iterates

variable {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]

/-- The coefficient matrix with letter entries `ι (δ x y)` in the free algebra. -/
private def letterCoeff (N : TypeDStructure d ι X) : Matrix X X (FreeAlgebra R A) :=
  N.coeff.map (FreeAlgebra.ι R)

omit [DecidableEq X] in
private theorem letterCoeff_apply (N : TypeDStructure d ι X) (x y : X) :
    letterCoeff N x y = FreeAlgebra.ι R (N.coeff x y) :=
  (rfl)

private theorem toTensor_letterCoeff_pow (N : TypeDStructure d ι X) (n : ℕ) (x y : X) :
    toTensor R A ((letterCoeff N ^ n) x y) = (N.tensorCoeff ^ n) x y := by
  have h : (toTensor R A).mapMatrix (letterCoeff N) =
      N.tensorCoeff := by
    ext x y
    simp [letterCoeff, TypeDStructure.tensorCoeff, toTensor_ι]
  have := congrArg (fun P => P x y)
    (map_pow ((toTensor R A).mapMatrix) (letterCoeff N) n)
  simpa [h] using this

/-- **Splitting the iterates.** The splittings of the paths of length `n` from `x` to `z` are the
pairs of a path of length `j` from `x` to some `y` and a path of length `n - j` from `y` to `z`. -/
private theorem deconcat_letterCoeff_pow (N : TypeDStructure d ι X) (n : ℕ) (x z : X) :
    deconcat R ((letterCoeff N ^ n) x z) =
      ∑ j ∈ range (n + 1), ∑ y, (letterCoeff N ^ j) x y ⊗ₜ[R] (letterCoeff N ^ (n - j)) y z := by
  induction n generalizing z with
  | zero =>
    simp only [zero_add, sum_range_one, Nat.sub_zero, pow_zero, Matrix.one_apply]
    by_cases h : x = z
    · subst h
      rw [sum_eq_single x (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
      simp [deconcat_one, Algebra.TensorProduct.one_def]
    · simp only [h, ite_false, map_zero]
      refine (sum_eq_zero fun y _ => ?_).symm
      by_cases hy : x = y
      · subst hy
        simp [h]
      · simp [hy]
  | succ n ih =>
    have key : ∀ y, deconcat R ((letterCoeff N ^ n) x y * letterCoeff N y z) =
        (∑ j ∈ range (n + 1), ∑ w,
          (letterCoeff N ^ j) x w ⊗ₜ[R] ((letterCoeff N ^ (n - j)) w y * letterCoeff N y z)) +
          ((letterCoeff N ^ n) x y * letterCoeff N y z) ⊗ₜ[R] 1 := by
      intro y
      rw [letterCoeff_apply, deconcat_mul_ι, ← letterCoeff_apply, ih, sum_mul]
      simp only [sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [pow_succ, Matrix.mul_apply, map_sum]
    simp only [key, sum_add_distrib]
    rw [sum_range_succ (n := n + 1), Nat.sub_self, pow_zero]
    congr 1
    · rw [sum_comm]
      refine sum_congr rfl fun j hj => ?_
      rw [sum_comm]
      refine sum_congr rfl fun w _ => ?_
      rw [← tmul_sum, Nat.sub_add_comm (Nat.lt_succ_iff.1 (mem_range.1 hj)), pow_succ,
        Matrix.mul_apply]
    · rw [← sum_tmul, ← Matrix.mul_apply, ← pow_succ,
        sum_eq_single z (fun y _ hy => by simp [hy]) (by simp)]
      simp

/-- The differentiated letters of the iterates, in the tensor algebra. -/
private def diffMat (N : TypeDStructure d ι X) (n : ℕ) : Matrix X X (TensorAlgebra R A) :=
  fun x z => toTensor R A (diffF d ((letterCoeff N ^ n) x z))

/-- The multiplied adjacent letters of the iterates, in the tensor algebra. -/
private def mergeMat (N : TypeDStructure d ι X) (n : ℕ) : Matrix X X (TensorAlgebra R A) :=
  fun x z => toTensor R A (mergeF R ((letterCoeff N ^ n) x z))

private theorem diffMat_zero (N : TypeDStructure d ι X) : diffMat N 0 = 0 := by
  ext x z
  by_cases h : x = z <;> simp [diffMat, h, diffF_one]

private theorem mergeMat_zero (N : TypeDStructure d ι X) : mergeMat N 0 = 0 := by
  ext x z
  by_cases h : x = z <;> simp [mergeMat, h, mergeF_one]

private theorem mergeMat_one (N : TypeDStructure d ι X) : mergeMat N 1 = 0 := by
  ext x z
  simp [mergeMat, letterCoeff, mergeF_ι]

/-- `Q_{n+1} = Q_n δ + δ^n (d δ)`, by the Leibniz rule for the differentiated letters. -/
private theorem diffMat_succ (N : TypeDStructure d ι X) (n : ℕ) :
    diffMat N (n + 1) = diffMat N n * N.tensorCoeff +
      N.tensorCoeff ^ n * (N.coeff.map d).map (TensorAlgebra.ι R) := by
  ext x z
  simp only [diffMat, pow_succ, Matrix.mul_apply, map_sum, letterCoeff_apply, Matrix.map_apply,
    diffF_mul_ι, map_add, map_mul, sum_add_distrib, toTensor_ι, toTensor_letterCoeff_pow,
    Matrix.add_apply, TypeDStructure.tensorCoeff_apply]

/-- `P_{n+2} = P_{n+1} δ + δ^n (δ * δ)`: the new adjacent pair is the last two letters. -/
private theorem mergeMat_add_two (N : TypeDStructure d ι X) (n : ℕ) :
    mergeMat N (n + 2) = mergeMat N (n + 1) * N.tensorCoeff +
      N.tensorCoeff ^ n * (N.coeff * N.coeff).map (TensorAlgebra.ι R) := by
  ext x z
  have hpow : (letterCoeff N ^ (n + 2)) x z =
      ∑ y, ∑ w, (letterCoeff N ^ n) x w * FreeAlgebra.ι R (N.coeff w y) *
        FreeAlgebra.ι R (N.coeff y z) := by
    rw [pow_succ, Matrix.mul_apply]
    refine sum_congr rfl fun y _ => ?_
    simp only [pow_succ, Matrix.mul_apply, sum_mul, letterCoeff_apply]
  simp only [mergeMat, hpow, map_sum, mergeF_mul_ι_mul_ι, map_add, map_mul, sum_add_distrib,
    toTensor_ι, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply,
    TypeDStructure.tensorCoeff_apply]
  congr 1
  · refine sum_congr rfl fun y _ => ?_
    simp only [← sum_mul, ← map_sum, pow_succ (letterCoeff N) n, Matrix.mul_apply,
      letterCoeff_apply]
  · rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [← mul_sum, ← map_sum, toTensor_letterCoeff_pow]

/-- In characteristic two the structure equation `d δ = δ * δ` makes the two recursions agree:
`P_{n+1} = Q_n`. -/
private theorem mergeMat_succ [CharP R 2] (N : TypeDStructure d ι X) (n : ℕ) :
    mergeMat N (n + 1) = diffMat N n := by
  induction n with
  | zero => rw [mergeMat_one, diffMat_zero]
  | succ n ih =>
    rw [mergeMat_add_two, ih, diffMat_succ, N.map_coeff_eq_coeff_mul_coeff]

/-- Once `δ^K = 0`, `Q_{K+m} = Q_K δ^m`; in particular `Q_{2K} = 0`. -/
private theorem diffMat_two_mul_eq_zero (N : TypeDStructure d ι X) {K : ℕ}
    (hK : N.tensorCoeff ^ K = 0) : diffMat N (2 * K) = 0 := by
  have h : ∀ m, diffMat N (K + m) = diffMat N K * N.tensorCoeff ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← add_assoc, diffMat_succ, ih, pow_eq_zero_of_le (Nat.le_add_right K m) hK, zero_mul,
        add_zero, pow_succ, mul_assoc]
  rw [two_mul, h, hK, mul_zero]

end Iterates

/-! ### The `A∞` relations on the free algebra -/

namespace TypeAModule

variable {d : A →ₗ[R] A} {M : Type*} [AddCommGroup M] [Module R M] (MM : TypeAModule d M)

/-- The action of a splitting `u ⊗ v` of a word: `act v ∘ act u`. -/
private def splitAct : FreeAlgebra R A ⊗[R] FreeAlgebra R A →ₗ[R] Module.End R M :=
  TensorProduct.lift ((LinearMap.mul R (Module.End R M)).flip.compl₁₂
    (MM.act.comp (toTensor R A).toLinearMap) (MM.act.comp (toTensor R A).toLinearMap))

private theorem splitAct_tmul (u v : FreeAlgebra R A) :
    MM.splitAct (u ⊗ₜ v) = MM.act (toTensor R A v) * MM.act (toTensor R A u) := by
  simp [splitAct]

/-- **The `A∞` relations on the free algebra.** For every `s`, the action of the splittings of `s`
plus the action of its bar differential vanishes; on words this is `TypeAModule.relation`. -/
private theorem splitAct_deconcat_add (s : FreeAlgebra R A) :
    MM.splitAct (deconcat R s) + MM.act (toTensor R A (diffF d s + mergeF R s)) = 0 := by
  have h : MM.splitAct.comp (deconcat R) +
      MM.act.comp ((toTensor R A).toLinearMap.comp (diffF d + mergeF R)) = 0 := by
    refine linearMap_ext_wordF fun w => ?_
    ext x
    simpa [deconcat, diffF, mergeF, ofWords_wordF, splitAct_tmul, toTensor_wordF, toTensor_ι,
      LinearMap.sum_apply, add_assoc] using MM.relation w x
  exact LinearMap.congr_fun h s

/-! ### The box tensor product -/

section BoxTensor

variable {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]

/-- The **differential of the box tensor product** `M ⊠ N`, truncated at `K`, on row vectors
`φ : X → M`, standing for `∑ x, φ x ⊗ x`:
`(∂ φ) z = ∑_{k < K} ∑_x act ((δ^k) x z) (φ x)`, that is
`∂ (m ⊗ x) = ∑_{k < K} (m_{k+1} ⊗ 1) (m ⊗ δ^k x)`. When `N` is bounded with `δ^K = 0` this is the
whole sum (`TauCeti.TypeAModule.boxDifferential_eq_of_le`). -/
def boxDifferential (N : TypeDStructure d ι X) (K : ℕ) : (X → M) →ₗ[R] (X → M) :=
  LinearMap.pi fun z => ∑ k ∈ range K, ∑ x, (MM.act ((N.tensorCoeff ^ k) x z)).comp
    (LinearMap.proj x)

theorem boxDifferential_apply (N : TypeDStructure d ι X) (K : ℕ) (φ : X → M) (z : X) :
    MM.boxDifferential N K φ z = ∑ k ∈ range K, ∑ x, MM.act ((N.tensorCoeff ^ k) x z) (φ x) := by
  simp [boxDifferential]

/-- **Finite evaluation.** If `δ^K = 0`, the truncation of the box differential at any `K' ≥ K`
is its truncation at `K`: the terms `k ≥ K` of the sum vanish. -/
theorem boxDifferential_eq_of_le {N : TypeDStructure d ι X} {K K' : ℕ}
    (hK : N.tensorCoeff ^ K = 0) (h : K ≤ K') :
    MM.boxDifferential N K' = MM.boxDifferential N K := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [boxDifferential_apply, boxDifferential_apply]
  refine (sum_subset (range_subset_range.2 h) fun k _ hk => ?_).symm
  simp [pow_eq_zero_of_le (not_lt.1 (mem_range.not.1 hk)) hK]

/-- **The box tensor differential squares to zero** when `N` is bounded, `δ^K = 0`
(Lipshitz–Ozsváth–Thurston, Proposition 2.3.10). This uses the `A∞` relations of `M` and the
structure equation of `N`. -/
theorem boxDifferential_boxDifferential [CharP R 2] {N : TypeDStructure d ι X} {K : ℕ}
    (hK : N.tensorCoeff ^ K = 0) (φ : X → M) :
    MM.boxDifferential N K (MM.boxDifferential N K φ) = 0 := by
  funext z
  -- `f j k x` is the action of the paths of length `j` from `x` followed by those of length `k`
  -- ending at `z`.
  set f : ℕ → ℕ → X → Module.End R M := fun j k x =>
    ∑ y, MM.act ((N.tensorCoeff ^ k) y z) * MM.act ((N.tensorCoeff ^ j) x y) with hf
  have hvan : ∀ j k x, K ≤ j ∨ K ≤ k → f j k x = 0 := by
    rintro j k x (h | h) <;> simp [hf, pow_eq_zero_of_le h hK]
  have hexpand : MM.boxDifferential N K (MM.boxDifferential N K φ) z =
      ∑ x, ∑ j ∈ range K, ∑ k ∈ range K, f j k x (φ x) := by
    simp only [boxDifferential_apply, map_sum, LinearMap.sum_apply, hf, mul_apply_eq_comp]
    -- Reorder the sums over `k`, `y`, `j`, `x` as `x`, `j`, `k`, `y`.
    conv_lhs =>
      enter [2, k]
      rw [sum_comm]
      enter [2, j]
      rw [sum_comm]
    conv_lhs =>
      rw [sum_comm]
      enter [2, j]
      rw [sum_comm]
    rw [sum_comm]
  -- The splittings of the paths of length at most `2 K` give the double sum.
  set s : X → FreeAlgebra R A := fun x => ∑ n ∈ range (2 * K + 1), (letterCoeff N ^ n) x z
    with hs
  have hsplit : ∀ x, MM.splitAct (deconcat R (s x)) = ∑ j ∈ range K, ∑ k ∈ range K, f j k x := by
    intro x
    have h1 : MM.splitAct (deconcat R (s x)) =
        ∑ n ∈ range (2 * K + 1), ∑ j ∈ range (n + 1), f j (n - j) x := by
      simp only [hs, map_sum, deconcat_letterCoeff_pow, splitAct_tmul, toTensor_letterCoeff_pow,
        hf]
    have hflip := sum_range_diag_flip (2 * K + 1) fun j k => f j k x
    rw [h1, hflip]
    rw [← sum_subset (range_subset_range.2 (by omega : K ≤ 2 * K + 1)) fun j _ hj => sum_eq_zero
      fun k _ => hvan j k x (Or.inl (not_lt.1 (mem_range.not.1 hj)))]
    refine sum_congr rfl fun j hj => ?_
    have hj : j < K := mem_range.1 hj
    exact (sum_subset (range_subset_range.2 (by omega)) fun k _ hk =>
      hvan j k x (Or.inr (not_lt.1 (mem_range.not.1 hk)))).symm
  -- The bar differential of `s x` acts by zero.
  have hbar : ∀ x, toTensor R A (diffF d (s x) + mergeF R (s x)) = 0 := by
    intro x
    have h : ∀ n, ∑ m ∈ range (n + 1), (diffMat N m + mergeMat N m) = diffMat N n := by
      intro n
      induction n with
      | zero => simp [diffMat_zero, mergeMat_zero]
      | succ n ih =>
        rw [sum_range_succ, ih, mergeMat_succ, add_comm (diffMat N _), add_assoc,
          ← two_smul R (diffMat N n), CharTwo.two_eq_zero, zero_smul, add_zero]
    have := congrFun₂ (h (2 * K)) x z
    rw [diffMat_two_mul_eq_zero N hK] at this
    simpa [hs, diffMat, mergeMat, Matrix.sum_apply, map_sum, sum_add_distrib] using this
  rw [hexpand]
  refine sum_eq_zero fun x _ => ?_
  have h := MM.splitAct_deconcat_add (s x)
  rw [hbar x, map_zero, add_zero, hsplit x] at h
  simp only [← LinearMap.sum_apply, h, LinearMap.zero_apply]

end BoxTensor

/-! ### Differential modules as type `A` modules -/

section DG

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

variable (R A M) in
/-- Right multiplication `m ↦ m * a`, as an `R`-linear function of `a`. -/
private def rightMul : A →ₗ[R] Module.End R M :=
  (Algebra.lsmul R R M).toLinearMap.comp (MulOpposite.opLinearEquiv R).toLinearMap

private theorem rightMul_apply (a : A) (m : M) : rightMul R A M a m = op a • m :=
  (rfl)

variable (R A M) in
/-- The algebra map `T(A) → End (M × M)` with `ι a ↦ ((m, m') ↦ (m' * a, 0))`. Products of two or
more generators act by zero, so a differential module, whose operations vanish beyond `m₂`, can be
read off it. -/
private def dgRep : TensorAlgebra R A →ₐ[R] Module.End R (M × M) :=
  TensorAlgebra.lift R
    ((LinearMap.llcomp R (M × M) M (M × M) (LinearMap.inl R M M)).comp
      ((LinearMap.lcomp R M (LinearMap.snd R M M)).comp (rightMul R A M)))

private theorem dgRep_ι_apply (a : A) (v : M × M) :
    dgRep R A M (TensorAlgebra.ι R a) v = (op a • v.2, 0) := by
  simp [dgRep, rightMul_apply]

private theorem dgRep_ι_mul_ι (a b : A) :
    dgRep R A M (TensorAlgebra.ι R a * TensorAlgebra.ι R b) = 0 := by
  ext v <;> simp [dgRep_ι_apply]

/-- `dgRep` kills every word with at least two letters. -/
private theorem dgRep_list_prod {w : List A} (hw : 2 ≤ w.length) :
    dgRep R A M (w.map (TensorAlgebra.ι R)).prod = 0 := by
  match w, hw with
  | a :: b :: w, _ =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← mul_assoc, map_mul,
      dgRep_ι_mul_ι, zero_mul]

variable (A) in
/-- The operations of the type `A` module of a differential module:
`t ↦ (m ↦ (dgRep t (dM m, m)).1)`, so `1` acts by `dM`, `ι a` by `m ↦ m * a`, and longer words by
zero. -/
private def dgAct (dM : M →ₗ[R] M) : TensorAlgebra R A →ₗ[R] Module.End R M where
  toFun t := (LinearMap.fst R M M).comp ((dgRep R A M t).comp (dM.prod LinearMap.id))
  map_add' s t := by
    ext m
    simp
  map_smul' r t := by
    ext m
    simp

private theorem dgAct_apply (dM : M →ₗ[R] M) (t : TensorAlgebra R A) (m : M) :
    dgAct A dM t m = (dgRep R A M t (dM m, m)).1 :=
  (rfl)

private theorem dgAct_one (dM : M →ₗ[R] M) (m : M) : dgAct A dM 1 m = dM m := by
  simp [dgAct_apply]

private theorem dgAct_ι (dM : M →ₗ[R] M) (a : A) (m : M) :
    dgAct A dM (TensorAlgebra.ι R a) m = op a • m := by
  simp [dgAct_apply, dgRep_ι_apply]

private theorem dgAct_list_prod (dM : M →ₗ[R] M) {w : List A} (hw : 2 ≤ w.length) :
    dgAct A dM (w.map (TensorAlgebra.ι R)).prod = 0 := by
  ext m
  simp [dgAct_apply, dgRep_list_prod hw]

private theorem dgAct_ι_mul_ι (dM : M →ₗ[R] M) (a b : A) :
    dgAct A dM (TensorAlgebra.ι R a * TensorAlgebra.ι R b) = 0 := by
  ext m
  simp [dgAct_apply, dgRep_ι_mul_ι]

private theorem dgAct_mul_ι_mul (dM : M →ₗ[R] M) (u v : List A) (a : A)
    (h : 1 ≤ u.length + v.length) :
    dgAct A dM ((u.map (TensorAlgebra.ι R)).prod * TensorAlgebra.ι R a *
      (v.map (TensorAlgebra.ι R)).prod) = 0 := by
  have : (u.map (TensorAlgebra.ι R)).prod * TensorAlgebra.ι R a * (v.map (TensorAlgebra.ι R)).prod =
      ((u ++ a :: v).map (TensorAlgebra.ι R)).prod := by
    simp [List.prod_append, mul_assoc]
  rw [this]
  exact dgAct_list_prod dM (by simp; omega)

/-- **A differential right module is a type `A` module**, with `m₁ = dM`, `m₂(m, a) = m * a` and
`m_{k+1} = 0` for `k ≥ 2`. Its `A∞` relations are `dM ∘ dM = 0`, the Leibniz rule and the
associativity of the action. -/
def ofDGModule [CharP R 2] {dM : M →ₗ[R] M} (hM : IsUngradedDGRightModule d dM) :
    TypeAModule d M where
  act := dgAct A dM
  relation w x := by
    have h2 : ∀ m : M, m + m = 0 := fun m => by
      rw [← two_smul R m, CharTwo.two_eq_zero, zero_smul]
    match w with
    | [] => simp [dgAct_one, hM.map_map]
    | [a] =>
      -- The Leibniz rule `dM (x * a) = dM x * a + x * d a`.
      have key : op a • dM x + dM (op a • x) + op (d a) • x = 0 := by
        rw [hM.map_smul]
        calc op a • dM x + (op a • dM x + op (d a) • x) + op (d a) • x =
            (op a • dM x + op a • dM x) + (op (d a) • x + op (d a) • x) := by abel
          _ = 0 := by rw [h2, h2, add_zero]
      simpa [sum_range_succ, dgAct_one, dgAct_ι] using key
    | [a, b] =>
      simp [sum_range_succ, dgAct_one, dgAct_ι, dgAct_ι_mul_ι, op_mul, mul_smul, h2]
    | a :: b :: c :: w =>
      have hd : ∀ i ∈ range (a :: b :: c :: w).length,
          dgAct A dM ((((a :: b :: c :: w).take i).map (TensorAlgebra.ι R)).prod *
            TensorAlgebra.ι R (d ((a :: b :: c :: w).getD i 0)) *
            (((a :: b :: c :: w).drop (i + 1)).map (TensorAlgebra.ι R)).prod) x = 0 := by
        intro i hi
        rw [dgAct_mul_ι_mul (R := R) dM _ _ _ (by simp; omega), LinearMap.zero_apply]
      have hm : ∀ i ∈ range ((a :: b :: c :: w).length - 1),
          dgAct A dM ((((a :: b :: c :: w).take i).map (TensorAlgebra.ι R)).prod *
            TensorAlgebra.ι R ((a :: b :: c :: w).getD i 0 * (a :: b :: c :: w).getD (i + 1) 0) *
            (((a :: b :: c :: w).drop (i + 2)).map (TensorAlgebra.ι R)).prod) x = 0 := by
        intro i hi
        rw [dgAct_mul_ι_mul (R := R) dM _ _ _ (by simp at hi ⊢; omega), LinearMap.zero_apply]
      have hs : ∀ i ∈ range ((a :: b :: c :: w).length + 1),
          dgAct A dM (((a :: b :: c :: w).drop i).map (TensorAlgebra.ι R)).prod
            (dgAct A dM (((a :: b :: c :: w).take i).map (TensorAlgebra.ι R)).prod x) = 0 := by
        intro i hi
        simp only [mem_range] at hi
        rcases Nat.lt_or_ge i 2 with hi2 | hi2
        · rw [dgAct_list_prod (R := R) dM (by simp; omega), LinearMap.zero_apply]
        · rw [dgAct_list_prod (R := R) dM (w := List.take i (a :: b :: c :: w)) (by simp; omega),
            LinearMap.zero_apply, map_zero]
      rw [sum_eq_zero hs, sum_eq_zero hd, sum_eq_zero hm, add_zero, add_zero]

private theorem dgAct_mul_ι_mul_ι (dM : M →ₗ[R] M) (t : TensorAlgebra R A) (a b : A) :
    dgAct A dM (t * TensorAlgebra.ι R a * TensorAlgebra.ι R b) = 0 := by
  ext m
  simp [dgAct_apply, mul_assoc, dgRep_ι_mul_ι]

@[simp]
theorem ofDGModule_act_one [CharP R 2] {dM : M →ₗ[R] M} (hM : IsUngradedDGRightModule d dM)
    (m : M) : (ofDGModule hM).act 1 m = dM m :=
  dgAct_one dM m

@[simp]
theorem ofDGModule_act_ι [CharP R 2] {dM : M →ₗ[R] M} (hM : IsUngradedDGRightModule d dM)
    (a : A) (m : M) : (ofDGModule hM).act (TensorAlgebra.ι R a) m = op a • m :=
  dgAct_ι dM a m

/-- The operations `m_{k+1}` of the type `A` module of a differential module vanish for `k ≥ 2`. -/
@[simp]
theorem ofDGModule_act_mul_ι_mul_ι [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (t : TensorAlgebra R A) (a b : A) :
    (ofDGModule hM).act (t * TensorAlgebra.ι R a * TensorAlgebra.ι R b) = 0 :=
  dgAct_mul_ι_mul_ι dM t a b

variable {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X] in
/-- **For a differential module the box tensor differential is the classical one**: truncated at
any `K ≥ 2`, it is `TauCeti.TypeDStructure.boxDifferential`,
`∂ (m ⊗ x) = dM m ⊗ x + ∑ y, m * δ x y ⊗ y`, for every type `D` structure `N`, bounded or not. -/
theorem boxDifferential_ofDGModule [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (N : TypeDStructure d ι X) {K : ℕ} (hK : 2 ≤ K) :
    (ofDGModule hM).boxDifferential N K = N.boxDifferential dM := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le' hK
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [boxDifferential_apply, TypeDStructure.boxDifferential_apply, sum_range_succ',
    sum_range_succ', sum_eq_zero fun k _ => sum_eq_zero fun x _ => ?_, zero_add]
  · simp only [zero_add, pow_one, pow_zero, Pi.add_apply, Matrix.one_apply]
    rw [add_comm]
    congr 1
    · rw [sum_eq_single z (fun x _ hx => by simp [hx]) (by simp)]
      simp
    · rw [continuationMap_apply (R := R) (M := M) N.coeff]
      simp [TypeDStructure.tensorCoeff_apply]
  · have h : (N.tensorCoeff ^ (k + 1 + 1)) x z = ∑ y, ∑ w, (N.tensorCoeff ^ k) x w *
        TensorAlgebra.ι R (N.coeff w y) * TensorAlgebra.ι R (N.coeff y z) := by
      simp only [pow_succ, Matrix.mul_apply, sum_mul, TypeDStructure.tensorCoeff_apply]
    simp [h, ofDGModule_act_mul_ι_mul_ι]

end DG

end TypeAModule

end TauCeti
