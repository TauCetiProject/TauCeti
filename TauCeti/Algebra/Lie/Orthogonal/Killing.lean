/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.Lie.BaseChange.Radical
import TauCeti.Algebra.Lie.Orthogonal.Basic
import TauCeti.Algebra.Lie.SkewAdjoint.BaseChange
import TauCeti.LinearAlgebra.Matrix.SkewAdjoint

/-!
# The Killing form of the orthogonal Lie algebras

Let `J` be a symmetric invertible matrix over a field `K`, the Gram matrix of a nondegenerate
symmetric bilinear form `B(u, v) = u ⬝ᵥ J v` on `n → K`, and let
`skewAdjointMatricesLieSubalgebra J` be its orthogonal Lie algebra. When `n` has at least three
elements the standard module `n → K` of this Lie algebra is irreducible, over every field. In
characteristic zero it follows that the Lie algebra has trivial radical, so by Cartan's criterion
its Killing form is nondegenerate. Over an algebraically closed field the standard module is
faithful, trace-free and irreducible, and
`LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful` applies; over an arbitrary field
of characteristic zero, the orthogonal Lie algebra of `J` becomes that of the image of `J` over an
algebraic closure after extension of scalars
(`TauCeti.skewAdjointMatricesLieSubalgebraBaseChangeEquiv`), and triviality of the radical
descends (`LieAlgebra.hasTrivialRadical_baseChange_iff`).

Mathlib's definite orthogonal Lie algebra `LieAlgebra.Orthogonal.so n K` (`J = 1`) and its
indefinite orthogonal Lie algebra `LieAlgebra.Orthogonal.so' p q K` (`J` diagonal with `p` entries
`1` and `q` entries `-1`) are the two instances recorded here. Over `ℝ` the second is `so(p, q)`,
which therefore has trivial radical, and so is semisimple (`LieAlgebra.IsSemisimple`, through
Mathlib's instances), as soon as `p + q ≥ 3`. Nothing here asserts simplicity, which fails for
`so(2, 2) ≅ sl₂(ℝ) × sl₂(ℝ)`. The bound cannot be lowered: for `p + q = 2` the Lie algebra is
one-dimensional, hence abelian.

The irreducibility argument uses, for vectors `u` and `v`, the element of the orthogonal Lie
algebra sending `x` to `B(u, x) v - B(v, x) u`. Applied to a vector `x` of a nonzero Lie submodule
`N` with `B(u, x) ≠ 0`, it shows that `N` contains the whole hyperplane `x^⊥` of vectors orthogonal
to `x`. If `N` also contains a vector `z` with `B(z, x) ≠ 0`, then `N = x^⊥ + K z` is everything.
Otherwise `N` lies in `x^⊥`, so for every `y ∈ N` the hyperplane `y^⊥ ⊆ N` lies in `x^⊥`, and `x`
is a multiple of `y`. With a third index, `x^⊥` contains two vectors that are not proportional,
and `x ≠ 0` cannot be a multiple of both.

## Main results

* `TauCeti.isIrreducible_skewAdjointMatricesLieSubalgebra_standard`: the standard module of the
  orthogonal Lie algebra of a symmetric invertible matrix is irreducible when the index type has
  at least three elements.
* `TauCeti.hasTrivialRadical_skewAdjointMatricesLieSubalgebra`: in characteristic zero, the
  orthogonal Lie algebra of a symmetric invertible matrix has trivial radical when the index type
  has at least three elements; in particular its Killing form is nondegenerate.
* `TauCeti.isIrreducible_so_standard`, `TauCeti.hasTrivialRadical_so`: the definite case.
* `TauCeti.isIrreducible_so'_standard`, `TauCeti.hasTrivialRadical_so'`: the indefinite case,
  in particular the semisimplicity of `so(p, q)` for `p + q ≥ 3`.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lecture 18 (the orthogonal Lie algebras).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2, 5 and 19.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, Chapter I (the real forms `so(p, q)` among
  the examples of semisimple Lie algebras).
* Mathlib's `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful` (faithful irreducible
  modules and reductivity).
-/

public section

open Matrix _root_.LieAlgebra LieModule
open scoped TensorProduct

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

section Symmetric

variable {n : Type*} [DecidableEq n] [Fintype n] {K : Type*} [Field K] {J : Matrix n n K}

/-- A Lie submodule of the standard module of the orthogonal Lie algebra of a symmetric matrix `J`
that contains a vector `x` with `J x ≠ 0` contains every vector `v` with `v ⬝ᵥ J x = 0`. -/
private theorem mem_of_dotProduct_mulVec_eq_zero (hJ : J.IsSymm)
    (N : LieSubmodule K (skewAdjointMatricesLieSubalgebra J) (n → K)) {x v : n → K} (hx : x ∈ N)
    (hJx : J *ᵥ x ≠ 0) (hv : v ⬝ᵥ J *ᵥ x = 0) : v ∈ N := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hJx
  have hmem := (mem_skewAdjointMatricesSubmodule J _).mpr
    (isSkewAdjoint_vecMulVec_sub_vecMulVec hJ (Pi.single i 1) v)
  have h := N.lie_mem (x := ⟨_, (mem_skewAdjointMatricesLieSubalgebra J _).mpr hmem⟩) hx
  rw [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply, vecMulVec_sub_vecMulVec_mulVec, hv,
    zero_smul, sub_zero, single_one_dotProduct] at h
  exact (N.toSubmodule.smul_mem_iff hi).mp h

/-- If every vector of a Lie submodule `N` is orthogonal to `x` for the form of a symmetric matrix
`J`, then `J x` is a multiple of `J y` for every `y ∈ N` with `J y ≠ 0`: the hyperplane
orthogonal to `y` lies in `N`, hence in the hyperplane orthogonal to `x`. -/
private theorem exists_mulVec_eq_smul_mulVec (hJ : J.IsSymm)
    (N : LieSubmodule K (skewAdjointMatricesLieSubalgebra J) (n → K)) {x y : n → K}
    (hN : ∀ z ∈ N, z ⬝ᵥ J *ᵥ x = 0) (hy : y ∈ N) (hJy : J *ᵥ y ≠ 0) :
    ∃ c : K, J *ᵥ x = c • J *ᵥ y := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hJy
  refine ⟨(J *ᵥ x) k / (J *ᵥ y) k, funext fun l ↦ ?_⟩
  have h := hN _ (mem_of_dotProduct_mulVec_eq_zero hJ N hy hJy
    (v := (J *ᵥ y) k • Pi.single l 1 - (J *ᵥ y) l • Pi.single k 1)
    (by simp [sub_dotProduct, mul_comm]))
  simp only [sub_dotProduct, smul_dotProduct, single_one_dotProduct, smul_eq_mul] at h
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hk]
  linear_combination h

/-- **The standard module of the orthogonal Lie algebra of a nondegenerate symmetric form is
irreducible**, over every field, for an index type with at least three elements. -/
theorem isIrreducible_skewAdjointMatricesLieSubalgebra_standard (hJ : J.IsSymm)
    (hJu : IsUnit J) (hn : 3 ≤ Fintype.card n) :
    IsIrreducible K (skewAdjointMatricesLieSubalgebra J) (n → K) := by
  -- Every index has two others distinct from it.
  have hthird (a b : n) : ∃ c, c ≠ a ∧ c ≠ b :=
    ENat.exists_ne_ne_of_three_le (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast hn) a b
  have hinj : Function.Injective J.mulVec := mulVec_injective_iff_isUnit.mpr hJu
  have hne {w : n → K} (hw : w ≠ 0) : J *ᵥ w ≠ 0 := fun h ↦ hw (hinj (h.trans (mulVec_zero J).symm))
  have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  apply IsIrreducible.mk
  intro N hN
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((LieSubmodule.toSubmodule_eq_bot N).not.mpr hN)
  -- It suffices to find a vector of `N` that is not orthogonal to `x`.
  suffices ∃ z ∈ N, z ⬝ᵥ J *ᵥ x ≠ 0 by
    obtain ⟨z, hz, hzx⟩ := this
    rw [eq_top_iff]
    intro v _
    set t := (v ⬝ᵥ J *ᵥ x) / (z ⬝ᵥ J *ᵥ x)
    have hw : v - t • z ∈ N := mem_of_dotProduct_mulVec_eq_zero hJ N hx (hne hx0) <| by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hzx, sub_self]
    simpa using N.add_mem hw (N.smul_mem t hz)
  by_contra! hN'
  -- The vectors `y k = (J x)ᵢ eₖ - (J x)ₖ eᵢ` are orthogonal to `x`, hence lie in `N`, and `x`
  -- is a multiple of each of them with `k ≠ i`.
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hne hx0)
  set y : n → n → K := fun k ↦ (J *ᵥ x) i • Pi.single k 1 - (J *ᵥ x) k • Pi.single i 1 with hy_def
  have hy (k : n) : y k ∈ N := mem_of_dotProduct_mulVec_eq_zero hJ N hx (hne hx0) <| by
    simp [hy_def, sub_dotProduct, mul_comm]
  have hyk (k : n) (hk : k ≠ i) : y k k = (J *ᵥ x) i := by simp [hy_def, hk]
  have hmul (k : n) (hk : k ≠ i) : ∃ c : K, x = c • y k := by
    have hyk0 : y k ≠ 0 := fun h ↦ hi (by simpa [h] using (hyk k hk).symm)
    obtain ⟨c, hc⟩ := exists_mulVec_eq_smul_mulVec hJ N hN' (hy k) (hne hyk0)
    exact ⟨c, hinj (by rw [hc, mulVec_smul])⟩
  -- Two such vectors with distinct `k` are not proportional: compare a coordinate.
  obtain ⟨j, hji, -⟩ := hthird i i
  obtain ⟨m, hmi, hmj⟩ := hthird i j
  obtain ⟨c, hc⟩ := hmul j hji
  obtain ⟨d, hd⟩ := hmul m hmi
  have hxj : x j = c * (J *ᵥ x) i := by
    conv_lhs => rw [hc]
    rw [Pi.smul_apply, hyk j hji, smul_eq_mul]
  have hxj' : x j = 0 := by
    rw [hd]
    simp [hy_def, Pi.single_eq_of_ne hmj.symm, Pi.single_eq_of_ne hji]
  have hc0 : c = 0 := by
    rw [hxj', eq_comm, mul_eq_zero] at hxj
    exact hxj.resolve_right hi
  exact hx0 (by rw [hc, hc0, zero_smul])

variable (K) [CharZero K]

/-- **The orthogonal Lie algebra of a nondegenerate symmetric form has trivial radical** over every
field of characteristic zero, for an index type with at least three elements. By Cartan's criterion
its Killing form is then nondegenerate. -/
theorem hasTrivialRadical_skewAdjointMatricesLieSubalgebra (hJ : J.IsSymm) (hJu : IsUnit J)
    (hn : 3 ≤ Fintype.card n) :
    HasTrivialRadical K (skewAdjointMatricesLieSubalgebra J) := by
  let A := AlgebraicClosure K
  let : Invertible (2 : A) := invertibleOfNonzero two_ne_zero
  have hJA : IsUnit (J.map (algebraMap K A)) := by
    simpa using hJu.map (algebraMap K A).mapMatrix
  have : IsIrreducible A (skewAdjointMatricesLieSubalgebra (J.map (algebraMap K A))) (n → A) :=
    isIrreducible_skewAdjointMatricesLieSubalgebra_standard (hJ.map _) hJA hn
  have : HasTrivialRadical A (skewAdjointMatricesLieSubalgebra (J.map (algebraMap K A))) :=
    hasTrivialRadical_of_isIrreducible_of_isFaithful A _ (n → A) fun ⟨x, hx⟩ ↦ by
      simpa using Matrix.IsSkewAdjoint.trace_eq_zero hJA
        ((mem_skewAdjointMatricesSubmodule _ x).mp hx)
  -- After extension of scalars to `A`, the orthogonal Lie algebra of `J` becomes that of its image.
  have : HasTrivialRadical A (A ⊗[K] skewAdjointMatricesLieSubalgebra J) :=
    hasTrivialRadical_of_equiv (skewAdjointMatricesLieSubalgebraBaseChangeEquiv A J).symm
  exact (hasTrivialRadical_baseChange_iff K (skewAdjointMatricesLieSubalgebra J) A).mp this

end Symmetric

section Definite

variable {l : Type*} [DecidableEq l] [Fintype l] {K : Type*} [Field K]

/-- **The standard module of the orthogonal Lie algebra is irreducible** over every field, for an
index type with at least three elements. -/
theorem isIrreducible_so_standard (hl : 3 ≤ Fintype.card l) :
    IsIrreducible K (Orthogonal.so l K) (l → K) :=
  isIrreducible_skewAdjointMatricesLieSubalgebra_standard isSymm_one isUnit_one hl

variable (K) [CharZero K]

/-- **The orthogonal Lie algebra has trivial radical** over every field of characteristic zero,
for an index type with at least three elements. By Cartan's criterion its Killing form is then
nondegenerate. -/
theorem hasTrivialRadical_so (hl : 3 ≤ Fintype.card l) :
    HasTrivialRadical K (Orthogonal.so l K) :=
  hasTrivialRadical_skewAdjointMatricesLieSubalgebra K isSymm_one isUnit_one hl

end Definite

section Indefinite

variable {p q : Type*} [DecidableEq p] [DecidableEq q] [Fintype p] [Fintype q]
  {K : Type*} [Field K]

/-- **The standard module of the indefinite orthogonal Lie algebra `so(p, q)` is irreducible**
over every field, as soon as `p + q ≥ 3`. -/
theorem isIrreducible_so'_standard (hpq : 3 ≤ Fintype.card p + Fintype.card q) :
    IsIrreducible K (Orthogonal.so' p q K) (p ⊕ q → K) :=
  isIrreducible_skewAdjointMatricesLieSubalgebra_standard (isSymm_diagonal _)
    Orthogonal.isUnit_indefiniteDiagonal
    (by rwa [Fintype.card_sum])

variable (K) [CharZero K]

/-- **The indefinite orthogonal Lie algebra `so(p, q)` has trivial radical** over every field of
characteristic zero, as soon as `p + q ≥ 3`. By Cartan's criterion its Killing form is then
nondegenerate, and it is semisimple; over `ℝ` this is the semisimplicity of `so(p, q)`. -/
theorem hasTrivialRadical_so' (hpq : 3 ≤ Fintype.card p + Fintype.card q) :
    HasTrivialRadical K (Orthogonal.so' p q K) :=
  hasTrivialRadical_skewAdjointMatricesLieSubalgebra K (isSymm_diagonal _)
    Orthogonal.isUnit_indefiniteDiagonal (by rwa [Fintype.card_sum])

end Indefinite

end TauCeti
