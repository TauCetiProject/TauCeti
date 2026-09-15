/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.InvariantStructure
public import TauCeti.LinearAlgebra.Matrix.IntCast

/-!
# Multiplicative matrices and derivations of the type-F4 invariant multiplication

The invariant symmetric multiplication of the twenty-six-dimensional module of type `F₄` is
recorded by the operators `TauCeti.F4ShortRoot.multiplicationOperator`. This file introduces, over
an arbitrary commutative ring, the operator of multiplication by a vector, the matrices
multiplicative for the multiplication, and the matrices differentiating it, and proves the
structural facts those two classes satisfy.

Multiplicativity of `g` says `g (m (u, v)) = m (g u, g v)`, which in operator form is
`g ∘ m (u, ·) = m (g u, ·) ∘ g`. The multiplicative matrices contain the identity and are closed
under multiplication, and a matrix inverse to a multiplicative matrix is again multiplicative.
Differentiation says `X (m (u, v)) = m (X u, v) + m (u, X v)`, which in operator form is
`⁅X, m (u, ·)⁆ = m (X u, ·)`. The differentiating matrices are closed under the commutator, and a
multiplicative invertible matrix carries them to themselves by conjugation. Under multiplicativity
the span of the multiplication operators is likewise carried to itself, which is what makes it an
ideal invariant under the group.

Nothing below verifies either condition for any particular matrix, and no Lie algebra structure is
built on the set of differentiating matrices.

## Main definitions

* `TauCeti.F4ShortRoot.multiplicationBy`: the operator `w ↦ m (v, w)` of multiplication by a
  vector.
* `TauCeti.F4ShortRoot.PreservesMultiplication`: multiplicativity for the multiplication.
* `TauCeti.F4ShortRoot.IsDerivation`: differentiation of the multiplication.

## Main results

* `TauCeti.F4ShortRoot.preservesMultiplication_one` and
  `TauCeti.F4ShortRoot.PreservesMultiplication.mul`: the multiplicative matrices contain the
  identity and are closed under multiplication;
  `TauCeti.F4ShortRoot.PreservesMultiplication.of_mul_eq_one` inverts a multiplicative matrix.
* `TauCeti.F4ShortRoot.PreservesMultiplication.mul_multiplicationOperator_mul`: a multiplicative
  invertible matrix carries the span of the multiplication operators to itself.
* `TauCeti.F4ShortRoot.IsDerivation.bracket`: the differentiating matrices are closed under the
  commutator; `TauCeti.F4ShortRoot.IsDerivation.add` and `TauCeti.F4ShortRoot.IsDerivation.smul`
  make them a submodule.
* `TauCeti.F4ShortRoot.IsDerivation.conj`: conjugating a differentiating matrix by a
  multiplicative invertible matrix.
* `TauCeti.F4ShortRoot.IsDerivation.map`: an integral derivation differentiates the multiplication
  over every commutative ring.

## References

* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4, for the derivation algebra of the exceptional Jordan algebra.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §7.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R]

/-! ## Multiplication by a vector -/

/-- **The operator of multiplication by a vector**: the matrix of `w ↦ m (v, w)`, the linear
combination of the multiplication operators with the coordinates of `v` as coefficients. -/
def multiplicationBy (v : Fin 26 → R) : Matrix (Fin 26) (Fin 26) R :=
  ∑ a, v a • (multiplicationOperator a).map (Int.cast : ℤ → R)

/-- The defining sum of the operator of multiplication by a vector. -/
theorem multiplicationBy_def (v : Fin 26 → R) :
    multiplicationBy v = ∑ a, v a • (multiplicationOperator a).map (Int.cast : ℤ → R) := by
  rw [multiplicationBy]

/-- Multiplication by a basis vector is the corresponding multiplication operator. -/
theorem multiplicationBy_single (k : Fin 26) :
    multiplicationBy (fun a => if a = k then (1 : R) else 0) =
      (multiplicationOperator k).map (Int.cast : ℤ → R) := by
  rw [multiplicationBy_def, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The column of the identity matrix is a basis vector. -/
private theorem one_col (k : Fin 26) :
    (fun a => (1 : Matrix (Fin 26) (Fin 26) R) a k) = fun a => if a = k then (1 : R) else 0 :=
  funext fun _ => Matrix.one_apply

/-- Multiplication by the zero vector is the zero matrix. -/
@[simp]
theorem multiplicationBy_zero : multiplicationBy (0 : Fin 26 → R) = 0 := by
  rw [multiplicationBy_def]
  exact Finset.sum_eq_zero fun a _ => by rw [Pi.zero_apply, zero_smul]

/-- Multiplication by a vector is additive in the vector. -/
theorem multiplicationBy_add (u v : Fin 26 → R) :
    multiplicationBy (u + v) = multiplicationBy u + multiplicationBy v := by
  rw [multiplicationBy_def, multiplicationBy_def, multiplicationBy_def, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.add_apply, add_smul]

/-- Multiplication by a vector is homogeneous in the vector. -/
theorem multiplicationBy_smul (c : R) (v : Fin 26 → R) :
    multiplicationBy (c • v) = c • multiplicationBy v := by
  rw [multiplicationBy_def, multiplicationBy_def, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- The column of a product is the first factor applied to the column of the second. -/
theorem mulVec_col (M N : Matrix (Fin 26) (Fin 26) R) (k : Fin 26) :
    M *ᵥ (fun a => N a k) = fun a => (M * N) a k :=
  funext fun a => by rw [Matrix.mulVec_apply_eq_sum, Matrix.mul_apply]

/-- A matrix applied to a basis vector is the corresponding column. -/
theorem mulVec_single (M : Matrix (Fin 26) (Fin 26) R) (k : Fin 26) :
    M *ᵥ (fun a => if a = k then (1 : R) else 0) = fun a => M a k := by
  rw [← one_col, mulVec_col, mul_one]

/-- Multiplication by a transformed vector, expanded over the columns of the transformation. -/
theorem multiplicationBy_mulVec (M : Matrix (Fin 26) (Fin 26) R) (v : Fin 26 → R) :
    multiplicationBy (M *ᵥ v) = ∑ a, v a • multiplicationBy fun b => M b a := by
  calc multiplicationBy (M *ᵥ v)
      = ∑ b, ∑ a, (M b a * v a) • (multiplicationOperator b).map (Int.cast : ℤ → R) := by
        rw [multiplicationBy_def]
        exact Finset.sum_congr rfl fun b _ => by
          rw [Matrix.mulVec_apply_eq_sum, Finset.sum_smul]
    _ = ∑ a, ∑ b, v a • (M b a • (multiplicationOperator b).map (Int.cast : ℤ → R)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
          rw [smul_smul, mul_comm]
    _ = ∑ a, v a • multiplicationBy fun b => M b a :=
        Finset.sum_congr rfl fun a _ => by rw [multiplicationBy_def, Finset.smul_sum]

/-! ## Multiplicative matrices -/

/-- A matrix **preserves the multiplication** when it is multiplicative for it,
`g (m (u, v)) = m (g u, g v)`, written as one matrix identity for each basis vector of the first
argument. -/
def PreservesMultiplication (g : Matrix (Fin 26) (Fin 26) R) : Prop :=
  ∀ k, g * (multiplicationOperator k).map (Int.cast : ℤ → R) =
    multiplicationBy (fun a => g a k) * g

/-- The defining equations of multiplicativity. -/
theorem preservesMultiplication_def (g : Matrix (Fin 26) (Fin 26) R) :
    PreservesMultiplication g ↔ ∀ k, g * (multiplicationOperator k).map (Int.cast : ℤ → R) =
      multiplicationBy (fun a => g a k) * g := Iff.rfl

/-- **Multiplicativity against an arbitrary vector.** -/
theorem PreservesMultiplication.mulVec {g : Matrix (Fin 26) (Fin 26) R}
    (hg : PreservesMultiplication g) (v : Fin 26 → R) :
    g * multiplicationBy v = multiplicationBy (g *ᵥ v) * g := by
  rw [multiplicationBy_def, Matrix.mul_sum, multiplicationBy_mulVec, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_smul, hg a, Matrix.smul_mul]

/-- The identity matrix preserves the multiplication. -/
theorem preservesMultiplication_one :
    PreservesMultiplication (1 : Matrix (Fin 26) (Fin 26) R) := fun k => by
  rw [one_mul, mul_one, one_col, multiplicationBy_single]

/-- **Matrices preserving the multiplication are closed under multiplication.** -/
theorem PreservesMultiplication.mul {g h : Matrix (Fin 26) (Fin 26) R}
    (hg : PreservesMultiplication g) (hh : PreservesMultiplication h) :
    PreservesMultiplication (g * h) := fun k => by
  rw [Matrix.mul_assoc, hh k, ← Matrix.mul_assoc, hg.mulVec (fun a => h a k), mulVec_col,
    Matrix.mul_assoc]

/-- **A matrix inverse to a multiplicative matrix is multiplicative.** -/
theorem PreservesMultiplication.of_mul_eq_one {g h : Matrix (Fin 26) (Fin 26) R}
    (hg : PreservesMultiplication g) (hgh : g * h = 1) (hhg : h * g = 1) :
    PreservesMultiplication h := by
  intro k
  have key : h * multiplicationBy (g *ᵥ fun a => h a k) =
      multiplicationBy (fun a => h a k) * h := by
    calc h * multiplicationBy (g *ᵥ fun a => h a k)
        = h * (multiplicationBy (g *ᵥ fun a => h a k) * g) * h := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hgh, mul_one]
      _ = h * g * multiplicationBy (fun a => h a k) * h := by
          rw [← hg.mulVec (fun a => h a k)]
          noncomm_ring
      _ = multiplicationBy (fun a => h a k) * h := by rw [hhg, one_mul]
  rwa [mulVec_col, hgh, one_col, multiplicationBy_single] at key

/-- **A multiplicative invertible matrix carries the span of the multiplication operators to
itself**, permuting the operators through the tautological action on their index. -/
theorem PreservesMultiplication.mul_multiplicationOperator_mul
    {g h : Matrix (Fin 26) (Fin 26) R} (hg : PreservesMultiplication g) (hgh : g * h = 1)
    (k : Fin 26) :
    g * (multiplicationOperator k).map (Int.cast : ℤ → R) * h =
      multiplicationBy fun a => g a k := by
  rw [hg k, Matrix.mul_assoc, hgh, mul_one]

/-! ## Derivations -/

/-- A matrix **differentiates the multiplication** when `X (m (u, v)) = m (X u, v) + m (u, X v)`,
written as one matrix identity for each basis vector of the first argument. -/
def IsDerivation (X : Matrix (Fin 26) (Fin 26) R) : Prop :=
  ∀ k, X * (multiplicationOperator k).map (Int.cast : ℤ → R) -
    (multiplicationOperator k).map (Int.cast : ℤ → R) * X = multiplicationBy fun a => X a k

/-- The defining equations of a derivation. -/
theorem isDerivation_def (X : Matrix (Fin 26) (Fin 26) R) :
    IsDerivation X ↔ ∀ k, X * (multiplicationOperator k).map (Int.cast : ℤ → R) -
      (multiplicationOperator k).map (Int.cast : ℤ → R) * X =
        multiplicationBy fun a => X a k := Iff.rfl

/-- **The derivation equation against an arbitrary vector.** -/
theorem IsDerivation.mulVec {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (v : Fin 26 → R) :
    X * multiplicationBy v - multiplicationBy v * X = multiplicationBy (X *ᵥ v) := by
  rw [multiplicationBy_def, Matrix.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    multiplicationBy_mulVec]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hX a]

/-- A scalar multiple of a derivation is a derivation. -/
theorem IsDerivation.smul {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X) (c : R) :
    IsDerivation (c • X) := fun k => by
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, hX k,
    show (fun a => (c • X) a k) = c • fun a => X a k from rfl, multiplicationBy_smul]

/-- The zero matrix is a derivation. -/
theorem isDerivation_zero : IsDerivation (0 : Matrix (Fin 26) (Fin 26) R) := fun k => by
  rw [Matrix.zero_mul, Matrix.mul_zero, sub_zero,
    show (fun a => (0 : Matrix (Fin 26) (Fin 26) R) a k) = (0 : Fin 26 → R) from rfl,
    multiplicationBy_zero]

/-- A sum of derivations is a derivation. -/
theorem IsDerivation.add {X Y : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hY : IsDerivation Y) : IsDerivation (X + Y) := fun k => by
  rw [Matrix.add_mul, Matrix.mul_add,
    show (fun a => (X + Y) a k) = (fun a => X a k) + (fun a => Y a k) from rfl,
    multiplicationBy_add, ← hX k, ← hY k]
  abel

/-- A finite sum of derivations is a derivation. -/
theorem IsDerivation.sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 26) (Fin 26) R)
    (h : ∀ i ∈ s, IsDerivation (f i)) : IsDerivation (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    exact isDerivation_zero
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self a s)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

/-- A difference of derivations is a derivation. -/
theorem IsDerivation.sub {X Y : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hY : IsDerivation Y) : IsDerivation (X - Y) := fun k => by
  have hfun : (fun a => (X - Y) a k) = (fun a => X a k) + (-1 : R) • fun a => Y a k := by
    funext a
    rw [Matrix.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg]
  rw [Matrix.sub_mul, Matrix.mul_sub, hfun, multiplicationBy_add, multiplicationBy_smul,
    ← hX k, ← hY k]
  module

/-- **The derivations are closed under the commutator.** -/
theorem IsDerivation.bracket {X Y : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hY : IsDerivation Y) : IsDerivation (X * Y - Y * X) := by
  intro k
  have hcomp : ∀ Z W : Matrix (Fin 26) (Fin 26) R, IsDerivation Z →
      Z * multiplicationBy (fun a => W a k) - multiplicationBy (fun a => W a k) * Z =
        multiplicationBy fun a => (Z * W) a k := fun Z W hZ => by
    rw [hZ.mulVec (fun a => W a k), mulVec_col]
  have hstep : (X * Y - Y * X) * (multiplicationOperator k).map (Int.cast : ℤ → R) -
      (multiplicationOperator k).map (Int.cast : ℤ → R) * (X * Y - Y * X) =
        (X * (Y * (multiplicationOperator k).map (Int.cast : ℤ → R) -
            (multiplicationOperator k).map (Int.cast : ℤ → R) * Y) -
          (Y * (multiplicationOperator k).map (Int.cast : ℤ → R) -
            (multiplicationOperator k).map (Int.cast : ℤ → R) * Y) * X) -
        (Y * (X * (multiplicationOperator k).map (Int.cast : ℤ → R) -
            (multiplicationOperator k).map (Int.cast : ℤ → R) * X) -
          (X * (multiplicationOperator k).map (Int.cast : ℤ → R) -
            (multiplicationOperator k).map (Int.cast : ℤ → R) * X) * Y) := by
    noncomm_ring
  have hfun : (fun a => (X * Y - Y * X) a k) =
      (fun a => (X * Y) a k) + (-1 : R) • fun a => (Y * X) a k := by
    funext a
    rw [Matrix.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg]
  rw [hstep, hX k, hY k, hcomp X Y hX, hcomp Y X hY, hfun, multiplicationBy_add,
    multiplicationBy_smul]
  module

/-- **Conjugating a derivation by a multiplicative invertible matrix gives a derivation.** -/
theorem IsDerivation.conj {X g h : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hg : PreservesMultiplication g) (hgh : g * h = 1) (hhg : h * g = 1) :
    IsDerivation (g * X * h) := by
  have hh : PreservesMultiplication h := hg.of_mul_eq_one hgh hhg
  intro k
  set v : Fin 26 → R := fun a => if a = k then (1 : R) else 0 with hv
  set A : Matrix (Fin 26) (Fin 26) R := multiplicationBy (fun a => h a k) with hA
  set B : Matrix (Fin 26) (Fin 26) R := multiplicationBy (fun a => (X * h) a k) with hB
  set C : Matrix (Fin 26) (Fin 26) R := multiplicationBy (fun a => (g * X * h) a k) with hC
  have hLv : multiplicationBy v = (multiplicationOperator k).map (Int.cast : ℤ → R) :=
    multiplicationBy_single k
  have hhv : h *ᵥ v = fun a => h a k := by
    rw [hv, ← one_col, mulVec_col, mul_one]
  have hhL : h * multiplicationBy v = A * h := by rw [hh.mulVec v, hhv, hA]
  have hXA : X * A = A * X + B := by
    have hd := hX.mulVec (fun a => h a k)
    rw [mulVec_col] at hd
    rw [hA, hB, ← hd]
    abel
  have hgA : g * A = multiplicationBy v * g := by
    rw [hA, hg.mulVec (fun a => h a k), mulVec_col, hgh, one_col, hv]
  have hgB : g * B = C * g := by
    rw [hB, hg.mulVec (fun a => (X * h) a k), mulVec_col, hC, Matrix.mul_assoc]
  rw [← hLv]
  have key : g * X * h * multiplicationBy v = multiplicationBy v * (g * X * h) + C := by
    calc g * X * h * multiplicationBy v = g * (X * (h * multiplicationBy v)) := by noncomm_ring
      _ = g * (X * (A * h)) := by rw [hhL]
      _ = g * ((A * X + B) * h) := by rw [← hXA]; noncomm_ring
      _ = g * A * (X * h) + g * B * h := by noncomm_ring
      _ = multiplicationBy v * g * (X * h) + C * g * h := by rw [hgA, hgB]
      _ = multiplicationBy v * (g * X * h) + C * (g * h) := by noncomm_ring
      _ = multiplicationBy v * (g * X * h) + C := by rw [hgh, mul_one]
  rw [key, hC]
  abel

/-! ## Integral derivations -/

/-- Over the integers, multiplication by a vector is the plain linear combination of the
multiplication operators. -/
theorem multiplicationBy_int (v : Fin 26 → ℤ) :
    multiplicationBy v = ∑ a, v a • multiplicationOperator a := by
  rw [multiplicationBy_def]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ?_
  ext c b
  rw [Matrix.map_apply, Int.cast_id]

/-- Over the integers, multiplication by a basis vector is the corresponding multiplication
operator. -/
theorem multiplicationBy_single_int (k : Fin 26) :
    multiplicationBy (fun a => if a = k then (1 : ℤ) else 0) = multiplicationOperator k := by
  rw [multiplicationBy_single]
  ext c b
  rw [Matrix.map_apply, Int.cast_id]

/-- Multiplication by an integral vector commutes with entrywise integer casts. -/
theorem map_multiplicationBy (v : Fin 26 → ℤ) :
    (multiplicationBy v).map (Int.cast : ℤ → R) = multiplicationBy fun a => ((v a : ℤ) : R) := by
  ext c b
  rw [Matrix.map_apply, multiplicationBy_int, multiplicationBy_def]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Int.cast_sum,
    Int.cast_mul]

/-- The derivation equations of an integer matrix, without casts. -/
theorem isDerivation_int_iff (N : Matrix (Fin 26) (Fin 26) ℤ) :
    IsDerivation N ↔ ∀ k, N * multiplicationOperator k - multiplicationOperator k * N =
      ∑ a, N a k • multiplicationOperator a := by
  have hmap : ∀ k, (multiplicationOperator k).map (Int.cast : ℤ → ℤ) = multiplicationOperator k :=
    fun k => by
      ext c b
      rw [Matrix.map_apply, Int.cast_id]
  constructor
  · intro h k
    have := h k
    rwa [hmap, multiplicationBy_int] at this
  · intro h k
    rw [hmap, multiplicationBy_int]
    exact h k

/-- **An integral derivation differentiates the multiplication over every commutative ring.** -/
theorem IsDerivation.map {N : Matrix (Fin 26) (Fin 26) ℤ} (hN : IsDerivation N) :
    IsDerivation (N.map (Int.cast : ℤ → R)) := by
  intro k
  have h := (isDerivation_int_iff N).mp hN k
  have key : (N * multiplicationOperator k - multiplicationOperator k * N).map
      (Int.cast : ℤ → R) = (∑ a, N a k • multiplicationOperator a).map (Int.cast : ℤ → R) := by
    rw [h]
  have hsub : (N * multiplicationOperator k - multiplicationOperator k * N).map
      (Int.cast : ℤ → R) =
        N.map (Int.cast : ℤ → R) * (multiplicationOperator k).map (Int.cast : ℤ → R) -
          (multiplicationOperator k).map (Int.cast : ℤ → R) * N.map (Int.cast : ℤ → R) := by
    ext a b
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Int.cast_sub, ← Matrix.map_apply
      (f := (Int.cast : ℤ → R)), ← Matrix.map_apply (f := (Int.cast : ℤ → R)),
      Matrix.map_intCast_mul, Matrix.map_intCast_mul]
  rw [hsub, ← multiplicationBy_int, map_multiplicationBy] at key
  rw [key]
  exact congrArg multiplicationBy (funext fun a => (Matrix.map_apply ..).symm)

end TauCeti.F4ShortRoot
