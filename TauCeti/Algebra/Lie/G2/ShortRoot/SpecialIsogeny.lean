/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.Matrix.Minor

/-!
# The special isogeny of type G2 as a matrix of minors

Over a field of characteristic three the group of type `G₂` admits an endomorphism `τ` exchanging
the two root lengths: it raises the parameter of a short simple root element to the third power
and leaves that of a long one alone. It is the *special isogeny*, and the Ree groups `²G₂(3^(2m+1))`
are cut out by the fixed points of its odd powers. This file writes `τ` as the explicit polynomial
map `Matrix.g2SpecialIsogeny` of signed `2 × 2` minors of a `7 × 7` matrix, read in the weight
basis of the seven-dimensional module of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`, and computes it
on the simple root elements and on the diagonal torus of that module.

## Where the formula comes from

The type-`G₂` Lie algebra acts on the seven-dimensional module `V`, and in characteristic three
the span `I` of the short root vectors and the short coroots is an ideal of it. The quotient by
`I` is again seven-dimensional, with the six long roots and zero as its weights, and the adjoint
action of a group element on that quotient, read in a basis matched to the weight basis of `V`
through the length-exchanging map on weights, is the special isogeny. The Lie algebra lies in the
skew endomorphisms of `V` for its invariant symmetric form, so every entry of that adjoint action
is a signed sum of `2 × 2` minors of the group element; the seven index pairs and the two
corrections at the middle index are the resulting bookkeeping. That the formula is multiplicative
in characteristic three, on the matrices preserving the invariant cross product, is proved in
`TauCeti.Algebra.Lie.G2.ShortRoot.IsogenyMultiplicative`.

## What is proved here

The pinning equations and the torus equation are polynomial identities valid over every
commutative ring, and none of them assumes a characteristic. The simple root elements are written
as explicit matrices, `1 + t E + t² E⁽²⁾` for the raising generator `E` of
`TauCeti.G2ShortRoot.raisingMatrix` and its divided square, and likewise for the lowering
generators; this file does not construct a group containing them.

## Main definitions

* `TauCeti.g2SpecialIsogenyPair`: the seven index pairs carrying the minors.
* `Matrix.g2SpecialIsogenyColumn`: the column combinations of minors on a fixed row pair.
* `Matrix.g2SpecialIsogeny`: the matrix of signed `2 × 2` minors carrying the isogeny.

## Main results

* `Matrix.g2SpecialIsogeny_one`, `Matrix.g2SpecialIsogeny_map` and
  `Matrix.g2SpecialIsogeny_diagonal`: the formula fixes the identity, commutes with entrywise ring
  morphisms, and sends diagonal matrices to diagonal matrices.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_one_add_smul_raisingMatrix_zero` and its three siblings:
  the pinning equations `τ (x_{α₁}(t)) = x_{α₂}(t³)` and `τ (x_{α₂}(t)) = x_{α₁}(t)`, together
  with their negative-root counterparts, so `τ` exchanges the two root lengths with exponent three
  at the short simple root and one at the long one.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_diagonal_torusCharacter`: on the diagonal torus of the
  weight basis the formula acts through `(s₀, s₁) ↦ (s₁, s₀³)`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the quotient by the short-root ideal in characteristic three.

The shape of the definitions follows the special isogeny of `Sp₄` in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SpecialIsogeny`.
-/

public section

open Matrix

universe u

namespace TauCeti

/-- The seven index pairs whose `2 × 2` minors carry the type-`G₂` special isogeny. -/
def g2SpecialIsogenyPair : Fin 7 → Fin 7 × Fin 7 :=
  ![(0, 1), (0, 2), (1, 4), (1, 5), (2, 5), (4, 6), (5, 6)]

@[simp] theorem g2SpecialIsogenyPair_zero : g2SpecialIsogenyPair 0 = (0, 1) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_one : g2SpecialIsogenyPair 1 = (0, 2) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_two : g2SpecialIsogenyPair 2 = (1, 4) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_three : g2SpecialIsogenyPair 3 = (1, 5) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_four : g2SpecialIsogenyPair 4 = (2, 5) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_five : g2SpecialIsogenyPair 5 = (4, 6) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_six : g2SpecialIsogenyPair 6 = (5, 6) := (rfl)

end TauCeti

namespace Matrix

open TauCeti

variable {R : Type u} [CommRing R]

/-- The minors of `g` on a fixed row pair `p` against the `j`-th column combination: the pair
`TauCeti.g2SpecialIsogenyPair j`, joined by the pair `(2, 4)` at the middle index `3`. -/
def g2SpecialIsogenyColumn (g : Matrix (Fin 7) (Fin 7) R) (p : Fin 7 × Fin 7) (j : Fin 7) : R :=
  pairMinor g p (g2SpecialIsogenyPair j) + if j = 3 then pairMinor g p (2, 4) else 0

/-- The defining equation of the column combination of minors. -/
@[simp]
theorem g2SpecialIsogenyColumn_def (g : Matrix (Fin 7) (Fin 7) R) (p : Fin 7 × Fin 7)
    (j : Fin 7) :
    g2SpecialIsogenyColumn g p j =
      pairMinor g p (g2SpecialIsogenyPair j) + if j = 3 then pairMinor g p (2, 4) else 0 := (rfl)

/-- **The type-`G₂` matrix of signed `2 × 2` minors.** Its `(i, j)` entry reads the `j`-th column
combination of minors on the row pair `TauCeti.g2SpecialIsogenyPair i`, diminished at the middle
index `3` by the same combination taken on the row pair `(0, 6)`. -/
def g2SpecialIsogeny (g : Matrix (Fin 7) (Fin 7) R) : Matrix (Fin 7) (Fin 7) R :=
  Matrix.of fun i j =>
    g2SpecialIsogenyColumn g (g2SpecialIsogenyPair i) j -
      if i = 3 then g2SpecialIsogenyColumn g (0, 6) j else 0

/-- The entrywise formula for the type-`G₂` matrix of signed minors. -/
@[simp]
theorem g2SpecialIsogeny_apply (g : Matrix (Fin 7) (Fin 7) R) (i j : Fin 7) :
    g2SpecialIsogeny g i j =
      g2SpecialIsogenyColumn g (g2SpecialIsogenyPair i) j -
        if i = 3 then g2SpecialIsogenyColumn g (0, 6) j else 0 := (rfl)

/-- The formula commutes with entrywise application of any morphism of rings. -/
@[simp]
theorem g2SpecialIsogeny_map {S F : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (g : Matrix (Fin 7) (Fin 7) R) :
    g2SpecialIsogeny (g.map f) = (g2SpecialIsogeny g).map f := by
  ext i j
  simp only [Matrix.map_apply, g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq,
    apply_ite f, map_zero, map_add, map_sub, map_mul]

/-- **The formula sends diagonal matrices to diagonal matrices**, pairing up the entries along
the seven distinguished index pairs. The two corrections at the middle index contribute nothing,
because the pairs they add are distinct from all seven. -/
theorem g2SpecialIsogeny_diagonal (d : Fin 7 → R) :
    g2SpecialIsogeny (Matrix.diagonal d) =
      Matrix.diagonal
        ![d 0 * d 1, d 0 * d 2, d 1 * d 4, d 1 * d 5, d 2 * d 5, d 4 * d 6, d 5 * d 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq]

/-- The formula fixes the identity matrix. -/
@[simp]
theorem g2SpecialIsogeny_one : g2SpecialIsogeny (1 : Matrix (Fin 7) (Fin 7) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq]

end Matrix

namespace TauCeti.G2ShortRoot

variable {R : Type u} [CommRing R]

/-! ### The action on the simple root elements -/

/-- The root element `1 + t E + t² E⁽²⁾` of the short positive simple root `α₁`, where the
divided square `E⁽²⁾` of the raising generator is the single unit matrix at `(2, 4)`, by
`TauCeti.G2ShortRoot.raisingMatrix_zero_mul_self`. -/
private theorem one_add_smul_raisingMatrix_zero (t : R) :
    1 + t • (raisingMatrix 0).map (Int.cast : ℤ → R) + t ^ 2 • Matrix.single 2 4 1 =
      !![1, t, 0, 0, 0, 0, 0;
         0, 1, 0, 0, 0, 0, 0;
         0, 0, 1, 2 * t, t ^ 2, 0, 0;
         0, 0, 0, 1, t, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 1, t;
         0, 0, 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

/-- **The special isogeny on the short positive simple root element**:
`τ (x_{α₁}(t)) = x_{α₂}(t³)`, the parameter cubed and the root exchanged for the long one. -/
theorem g2SpecialIsogeny_one_add_smul_raisingMatrix_zero (t : R) :
    g2SpecialIsogeny
        (1 + t • (raisingMatrix 0).map (Int.cast : ℤ → R) + t ^ 2 • Matrix.single 2 4 1) =
      1 + t ^ 3 • (raisingMatrix 1).map (Int.cast : ℤ → R) := by
  rw [one_add_smul_raisingMatrix_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;>
    ring

/-- **The special isogeny on the long positive simple root element**:
`τ (x_{α₂}(t)) = x_{α₁}(t)`, the parameter kept and the root exchanged for the short one. -/
theorem g2SpecialIsogeny_one_add_smul_raisingMatrix_one (t : R) :
    g2SpecialIsogeny (1 + t • (raisingMatrix 1).map (Int.cast : ℤ → R)) =
      1 + t • (raisingMatrix 0).map (Int.cast : ℤ → R) + t ^ 2 • Matrix.single 2 4 1 := by
  rw [one_add_smul_raisingMatrix_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;>
    ring

/-- The root element `1 + t F + t² F⁽²⁾` of the short negative simple root `-α₁`, where the
divided square `F⁽²⁾` of the lowering generator is the single unit matrix at `(4, 2)`, by
`TauCeti.G2ShortRoot.loweringMatrix_zero_mul_self`. -/
private theorem one_add_smul_loweringMatrix_zero (t : R) :
    1 + t • (loweringMatrix 0).map (Int.cast : ℤ → R) + t ^ 2 • Matrix.single 4 2 1 =
      !![1, 0, 0, 0, 0, 0, 0;
         t, 1, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, t, 1, 0, 0, 0;
         0, 0, t ^ 2, 2 * t, 1, 0, 0;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

/-- **The special isogeny on the short negative simple root element**:
`τ (x_{-α₁}(t)) = x_{-α₂}(t³)`. -/
theorem g2SpecialIsogeny_one_add_smul_loweringMatrix_zero (t : R) :
    g2SpecialIsogeny
        (1 + t • (loweringMatrix 0).map (Int.cast : ℤ → R) + t ^ 2 • Matrix.single 4 2 1) =
      1 + t ^ 3 • (loweringMatrix 1).map (Int.cast : ℤ → R) := by
  rw [one_add_smul_loweringMatrix_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;>
    ring

/-- **The special isogeny on the long negative simple root element**:
`τ (x_{-α₂}(t)) = x_{-α₁}(t)`. -/
theorem g2SpecialIsogeny_one_add_smul_loweringMatrix_one (t : R) :
    g2SpecialIsogeny (1 + t • (loweringMatrix 1).map (Int.cast : ℤ → R)) =
      1 + t • (loweringMatrix 0).map (Int.cast : ℤ → R) + t ^ 2 • Matrix.single 4 2 1 := by
  rw [one_add_smul_loweringMatrix_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;>
    ring

/-! ### The action on the diagonal torus -/

/-- **The special isogeny on the diagonal torus.** On the diagonal matrix of the weight characters
of a torus point `s`, the formula returns the diagonal matrix of the weight characters of the
length-exchanged point `(s₁, s₀³)`. On characters this is the map `μ ↦ (3 μ₁, μ₀)` that the special
isogeny induces on the character lattice. -/
theorem g2SpecialIsogeny_diagonal_torusCharacter (s : Fin 2 → Rˣ) :
    g2SpecialIsogeny (Matrix.diagonal fun a => (torusCharacter s (weight a) : R)) =
      Matrix.diagonal fun a => (torusCharacter ![s 1, s 0 ^ 3] (weight a) : R) := by
  have hswap : ∀ μ : Fin 2 → ℤ,
      torusCharacter ![s 1, s 0 ^ 3] μ = torusCharacter s ![3 * μ 1, μ 0] := fun μ => by
    rw [torusCharacter_def, torusCharacter_def, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← zpow_natCast (s 0) 3, ← _root_.zpow_mul, mul_comm]
    norm_num
  rw [g2SpecialIsogeny_diagonal]
  refine congrArg Matrix.diagonal (funext fun a => ?_)
  rw [hswap]
  fin_cases a <;>
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ← Units.val_mul, ← torusCharacter_add] <;>
    exact congrArg (fun μ : Fin 2 → ℤ => ((torusCharacter s μ : Rˣ) : R))
      (by ext b; fin_cases b <;> simp [weight_apply])

end TauCeti.G2ShortRoot
