/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Carrier
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special
public import TauCeti.LinearAlgebra.Matrix.Minor

/-!
# The special isogeny of type G2 on the seven-dimensional weight basis

Over a field of characteristic three the pinned group of type `G₂` admits an endomorphism `τ`
exchanging the two root lengths: it raises the parameter of a short simple root subgroup to the
third power and leaves that of a long one alone. It is the *special isogeny*. This file writes
`τ` as the explicit polynomial map `Matrix.g2SpecialIsogeny` of signed `2 × 2` minors, read in the
weight basis of the seven-dimensional module of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`, and
computes it on the four numbered simple-root points of the short-root carrier and on its weight
torus.

## Where the formula comes from

The type-`G₂` Lie algebra acts on the seven-dimensional module `V`, and in characteristic three
the span `I` of the short root vectors and the short coroots is an ideal of it. The quotient by
`I` is again seven-dimensional, with the six long roots and zero as its weights, and the adjoint
action of a group element on that quotient, read in a basis matched to the weight basis of `V`
through the length-exchanging map on weights, is the special isogeny. The Lie algebra lies in the
skew endomorphisms of `V` for its invariant symmetric form, so every entry of that adjoint action
is a signed sum of `2 × 2` minors of the group element; the seven index pairs and the two
corrections at the middle index are the resulting bookkeeping, recorded in
`Matrix.g2SpecialIsogeny`.

## What is proved here

The four pinning equations, the torus equation and the square relation on the numbered simple-root
points are polynomial identities valid over every commutative ring, and none of them assumes a
characteristic. What needs characteristic three is that the formula preserves products, and that
is not proved here: nothing below shows that the formula is multiplicative, that it carries points
of the carrier to points of the carrier, or that its square is the cubing map on anything other
than the numbered simple-root points.

The carrier built from this representation is not identified with the pinned simply connected
group scheme of type `G₂`, and constructions on it transfer to that scheme only along such an
identification.

## Main definitions

* `Matrix.g2SpecialIsogeny`: the matrix of signed `2 × 2` minors carrying the isogeny, on the seven
  index pairs `TauCeti.g2SpecialIsogenyPair` and through the column combinations
  `Matrix.g2SpecialIsogenyColumn`.
* `TauCeti.G2ShortRoot.specialIsogenyRootIndex` and `TauCeti.G2ShortRoot.specialIsogenyExponent`:
  the length-exchanging permutation of the numbered simple root indices, the diagram permutation
  `TauCeti.lengthPermRankTwo` on each summand, and the exponent it carries, the squared length of
  the root at the exchanged node.
* `TauCeti.G2ShortRoot.specialIsogenyTorusMap`: the induced map `(s₀, s₁) ↦ (s₁, s₀³)` on torus
  points, with `TauCeti.G2ShortRoot.specialIsogenyExponent_inl` reading the exponent off the
  squared length of the exchanged simple root and
  `TauCeti.G2ShortRoot.specialIsogenyExponent_inl_eq_ite` giving its two values.

## Main results

* `Matrix.g2SpecialIsogeny_one`, `Matrix.g2SpecialIsogeny_map` and
  `Matrix.g2SpecialIsogeny_diagonal`: the formula fixes the identity, commutes with entrywise ring
  morphisms, and sends diagonal matrices to diagonal matrices.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_coe_rootSubgroupPoints_inl_zero` and its three siblings:
  the pinning equations `τ (x_{α₁}(t)) = x_{α₂}(t³)` and `τ (x_{α₂}(t)) = x_{α₁}(t)` together with
  their negative-root counterparts, gathered uniformly in
  `TauCeti.G2ShortRoot.g2SpecialIsogeny_coe_rootSubgroupPoints`.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_diagonal_torusCharacter` and
  `TauCeti.G2ShortRoot.g2SpecialIsogeny_coe_weightTorusPoints`: on the weight torus the formula
  acts through the length-exchanging map on characters, which
  `TauCeti.G2ShortRoot.torusCharacter_specialIsogenyTorusMap` reads on the character lattice; the
  second states this on the carrier's own weight-torus points.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints`: the square
  relation `τ ∘ τ = Frob₃` on every numbered simple-root point of the carrier.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the quotient by the short-root ideal in characteristic three.
-/

-- Adapted from `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SpecialIsogeny`, the
-- special isogeny of Sp₄, with the same shape of definitions and equations.

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

/-- The formula commutes with entrywise application of any morphism of rings, an algebra
morphism as much as a ring morphism. -/
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

/-! ### The action on the numbered simple-root points -/

/-- **The four pinning equations.** The minor formula carries each numbered simple-root point to
the point at the length-exchanged index, with the parameter raised to the squared length of the
root it lands on: the cube at the two short roots and the first power at the two long ones. -/
-- The four are stated together because one entrywise expansion of the minors proves them all.
private theorem g2SpecialIsogeny_coe_rootSubgroupPoints_aux (t : R) :
    g2SpecialIsogeny
          ((rootSubgroupPoints (.inl 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
        ((rootSubgroupPoints (.inl 1) R (Multiplicative.ofAdd (t ^ 3)) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) ∧
      g2SpecialIsogeny
            ((rootSubgroupPoints (.inl 1) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
          ((rootSubgroupPoints (.inl 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) ∧
      g2SpecialIsogeny
            ((rootSubgroupPoints (.inr 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
          ((rootSubgroupPoints (.inr 1) R (Multiplicative.ofAdd (t ^ 3)) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) ∧
      g2SpecialIsogeny
            ((rootSubgroupPoints (.inr 1) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
          ((rootSubgroupPoints (.inr 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [coe_rootSubgroupPoints_inl_zero, coe_rootSubgroupPoints_inl_one,
      coe_rootSubgroupPoints_inr_zero, coe_rootSubgroupPoints_inr_one] <;>
    (ext i j
     fin_cases i <;> fin_cases j <;>
       simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;> ring)

/-- The special isogeny carries the short positive simple root subgroup to the long one and
cubes the parameter: `τ (x_{α₁}(t)) = x_{α₂}(t³)`. -/
theorem g2SpecialIsogeny_coe_rootSubgroupPoints_inl_zero (t : R) :
    g2SpecialIsogeny
        ((rootSubgroupPoints (.inl 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
      ((rootSubgroupPoints (.inl 1) R (Multiplicative.ofAdd (t ^ 3)) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) :=
  (g2SpecialIsogeny_coe_rootSubgroupPoints_aux t).1

/-- The special isogeny carries the long positive simple root subgroup to the short one and
keeps the parameter: `τ (x_{α₂}(t)) = x_{α₁}(t)`. -/
theorem g2SpecialIsogeny_coe_rootSubgroupPoints_inl_one (t : R) :
    g2SpecialIsogeny
        ((rootSubgroupPoints (.inl 1) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
      ((rootSubgroupPoints (.inl 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) :=
  (g2SpecialIsogeny_coe_rootSubgroupPoints_aux t).2.1

/-- The special isogeny on the short negative simple root subgroup:
`τ (x_{-α₁}(t)) = x_{-α₂}(t³)`. -/
theorem g2SpecialIsogeny_coe_rootSubgroupPoints_inr_zero (t : R) :
    g2SpecialIsogeny
        ((rootSubgroupPoints (.inr 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
      ((rootSubgroupPoints (.inr 1) R (Multiplicative.ofAdd (t ^ 3)) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) :=
  (g2SpecialIsogeny_coe_rootSubgroupPoints_aux t).2.2.1

/-- The special isogeny on the long negative simple root subgroup:
`τ (x_{-α₂}(t)) = x_{-α₁}(t)`. -/
theorem g2SpecialIsogeny_coe_rootSubgroupPoints_inr_one (t : R) :
    g2SpecialIsogeny
        ((rootSubgroupPoints (.inr 1) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
      ((rootSubgroupPoints (.inr 0) R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) :=
  (g2SpecialIsogeny_coe_rootSubgroupPoints_aux t).2.2.2

/-- The length-exchanging permutation of the numbered simple root indices: the length-exchanging
diagram permutation `TauCeti.lengthPermRankTwo` on each of the two summands. -/
def specialIsogenyRootIndex : Equiv.Perm (Fin 2 ⊕ Fin 2) :=
  Equiv.Perm.sumCongr lengthPermRankTwo lengthPermRankTwo

/-- The defining equation of the length-exchanging permutation on positive indices. -/
@[simp]
theorem specialIsogenyRootIndex_inl (i : Fin 2) :
    specialIsogenyRootIndex (.inl i) = .inl (lengthPermRankTwo i) := by
  rw [specialIsogenyRootIndex, Equiv.Perm.sumCongr_apply, Sum.map_inl]

/-- The defining equation of the length-exchanging permutation on negative indices. -/
@[simp]
theorem specialIsogenyRootIndex_inr (i : Fin 2) :
    specialIsogenyRootIndex (.inr i) = .inr (lengthPermRankTwo i) := by
  rw [specialIsogenyRootIndex, Equiv.Perm.sumCongr_apply, Sum.map_inr]

/-- The length-exchanging permutation of the numbered simple root indices is an involution. -/
@[simp]
theorem specialIsogenyRootIndex_specialIsogenyRootIndex (k : Fin 2 ⊕ Fin 2) :
    specialIsogenyRootIndex (specialIsogenyRootIndex k) = k := by
  rcases k with i | i <;>
    simp [lengthPermRankTwo_lengthPermRankTwo]

/-- The exponent of the special isogeny at a numbered simple root index: the exponent that the
special isogeny `TauCeti.DynkinType.g2SpecialIsogeny` of the pinned `G₂` root datum carries at the
root the length permutation exchanges it with, read through the embedding of the two simple roots
into the twelve roots. -/
def specialIsogenyExponent : Fin 2 ⊕ Fin 2 → ℕ
  | .inl i => (DynkinType.g2SpecialIsogeny.exponent
      (Fin.castLE (by omega) (lengthPermRankTwo i))).toNat
  | .inr i => (DynkinType.g2SpecialIsogeny.exponent
      (Fin.castLE (by omega) (lengthPermRankTwo i))).toNat

/-- **The exponent on positive indices is the squared length of the exchanged simple root**, three
at the short node and one at the long one. -/
@[simp]
theorem specialIsogenyExponent_inl (i : Fin 2) :
    specialIsogenyExponent (.inl i) =
      (DynkinType.G2.rootLength (lengthPermRankTwo i)).toNat := by
  rw [specialIsogenyExponent, DynkinType.g2SpecialIsogeny_exponent, DynkinType.g2Length_castLE]

/-- **The exponent on negative indices is the squared length of the exchanged simple root.** -/
@[simp]
theorem specialIsogenyExponent_inr (i : Fin 2) :
    specialIsogenyExponent (.inr i) =
      (DynkinType.G2.rootLength (lengthPermRankTwo i)).toNat := by
  rw [specialIsogenyExponent, DynkinType.g2SpecialIsogeny_exponent, DynkinType.g2Length_castLE]

/-- **The two values of the exponent.** It is one at the long simple root, Bourbaki node one of
the `G₂` diagram, and the defining characteristic three at the short one. -/
theorem specialIsogenyExponent_inl_eq_ite (i : Fin 2) :
    specialIsogenyExponent (.inl i) = if i = 1 then 1 else 3 := by
  fin_cases i <;> simp [specialIsogenyExponent_inl, DynkinType.rootLength_G2]

/-- **The pinning equations, uniformly.** The special isogeny sends the numbered simple-root point
at `k` to the one at the length-exchanged index, with the parameter raised to the exponent of
`k`. -/
theorem g2SpecialIsogeny_coe_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (t : R) :
    g2SpecialIsogeny ((rootSubgroupPoints k R (Multiplicative.ofAdd t) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) =
      ((rootSubgroupPoints (specialIsogenyRootIndex k) R
          (Multiplicative.ofAdd (t ^ specialIsogenyExponent k)) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) := by
  rcases k with i | i <;> fin_cases i <;>
    simp [specialIsogenyExponent_inl, specialIsogenyExponent_inr, DynkinType.rootLength_G2,
      g2SpecialIsogeny_coe_rootSubgroupPoints_inl_zero,
      g2SpecialIsogeny_coe_rootSubgroupPoints_inl_one,
      g2SpecialIsogeny_coe_rootSubgroupPoints_inr_zero,
      g2SpecialIsogeny_coe_rootSubgroupPoints_inr_one,
      -coe_rootSubgroupPoints]

/-- **The square of the special isogeny cubes the parameter of every numbered simple-root
point**: `τ (τ (x_k(t))) = x_k(t³)`. -/
theorem g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (t : R) :
    g2SpecialIsogeny (g2SpecialIsogeny
        ((rootSubgroupPoints k R (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R)) =
      ((rootSubgroupPoints k R (Multiplicative.ofAdd (t ^ 3)) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) := by
  rcases k with i | i <;> fin_cases i <;>
    simp [
      g2SpecialIsogeny_coe_rootSubgroupPoints_inl_zero,
      g2SpecialIsogeny_coe_rootSubgroupPoints_inl_one,
      g2SpecialIsogeny_coe_rootSubgroupPoints_inr_zero,
      g2SpecialIsogeny_coe_rootSubgroupPoints_inr_one,
      -coe_rootSubgroupPoints]

/-! ### The action on the weight torus -/

/-- The map induced by the special isogeny on torus points, `(s₀, s₁) ↦ (s₁, s₀³)`: the transpose
of the length-exchanging map on the character lattice. -/
def specialIsogenyTorusMap (s : Fin 2 → Rˣ) : Fin 2 → Rˣ := ![s 1, s 0 ^ 3]

/-- The defining equation of the induced map on torus points. -/
@[simp]
theorem specialIsogenyTorusMap_def (s : Fin 2 → Rˣ) :
    specialIsogenyTorusMap s = ![s 1, s 0 ^ 3] := (rfl)

/-- **The induced map on characters.** Evaluating a character at the length-exchanged point is
evaluating at the original point the character `μ ↦ (3 μ₁, μ₀)`. That is the map the special
isogeny induces on the character lattice, whose matrix is the transpose of the one the isogeny
induces on torus coordinates. -/
theorem torusCharacter_specialIsogenyTorusMap (s : Fin 2 → Rˣ) (μ : Fin 2 → ℤ) :
    torusCharacter (specialIsogenyTorusMap s) μ = torusCharacter s ![3 * μ 1, μ 0] := by
  have h : ((s 0) ^ (3 : ℕ)) ^ μ 1 = s 0 ^ (3 * μ 1) := by
    rw [← zpow_natCast (s 0) 3, ← _root_.zpow_mul]
    norm_num
  rw [torusCharacter_def, torusCharacter_def, Fin.prod_univ_two, Fin.prod_univ_two,
    specialIsogenyTorusMap_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h, mul_comm]

/-- **The special isogeny on the weight torus.** On the diagonal matrix of the weight characters
of a torus point `s`, the formula returns the diagonal matrix of the weight characters of the
length-exchanged point `(s₁, s₀³)`. -/
theorem g2SpecialIsogeny_diagonal_torusCharacter (s : Fin 2 → Rˣ) :
    g2SpecialIsogeny (Matrix.diagonal fun a => (torusCharacter s (weight a) : R)) =
      Matrix.diagonal fun a => (torusCharacter (specialIsogenyTorusMap s) (weight a) : R) := by
  rw [g2SpecialIsogeny_diagonal]
  refine congrArg Matrix.diagonal (funext fun a => ?_)
  rw [torusCharacter_specialIsogenyTorusMap]
  fin_cases a <;>
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ← Units.val_mul, ← torusCharacter_add] <;>
    exact congrArg (fun μ : Fin 2 → ℤ => ((torusCharacter s μ : Rˣ) : R))
      (by ext b; fin_cases b <;> simp [weight_apply])

/-- **The special isogeny on the carrier's weight torus**: a point of the split weight torus is
carried to the point of the length-exchanged coordinates `(s₁, s₀³)`. -/
theorem g2SpecialIsogeny_coe_weightTorusPoints (s : Fin 2 → Rˣ) :
    g2SpecialIsogeny ((weightTorusPoints R s : _root_.Matrix.GeneralLinearGroup (Fin 7) R) :
        Matrix (Fin 7) (Fin 7) R) =
      ((weightTorusPoints R (specialIsogenyTorusMap s) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) := by
  rw [coe_weightTorusPoints_eq_diagonal, coe_weightTorusPoints_eq_diagonal,
    g2SpecialIsogeny_diagonal_torusCharacter]

end TauCeti.G2ShortRoot
