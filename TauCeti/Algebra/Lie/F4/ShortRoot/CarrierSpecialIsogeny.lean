/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Frobenius
public import TauCeti.Algebra.Lie.F4.ShortRoot.SpecialIsogeny

/-!
# The special isogeny on the pinned subgroups of the short-root type-F4 carrier

`TauCeti.F4ShortRoot.specialIsogenyMatrix` is the matrix formula for the special isogeny `τ` of
type `F4` in characteristic two, and `TauCeti.F4ShortRoot.points` realizes the short-root
carrier's points as a subgroup of `GL₂₆`. This file reads the formula on the carrier's eight
numbered simple root subgroups and on its rank-four split weight torus: the matrix of a numbered
simple-root point is the numbered simple root element matrix of the same parameter, and that of a
weight-torus point is the diagonal matrix of its weight characters, so the pinning equations, the
torus equation and the square relation proved for those matrices become statements about the
carrier's own pinned subgroups and its own Frobenius.

On the weight torus the formula exchanges the two root lengths on the character lattice: it
reverses the Bourbaki numbering of the coordinates and squares the two that pair with the long
simple roots.

Only the pinned subgroups are covered. The formula is not shown to be multiplicative, to carry
points of the carrier to points of the carrier, or to have any property at all at a point that is
not one of the numbered simple root elements or a weight-torus point; the square relations below
are the ones on those elements, not an identity of endomorphisms. The carrier is not identified
with the pinned simply connected group scheme of type `F4`, and constructions made here transfer
to that group scheme only along such an identification.

## Main definitions

* `TauCeti.F4ShortRoot.isogenyTorusMap`: the map the special isogeny induces on the coordinates
  of the split weight torus.

## Main results

* `TauCeti.F4ShortRoot.coe_rootSubgroupPoints_eq_rootElementMatrix`: the matrix of a numbered
  simple-root point is the numbered simple root element matrix.
* `TauCeti.F4ShortRoot.specialIsogenyMatrix_rootSubgroupPoints`: **the pinning equations** on the
  carrier's numbered simple root subgroups, exchanging the two root lengths.
* `TauCeti.F4ShortRoot.specialIsogenyMatrix_specialIsogenyMatrix_rootSubgroupPoints`: **the
  square relation** on those subgroups, against the carrier's own Frobenius at exponent one.
* `TauCeti.F4ShortRoot.coe_weightTorusPoints_eq_diagonal` and
  `TauCeti.F4ShortRoot.specialIsogenyMatrix_weightTorusPoints`: the matrix of a weight-torus
  point and **the torus equation** on it, with
  `TauCeti.F4ShortRoot.specialIsogenyMatrix_specialIsogenyMatrix_weightTorusPoints` the square
  relation there.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3 and §13.4.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

universe v

variable {A : Type v} [CommRing A] [CharP A 2]

omit [CharP A 2] in
/-- The matrix of a numbered simple-root point of the short-root carrier is the numbered simple
root element matrix of the same parameter. -/
-- Not a `simp` lemma: `TauCeti.F4ShortRoot.coe_rootSubgroupPoints` already rewrites the coercion
-- of a numbered simple-root point into the Kostant root-subgroup matrix, so it reaches the
-- left-hand side of this equation, and of the two below, before any of them can fire.
theorem coe_rootSubgroupPoints_eq_rootElementMatrix (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    ((rootSubgroupPoints k A u : GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) =
      rootElementMatrix k (Multiplicative.toAdd u) := by
  rw [coe_rootSubgroupPoints_eq, rootElementMatrix_def]

/-- **The pinning equations of the special isogeny on the carrier's numbered simple root
subgroups**: the numbered simple-root point of index `k` and parameter `u` is carried to the one
of the length-exchanged index, with the parameter raised to the length exponent. -/
-- Not a `simp` lemma, for the reason given at `coe_rootSubgroupPoints_eq_rootElementMatrix`.
theorem specialIsogenyMatrix_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    specialIsogenyMatrix
        (rootSubgroupPoints k A u : GeneralLinearGroup (Fin 26) A) =
      ((rootSubgroupPoints (isogenyReverse k) A
          (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) :
        GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
  rw [coe_rootSubgroupPoints_eq_rootElementMatrix]
  exact specialIsogenyMatrix_of_coe_eq k (Multiplicative.toAdd u)
    (coe_rootSubgroupPoints_eq_rootElementMatrix k u)

/-- **The square relation on the carrier's numbered simple root subgroups**: applying the special
isogeny twice to a numbered simple-root point gives the carrier's Frobenius at exponent one of
that point. -/
-- Not a `simp` lemma, for the reason given at `coe_rootSubgroupPoints_eq_rootElementMatrix`.
theorem specialIsogenyMatrix_specialIsogenyMatrix_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4)
    (u : Multiplicative A) :
    specialIsogenyMatrix
        (rootSubgroupPoints (isogenyReverse k) A
          (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) :
          GeneralLinearGroup (Fin 26) A) =
      ((frobenius 2 1 A (rootSubgroupPoints k A u) : GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) := by
  rw [specialIsogenyMatrix_specialIsogenyMatrix k (Multiplicative.toAdd u)
      (coe_rootSubgroupPoints_eq_rootElementMatrix k u)
      (specialIsogenyMatrix_rootSubgroupPoints k u).symm,
    rootElementMatrix_map_pow_two, frobenius_rootSubgroupPoints,
    coe_rootSubgroupPoints_eq_rootElementMatrix]
  norm_num

/-! ## The weight torus -/

/-- The map the special isogeny of type `F4` induces on the coordinates of the rank-four split
weight torus, `(s₀, s₁, s₂, s₃) ↦ (s₃², s₂², s₁, s₀)`: the transpose of the length-exchanging map
of the character lattice, which reverses the Bourbaki numbering and squares the two coordinates
pairing with the long simple roots. -/
def isogenyTorusMap (s : Fin 4 → Aˣ) : Fin 4 → Aˣ := ![s 3 ^ 2, s 2 ^ 2, s 1, s 0]

omit [CharP A 2] in
/-- The defining formula of the induced map on torus coordinates. -/
theorem isogenyTorusMap_def (s : Fin 4 → Aˣ) :
    isogenyTorusMap s = ![s 3 ^ 2, s 2 ^ 2, s 1, s 0] := (rfl)

omit [CharP A 2] in
/-- **Applying the induced map on torus coordinates twice squares every coordinate.** -/
@[simp]
theorem isogenyTorusMap_isogenyTorusMap (s : Fin 4 → Aˣ) :
    isogenyTorusMap (isogenyTorusMap s) = s ^ 2 := by
  funext i
  fin_cases i <;>
    simp only [isogenyTorusMap_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.pow_apply, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]

omit [CharP A 2] in
/-- **The induced map on characters.** Evaluating a weight character at the length-exchanged
point is evaluating at the original point the character `μ ↦ (μ₃, μ₂, 2 μ₁, 2 μ₀)`, the transpose
of the map the special isogeny induces on the character lattice. -/
theorem torusCharacter_isogenyTorusMap (s : Fin 4 → Aˣ) (μ : Fin 4 → ℤ) :
    torusCharacter (isogenyTorusMap s) μ =
      torusCharacter s ![μ 3, μ 2, 2 * μ 1, 2 * μ 0] := by
  have h : ∀ t : Aˣ, ∀ z : ℤ, (t ^ (2 : ℕ)) ^ z = t ^ (2 * z) := fun t z => by
    rw [← zpow_natCast t 2, ← _root_.zpow_mul]
    norm_num
  rw [torusCharacter_def, torusCharacter_def, Fin.prod_univ_four, Fin.prod_univ_four,
    isogenyTorusMap_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  rw [h (s 3) (μ 0), h (s 2) (μ 1)]
  simp only [mul_comm, mul_assoc, mul_left_comm]

/-- The two entries the `p`th quotient coordinate reads sit in a row and a column whose weights
differ by the length-exchanged weight of `p`. -/
private theorem f4ShortRootWeight_coordinateRow_sub_coordinateCol (p : Fin 26) :
    f4ShortRootWeight (coordinateRow 0 p) - f4ShortRootWeight (coordinateCol 0 p) =
      ![f4ShortRootWeight p 3, f4ShortRootWeight p 2, 2 * f4ShortRootWeight p 1,
        2 * f4ShortRootWeight p 0] := by
  revert p
  decide +kernel

/-- **The special isogeny on the weight torus, as a matrix formula.** A group element whose matrix
is the diagonal matrix of the weight characters of a torus point `s` is carried to the diagonal
matrix of the weight characters of the length-exchanged point. -/
theorem specialIsogenyMatrix_of_coe_eq_torus {g : GeneralLinearGroup (Fin 26) A} (s : Fin 4 → Aˣ)
    (hg : (g : Matrix (Fin 26) (Fin 26) A) =
      Matrix.diagonal fun a => (torusCharacter s (f4ShortRootWeight a) : A)) :
    specialIsogenyMatrix g =
      Matrix.diagonal fun a => (torusCharacter (isogenyTorusMap s) (f4ShortRootWeight a) : A) := by
  rw [specialIsogenyMatrix_of_coe_eq_diagonal
    (fun a => torusCharacter s (f4ShortRootWeight a)) hg]
  refine congrArg Matrix.diagonal (funext fun p => ?_)
  rw [torusCharacter_isogenyTorusMap, ← Units.val_mul, ← div_eq_mul_inv, ← torusCharacter_sub,
    f4ShortRootWeight_coordinateRow_sub_coordinateCol]

omit [CharP A 2] in
/-- The matrix of a point of the carrier's split weight torus is the diagonal matrix of the weight
characters at that point. -/
theorem coe_weightTorusPoints_eq_diagonal (s : Fin 4 → Aˣ) :
    ((weightTorusPoints A s : GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) =
      Matrix.diagonal fun a => (torusCharacter s (f4ShortRootWeight a) : A) := by
  rw [coe_weightTorusPoints, TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    diagGL_coe]

/-- **The torus equation of the special isogeny on the carrier's weight torus**: a point of the
split weight torus is carried to the point of the length-exchanged coordinates. -/
theorem specialIsogenyMatrix_weightTorusPoints (s : Fin 4 → Aˣ) :
    specialIsogenyMatrix (weightTorusPoints A s : GeneralLinearGroup (Fin 26) A) =
      ((weightTorusPoints A (isogenyTorusMap s) : GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) := by
  rw [coe_weightTorusPoints_eq_diagonal]
  exact specialIsogenyMatrix_of_coe_eq_torus s (coe_weightTorusPoints_eq_diagonal s)

/-- **The square relation on the carrier's weight torus**: applying the special isogeny twice to
a weight-torus point gives the carrier's Frobenius at exponent one of that point. -/
theorem specialIsogenyMatrix_specialIsogenyMatrix_weightTorusPoints (s : Fin 4 → Aˣ) :
    specialIsogenyMatrix
        (weightTorusPoints A (isogenyTorusMap s) : GeneralLinearGroup (Fin 26) A) =
      ((frobenius 2 1 A (weightTorusPoints A s) : GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) := by
  rw [specialIsogenyMatrix_weightTorusPoints, isogenyTorusMap_isogenyTorusMap,
    frobenius_weightTorusPoints, pow_one]

end TauCeti.F4ShortRoot
