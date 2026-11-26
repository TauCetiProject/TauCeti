/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.transvection` and its product law are the subject of this file.
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
-- `TauCeti.diagGL` occurs in the conjugation statement below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `TauCeti.permutationGL` occurs in the permutation-conjugation statement below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
-- `MonoidHom.noncommCoprod` packages products of commuting one-parameter subgroups.
public import Mathlib.GroupTheory.NoncommCoprod
-- `Matrix.GeneralLinearGroup.transvection` occurs in the bridge statement below.
public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
-- Non-public: the diagonal-matrix-unit product law is used only in a proof below.
import TauCeti.GroupTheory.Commutator
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Transvections in the general linear group

Mathlib's `Matrix.transvection i j c = 1 + c Eᵢⱼ` is the elementary matrix adding `c` times the
`j`-th coordinate to the `i`-th one. For `i ≠ j` it is invertible, and Mathlib packages it as
`Matrix.SpecialLinearGroup.transvection`, together with its zero, addition and inverse laws. This
file packages the invertible matrix `1 + c Eᵢⱼ` in `GL n A` as `TauCeti.transvectionUnit`, over a
possibly noncommutative ring `A`, where its inverse is `1 - c Eᵢⱼ`, and packages the resulting
one-parameter subgroup as `TauCeti.transvectionHom`. Over a commutative ring the transvection is
Mathlib's one viewed along `Matrix.SpecialLinearGroup.toGL`
(`TauCeti.toGL_transvection_eq_transvectionUnit`), and it is also Mathlib's
`Matrix.GeneralLinearGroup.transvection` (`TauCeti.transvectionUnit_eq_transvection`).

Writing `xᵢⱼ(c)` for the transvection, the relations are

* `xᵢⱼ(c) xₖₗ(d) = xₖₗ(d) xᵢⱼ(c)` whenever `j ≠ k` and `l ≠ i`;
* `⁅xᵢⱼ(c), xⱼₗ(d)⁆ = xᵢₗ(cd)` whenever `i`, `j` and `l` are distinct.

They are the **Chevalley commutator relations** of the general linear group. Reading the pair
`(i, j)` as the root `εᵢ - εⱼ` of the diagonal torus, the first covers every pair of roots whose
sum is neither a root nor zero, and the second every pair whose sum is a root:
`(εᵢ - εⱼ) + (εⱼ - εₗ)` is `εᵢ - εₗ`. In type `A` the structure constants are `±1`; the chosen
orientation in the second relation gives `1`, which is why its right-hand side is `xᵢₗ(cd)`.

The one remaining case, `xᵢⱼ(c)` against `xⱼᵢ(d)`, is deliberately absent: there the sum of the two
roots is zero, and no commutator formula in terms of a single root subgroup holds.

The opposite root subgroups nevertheless build the standard Weyl representative
`nᵢⱼ = xᵢⱼ(1) xⱼᵢ(-1) xᵢⱼ(1)`, the signed Weyl word. Over every ring it is the signed permutation
matrix `!![0, 1; -1, 0]` in the coordinates `i`, `j` and the identity elsewhere, its square is
`-1` on the plane of `i` and `j`, and the product `nᵢⱼ nₖᵢ` is the permutation matrix of a
three-cycle. The file also records its inverse and its conjugation action on the other
transvections; this is the normalizer half of the data pinning the elementary matrices against
the torus.

Over any ring, `TauCeti.diagGL_mul_transvectionUnit_mul_inv` says that conjugating a transvection
by an invertible diagonal matrix multiplies its parameter on both sides: `t xᵢⱼ(c) t⁻¹` is
`xᵢⱼ(tᵢ c tⱼ⁻¹)`. When `A` is commutative this rescales the parameter by `tᵢ tⱼ⁻¹`, the value at
`t` of the root `εᵢ - εⱼ`. Together with the two relations above these are the equations that pin
the elementary matrices against the diagonal torus.

## Main definitions

* `TauCeti.transvectionUnit`: a transvection `1 + c Eᵢⱼ` at a pair of distinct indices, as an
  element of `GL n A` over a ring `A`; over a commutative ring it is
  `Matrix.SpecialLinearGroup.transvection` along `Matrix.SpecialLinearGroup.toGL`.
* `TauCeti.transvectionHom`: the resulting homomorphism from the additive group of `A`.
* `TauCeti.commutingTransvectionPairHom`: the product of two commuting transvection
  homomorphisms, with a shared parameter.
* `TauCeti.transvectionWeylElement`: the standard Weyl representative exchanging two indices.

## Main results

* `TauCeti.toGL_transvection_eq_transvectionUnit`: over a commutative ring,
  `TauCeti.transvectionUnit` is Mathlib's special-linear transvection viewed in `GL n A`.
* `TauCeti.transvectionUnit_mem_of_adjacent`: a subgroup containing the adjacent transvections
  in both orientations contains every transvection.
* `TauCeti.commute_transvectionUnit`: transvections at index pairs that do not chain commute.
* `TauCeti.commutatorElement_transvectionUnit` and
  `TauCeti.commutatorElement_transvectionUnit_reverse`: the commutators of two chaining
  transvections in either orientation.
* `Equiv.reindexGL_transvectionUnit`: relabelling the indices sends a transvection to the
  transvection at the relabelled pair of indices.
* `TauCeti.det_transvectionUnit` and `TauCeti.transvectionUnit_injective`: a transvection has
  determinant `1`, and distinct parameters give distinct transvections.
* `TauCeti.diagGL_mul_transvectionUnit_mul_inv`: conjugation by an invertible diagonal matrix.
* `TauCeti.permutationGL_inv_mul_transvectionUnit_mul_permutationGL`: conjugation by a
  permutation matrix relabels the two indices.
* `TauCeti.map_transvectionUnit` and `TauCeti.map_transvectionWeylElement`: transvections and their
  Weyl representatives are natural in the base ring.
* `TauCeti.coe_transvectionWeylElement` and `TauCeti.coe_transvectionWeylElement_fin_two`: the
  signed Weyl word is `1 - Eᵢᵢ - Eⱼⱼ + Eᵢⱼ - Eⱼᵢ`, which in size two is `!![0, 1; -1, 0]`.
* `TauCeti.transvectionWeylElement_mul_self` and
  `TauCeti.transvectionWeylElement_fin_two_mul_self`: its square is the diagonal matrix with
  `-1` in positions `i` and `j`, which in size two is `-1`.
* `TauCeti.transvectionWeylElement_eq_diagGL_mul_permutationGL`: it is the permutation matrix of
  the transposition of `i` and `j` with its `j`-th row negated.
* `TauCeti.permutationGL_swap_mul_swap_same_eq_transvectionWeylElement_mul`: the permutation
  matrix of the three-cycle `(i j) (i k)` is `nᵢⱼ nₖᵢ`.
* `TauCeti.transvectionWeylElement_inv`: the representative for the opposite root is the inverse.
* `TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_self` and
  `TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_symm`: the reflection exchanges
  its two root subgroups and negates their parameters.
* `TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_left` and
  `TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_right`: conjugation by `nᵢⱼ`
  moves an occurrence of `j` to `i` with unchanged parameter. Applying these at the opposite root
  describes the reverse index movement by conjugation with `nᵢⱼ⁻¹`.
* `TauCeti.commute_transvectionUnit_transvectionWeylElement` and
  `TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_of_ne`: a transvection whose two
  indices avoid `i` and `j` commutes with `nᵢⱼ`, so conjugation by `nᵢⱼ` fixes it.
* `TauCeti.transvectionWeylElement_mul_diagGL_mul_inv`: conjugation by `nᵢⱼ` exchanges the
  two corresponding diagonal coordinates.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3, where these relations are the type `A`
  case of the Chevalley commutator formula.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open Matrix

open scoped commutatorElement

namespace TauCeti

universe u v

variable {n : Type*} [DecidableEq n] {A : Type u} {i j k l : n}

section Products

variable [Fintype n]

variable [CommRing A]

/-- Conjugating a transvection by a diagonal matrix rescales its parameter by the two
corresponding diagonal entries. The hypothesis says that the two diagonals are inverse to one
another. -/
theorem diagonal_mul_transvection_mul_diagonal {v w : n → A} (hvw : ∀ a, v a * w a = 1) (c : A) :
    diagonal v * transvection i j c * diagonal w = transvection i j (v i * c * w j) := by
  have hd : diagonal v * diagonal w = (1 : Matrix n n A) := by
    rw [Matrix.diagonal_mul_diagonal]
    exact Matrix.diagonal_eq_one.2 (by ext a; exact hvw a)
  simp only [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hd,
    diagonal_mul_single_mul_diagonal]

end Products

/-! ## Transvections as invertible matrices -/

section Ring

variable [Fintype n] [Ring A]

/-- A transvection `1 + c Eᵢⱼ` at a pair of distinct indices, as an element of `GL n A` over a
possibly noncommutative ring; its inverse is `1 - c Eᵢⱼ`. It is the value at `c` of the root
subgroup homomorphism `TauCeti.transvectionHom` attached to the root `εᵢ - εⱼ` of the diagonal
torus. -/
def transvectionUnit (hij : i ≠ j) (c : A) : GL n A where
  val := 1 + single i j c
  inv := 1 + single i j (-c)
  val_inv := by simp [add_mul, mul_add, hij.symm, add_assoc, ← single_add]
  inv_val := by simp [add_mul, mul_add, hij.symm, add_assoc, ← single_add]

/-- The matrix underlying `TauCeti.transvectionUnit` is `1 + c Eᵢⱼ`. This is the `simp` normal
form over a noncommutative ring; it has low priority so that over a commutative ring the
higher-priority `TauCeti.coe_transvectionUnit` fires first and rewrites to Mathlib's
`Matrix.transvection`, the form its transvection lemmas expect. -/
@[simp low]
theorem coe_transvectionUnit_eq_one_add_single (hij : i ≠ j) (c : A) :
    (transvectionUnit hij c : Matrix n n A) = 1 + single i j c :=
  (rfl)

/-- A transvection acts on column vectors by the elementary row operation adding `c` times the
`j`-th coordinate to the `i`-th one. -/
theorem transvectionUnit_mulVec (hij : i ≠ j) (c : A) (v : n → A) :
    (transvectionUnit hij c : Matrix n n A) *ᵥ v = Function.update v i (v i + c * v j) := by
  rw [coe_transvectionUnit_eq_one_add_single, add_mulVec, one_mulVec, single_mulVec]
  ext k
  rcases eq_or_ne k i with rfl | hk <;> simp [*]

/-- The transvection of parameter zero is the identity. -/
@[simp]
theorem transvectionUnit_zero (hij : i ≠ j) : transvectionUnit hij (0 : A) = 1 :=
  Units.ext (by simp [coe_transvectionUnit_eq_one_add_single])

/-- The parameter of a transvection is additive: the root subgroup is one-parameter. -/
@[simp]
theorem transvectionUnit_add (hij : i ≠ j) (c d : A) :
    transvectionUnit hij (c + d) = transvectionUnit hij c * transvectionUnit hij d :=
  Units.ext (by
    simp [coe_transvectionUnit_eq_one_add_single, add_mul, mul_add, hij.symm, single_add,
      add_assoc])

/-- The inverse of a transvection negates its parameter. -/
@[simp]
theorem transvectionUnit_inv (hij : i ≠ j) (c : A) :
    (transvectionUnit hij c)⁻¹ = transvectionUnit hij (-c) :=
  Units.ext (rfl)

/-- The transvections at a fixed pair of distinct indices form a one-parameter subgroup of
`GL n A`, isomorphic to the additive group of `A`. This is the root subgroup of `εᵢ - εⱼ`. -/
def transvectionHom (hij : i ≠ j) : Multiplicative A →* GL n A where
  toFun c := transvectionUnit hij c.toAdd
  map_one' := transvectionUnit_zero hij
  map_mul' c d := transvectionUnit_add hij c.toAdd d.toAdd

/-- The value of the root subgroup homomorphism is the transvection of the parameter. -/
@[simp]
theorem transvectionHom_apply (hij : i ≠ j) (c : Multiplicative A) :
    transvectionHom hij c = transvectionUnit hij (Multiplicative.toAdd c) :=
  (rfl)

/-- Distinct parameters give distinct transvections: the parameter is the `(i, j)` entry. So the
root subgroup is a copy of the additive group of `A` inside `GL n A`, not a quotient of it. -/
theorem transvectionUnit_injective (hij : i ≠ j) :
    Function.Injective fun c : A => transvectionUnit hij c := by
  intro c d h
  simpa [coe_transvectionUnit_eq_one_add_single, hij] using
    congrArg (fun u : GL n A => (u : Matrix n n A) i j) h

/-- The bundled root subgroup homomorphism is injective. -/
theorem transvectionHom_injective (hij : i ≠ j) :
    Function.Injective (transvectionHom (A := A) hij) := by
  intro c d h
  apply Multiplicative.toAdd.injective
  apply transvectionUnit_injective hij
  simpa only [transvectionHom_apply] using h

/-- Transvections at index pairs that do not chain commute in `GL n A`. -/
theorem commute_transvectionUnit (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (c d : A) : Commute (transvectionUnit hij c) (transvectionUnit hkl d) :=
  Units.ext (by
    simp [coe_transvectionUnit_eq_one_add_single, add_mul, mul_add, hjk, hli]
    abel)

/-- Two pointwise commuting transvection homomorphisms, evaluated at a shared parameter after a
chosen endomorphism in the second component. This packages the standard construction of a
one-parameter subgroup as a product of two commuting elementary one-parameter subgroups. -/
def commutingTransvectionPairHom (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (second : Multiplicative A →* Multiplicative A) : Multiplicative A →* GL n A :=
  ((transvectionHom hij).noncommCoprod (transvectionHom hkl)
      (fun c d ↦ by simpa only [transvectionHom_apply] using
        commute_transvectionUnit hij hkl hjk hli c.toAdd d.toAdd)).comp
    ((MonoidHom.id _).prod second)

/-- The commuting-pair homomorphism evaluates to the product of its two transvections. -/
@[simp]
theorem commutingTransvectionPairHom_apply (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (second : Multiplicative A →* Multiplicative A) (c : Multiplicative A) :
    commutingTransvectionPairHom hij hkl hjk hli second c =
      transvectionUnit hij c.toAdd * transvectionUnit hkl (second c).toAdd := by
  simp [commutingTransvectionPairHom]

/-- The product of two chaining transvections in `GL n A`, in the two orders. -/
theorem transvectionUnit_mul_transvectionUnit_eq_mul_mul
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (c d : A) :
    transvectionUnit hij c * transvectionUnit hjl d =
      transvectionUnit hjl d * transvectionUnit hij c * transvectionUnit hil (c * d) :=
  Units.ext (by
    simp [coe_transvectionUnit_eq_one_add_single, add_mul, mul_add, hij.symm, hil.symm]
    abel)

/-- **The Chevalley commutator relation of type `A`.** The commutator of the root subgroup elements
`xᵢⱼ(c)` and `xⱼₗ(d)`, for distinct `i`, `j` and `l`, is `xᵢₗ(cd)`: the root `εᵢ - εₗ` is the sum
of `εᵢ - εⱼ` and `εⱼ - εₗ`, and the structure constant is `1`. -/
theorem commutatorElement_transvectionUnit (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (c d : A) :
    ⁅transvectionUnit hij c, transvectionUnit hjl d⁆ = transvectionUnit hil (c * d) := by
  ext : 1
  simp only [commutatorElement_def, Units.val_mul, transvectionUnit_inv,
    coe_transvectionUnit_eq_one_add_single, ← single_neg]
  simp [add_mul, mul_add, hij.symm, hjl.symm, hil.symm]
  abel

/-- The reverse-orientation form of the type-`A` Chevalley commutator relation:
`[xᵢⱼ(c), xₖᵢ(d)] = xₖⱼ(-(dc))`. -/
theorem commutatorElement_transvectionUnit_reverse
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (c d : A) :
    ⁅transvectionUnit hij c, transvectionUnit hki d⁆ = transvectionUnit hkj (-(d * c)) := by
  calc
    ⁅transvectionUnit hij c, transvectionUnit hki d⁆ =
        ⁅transvectionUnit hki d, transvectionUnit hij c⁆⁻¹ :=
      (commutatorElement_inv _ _).symm
    _ = (transvectionUnit hkj (d * c))⁻¹ := by
      rw [commutatorElement_transvectionUnit hki hij hkj]
    _ = transvectionUnit hkj (-(d * c)) := transvectionUnit_inv hkj (d * c)

/-- The commutator of opposite transvections `xᵢₖ(c)` and `xₖᵢ(d)` with `d * c = 0` is the
matrix `1 + (c * d) Eᵢᵢ`, which differs from the identity only in the diagonal entry `(i, i)`. -/
theorem coe_commutatorElement_transvectionUnit_of_mul_eq_zero (hik : i ≠ k) {c d : A}
    (hdc : d * c = 0) :
    (⁅transvectionUnit hik c, transvectionUnit hik.symm d⁆ : GL n A) =
      (1 : Matrix n n A) + single i i (c * d) := by
  simp only [commutatorElement_def, Units.val_mul, transvectionUnit_inv,
    coe_transvectionUnit_eq_one_add_single]
  simp [add_mul, mul_add, hik, hik.symm, single_mul_single_same, hdc, mul_assoc, ← single_neg]
  abel

/-! ## Weyl elements -/

/-- The standard representative in `GL n A` of the Weyl-group transposition exchanging `i` and
`j`, written as the three-factor word `xᵢⱼ(1) xⱼᵢ(-1) xᵢⱼ(1)`. -/
def transvectionWeylElement (hij : i ≠ j) : GL n A :=
  transvectionUnit hij 1 * transvectionUnit hij.symm (-1) * transvectionUnit hij 1

/-- The transvection Weyl element is its standard three-factor word. -/
theorem transvectionWeylElement_def (hij : i ≠ j) :
    transvectionWeylElement (A := A) hij =
      transvectionUnit hij 1 * transvectionUnit hij.symm (-1) * transvectionUnit hij 1 := (rfl)

/-- A transvection whose two indices both avoid `i` and `j` commutes with the Weyl representative
exchanging `i` and `j`: it commutes with each of the three transvections of the defining word. -/
theorem commute_transvectionUnit_transvectionWeylElement (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (hik : i ≠ k) (hlj : l ≠ j) (c : A) :
    Commute (transvectionUnit hkl c) (transvectionWeylElement (A := A) hij) := by
  rw [transvectionWeylElement_def]
  have hpos : Commute (transvectionUnit hkl c) (transvectionUnit hij (1 : A)) :=
    commute_transvectionUnit hkl hij hli hjk c 1
  have hneg : Commute (transvectionUnit hkl c) (transvectionUnit hij.symm (-1 : A)) :=
    commute_transvectionUnit hkl hij.symm hlj hik c (-1)
  exact (hpos.mul_right hneg).mul_right hpos

/-- **The signed Weyl word as a matrix.** The Weyl representative `xᵢⱼ(1) xⱼᵢ(-1) xᵢⱼ(1)` is
`1 - Eᵢᵢ - Eⱼⱼ + Eᵢⱼ - Eⱼᵢ`: in the coordinates `i`, `j` it is `!![0, 1; -1, 0]`, and it is the
identity on the other coordinates. -/
theorem coe_transvectionWeylElement (hij : i ≠ j) :
    ((transvectionWeylElement (A := A) hij : GL n A) : Matrix n n A) =
      1 - single i i 1 - single j j 1 + single i j 1 - single j i 1 := by
  simp only [transvectionWeylElement_def, Units.val_mul, coe_transvectionUnit_eq_one_add_single]
  simp [add_mul, mul_add, hij.symm, ← single_neg]
  abel

/-- The entries of the Weyl representative exchanging `i` and `j`: its `i`-th row is the `j`-th
row of the identity, its `j`-th row is minus the `i`-th row of the identity, and every other row
is that of the identity. -/
theorem coe_transvectionWeylElement_apply (hij : i ≠ j) (a b : n) :
    ((transvectionWeylElement (A := A) hij : GL n A) : Matrix n n A) a b =
      if a = i then (1 : Matrix n n A) j b
      else if a = j then -(1 : Matrix n n A) i b
      else (1 : Matrix n n A) a b := by
  rw [coe_transvectionWeylElement]
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
    by_cases hbj : b = j <;> subst_vars <;> simp_all [Matrix.one_apply, eq_comm]

private theorem coe_transvectionWeylElement_mul_apply (hij : i ≠ j) (M : Matrix n n A)
    (a b : n) :
    (((transvectionWeylElement (A := A) hij : GL n A) : Matrix n n A) * M) a b =
      if a = i then M j b else if a = j then -M i b else M a b := by
  rw [Matrix.mul_apply]
  simp_rw [coe_transvectionWeylElement_apply hij a]
  by_cases hai : a = i
  · subst a
    simp [Matrix.one_apply]
  · by_cases haj : a = j
    · subst a
      simp [Matrix.one_apply, hij.symm]
    · simp [Matrix.one_apply, hai, haj]

/-- **The square of the signed Weyl word** is the diagonal matrix with `-1` in positions `i` and
`j` and `1` elsewhere: on the plane of the coordinates `i` and `j` it is `-1`. -/
theorem transvectionWeylElement_mul_self (hij : i ≠ j) :
    transvectionWeylElement (A := A) hij * transvectionWeylElement hij =
      diagGL (Pi.mulSingle i (-1) * Pi.mulSingle j (-1)) := by
  ext a b
  rw [Units.val_mul, coe_transvectionWeylElement_mul_apply, diagGL_apply]
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
    by_cases hbj : b = j <;> subst_vars <;>
    simp_all [coe_transvectionWeylElement_apply, Matrix.one_apply, eq_comm]

/-- The signed Weyl word is a signed permutation matrix: it is the permutation matrix of the
transposition of `i` and `j`, with its `j`-th row negated. -/
theorem transvectionWeylElement_eq_diagGL_mul_permutationGL (hij : i ≠ j) :
    transvectionWeylElement (A := A) hij =
      diagGL (Pi.mulSingle j (-1)) * permutationGL (Equiv.swap i j) := by
  ext a b
  rw [coe_transvectionWeylElement_apply, Units.val_mul, diagGL_coe, permutationGL_coe,
    Matrix.diagonal_mul]
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
    by_cases hbj : b = j <;> subst_vars <;>
    simp_all [Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.swap_apply_def, eq_comm]

/-- The permutation matrix of the three-cycle `(i j) (i k)` is the product of the two signed Weyl
words `nᵢⱼ nₖᵢ`: their signs cancel. -/
theorem permutationGL_swap_mul_swap_same_eq_transvectionWeylElement_mul (hij : i ≠ j)
    (hik : i ≠ k) :
    permutationGL (k := A) (Equiv.swap i j * Equiv.swap i k) =
      transvectionWeylElement hij * transvectionWeylElement hik.symm := by
  ext a b
  rw [Units.val_mul, coe_transvectionWeylElement_mul_apply, permutationGL_coe]
  simp only [coe_transvectionWeylElement_apply, Matrix.one_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    _root_.mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.swap_apply_def]
  split_ifs <;> grind

/-- In size two the signed Weyl word `x₀₁(1) x₁₀(-1) x₀₁(1)` is the matrix `!![0, 1; -1, 0]`. -/
theorem coe_transvectionWeylElement_fin_two :
    ((transvectionWeylElement (A := A) (zero_ne_one : (0 : Fin 2) ≠ 1) : GL (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) = !![0, 1; -1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_transvectionWeylElement_apply]

/-- In size two the square of the signed Weyl word is `-1`. -/
theorem transvectionWeylElement_fin_two_mul_self :
    transvectionWeylElement (A := A) (zero_ne_one : (0 : Fin 2) ≠ 1) *
      transvectionWeylElement zero_ne_one = -1 := by
  rw [transvectionWeylElement_mul_self]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-! ## Conjugation by invertible diagonal matrices -/

/-- Conjugating the root subgroup element `xᵢⱼ(c)` by the diagonal matrix with entries `t` gives
`xᵢⱼ(tᵢ c tⱼ⁻¹)`, over any ring. When `A` is commutative this rescales the parameter by `tᵢ tⱼ⁻¹`,
the value at `t` of the root `εᵢ - εⱼ`. This is the equation pinning the root subgroup against the
diagonal torus. -/
theorem diagGL_mul_transvectionUnit_mul_inv (hij : i ≠ j) (t : n → Aˣ) (c : A) :
    diagGL t * transvectionUnit hij c * (diagGL t)⁻¹ =
      transvectionUnit hij ((t i : A) * c * ((t j)⁻¹ : Aˣ)) := by
  have hval : ((((diagGL t)⁻¹ : GL n A)) : Matrix n n A) =
      diagonal fun a => (((t a)⁻¹ : Aˣ) : A) := by
    rw [← map_inv diagGL t, diagGL_coe]
    simp
  have hd : diagonal (fun a => (t a : A)) * diagonal (fun a => (((t a)⁻¹ : Aˣ) : A)) = 1 := by
    rw [diagonal_mul_diagonal]
    exact diagonal_eq_one.2 (funext fun a => (t a).mul_inv)
  refine Units.ext ?_
  -- `t (1 + c Eᵢⱼ) t⁻¹ = t t⁻¹ + tᵢ c tⱼ⁻¹ Eᵢⱼ`
  simp only [Units.val_mul, coe_transvectionUnit_eq_one_add_single, diagGL_coe, hval,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hd, diagonal_mul_single_mul_diagonal]

end Ring

variable [CommRing A]

section Unit

variable [Fintype n]

/-- Over a commutative ring, the matrix underlying `TauCeti.transvectionUnit` is Mathlib's
transvection. -/
@[simp]
theorem coe_transvectionUnit (hij : i ≠ j) (c : A) :
    (transvectionUnit hij c : Matrix n n A) = transvection i j c :=
  (rfl)

/-- Viewing a special-linear transvection in the general linear group gives
`TauCeti.transvectionUnit`. -/
theorem toGL_transvection_eq_transvectionUnit (hij : i ≠ j) (c : A) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij c) =
      transvectionUnit hij c :=
  Units.ext (rfl)

/-- Over a commutative ring, `TauCeti.transvectionUnit` is Mathlib's
`Matrix.GeneralLinearGroup.transvection`. -/
theorem transvectionUnit_eq_transvection (hij : i ≠ j) (c : A) :
    transvectionUnit hij c = Matrix.GeneralLinearGroup.transvection i j hij c :=
  Units.ext (rfl)

/-- A transvection has determinant one, so the root subgroup lands in `SLₙ`. -/
@[simp]
theorem det_transvectionUnit (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup.det (transvectionUnit hij c) = 1 := by
  rw [← toGL_transvection_eq_transvectionUnit]
  exact SpecialLinearGroup.coeToGL_det _

private theorem transpose_coe_transvectionWeylElement_symm (hij : i ≠ j) :
    (((transvectionWeylElement (A := A) hij.symm : GL n A) : Matrix n n A).transpose) =
      ((transvectionWeylElement hij : GL n A) : Matrix n n A) := by
  ext a b
  rw [Matrix.transpose_apply, coe_transvectionWeylElement_apply,
    coe_transvectionWeylElement_apply]
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      simp_all [Matrix.one_apply, eq_comm]

private theorem coe_mul_transvectionWeylElement_symm_apply (hij : i ≠ j) (M : Matrix n n A)
    (a b : n) :
    (M * ((transvectionWeylElement (A := A) hij.symm : GL n A) : Matrix n n A)) a b =
      if b = i then M a j else if b = j then -M a i else M a b := by
  -- Read the entry off the transposed product, where the Weyl factor becomes the left one and
  -- `coe_transvectionWeylElement_mul_apply` applies.
  rw [← Matrix.transpose_apply
        (M * ((transvectionWeylElement (A := A) hij.symm : GL n A) : Matrix n n A)) b a,
    Matrix.transpose_mul, transpose_coe_transvectionWeylElement_symm (A := A) hij,
    coe_transvectionWeylElement_mul_apply (A := A) hij]
  simp only [Matrix.transpose_apply]

private theorem coe_transvectionWeylElement_conj_apply (hij : i ≠ j) (M : Matrix n n A)
    (a b : n) :
    (((transvectionWeylElement (A := A) hij : GL n A) : Matrix n n A) * M *
        ((transvectionWeylElement hij.symm : GL n A) : Matrix n n A)) a b =
      if a = i then
        if b = i then M j j else if b = j then -M j i else M j b
      else if a = j then
        if b = i then -M i j else if b = j then M i i else -M i b
      else if b = i then M a j else if b = j then -M a i else M a b := by
  rw [coe_mul_transvectionWeylElement_symm_apply (A := A) hij]
  simp only [coe_transvectionWeylElement_mul_apply (A := A)]
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;> simp_all

/-- The inverse of the Weyl representative for `εᵢ-εⱼ` is the representative for the
opposite root `εⱼ-εᵢ`. -/
@[simp]
theorem transvectionWeylElement_inv (hij : i ≠ j) :
    (transvectionWeylElement (A := A) hij)⁻¹ = transvectionWeylElement hij.symm := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  ext a b
  rw [Units.val_mul]
  rw [coe_transvectionWeylElement_mul_apply]
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp_all [coe_transvectionWeylElement_apply, Matrix.one_apply]

/-- Conjugation by the Weyl representative for `εᵢ-εⱼ` sends its own root subgroup to
the opposite root subgroup and negates the parameter. -/
@[simp]
theorem transvectionWeylElement_mul_transvectionUnit_mul_inv_self (hij : i ≠ j) (c : A) :
    transvectionWeylElement hij * transvectionUnit hij c *
        transvectionWeylElement hij.symm =
      transvectionUnit hij.symm (-c) := by
  apply Units.ext
  ext a b
  simp only [Units.val_mul, coe_transvectionUnit]
  rw [coe_transvectionWeylElement_conj_apply]
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      simp_all [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, eq_comm]

/-- Conjugation by the Weyl representative for `εᵢ-εⱼ` sends the opposite root subgroup
back to its root subgroup and negates the parameter. -/
@[simp]
theorem transvectionWeylElement_mul_transvectionUnit_mul_inv_symm (hij : i ≠ j) (c : A) :
    transvectionWeylElement hij * transvectionUnit hij.symm c *
        transvectionWeylElement hij.symm =
      transvectionUnit hij (-c) := by
  have hT : (((transvectionWeylElement (A := A) hij : GL n A) : Matrix n n A)).transpose =
      ((transvectionWeylElement hij.symm : GL n A) : Matrix n n A) :=
    transpose_coe_transvectionWeylElement_symm (A := A) hij.symm
  have h := congrArg Matrix.transpose (congrArg Units.val
    (transvectionWeylElement_mul_transvectionUnit_mul_inv_self (A := A) hij c))
  apply Units.ext
  simpa only [Units.val_mul, coe_transvectionUnit, Matrix.transpose_mul, mul_assoc,
    Matrix.transpose_transvection, transpose_coe_transvectionWeylElement_symm (A := A) hij,
    hT] using h

/-- Conjugation by the Weyl representative exchanging `i` and `j` replaces the left index `j`
of `xⱼₖ(c)` by `i`. -/
@[simp]
theorem transvectionWeylElement_mul_transvectionUnit_mul_inv_left
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (c : A) :
    transvectionWeylElement hij * transvectionUnit hjk c *
        transvectionWeylElement hij.symm =
      transvectionUnit hik c := by
  rw [← transvectionWeylElement_inv hij]
  rw [transvectionWeylElement_def]
  set x := transvectionUnit hij (1 : A)
  set y := transvectionUnit hij.symm (-1 : A)
  set z := transvectionUnit hjk c
  set t := transvectionUnit hik c
  have hxz : MulAut.conj x z = t * z := by
    rw [conj_eq_commutatorElement_mul, commutatorElement_transvectionUnit hij hjk hik]
    simp only [one_mul, z, t]
  have hyt : MulAut.conj y t = z⁻¹ * t := by
    rw [conj_eq_commutatorElement_mul, commutatorElement_transvectionUnit hij.symm hik hjk]
    simp only [neg_one_mul, transvectionUnit_inv, z, t]
  have hyz : Commute y z :=
    commute_transvectionUnit hij.symm hjk hij hjk.symm (-1) c
  have hxt : Commute x t :=
    commute_transvectionUnit hij hik hij.symm hik.symm 1 c
  have htz : Commute t z :=
    commute_transvectionUnit hik hjk hjk.symm hik.symm c c
  calc
    (x * y * x) * z * (x * y * x)⁻¹ =
        x * (y * (x * z * x⁻¹) * y⁻¹) * x⁻¹ := by group
    _ = x * (y * (t * z) * y⁻¹) * x⁻¹ := by
      rw [← MulAut.conj_apply x z, hxz]
    _ = x * ((y * t * y⁻¹) * (y * z * y⁻¹)) * x⁻¹ := by group
    _ = x * ((z⁻¹ * t) * z) * x⁻¹ := by
      rw [← MulAut.conj_apply y t, hyt, hyz.mul_inv_cancel]
    _ = x * t * x⁻¹ := by rw [htz.symm.inv_mul_cancel]
    _ = t := hxt.mul_inv_cancel

/-- Conjugation by the Weyl representative exchanging `i` and `j` replaces the right index `j`
of `xₖⱼ(c)` by `i`. -/
@[simp]
theorem transvectionWeylElement_mul_transvectionUnit_mul_inv_right
    (hij : i ≠ j) (hkj : k ≠ j) (hki : k ≠ i) (c : A) :
    transvectionWeylElement hij * transvectionUnit hkj c *
        transvectionWeylElement hij.symm =
      transvectionUnit hki c := by
  rw [← transvectionWeylElement_inv hij]
  rw [transvectionWeylElement_def]
  set x := transvectionUnit hij (1 : A)
  set y := transvectionUnit hij.symm (-1 : A)
  set z := transvectionUnit hkj c
  set t := transvectionUnit hki c
  have hxz : Commute x z :=
    commute_transvectionUnit hij hkj hkj.symm hij.symm 1 c
  have hyz : MulAut.conj y z = t * z := by
    rw [conj_eq_commutatorElement_mul,
      commutatorElement_transvectionUnit_reverse hij.symm hkj hki]
    simp only [mul_neg, mul_one, neg_neg, z, t]
  have hxt : MulAut.conj x t = z⁻¹ * t := by
    rw [conj_eq_commutatorElement_mul,
      commutatorElement_transvectionUnit_reverse hij hki hkj]
    simp only [mul_one, transvectionUnit_inv, z, t]
  have htz : Commute t z :=
    commute_transvectionUnit hki hkj hki.symm hkj.symm c c
  calc
    (x * y * x) * z * (x * y * x)⁻¹ =
        x * (y * (x * z * x⁻¹) * y⁻¹) * x⁻¹ := by group
    _ = x * (y * z * y⁻¹) * x⁻¹ := by rw [hxz.mul_inv_cancel]
    _ = x * (t * z) * x⁻¹ := by rw [← MulAut.conj_apply y z, hyz]
    _ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
    _ = (z⁻¹ * t) * z := by rw [← MulAut.conj_apply x t, hxt, hxz.mul_inv_cancel]
    _ = t := htz.symm.inv_mul_cancel

/-- Conjugation by the Weyl representative exchanging `i` and `j` fixes a transvection whose two
indices both avoid `i` and `j`: the reflection in `εᵢ - εⱼ` fixes the root `εₖ - εₗ`. -/
@[simp]
theorem transvectionWeylElement_mul_transvectionUnit_mul_inv_of_ne
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (hik : i ≠ k) (hlj : l ≠ j) (c : A) :
    transvectionWeylElement hij * transvectionUnit hkl c *
        transvectionWeylElement hij.symm =
      transvectionUnit hkl c := by
  have hcomm := commute_transvectionUnit_transvectionWeylElement hij hkl hjk hli hik hlj c
  rw [← transvectionWeylElement_inv hij]
  exact hcomm.symm.mul_inv_cancel

/-- If a subgroup of `GL (Fin (m + 1), A)` contains every adjacent transvection in both
orientations, then it contains every elementary transvection. -/
theorem transvectionUnit_mem_of_adjacent {m : ℕ}
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (m + 1)) A))
    (hadjacent : ∀ {i j : Fin (m + 1)} (hij : i ≠ j) (c : A),
      i.val + 1 = j.val ∨ j.val + 1 = i.val → transvectionUnit hij c ∈ H)
    {i j : Fin (m + 1)} (hij : i ≠ j) (c : A) : transvectionUnit hij c ∈ H := by
  exact Subgroup.mem_of_adjacent_of_commutator H
    (fun hij c => transvectionUnit hij c)
    (fun hij hjk hik a => by
      simpa using commutatorElement_transvectionUnit hij hjk hik a 1)
    hadjacent hij c

/-- Conjugating the transvection `xᵢⱼ(c)` by the permutation matrix of `σ` gives the transvection
`x_{σ⁻¹ i, σ⁻¹ j}(c)`. -/
@[simp]
theorem permutationGL_inv_mul_transvectionUnit_mul_permutationGL (σ : Equiv.Perm n)
    (hij : i ≠ j) (c : A) :
    (permutationGL (k := A) σ)⁻¹ * transvectionUnit hij c * permutationGL (k := A) σ =
      transvectionUnit (σ.symm.injective.ne hij) c := by
  ext a b
  rw [coe_permutationGL_inv_mul_mul_permutationGL_apply, coe_transvectionUnit,
    coe_transvectionUnit]
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Equiv.symm_apply_eq]

end Unit

/-! ## Naturality in the base ring -/

section Map

variable [Fintype n] {B : Type v} [CommRing B]

/-- A transvection is natural in the base ring: applying a ring homomorphism entrywise to
`xᵢⱼ(c)` gives `xᵢⱼ(f c)`. -/
@[simp]
theorem map_transvectionUnit (f : A →+* B) (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup.map f (transvectionUnit hij c) = transvectionUnit hij (f c) := by
  ext a b
  exact congrArg (fun s : Matrix.SpecialLinearGroup n B => (s : Matrix n n B) a b)
    (SpecialLinearGroup.map_transvection f hij c)

/-- A transvection Weyl representative is natural in the base ring. -/
@[simp]
theorem map_transvectionWeylElement (f : A →+* B) (hij : i ≠ j) :
    Matrix.GeneralLinearGroup.map f (transvectionWeylElement hij) =
      transvectionWeylElement hij := by
  simp [transvectionWeylElement]

end Map

/-! ## Conjugation by the diagonal torus -/

section Torus

variable {N : ℕ} {i j : Fin N}

/-- Conjugating an invertible diagonal matrix by the Weyl representative for `εᵢ - εⱼ`
exchanges its `i`-th and `j`-th diagonal entries. -/
@[simp]
theorem transvectionWeylElement_mul_diagGL_mul_inv (hij : i ≠ j) (t : Fin N → Aˣ) :
    transvectionWeylElement hij * diagGL t * transvectionWeylElement hij.symm =
      diagGL (t ∘ Equiv.swap i j) := by
  apply Units.ext
  ext a b
  simp only [Units.val_mul, diagGL_coe]
  rw [coe_transvectionWeylElement_conj_apply]
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      subst_vars <;> simp_all [Matrix.diagonal_apply, Equiv.swap_apply_def, eq_comm]

end Torus

end TauCeti

namespace Equiv

open TauCeti

variable {n m : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] {A : Type*} [Ring A]
  {i j : n}

/-- Relabelling the indices sends an elementary matrix to the elementary matrix with the same
parameter at the relabelled pair of indices. -/
theorem reindexGL_transvectionUnit (e : n ≃ m) (hij : i ≠ j) (a : A) :
    e.reindexGL A (transvectionUnit hij a) = transvectionUnit (e.injective.ne hij) a := by
  ext : 1
  simp [coe_transvectionUnit_eq_one_add_single, submatrix_add, submatrix_single_equiv,
    submatrix_one_equiv]

end Equiv

namespace RingHom

open TauCeti

variable {A B n : Type*} [Ring A] [Ring B] [Fintype n] [DecidableEq n]

/-- Applying a ring homomorphism entrywise to a transvection applies it to the coefficient.
This holds for noncommutative rings as well. -/
@[simp]
theorem unitsMap_mapMatrix_transvectionUnit (f : A →+* B) {i j : n} (hij : i ≠ j) (a : A) :
    Units.map (f.mapMatrix (m := n) : Matrix n n A →* Matrix n n B)
      (transvectionUnit hij a) = transvectionUnit hij (f a) := by
  ext r s
  simp [Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all

end RingHom
