/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Data.ZMod.Pow
public import TauCeti.GroupTheory.GroupExtension.DihedralSixteen
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# The `Pin⁺` model of the plane and the lift of `C₂ ≀ C₂` to `D₁₆`

The Clifford algebra of the plane `F²` with the unit form `⟨1, 1⟩` is the matrix algebra `M₂(F)`,
with generators `e₁ = diag(1, −1)` and `e₂ = [[0, 1], [1, 0]]` (`TauCeti.pinE1`, `TauCeti.pinE2`):
they satisfy `e₁² = e₂² = +1` and `e₁ e₂ = −e₂ e₁`, so that the vector `y₀ e₁ + y₁ e₂`
(`TauCeti.pinVec`) squares to `y₀² + y₁²`. An orthogonal matrix `x` acts on these vectors by the
twisted adjoint action `v ↦ det(x) · x v xᵀ`; a **`Pin⁺` lift** of `w` is an orthogonal `x` whose
twisted action is `w` (`TauCeti.IsPinLift`). With the sign, a unit vector lifts its own
reflection (`TauCeti.isPinLift_pinVec`). Lifts multiply, invert and are carried by ring
homomorphisms, such as a Galois action on the entries; an orthogonal `x` lifts exactly one `w`
(`TauCeti.IsPinLift.unique`), and over a domain in which `2 ≠ 0` two lifts of the same `w` differ by
a sign (`TauCeti.IsPinLift.eq_or_eq_neg`). The sign matrix `diag((−1)^{ε₀}, (−1)^{ε₁})` has the
diagonal lift `e₁^{ε₀} e₂^{ε₁}` (`TauCeti.pinDiagonalLift`), whose products carry the sign
`(−1)^{ε₁ ε'₀}` (`TauCeti.pinDiagonalLift_mul`).

The wreath product `C₂ ≀ C₂` acts on `F²` by signed permutations (`TauCeti.wreathSignedPerm`).
For a square root `r2` of `2`, the unit vector `t = (e₁ − e₂)/√2` (`TauCeti.pinT`) lifts the swap,
`e₁ t = r2⁻¹ · [[1, −1], [1, 1]]` has order `8` (over `ℝ` with `r2 = √2 > 0` it is the rotation
by `π/4`), and `r ↦ e₁ t`, `f ↦ t` is a homomorphism
`TauCeti.pinDihedral` from the dihedral group `D₁₆` of order sixteen into `M₂(F)`. It lies over
the quotient map `D₁₆ → C₂ ≀ C₂` (`TauCeti.isPinLift_pinDihedral`), and through the section
`TauCeti.wreathSection` it gives a lift `TauCeti.pinLift` of `C₂ ≀ C₂` whose factor set is the
`D₁₆` extension cocycle `c_{D₁₆}` read as a sign (`TauCeti.pinLift_mul_mul_inv`).

The signs matter. With `e_i² = +1` the lift of `C₂ ≀ C₂` is the dihedral group `D₁₆` of `Pin⁺`
and not the quaternion group `Q₁₆`; this is the convention of Mathlib's `CliffordAlgebra` for the
form `⟨1, 1⟩`, but not that of `CliffordAlgebra.pinGroup`, a vector in which has `Q v = −1`. The
model is therefore stated in explicit matrices. It is the model in which Serre's second proof of
his Théorème 1′ computes the Evens norm of a Kummer class, at `n = 2`.

## Main definitions

* `TauCeti.pinE1`, `TauCeti.pinE2`: the Clifford generators of `M₂(R)`.
* `TauCeti.pinVec`: the vector `y₀ e₁ + y₁ e₂`, as a linear map.
* `TauCeti.IsPinLift`: `x` is a `Pin⁺` lift of `w`.
* `TauCeti.pinDiagonalLift`: the lift `e₁^{ε₀} e₂^{ε₁}` of a diagonal sign matrix.
* `TauCeti.wreathSignedPerm`: the signed-permutation representation
  `(a, b, c) ↦ diag((−1)^a, (−1)^b) · e₂^c` of `C₂ ≀ C₂`.
* `TauCeti.pinT`: the unit vector `(e₁ − e₂)/√2`.
* `TauCeti.pinDihedral`: the homomorphism `D₁₆ → M₂(F)`, `r ↦ e₁ t`, `f ↦ t`.
* `TauCeti.pinLift`: the lift `C₂ ≀ C₂ → M₂(F)` through `TauCeti.wreathSection`.

## Main results

* `TauCeti.pinE1_mul_self`, `TauCeti.pinE2_mul_self`, `TauCeti.pinE1_mul_pinE2`,
  `TauCeti.pinVec_mul_self`: the Clifford relations.
* `TauCeti.isPinLift_pinVec`: a unit vector lifts its own reflection.
* `TauCeti.isPinLift_iff`: a lift is checked on the generators `e₁` and `e₂`.
* `TauCeti.IsPinLift.mul`, `TauCeti.IsPinLift.inv`, `TauCeti.IsPinLift.map`: lifts multiply,
  invert, and are natural in the coefficient ring.
* `TauCeti.IsPinLift.unique`, `TauCeti.IsPinLift.eq_or_eq_neg`: a lift determines what it lifts,
  and two lifts of the same matrix differ by a sign.
* `TauCeti.isPinLift_pinDiagonalLift`, `TauCeti.pinDiagonalLift_mul`: the diagonal lift and its
  factor set `(−1)^{ε₁ ε'₀}`; it is defined over the prime ring (`TauCeti.map_pinDiagonalLift`).
* `TauCeti.pinE1_mul_pinT_pow_four`: `(e₁ t)⁴ = −1`.
* `TauCeti.isPinLift_pinDihedral`: `pinDihedral z` lifts the signed permutation of the image
  of `z` in `C₂ ≀ C₂`.
* `TauCeti.pinLift_mul_pinLift` and `TauCeti.pinLift_mul_mul_inv`: the factor set of `pinLift` is
  `(−1)^{c_{D₁₆}}`.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676: the groups `Pin⁺`, and the second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256: the extension `D₁₆` of `C₂ ≀ C₂`.
-/

public section

namespace TauCeti

open Matrix DihedralGroup WreathC2

section Ring

variable {R : Type*} [Ring R]

/-- **The first Clifford generator** `e₁ = diag(1, −1)` of `M₂(R)`. -/
def pinE1 : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

/-- **The second Clifford generator** `e₂ = [[0, 1], [1, 0]]` of `M₂(R)`, which is also the
permutation matrix of the swap. -/
def pinE2 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- The entries of `e₁`. -/
theorem pinE1_def : (pinE1 : Matrix (Fin 2) (Fin 2) R) = !![1, 0; 0, -1] := (rfl)

/-- The entries of `e₂`. -/
theorem pinE2_def : (pinE2 : Matrix (Fin 2) (Fin 2) R) = !![0, 1; 1, 0] := (rfl)

/-- `e₁² = +1`: with this sign the lift of `C₂ ≀ C₂` is `D₁₆` and not `Q₁₆`. -/
@[simp]
theorem pinE1_mul_self : (pinE1 : Matrix (Fin 2) (Fin 2) R) * pinE1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinE1, Matrix.mul_apply, Fin.sum_univ_two]

/-- `e₂² = +1`. -/
@[simp]
theorem pinE2_mul_self : (pinE2 : Matrix (Fin 2) (Fin 2) R) * pinE2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinE2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `e₁ e₂ = −e₂ e₁`. -/
theorem pinE1_mul_pinE2 : (pinE1 : Matrix (Fin 2) (Fin 2) R) * pinE2 = -(pinE2 * pinE1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinE1, pinE2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugating a diagonal matrix by the swap `e₂` exchanges its two entries. -/
theorem pinE2_mul_diagonal (d : Fin 2 → R) :
    pinE2 * diagonal d = diagonal ![d 1, d 0] * pinE2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinE2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The signed-permutation representation of `C₂ ≀ C₂`,**
`(a, b, c) ↦ diag((−1)^a, (−1)^b) · e₂^c`: the base coordinates are signs and the top coordinate
swaps the two coordinates of `R²`. Its value on coordinates is `TauCeti.wreathSignedPerm_mk`. -/
def wreathSignedPerm : WreathC2 →* Matrix (Fin 2) (Fin 2) R where
  toFun g := diagonal ![(-1) ^ (coordA g).val, (-1) ^ (coordB g).val] * pinE2 ^ (coordC g).val
  map_one' := by
    rw [coordA_one, coordB_one, coordC_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    -- The diagonal sign matrix `diag((−1)^a, (−1)^b)` is multiplicative in `(a, b)`.
    have hdiag (a b a' b' : ZMod 2) :
        diagonal ![(-1 : R) ^ a.val, (-1) ^ b.val] * diagonal ![(-1) ^ a'.val, (-1) ^ b'.val] =
          diagonal ![(-1) ^ (a + a').val, (-1) ^ (b + b').val] := by
      rw [diagonal_mul_diagonal, pow_val_add neg_one_sq, pow_val_add neg_one_sq]
      congr 1
      ext i; fin_cases i <;> rfl
    simp only [coordA_mul, coordB_mul, coordC_mul]
    generalize coordA g = a, coordB g = b, coordC g = c, coordA h = a', coordB h = b',
      coordC h = c'
    have hE2 : (pinE2 : Matrix (Fin 2) (Fin 2) R) ^ 2 = 1 := by rw [pow_two, pinE2_mul_self]
    rw [pow_val_add hE2]
    simp only [← mul_assoc]
    obtain rfl | rfl : c = 0 ∨ c = 1 := by revert c; decide
    · simp only [zero_mul, add_zero, ZMod.val_zero, pow_zero, mul_one, hdiag]
    · have hA : ∀ x y z : ZMod 2, x + y + 1 * (y + z) = x + z := by decide
      have hB : ∀ x y z : ZMod 2, x + y + 1 * (z + y) = x + z := by decide
      rw [mul_assoc (diagonal _) (pinE2 ^ _) (diagonal _), ZMod.val_one, pow_one,
        pinE2_mul_diagonal, ← mul_assoc, hA, hB]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hdiag]

/-- The signed permutation of `g` is `diag((−1)^a, (−1)^b) · e₂^c` on its coordinates. -/
theorem wreathSignedPerm_apply (g : WreathC2) :
    (wreathSignedPerm g : Matrix (Fin 2) (Fin 2) R) =
      diagonal ![(-1) ^ (coordA g).val, (-1) ^ (coordB g).val] * pinE2 ^ (coordC g).val :=
  (rfl)

/-- The signed permutation of `(a, b, c)` is `diag((−1)^a, (−1)^b) · e₂^c`. -/
@[simp]
theorem wreathSignedPerm_mk (a b c : ZMod 2) :
    (wreathSignedPerm (mk a b c) : Matrix (Fin 2) (Fin 2) R) =
      diagonal ![(-1) ^ a.val, (-1) ^ b.val] * pinE2 ^ c.val := by
  rw [wreathSignedPerm_apply, coordA_mk, coordB_mk, coordC_mk]

/-- The swap `s = (0, 0, 1)` acts as the permutation matrix `e₂`. -/
@[simp]
theorem wreathSignedPerm_wreathSwap :
    (wreathSignedPerm wreathSwap : Matrix (Fin 2) (Fin 2) R) = pinE2 := by
  rw [wreathSignedPerm_apply, coordA_wreathSwap, coordB_wreathSwap, coordC_wreathSwap,
    ZMod.val_one, pow_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinE2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The diagonal lift** `e₁^{ε₀} e₂^{ε₁}` of the sign matrix `diag((−1)^{ε₀}, (−1)^{ε₁})`
(`TauCeti.isPinLift_pinDiagonalLift`). -/
def pinDiagonalLift (ε : Fin 2 → ZMod 2) : Matrix (Fin 2) (Fin 2) R :=
  pinE1 ^ (ε 0).val * pinE2 ^ (ε 1).val

/-- The diagonal lift of `ε` is `e₁^{ε₀} e₂^{ε₁}`. -/
theorem pinDiagonalLift_def (ε : Fin 2 → ZMod 2) :
    (pinDiagonalLift ε : Matrix (Fin 2) (Fin 2) R) = pinE1 ^ (ε 0).val * pinE2 ^ (ε 1).val :=
  (rfl)

/-- The diagonal lift of the trivial sign is the identity. -/
@[simp]
theorem pinDiagonalLift_zero : (pinDiagonalLift 0 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp [pinDiagonalLift_def]

/-- **The product of two diagonal lifts,**
`e₁^a e₂^b · e₁^{a'} e₂^{b'} = (−1)^{b a'} e₁^{a + a'} e₂^{b + b'}`: this is where `e₁² = e₂² = +1`
and `e₁ e₂ = −e₂ e₁` enter. -/
@[simp]
theorem pinDiagonalLift_mul (ε ε' : Fin 2 → ZMod 2) :
    (pinDiagonalLift ε : Matrix (Fin 2) (Fin 2) R) * pinDiagonalLift ε' =
      (-1) ^ (ε 1 * ε' 0).val * pinDiagonalLift (ε + ε') := by
  -- Moving `e₂^b` past `e₁^{a'}` costs the sign `(−1)^{b a'}`.
  have hswap (b a : ZMod 2) : (pinE2 : Matrix (Fin 2) (Fin 2) R) ^ b.val * pinE1 ^ a.val =
      (-1) ^ (b * a).val * (pinE1 ^ a.val * pinE2 ^ b.val) := by
    obtain rfl | rfl : b = 0 ∨ b = 1 := by revert b; decide
    · simp
    obtain rfl | rfl : a = 0 ∨ a = 1 := by revert a; decide
    · simp
    · simp [ZMod.val_one_eq_one_mod, pinE1_mul_pinE2]
  have h1 : (pinE1 : Matrix (Fin 2) (Fin 2) R) ^ 2 = 1 := by rw [pow_two, pinE1_mul_self]
  have h2 : (pinE2 : Matrix (Fin 2) (Fin 2) R) ^ 2 = 1 := by rw [pow_two, pinE2_mul_self]
  rw [pinDiagonalLift_def, pinDiagonalLift_def, pinDiagonalLift_def, Pi.add_apply, Pi.add_apply,
    pow_val_add h1, pow_val_add h2, Matrix.mul_assoc, ← Matrix.mul_assoc (pinE2 ^ _), hswap]
  simp only [Matrix.mul_assoc]
  rw [((Commute.neg_one_left _).pow_left _).symm.left_comm]

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- **The vector** `y₀ e₁ + y₁ e₂` of the plane `R²` inside its Clifford model `M₂(R)`. -/
def pinVec : (Fin 2 → R) →ₗ[R] Matrix (Fin 2) (Fin 2) R :=
  (LinearMap.proj 0).smulRight pinE1 + (LinearMap.proj 1).smulRight pinE2

/-- The vector `pinVec y` is `y₀ e₁ + y₁ e₂`. -/
theorem pinVec_apply (y : Fin 2 → R) : pinVec y = y 0 • pinE1 + y 1 • pinE2 := (rfl)

/-- The vector `y₀ e₁ + y₁ e₂` is the symmetric matrix `[[y₀, y₁], [y₁, −y₀]]`. -/
theorem pinVec_eq (y : Fin 2 → R) : pinVec y = !![y 0, y 1; y 1, -y 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinVec_apply, pinE1, pinE2]

/-- A vector of the Clifford model determines its coordinates. -/
theorem pinVec_injective :
    Function.Injective (pinVec : (Fin 2 → R) → Matrix (Fin 2) (Fin 2) R) := by
  intro y z hyz
  have h0 := congrFun (congrFun hyz 0) 0
  have h1 := congrFun (congrFun hyz 0) 1
  simp only [pinVec_eq, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at h0 h1
  ext i; fin_cases i <;> assumption

/-- **The Clifford relation** `v² = q(v) · 1` for the unit form `q(y) = y₀² + y₁²`. -/
@[simp]
theorem pinVec_mul_self (y : Fin 2 → R) : pinVec y * pinVec y = (y ⬝ᵥ y) • 1 := by
  rw [pinVec_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, dotProduct] <;> ring

/-- **The polarized Clifford relation** `u v + v u = 2 ⟨u, v⟩ · 1`. -/
theorem pinVec_mul_add_pinVec_mul (y z : Fin 2 → R) :
    pinVec y * pinVec z + pinVec z * pinVec y = (2 * (y ⬝ᵥ z)) • 1 := by
  rw [pinVec_eq, pinVec_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, dotProduct] <;> ring

/-- The vectors of the Clifford model are symmetric matrices. -/
@[simp]
theorem pinVec_transpose (y : Fin 2 → R) : (pinVec y)ᵀ = pinVec y := by
  rw [pinVec_eq]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The determinant of the vector `y` is `−q(y) = −(y₀² + y₁²)`. -/
@[simp]
theorem det_pinVec (y : Fin 2 → R) : (pinVec y).det = -(y ⬝ᵥ y) := by
  rw [pinVec_eq, det_fin_two_of]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- **`x` is a `Pin⁺` lift of `w`:** `x` is orthogonal and its twisted adjoint action
`v ↦ det(x) · x v xᵀ` on the vectors `TauCeti.pinVec y` is `w`. Over a field an orthogonal
`2 × 2` matrix is even when its determinant is `1` and odd when it is `−1`, so this action is
`v ↦ (−1)^{|x|} x v x⁻¹`; without the sign, `e₁` would act as `diag(1, −1)`, the reflection in
the wrong line.

This is not Mathlib's `CliffordAlgebra.pinGroup`: a vector in that group has `Q v = −1` and
squares to `−1`, which lifts `C₂ ≀ C₂` to the quaternion group `Q₁₆` rather than to `D₁₆`. -/
structure IsPinLift (x w : Matrix (Fin 2) (Fin 2) R) : Prop where
  /-- A `Pin⁺` lift is orthogonal. -/
  mem_orthogonalGroup : x ∈ orthogonalGroup (Fin 2) R
  /-- The twisted adjoint action of a `Pin⁺` lift of `w` on vectors is `w`. -/
  det_smul_mul_pinVec_mul_transpose (y : Fin 2 → R) :
    x.det • (x * pinVec y * xᵀ) = pinVec (w *ᵥ y)

/-- The identity lifts the identity. -/
theorem IsPinLift.one : IsPinLift (1 : Matrix (Fin 2) (Fin 2) R) 1 :=
  ⟨one_mem _, fun y => by simp⟩

/-- Lifts multiply. -/
theorem IsPinLift.mul {x w x' w' : Matrix (Fin 2) (Fin 2) R} (h : IsPinLift x w)
    (h' : IsPinLift x' w') : IsPinLift (x * x') (w * w') := by
  refine ⟨mul_mem h.mem_orthogonalGroup h'.mem_orthogonalGroup, fun y => ?_⟩
  rw [det_mul, ← mulVec_mulVec, ← h.det_smul_mul_pinVec_mul_transpose,
    ← h'.det_smul_mul_pinVec_mul_transpose, transpose_mul, mul_smul, Matrix.mul_smul,
    Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

/-- Lifts are compatible with powers. -/
theorem IsPinLift.pow {x w : Matrix (Fin 2) (Fin 2) R} (h : IsPinLift x w) (n : ℕ) :
    IsPinLift (x ^ n) (w ^ n) := by
  induction n with
  | zero => simpa using IsPinLift.one
  | succ n ih => simpa [pow_succ] using ih.mul h

/-- **A unit vector lifts its own reflection** `v ↦ v − 2 ⟨u, v⟩ u`: the vector `u` squares to
`1`, has determinant `−1`, and `u v u = 2 ⟨u, v⟩ u − v` by the Clifford relation. -/
theorem isPinLift_pinVec {u : Fin 2 → R} (hu : u ⬝ᵥ u = 1) :
    IsPinLift (pinVec u) (1 - (2 : R) • vecMulVec u u) := by
  have hsq : pinVec u * pinVec u = 1 := by rw [pinVec_mul_self, hu, one_smul]
  refine ⟨(mem_orthogonalGroup_iff' _ _).2 (by rw [pinVec_transpose, hsq]), fun y => ?_⟩
  have hconj : pinVec u * pinVec y * pinVec u = (2 * (u ⬝ᵥ y)) • pinVec u - pinVec y := by
    calc pinVec u * pinVec y * pinVec u
        = (pinVec u * pinVec y + pinVec y * pinVec u) * pinVec u -
            pinVec y * (pinVec u * pinVec u) := by noncomm_ring
      _ = (2 * (u ⬝ᵥ y)) • pinVec u - pinVec y := by
        rw [pinVec_mul_add_pinVec_mul, hsq, smul_one_mul, mul_one]
  rw [det_pinVec, hu, pinVec_transpose, hconj, sub_mulVec, one_mulVec, smul_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, smul_smul, map_sub, map_smul]
  module

/-- **`e₁` lifts `diag(−1, 1)`,** the reflection in the second coordinate axis. -/
theorem isPinLift_pinE1 : IsPinLift (pinE1 : Matrix (Fin 2) (Fin 2) R) (diagonal ![-1, 1]) := by
  have h := isPinLift_pinVec (R := R) (u := ![1, 0]) (by simp)
  have hv : pinVec ![(1 : R), 0] = pinE1 := by simp [pinVec_apply]
  have hw : 1 - (2 : R) • vecMulVec ![(1 : R), 0] ![1, 0] = diagonal ![-1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [vecMulVec_apply, Matrix.one_apply]
  rwa [hv, hw] at h

/-- **`e₂` lifts `diag(1, −1)`,** the reflection in the first coordinate axis. -/
theorem isPinLift_pinE2 : IsPinLift (pinE2 : Matrix (Fin 2) (Fin 2) R) (diagonal ![1, -1]) := by
  have h := isPinLift_pinVec (R := R) (u := ![0, 1]) (by simp)
  have hv : pinVec ![(0 : R), 1] = pinE2 := by simp [pinVec_apply]
  have hw : 1 - (2 : R) • vecMulVec ![(0 : R), 1] ![0, 1] = diagonal ![1, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [vecMulVec_apply, Matrix.one_apply]
  rwa [hv, hw] at h

/-- **The diagonal lift** `e₁^{ε₀} e₂^{ε₁}` lifts `diag((−1)^{ε₀}, (−1)^{ε₁})`, since `e₁` lifts
`diag(−1, 1)` and `e₂` lifts `diag(1, −1)`. -/
theorem isPinLift_pinDiagonalLift (ε : Fin 2 → ZMod 2) :
    IsPinLift (pinDiagonalLift ε : Matrix (Fin 2) (Fin 2) R)
      (diagonal fun i => (-1) ^ (ε i).val) := by
  have h := (isPinLift_pinE1 (R := R).pow (ε 0).val).mul (isPinLift_pinE2.pow (ε 1).val)
  rw [diagonal_pow, diagonal_pow, diagonal_mul_diagonal, ← pinDiagonalLift_def] at h
  convert h using 2
  ext i; fin_cases i <;> simp

/-- **A `Pin⁺` lift is checked on the two generators:** `x` lifts `w` if and only if `x` is
orthogonal and its twisted action sends `e₁` and `e₂` to the vectors of the two columns of `w`. -/
theorem isPinLift_iff {x w : Matrix (Fin 2) (Fin 2) R} :
    IsPinLift x w ↔ x ∈ orthogonalGroup (Fin 2) R ∧
      x.det • (x * pinE1 * xᵀ) = pinVec (wᵀ 0) ∧ x.det • (x * pinE2 * xᵀ) = pinVec (wᵀ 1) := by
  refine ⟨fun h => ⟨h.mem_orthogonalGroup, ?_, ?_⟩, fun ⟨hx, h1, h2⟩ => ⟨hx, fun y => ?_⟩⟩
  · simpa [pinVec_apply, mulVec_single_one] using
      h.det_smul_mul_pinVec_mul_transpose (Pi.single 0 1)
  · simpa [pinVec_apply, mulVec_single_one] using
      h.det_smul_mul_pinVec_mul_transpose (Pi.single 1 1)
  · have hy : w *ᵥ y = y 0 • wᵀ 0 + y 1 • wᵀ 1 := by
      ext i; simp [mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
    rw [hy, map_add, map_smul, map_smul, ← h1, ← h2, pinVec_apply]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
    rw [smul_comm x.det (y 0), smul_comm x.det (y 1)]

/-- **The target of a `Pin⁺` lift is unique:** an orthogonal `x` has only one twisted action. -/
theorem IsPinLift.unique {x w w' : Matrix (Fin 2) (Fin 2) R} (h : IsPinLift x w)
    (h' : IsPinLift x w') : w = w' := by
  rw [isPinLift_iff] at h h'
  have c0 := pinVec_injective (h.2.1.symm.trans h'.2.1)
  have c1 := pinVec_injective (h.2.2.symm.trans h'.2.2)
  rw [← transpose_transpose w, ← transpose_transpose w']
  congr 1
  ext i j; fin_cases i
  · exact congrFun c0 j
  · exact congrFun c1 j

/-- A symmetric matrix of trace zero is a vector of the Clifford model. -/
private theorem pinVec_of_transpose_eq_of_trace_eq_zero {M : Matrix (Fin 2) (Fin 2) R}
    (hM : Mᵀ = M) (htr : M.trace = 0) : pinVec ![M 0 0, M 0 1] = M := by
  have h10 : M 1 0 = M 0 1 := by simpa using congrFun (congrFun hM 0) 1
  have h11 : M 1 1 = -M 0 0 := by
    rw [trace_fin_two] at htr
    linear_combination htr
  rw [pinVec_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [h10, h11]

/-- **Every orthogonal matrix is a `Pin⁺` lift of something:** its twisted action preserves the
vectors, which are the symmetric matrices of trace zero. -/
private theorem exists_isPinLift_of_mem_orthogonalGroup {x : Matrix (Fin 2) (Fin 2) R}
    (hx : x ∈ orthogonalGroup (Fin 2) R) : ∃ w, IsPinLift x w := by
  have hxx : xᵀ * x = 1 := (mem_orthogonalGroup_iff' _ _).1 hx
  -- The twisted action of `x` on a vector `v` is symmetric of trace zero.
  have hvec (v : Matrix (Fin 2) (Fin 2) R) (hv : vᵀ = v) (htr : v.trace = 0) :
      ∃ y, x.det • (x * v * xᵀ) = pinVec y := by
    refine ⟨_, (pinVec_of_transpose_eq_of_trace_eq_zero ?_ ?_).symm⟩
    · rw [transpose_smul, transpose_mul, transpose_mul, transpose_transpose, hv, Matrix.mul_assoc]
    · rw [trace_smul, trace_mul_comm, ← Matrix.mul_assoc, hxx, Matrix.one_mul, htr, smul_zero]
  obtain ⟨y₁, hy₁⟩ := hvec pinE1 (by rw [pinE1_def]; ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simp [pinE1_def, trace_fin_two])
  obtain ⟨y₂, hy₂⟩ := hvec pinE2 (by rw [pinE2_def]; ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simp [pinE2_def, trace_fin_two])
  refine ⟨(of ![y₁, y₂])ᵀ, isPinLift_iff.2 ⟨hx, ?_, ?_⟩⟩ <;>
    simpa only [transpose_transpose, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one]

/-- **Lifts invert:** the inverse `x⁻¹ = xᵀ` of a lift of `w` lifts `w⁻¹`. -/
theorem IsPinLift.inv {x w : Matrix (Fin 2) (Fin 2) R} (h : IsPinLift x w) :
    IsPinLift x⁻¹ w⁻¹ := by
  have hxx : x * xᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 h.mem_orthogonalGroup
  obtain ⟨w', h'⟩ :=
    exists_isPinLift_of_mem_orthogonalGroup ((mem_orthogonalGroup_iff' _ _).2 (by
      rwa [transpose_transpose]))
  have hww : w * w' = 1 := (h.mul h').unique (by rw [hxx]; exact IsPinLift.one)
  rwa [inv_eq_right_inv hxx, inv_eq_right_inv hww]

variable {S : Type*} [CommRing S]

/-- The generator `e₁` is defined over the prime ring. -/
@[simp]
theorem map_pinE1 (φ : R →+* S) : (pinE1 : Matrix (Fin 2) (Fin 2) R).map φ = pinE1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinE1]

/-- The generator `e₂` is defined over the prime ring. -/
@[simp]
theorem map_pinE2 (φ : R →+* S) : (pinE2 : Matrix (Fin 2) (Fin 2) R).map φ = pinE2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinE2]

/-- The diagonal lift is defined over the prime ring. -/
@[simp]
theorem map_pinDiagonalLift (φ : R →+* S) (ε : Fin 2 → ZMod 2) :
    (pinDiagonalLift ε : Matrix (Fin 2) (Fin 2) R).map φ = pinDiagonalLift ε := by
  rw [pinDiagonalLift_def, pinDiagonalLift_def, ← RingHom.mapMatrix_apply, map_mul, map_pow,
    map_pow, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_pinE1, map_pinE2]

/-- The vector `y₀ e₁ + y₁ e₂` is natural in the coefficient ring. -/
@[simp]
theorem map_pinVec (φ : R →+* S) (y : Fin 2 → R) : (pinVec y).map φ = pinVec (φ ∘ y) := by
  rw [pinVec_eq, pinVec_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **Lifts are carried by ring homomorphisms,** in particular by a Galois action on the entries. -/
theorem IsPinLift.map (φ : R →+* S) {x w : Matrix (Fin 2) (Fin 2) R} (h : IsPinLift x w) :
    IsPinLift (x.map φ) (w.map φ) := by
  obtain ⟨hx, h1, h2⟩ := isPinLift_iff.1 h
  refine isPinLift_iff.2 ⟨?_, ?_, ?_⟩
  · rw [mem_orthogonalGroup_iff'] at hx ⊢
    rw [← transpose_map, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, hx,
      map_one]
  · have h := congrArg (·.map φ) h1
    simp only [Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_mul, map_pinE1, map_pinVec,
      transpose_map, RingHom.map_det, RingHom.mapMatrix_apply] at h
    convert h using 2
    ext i; simp
  · have h := congrArg (·.map φ) h2
    simp only [Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_mul, map_pinE2, map_pinVec,
      transpose_map, RingHom.map_det, RingHom.mapMatrix_apply] at h
    convert h using 2
    ext i; simp

end CommRing

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R] [NeZero (2 : R)]

/-- The `Pin⁺` lifts of the identity are `±1`: of determinant `1` such a lift commutes with `e₁` and
`e₂` and is a scalar, and of determinant `−1` it would anticommute with both, which no orthogonal
matrix does when `2 ≠ 0`. -/
private theorem eq_one_or_eq_neg_one_of_isPinLift_one {z : Matrix (Fin 2) (Fin 2) R}
    (h : IsPinLift z 1) : z = 1 ∨ z = -1 := by
  obtain ⟨hz, h1, h2⟩ := isPinLift_iff.1 h
  have hzz := (mem_orthogonalGroup_iff' _ _).1 hz
  have hzz' := (mem_orthogonalGroup_iff _ _).1 hz
  rw [eta_fin_two z] at h1 h2 hzz hzz' ⊢
  set a := z 0 0
  set b := z 0 1
  set c := z 1 0
  set d := z 1 1
  -- The entries of the two generator equations and of orthogonality.
  have e1 : (a * d - b * c) * (a * a - b * b) = 1 := by
    have := congrFun (congrFun h1 0) 0
    simp [pinE1, pinVec_eq, det_fin_two, vecMul, dotProduct, Fin.sum_univ_two] at this
    linear_combination this
  have e2 : (a * d - b * c) * (2 * (a * b)) = 0 := by
    have := congrFun (congrFun h2 0) 0
    simp [pinE2, pinVec_eq, det_fin_two, vecMul, dotProduct, Fin.sum_univ_two, -mul_eq_zero]
      at this
    linear_combination this
  have e3 : (a * d - b * c) * (a * d + b * c) = 1 := by
    have := congrFun (congrFun h2 0) 1
    simp [pinE2, pinVec_eq, det_fin_two, vecMul, dotProduct, Fin.sum_univ_two] at this
    linear_combination this
  have o1 : a * a + c * c = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hzz 0) 0
  have o2 : a * a + b * b = 1 := by
    simpa [vecMul, dotProduct, Fin.sum_univ_two] using congrFun (congrFun hzz' 0) 0
  have o3 : a * c + b * d = 0 := by
    simpa [vecMul, dotProduct, Fin.sum_univ_two, -mul_eq_zero] using congrFun (congrFun hzz' 0) 1
  have o4 : b * b + d * d = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hzz 1) 1
  have o5 : a * b + c * d = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_zero] using congrFun (congrFun hzz 0) 1
  -- The determinant `δ = a d − b c` squares to one, and `δ (a d + b c) = 1`, so `b c = 0`.
  have hδ : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (b * b + d * d) * o1 + o4 - (a * b + c * d) * o5
  have hδ0 : a * d - b * c ≠ 0 := left_ne_zero_of_mul_eq_one hδ
  have h20 : (2 : R) ≠ 0 := two_ne_zero
  have hbc : b * c = 0 := by
    have : (a * d - b * c) * (2 * (b * c)) = 0 := by linear_combination e3 - hδ
    simpa [hδ0, h20] using this
  have hab : a * b = 0 := by simpa [hδ0, h20] using e2
  have ha : a ≠ 0 := by
    rintro ha
    exact hδ0 (by rw [ha, zero_mul, zero_sub, hbc, neg_zero])
  have hb : b = 0 := (mul_eq_zero.1 hab).resolve_left ha
  have hc : c = 0 := by
    rw [hb, zero_mul, add_zero] at o3
    exact (mul_eq_zero.1 o3).resolve_left ha
  rw [hb, mul_zero, add_zero] at o2
  have had : a * d = 1 := by
    rw [hb, zero_mul, sub_zero, mul_zero, sub_zero, o2, mul_one] at e1
    exact e1
  have hd : d = a := by linear_combination (-d) * o2 + a * had
  rw [hb, hc, hd]
  rcases mul_self_eq_one_iff.1 o2 with ha1 | ha1 <;> rw [ha1]
  · exact Or.inl (one_fin_two (α := R)).symm
  · exact Or.inr (by ext i j; fin_cases i <;> fin_cases j <;> simp)

/-- **Two `Pin⁺` lifts of the same `w` differ by a sign:** `x' x⁻¹` lifts the identity, hence is
`±1`. -/
theorem IsPinLift.eq_or_eq_neg {x x' w : Matrix (Fin 2) (Fin 2) R} (h : IsPinLift x w)
    (h' : IsPinLift x' w) : x' = x ∨ x' = -x := by
  have hdet : IsUnit x.det :=
    isUnit_det_of_right_inverse ((mem_orthogonalGroup_iff _ _).1 h.mem_orthogonalGroup)
  have hw : w * w⁻¹ = 1 :=
    (h.mul h.inv).unique (by rw [mul_nonsing_inv _ hdet]; exact IsPinLift.one)
  have hz := h'.mul h.inv
  rw [hw] at hz
  have hx' : x' = x' * x⁻¹ * x := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]
  rcases eq_one_or_eq_neg_one_of_isPinLift_one hz with hz | hz <;> rw [hx', hz]
  · exact Or.inl (Matrix.one_mul x)
  · exact Or.inr (neg_one_mul x)

end IsDomain

section Field

variable {F : Type*} [Field F] [NeZero (2 : F)] {r2 : F}

/-- **The unit vector `t = (e₁ − e₂)/√2`** of the Clifford model, for a square root `r2` of `2`.
Its reflection is the swap of the two coordinates (`TauCeti.isPinLift_pinT`). -/
noncomputable def pinT (r2 : F) : Matrix (Fin 2) (Fin 2) F := pinVec ![r2⁻¹, -r2⁻¹]

omit [NeZero (2 : F)] in
/-- `t = r2⁻¹ (e₁ − e₂)`. -/
theorem pinT_def (r2 : F) : pinT r2 = r2⁻¹ • (pinE1 - pinE2) := by
  simp [pinT, pinVec_apply, sub_eq_add_neg]

/-- `(r2⁻¹, −r2⁻¹)` is a unit vector. -/
private theorem dotProduct_pinTVec (hr2 : r2 ^ 2 = 2) :
    ![r2⁻¹, -r2⁻¹] ⬝ᵥ ![r2⁻¹, -r2⁻¹] = 1 := by
  have hr : r2 ≠ 0 := ne_zero_pow two_ne_zero (hr2 ▸ two_ne_zero)
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  linear_combination -hr2

/-- `t² = +1`. -/
@[simp]
theorem pinT_mul_self (hr2 : r2 ^ 2 = 2) : pinT r2 * pinT r2 = 1 := by
  rw [pinT, pinVec_mul_self, dotProduct_pinTVec hr2, one_smul]

/-- **`t` lifts the swap** `e₂`, its reflection. -/
theorem isPinLift_pinT (hr2 : r2 ^ 2 = 2) : IsPinLift (pinT r2) pinE2 := by
  have h := isPinLift_pinVec (dotProduct_pinTVec hr2)
  have hr : r2 ≠ 0 := ne_zero_pow two_ne_zero (hr2 ▸ two_ne_zero)
  have hw : 1 - (2 : F) • vecMulVec ![r2⁻¹, -r2⁻¹] ![r2⁻¹, -r2⁻¹] = pinE2 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [pinE2] <;> field_simp <;>
      first | linear_combination hr2 | linear_combination -hr2
  rwa [hw] at h

/-- **`(e₁ t)⁴ = −1`,** since `e₁ t = r2⁻¹ · [[1, −1], [1, 1]]` squares to `[[0, −1], [1, 0]]`.
So `e₁ t` has order `8`, the characteristic not being two; over `ℝ` with `r2 = √2 > 0` it is the
rotation by `π/4`. -/
theorem pinE1_mul_pinT_pow_four (hr2 : r2 ^ 2 = 2) : (pinE1 * pinT r2) ^ 4 = -1 := by
  have hr : r2 ≠ 0 := ne_zero_pow two_ne_zero (hr2 ▸ two_ne_zero)
  have hsq : (pinE1 * pinT r2) ^ 2 = !![0, -1; 1, 0] := by
    rw [pinT_def]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [pow_two, pinE1, pinE2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
      first | linear_combination hr2 | linear_combination -hr2
  calc (pinE1 * pinT r2) ^ 4 = ((pinE1 * pinT r2) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = -1 := by
      rw [hsq]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The second involution `t e₁ t` of the dihedral presentation. -/
private theorem pinT_mul_pinE1_mul_pinT_mul_self (hr2 : r2 ^ 2 = 2) :
    pinT r2 * pinE1 * pinT r2 * (pinT r2 * pinE1 * pinT r2) = 1 := by
  simp only [← mul_assoc]
  rw [mul_assoc _ (pinT r2) (pinT r2), pinT_mul_self hr2, mul_one, mul_assoc _ pinE1 pinE1,
    pinE1_mul_self, mul_one, pinT_mul_self hr2]

/-- The product of the two involutions `t` and `t e₁ t` is `e₁ t`. -/
private theorem pinT_mul_pinT_mul_pinE1_mul_pinT (hr2 : r2 ^ 2 = 2) :
    pinT r2 * (pinT r2 * pinE1 * pinT r2) = pinE1 * pinT r2 := by
  rw [← mul_assoc, ← mul_assoc, pinT_mul_self hr2, one_mul]

/-- **The dihedral group `D₁₆` in `M₂(F)`,** on Mathlib's `DihedralGroup 8`: `r ↦ e₁ t`, of
order `8` (the rotation by `π/4` over `ℝ` with `r2 = √2 > 0`), and `f = sr 0 ↦ t`, so that
`r i ↦ (e₁ t)^i` and `sr i ↦ t (e₁ t)^i` (`TauCeti.pinDihedral_r`, `TauCeti.pinDihedral_sr`).
It is `TauCeti.dihedralHom` at the two involutions `t` and `t e₁ t`, whose product `e₁ t`
satisfies `(e₁ t)⁸ = 1` by `TauCeti.pinE1_mul_pinT_pow_four`. -/
noncomputable def pinDihedral (hr2 : r2 ^ 2 = 2) : DihedralGroup 8 →* Matrix (Fin 2) (Fin 2) F :=
  dihedralHom (pinT_mul_self hr2) (pinT_mul_pinE1_mul_pinT_mul_self hr2) (by
    rw [pinT_mul_pinT_mul_pinE1_mul_pinT hr2, ← neg_one_sq, ← pinE1_mul_pinT_pow_four hr2,
      ← pow_mul])

/-- The rotation `r i` maps to `(e₁ t)^i`. -/
@[simp]
theorem pinDihedral_r (hr2 : r2 ^ 2 = 2) (i : ZMod 8) :
    pinDihedral hr2 (r i) = (pinE1 * pinT r2) ^ i.val := by
  simp only [pinDihedral, dihedralHom_r_units, ZMod.cast_eq_val, zpow_natCast,
    Units.val_pow_eq_pow_val, Units.val_mul, pinT_mul_pinT_mul_pinE1_mul_pinT hr2]

/-- The reflection `sr i` maps to `t (e₁ t)^i`. -/
@[simp]
theorem pinDihedral_sr (hr2 : r2 ^ 2 = 2) (i : ZMod 8) :
    pinDihedral hr2 (sr i) = pinT r2 * (pinE1 * pinT r2) ^ i.val := by
  rw [← pinDihedral_r hr2 i, pinDihedral, dihedralHom_sr_units, dihedralHom_r_units]

/-- The central element `r⁴` of `D₁₆` maps to `−1`. -/
theorem pinDihedral_r_four (hr2 : r2 ^ 2 = 2) : pinDihedral hr2 (r 4) = -1 := by
  rw [pinDihedral_r, ZMod.val_ofNat_of_lt (by norm_num), pinE1_mul_pinT_pow_four hr2]

/-- **`D₁₆` lies over `C₂ ≀ C₂`:** `pinDihedral z` is a `Pin⁺` lift of the signed permutation of
the image of `z` under `TauCeti.dihedralToWreath`. -/
theorem isPinLift_pinDihedral (hr2 : r2 ^ 2 = 2) (z : DihedralGroup 8) :
    IsPinLift (pinDihedral hr2 z) (wreathSignedPerm (dihedralToWreath z)) := by
  -- On the generators: `e₁ t` lifts `diag(−1, 1) · e₂` and `t` lifts `e₂`.
  have hr : IsPinLift (pinDihedral hr2 (r 1)) (wreathSignedPerm (dihedralToWreath (r 1))) := by
    rw [pinDihedral_r, dihedralToWreath_r_one, wreathSignedPerm_mk]
    simpa [ZMod.val_one_eq_one_mod] using isPinLift_pinE1.mul (isPinLift_pinT hr2)
  have hs : IsPinLift (pinDihedral hr2 (sr 0)) (wreathSignedPerm (dihedralToWreath (sr 0))) := by
    rw [pinDihedral_sr, dihedralToWreath_sr_zero, wreathSignedPerm_wreathSwap]
    simpa using isPinLift_pinT hr2
  have hpow (k : ℕ) :
      IsPinLift (pinDihedral hr2 (r k)) (wreathSignedPerm (dihedralToWreath (r k))) := by
    rw [← r_one_pow, map_pow, map_pow, map_pow]
    exact hr.pow k
  rcases z with i | i
  · simpa using hpow i.val
  · rw [← zero_add i, ← sr_mul_r, map_mul, map_mul, map_mul]
    exact hs.mul (by simpa using hpow i.val)

/-- **The lift of `C₂ ≀ C₂` into `D₁₆`** through the section `TauCeti.wreathSection`,
`(u s)ⁱ sʲ ↦ (e₁ t)ⁱ tʲ`. It lifts the signed permutations (`TauCeti.isPinLift_pinLift`), and its
factor set is `(−1)^{c_{D₁₆}}` (`TauCeti.pinLift_mul_mul_inv`). -/
noncomputable def pinLift (hr2 : r2 ^ 2 = 2) (g : WreathC2) : Matrix (Fin 2) (Fin 2) F :=
  pinDihedral hr2 (wreathSection g)

/-- `pinLift g` is the image under `TauCeti.pinDihedral` of the section value `wreathSection g`. -/
theorem pinLift_def (hr2 : r2 ^ 2 = 2) (g : WreathC2) :
    pinLift hr2 g = pinDihedral hr2 (wreathSection g) :=
  (rfl)

/-- The lift is normalized. -/
@[simp]
theorem pinLift_one (hr2 : r2 ^ 2 = 2) : pinLift hr2 1 = 1 := by
  rw [pinLift_def, wreathSection_one, map_one]

/-- `pinLift g` is a `Pin⁺` lift of the signed permutation of `g`. -/
theorem isPinLift_pinLift (hr2 : r2 ^ 2 = 2) (g : WreathC2) :
    IsPinLift (pinLift hr2 g) (wreathSignedPerm g) := by
  rw [pinLift_def]
  simpa using isPinLift_pinDihedral hr2 (wreathSection g)

/-- **`pinLift` is multiplicative up to the sign `(−1)^{c_{D₁₆}}`:**
`pinLift g · pinLift h = (−1)^{c_{D₁₆}(g, h)} · pinLift (g h)`, the image of
`TauCeti.wreathSection_mul_wreathSection` under `TauCeti.pinDihedral`, which sends `r⁴` to `−1`. -/
theorem pinLift_mul_pinLift (hr2 : r2 ^ 2 = 2) (g h : WreathC2) :
    pinLift hr2 g * pinLift hr2 h = (-1) ^ (wreathD16Cocycle (g, h)).val * pinLift hr2 (g * h) := by
  rw [pinLift_def, pinLift_def, pinLift_def, ← map_mul, wreathSection_mul_wreathSection, map_mul]
  congr 1
  obtain h0 | h1 : wreathD16Cocycle (g, h) = 0 ∨ wreathD16Cocycle (g, h) = 1 := by
    generalize wreathD16Cocycle (g, h) = c
    revert c
    decide
  · rw [h0, ZMod.val_zero, Nat.cast_zero, mul_zero, ← one_def, map_one, pow_zero]
  · rw [h1, ZMod.val_one, Nat.cast_one, mul_one, pow_one, pinDihedral_r_four]

/-- **The factor set of `pinLift` is `c_{D₁₆}`,** the `D₁₆` extension cocycle
`TauCeti.wreathD16Cocycle` read as a sign:
`pinLift g · pinLift h · pinLift (g h)⁻¹ = (−1)^{c_{D₁₆}(g, h)}`. -/
theorem pinLift_mul_mul_inv (hr2 : r2 ^ 2 = 2) (g h : WreathC2) :
    pinLift hr2 g * pinLift hr2 h * (pinLift hr2 (g * h))⁻¹ =
      (-1) ^ (wreathD16Cocycle (g, h)).val := by
  have hu : IsUnit (pinLift hr2 (g * h)).det :=
    (isUnit_iff_isUnit_det _).1 ((Group.isUnit _).map (pinDihedral hr2))
  rw [pinLift_mul_pinLift, mul_assoc, mul_nonsing_inv _ hu, mul_one]

end Field

end TauCeti
