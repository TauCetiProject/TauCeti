/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

/-!
# Twisted boundaries of matrix-valued Galois cochains

For a matrix-valued one-cochain `x` of the absolute Galois group, its twisted boundary is

`δx(g, h) = x(g) · g(x(h)) · x(gh)⁻¹`.

This is the nonabelian boundary used to compare lifts of orthogonal Galois cocycles.  Changing a
cochain by the Galois-twisted conjugation `x(g) ↦ Q⁻¹ x(g) g(Q)` conjugates its boundary by the
constant matrix `Q`.  In particular, a scalar boundary is unchanged.  The mod-two reading
`twistedBoundaryF2` records whether the boundary is the identity; when `K` has characteristic
different from two, `n` is nonempty, and the boundary is a sign matrix `±1`, this is its exponent.

The convention for the order of the Galois action is important: applying `h` to the entries and
then `g` is the action of `g * h`.  This is the convention of `Gal(SeparableClosure K / K)` and is
the one needed for the descent cocycles of transferred quadratic forms.

## Main definitions

* `TauCeti.twistedBoundary`: the matrix-valued twisted boundary.
* `TauCeti.twistedBoundaryF2`: its mod-two reading, the exponent of a sign boundary away from
  characteristic two when `n` is nonempty.

## Main results

* `TauCeti.twistedBoundary_conj`: twisted conjugation conjugates the boundary by the constant
  matrix.
* `TauCeti.twistedBoundary_conj_of_eq_scalar`: a scalar boundary is invariant under twisted
  conjugation.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

namespace TauCeti

open Matrix

universe u

variable {K : Type u} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The twisted boundary of a matrix-valued one-cochain of the absolute Galois group:
`δx(g, h) = x(g) · g(x(h)) · x(gh)⁻¹`. -/
def twistedBoundary
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) :
    Matrix n n (SeparableClosure K) :=
  x q.1 * (x q.2).map q.1 * (x (q.1 * q.2))⁻¹

/-- The defining equation for the twisted boundary. -/
theorem twistedBoundary_apply
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (g h : AbsoluteGaloisGroup K) :
    twistedBoundary x (g, h) = x g * (x h).map g * (x (g * h))⁻¹ :=
  (rfl)

/-- The twisted boundary of the constant identity cochain is the identity matrix. -/
@[simp]
theorem twistedBoundary_one (g h : AbsoluteGaloisGroup K) :
    twistedBoundary (fun _ ↦ (1 : Matrix n n (SeparableClosure K))) (g, h) = 1 := by
  simp [twistedBoundary]

/-- The twisted boundary is the identity exactly when the cochain satisfies the multiplicative
one-cocycle equation at `(g, h)`. -/
theorem twistedBoundary_eq_one_iff
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (g h : AbsoluteGaloisGroup K) (hx : IsUnit (x (g * h)).det) :
    twistedBoundary x (g, h) = 1 ↔ x g * (x h).map g = x (g * h) := by
  constructor
  · intro hδ
    have h := congrArg (· * x (g * h)) hδ
    simpa only [twistedBoundary_apply, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hx,
      Matrix.mul_one, Matrix.one_mul] using h
  · intro hδ
    rw [twistedBoundary_apply, hδ, Matrix.mul_nonsing_inv _ hx]

/-- The twisted boundary read in `𝔽₂`: it is `0` at the identity and `1` elsewhere.  When `K`
has characteristic different from two, `n` is nonempty, and the boundary is a sign matrix `±1`,
this is precisely its exponent. -/
noncomputable def twistedBoundaryF2
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) : ZMod 2 := by
  classical
  exact if twistedBoundary x q = 1 then 0 else 1

/-- The mod-two twisted boundary vanishes exactly when the matrix boundary is the identity. -/
@[simp]
theorem twistedBoundaryF2_eq_zero_iff
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) :
    twistedBoundaryF2 x q = 0 ↔ twistedBoundary x q = 1 := by
  classical
  simp [twistedBoundaryF2]

/-- The mod-two twisted boundary is `1` exactly when the matrix boundary is not the identity. -/
@[simp]
theorem twistedBoundaryF2_eq_one_iff
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) :
    twistedBoundaryF2 x q = 1 ↔ twistedBoundary x q ≠ 1 := by
  classical
  simp [twistedBoundaryF2]

/-- For a sign boundary, the mod-two twisted boundary recovers its exponent. -/
theorem twistedBoundaryF2_eq_of_eq_sign
    [Nonempty n] [NeZero (2 : K)]
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) (e : ZMod 2)
    (hx : twistedBoundary x q =
      (-1 : SeparableClosure K) ^ e.val • (1 : Matrix n n (SeparableClosure K))) :
    twistedBoundaryF2 x q = e := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) e with rfl | rfl
  · exact (twistedBoundaryF2_eq_zero_iff x q).2 (by simpa using hx)
  · apply (twistedBoundaryF2_eq_one_iff x q).2
    intro hδ
    have hmatrix :
        (-1 : SeparableClosure K) ^ (1 : ZMod 2).val •
            (1 : Matrix n n (SeparableClosure K)) = 1 :=
      hx.symm.trans hδ
    let i : n := Classical.choice inferInstance
    have hi := congrFun (congrFun hmatrix i) i
    have hneg : (-1 : SeparableClosure K) = 1 := by
      simpa only [ZMod.val_one, pow_one, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one] using hi
    have htwo : (2 : SeparableClosure K) ≠ 0 :=
      (map_ne_zero (algebraMap K (SeparableClosure K))).2 two_ne_zero
    apply htwo
    have hadd := congrArg (· + (1 : SeparableClosure K)) hneg
    simpa only [neg_add_cancel, one_add_one_eq_two] using hadd.symm

/-- Twisted conjugation of a cochain conjugates its boundary by the constant matrix. -/
theorem twistedBoundary_conj
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (Q : Matrix n n (SeparableClosure K)) (hQ : IsUnit Q.det)
    (g h : AbsoluteGaloisGroup K) :
    twistedBoundary (fun j ↦ Q⁻¹ * x j * Q.map j) (g, h) =
      Q⁻¹ * twistedBoundary x (g, h) * Q := by
  have hmap_inv (j : AbsoluteGaloisGroup K) : (Q⁻¹).map j = (Q.map j)⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    have hj := congrArg (fun A => A.map j) (Matrix.mul_nonsing_inv Q hQ)
    simpa only [Matrix.map_mul, map_mul, Matrix.map_one, map_zero, map_one] using hj
  have hmap_mul : (Q.map h).map g = Q.map (g * h) := by
    ext i j
    simp only [Matrix.map_apply]
    exact congrArg Subtype.val (AlgEquiv.mul_apply g h (Q i j)).symm
  rw [twistedBoundary_apply, twistedBoundary_apply, Matrix.map_mul, Matrix.map_mul,
    hmap_inv, hmap_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv Q hQ]
  have hQg : IsUnit (Q.map g).det := by
    have hdet : g Q.det = (Q.map g).det := by
      rw [AlgEquiv.map_det]
      congr 1
    rw [← hdet]
    exact hQ.map g
  have hQgh : IsUnit (Q.map (g * h)).det := by
    have hdet : (g * h) Q.det = (Q.map (g * h)).det := by
      rw [AlgEquiv.map_det]
      congr 1
    rw [← hdet]
    exact hQ.map (g * h)
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hQg,
    Matrix.mul_nonsing_inv_cancel_left _ _ hQgh]

/-- A scalar twisted boundary is unchanged by twisted conjugation. -/
theorem twistedBoundary_conj_of_eq_scalar
    (x : AbsoluteGaloisGroup K → Matrix n n (SeparableClosure K))
    (Q : Matrix n n (SeparableClosure K)) (hQ : IsUnit Q.det)
    (g h : AbsoluteGaloisGroup K) (a : SeparableClosure K)
    (hx : twistedBoundary x (g, h) = a • 1) :
    twistedBoundary (fun j ↦ Q⁻¹ * x j * Q.map j) (g, h) = a • 1 := by
  rw [twistedBoundary_conj x Q hQ g h, hx, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.nonsing_inv_mul Q hQ]

end TauCeti
