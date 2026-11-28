/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.LinearAlgebra.Matrix.Charpoly.Amitsur

/-!
# Characteristic coefficients of families of matrix representations

Let `O` be a commutative ring, `L` a commutative `O`-algebra, `J` and `Y` types, and
`u_x : G →* M_σ(L)` (`x ∈ Y`) a family of matrix representations of a monoid `G` over `L`. Let `S`
be an `O`-subalgebra of the families `Y → L[X_j]` of polynomials over `L` in variables `X_j`
(`j ∈ J`). If `S` contains the families of the coefficients of the characteristic polynomials of
the `u_x(g)`, read as constant polynomials, then it contains those of the images `u_x(w)` of every
element `w` of the monoid algebra `O[G]` (`TauCeti.C_charpoly_coeff_lift_mem`), and in particular
the families of the determinants `x ↦ det (∑_g θ_g (u_x(g) - 1))`
(`TauCeti.C_det_linearCombination_sub_one_mem`).

The proof applies Amitsur's theorem for the image of a monoid algebra
(`TauCeti.charpoly_coeff_lift_mem`) to the family of the `u_x` as one representation by matrices
over the product ring `Y → L[X_j]`, whose characteristic polynomials are the families of the
componentwise characteristic polynomials.

## Main results

* `TauCeti.C_charpoly_coeff_lift_mem`, `TauCeti.C_det_linearCombination_sub_one_mem`: the
  families of characteristic coefficients and of determinants of `u_x(w)`, `w` in the monoid
  algebra, lie in `S`.

## References

* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear
  Algebra **8** (1980), no. 3, 177–182.
* The determinant families follow `New.Selmer.C_det_linearCombination_mem`
  (`src/New/Congruences/FirstOrder/RibetLemma.lean`) in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Matrix

namespace TauCeti

variable {O L Y J G σ : Type*} [CommRing O] [CommRing L] [Algebra O L] [Fintype σ] [DecidableEq σ]
  [Monoid G] {S : Subalgebra O (Y → MvPolynomial J L)}

/-- The family `x ↦ U_x` of matrices, with entries read as constant polynomials, as one
representation of `G` by matrices over the families `Y → L[X_j]`. -/
private noncomputable def familyRep (u : Y → G →* Matrix σ σ L) :
    G →* Matrix σ σ (Y → MvPolynomial J L) :=
  (Matrix.piRingEquiv.symm : _ ≃+* Matrix σ σ (Y → MvPolynomial J L)).toMonoidHom.comp
    (MonoidHom.pi fun x ↦ (MvPolynomial.C.mapMatrix : Matrix σ σ L →+* _).toMonoidHom.comp (u x))

private theorem familyRep_apply (u : Y → G →* Matrix σ σ L) (g : G) (i j : σ) (x : Y) :
    familyRep (J := J) u g i j x = MvPolynomial.C (u x g i j) :=
  rfl

private theorem lift_familyRep_apply (u : Y → G →* Matrix σ σ L) (w : MonoidAlgebra O G)
    (i j : σ) (x : Y) :
    MonoidAlgebra.lift O _ G (familyRep (J := J) u) w i j x =
      MvPolynomial.C (MonoidAlgebra.lift O _ G (u x) w i j) := by
  have hC (b : O) (l : L) :
      MvPolynomial.C (b • l) = b • (MvPolynomial.C l : MvPolynomial J L) := by
    simp only [Algebra.smul_def, map_mul, MvPolynomial.algebraMap_apply]
  induction w using MonoidAlgebra.induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih, familyRep_apply, hC]

/-- If `S` contains the families of the coefficients of the characteristic polynomials of the
`u_x(g)`, as constant polynomials, then it contains those of the image `u_x(w)` of every element
`w` of the monoid algebra `O[G]`. -/
theorem C_charpoly_coeff_lift_mem (u : Y → G →* Matrix σ σ L)
    (hS : ∀ g n, (fun x ↦ MvPolynomial.C ((u x g).charpoly.coeff n)) ∈ S)
    (w : MonoidAlgebra O G) (n : ℕ) :
    (fun x ↦ MvPolynomial.C ((MonoidAlgebra.lift O _ G (u x) w).charpoly.coeff n)) ∈ S := by
  -- The characteristic polynomial of a matrix over the product ring `Y → L[X_j]` is the family
  -- of the characteristic polynomials of its components.
  have hcomp (w : MonoidAlgebra O G) (n : ℕ) :
      (MonoidAlgebra.lift O _ G (familyRep (J := J) u) w).charpoly.coeff n =
        fun x ↦ MvPolynomial.C ((MonoidAlgebra.lift O _ G (u x) w).charpoly.coeff n) := by
    funext x
    have hmap : (MonoidAlgebra.lift O _ G (familyRep (J := J) u) w).map (Pi.evalRingHom _ x) =
        (MonoidAlgebra.lift O _ G (u x) w).map MvPolynomial.C :=
      Matrix.ext fun i j ↦ lift_familyRep_apply u w i j x
    calc (MonoidAlgebra.lift O _ G (familyRep (J := J) u) w).charpoly.coeff n x
        = Pi.evalRingHom _ x
            ((MonoidAlgebra.lift O _ G (familyRep (J := J) u) w).charpoly.coeff n) :=
          (Pi.evalRingHom_apply _ _ _).symm
      _ = _ := by rw [← Polynomial.coeff_map, ← charpoly_map, hmap, charpoly_map,
          Polynomial.coeff_map]
  rw [← hcomp]
  refine charpoly_coeff_lift_mem (fun g k ↦ ?_) w n
  have h := hcomp (MonoidAlgebra.of O G g) k
  simp only [MonoidAlgebra.lift_of] at h
  rw [h]
  exact hS g k

/-- If `S` contains the families of the coefficients of the characteristic polynomials of the
`u_x(g)`, as constant polynomials, then it contains the families of the determinants
`x ↦ det (∑_g θ_g (u_x(g) - 1))` of all `O`-linear combinations. -/
theorem C_det_linearCombination_sub_one_mem (u : Y → G →* Matrix σ σ L)
    (hS : ∀ g n, (fun x ↦ MvPolynomial.C ((u x g).charpoly.coeff n)) ∈ S) (θ : G →₀ O) :
    (fun x ↦ MvPolynomial.C
      (Finsupp.linearCombination O (fun g ↦ u x g - 1) θ).det) ∈ S := by
  have hw (x : Y) : Finsupp.linearCombination O (fun g ↦ u x g - 1) θ =
      MonoidAlgebra.lift O _ G (u x)
        (Finsupp.linearCombination O (fun g ↦ MonoidAlgebra.of O G g - 1) θ) := by
    rw [← AlgHom.toLinearMap_apply, Finsupp.apply_linearCombination]
    exact congrArg (fun v ↦ Finsupp.linearCombination O v θ) (funext fun g ↦ by simp)
  have h := Subalgebra.smul_mem S (C_charpoly_coeff_lift_mem u hS
    (Finsupp.linearCombination O (fun g ↦ MonoidAlgebra.of O G g - 1) θ) 0)
    ((-1) ^ Fintype.card σ : O)
  convert h using 1
  funext x
  simp [hw, det_eq_sign_charpoly_coeff, Algebra.smul_def, MvPolynomial.algebraMap_apply]

end TauCeti
