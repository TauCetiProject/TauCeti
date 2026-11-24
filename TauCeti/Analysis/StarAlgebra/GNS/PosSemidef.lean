/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Positive semidefiniteness of `⋆`-moment matrices

For any algebraic positive functional `φ : StarPositiveFunctional A` on a complex star algebra `A`
(without any norm or partial order on `A`), the algebraic GNS quotient `φ.GNS` identifies every
`⋆`-moment matrix `(i, j) ↦ φ (star (s i) * s j)` of a family `s : ι → A` with the Gram matrix of
the classes `i ↦ φ.classMap (s i)`, which is positive semidefinite by `Matrix.posSemidef_gram`
(`TauCeti.StarPositiveFunctional.posSemidef_apply_star_mul`).

In particular, for a family of self-adjoint elements `s : ι → A`, any complex or real matrix whose
entries agree with the second moments `φ (s i * s j)` is positive semidefinite. Through
`StarPositiveFunctional.ofPositiveLinearMap`, the same statements hold for any order-positive
functional `f : B →ₚ[ℂ] ℂ` on a `StarOrderedRing`.

## Main results

* `TauCeti.StarPositiveFunctional.posSemidef_apply_star_mul` and
  `PositiveLinearMap.posSemidef_apply_star_mul`: every `⋆`-moment matrix
  `(i, j) ↦ φ (star (s i) * s j)` is positive semidefinite.
* `TauCeti.StarPositiveFunctional.posSemidef_of_forall_apply_mul_eq`,
  `PositiveLinearMap.posSemidef_of_forall_apply_mul_eq`, and
  `PositiveLinearMap.posSemidef_of_forall_apply_mul_eq_ofReal`: complex and real second-moment
  matrices of self-adjoint families are positive semidefinite.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 4.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open scoped ComplexOrder InnerProductSpace

namespace TauCeti.StarPositiveFunctional

variable {A ι : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] (φ : StarPositiveFunctional A)

/-- For any algebraic positive functional `φ` on a complex star algebra `A` and any family
`s : ι → A`, the `⋆`-moment matrix `(i, j) ↦ φ (star (s i) * s j)` is positive semidefinite. -/
theorem posSemidef_apply_star_mul (s : ι → A) :
    (Matrix.of fun i j => φ (star (s i) * s j)).PosSemidef := by
  have hgram : Matrix.gram ℂ (fun i => φ.classMap (s i)) =
      Matrix.of fun i j => φ (star (s i) * s j) := by
    ext i j
    simp
  exact hgram ▸ Matrix.posSemidef_gram ℂ (fun i => φ.classMap (s i))

/-- Any complex matrix `C : Matrix ι ι ℂ` whose entries are the `⋆`-moments
`φ (star (s i) * s j)` of a family `s : ι → A` under an algebraic positive functional `φ` is
positive semidefinite. -/
theorem posSemidef_of_forall_apply_star_mul_eq {s : ι → A} {C : Matrix ι ι ℂ}
    (hC : ∀ i j, φ (star (s i) * s j) = C i j) :
    C.PosSemidef :=
  Matrix.ext hC ▸ φ.posSemidef_apply_star_mul s

/-- For a family of self-adjoint elements `s : ι → A`, the second-moment matrix
`(i, j) ↦ φ (s i * s j)` under an algebraic positive functional `φ` is positive semidefinite. -/
theorem posSemidef_apply_mul_of_isSelfAdjoint {s : ι → A} (hs : ∀ i, IsSelfAdjoint (s i)) :
    (Matrix.of fun i j => φ (s i * s j)).PosSemidef :=
  φ.posSemidef_of_forall_apply_star_mul_eq fun i j => by rw [Matrix.of_apply, (hs i).star_eq]

/-- If a complex matrix `C : Matrix ι ι ℂ` gives the second moments `φ (s i * s j) = C i j` of a
family of self-adjoint elements `s : ι → A` under an algebraic positive functional `φ`, then `C` is
positive semidefinite. -/
theorem posSemidef_of_forall_apply_mul_eq {s : ι → A} (hs : ∀ i, IsSelfAdjoint (s i))
    {C : Matrix ι ι ℂ} (hC : ∀ i j, φ (s i * s j) = C i j) :
    C.PosSemidef :=
  φ.posSemidef_of_forall_apply_star_mul_eq fun i j => by rw [(hs i).star_eq, hC]

/-- If a real matrix `C : Matrix ι ι ℝ` gives the second moments `φ (s i * s j) = C i j` of a
family of self-adjoint elements `s : ι → A` under an algebraic positive functional `φ`, then `C` is
positive semidefinite. -/
theorem posSemidef_of_forall_apply_mul_eq_ofReal {s : ι → A} (hs : ∀ i, IsSelfAdjoint (s i))
    {C : Matrix ι ι ℝ} (hC : ∀ i j, φ (s i * s j) = (C i j : ℂ)) :
    C.PosSemidef :=
  Matrix.posSemidef_map_complex_ofReal_iff.mp <|
    φ.posSemidef_of_forall_apply_mul_eq hs fun i j => by simpa using hC i j

end TauCeti.StarPositiveFunctional

namespace PositiveLinearMap

open TauCeti

variable {B ι : Type*} [NonUnitalRing B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
  [Module ℂ B] [StarModule ℂ B] [IsScalarTower ℂ B B] (f : B →ₚ[ℂ] ℂ)

/-- For any order-positive complex-linear functional `f` on a `StarOrderedRing` and any family
`s : ι → B`, the `⋆`-moment matrix `(i, j) ↦ f (star (s i) * s j)` is positive semidefinite. -/
theorem posSemidef_apply_star_mul (s : ι → B) :
    (Matrix.of fun i j => f (star (s i) * s j)).PosSemidef := by
  simpa using (StarPositiveFunctional.ofPositiveLinearMap f).posSemidef_apply_star_mul s

/-- Any complex matrix `C : Matrix ι ι ℂ` whose entries are the `⋆`-moments
`f (star (s i) * s j)` of a family `s : ι → B` under a positive functional `f` is positive
semidefinite. -/
theorem posSemidef_of_forall_apply_star_mul_eq {s : ι → B} {C : Matrix ι ι ℂ}
    (hC : ∀ i j, f (star (s i) * s j) = C i j) :
    C.PosSemidef :=
  (StarPositiveFunctional.ofPositiveLinearMap f).posSemidef_of_forall_apply_star_mul_eq
    fun i j => by simpa using hC i j

/-- For a family of self-adjoint elements `s : ι → B`, the second-moment matrix
`(i, j) ↦ f (s i * s j)` under a positive functional `f` is positive semidefinite. -/
theorem posSemidef_apply_mul_of_isSelfAdjoint {s : ι → B} (hs : ∀ i, IsSelfAdjoint (s i)) :
    (Matrix.of fun i j => f (s i * s j)).PosSemidef := by
  simpa using
    (StarPositiveFunctional.ofPositiveLinearMap f).posSemidef_apply_mul_of_isSelfAdjoint hs

/-- If a complex matrix `C : Matrix ι ι ℂ` gives the second moments `f (s i * s j) = C i j` of a
family of self-adjoint elements `s : ι → B` under a positive functional `f`, then `C` is positive
semidefinite. -/
theorem posSemidef_of_forall_apply_mul_eq {s : ι → B} (hs : ∀ i, IsSelfAdjoint (s i))
    {C : Matrix ι ι ℂ} (hC : ∀ i j, f (s i * s j) = C i j) :
    C.PosSemidef :=
  (StarPositiveFunctional.ofPositiveLinearMap f).posSemidef_of_forall_apply_mul_eq hs
    fun i j => by simpa using hC i j

/-- If a real matrix `C : Matrix ι ι ℝ` gives the second moments `f (s i * s j) = C i j` of a
family of self-adjoint elements `s : ι → B` under a positive functional `f`, then `C` is positive
semidefinite. -/
theorem posSemidef_of_forall_apply_mul_eq_ofReal {s : ι → B} (hs : ∀ i, IsSelfAdjoint (s i))
    {C : Matrix ι ι ℝ} (hC : ∀ i j, f (s i * s j) = (C i j : ℂ)) :
    C.PosSemidef :=
  (StarPositiveFunctional.ofPositiveLinearMap f).posSemidef_of_forall_apply_mul_eq_ofReal hs
    fun i j => by simpa using hC i j

end PositiveLinearMap
