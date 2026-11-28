/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UnimodularFrame.Semilocal

/-!
# Unimodular frames over a product of semilocal rings

Over a commutative semilocal ring `R`, the general linear group `GL n R` acts transitively on the
unimodular `k`-frames of `Rⁿ`, the `n × k` matrices with a left inverse
(`TauCeti.exists_smul_eq_of_mul_eq_one`). The same holds over an arbitrary product `∏ i, R i` of
commutative semilocal rings, which need not be semilocal: a frame over the product is a family of
frames over the factors, and the invertible matrices moving them into each other factor by factor
assemble into one invertible matrix over the product. An example is the ring of integral finite
adeles of a number field, the product of the rings of integers of its completions at the finite
places, each of them a local ring.

## Main results

* `TauCeti.exists_smul_eq_of_mul_eq_one_pi`: over a product of commutative semilocal rings, any
  two `k`-frames of `Rⁿ` lie in the same orbit of `GL n R`.
-/

public section

open Matrix

namespace TauCeti

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] {n : Type*} [Fintype n]
  [DecidableEq n] {k : Type*} [DecidableEq k] [Finite k]

/-- Over a product `∏ i, R i` of commutative semilocal rings, `GL n (∏ i, R i)` acts transitively
on the unimodular `k`-frames: if the `n × k` matrices `A` and `A'` have left inverses, then
`g • A = A'` for some invertible `g`. -/
theorem exists_smul_eq_of_mul_eq_one_pi [∀ i, Finite (MaximalSpectrum (R i))]
    {A A' : Matrix n k (∀ i, R i)} {B B' : Matrix k n (∀ i, R i)} (h : B * A = 1)
    (h' : B' * A' = 1) : ∃ g : GL n (∀ i, R i), g • A = A' := by
  -- reduce to each factor
  have h_eval {C : Matrix k n (∀ i, R i)} {D : Matrix n k (∀ i, R i)} (hCD : C * D = 1) (i : ι) :
      C.map (Pi.evalRingHom R i) * D.map (Pi.evalRingHom R i) = 1 := by
    rw [← Matrix.map_mul, hCD, Matrix.map_one _ (map_zero _) (map_one _)]
  choose g hg using fun i ↦ exists_smul_eq_of_mul_eq_one (h_eval h i) (h_eval h' i)
  -- and assemble the matrices of the factors
  set g' := (GeneralLinearGroup.piEquiv R).symm g
  have h_coe (i : ι) : (g' : Matrix n n (∀ i, R i)).map (Pi.evalRingHom R i) = g i := by
    ext r c
    simp [g']
  have h_map (i : ι) : (g' • A).map (Pi.evalRingHom R i) = A'.map (Pi.evalRingHom R i) := by
    rw [GeneralLinearGroup.smul_def, Matrix.map_mul, h_coe, ← GeneralLinearGroup.smul_def, hg i]
  refine ⟨g', Matrix.ext fun r c ↦ funext fun i ↦ ?_⟩
  simpa only [Matrix.map_apply, Pi.evalRingHom_apply] using congrFun₂ (h_map i) r c

end TauCeti
