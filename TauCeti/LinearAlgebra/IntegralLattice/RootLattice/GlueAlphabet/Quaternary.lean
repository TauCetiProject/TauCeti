/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.D4
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Labels

/-!
# The `D₄` glue labels as a field of four elements

The glue alphabet of `D₄` is the Klein four-group with Conway--Sloane labels `0`, `1 = s`,
`2 = v`, `3 = c`. Given a root `ω` of `X² + X + 1` in a field `F₄` of four elements, these labels
are identified with `0, ω, 1, ω²`, as an isometry onto the quaternary `D₄` alphabet of
`TauCeti.typeD4QuaternaryQuadraticModule`, whose nonzero elements have quadratic value `1 / 2`.

## Main declarations

* `TauCeti.typeD4GlueAlphabetQuaternaryIsometry`: the label identification above.
* `TauCeti.typeD4GlueAlphabetQuaternaryIsometry_glueLabelEquiv`: the labels `0, 1, 2, 3`
  correspond to `0, ω, 1, ω²`.
* `TauCeti.sum_glueMinimum_eq_hammingNorm`: the shortest norm of a word in copies of the `D₄`
  glue alphabet is the Hamming weight of its image in `F₄`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §§3 and 7, and Chapter 7, §§8–9.
-/

public section

namespace TauCeti

open DynkinType IntegralLattice

variable {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

/-- **The `D₄` glue alphabet as a field of four elements**: the isometry onto the quaternary `D₄`
alphabet sending the vector label `[2] = v` to `1`, the spinor label `[1] = s` to `ω` and the
cospinor label `[3] = c` to `ω²`. It is the composite of the identifications of both sides with the
discriminant module of the checkerboard lattice `D₄`. -/
noncomputable def typeD4GlueAlphabetQuaternaryIsometry :
    FiniteQuadraticModule.Isometry ((D 4).glueAlphabet (isSimplyLaced_D 4))
      (typeD4QuaternaryQuadraticModule hF) :=
  (FiniteQuadraticModule.Isometry.ofEq
      (glueAlphabet_D_of_even 4 (isSimplyLaced_D 4) (by decide))).trans <|
    (checkerboardDiscriminantQuadraticIsometry 4 (by decide)).trans
      (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).symm

/-- The label identification sends the Klein four model `(a, b)` of a `D₄` label to `a + bω`. -/
theorem typeD4GlueAlphabetQuaternaryIsometry_apply
    (x : (D 4).glueAlphabet (isSimplyLaced_D 4)) :
    typeD4GlueAlphabetQuaternaryIsometry hF hω x =
      zmodTwoProdAddEquiv hF hω (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_even 4 (isSimplyLaced_D 4) (by decide)) x) := by
  refine ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).symm_apply_eq).mpr ?_
  rw [typeD4QuaternaryDiscriminantQuadraticIsometry_apply]
  -- The carrier of the Klein four model is `ZMod 2 × ZMod 2` only up to unfolding, so the
  -- cancellation of `zmodTwoProdAddEquiv` is applied in term mode.
  exact (checkerboardDiscriminantQuadraticIsometry_apply 4 _ _).trans
    (congrArg _ (AddEquiv.symm_apply_apply _ _).symm)

/-- **The Conway--Sloane labels `0, 1, 2, 3` of `D₄` correspond to `0, ω, 1, ω²`.** -/
@[simp]
theorem typeD4GlueAlphabetQuaternaryIsometry_glueLabelEquiv (i : Fin 4) :
    typeD4GlueAlphabetQuaternaryIsometry hF hω ((D 4).glueLabelEquiv (isSimplyLaced_D 4) i) =
      ![0, ω, 1, ω ^ 2] i := by
  rw [typeD4GlueAlphabetQuaternaryIsometry_apply, glueLabelEquiv_D_of_even]
  fin_cases i <;> simp

/-- **The shortest norm of a word in copies of the `D₄` glue alphabet is its Hamming weight**:
every nonzero `D₄` label has shortest norm `1`. -/
theorem sum_glueMinimum_eq_hammingNorm [DecidableEq F] {ι : Type*} [Fintype ι]
    (w : ι → (D 4).glueAlphabet (isSimplyLaced_D 4)) :
    ∑ j, (D 4).glueMinimum (isSimplyLaced_D 4) (w j) =
      hammingNorm fun j ↦ typeD4GlueAlphabetQuaternaryIsometry hF hω (w j) := by
  classical
  rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : w j = 0
  · simp [hj]
  · have hj' : typeD4GlueAlphabetQuaternaryIsometry hF hω (w j) ≠ 0 :=
      (map_ne_zero_iff _ (EquivLike.injective _)).mpr hj
    simp [glueMinimum_D_four_of_ne_zero hj, hj']

end TauCeti
