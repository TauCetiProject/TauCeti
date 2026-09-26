/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal

/-!
# Spinor norms under extension of scalars

Let `L / K` be a field extension and `Q` a nondegenerate quadratic form on a finite-dimensional
`K`-vector space `V`. Extending scalars carries an orthogonal automorphism `g` of `Q` to an
orthogonal automorphism `g_L` of `Q.baseChange L`. This file proves that the spinor norm of `g_L`
is the image of the spinor norm of `g` under the pushforward of square classes
`Kˣ/(Kˣ)² → Lˣ/(Lˣ)²`.

Extending scalars carries the reflection in `v` to the reflection in `1 ⊗ₜ v`, whose norm is the
image of `Q v`. Since reflections generate the orthogonal group, the two homomorphisms agree
everywhere. Restricting to determinant one gives the same compatibility for the spinor norm on the
special orthogonal group. Applied to the completions of a number field, this compares a global
spinor norm with its local ones.

## Main results

* `CliffordAlgebra.orthogonalSpinorNorm_comp_orthogonalGroupBaseChange`: the spinor norm after
  extension of scalars is the pushforward of the spinor norm, as an equality of homomorphisms.
* `CliffordAlgebra.orthogonalSpinorNorm_orthogonalGroupBaseChange`: its pointwise form.
* `CliffordAlgebra.spinorNorm_specialOrthogonalGroupBaseChange`: the same on `SO(Q)`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §55.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

open TauCeti

universe u v w

variable {K : Type u} {L : Type w} {V : Type v} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Invertible (2 : K)]

/-- Extending scalars from `K` to `L` intertwines the spinor norms of `Q` and of
`Q.baseChange L` with the pushforward of square classes along `K → L`. -/
theorem orthogonalSpinorNorm_comp_orthogonalGroupBaseChange (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (orthogonalSpinorNorm (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)).comp
        (QuadraticMap.orthogonalGroupBaseChange Q) =
      (AddMonoidHom.toMultiplicative (algebraMap K L).squareClassMap.toAddMonoidHom).comp
        (orthogonalSpinorNorm Q hQ) := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  refine QuadraticMap.orthogonalGroup_hom_ext Q hQ fun v _ ↦ ?_
  have hv : Q.baseChange L (1 ⊗ₜ v) = algebraMap K L (Q v) := by
    rw [QuadraticForm.baseChange_tmul, mul_one, Algebra.smul_def, mul_one]
  let _ : Invertible (Q.baseChange L (1 ⊗ₜ v)) :=
    (Invertible.map (algebraMap K L) (Q v)).copy _ hv
  have hrefl : QuadraticMap.orthogonalGroupBaseChange Q (QuadraticMap.reflectionOrthogonal Q v) =
      QuadraticMap.reflectionOrthogonal (Q.baseChange L) (1 ⊗ₜ v) := by
    apply Subtype.ext
    rw [QuadraticMap.coe_orthogonalGroupBaseChange, QuadraticMap.coe_reflectionOrthogonal,
      QuadraticMap.coe_reflectionOrthogonal, QuadraticMap.reflection_baseChange]
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hrefl,
    orthogonalSpinorNorm_reflectionOrthogonal, orthogonalSpinorNorm_reflectionOrthogonal]
  simp only [squareClassHom_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
    LinearMap.toAddMonoidHom_coe, RingHom.squareClassMap_apply]
  exact congrArg (Multiplicative.ofAdd ∘ squareClass) (Units.ext hv)

/-- The spinor norm of an orthogonal automorphism after extending scalars from `K` to `L` is the
image of its spinor norm under the pushforward of square classes. -/
@[simp]
theorem orthogonalSpinorNorm_orthogonalGroupBaseChange (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (g : QuadraticMap.orthogonalGroup Q) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    orthogonalSpinorNorm (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)
        (QuadraticMap.orthogonalGroupBaseChange Q g) =
      Multiplicative.ofAdd
        ((algebraMap K L).squareClassMap (orthogonalSpinorNorm Q hQ g).toAdd) :=
  DFunLike.congr_fun (orthogonalSpinorNorm_comp_orthogonalGroupBaseChange Q hQ) g

/-- The spinor norm of a special orthogonal automorphism after extending scalars from `K` to `L`
is the image of its spinor norm under the pushforward of square classes. -/
-- `spinorNorm_apply` already simplifies the left-hand side, so this is not a simp-normal form.
theorem spinorNorm_specialOrthogonalGroupBaseChange (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (g : QuadraticMap.specialOrthogonalGroup Q) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    spinorNorm (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)
        (QuadraticMap.specialOrthogonalGroupBaseChange Q g) =
      Multiplicative.ofAdd ((algebraMap K L).squareClassMap (spinorNorm Q hQ g).toAdd) := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [spinorNorm_apply, spinorNorm_apply, ← orthogonalSpinorNorm_orthogonalGroupBaseChange]
  congr 1
  apply Subtype.ext
  rw [QuadraticMap.coe_specialOrthogonalToOrthogonal, QuadraticMap.coe_orthogonalGroupBaseChange,
    QuadraticMap.coe_specialOrthogonalToOrthogonal,
    QuadraticMap.coe_specialOrthogonalGroupBaseChange]

end CliffordAlgebra
