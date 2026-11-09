/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Transporting the complex structure of a Lie algebra

A real Lie equivalence from a complex Lie algebra with scalars restricted to `ℝ` transports
multiplication by `Complex.I` to a real-linear endomorphism. Its square is minus the identity,
and it commutes with the Lie bracket in each argument. These are algebraic statements;
no topology or finite-dimensionality is required.

## Main results

* `LieEquiv.complexStructure`: the transported real-linear endomorphism.
* `LieEquiv.complexStructure_apply` and `LieEquiv.complexStructure_apply_image`:
  coordinate equations for the endomorphism and for its value on the equivalence's image.
* `LieEquiv.complexStructure_sq` and `LieEquiv.complexStructure_apply_apply`:
  its square is minus the identity.
* `LieEquiv.complexStructure_lie_left` and `LieEquiv.complexStructure_lie_right`:
  compatibility with the bracket.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1, for the complex structure on a real Lie algebra.
-/

public section

namespace LieEquiv

noncomputable section

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing L'] [LieAlgebra ℝ L']
  (e : RestrictScalars ℝ ℂ L ≃ₗ⁅ℝ⁆ L')

/-- Multiplication by `Complex.I` transported to the real Lie algebra
through a real Lie equivalence from a complex Lie algebra with scalars restricted to `ℝ`. -/
def complexStructure : Module.End ℝ L' :=
  e.toLinearEquiv.conj
    (RestrictScalars.lsmul ℝ ℂ L Complex.I)

/-- The induced real endomorphism corresponds to multiplication by `Complex.I`. -/
theorem complexStructure_apply_image
    (x : RestrictScalars ℝ ℂ L) :
    e.complexStructure (e x) =
      e
        ((RestrictScalars.addEquiv ℝ ℂ _).symm
          (Complex.I • RestrictScalars.addEquiv ℝ ℂ _ x)) := by
  let c := e.toLinearEquiv
  let t : Module.End ℝ (RestrictScalars ℝ ℂ L) :=
    RestrictScalars.lsmul ℝ ℂ L Complex.I
  -- Keep the restricted module explicit while passing between the two equivalence coercions.
  have hc (y) : c y = e y := congrFun (LieEquiv.coe_toLinearEquiv e) y
  calc
    e.complexStructure (e x) = c (t (c.symm (e x))) :=
      LinearEquiv.conj_apply_apply c t (e x)
    _ = c (t x) := by rw [← hc x, c.symm_apply_apply]
    _ = e (t x) := hc _
    _ = e ((RestrictScalars.addEquiv ℝ ℂ _).symm
        (Complex.I • RestrictScalars.addEquiv ℝ ℂ _ x)) :=
      congrArg e (RestrictScalars.lsmul_apply_apply ℝ ℂ
        L Complex.I x)

/-- The induced complex structure is multiplication by `Complex.I` in complex Lie-algebra
coordinates. -/
-- Keep the complex structure opaque to simp so its algebraic bracket laws are normal forms.
theorem complexStructure_apply (D : L') :
    e.complexStructure D =
      e
        ((RestrictScalars.addEquiv ℝ ℂ _).symm
          (Complex.I • RestrictScalars.addEquiv ℝ ℂ _
            (e.symm D))) := by
  obtain ⟨x, rfl⟩ := e.surjective D
  simp only [LieEquiv.coe_coe]
  rw [LieEquiv.symm_apply_apply]
  exact e.complexStructure_apply_image x

/-- The induced endomorphism of the real Lie algebra squares to minus the identity. -/
@[simp]
theorem complexStructure_sq :
    (e.complexStructure) ^ 2 = -1 := by
  rw [pow_two]
  apply LinearMap.ext
  intro X
  rw [mul_apply_eq_comp, LinearMap.neg_apply, one_apply_eq_self]
  let a := RestrictScalars.addEquiv ℝ ℂ L
  obtain ⟨x, rfl⟩ := e.surjective X
  simp only [LieEquiv.coe_coe]
  rw [e.complexStructure_apply_image,
    e.complexStructure_apply_image]
  have hs : a.symm (Complex.I • a (a.symm (Complex.I • a x))) = -x := by
    rw [a.apply_symm_apply, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg,
      a.symm_apply_apply]
  rw [hs]
  exact e.toLieHom.toLinearMap.map_neg x

/-- Two applications of the induced complex structure negate a vector in the real Lie algebra. -/
@[simp]
theorem complexStructure_apply_apply
    (D : L') :
    e.complexStructure (e.complexStructure D) = -D := by
  have h := DFunLike.congr_fun
    (e.complexStructure_sq) D
  simpa only [pow_two, mul_apply_eq_comp, LinearMap.neg_apply, one_apply_eq_self] using h

/-- The complex structure commutes with the real Lie bracket in its first argument. -/
@[simp]
theorem complexStructure_lie_left (X Y : L') :
    ⁅e.complexStructure X, Y⁆ =
      e.complexStructure ⁅X, Y⁆ := by
  obtain ⟨x, rfl⟩ := e.surjective X
  obtain ⟨y, rfl⟩ := e.surjective Y
  -- Normalize the Lie-equivalence coercion introduced by its surjectivity API.
  change ⁅e.complexStructure
      (e x),
        e y⁆ =
    e.complexStructure
      ⁅e x,
        e y⁆
  rw [e.complexStructure_apply_image,
    ← e.map_lie, ← e.map_lie,
    e.complexStructure_apply_image]
  apply congrArg e
  apply (RestrictScalars.addEquiv ℝ ℂ L).injective
  -- Scalar restriction uses the original complex bracket on the underlying additive group.
  change ⁅Complex.I • RestrictScalars.addEquiv ℝ ℂ _ x,
      RestrictScalars.addEquiv ℝ ℂ _ y⁆ =
    Complex.I • ⁅RestrictScalars.addEquiv ℝ ℂ _ x, RestrictScalars.addEquiv ℝ ℂ _ y⁆
  exact smul_lie _ _ _

/-- The complex structure commutes with the real Lie bracket in its second argument. -/
@[simp]
theorem complexStructure_lie_right
    (X Y : L') :
    ⁅X, e.complexStructure Y⁆ =
      e.complexStructure ⁅X, Y⁆ := by
  rw [← lie_skew X (e.complexStructure Y),
    e.complexStructure_lie_left, ← map_neg, lie_skew X Y]


end

end LieEquiv
