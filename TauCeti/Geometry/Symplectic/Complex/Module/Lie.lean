/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Complex
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Transported complex structures and Lie brackets

A real Lie equivalence from a complex Lie algebra transports its canonical almost complex
structure through the underlying linear equivalence. The transported structure commutes with
the bracket in both arguments. The construction and square laws are the existing almost
complex structure transport API.

## Main results

* `LieEquiv.transport_ofRestrictScalars_apply_image`: multiplication by `I` at an image vector.
* `LieEquiv.transport_ofRestrictScalars_lie_left` and
  `LieEquiv.transport_ofRestrictScalars_lie_right`: bracket compatibility of the transported
  canonical complex structure.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1.
-/

public section


open TauCeti

namespace LieEquiv

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing L'] [LieAlgebra ℝ L']
  (e : RestrictScalars ℝ ℂ L ≃ₗ⁅ℝ⁆ L')

/-- The transported canonical complex structure on the image of the equivalence. -/
-- The generic transport and normalized-equivalence simp rules already prove this equation.
theorem transport_ofRestrictScalars_apply_image (x : RestrictScalars ℝ ℂ L) :
    (AlmostComplexStructure.ofRestrictScalars L).transport e.toRealLinearEquiv (e x) =
      e ((RestrictScalars.addEquiv ℝ ℂ L).symm
        (Complex.I • RestrictScalars.addEquiv ℝ ℂ L x)) := by
  rw [AlmostComplexStructure.transport_apply, toRealLinearEquiv_symm_apply,
    e.symm_apply_apply]
  exact (toRealLinearEquiv_apply e _).trans
    (congrArg e (AlmostComplexStructure.ofRestrictScalars_apply L x))

/-- The transported complex structure commutes with the bracket in its first argument. -/
-- These are explicit rewrite rules: the existing transport application simp lemma expands
-- their left-hand sides before the bracket laws can match.
theorem transport_ofRestrictScalars_lie_left (X Y : L') :
    ⁅(AlmostComplexStructure.ofRestrictScalars L).transport e.toRealLinearEquiv X, Y⁆ =
      (AlmostComplexStructure.ofRestrictScalars L).transport
        e.toRealLinearEquiv ⁅X, Y⁆ := by
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective X
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective Y
  have hlie (u v : RestrictScalars ℝ ℂ L) : ⁅e u, e v⁆ = e ⁅u, v⁆ :=
    (e.map_lie u v).symm
  simp only [LieEquiv.coe_toLinearEquiv]
  rw [transport_ofRestrictScalars_apply_image, hlie, hlie,
    transport_ofRestrictScalars_apply_image]
  apply congrArg e
  apply (RestrictScalars.addEquiv ℝ ℂ L).injective
  simp only [RestrictScalars.addEquiv_lie, AddEquiv.apply_symm_apply, smul_lie]

/-- The transported complex structure commutes with the bracket in its second argument. -/
theorem transport_ofRestrictScalars_lie_right (X Y : L') :
    ⁅X, (AlmostComplexStructure.ofRestrictScalars L).transport e.toRealLinearEquiv Y⁆ =
      (AlmostComplexStructure.ofRestrictScalars L).transport
        e.toRealLinearEquiv ⁅X, Y⁆ := by
  rw [← lie_skew X
    ((AlmostComplexStructure.ofRestrictScalars L).transport e.toRealLinearEquiv Y),
    transport_ofRestrictScalars_lie_left, ← LinearMap.map_neg, lie_skew X Y]

end LieEquiv
