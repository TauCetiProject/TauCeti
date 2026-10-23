/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.BilinearForm.Squares

/-!
# Exterior squares and skew-adjoint endomorphisms

A perfect symmetric bilinear form on a finite free module identifies the second exterior power
with its skew-adjoint endomorphisms, provided `2` is invertible. The construction factors through
alternating bilinear forms and Mathlib's dual pairing for exterior powers.

Over a field, a nondegenerate form on a finite-dimensional vector space is perfect, as witnessed
by `LinearMap.BilinForm.toDual`. Over a commutative ring, perfection means that the linear map
from the module to its dual is bijective.

## Main definitions

* `LinearMap.BilinForm.exteriorSquareEquivSkewAdjoint`: the linear equivalence from the second
  exterior power to the skew-adjoint endomorphisms.

## Main results

* `LinearMap.BilinForm.exteriorSquareEquivSkewAdjoint_apply_ιMulti_apply`: the action of a
  decomposable bivector.
-/

public section

open LinearMap (BilinForm)

universe u v

namespace LinearMap.BilinForm

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

private theorem isAlt_compLeft_of_skewAdjoint
    (B : BilinForm R V) (hBsymm : B.IsSymm) [Invertible (2 : R)]
    (f : skewAdjointLieSubalgebra B) : LinearMap.IsAlt (B.compLeft f) := by
  intro x
  have hskew := (LinearMap.mem_skewAdjointSubmodule
    (B := B) (f : Module.End R V)).mp f.property x x
  have ha : B ((f : Module.End R V) x) x = -B ((f : Module.End R V) x) x := by
    simpa [hBsymm.eq] using hskew
  calc
    B ((f : Module.End R V) x) x = ⅟(2 : R) * (2 * B ((f : Module.End R V) x) x) := by
      rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [two_mul, add_eq_zero_iff_eq_neg.mpr ha, mul_zero]

private noncomputable def skewAdjointEquivExteriorDual
    (B : BilinForm R V) (hB : Function.Bijective B) (hBsymm : B.IsSymm)
    [Invertible (2 : R)] :
    skewAdjointLieSubalgebra B ≃ₗ[R] Module.Dual R (⋀[R]^2 V) where
  toFun f := exteriorPower.alternatingMapLinearEquiv
    (LinearMap.IsAlt.toAlternatingMap (isAlt_compLeft_of_skewAdjoint B hBsymm f))
  invFun ψ := ⟨(LinearEquiv.ofBijective B hB).symm.comp
    (TauCeti.BilinForm.ofExteriorSquareDual ψ), by
    -- Membership in the Lie subalgebra is membership in its underlying submodule.
    change _ ∈ B.skewAdjointSubmodule
    rw [LinearMap.mem_skewAdjointSubmodule]
    intro x y
    have hxy := (TauCeti.BilinForm.isAlt_ofExteriorSquareDual ψ).neg_eq x y
    rw [LinearMap.comp_apply, Pi.neg_apply, map_neg, hBsymm.eq x]
    simpa using congrArg Neg.neg hxy⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    apply hB.injective
    ext y
    simp [TauCeti.BilinForm.ofExteriorSquareDual_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.IsAlt.toAlternatingMap_apply]
  right_inv ψ := by
    apply TauCeti.BilinForm.ofExteriorSquareDual_injective
    ext x y
    simp [TauCeti.BilinForm.ofExteriorSquareDual_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.IsAlt.toAlternatingMap_apply]
  map_add' f g := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [LinearMap.IsAlt.toAlternatingMap_apply]
  map_smul' c f := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [LinearMap.IsAlt.toAlternatingMap_apply]

private theorem skewAdjointEquivExteriorDual_apply_ιMulti
    (B : BilinForm R V) (hB : Function.Bijective B) (hBsymm : B.IsSymm)
    [Invertible (2 : R)] (f : skewAdjointLieSubalgebra B) (x y : V) :
    skewAdjointEquivExteriorDual B hB hBsymm f
      (exteriorPower.ιMulti R 2 ![x, y]) = B ((f : Module.End R V) x) y := by
  simp [skewAdjointEquivExteriorDual,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    LinearMap.IsAlt.toAlternatingMap_apply]

variable [Module.Free R V] [Module.Finite R V]

/-- A perfect symmetric bilinear form on a finite free module identifies the second exterior
power with its skew-adjoint endomorphisms. The sign is chosen to agree with the normalized
Clifford bivector action. -/
noncomputable def exteriorSquareEquivSkewAdjoint
    (B : BilinForm R V) (hB : Function.Bijective B) (hBsymm : B.IsSymm)
    [Invertible (2 : R)] : ⋀[R]^2 V ≃ₗ[R] skewAdjointLieSubalgebra B :=
  (LinearEquiv.neg R).trans <|
    (LinearEquiv.ofBijective
      ((exteriorPower.pairingDual R V 2).comp (exteriorPower.map 2 B))
      ((exteriorPower.bijective_pairingDual R V 2).comp
        ⟨exteriorPower.map_injective (LinearEquiv.ofBijective B hB).symm (by ext; simp),
          exteriorPower.map_surjective hB.surjective⟩)).trans
      (skewAdjointEquivExteriorDual B hB hBsymm).symm

/-- A decomposable bivector acts by the standard skew-adjoint rank-two endomorphism. -/
@[simp]
theorem exteriorSquareEquivSkewAdjoint_apply_ιMulti_apply
    (B : BilinForm R V) (hB : Function.Bijective B) (hBsymm : B.IsSymm)
    [Invertible (2 : R)] (u v x : V) :
    ((exteriorSquareEquivSkewAdjoint B hB hBsymm
      (exteriorPower.ιMulti R 2 ![u, v]) : skewAdjointLieSubalgebra B) : Module.End R V) x =
      B v x • u - B u x • v := by
  apply hB.injective
  ext y
  rw [← skewAdjointEquivExteriorDual_apply_ιMulti B hB hBsymm]
  -- Evaluate the transported exterior form after cancelling the skew-adjoint equivalence.
  have hcomp : skewAdjointEquivExteriorDual B hB hBsymm
      (exteriorSquareEquivSkewAdjoint B hB hBsymm
        (exteriorPower.ιMulti R 2 ![u, v])) =
      (exteriorPower.pairingDual R V 2)
        (exteriorPower.map 2 B (-exteriorPower.ιMulti R 2 ![u, v])) := by
    simp [exteriorSquareEquivSkewAdjoint]
  rw [hcomp]
  simp [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
    Matrix.det_fin_two]

end LinearMap.BilinForm
