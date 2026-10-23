/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of the nodal equation

The coordinate algebra of `xy = a` commutes with change of coefficient ring. The canonical
isomorphism identifies the two coordinates and the scalar extension maps. It gives the affine
chart comparison needed when a nodal curve is pulled back along a morphism of bases.

## Reference

* Stacks Project, Example 55.14.1, Tag 0CDC.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open Algebra TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (a : R)

/-- The isomorphism from the scalar extension of the nodal algebra to the nodal algebra
of the image of its smoothing parameter. -/
def baseChange : S ⊗[R] NodeAlgebra R a ≃ₐ[S]
    NodeAlgebra S (algebraMap R S a) := by
  letI : Algebra R (NodeAlgebra S (algebraMap R S a)) :=
    Algebra.compHom _ (algebraMap R S)
  letI : IsScalarTower R S (NodeAlgebra S (algebraMap R S a)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let m : NodeAlgebra R a →ₐ[R] NodeAlgebra S (algebraMap R S a) :=
    lift a (coord (algebraMap R S a) 0) (coord (algebraMap R S a) 1) (by
      simpa only [coord_zero_mul_coord_one] using
        (IsScalarTower.algebraMap_apply R S (NodeAlgebra S (algebraMap R S a)) a).symm)
  let f : S ⊗[R] NodeAlgebra R a →ₐ[S] NodeAlgebra S (algebraMap R S a) :=
    (AlgHom.liftEquiv R S (NodeAlgebra R a)
      (NodeAlgebra S (algebraMap R S a))) m
  let g : NodeAlgebra S (algebraMap R S a) →ₐ[S] S ⊗[R] NodeAlgebra R a :=
    lift (algebraMap R S a) ((1 : S) ⊗ₜ[R] coord a 0) ((1 : S) ⊗ₜ[R] coord a 1) (by
      calc
        ((1 : S) ⊗ₜ[R] coord a 0) * ((1 : S) ⊗ₜ[R] coord a 1) =
            (1 : S) ⊗ₜ[R] (coord a 0 * coord a 1) := by simp
        _ = (1 : S) ⊗ₜ[R] algebraMap R (NodeAlgebra R a) a := by rw [coord_zero_mul_coord_one]
        _ = (algebraMap R S a) ⊗ₜ[R] (1 : NodeAlgebra R a) := by
          simp [Algebra.algebraMap_eq_smul_one, smul_tmul, Algebra.algebraMap_eq_smul_one]
        _ = algebraMap S (S ⊗[R] NodeAlgebra R a) (algebraMap R S a) := by
          simp [Algebra.TensorProduct.algebraMap_apply])
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply hom_ext
    · simp [f, g, m]
    · simp [f, g, m]
  · apply Algebra.TensorProduct.ext_ring
    apply hom_ext
    · simp [f, g, m]
    · simp [f, g, m]

/-- The ring map taking the original nodal coordinates into the changed coefficient ring. -/
def map : NodeAlgebra R a →+* NodeAlgebra S (algebraMap R S a) :=
  (baseChange a).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : NodeAlgebra R a →ₐ[R] S ⊗[R] NodeAlgebra R a).toRingHom

/-- Changing coefficients sends constants to their images in the new coefficient ring. -/
@[simp]
theorem map_algebraMap (r : R) :
    map a (algebraMap R (NodeAlgebra R a) r) =
      algebraMap S (NodeAlgebra S (algebraMap R S a)) (algebraMap R S r) := by
  -- Expose the underlying ring maps before using the algebra-map commutation laws.
  change (baseChange a)
    ((Algebra.TensorProduct.includeRight : NodeAlgebra R a →ₐ[R] S ⊗[R] NodeAlgebra R a)
      (algebraMap R (NodeAlgebra R a) r)) = _
  rw [(Algebra.TensorProduct.includeRight :
    NodeAlgebra R a →ₐ[R] S ⊗[R] NodeAlgebra R a).commutes r]
  rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] NodeAlgebra R a) r]
  exact (baseChange a).commutes (algebraMap R S r)

/-- Changing coefficients preserves each nodal coordinate. -/
@[simp]
theorem map_coord (i : Fin 2) :
    map a (coord a i) = coord (algebraMap R S a) i := by
  fin_cases i <;> simp [map, baseChange]

/-- Base change of a pure tensor is scalar multiplication of the changed coordinate map. -/
@[simp]
theorem baseChange_tmul (s : S) (x : NodeAlgebra R a) :
    baseChange a (s ⊗ₜ[R] x) = s • map a x := by
  have hmap : map a x = baseChange a ((1 : S) ⊗ₜ[R] x) := by
    simp only [map, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.includeRight_apply]
  rw [hmap]
  simp only [baseChange, AlgEquiv.ofAlgHom_apply, AlgHom.liftEquiv_tmul, one_smul]

/-- The inverse base-change map sends the new coordinates to the old coordinates in the
extended algebra. -/
@[simp]
theorem baseChange_symm_coord (i : Fin 2) :
    (baseChange a).symm (coord (algebraMap R S a) i) =
      (1 : S) ⊗ₜ[R] coord a i := by
  apply (baseChange a).injective
  simp

end TauCeti.NodeAlgebra
