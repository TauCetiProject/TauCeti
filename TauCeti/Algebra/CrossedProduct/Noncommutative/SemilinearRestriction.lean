/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Module
public import TauCeti.Algebra.CrossedProduct.Noncommutative.Restriction

/-!
# Restricting semilinear crossed-product actions

Restricting the index monoid of a semilinear action agrees with restricting scalars
along the crossed-product map `CrossedSystem.Algebra.comapHom`. The comparison is an
equality of algebra actions, and hence of the resulting module structures, on the
original carrier. It applies to subgroup inclusions without any finite-index assumption.

At the crossed-system level, restriction commutes with passing to opposite coefficients
and inverse factors (`comap_opInv`).

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti.CrossedSystem

variable {k D G H : Type*} [CommSemiring k] [Semiring D] [_root_.Algebra k D]
  [Monoid G] [Monoid H]

/-- Restricting indices commutes with opposite coefficients and inverse factors. -/
@[simp]
theorem comap_opInv (c : CrossedSystem k D G) (f : H →* G) :
    (c.comap f).opInv = c.opInv.comap f := by
  ext <;> simp

namespace SemilinearAction

variable {c : CrossedSystem k D G} {M : Type*}
  [AddCommMonoid M] [Module k M] [Module D M]

/-- Restrict the semilinear operators along a homomorphism of index monoids. -/
def comap (s : SemilinearAction c M) (f : H →* G) : SemilinearAction (c.comap f) M where
  operator h := s.operator (f h)
  operator_one := by simp [s.operator_one]
  operator_smul h d m := by simpa only [comap_action] using s.operator_smul (f h) d m
  operator_mul h j m := by
    simpa only [map_mul, comap_factor] using s.operator_mul (f h) (f j) m

/-- The restricted operator is the original operator at the image index. -/
@[simp]
theorem comap_operator (s : SemilinearAction c M) (f : H →* G) (h : H) :
    (s.comap f).operator h = s.operator (f h) := (rfl)

variable [IsScalarTower k D M]

/-- Extending restricted operators to the crossed product is restriction of the
original algebra action along the crossed-product homomorphism. -/
@[simp]
theorem comap_toAlgHom (s : SemilinearAction c M) (f : H →* G) :
    (s.comap f).toAlgHom = s.toAlgHom.comp (Algebra.comapHom c f) := by
  apply Algebra.algHom_ext <;> intro x <;> simp

/-- Every scalar in the restricted crossed product acts by its image in the original
crossed product, not just the distinguished basis elements. -/
theorem comap_module_smul (s : SemilinearAction c M) (f : H →* G)
    (a : Algebra (c.comap f)) (m : M) :
    letI := (s.comap f).module
    a • m = s.toAlgHom (Algebra.comapHom c f a) m := by
  rw [module_smul, comap_toAlgHom, AlgHom.comp_apply]

/-- The module built from restricted operators is exactly the module obtained by
restriction of scalars along `Algebra.comapHom`, on the same additive carrier. -/
theorem comap_module (s : SemilinearAction c M) (f : H →* G) :
    (s.comap f).module =
      letI := s.module
      Module.compHom M (Algebra.comapHom c f).toRingHom := by
  apply Module.ext'
  exact comap_module_smul s f

end SemilinearAction

end TauCeti.CrossedSystem
