/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Characters with values in an integrally closed extension

If `B` is an integral `R`-algebra and `R` is integrally closed in `S`, every `R`-algebra
homomorphism `B → S` factors uniquely through `R`. The source need not be commutative.
This gives descent of rational points of finite algebras over valuation rings.

## References

* The Stacks Project, Section 10.36, especially Definition 10.36.9 (Tag 00GP),
  https://stacks.math.columbia.edu/tag/00GH.
-/

public section

variable {R B S : Type*} [CommRing R] [Ring B] [Algebra R B] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R B] [IsIntegrallyClosedIn R S]

namespace AlgHom

/-- The `R`-valued character whose composite with `algebraMap R S` is `f`, when `B` is
integral over `R` and `R` is integrally closed in `S`. -/
noncomputable def restrictOfIsIntegrallyClosedIn (f : B →ₐ[R] S) : B →ₐ[R] R where
  toFun b := IsIntegralClosure.mk' R (f b) ((Algebra.IsIntegral.isIntegral (R := R) b).map f)
  map_zero' := by simp only [map_zero, IsIntegralClosure.mk'_zero]
  map_one' := by simp only [map_one, IsIntegralClosure.mk'_one]
  map_add' b c := by
    apply IsIntegralClosure.algebraMap_injective R R S
    simp only [IsIntegralClosure.algebraMap_mk', map_add]
  map_mul' b c := by
    apply IsIntegralClosure.algebraMap_injective R R S
    simp only [IsIntegralClosure.algebraMap_mk', map_mul]
  commutes' r := by simp only [AlgHom.commutes, IsIntegralClosure.mk'_algebraMap,
    Algebra.algebraMap_self_apply]

/-- Composing the restricted character with `algebraMap R S` recovers the original value. -/
@[simp, grind =]
theorem algebraMap_restrictOfIsIntegrallyClosedIn (f : B →ₐ[R] S) (b : B) :
    algebraMap R S (f.restrictOfIsIntegrallyClosedIn b) = f b :=
  IsIntegralClosure.algebraMap_mk' (R := R) R (f b)
    ((Algebra.IsIntegral.isIntegral (R := R) b).map f)

end AlgHom

namespace TauCeti

/-- Composing with `algebraMap R S` gives a bijection from `R`-valued to `S`-valued characters
of an integral algebra when `R` is integrally closed in `S`. -/
noncomputable def algHomEquivOfIsIntegrallyClosedIn (R B S : Type*)
    [CommRing R] [Ring B] [Algebra R B] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R B] [IsIntegrallyClosedIn R S] :
    (B →ₐ[R] R) ≃ (B →ₐ[R] S) where
  toFun f := (Algebra.ofId R S).comp f
  invFun := AlgHom.restrictOfIsIntegrallyClosedIn
  left_inv f := by
    ext b
    apply IsIntegralClosure.algebraMap_injective R R S
    rw [AlgHom.algebraMap_restrictOfIsIntegrallyClosedIn]
    rfl
  right_inv f := by ext; simp

variable (R B S)

/-- The character descent equivalence composes character values with `algebraMap R S`. -/
@[simp, grind =]
theorem algHomEquivOfIsIntegrallyClosedIn_apply (f : B →ₐ[R] R) (b : B) :
    algHomEquivOfIsIntegrallyClosedIn R B S f b = algebraMap R S (f b) := (rfl)

/-- The inverse character descent equivalence is restriction to the base ring. -/
@[simp, grind =]
theorem algHomEquivOfIsIntegrallyClosedIn_symm_apply (f : B →ₐ[R] S) :
    (algHomEquivOfIsIntegrallyClosedIn R B S).symm f = f.restrictOfIsIntegrallyClosedIn := (rfl)

end TauCeti
