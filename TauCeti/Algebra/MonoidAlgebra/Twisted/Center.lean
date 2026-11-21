/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Centers of twisted monoid algebras

Commutation with the basis elements tests centrality for every twisted monoid algebra.
For a commutative cancellative monoid, centrality says that each coefficient multiplied by either
opposite factor-set value gives the same result. The factors themselves may differ when the scalar
coefficient cannot be cancelled. With cancellation away from zero, the center is the span
of the basis elements at which the factor set is symmetric against every monoid element.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

section Monoid

variable {R G : Type*} [CommSemiring R] [Monoid G]
  {α : G → G → Rˣ} [IsFactorSet α]

/-- A twisted monoid-algebra element is central exactly when it commutes with every
basis element. -/
theorem mem_center_iff_commute_of (f : twistedMonoidAlgebra R G α) :
    f ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔ ∀ b, Commute f (of b) := by
  -- The algebra is associative, so the basis test's additional associativity conditions vanish.
  change f ∈ Set.center (twistedMonoidAlgebra R G α) ↔ _
  simpa only [mul_assoc, eq_self, implies_true, forall_const, and_true,
    Commute.symm_iff, basis_apply] using
    ((basis R G α).mem_center_iff (z := f))

end Monoid

section CommMonoid

variable {R G : Type*} [CommSemiring R] [CommMonoid G]
  {α : G → G → Rˣ} [IsFactorSet α]

/-- A basis element is central exactly when the factor set is symmetric against every
index, without requiring index cancellation or scalar cancellation. -/
@[simp]
theorem of_mem_center_iff (a : G) :
    of a ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔ ∀ b, α a b = α b a := by
  rw [mem_center_iff_commute_of]
  constructor
  · intro h b
    have he := (h b).eq
    rw [of_mul_of, of_mul_of, mul_comm b a] at he
    apply Units.ext
    simpa only [map_smul, repr_of, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] using congrArg (fun z ↦ (basis R G α).repr z (a * b)) he
  · intro h b
    rw [commute_iff_eq, of_mul_of, of_mul_of, h b, mul_comm a b]

end CommMonoid

section CancelCommMonoid

variable {R G : Type*} [CommSemiring R] [CancelCommMonoid G]
  {α : G → G → Rˣ} [IsFactorSet α]

/-- Centrality means that every coefficient multiplied by either opposite factor-set value
gives the same result. The two factor-set values need not themselves be equal. -/
theorem mem_center_iff_coeff (f : twistedMonoidAlgebra R G α) :
    f ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔ ∀ a b,
      (basis R G α).repr f a * (α a b : R) =
        (basis R G α).repr f a * (α b a : R) := by
  rw [mem_center_iff_commute_of]
  simp_rw [commute_of_iff]
  exact forall_comm

/-- If nonzero scalar coefficients can be cancelled, centrality is support on exponents
where the factor set is symmetric against every test element. -/
theorem mem_center_iff_support [IsLeftCancelMulZero R] (f : twistedMonoidAlgebra R G α) :
    f ∈ Subalgebra.center R (twistedMonoidAlgebra R G α) ↔
      ∀ a ∈ ((basis R G α).repr f).support, ∀ b, α a b = α b a := by
  rw [mem_center_iff_coeff]
  constructor
  · intro h a ha b
    apply Units.ext
    exact mul_left_cancel₀ (Finsupp.mem_support_iff.mp ha) (h a b)
  · intro h a b
    by_cases ha : (basis R G α).repr f a = 0
    · simp [ha]
    · rw [h a (Finsupp.mem_support_iff.mpr ha) b]

/-- The center is the span of the symmetric-factor-set basis elements when nonzero
scalar coefficients can be cancelled. -/
theorem center_toSubmodule_eq_span [IsLeftCancelMulZero R] :
    (Subalgebra.center R (twistedMonoidAlgebra R G α)).toSubmodule =
      Submodule.span R (of '' {a : G | ∀ b, α a b = α b a}) := by
  have hb : (basis R G α : G → twistedMonoidAlgebra R G α) = of :=
    funext fun a ↦ basis_apply R G α a
  have hi : (basis R G α) '' {a : G | ∀ b, α a b = α b a} =
      of '' {a : G | ∀ b, α a b = α b a} := congrArg (fun v ↦ v '' _) hb
  rw [← hi]
  ext f
  rw [Subalgebra.mem_toSubmodule, mem_center_iff_support, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]

end CancelCommMonoid

end TauCeti.TwistedMonoidAlgebra
