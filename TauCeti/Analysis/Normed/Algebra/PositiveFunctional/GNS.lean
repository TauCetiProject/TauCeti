/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.PositiveFunctional.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Uniqueness

/-!
# The GNS representation for Banach ⋆-algebras

Let `A` be a unital complex normed ⋆-algebra with isometric involution (`NormedStarGroup A`) and
let `φ : StarPositiveFunctional A` be an algebraically square-positive functional. No C⋆-order on
`A` and no normalization `‖1‖ = 1` are assumed.

When `A` is complete, or more generally whenever `φ` is continuous, the quadratic-form inequality
`φ (star b * star a * a * b) ≤ (‖a‖ : ℂ) ^ 2 * φ (star b * b)` shows that left multiplication
by every `a : A` is continuous on the GNS quotient `φ.GNS` with operator norm at most `‖a‖`. Thus
the bounded GNS construction of `TauCeti.StarPositiveFunctional.boundedRepresentation` defines a
contractive unital ⋆-representation of `A` on the Hilbert completion `φ.HilbertGNS`, with cyclic
vector `φ.hilbertCyclicVector` realizing `φ` as its vector functional.

This file provides:
* `TauCeti.StarPositiveFunctional.nullIdeal`: the GNS null space `{a | φ (star a * a) = 0}` as a
  left `Ideal A`.
* `TauCeti.StarPositiveFunctional.continuous_leftMul` and
  `TauCeti.StarPositiveFunctional.norm_boundedRepresentation_le`: boundedness and contractivity of
  the GNS representation on a unital complex Banach ⋆-algebra (and on any unital normed ⋆-algebra
  for continuous `φ`).
* `TauCeti.StarPositiveFunctional.exists_gns` and `LinearMap.exists_gns`: existence of a
  contractive cyclic Hilbert-space ⋆-representation realizing `φ`.
* `TauCeti.StarPositiveFunctional.subsingleton_hilbertGNS_of_eq_zero`: when `φ = 0`, the null
  ideal is `⊤`, the GNS Hilbert space is trivial, and both the cyclic vector and every represented
  operator vanish.

## References

* M. A. Rieffel, *C⋆-algebras*, Math 208 lectures, UC Berkeley, Spring 2008, notes by
  T. Johnson-Freyd, pp. 11–14.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §1.3.
-/

public section

noncomputable section

universe u

open scoped ComplexOrder InnerProductSpace

namespace TauCeti.StarPositiveFunctional

section Algebraic

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  (φ : StarPositiveFunctional A)

/-- The GNS null space `{a : A | φ (star a * a) = 0}` as a left ideal of `A`. -/
def nullIdeal : Ideal A where
  toAddSubmonoid := φ.nullSubmodule.toAddSubmonoid
  smul_mem' a _ hb := φ.mul_mem_nullSubmodule a hb

@[simp]
theorem mem_nullIdeal_iff (a : A) : a ∈ φ.nullIdeal ↔ φ (star a * a) = 0 :=
  φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero a

@[simp]
theorem restrictScalars_nullIdeal : (φ.nullIdeal.restrictScalars ℂ) = φ.nullSubmodule := by
  ext a
  simp

/-- When `φ` vanishes identically, the null ideal is all of `A`. -/
theorem nullIdeal_eq_top_of_eq_zero (hφ : ∀ a, φ a = 0) : φ.nullIdeal = ⊤ := by
  ext a
  simp [hφ]

/-- When `φ` vanishes identically, the GNS Hilbert space `φ.HilbertGNS` is a subsingleton. -/
theorem subsingleton_hilbertGNS_of_eq_zero (hφ : ∀ a, φ a = 0) : Subsingleton φ.HilbertGNS := by
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ z : φ.HilbertGNS, z = 0 := by
    intro z
    refine φ.denseRange_hilbertClassMap.induction_on z ?_ ?_
    · exact isClosed_eq continuous_id continuous_const
    · intro a
      simp [φ.hilbertClassMap_eq_zero_iff, hφ]
  rw [hzero x, hzero y]

/-- When `φ` vanishes identically, the canonical GNS cyclic vector is zero. -/
theorem hilbertCyclicVector_eq_zero_of_eq_zero (hφ : ∀ a, φ a = 0) :
    φ.hilbertCyclicVector = 0 := by
  have := φ.subsingleton_hilbertGNS_of_eq_zero hφ
  exact Subsingleton.elim _ _

end Algebraic

section Normed

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [NormedStarGroup A]
  [StarModule ℂ A] (φ : StarPositiveFunctional A)

/-- If `φ` is continuous on a unital normed ⋆-algebra with isometric involution, left
multiplication by every `a : A` is continuous on `φ.GNS`. -/
theorem continuous_leftMul_of_continuous (hc : Continuous φ) (a : A) :
    Continuous (φ.leftMul a) :=
  (φ.continuous_leftMul_iff a).mpr
    ⟨‖a‖, norm_nonneg a, φ.map_star_mul_star_mul_self_le_of_continuous hc a⟩

/-- If `φ` is continuous on a unital normed ⋆-algebra with isometric involution, the canonical GNS
representation is contractive: `‖π a‖ ≤ ‖a‖`. -/
theorem norm_boundedRepresentation_le_of_continuous (hc : Continuous φ) (a : A) :
    ‖φ.boundedRepresentation (φ.continuous_leftMul_of_continuous hc) a‖ ≤ ‖a‖ := by
  rw [φ.boundedRepresentation_apply,
    φ.norm_hilbertLeftMul_le_iff (φ.continuous_leftMul_of_continuous hc a) (norm_nonneg a)]
  exact φ.map_star_mul_star_mul_self_le_of_continuous hc a

/-- Every continuous positive functional on a unital complex normed ⋆-algebra with isometric
involution admits a contractive cyclic Hilbert-space ⋆-representation realizing it as a vector
functional. -/
theorem exists_gns_of_continuous (hc : Continuous φ) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H),
      (∀ a, ‖π a‖ ≤ ‖a‖) ∧
      (∀ a, φ a = ⟪ξ, π a ξ⟫_ℂ) ∧
      closure (Set.range fun a : A => π a ξ) = Set.univ := by
  refine ⟨φ.HilbertGNS, inferInstance, inferInstance, inferInstance,
    φ.boundedRepresentation (φ.continuous_leftMul_of_continuous hc), φ.hilbertCyclicVector,
    φ.norm_boundedRepresentation_le_of_continuous hc, fun a => ?_, ?_⟩
  · simp
  · exact (φ.denseRange_boundedRepresentation_hilbertCyclicVector
      (φ.continuous_leftMul_of_continuous hc)).closure_range

/-- Uniqueness of the cyclic GNS realization of a continuous positive functional on a unital
normed ⋆-algebra with isometric involution. -/
theorem existsUnique_gnsEquiv_of_continuous (hc : Continuous φ) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun a : A => π a ξ)) (hφ : ∀ a, ⟪ξ, π a ξ⟫_ℂ = φ a) :
    ∃! U : φ.HilbertGNS ≃ₗᵢ[ℂ] H, U φ.hilbertCyclicVector = ξ ∧
      ∀ (a : A) (v : φ.HilbertGNS),
        U (φ.boundedRepresentation (φ.continuous_leftMul_of_continuous hc) a v) = π a (U v) :=
  φ.existsUnique_gnsEquiv π ξ hcyc hφ (φ.continuous_leftMul_of_continuous hc)

section Complete

variable [CompleteSpace A]

/-- On a unital complex Banach ⋆-algebra with isometric involution, left multiplication by every
element is continuous on the GNS quotient `φ.GNS`. -/
theorem continuous_leftMul (a : A) : Continuous (φ.leftMul a) :=
  φ.continuous_leftMul_of_continuous φ.continuous a

/-- On a unital complex Banach ⋆-algebra with isometric involution, the canonical GNS
representation is contractive: `‖π a‖ ≤ ‖a‖`. -/
theorem norm_boundedRepresentation_le (a : A) :
    ‖φ.boundedRepresentation φ.continuous_leftMul a‖ ≤ ‖a‖ :=
  φ.norm_boundedRepresentation_le_of_continuous φ.continuous a

/-- When `φ` vanishes identically, every operator in the canonical GNS representation is zero. -/
theorem boundedRepresentation_apply_eq_zero_of_eq_zero (hφ : ∀ a, φ a = 0) (a : A) :
    φ.boundedRepresentation φ.continuous_leftMul a = 0 := by
  have := φ.subsingleton_hilbertGNS_of_eq_zero hφ
  exact Subsingleton.elim _ _

/-- **Banach-input GNS theorem**: every algebraically positive functional on a unital complex
Banach ⋆-algebra with isometric involution admits a contractive cyclic Hilbert-space
⋆-representation realizing it as a vector functional. -/
theorem exists_gns :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H),
      (∀ a, ‖π a‖ ≤ ‖a‖) ∧
      (∀ a, φ a = ⟪ξ, π a ξ⟫_ℂ) ∧
      closure (Set.range fun a : A => π a ξ) = Set.univ :=
  φ.exists_gns_of_continuous φ.continuous

end Complete

end Normed

end TauCeti.StarPositiveFunctional

namespace LinearMap

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [NormedStarGroup A] [StarModule ℂ A]

/-- **Banach-input GNS theorem**: every algebraically square-positive linear functional on a unital
complex Banach ⋆-algebra with isometric involution admits a contractive cyclic Hilbert-space
⋆-representation realizing it as a vector functional. -/
theorem exists_gns (φ : A →ₗ[ℂ] ℂ) (hφ : ∀ a, 0 ≤ φ (star a * a)) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H),
      (∀ a, ‖π a‖ ≤ ‖a‖) ∧
      (∀ a, φ a = ⟪ξ, π a ξ⟫_ℂ) ∧
      closure (Set.range fun a : A => π a ξ) = Set.univ :=
  TauCeti.StarPositiveFunctional.exists_gns ⟨φ, hφ⟩

end LinearMap
