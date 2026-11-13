/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.StarAlgebra.GNS.Bounded
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Unitary uniqueness of the bounded GNS representation

A cyclic bounded Hilbert-space `⋆`-representation realizing a positive functional
`φ : StarPositiveFunctional A` as a vector state is unitarily equivalent to the canonical
bounded GNS representation on `φ.HilbertGNS`.

The intertwining unitary `StarPositiveFunctional.gnsEquiv` sends `φ.hilbertClassMap a` to
`π a ξ`, intertwines `φ.hilbertLeftMul` (and, in the unital case, `φ.boundedRepresentation`)
with `π`, and is uniquely characterized by this action on algebra classes. For a unital
representation of an algebra whose elements all act boundedly,
`StarPositiveFunctional.existsUnique_gnsEquiv` characterizes it as the unique unitary carrying the
canonical cyclic vector `φ.hilbertCyclicVector` to `ξ` and intertwining the representations. Zero
functionals and zero Hilbert spaces are included.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
* Adapted from `TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness`.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace TauCeti.StarPositiveFunctional

section NonUnital

variable {A H : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : StarPositiveFunctional A) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hcyc : DenseRange (fun a : A => π a ξ))
  (hφ : ∀ a, ⟪ξ, π a ξ⟫_ℂ = φ a)

include hφ in
/-- A cyclic-type vector realization of `φ` gives orbit vectors the same norms as the
corresponding GNS classes; density of the orbit is not required. -/
theorem norm_apply_eq_norm_hilbertClassMap (a : A) :
    ‖π a ξ‖ = ‖φ.hilbertClassMap a‖ := by
  calc
    ‖π a ξ‖ = √(⟪ξ, π (star a * a) ξ⟫_ℂ).re := by
      simpa only [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
        ← StarHomClass.map_star, ← map_mul, RCLike.re_to_complex] using
        ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right (π a) ξ
    _ = ‖φ.hilbertClassMap a‖ := by
      rw [hφ, ← sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _),
        Real.sq_sqrt (by simpa using (φ.square_nonneg a).1), φ.norm_hilbertClassMap_sq]

/-- The unitary equivalence from `φ.HilbertGNS` to a cyclic bounded Hilbert-space `⋆`-realization
of `φ`. It sends `φ.hilbertClassMap a` to `π a ξ`. -/
def gnsEquiv : φ.HilbertGNS ≃ₗᵢ[ℂ] H :=
  (LinearEquiv.refl ℂ A).extendOfIsometry φ.hilbertClassMap
    ((ContinuousLinearMap.apply ℂ H ξ).toLinearMap.comp (LinearMap.ofClass π))
    φ.denseRange_hilbertClassMap hcyc (φ.norm_apply_eq_norm_hilbertClassMap π ξ hφ)

/-- The GNS unitary takes an algebra class to the corresponding orbit vector. -/
@[simp]
theorem gnsEquiv_apply_hilbertClassMap (a : A) :
    φ.gnsEquiv π ξ hcyc hφ (φ.hilbertClassMap a) = π a ξ :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

/-- The inverse GNS unitary takes an orbit vector to its algebra class. -/
@[simp]
theorem gnsEquiv_symm_apply (a : A) :
    (φ.gnsEquiv π ξ hcyc hφ).symm (π a ξ) = φ.hilbertClassMap a := by
  apply (φ.gnsEquiv π ξ hcyc hφ).injective
  simp

/-- The GNS unitary intertwines bounded left multiplication with the given representation. -/
@[simp]
theorem gnsEquiv_intertwines {a : A} (ha : Continuous (φ.leftMul a)) (v : φ.HilbertGNS) :
    φ.gnsEquiv π ξ hcyc hφ (φ.hilbertLeftMul ha v) = π a (φ.gnsEquiv π ξ hcyc hφ v) := by
  refine φ.denseRange_hilbertClassMap.induction_on v ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro b
    simp [map_mul]

/-- The inverse GNS unitary intertwines the given representation with bounded left
multiplication. -/
@[simp]
theorem gnsEquiv_symm_intertwines {a : A} (ha : Continuous (φ.leftMul a)) (w : H) :
    (φ.gnsEquiv π ξ hcyc hφ).symm (π a w) =
      φ.hilbertLeftMul ha ((φ.gnsEquiv π ξ hcyc hφ).symm w) := by
  apply (φ.gnsEquiv π ξ hcyc hφ).injective
  simp

/-- Agreement on algebra classes uniquely determines the GNS unitary. -/
theorem gnsEquiv_unique (U : φ.HilbertGNS ≃ₗᵢ[ℂ] H)
    (hU : ∀ a, U (φ.hilbertClassMap a) = π a ξ) : U = φ.gnsEquiv π ξ hcyc hφ := by
  ext v
  exact congrFun (φ.denseRange_hilbertClassMap.equalizer U.continuous
    (φ.gnsEquiv π ξ hcyc hφ).continuous (funext fun a => by simpa using hU a)) v

end NonUnital

section Unital

variable {A H : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : StarPositiveFunctional A) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hcyc : DenseRange (fun a : A => π a ξ))
  (hφ : ∀ a, ⟪ξ, π a ξ⟫_ℂ = φ a)

/-- The GNS unitary intertwines the unital canonical representation with the given one. -/
@[simp↓]
theorem gnsEquiv_intertwines_unital (hA : ∀ a : A, Continuous (φ.leftMul a)) (a : A)
    (v : φ.HilbertGNS) :
    φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ (φ.boundedRepresentation hA a v) =
      π a (φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ v) := by
  rw [φ.boundedRepresentation_apply]
  exact φ.gnsEquiv_intertwines π.toNonUnitalStarAlgHom ξ hcyc hφ (hA a) v

/-- For a unital representation, the GNS unitary preserves the distinguished cyclic vector. -/
@[simp]
theorem gnsEquiv_apply_hilbertCyclicVector :
    φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ φ.hilbertCyclicVector = ξ := by
  simpa [hilbertCyclicVector_def] using
    φ.gnsEquiv_apply_hilbertClassMap π.toNonUnitalStarAlgHom ξ hcyc hφ 1

/-- The inverse GNS unitary intertwines the given unital representation with the canonical one. -/
@[simp]
theorem gnsEquiv_symm_intertwines_unital (hA : ∀ a : A, Continuous (φ.leftMul a)) (a : A)
    (w : H) :
    (φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ).symm (π a w) =
      φ.boundedRepresentation hA a ((φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ).symm w) := by
  rw [φ.boundedRepresentation_apply]
  exact φ.gnsEquiv_symm_intertwines π.toNonUnitalStarAlgHom ξ hcyc hφ (hA a) w

/-- The inverse GNS unitary sends the given cyclic vector to the canonical one. -/
@[simp]
theorem gnsEquiv_symm_apply_self :
    (φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ).symm ξ = φ.hilbertCyclicVector := by
  apply (φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ).injective
  simp

include hcyc hφ in
/-- A cyclic unital Hilbert-space `⋆`-realization of `φ` has a unique unitary intertwiner from
`φ.HilbertGNS` that carries the canonical cyclic vector to `ξ`. -/
theorem existsUnique_gnsEquiv (hA : ∀ a : A, Continuous (φ.leftMul a)) :
    ∃! U : φ.HilbertGNS ≃ₗᵢ[ℂ] H, U φ.hilbertCyclicVector = ξ ∧
      ∀ (a : A) (v : φ.HilbertGNS), U (φ.boundedRepresentation hA a v) = π a (U v) := by
  refine ⟨φ.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hφ, ⟨?_, ?_⟩, ?_⟩
  · exact φ.gnsEquiv_apply_hilbertCyclicVector π ξ hcyc hφ
  · exact φ.gnsEquiv_intertwines_unital π ξ hcyc hφ hA
  · rintro U ⟨hvec, hinter⟩
    apply φ.gnsEquiv_unique π.toNonUnitalStarAlgHom ξ hcyc hφ U
    intro a
    simpa [hvec] using hinter a φ.hilbertCyclicVector

end Unital

end TauCeti.StarPositiveFunctional
