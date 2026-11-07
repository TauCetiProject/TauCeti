/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Unitary uniqueness of the cyclic GNS representation

A cyclic vector representation of a positive functional is unitarily equivalent to its
canonical GNS representation. `PositiveLinearMap.gnsEquiv` sends the class of `a` to
`π a ξ`, intertwines the representations, and is uniquely characterized by this class-map
formula. This construction also applies to nonunital C⋆-algebras, provided the orbit of the
given vector is dense. Neither faithfulness nor normalization of the functional is required.

For a unital representation, `PositiveLinearMap.existsUnique_gnsEquiv` gives the usual
uniqueness statement in terms of the cyclic vector and the intertwining identity. Thus
concrete cyclic models can be identified with GNS without choosing bases or representatives
of null classes. Zero functionals and zero Hilbert spaces are included.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open scoped InnerProductSpace ComplexOrder

namespace PositiveLinearMap

variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hcyc : DenseRange (fun a : A => π a ξ))
  (hf : ∀ a, inner ℂ ξ (π a ξ) = f a)

include hf in
/-- A vector realization of a positive functional gives orbit vectors the same norms as
the corresponding GNS classes; density of the orbit is not required. -/
theorem norm_apply_eq_norm_toGNS (a : A) : ‖π a ξ‖ = ‖f.toGNS a‖ := by
  calc
    ‖π a ξ‖ = √(inner ℂ ξ (π (star a * a) ξ)).re := by
      simpa only [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
        ← map_star, ← map_mul, RCLike.re_to_complex] using
        ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right (π a) ξ
    _ = ‖f.toGNS a‖ := by
      simp only [hf, toGNS_apply, UniformSpace.Completion.norm_coe, preGNS_norm_def,
        ofPreGNS_toPreGNS]

/-- The unitary from the canonical GNS space to a cyclic vector realization of the same
positive functional. It sends the class of `a` to `π a ξ`. -/
noncomputable def gnsEquiv : f.GNS ≃ₗᵢ[ℂ] H :=
  (LinearEquiv.refl ℂ A).extendOfIsometry f.toGNS.toLinearMap
    ((ContinuousLinearMap.apply ℂ H ξ).toLinearMap.comp (LinearMap.ofClass π))
    f.denseRange_toGNS hcyc (f.norm_apply_eq_norm_toGNS π ξ hf)

/-- The GNS unitary takes an algebra class to the corresponding orbit vector. -/
@[simp]
theorem gnsEquiv_apply_coe (a : A) :
    f.gnsEquiv π ξ hcyc hf (f.toPreGNS a : f.GNS) = π a ξ := by
  rw [← toGNS_apply]
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

/-- The inverse GNS unitary takes an orbit vector to its algebra class. -/
@[simp]
theorem gnsEquiv_symm_apply (a : A) :
    (f.gnsEquiv π ξ hcyc hf).symm (π a ξ) = (f.toPreGNS a : f.GNS) := by
  apply (f.gnsEquiv π ξ hcyc hf).injective
  simp

/-- The GNS unitary intertwines the canonical representation with the given one. -/
@[simp]
theorem gnsEquiv_intertwines (a : A) (v : f.GNS) :
    f.gnsEquiv π ξ hcyc hf (f.gnsNonUnitalStarAlgHom a v) =
      π a (f.gnsEquiv π ξ hcyc hf v) := by
  refine f.denseRange_toGNS.induction_on v ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro b
    simp [toGNS_apply, map_mul]

/-- Agreement on algebra classes uniquely determines the GNS unitary. -/
theorem gnsEquiv_unique (U : f.GNS ≃ₗᵢ[ℂ] H)
    (hU : ∀ a, U (f.toGNS a) = π a ξ) : U = f.gnsEquiv π ξ hcyc hf := by
  ext v
  exact congrFun (f.denseRange_toGNS.equalizer U.continuous
    (f.gnsEquiv π ξ hcyc hf).continuous (by funext a; simpa using hU a)) v

end PositiveLinearMap

namespace PositiveLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hcyc : DenseRange (fun a : A => π a ξ))
  (hf : ∀ a, inner ℂ ξ (π a ξ) = f a)

/-- The GNS unitary intertwines the unital canonical representation with the given one. -/
-- Rewrite before `gnsStarAlgHom_apply` replaces the unital representation in the argument.
@[simp↓]
theorem gnsEquiv_intertwines_unital (a : A) (v : f.GNS) :
    f.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hf (f.gnsStarAlgHom a v) =
      π a (f.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hf v) :=
  f.gnsEquiv_intertwines π.toNonUnitalStarAlgHom ξ hcyc hf a v

/-- For a unital representation the GNS unitary preserves the distinguished cyclic vector. -/
@[simp]
theorem gnsEquiv_apply_gnsVector :
    f.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hf f.gnsVector = ξ := by
  simpa [toGNS_apply, gnsVector_def] using
    f.gnsEquiv_apply_coe π.toNonUnitalStarAlgHom ξ hcyc hf 1

include hcyc hf in
/-- A cyclic unital vector realization of a positive functional has a unique unitary
intertwiner from GNS that sends the canonical cyclic vector to the given vector. -/
theorem existsUnique_gnsEquiv :
    ∃! U : f.GNS ≃ₗᵢ[ℂ] H, U f.gnsVector = ξ ∧
      ∀ (a : A) (v : f.GNS), U (f.gnsStarAlgHom a v) = π a (U v) := by
  refine ⟨f.gnsEquiv π.toNonUnitalStarAlgHom ξ hcyc hf, ⟨?_, ?_⟩, ?_⟩
  · exact f.gnsEquiv_apply_gnsVector π ξ hcyc hf
  · exact f.gnsEquiv_intertwines_unital π ξ hcyc hf
  · rintro U ⟨hvec, hinter⟩
    apply f.gnsEquiv_unique π.toNonUnitalStarAlgHom ξ hcyc hf U
    intro a
    simpa [hvec] using hinter a f.gnsVector

end PositiveLinearMap
