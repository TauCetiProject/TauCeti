/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Projection

/-!
# Complements of submodules of projective modules

A submodule with a complement in a projective module is projective: the inclusion is split by the
projection onto it. In particular the range of an idempotent endomorphism of a projective module,
complemented by its kernel, is projective. So is the quotient by a complemented submodule, which is
isomorphic to the complement. Conversely, the kernel of a surjection onto a projective module has a
complement, the image of a section. Hence a linear map into a projective module with projective
cokernel has complemented range and kernel, and every linear map out of a submodule with projective
quotient extends to the ambient module.

## Main results

* `Module.Projective.of_isCompl`: a submodule with a complement in a projective module is
  projective.
* `LinearMap.IsIdempotentElem.projective_range`: the range of an idempotent endomorphism of a
  projective module is projective.
* `Module.Projective.quotient_of_isCompl`: the quotient of a projective module by a submodule with
  a complement is projective.
* `LinearMap.isComplemented_ker_of_surjective`: the kernel of a surjection onto a projective
  module is a direct summand.
* `Submodule.isComplemented_of_projective_quotient`: a submodule with projective quotient is a
  direct summand.
* `LinearMap.isComplemented_range_of_projective_quotient`,
  `LinearMap.isComplemented_ker_of_projective_quotient`: a map into a projective module with
  projective cokernel has complemented range and kernel.
* `LinearMap.surjective_comp_subtype_of_projective_quotient`: linear maps extend from a submodule
  with projective quotient; `Submodule.dualRestrict_surjective_of_projective_quotient` is the case
  of functionals.
-/

public section

/-- A submodule with a complement in a projective module is projective: the inclusion is split by
the projection onto it. -/
theorem Module.Projective.of_isCompl {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Module.Projective R M] {T T' : Submodule R M} (hcompl : IsCompl T T') :
    Module.Projective R T :=
  Module.Projective.of_split T.subtype (T.projectionOnto T' hcompl) (by ext x; simp)

/-- The range of an idempotent endomorphism `p` of a projective module is projective: the
inclusion is split by `p` itself. -/
theorem LinearMap.IsIdempotentElem.projective_range {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Module.Projective R M] {p : M →ₗ[R] M} (hp : IsIdempotentElem p) :
    Module.Projective R (LinearMap.range p) :=
  .of_split (LinearMap.range p).subtype p.rangeRestrict <|
    LinearMap.ext fun v ↦ Subtype.ext ((mem_range_iff hp).1 v.property)

/-- The quotient of a projective module by a submodule with a complement is projective: it is
isomorphic to the complement. -/
theorem Module.Projective.quotient_of_isCompl {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Module.Projective R M] {T T' : Submodule R M} (hcompl : IsCompl T T') :
    Module.Projective R (M ⧸ T) :=
  have := Module.Projective.of_isCompl hcompl.symm
  Module.Projective.of_equiv (T.quotientEquivOfIsCompl T' hcompl).symm

namespace LinearMap

variable {R N P : Type*} [Ring R] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The kernel of a surjection onto a projective module is a direct summand. -/
theorem isComplemented_ker_of_surjective [Module.Projective R P] (g : N →ₗ[R] P)
    (hg : Function.Surjective g) : IsComplemented (ker g) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  -- `s ∘ g` is an idempotent with the same kernel as `g`, since `s` is injective.
  have hidem : IsIdempotentElem (s ∘ₗ g) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, comp_assoc, ← comp_assoc g s g, hs, id_comp]
  rw [← ker_comp_of_ker_eq_bot g (ker_eq_bot_of_inverse hs)]
  exact ⟨_, (LinearMap.IsIdempotentElem.isCompl hidem).symm⟩

/-- A submodule with projective quotient is a direct summand: it is the kernel of the quotient
map. -/
theorem _root_.Submodule.isComplemented_of_projective_quotient (W : Submodule R N)
    [Module.Projective R (N ⧸ W)] : IsComplemented W := by
  simpa using isComplemented_ker_of_surjective W.mkQ W.mkQ_surjective

variable {M : Type*} [AddCommGroup M] [Module R M] (f : M →ₗ[R] N)

/-- A linear map whose cokernel is projective has complemented range. -/
theorem isComplemented_range_of_projective_quotient [Module.Projective R (N ⧸ range f)] :
    IsComplemented (range f) :=
  (range f).isComplemented_of_projective_quotient

/-- A linear map into a projective module whose cokernel is projective has complemented
kernel. -/
theorem isComplemented_ker_of_projective_quotient [Module.Projective R N]
    [Module.Projective R (N ⧸ range f)] : IsComplemented (ker f) := by
  obtain ⟨q, hq⟩ := f.isComplemented_range_of_projective_quotient
  have := Module.Projective.of_isCompl hq
  simpa using isComplemented_ker_of_surjective f.rangeRestrict f.surjective_rangeRestrict

/-- **Linear maps extend from a submodule with projective quotient**, which is a direct summand:
every linear map `W → N` is the restriction of a linear map `M → N`. -/
theorem surjective_comp_subtype_of_projective_quotient {W : Submodule R M}
    [Module.Projective R (M ⧸ W)] : Function.Surjective fun φ : M →ₗ[R] N ↦ φ ∘ₗ W.subtype :=
  surjective_comp_subtype_of_isComplemented W.isComplemented_of_projective_quotient

end LinearMap

/-- **Functionals extend from a submodule with projective quotient**: restriction of functionals
`M^∨ → W^∨` is surjective. This is the ring analogue of `Subspace.dualRestrict_surjective`. -/
theorem Submodule.dualRestrict_surjective_of_projective_quotient {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {W : Submodule R M} [Module.Projective R (M ⧸ W)] :
    Function.Surjective W.dualRestrict := fun ψ ↦ by
  obtain ⟨φ, hφ⟩ := LinearMap.surjective_comp_subtype_of_projective_quotient (N := R) (W := W) ψ
  exact ⟨φ, LinearMap.ext fun x ↦ by
    rw [Submodule.dualRestrict_apply, ← hφ, LinearMap.comp_apply, Submodule.subtype_apply]⟩
