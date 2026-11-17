/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Ranges after extension of scalars

If the coefficient algebra is faithfully flat, membership of a vector in the range of a linear map
can be checked after extension of scalars.  This is the linear-algebraic descent step used when an
equation acquires a solution after passing to a larger field.

Membership in a submodule is the case of a cyclic submodule in `Submodule.baseChange_le_iff` from
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`: faithfully flat extension of scalars reflects
inclusions of submodules.  The statement for ranges follows because extension of scalars commutes
with ranges, `LinearMap.baseChange_range`.

Without any flatness, extension of scalars still behaves well on a submodule `p` with a
complement: the projection onto `p` along the complement is a left inverse of the inclusion, so the
inclusion stays injective after extension of scalars and `p.baseChange A` is a copy of `A ⊗[R] p`.
When `p` is free its rank is therefore unchanged by every extension of scalars to a nontrivial
coefficient ring. For a submodule without a complement this fails: the submodule `2ℤ` of `ℤ` is free
of rank one, while its extension to `ZMod 2` is zero.

## Main results

* `Submodule.one_tmul_mem_baseChange_iff`: a vector belongs to a submodule exactly when its
  canonical image belongs to the extended submodule, for a faithfully flat coefficient algebra.
* `LinearMap.one_tmul_mem_range_baseChange_iff`: a vector belongs to a range exactly when its
  canonical image belongs to the extended range, for a faithfully flat coefficient algebra.
* `Submodule.baseChange_subtype_injective_of_isComplemented`: the inclusion of a complemented
  submodule stays injective after extension of scalars.
* `LinearMap.baseChange_injective_of_isComplemented`: so does every injective linear map with
  complemented range.
* `Submodule.finrank_baseChange_of_isComplemented`: extension of scalars to a nontrivial
  coefficient ring preserves the rank of a free complemented submodule.
-/

public section

open TensorProduct

namespace Submodule

universe u v w

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M]

/-- Over a faithfully flat coefficient algebra, a vector belongs to a submodule exactly when its
canonical image belongs to the extension of that submodule. -/
@[simp]
theorem one_tmul_mem_baseChange_iff [Module.FaithfullyFlat R A]
    (p : Submodule R M) (m : M) :
    (1 : A) ⊗ₜ[R] m ∈ p.baseChange A ↔ m ∈ p := by
  simpa using baseChange_le_iff (A := A) (p := span R {m}) (q := p)

end Submodule

namespace Submodule

variable {R A M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Submodule R M}

/-- The inclusion of a complemented submodule stays injective after extension of scalars, for every
coefficient algebra: the projection onto the submodule along a complement is a left inverse of the
inclusion, and so is its extension of scalars. -/
theorem baseChange_subtype_injective_of_isComplemented [Semiring A] [Algebra R A]
    (hp : IsComplemented p) : Function.Injective (p.subtype.baseChange A) := by
  obtain ⟨q, hpq⟩ := hp
  refine Function.LeftInverse.injective (g := (p.projectionOnto q hpq).baseChange A) fun x => ?_
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, projectionOnto_comp_subtype,
    LinearMap.baseChange_id, LinearMap.id_apply]

/-- **Extension of scalars preserves the rank of a free complemented submodule**: the extension
`p.baseChange A ⊆ A ⊗[R] M` of a complemented submodule `p` that is free over `R` has the same rank
over any nontrivial commutative coefficient algebra `A` as `p` has over `R`. -/
theorem finrank_baseChange_of_isComplemented [CommSemiring A] [Nontrivial A] [Algebra R A]
    [Module.Free R p] (hp : IsComplemented p) :
    Module.finrank A (p.baseChange A) = Module.finrank R p := by
  have := (algebraMap R A).domain_nontrivial
  rw [baseChange,
    LinearMap.finrank_range_of_inj (baseChange_subtype_injective_of_isComplemented hp),
    Module.finrank_baseChange]

end Submodule

namespace LinearMap

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w} {N : Type x}

section Descent

variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Over a faithfully flat coefficient algebra, a vector belongs to the range of a linear map if
and only if its canonical image belongs to the range after extension of scalars. -/
theorem one_tmul_mem_range_baseChange_iff [Module.FaithfullyFlat R A]
    (f : M →ₗ[R] N) (y : N) :
    (1 : A) ⊗ₜ[R] y ∈ range (f.baseChange A) ↔ y ∈ range f := by
  rw [← baseChange_range, Submodule.one_tmul_mem_baseChange_iff]

end Descent

section Complemented

variable [CommRing R] [Semiring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An injective linear map with complemented range stays injective after extension of scalars,
for every coefficient algebra: it is an isomorphism onto a direct summand of its target. -/
theorem baseChange_injective_of_isComplemented {f : M →ₗ[R] N} (hf : Function.Injective f)
    (hc : IsComplemented (range f)) : Function.Injective (f.baseChange A) := by
  have hfe : f = (range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap := by
    ext; simp
  rw [hfe, baseChange_comp, coe_comp, ← LinearEquiv.coe_baseChange]
  exact (Submodule.baseChange_subtype_injective_of_isComplemented hc).comp
    (LinearEquiv.injective _)

end Complemented

end LinearMap
