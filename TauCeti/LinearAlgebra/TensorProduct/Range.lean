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
import TauCeti.LinearAlgebra.TensorProduct.Tower

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
commutative coefficient algebra. For a submodule without a complement this fails: the submodule
`2ℤ` of `ℤ` is free of rank one, while its extension to `ZMod 2` is zero.

Applied to the range of a linear map `f`, this says that when the range of `f` is a free direct
summand of the target, `f.baseChange A` has the same rank as `f`. If moreover the source of `f` is
finite free, then `f.baseChange A` is injective exactly when `f` is: in the converse direction the
ranks show that the surjection of `f` onto its range is a surjection between finite free modules
of the same rank, hence bijective.

## Main results

* `Submodule.one_tmul_mem_baseChange_iff`: a vector belongs to a submodule exactly when its
  canonical image belongs to the extended submodule, for a faithfully flat coefficient algebra.
* `LinearMap.one_tmul_mem_range_baseChange_iff`: a vector belongs to a range exactly when its
  canonical image belongs to the extended range, for a faithfully flat coefficient algebra.
* `Submodule.baseChange_subtype_injective_of_isComplemented`: the inclusion of a complemented
  submodule stays injective after extension of scalars.
* `LinearMap.baseChange_injective_of_isComplemented`: so does every injective linear map with
  complemented range.
* `Submodule.rank_baseChange_of_isComplemented`, `Submodule.finrank_baseChange_of_isComplemented`:
  extension of scalars to a nontrivial commutative coefficient algebra preserves the rank of a free
  complemented submodule.
* `LinearMap.finrank_range_baseChange_of_isComplemented`: the same for the rank of a linear map
  whose range is a free direct summand.
* `LinearMap.baseChange_injective_iff_of_isComplemented`: a linear map from a finite free module
  whose range is a free direct summand is injective after extension of scalars to a nontrivial
  commutative coefficient algebra if and only if it is injective.
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

universe u v w

variable {R : Type u} {A : Type v} {M : Type w} [CommRing R] [AddCommGroup M] [Module R M]

/-- The inclusion of a complemented submodule stays injective after extension of scalars, for every
coefficient algebra: the projection onto the submodule along a complement is a left inverse of the
inclusion, and so is its extension of scalars. -/
theorem baseChange_subtype_injective_of_isComplemented [Semiring A] [Algebra R A]
    (p : Submodule R M) (hp : IsComplemented p) : Function.Injective (p.subtype.baseChange A) := by
  obtain ⟨q, hpq⟩ := hp
  exact (LinearMap.baseChange_leftInverse (projectionOnto_comp_subtype hpq)).injective

/-- **Extension of scalars preserves the rank of a free complemented submodule**: the extension
`p.baseChange A ⊆ A ⊗[R] M` of a complemented submodule `p` that is free over `R` has the same rank
over any nontrivial commutative coefficient algebra `A` as `p` has over `R`. -/
theorem rank_baseChange_of_isComplemented [CommSemiring A] [Nontrivial A] [Algebra R A]
    (p : Submodule R M) [Module.Free R p] (hp : IsComplemented p) :
    Module.rank A (p.baseChange A) = Cardinal.lift.{v} (Module.rank R p) := by
  have := (algebraMap R A).domain_nontrivial
  rw [baseChange,
    rank_range_of_injective _ (p.baseChange_subtype_injective_of_isComplemented hp),
    Module.rank_baseChange]

/-- Extension of scalars to a nontrivial commutative coefficient algebra preserves the finite rank
of a free complemented submodule. -/
theorem finrank_baseChange_of_isComplemented [CommSemiring A] [Nontrivial A] [Algebra R A]
    (p : Submodule R M) [Module.Free R p] (hp : IsComplemented p) :
    Module.finrank A (p.baseChange A) = Module.finrank R p := by
  rw [Module.finrank, p.rank_baseChange_of_isComplemented hp, Cardinal.toNat_lift, Module.finrank]

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

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An injective linear map with complemented range stays injective after extension of scalars,
for every coefficient algebra: it is an isomorphism onto a direct summand of its target. -/
theorem baseChange_injective_of_isComplemented [Semiring A] [Algebra R A] (f : M →ₗ[R] N)
    (hf : Function.Injective f) (hc : IsComplemented (range f)) :
    Function.Injective (f.baseChange A) := by
  have hfe : f = (range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap :=
    LinearMap.ext fun x => (LinearEquiv.ofInjective_apply f (h := hf) x).symm
  rw [hfe, baseChange_comp, coe_comp, ← LinearEquiv.coe_baseChange]
  exact ((range f).baseChange_subtype_injective_of_isComplemented hc).comp
    (LinearEquiv.injective _)

/-- **The rank of a map with free split range is invariant under extension of scalars.** If the
range of a linear map `f` is a free direct summand of its target, then `f.baseChange A` has the
same rank as `f` over every nontrivial commutative `R`-algebra `A`. -/
theorem finrank_range_baseChange_of_isComplemented (f : M →ₗ[R] N) [Module.Free R (range f)]
    (hf : IsComplemented (range f)) (A : Type*) [CommSemiring A] [Nontrivial A] [Algebra R A] :
    Module.finrank A (range (f.baseChange A)) = Module.finrank R (range f) := by
  rw [← baseChange_range, (range f).finrank_baseChange_of_isComplemented hf]

/-- **Injectivity of a map with free split range is invariant under extension of scalars.** A
linear map `f` from a finite free module, whose range is a free direct summand of its target, is
injective after extension of scalars to a nontrivial commutative `R`-algebra `A` if and only if it
is injective. -/
theorem baseChange_injective_iff_of_isComplemented [Module.Finite R M] [Module.Free R M]
    (f : M →ₗ[R] N) [Module.Free R (range f)] (hf : IsComplemented (range f)) (A : Type*)
    [CommSemiring A] [Nontrivial A] [Algebra R A] :
    Function.Injective (f.baseChange A) ↔ Function.Injective f := by
  refine ⟨fun h => ?_, fun h => f.baseChange_injective_of_isComplemented h hf⟩
  have := (algebraMap R A).domain_nontrivial
  have hrank : Module.finrank R (range f) = Module.finrank R M := by
    rw [← f.finrank_range_baseChange_of_isComplemented hf A, finrank_range_of_inj h,
      Module.finrank_baseChange]
  exact (injective_rangeRestrict_iff f).mp (OrzechProperty.bijective_of_surjective_of_finrank_le
    f.rangeRestrict f.surjective_rangeRestrict hrank.ge).1

end Complemented

end LinearMap
