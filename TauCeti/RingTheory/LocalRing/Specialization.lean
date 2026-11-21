/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import TauCeti.LinearAlgebra.TensorProduct.Range
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.RingTheory.OrzechProperty

/-!
# Ranks of split images under specialization over a local ring

Let `R` be a local ring, for instance the ring of rational functions in a parameter `t` that are
regular at a point `τ`. Its residue field is the field of coefficients specialized at `t = τ`, and
when `R` is a domain its fraction field is the field of generic coefficients. A linear map `f`
between finite free `R`-modules extends to both fields, and its two ranks can differ:
multiplication by `t - τ` on `R` has rank one generically and rank zero at `τ`. Specialization
only bounds the rank of `f` above by its generic rank.

The two ranks agree when the range of `f` is a direct summand of the target. Then the range is a
finitely generated projective module, hence free over the local ring `R`
(`Submodule.free_of_isComplemented`), and its extension of scalars to any nontrivial coefficient
ring `A` is the range of `f.baseChange A`, of the same rank
(`LinearMap.finrank_range_baseChange_of_isComplemented`). In particular, an idempotent
endomorphism `E` of a finite projective `R`-module `L` has the same rank after every extension of
scalars (`LinearMap.IsIdempotentElem.finrank_range_baseChange`). This is the constancy of
dimension behind specialization arguments, such as Goodman–Wenzl's classification of the tensor
ideals of the Temperley–Lieb category, where `E(x) = e x f` for idempotents `e` and `f` of a
generic algebra that can be evaluated at `τ`. That `E` is an endomorphism of the lattice `L` is
essential: the map `x ↦ e x f` need not preserve the span of an arbitrary set of diagrams, and the
dimensions of `e L f` before and after specialization can then differ.

For a map with split range, injectivity is also insensitive to specialization: `f.baseChange A` is
injective exactly when `f` is (`LinearMap.baseChange_injective_iff_of_isComplemented`), so a map
that is injective generically stays injective at `τ`.

## Main results

* `Submodule.free_of_isComplemented`: a direct summand of a finite projective module over a local
  ring is free.
* `LinearMap.finrank_range_baseChange_of_isComplemented`: the rank of a linear map with
  complemented range does not change under extension of scalars.
* `LinearMap.IsIdempotentElem.finrank_range_baseChange`: neither does the rank of an idempotent
  endomorphism.
* `LinearMap.baseChange_injective_iff_of_isComplemented`: a linear map with complemented range
  from a finite free module is injective after extension of scalars if and only if it is injective.

## References

* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, appendix to
  M. H. Freedman, *A magnetic model with a possible Chern–Simons phase*, Comm. Math. Phys. 234
  (2003), 129–183, Section 1.
-/

public section

open Module

namespace Submodule

variable {R N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N]
  [Module.Finite R N] [Module.Projective R N]

/-- A direct summand of a finite projective module over a local ring is free: it is again finite
and projective, as the image and a retract of the module under the projection along a complement. -/
theorem free_of_isComplemented {p : Submodule R N} (hp : IsComplemented p) : Module.Free R p := by
  obtain ⟨q, hpq⟩ := hp
  have := Module.Finite.of_surjective _ (projectionOnto_surjective hpq)
  have := Module.Projective.of_split _ _ (projectionOnto_comp_subtype hpq)
  exact Module.free_of_flat_of_isLocalRing

end Submodule

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- **The rank of a map with split range is constant under specialization.** If the range of a
linear map `f` into a finite projective module over a local ring `R` is a direct summand, then
`f.baseChange A` has the same rank over every nontrivial commutative `R`-algebra `A`, for instance
over the fraction field and over the residue field of `R`. -/
theorem finrank_range_baseChange_of_isComplemented (f : M →ₗ[R] N)
    (hf : IsComplemented (range f)) (A : Type*) [CommSemiring A] [Nontrivial A] [Algebra R A] :
    finrank A (range (f.baseChange A)) = finrank R (range f) := by
  have := Submodule.free_of_isComplemented hf
  rw [← baseChange_range, Submodule.finrank_baseChange_of_isComplemented hf]

/-- **Constancy of dimension.** An idempotent endomorphism `E` of a finite projective module over
a local ring `R` has the same rank after extension of scalars to every nontrivial commutative
`R`-algebra `A`. In particular, its ranks over the fraction field and over the residue field of
`R` agree. -/
theorem IsIdempotentElem.finrank_range_baseChange {E : Module.End R N} (hE : IsIdempotentElem E)
    (A : Type*) [CommSemiring A] [Nontrivial A] [Algebra R A] :
    finrank A (range (E.baseChange A)) = finrank R (range E) :=
  finrank_range_baseChange_of_isComplemented E ⟨_, IsIdempotentElem.isCompl hE⟩ A

/- The generic and the special rank of an idempotent over a local domain agree. -/
example [IsDomain R] {E : Module.End R N} (hE : IsIdempotentElem E) :
    finrank (FractionRing R) (range (E.baseChange (FractionRing R))) =
      finrank (IsLocalRing.ResidueField R) (range (E.baseChange (IsLocalRing.ResidueField R))) := by
  rw [IsIdempotentElem.finrank_range_baseChange hE, IsIdempotentElem.finrank_range_baseChange hE]

/-- **Injectivity of a map with split range is insensitive to specialization.** A linear map
`f` from a finite free module into a finite projective module over a local ring `R`, whose range is
a direct summand, is injective after extension of scalars to a nontrivial commutative `R`-algebra
`A` if and only if it is injective. So `f` is injective over the fraction field of `R` exactly when
it is injective over the residue field. -/
theorem baseChange_injective_iff_of_isComplemented [Module.Finite R M] [Module.Free R M]
    {f : M →ₗ[R] N} (hf : IsComplemented (range f)) (A : Type*) [CommSemiring A] [Nontrivial A]
    [Algebra R A] :
    Function.Injective (f.baseChange A) ↔ Function.Injective f := by
  refine ⟨fun h => ?_, fun h => baseChange_injective_of_isComplemented h hf⟩
  have := Submodule.free_of_isComplemented hf
  have hrank : finrank R (range f) = finrank R M := by
    rw [← finrank_range_baseChange_of_isComplemented f hf A, finrank_range_of_inj h,
      finrank_baseChange]
  -- Identifying the range of `f` with its source, which is free of the same finite rank, turns the
  -- surjection of `f` onto its range into a surjective endomorphism, which is injective.
  let e := LinearEquiv.ofFinrankEq _ _ hrank
  have hinj : Function.Injective (e.toLinearMap ∘ₗ f.rangeRestrict) :=
    OrzechProperty.injective_of_surjective_endomorphism _
      (e.surjective.comp f.surjective_rangeRestrict)
  rw [coe_comp] at hinj
  rw [← ker_eq_bot, ← ker_rangeRestrict, ker_eq_bot]
  exact hinj.of_comp

end LinearMap
