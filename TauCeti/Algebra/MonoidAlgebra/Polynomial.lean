/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Lifting polynomials over monoid algebras along monoid homomorphisms

For an injective homomorphism `f : M →* N` of monoids (or `f : M →+ N` of additive monoids), a
polynomial over `R[N]` lies in `Polynomial.lifts (mapDomainRingHom R f)` if and only if the support
of each nonzero coefficient lies in `Set.range f` (`MonoidAlgebra.mem_lifts_mapDomainRingHom_iff`
and `AddMonoidAlgebra.mem_lifts_mapDomainRingHom_iff`). This packages the finite-support subgroup
reduction for polynomial equations over monoid and group algebras.
-/

public section

namespace MonoidAlgebra

variable {R M N : Type*} [CommSemiring R] [Monoid M] [Monoid N]

/-- For an injective monoid homomorphism `f : M →* N`, a polynomial over `R[N]` lifts to `R[M]`
along `mapDomainRingHom R f` if and only if the support of each of its coefficients lies in
`Set.range f`. -/
@[to_additive (dont_translate := R)
/-- For an injective additive monoid homomorphism `f : M →+ N`, a polynomial over `R[N]` lifts to
`R[M]` along `mapDomainRingHom R f` if and only if the support of each of its coefficients lies in
`Set.range f`. -/]
theorem mem_lifts_mapDomainRingHom_iff {f : M →* N} (hf : Function.Injective f)
    (p : Polynomial (MonoidAlgebra R N)) :
    p ∈ Polynomial.lifts (mapDomainRingHom R f) ↔
      ∀ i ∈ p.support, ∀ n ∈ (p.coeff i).coeff.support, n ∈ Set.range f := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  refine ⟨fun h i _ ↦ (mem_range_mapDomain_iff hf (p.coeff i)).mp (by simpa using h i),
    fun h i ↦ ?_⟩
  by_cases hi : i ∈ p.support
  · simpa using (mem_range_mapDomain_iff hf (p.coeff i)).mpr (h i hi)
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hi]⟩

end MonoidAlgebra
