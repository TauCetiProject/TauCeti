/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SymmetricAlgebra.HilbertIdeal
public import TauCeti.RingTheory.GradedAlgebra.ModuleGenerators

/-!
# Homogeneous generators over polynomial invariants

For a finite group acting on a finite-dimensional vector space `M`, the symmetric algebra
`S = Sym M` has a finite homogeneous generating family over its invariant subalgebra `A` whose
classes form a basis of the coinvariant algebra `S / A₊ S`. Thus these lifts give a minimal
homogeneous presentation: every coefficient in a relation among them has zero constant term.

The construction applies in every characteristic, including the modular case. Generation and
minimality alone do not imply that the lifted elements form an `A`-basis. They supply the
presentation used to deduce freeness once its kernel is shown to vanish.

For polynomial functions on a representation `V`, apply the results to the contragredient
representation on `M = V*`.

## References

* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 2 and § 7.2.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §§ 17–18.

The construction uses `Representation.moduleFinite_quotient_symmetricAlgebraHilbertIdeal` and
graded Nakayama in `Subalgebra.span_eq_top_of_span_quotient_eq_top`.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

section CommRing

variable {R G M : Type*} [CommRing R] [Monoid G] [AddCommMonoid M] [Module R M]
  (ρ : Representation R G M)

/-- The class of an invariant modulo the Hilbert ideal is its constant term. -/
@[simp]
theorem mk_symmetricAlgebraHilbertIdeal_coe (a : ρ.symmetricAlgebraInvariants) :
    Ideal.Quotient.mk ρ.symmetricAlgebraHilbertIdeal (a : SymmetricAlgebra R M) =
      algebraMap R (SymmetricAlgebra R M ⧸ ρ.symmetricAlgebraHilbertIdeal)
        (SymmetricAlgebra.algebraMapInv (a : SymmetricAlgebra R M)) := by
  have ha : (a : SymmetricAlgebra R M) - algebraMap R _
      (SymmetricAlgebra.algebraMapInv (a : SymmetricAlgebra R M)) ∈
        ρ.symmetricAlgebraHilbertIdeal := by
    apply ρ.mem_symmetricAlgebraHilbertIdeal_of_mem
    · exact ρ.symmetricAlgebraInvariants.sub_mem a.2
        (ρ.symmetricAlgebraInvariants.algebraMap_mem _)
    · rw [← HomogeneousIdeal.mem_iff, toIdeal_irrelevant_eq_ker_algebraMapInv,
        RingHom.mem_ker]
      simp
  rw [IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M), Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.eq.mpr ha

/-- Relations between lifts of linearly independent coinvariant classes have coefficients
with zero constant term. This is minimality of the presentation over the invariants. -/
theorem algebraMapInv_eq_zero_of_sum_smul_eq_zero {ι : Type*}
    (b : ι → SymmetricAlgebra R M)
    (hb : LinearIndependent R (fun i ↦ Ideal.Quotient.mk ρ.symmetricAlgebraHilbertIdeal (b i)))
    (s : Finset ι) (c : ι → ρ.symmetricAlgebraInvariants)
    (hc : ∑ i ∈ s, c i • b i = 0) {i : ι} (hi : i ∈ s) :
    SymmetricAlgebra.algebraMapInv (c i : SymmetricAlgebra R M) = 0 := by
  apply linearIndependent_iff'.1 hb s
    (fun j ↦ SymmetricAlgebra.algebraMapInv (c j : SymmetricAlgebra R M)) ?_ i hi
  have h := congrArg (Ideal.Quotient.mk ρ.symmetricAlgebraHilbertIdeal) hc
  simpa only [map_sum, map_zero, Subalgebra.smul_def, smul_eq_mul, map_mul,
    ρ.mk_symmetricAlgebraHilbertIdeal_coe, ← Algebra.smul_def] using h

end CommRing

universe u v

variable {K : Type u} {M : Type v} {G : Type*}
  [Field K] [Group G] [Finite G] [AddCommMonoid M]
  [Module K M] [Module.Finite K M]
  (σ : Representation K G M)

/-- A finite group acting on a finite-dimensional space has a finite homogeneous generating
family for its symmetric algebra over the invariants whose coinvariant classes form a basis.
No assumption on the characteristic or on generation by reflections is required. -/
theorem exists_homogeneous_generators_symmetricAlgebra :
    ∃ (ι : Type (max u v)) (_ : Finite ι) (b : ι → SymmetricAlgebra K M) (d : ι → ℕ),
      (∀ i, b i ∈ homogeneousSubmodule K M (d i)) ∧
      LinearIndependent K (fun i ↦ Ideal.Quotient.mk σ.symmetricAlgebraHilbertIdeal (b i)) ∧
      Submodule.span K (Set.range fun i ↦ Ideal.Quotient.mk
        σ.symmetricAlgebraHilbertIdeal (b i)) = ⊤ ∧
      Submodule.span σ.symmetricAlgebraInvariants (Set.range b) = ⊤ := by
  have hI := σ.symmetricAlgebraHilbertIdeal_eq_span
  have : Module.Finite K (SymmetricAlgebra K M ⧸ Ideal.span
      {p | p ∈ σ.symmetricAlgebraInvariants ∧
        ∃ n, 0 < n ∧ p ∈ homogeneousSubmodule K M n}) :=
    hI ▸ σ.moduleFinite_quotient_symmetricAlgebraHilbertIdeal
  rw [hI]
  exact TauCeti.GradedAlgebra.exists_homogeneous_generators_of_finite_quotient
      (homogeneousSubmodule K M) σ.symmetricAlgebraInvariants
      σ.isHomogeneous_symmetricAlgebraInvariants

end Representation
