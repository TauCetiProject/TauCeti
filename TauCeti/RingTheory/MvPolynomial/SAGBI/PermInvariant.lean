/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.PermInvariant
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Basic

/-!
# Leading exponents of permutation invariants

Let `G` be a finite subgroup of the permutation group of the variables `σ` (for instance, any
permutation group of finitely many variables), and let `m` be a
monomial order. The coefficients of a `G`-invariant polynomial are constant on the `G`-orbits of
exponents, so its leading exponent `e` is the largest exponent of its orbit: renaming by any
`g ∈ G` gives `m.toSyn (e.mapDomain g) ≤ m.toSyn e`. Conversely, if `e` is the largest exponent of
its orbit, the orbit sum `TauCeti.MvPolynomial.orbitSum R G e` is monic with leading exponent `e`.

Hence, over coefficients without zero divisors, the leading exponents of the invariant subalgebra
`TauCeti.MvPolynomial.permInvariants R G` are exactly the exponents that are largest in their orbits
(`MonomialOrder.mem_leadingExponents_permInvariants_iff`), and the orbit sums form a SAGBI basis of
the invariant subalgebra for every monomial order (`MonomialOrder.isSAGBIBasis_range_orbitSum`).
When `σ` is nonempty and `R` is nontrivial, this orbit-sum SAGBI basis is infinite. Over a field,
the invariant subalgebra has a finite SAGBI basis exactly when the monoid of orbit-maximal exponents
is finitely generated
(`MonomialOrder.exists_finite_isSAGBIBasis_iff_fg`); this is the monoid through which finite SAGBI
bases of permutation invariants are classified.

## Main results

* `MonomialOrder.toSyn_mapDomain_degree_le_of_mem_permInvariants`: the leading exponent of an
  invariant polynomial is the largest exponent of its orbit.
* `MonomialOrder.degree_orbitSum`, `MonomialOrder.monic_orbitSum`: the orbit sum of an
  orbit-maximal exponent is monic with that leading exponent.
* `MonomialOrder.mem_leadingExponents_permInvariants_iff`: the leading exponents of the invariant
  subalgebra are the orbit-maximal exponents.
* `MonomialOrder.isSAGBIBasis_range_orbitSum`: the orbit sums form a SAGBI basis of the invariant
  subalgebra.

## References

* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Math. **1430**, Springer, 1990, 61–87.
* M. Göbel, *Computing bases for rings of permutation-invariant polynomials*, J. Symbolic Comput.
  **19** (1995), 285–291.
* N. M. Thiéry, S. Thomassé, *Convex cones and SAGBI bases of permutation invariants*,
  arXiv:math/0607380.
-/

public section

namespace MonomialOrder

open MvPolynomial TauCeti.MvPolynomial

variable {σ R : Type*} [CommSemiring R] (m : MonomialOrder σ) {G : Subgroup (Equiv.Perm σ)}
  {e : σ →₀ ℕ} {p : MvPolynomial σ R}

/-- The leading exponent of a `G`-invariant polynomial is the largest exponent of its `G`-orbit. -/
theorem toSyn_mapDomain_degree_le_of_mem_permInvariants (hp : p ∈ permInvariants R G)
    {g : Equiv.Perm σ} (hg : g ∈ G) :
    m.toSyn ((m.degree p).mapDomain g) ≤ m.toSyn (m.degree p) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  refine m.le_degree (mem_support_iff.2 ?_)
  rw [mem_permInvariants_iff_forall_coeff_mapDomain.1 hp g hg]
  exact m.coeff_degree_ne_zero_iff.2 hp0

variable [Finite G]

variable (G) in
/-- Every `G`-orbit of exponents has a largest element for the monomial order. -/
theorem exists_permOrbitRel_forall_toSyn_mapDomain_le (e : σ →₀ ℕ) :
    ∃ f, permOrbitRel G e f ∧ ∀ g ∈ G, m.toSyn (f.mapDomain g) ≤ m.toSyn f := by
  obtain ⟨f, hf, hmax⟩ := (finite_setOf_permOrbitRel G e).toFinset.exists_max_image m.toSyn
    ⟨e, by simp⟩
  rw [Set.Finite.mem_toFinset] at hf
  refine ⟨f, hf, fun g hg ↦ hmax _ ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact (permOrbitRel G).trans' hf (permOrbitRel_mapDomain hg f)

/-- The orbit sum of an exponent that is largest in its orbit has that exponent as its leading
exponent. -/
theorem degree_orbitSum [Nontrivial R]
    (he : ∀ g ∈ G, m.toSyn (e.mapDomain g) ≤ m.toSyn e) : m.degree (orbitSum R G e) = e := by
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun f hf ↦ ?_)
    (m.le_degree (mem_support_orbitSum.2 ((permOrbitRel G).refl' e))))
  obtain ⟨g, hg, rfl⟩ := permOrbitRel_iff.1 (mem_support_orbitSum.1 hf)
  exact he g hg

/-- The orbit sum of an exponent that is largest in its orbit is monic. -/
theorem monic_orbitSum (he : ∀ g ∈ G, m.toSyn (e.mapDomain g) ≤ m.toSyn e) :
    m.Monic (orbitSum R G e) := by
  nontriviality R
  rw [Monic, leadingCoeff, m.degree_orbitSum he,
    coeff_orbitSum_of_rel ((permOrbitRel G).refl' e)]

/-- The leading term of the orbit sum of an exponent that is largest in its orbit is the monomial
of that exponent. -/
theorem leadingTerm_orbitSum (he : ∀ g ∈ G, m.toSyn (e.mapDomain g) ≤ m.toSyn e) :
    m.leadingTerm (orbitSum R G e) = monomial e 1 := by
  nontriviality R
  rw [leadingTerm, (m.monic_orbitSum he).leadingCoeff_eq_one, m.degree_orbitSum he]

/-- Over coefficients without zero divisors, the leading exponents of the `G`-invariant
polynomials are the exponents that are largest in their `G`-orbits. -/
theorem mem_leadingExponents_permInvariants_iff [NoZeroDivisors R] [Nontrivial R] :
    e ∈ m.leadingExponents (permInvariants R G) ↔
      ∀ g ∈ G, m.toSyn (e.mapDomain g) ≤ m.toSyn e := by
  refine ⟨fun h ↦ ?_, fun he ↦ mem_leadingExponents_iff.2 ⟨orbitSum R G e,
    orbitSum_mem_permInvariants e, orbitSum_ne_zero, m.degree_orbitSum he⟩⟩
  obtain ⟨f, hf, -, rfl⟩ := mem_leadingExponents_iff.1 h
  exact fun g hg ↦ m.toSyn_mapDomain_degree_le_of_mem_permInvariants hf hg

variable (R G) in
/-- The orbit sums form a SAGBI basis of the invariant subalgebra of a permutation group, for
every monomial order. -/
theorem isSAGBIBasis_range_orbitSum :
    m.IsSAGBIBasis (Set.range (orbitSum R G)) (permInvariants R G) := by
  rw [isSAGBIBasis_iff_initialAlgebra_le, initialAlgebra_def]
  refine ⟨Set.range_subset_iff.2 orbitSum_mem_permInvariants, Algebra.adjoin_le ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  have hmax : ∀ g ∈ G, m.toSyn ((m.degree f).mapDomain g) ≤ m.toSyn (m.degree f) :=
    fun g hg ↦ m.toSyn_mapDomain_degree_le_of_mem_permInvariants hf hg
  have hterm : m.leadingTerm f = C (m.leadingCoeff f) * m.leadingTerm (orbitSum R G (m.degree f)) :=
    by rw [m.leadingTerm_orbitSum hmax, C_mul_monomial, mul_one, leadingTerm]
  rw [hterm]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩)

end MonomialOrder
