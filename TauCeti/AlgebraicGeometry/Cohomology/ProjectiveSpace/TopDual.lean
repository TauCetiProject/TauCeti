/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# The top cohomology of `𝒪(m)` on projective space as a dual module

Let `M` be a free `R`-module with a basis indexed by `κ`, so that `Proj (Sym M)` is projective
space `ℙⁿ_R` with `n + 1 = card κ`. The top cohomology `Hⁿ(ℙⁿ_R, 𝒪(m))` is the free `R`-module on
the Laurent monomials `xᵉ` of degree `m` all of whose exponents are negative
(`Module.Basis.nonempty_linearEquiv_cohomology_top_twistingSheaf`). Shifting every exponent by one
and negating identifies these monomials with the ordinary monomials of degree `-m - n - 1`, which
index the monomial basis of the forms `Sym^{-m-n-1} M` of that degree. Hence `Hⁿ(ℙⁿ_R, 𝒪(m))` is
isomorphic to the dual of the module of forms of degree `-m - n - 1` (Stacks, Lemma 30.8.1 (01XT)).

## Main declarations

* `TauCeti.SymmetricAlgebra.negativeExponentsEquivDegree`: exponents of degree `m` with all
  entries negative correspond to exponent vectors in `ℕ` of total degree `j = -m - card κ`, by
  `e ↦ -e - 1`.
* `Module.Basis.nonempty_linearEquiv_cohomology_top_twistingSheaf_dual`:
  `Hⁿ(ℙⁿ_R, 𝒪(m)) ≃ₗ[R] (Sym^j M)^∨` for `j = -m - n - 1`.

## References

* [Stacks Project, Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XT)
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.SymmetricAlgebra

/-- Exponents `e : κ → ℤ` of degree `m` with all entries negative correspond to exponent vectors
`d : κ →₀ ℕ` of total degree `j = -m - card κ`, by `d = -e - 1`. -/
noncomputable def negativeExponentsEquivDegree (κ : Type*) [Fintype κ] {m : ℤ} {j : ℕ}
    (hj : (j : ℤ) = -m - Fintype.card κ) :
    negativeExponents κ m ≃ {d : κ →₀ ℕ // d.degree = j} where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm fun i ↦ (-e.1 i - 1).toNat, by
    obtain ⟨hsum, hneg⟩ := mem_negativeExponents.1 e.2
    have he : ∀ i, ((-e.1 i - 1).toNat : ℤ) = -e.1 i - 1 := fun i ↦
      Int.toNat_of_nonneg (by have := hneg i; omega)
    have hdeg : ((∑ i, (-e.1 i - 1).toNat : ℕ) : ℤ) = j := by
      push_cast
      simp only [he, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hsum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one, hj]
    rw [Finsupp.degree_eq_sum]
    exact_mod_cast hdeg⟩
  invFun d := ⟨fun i ↦ -(d.1 i : ℤ) - 1, by
    refine mem_negativeExponents.2 ⟨?_, fun i ↦ by omega⟩
    have hd : ((∑ i, d.1 i : ℕ) : ℤ) = j := by rw [← Finsupp.degree_eq_sum, d.2]
    push_cast at hd
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hd, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, hj]
    ring⟩
  left_inv e := by
    ext i
    have := (mem_negativeExponents.1 e.2).2 i
    change -((-e.1 i - 1).toNat : ℤ) - 1 = e.1 i
    omega
  right_inv d := by
    ext i
    simp

end TauCeti.SymmetricAlgebra

namespace Module.Basis

open TauCeti.SymmetricAlgebra (negativeExponentsEquivDegree)

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M

/-- **The top cohomology of `𝒪(m)` on projective space is dual to the forms of degree
`-m - n - 1`.** Let `M` be a free `R`-module with a basis indexed by `κ` of cardinality `n + 2`,
so that `Proj (Sym M)` is projective space of dimension `n + 1` over `R`. For `j : ℕ` with
`j = -m - (n + 2)`, the top cohomology `H^{n+1}(Proj (Sym M), 𝒪(m))` is isomorphic to the dual of
the module `Symʲ M` of forms of degree `j`, over any commutative ring `R` (Stacks, Lemma 30.8.1
(01XT)). No isomorphism is singled out. -/
theorem nonempty_linearEquiv_cohomology_top_twistingSheaf_dual {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {n j : ℕ} (hn : Fintype.card κ = n + 2)
    (hj : (j : ℤ) = -m - Fintype.card κ) :
    Nonempty (Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1) ≃ₗ[R]
      Module.Dual R (𝒜 j)) := by
  classical
  obtain ⟨φ⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf m hn
  exact ⟨φ.trans ((Finsupp.domLCongr ((negativeExponentsEquivDegree κ hj).trans
    (Sym.equivFinsuppDegree κ j).symm)).trans
      (b.symmetricAlgebraHomogeneous j).dualBasis.repr.symm)⟩

end Module.Basis
