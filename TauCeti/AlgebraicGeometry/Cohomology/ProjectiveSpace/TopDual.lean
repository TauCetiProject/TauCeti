/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf

/-!
# The top cohomology of `𝒪(m)` on projective space as a dual module

Let `M` be a free `R`-module with a basis indexed by `κ`, so that `Proj (Sym M)` is projective
space `ℙⁿ_R` with `n + 1 = card κ`, and suppose `n ≥ 1`. The top cohomology `Hⁿ(ℙⁿ_R, 𝒪(m))` is
the free `R`-module on the Laurent monomials `xᵉ` of degree `m` all of whose exponents are negative
(`Module.Basis.nonempty_linearEquiv_cohomology_top_twistingSheaf`). Such monomials exist only when
`m ≤ -n - 1`. Shifting every exponent by one and negating identifies them with the ordinary
monomials of degree `j = -m - n - 1 ≥ 0`, which index the monomial basis of the forms `Symʲ M` of
that degree. Hence for `n ≥ 1` and `m ≤ -n - 1` the module `Hⁿ(ℙⁿ_R, 𝒪(m))` is isomorphic to the
dual of `Symʲ M` (Stacks, Lemma 30.8.1 (01XT)). In particular, over a nonzero ring the top
cohomology `Hⁿ(ℙⁿ_R, 𝒪(m))` is nonzero for `m ≤ -n - 1`; for `n = 0` this is the computation of the
global sections of `𝒪(m)` on `ℙ⁰_R`.

## Main declarations

* `TauCeti.SymmetricAlgebra.negativeExponentsEquivFinsuppDegree`: exponents of degree `m` with all
  entries negative correspond to exponent vectors in `ℕ` of total degree `j = -m - card κ`, by
  `e ↦ -e - 1`.
* `Module.Basis.nonempty_linearEquiv_cohomology_top_twistingSheaf_dual`: for `n ≥ 1` and `j : ℕ`
  with `j = -m - n - 1`, the module `Hⁿ(ℙⁿ_R, 𝒪(m))` is isomorphic to `(Symʲ M)^∨`; no
  isomorphism is singled out.
* `Module.Basis.nonempty_linearEquiv_cohomology_top_twistingSheaf_neg_card`: for `n ≥ 1`,
  `Hⁿ(ℙⁿ_R, 𝒪(-n-1)) ≅ R`.
* `Module.Basis.nontrivial_cohomology_top_twistingSheaf_of_le_neg_card`: for `n ≥ 0`, `R ≠ 0`
  and `m ≤ -n - 1`, `Hⁿ(ℙⁿ_R, 𝒪(m)) ≠ 0`.

## References

* [Stacks Project, Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XT)
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.SymmetricAlgebra

/-- Exponents `e : κ → ℤ` of degree `m` with all entries negative correspond to exponent vectors
`d : κ →₀ ℕ` of total degree `j = -m - card κ`, by `d = -e - 1`. -/
noncomputable def negativeExponentsEquivFinsuppDegree (κ : Type*) [Fintype κ] {m : ℤ} {j : ℕ}
    (hj : (j : ℤ) = -m - Fintype.card κ) :
    negativeExponents κ m ≃ {d : κ →₀ ℕ // d.degree = j} where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm fun i ↦ (-e.val i - 1).toNat, by
    obtain ⟨hsum, hneg⟩ := mem_negativeExponents.1 e.property
    have he : ∀ i, ((-e.val i - 1).toNat : ℤ) = -e.val i - 1 := fun i ↦
      Int.toNat_of_nonneg (by have := hneg i; omega)
    have hdeg : ((∑ i, (-e.val i - 1).toNat : ℕ) : ℤ) = j := by
      push_cast
      simp only [he, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hsum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one, hj]
    rw [Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm]
    exact_mod_cast hdeg⟩
  invFun d := ⟨fun i ↦ -(d.val i : ℤ) - 1, by
    refine mem_negativeExponents.2 ⟨?_, fun i ↦ by omega⟩
    have hd : ((∑ i, d.val i : ℕ) : ℤ) = j := by rw [← Finsupp.degree_eq_sum, d.property]
    push_cast at hd
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hd, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, hj]
    ring⟩
  left_inv e := by
    ext i
    have := (mem_negativeExponents.1 e.property).2 i
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    omega
  right_inv d := by
    ext i
    simp

/-- The entries of `negativeExponentsEquivFinsuppDegree κ hj e`, viewed in `ℤ`, are `-e i - 1`. -/
@[simp]
theorem natCast_coe_negativeExponentsEquivFinsuppDegree_apply_apply {κ : Type*} [Fintype κ]
    {m : ℤ} {j : ℕ} (hj : (j : ℤ) = -m - Fintype.card κ) (e : negativeExponents κ m) (i : κ) :
    ((negativeExponentsEquivFinsuppDegree κ hj e : κ →₀ ℕ) i : ℤ) = -e.val i - 1 := by
  have := (mem_negativeExponents.1 e.property).2 i
  simp only [negativeExponentsEquivFinsuppDegree, Equiv.coe_fn_mk,
    Finsupp.coe_equivFunOnFinite_symm]
  omega

/-- The inverse of `negativeExponentsEquivFinsuppDegree` sends `d` to the exponent `-d - 1`. -/
@[simp]
theorem coe_negativeExponentsEquivFinsuppDegree_symm_apply_apply {κ : Type*} [Fintype κ] {m : ℤ}
    {j : ℕ} (hj : (j : ℤ) = -m - Fintype.card κ) (d : {d : κ →₀ ℕ // d.degree = j}) (i : κ) :
    ((negativeExponentsEquivFinsuppDegree κ hj).symm d : κ → ℤ) i = -(d.val i : ℤ) - 1 := by
  simp only [negativeExponentsEquivFinsuppDegree, Equiv.coe_fn_symm_mk]

end TauCeti.SymmetricAlgebra

namespace Module.Basis

open TauCeti.SymmetricAlgebra (negativeExponentsEquivFinsuppDegree)

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M

/-- **The top cohomology of `𝒪(m)` on projective space is dual to a module of forms.** Let `M` be
a free `R`-module with a basis indexed by `κ` of cardinality `n + 2`, so that `Proj (Sym M)` is
projective space of dimension `n + 1` over `R`. For `j : ℕ` with `j = -m - (n + 2)`, the top
cohomology `H^{n+1}(Proj (Sym M), 𝒪(m))` is isomorphic to the dual of the module `Symʲ M` of forms
of degree `j`, over any commutative ring `R` (Stacks, Lemma 30.8.1 (01XT)). No isomorphism is
singled out. -/
theorem nonempty_linearEquiv_cohomology_top_twistingSheaf_dual {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {n j : ℕ} (hn : Fintype.card κ = n + 2)
    (hj : (j : ℤ) = -m - Fintype.card κ) :
    Nonempty (Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1) ≃ₗ[R]
      Module.Dual R (𝒜 j)) := by
  classical
  obtain ⟨φ⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf m hn
  exact ⟨φ.trans ((Finsupp.domLCongr ((negativeExponentsEquivFinsuppDegree κ hj).trans
    (Sym.equivFinsuppDegree κ j).symm)).trans
      (b.symmetricAlgebraHomogeneous j).dualBasis.repr.symm)⟩

/-- **The top cohomology of `𝒪(-(n + 2))` on projective space of dimension `n + 1` is free of
rank one.** For a free `R`-module `M` with a basis indexed by `κ` of cardinality `n + 2`, so that
`Proj (Sym M)` is projective space of dimension `n + 1` over `R`,
`H^{n+1}(Proj (Sym M), 𝒪(-(n + 2)))` is isomorphic to `R`, over any commutative ring `R`: it is
the dual of the forms of degree zero. No isomorphism is singled out. -/
theorem nonempty_linearEquiv_cohomology_top_twistingSheaf_neg_card {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) {n : ℕ} (hn : Fintype.card κ = n + 2) :
    Nonempty (Cohomology (Proj.twistingSheaf 𝒜 (-((n + 2 : ℕ) : ℤ))) (n + 1) ≃ₗ[R] R) := by
  obtain ⟨φ⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf_dual
    (-((n + 2 : ℕ) : ℤ)) (j := 0) hn (by rw [hn]; ring)
  exact ⟨φ.trans ((TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv R M).dualMap.symm.trans
    (LinearMap.ringLmapEquivSelf R R R))⟩

/-- **The top cohomology of `𝒪(m)` on projective space of dimension `n` is nonzero for
`m ≤ -(n + 1)`.** For a nonzero ring `R` and a free `R`-module `M` with a basis indexed by `κ` of
cardinality `n + 1`, so that `Proj (Sym M)` is projective space of dimension `n` over `R`,
`Hⁿ(Proj (Sym M), 𝒪(m))` is nontrivial when `m ≤ -(n + 1)`. For `n ≥ 1` it is the dual of the
free module of forms of degree `-m - (n + 1)`, which has a monomial basis; for `n = 0` every
twisting sheaf on `ℙ⁰_R` has a nonzero global section. -/
theorem nontrivial_cohomology_top_twistingSheaf_of_le_neg_card [Nontrivial R] {κ : Type*}
    [Fintype κ] (b : Module.Basis κ R M) {n : ℕ} (hn : Fintype.card κ = n + 1) {m : ℤ}
    (hm : m ≤ -((n + 1 : ℕ) : ℤ)) :
    Nontrivial (Cohomology (Proj.twistingSheaf 𝒜 m) n) := by
  classical
  cases n with
  | zero =>
    obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hn
    exact TauCeti.SymmetricAlgebra.nontrivial_cohomology_zero_twistingSheaf_of_unique b m
  | succ n =>
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = -m - Fintype.card κ :=
      ⟨(-m - Fintype.card κ).toNat, Int.toNat_of_nonneg (by rw [hn]; omega)⟩
    obtain ⟨φ⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf_dual m hn hj
    obtain ⟨k⟩ : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
    let c := (b.symmetricAlgebraHomogeneous j).dualBasis
    have : Nontrivial (Module.Dual R (𝒜 j)) :=
      nontrivial_of_ne (c (Sym.replicate j k)) 0 (c.ne_zero _)
    exact φ.toEquiv.nontrivial

end Module.Basis
