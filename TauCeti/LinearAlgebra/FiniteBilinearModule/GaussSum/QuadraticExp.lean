/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum
import TauCeti.LinearAlgebra.QuadraticForm.OfExp

/-!
# Gauss sums of exponentials of quadratic functions on a quotient

Let `H` be a subgroup of an abelian group `G` and `ψ` a biadditive complex form on `G`. A function
`q` on `G ⧸ H` with `q (x) = exp (ψ (x, x))` for every representative `x` is, when `G ⧸ H` is
finite, `e^{2πi Q}` for a `ℚ/ℤ`-valued quadratic map `Q` on `G ⧸ H`
(`TauCeti.exists_quadraticMap_expCircle_eq`). The sum of the values of `q` is then the Gauss sum of
the finite quadratic module `(G ⧸ H, Q)`, whose fourth power is real
(`TauCeti.FiniteQuadraticModule.conj_gaussSum_pow_four`). This gives
`(∑ q)⁴ = (∑ conj q)⁴` (`TauCeti.finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_diagonal`).
The sums are `finsum`s: the ordinary finite sums when `G ⧸ H` is finite, and both `0` when it is
infinite.

The same holds for `q (x) = exp (B (x, T x))` on `M ⧸ (M ∩ L)` (which is `M ⧸ L` when `L ⊆ M`), for
a biadditive form `B`, an additive endomorphism `T` and subgroups `L`, `M` of an abelian group
(`TauCeti.finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_form`).

## Main results

* `TauCeti.finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_diagonal`: `(∑ q)⁴ = (∑ conj q)⁴`
  for `q (x) = exp (ψ (x, x))` on a quotient `G ⧸ H`.
* `TauCeti.finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_form`: the same for
  `q (x) = exp (B (x, T x))` on `M ⧸ (M ∩ L)`.

## References

* This statement appears for Hermitian actions as
  `New.ThetaTori.IsHermitianAction.sum_conj_pow_four_eq_sum_pow_four` in
  `Lib/Shimura/GoodReduction/GaussSums` of the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open Complex ComplexConjugate

namespace TauCeti

variable {G : Type*} [AddCommGroup G] {H : AddSubgroup G} {ψ : G →+ G →+ ℂ} {q : G ⧸ H → ℂ}

/-- **The fourth power of a quadratic Gauss sum on a quotient is real.** Let `ψ` be a biadditive
complex form on an abelian group `G`, `H` a subgroup, and `q` a function on `G ⧸ H` with
`q (x) = exp (ψ (x, x))` for every representative `x`. Then `(∑ q)⁴ = (∑ conj q)⁴`. The sums are
`finsum`s: the ordinary finite sums when `G ⧸ H` is finite, and both `0` when it is infinite. -/
theorem finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_diagonal
    (hq : ∀ x : G, q x = exp (ψ x x)) : (∑ᶠ z, q z) ^ 4 = (∑ᶠ z, conj (q z)) ^ 4 := by
  have hq0 (z : G ⧸ H) : q z ≠ 0 := by
    induction z using QuotientAddGroup.induction_on with | H x =>
    rw [hq]
    exact exp_ne_zero _
  rcases finite_or_infinite (G ⧸ H) with h | h
  · obtain ⟨Q, hQ⟩ := exists_quadraticMap_expCircle_eq hq
    -- The Gauss sum of `(G ⧸ H, Q)` is the sum of the values of `q`.
    have hsum : (FiniteQuadraticModule.ofQuadraticMap Q).gaussSum = ∑ᶠ z, q z := by
      obtain ⟨_⟩ := nonempty_fintype (G ⧸ H)
      -- The carrier of the module of `Q` is `G ⧸ H`.
      let : Fintype (FiniteQuadraticModule.ofQuadraticMap Q).carrier :=
        inferInstanceAs (Fintype (G ⧸ H))
      rw [FiniteQuadraticModule.gaussSum_eq_sum, ← finsum_eq_sum_of_fintype]
      exact finsum_congr fun z ↦
        (congrArg expCircle (FiniteQuadraticModule.ofQuadraticMap_quadratic Q z)).trans (hQ z)
    have hconj : ∑ᶠ z, conj (q z) = conj (∑ᶠ z, q z) :=
      ((starRingEnd ℂ).toAddMonoidHom.map_finsum_of_injective star_injective q).symm
    rw [hconj, ← map_pow, ← hsum, FiniteQuadraticModule.conj_gaussSum_pow_four]
  · rw [finsum_of_infinite_support, finsum_of_infinite_support] <;>
      simp [Function.support, hq0, Set.infinite_univ]

/-- **The fourth power of a quadratic Gauss sum on `M ⧸ (M ∩ L)` is real.** Let `B` be a
biadditive complex form and `T` an additive endomorphism of an abelian group `V`, `L` and `M`
subgroups of `V`, and `q` a function on `M ⧸ (M ∩ L)` (which is `M ⧸ L` when `L ⊆ M`) with
`q (x) = exp (B (x, T x))` for every representative `x`. Then `(∑ q)⁴ = (∑ conj q)⁴`. The sums are
`finsum`s: the ordinary finite sums when `M ⧸ (M ∩ L)` is finite, and both `0` when it is
infinite. -/
theorem finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_form {V : Type*} [AddCommGroup V]
    (B : V →+ V →+ ℂ) (T : V →+ V) {L M : Submodule ℤ V} {q : M ⧸ L.submoduleOf M → ℂ}
    (hq : ∀ x : M, q (Submodule.Quotient.mk x) = exp (B x (T x))) :
    (∑ᶠ z, q z) ^ 4 = (∑ᶠ z, conj (q z)) ^ 4 :=
  finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_diagonal (H := (L.submoduleOf M).toAddSubgroup)
    (ψ := (B.comp M.subtype.toAddMonoidHom).compl₂ (T.comp M.subtype.toAddMonoidHom))
    fun x ↦ by
      rw [Submodule.Quotient.quotientAddGroupMk_eq_mk, hq]
      simp

end TauCeti
