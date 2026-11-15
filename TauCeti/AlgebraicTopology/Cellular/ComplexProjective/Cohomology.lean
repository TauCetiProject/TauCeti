/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Basic
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ComplexProjective
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# The additive singular cohomology of complex projective space

With coefficients in a projective module `R` over a commutative ring `k`, the singular homology
of `CPⁿ` is `R` in the degrees `0, 2, …, 2n` and zero otherwise
(`TauCeti.ComplexProjectiveSpace.singularHomologyIso`), so it is projective in every degree. The
universal coefficient theorem with projective homology
(`TopCat.singularKroneckerEquivOfProjectiveHomology`) then identifies the cohomology with the dual
of the homology, with no hereditary-ring or field hypothesis: `H²ⁱ(CPⁿ; R, M) ≃ Hom(R, M)` for
`i ≤ n`, and every other cohomology module vanishes. With `R = k` this reads
`H²ⁱ(CPⁿ; k, M) ≃ M`.

This is only the additive computation. The cup-product ring `ℤ[u]/(uⁿ⁺¹)` is not treated here.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.projective_singularHomology`: the singular homology of `CPⁿ`
  with projective coefficients is projective in every degree.
* `TauCeti.ComplexProjectiveSpace.singularCohomologyEquiv`: for `i ≤ n`,
  `H²ⁱ(CPⁿ; R, M) ≃ₗ[k] (R ⟶ M)`, the Kronecker map read through `singularHomologyIso`.
* `TauCeti.ComplexProjectiveSpace.singularCohomologyEquivSelf`: for `i ≤ n`,
  `H²ⁱ(CPⁿ; k, M) ≃ₗ[k] M`.
* `TauCeti.ComplexProjectiveSpace.isZero_singularCohomology_of_odd` and
  `TauCeti.ComplexProjectiveSpace.isZero_singularCohomology_of_lt`: `Hᵐ(CPⁿ; R, M) = 0` for odd
  `m` and for `m > 2n`.
* `TauCeti.ComplexProjectiveSpace.finrank_singularCohomology`: over a nontrivial commutative ring,
  `Hᵐ(CPⁿ; k, k)` has rank `1` if `m` is even and `m ≤ 2n`, and `0` otherwise.
* `TauCeti.ComplexProjectiveSpace.finsum_finrank_singularCohomology`: the alternating sum of
  these ranks is `n + 1`, agreeing with `TauCeti.eulerChar_complexProjectiveSpace`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (the cellular homology of `CPⁿ` after Theorem 2.35) and Section 3.1 (Theorem 3.2,
  the universal coefficient theorem).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Module

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} {k : Type} [CommRing k] (R M : ModuleCat.{0} k)

/-- **The singular homology of `CPⁿ` is projective.** With projective coefficients `R`, every
singular homology module of `CPⁿ` is projective: it is `R` in the degrees `0, 2, …, 2n` and zero
in every other degree. -/
instance projective_singularHomology [Module.Projective k R] (m : ℕ) :
    Projective (((singularHomologyFunctor (ModuleCat.{0} k) m).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n))) := by
  rcases Nat.even_or_odd m with ⟨i, rfl⟩ | hm
  · rw [← two_mul]
    by_cases hi : i ≤ n
    · exact Projective.of_iso (singularHomologyIso R hi).symm inferInstance
    · exact (isZero_singularHomology_of_lt R (by omega)).projective
  · exact (isZero_singularHomology_of_odd R hm).projective

variable [Module.Projective k R]

/-- **The even-degree cohomology of complex projective space.** For a projective coefficient
module `R` and `i ≤ n`, the Kronecker map identifies `H²ⁱ(CPⁿ; R, M)` with `Hom(R, M)`, read on
`H₂ᵢ(CPⁿ; R)` through `TauCeti.ComplexProjectiveSpace.singularHomologyIso`. This holds over any
commutative ring `k`, since the homology of `CPⁿ` is projective. -/
def singularCohomologyEquiv {i : ℕ} (hi : i ≤ n) :
    (TopCat.of (ComplexProjectiveSpace n)).singularCohomology R k M (2 * i) ≃ₗ[k] (R ⟶ M) :=
  (TopCat.of (ComplexProjectiveSpace n)).singularKroneckerEquivOfProjectiveHomology R M (2 * i) ≪≫ₗ
    Linear.homCongr k (singularHomologyIso R hi) (Iso.refl M)

/-- `TauCeti.ComplexProjectiveSpace.singularCohomologyEquiv` evaluates a class on homology and
reads the result on `R` through the inverse of `singularHomologyIso`. -/
@[simp]
theorem singularCohomologyEquiv_apply {i : ℕ} (hi : i ≤ n)
    (α : (TopCat.of (ComplexProjectiveSpace n)).singularCohomology R k M (2 * i)) :
    singularCohomologyEquiv R M hi α =
      (singularHomologyIso R hi).inv ≫
        (TopCat.of (ComplexProjectiveSpace n)).singularKronecker k (2 * i) α := by
  simp [singularCohomologyEquiv, Linear.homCongr_apply]

/-- **The odd-degree cohomology of complex projective space vanishes.** `Hᵐ(CPⁿ; R, M) = 0` for
odd `m`, for every projective coefficient module `R` and every module `M`. -/
theorem isZero_singularCohomology_of_odd {m : ℕ} (hm : Odd m) :
    IsZero ((TopCat.of (ComplexProjectiveSpace n)).singularCohomology R k M m) := by
  have : Subsingleton (((singularHomologyFunctor (ModuleCat.{0} k) m).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n)) ⟶ M) :=
    ⟨(isZero_singularHomology_of_odd R hm).eq_of_src⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso
    ((TopCat.of (ComplexProjectiveSpace n)).singularKroneckerEquivOfProjectiveHomology
      R M m).toModuleIso

/-- The singular cohomology of `CPⁿ` vanishes above degree `2n`, for every projective coefficient
module `R` and every module `M`. -/
theorem isZero_singularCohomology_of_lt {m : ℕ} (hm : 2 * n < m) :
    IsZero ((TopCat.of (ComplexProjectiveSpace n)).singularCohomology R k M m) := by
  have : Subsingleton (((singularHomologyFunctor (ModuleCat.{0} k) m).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n)) ⟶ M) :=
    ⟨(isZero_singularHomology_of_lt R hm).eq_of_src⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso
    ((TopCat.of (ComplexProjectiveSpace n)).singularKroneckerEquivOfProjectiveHomology
      R M m).toModuleIso

variable (k) in
/-- **The even-degree cohomology of complex projective space with ring coefficients.** For
`i ≤ n`, `H²ⁱ(CPⁿ; k, M) ≃ₗ[k] M`: a class goes to its evaluation on the image of `1` under the
inverse of `singularHomologyIso`. -/
def singularCohomologyEquivSelf {i : ℕ} (hi : i ≤ n) :
    (TopCat.of (ComplexProjectiveSpace n)).singularCohomology (ModuleCat.of k k) k M (2 * i) ≃ₗ[k]
      M :=
  singularCohomologyEquiv (ModuleCat.of k k) M hi ≪≫ₗ ModuleCat.homLinearEquiv ≪≫ₗ
    LinearMap.ringLmapEquivSelf k k M

variable (k) in
/-- `TauCeti.ComplexProjectiveSpace.singularCohomologyEquivSelf` evaluates a class on the
homology class corresponding to `1` under `singularHomologyIso`. -/
@[simp]
theorem singularCohomologyEquivSelf_apply {i : ℕ} (hi : i ≤ n)
    (α : (TopCat.of (ComplexProjectiveSpace n)).singularCohomology (ModuleCat.of k k) k M
      (2 * i)) :
    singularCohomologyEquivSelf k M hi α =
      (TopCat.of (ComplexProjectiveSpace n)).singularKronecker k (2 * i) α
        ((singularHomologyIso (ModuleCat.of k k) hi).inv (1 : k)) := by
  simp only [singularCohomologyEquivSelf, LinearEquiv.trans_apply, singularCohomologyEquiv_apply,
    LinearMap.ringLmapEquivSelf_apply]
  rw [ModuleCat.homLinearEquiv_apply]
  exact ModuleCat.comp_apply _ _ _

variable (k) in
/-- **The ranks of the cohomology of complex projective space.** Over a nontrivial commutative
ring `k`, `Hᵐ(CPⁿ; k, k)` is free of rank `1` when `m` is even with `m ≤ 2n`, and zero otherwise.
-/
theorem finrank_singularCohomology [Nontrivial k] (m : ℕ) :
    finrank k ((TopCat.of (ComplexProjectiveSpace n)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) m) = if Even m ∧ m ≤ 2 * n then 1 else 0 := by
  split_ifs with h
  · obtain ⟨⟨i, rfl⟩, hm⟩ := h
    rw [← two_mul] at hm ⊢
    rw [(singularCohomologyEquivSelf k (ModuleCat.of k k) (n := n) (i := i) (by omega)).finrank_eq]
    exact finrank_self k
  · rw [not_and_or, Nat.not_even_iff_odd, not_le] at h
    have := ModuleCat.subsingleton_of_isZero <| h.elim
      (isZero_singularCohomology_of_odd (n := n) (ModuleCat.of k k) (ModuleCat.of k k))
      (isZero_singularCohomology_of_lt (n := n) (ModuleCat.of k k) (ModuleCat.of k k))
    exact finrank_zero_of_subsingleton

variable (k) in
/-- **The cohomological Euler characteristic of complex projective space.** Over a nontrivial
commutative ring, the alternating sum of the ranks of `Hᵐ(CPⁿ; k, k)` is `n + 1`, in agreement
with `TauCeti.eulerChar_complexProjectiveSpace`. -/
theorem finsum_finrank_singularCohomology [Nontrivial k] :
    ∑ᶠ m : ℕ, (-1 : ℤ) ^ m * finrank k ((TopCat.of (ComplexProjectiveSpace n)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) m) = n + 1 := by
  let := cwComplex n
  rw [← cwEulerChar_cwComplex, cwEulerChar_def]
  simp_rw [finrank_singularCohomology, nat_card_cell_cwComplex]

end TauCeti.ComplexProjectiveSpace
