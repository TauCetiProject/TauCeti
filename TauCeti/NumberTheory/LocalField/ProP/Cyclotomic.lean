/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Marked

/-!
# The marked pro-`p` Galois group of `ℚ_p(μ_p)`

For an odd prime `p`, the maximal pro-`p` Galois group of `ℚ_p(μ_p)` has the presentation

`⟨x₁, …, x_{p+1} ∣ x₁^p (x₁, x₂) (x₃, x₄) ⋯ (x_p, x_{p+1})⟩`.

The marked isomorphism records the cyclotomic orientation: its value on the second generator
is `(1 - p)⁻¹`, and its values on all other generators are `1`. The commutator convention is
`(x, y) = x⁻¹ y⁻¹ x y`, and the quotient uses the closed normal closure of the relator.

The statement applies to any compatible local-field model of the cyclotomic extension in
`Type 0`, the universe supported by the marked classification theorem used here.
Its arithmetic inputs are `TauCeti.finrank_cyclotomic_prime_pow_ratPadic` and
`TauCeti.localRootOfUnityOrder_cyclotomic_prime_pow_ratPadic`: the field degree is `p - 1`
and the root-of-unity order is exactly `p`. The generator rank `p + 1` is also computed
independently in `TauCeti.topologicalGeneratorRankNat_cyclotomic_prime_ratPadic`.
The marked presentation specializes `TauCeti.absoluteGaloisGroupProP_marked_of_q_ne_two`,
so the orientation is the descended cyclotomic character, not a separately chosen character
of the abstract presentation.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Theorem 7.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.12).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K]
  [ValuativeExtension ℚ_[p] K] [IsCyclotomicExtension {p} ℚ_[p] K]

/-- For an odd prime `p`, `G_{ℚ_p(μ_p)}(p)` has the single-relator presentation
`x₁^p (x₁, x₂) ⋯ (x_p, x_{p+1})` on `p + 1` generators. Under the marked isomorphism, the
cyclotomic orientation takes the value `(1 - p)⁻¹` on the second generator and is trivial
on every other generator. -/
theorem absoluteGaloisGroupProP_cyclotomic_prime_ratPadic_marked (hp : p ≠ 2) :
    ∃ e : absoluteGaloisGroupProP p K ≃ₜ*
        presentedProP p (Fin (p + 1))
          {demushkinWordNeTwo p (p + 1) (freeProPGen p (p + 1))},
      ((cyclotomicOrientation p K
            ⟨IsCyclotomicExtension.zeta p ℚ_[p] K, IsCyclotomicExtension.zeta_spec p ℚ_[p] K⟩
            (e.symm (presentedProPGen p (p + 1) _ 1)) : ℤ_[p]) * (1 - (p : ℤ_[p])) = 1) ∧
        ∀ i : ℕ, i ≠ 1 → i < p + 1 →
          cyclotomicOrientation p K
            ⟨IsCyclotomicExtension.zeta p ℚ_[p] K, IsCyclotomicExtension.zeta_spec p ℚ_[p] K⟩
            (e.symm (presentedProPGen p (p + 1) _ i)) = 1 := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ_[p] K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ_[p] K)
  let hmu : ∃ ζ : K, IsPrimitiveRoot ζ p :=
    ⟨IsCyclotomicExtension.zeta p ℚ_[p] K, IsCyclotomicExtension.zeta_spec p ℚ_[p] K⟩
  have hq : localRootOfUnityOrder p K
      (finite_pPowerRootsOfUnity (hmu.elim fun _ hζ ↦ hζ.neZero'.out)) = p := by
    simpa using localRootOfUnityOrder_cyclotomic_prime_pow_ratPadic p K 0
      (finite_pPowerRootsOfUnity (hmu.elim fun _ hζ ↦ hζ.neZero'.out))
  have hdegree : Module.finrank ℚ_[p] K = p - 1 := by
    simpa using finrank_cyclotomic_prime_pow_ratPadic p K 0
  have hrank : Module.finrank ℚ_[p] K + 2 = p + 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hmarked :=
    absoluteGaloisGroupProP_marked_of_q_ne_two p K hmu (by rw [hq]; exact hp)
  rwa [hq, hrank] at hmarked

end TauCeti
