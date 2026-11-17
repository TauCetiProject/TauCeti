/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Japanese
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import TauCeti.RingTheory.IntegralClosure.PurelyInseparable
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.PurelyInseparable
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization

/-!
# Tate algebras are Japanese domains

Let `K` be a complete nonarchimedean field of arbitrary characteristic (nontrivially or trivially
normed) and `σ` a finite set of variables. This file proves that every integrally closed
restricted-series ring `K{X / c}` at positive polyradius `c` is a Japanese domain
(`TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_of_isIntegrallyClosed`), and in particular
that the unit-polyradius Tate algebra `K⟨X₁, …, Xₙ⟩` is a Japanese domain
(`TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`), with no discrete-valuation or
perfectness hypothesis on `K`. Together with affinoid Noether normalization
(`TauCeti.RingTheory.Affinoid.Japanese`), this makes every affinoid domain Japanese, every affinoid
algebra Nagata, and the normalization of every reduced affinoid algebra finite and (over a
nontrivially normed field) again affinoid.

## Proof outline

By Kedlaya's Gröbner-basis theorem (`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`),
`T := K{X / c}` is Noetherian. By the linear-separation criterion for Japanese domains
(`TauCeti.Ring.IsJapanese.of_forall_exists_dual_ne_zero`, following Bosch–Güntzer–Remmert,
*Non-Archimedean Analysis*, §4.1, Lemma 3), it suffices to separate every nonzero integral element
`x₀` of any finite purely inseparable extension `M` of `F := GaussFractionField σ K c` by an
`F`-linear functional `φ : Module.Dual F M` sending every element of `M` integral over `T` into
`Set.range (algebraMap T F)`.

Since `T` is integrally closed, every `y : M` integral over `T` has its
`ringExpChar K ^ IsPurelyInseparable.exponent F M`-th power in `T`
(`IsIntegral.exists_algebraMap_eq_iterateFrobenius`), so
`TauCeti.MvPowerSeries.exists_dual_norm_le_spectralNorm_of_isPurelyInseparable` immediately
produces the required separating functional `φ`.

## Main results

* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_iff_of_isEmpty`: in zero variables,
  `R{X / c}` is Japanese if and only if `R` is Japanese.
* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_of_isIntegrallyClosed`: over a complete
  nonarchimedean field `K` and finite variable set `σ`, every integrally closed restricted-series
  ring `K{X / c}` at positive polyradius `c` is Japanese
  (Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §5.3.2, Theorem 1).
* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`: the unit-polyradius Tate algebra
  `K⟨X₁, …, Xₙ⟩` is a Japanese domain.
* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_of_norm_mul_pow_eq_one`: restricted-series
  rings `K{X / r}` at radii in the divisible hull of `|Kˣ|` are Japanese domains.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §§4.1, 4.4, and 5.3.2,
  Theorem 1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section Empty

/-- With no variables, `IsRestricted.subring (R := R) c` is a Japanese domain if and only if `R`
is a Japanese domain. -/
@[simp]
theorem isJapanese_isRestricted_subring_iff_of_isEmpty {σ R : Type*}
    [NormedCommRing R] [IsUltrametricDist R] [IsDomain R] [IsEmpty σ] (c : σ → ℝ) :
    Ring.IsJapanese (IsRestricted.subring (R := R) c) ↔ Ring.IsJapanese R :=
  ⟨fun _ ↦ (IsRestricted.isEmptyEquiv (R := R) c).toRingEquiv.isJapanese,
    fun _ ↦ (IsRestricted.isEmptyEquiv (R := R) c).symm.toRingEquiv.isJapanese⟩

end Empty

section Japanese

/-- **Integrally closed restricted-series rings are Japanese**
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §5.3.2, Theorem 1).
Over a complete nonarchimedean field `K` (of arbitrary characteristic, with trivial or nontrivial
norm) and finitely many variables `σ`, any integrally closed restricted-series ring `K{X / c}` at
positive polyradius `c` is a Japanese domain. -/
theorem isJapanese_isRestricted_subring_of_isIntegrallyClosed {σ K : Type*} [Finite σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)]
    [IsIntegrallyClosed (IsRestricted.subring (R := K) c)] :
    Ring.IsJapanese (IsRestricted.subring (R := K) c) := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  have : IsNoetherianRing T := isNoetherianRing_isRestricted_subring
  have : ExpChar F (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K F).injective (ringExpChar K)
  refine Ring.IsJapanese.of_forall_exists_dual_ne_zero F fun M _ _ _ _ _ _ x₀ _ hx₀ ↦ ?_
  obtain ⟨φ, -, -, -, hφ_mem, hφ_ne⟩ :=
    exists_dual_norm_le_spectralNorm_of_isPurelyInseparable (K := K) (c := c) M hx₀
  refine ⟨φ, fun y hy ↦ hφ_mem y ?_, hφ_ne⟩
  obtain ⟨fy, hfy⟩ := hy.exists_algebraMap_eq_iterateFrobenius (K := F) (ringExpChar K) le_rfl
  exact ⟨fy, by rw [Function.comp_apply, hfy, IsPurelyInseparable.algebraMap_iterateFrobenius]⟩

/-- **Tate algebras are Japanese domains.** Over a complete nonarchimedean field `K` (of arbitrary
characteristic) and finitely many variables `σ`, the unit-polyradius Tate algebra `K⟨X₁, …, Xₙ⟩` is
a Japanese domain (Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §5.3.2, Theorem 1). -/
instance isJapanese_isRestricted_subring {σ K : Type*} [Finite σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    Ring.IsJapanese (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) :=
  isJapanese_isRestricted_subring_of_isIntegrallyClosed (fun _ : σ ↦ 1)

/-- Restricted-series rings `K{X / r}` in finitely many variables at radii in the divisible hull of
`|Kˣ|` over a complete nonarchimedean field `K` are Japanese domains. -/
theorem isJapanese_isRestricted_subring_of_norm_mul_pow_eq_one {σ K : Type*} [Finite σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {r : σ → ℝ} [∀ i, Fact (0 < r i)]
    (hr : ∀ i, ∃ n ≠ 0, ∃ a : K, ‖a‖ * r i ^ n = 1) :
    Ring.IsJapanese (IsRestricted.subring (R := K) r) := by
  obtain ⟨φ, hφ_inj, hφ_fin⟩ := exists_injective_finite_algHom_of_norm_mul_pow_eq_one hr
  let _ : Algebra (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
    (IsRestricted.subring (R := K) r) := φ.toRingHom.toAlgebra
  have : FaithfulSMul (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
    (IsRestricted.subring (R := K) r) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hφ_inj
  have : Module.Finite (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
    (IsRestricted.subring (R := K) r) := hφ_fin
  exact Ring.IsJapanese.of_finite (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) _

end Japanese

end TauCeti.MvPowerSeries
