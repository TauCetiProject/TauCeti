/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Japanese
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Finsupp.Encodable
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Localization.Integer
import TauCeti.RingTheory.IntegralClosure.LinearSeparation
import TauCeti.RingTheory.IntegralClosure.PurelyInseparable
import TauCeti.RingTheory.MvPowerSeries.LexOrder
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.PurelyInseparable
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization

/-!
# Tate algebras are Japanese domains

Let `K` be a complete nonarchimedean field of arbitrary characteristic (nontrivially or trivially
normed) and `σ` a finite set of variables. This file proves that every integrally closed
restricted-series ring `K{X / c}` at positive polyradius `c` is a Japanese domain
(`TauCeti.MvPowerSeries.isJapanese_of_isIntegrallyClosed`), and in particular that the
unit-polyradius Tate algebra `K⟨X₁, …, Xₙ⟩` is a Japanese domain
(`TauCeti.MvPowerSeries.isJapanese`), with no discrete-valuation or perfectness hypothesis on `K`.

## Proof outline

By Kedlaya's Gröbner-basis theorem (`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`),
`T := K{X / c}` is Noetherian. By the linear-separation criterion for Japanese domains
(`TauCeti.Ring.IsJapanese.of_forall_exists_dual_ne_zero`, following [bosch-guntzer-remmert], §4.1,
Lemma 3), it suffices to separate every nonzero integral element `x₀` of any finite purely
inseparable extension `M` of `F := GaussFractionField σ K c` by an `F`-linear functional
`φ : Module.Dual F M` sending the integral closure of `T` in `M` into `T`.

1. Let `p := ringExpChar K`, `e := IsPurelyInseparable.exponent F M`, `q := p ^ e`,
   `K' := FrobeniusRoot K p e`, and `r i = c i ^ q⁻¹` (`r i ^ q = c i`). Using
   `TauCeti.MvPowerSeries.exists_isometric_ringHom_of_isPurelyInseparable`, embed `M` into
   `F' := GaussFractionField σ K' r` compatibly with the Frobenius-expansion map `Ψ : T →+* T'`
   (`T' := K'{X / r}`), sending an `F`-basis `b` of `M` into `T'` via `rootG : Fin m → T'`.
2. Let `E ⊆ K'` be the `K`-span of all power-series coefficients of the generators `rootG j`. Since
   `σ` is finite, `E` is countably generated over the complete ultrametric field `K`, so bounded
   `K`-linear functionals separate points of `E`
   (`TauCeti.MvPowerSeries.exists_bounded_dual_ne_zero_span_of_countable_frobeniusRoot`).
3. Clearing denominators of `b.repr x₀` and applying
   `TauCeti.MvPowerSeries.exists_restricted_projection_of_ne_zero` produces a `q`-adic projection
   `π` to `T` that is `T`-linear along `Ψ` and nonzero at the cleared numerator of `x₀`. Define
   `φ : Module.Dual F M` on the basis `b` by `b j ↦ π (rootG j)`; then `φ x₀ ≠ 0`.
4. If `y ∈ M` is integral over the integrally closed domain `T`, then `y ^ q ∈ T`
   (`IsIntegral.exists_algebraMap_eq_iterateFrobenius`), so `ι y` lies in `T'` as a `tateRoot`
   series `r_y`. Clearing denominators `s • b.repr y = a` gives
   `Ψ s * r_y = ∑ j, Ψ (a j) * rootG j` in `T'`. Because `(Ψ s : MvPowerSeries σ K')` has
   coefficients in `K` and is nonzero, lexicographic induction on exponents
   (`MvPowerSeries.coeff_mem_of_coeff_map_mul_mem`) shows that all coefficients of `r_y` belong to
   `E`. Applying `π` to both sides yields `s * π r_y = ∑ j, a j * g j` in `T`, hence
   `φ y = algebraMap T F (π r_y) ∈ Set.range (algebraMap T F)`.

## Main results

* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_iff_of_isEmpty`: in zero variables,
  `R{X / c}` is Japanese if and only if `R` is Japanese.
* `TauCeti.MvPowerSeries.isJapanese_of_isIntegrallyClosed`: over a complete nonarchimedean field
  `K` and finite variable set `σ`, every integrally closed restricted-series ring `K{X / c}` at
  positive polyradius `c` is Japanese ([bosch-guntzer-remmert], §5.3.2, Theorem 1).
* `TauCeti.MvPowerSeries.isJapanese`: the unit-polyradius Tate algebra `K⟨X₁, …, Xₙ⟩` is a Japanese
  domain.
* `TauCeti.MvPowerSeries.isJapanese_of_norm_mul_pow_eq_one`: restricted-series rings `K{X / r}` at
  radii in the divisible hull of `|Kˣ|` are Japanese domains.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§4.1, 4.4, and
  5.3.2, Theorem 1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries
open scoped IntermediateField

section Empty

/-- With no variables, `IsRestricted.subring (R := R) c` is a Japanese domain if and only if `R`
is a Japanese domain. -/
theorem isJapanese_isRestricted_subring_iff_of_isEmpty {σ R : Type*}
    [NormedCommRing R] [IsUltrametricDist R] [IsDomain R] [IsEmpty σ] (c : σ → ℝ) :
    Ring.IsJapanese (IsRestricted.subring (R := R) c) ↔ Ring.IsJapanese R :=
  ⟨fun _ ↦ (IsRestricted.isEmptyEquiv (R := R) c).toRingEquiv.isJapanese,
    fun _ ↦ (IsRestricted.isEmptyEquiv (R := R) c).symm.toRingEquiv.isJapanese⟩

end Empty

section Japanese

/-- **Integrally closed restricted-series rings are Japanese**
([bosch-guntzer-remmert], §5.3.2, Theorem 1).
Over a complete nonarchimedean field `K` (of arbitrary characteristic, with trivial or nontrivial
norm) and finitely many variables `σ`, any integrally closed restricted-series ring `K{X / c}` at
positive polyradius `c` is a Japanese domain. -/
theorem isJapanese_of_isIntegrallyClosed {σ K : Type*} [Finite σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)]
    [IsIntegrallyClosed (IsRestricted.subring (R := K) c)] :
    Ring.IsJapanese (IsRestricted.subring (R := K) c) := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  have : IsNoetherianRing T := isNoetherianRing_isRestricted_subring
  refine Ring.IsJapanese.of_forall_exists_dual_ne_zero F fun M _ _ _ _ _ _ x₀ _ hx₀ ↦ ?_
  let p := ringExpChar K
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let e := IsPurelyInseparable.exponent F M
  have he : IsPurelyInseparable.exponent F M ≤ e := le_rfl
  set q := p ^ e
  have hq : q ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  have hqR_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  -- Step 1: Embed `M` into `F' = GaussFractionField σ K' r` using `K' = FrobeniusRoot K p e`.
  let K' := FrobeniusRoot K p e
  let r : σ → ℝ := fun i ↦ c i ^ ((q : ℝ)⁻¹)
  have hr_fact : ∀ i, Fact (0 < r i) := fun i ↦ ⟨Real.rpow_pos_of_pos (Fact.out : 0 < c i) _⟩
  have hr (i : σ) : r i ^ q = c i := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < c i).le, inv_mul_cancel₀ hqR_ne,
      Real.rpow_one]
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have h_iso (a : K) : ‖algebraMap K K' a‖ ≤ 1 * ‖a‖ := by simp
  obtain ⟨Ψ, m, b, rootG, ι, hΨ_def, hΨ_norm, hι_alg, _, hι_b⟩ :=
    exists_isometric_ringHom_of_isPurelyInseparable M p e he (fun _ ↦ rfl) hr h_iso
  -- Step 2: Span a countably generated `K`-subspace `E ⊆ K'` from all coefficients of `rootG`.
  let S : Set K' := Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
    coeff idx.2 (rootG idx.1 : _root_.MvPowerSeries σ K')
  let E : Submodule K K' := Submodule.span K S
  have hrootG_mem (j : Fin m) (α : σ →₀ ℕ) :
      coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E := Submodule.subset_span ⟨(j, α), rfl⟩
  have hu_mem (a : Fin m → T) (α : σ →₀ ℕ) :
      coeff α ((∑ j, Ψ (a j) * rootG j : T') : _root_.MvPowerSeries σ K') ∈ E := by
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    exact sum_mem fun j _ ↦
      coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso hΨ_def (a j) (hrootG_mem j) α
  -- Step 3: Separate `x₀` by a `q`-adic coefficientwise projection `π` back to `T`.
  obtain ⟨s₀, hs₀⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T) (b.repr x₀)
  choose a₀ ha₀ using hs₀
  have hs₀_F_ne : algebraMap T' F' (Ψ s₀) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_algebraMap_gaussFractionField, hΨ_norm, norm_ne_zero_iff]
    exact nonZeroDivisors.ne_zero s₀.2
  have hu₀_ne : ∑ j, Ψ (a₀ j) * rootG j ≠ 0 := fun h0 ↦ by
    have hmul : algebraMap T' F' (Ψ s₀) * ι x₀ = 0 := by
      rw [← algebraMap_sum_mul_eq_mul b Ψ rootG ι hι_alg hι_b x₀ s₀ a₀ ha₀, h0, map_zero]
    exact mul_ne_zero hs₀_F_ne ((map_ne_zero_iff ι ι.injective).mpr hx₀) hmul
  obtain ⟨π, _, hπ_sum, hπ_mul, _, hπ_ne⟩ :=
    exists_restricted_projection_of_ne_zero hq hr h_iso hΨ_def
      (exists_bounded_dual_ne_zero_span_of_countable_frobeniusRoot p e (Set.countable_range _))
      (hu_mem a₀) hu₀_ne
  let g (j : Fin m) : T := π (rootG j) (hrootG_mem j)
  have hπ_lin (a : Fin m → T) :
      ∑ j, a j * g j = π (∑ j, Ψ (a j) * rootG j) (hu_mem a) := by
    rw [hπ_sum Finset.univ (fun j ↦ Ψ (a j) * rootG j)
      (fun j ↦ coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso hΨ_def (a j) (hrootG_mem j))
      (hu_mem a)]
    exact Finset.sum_congr rfl fun j _ ↦ (hπ_mul (a j) (rootG j) (hrootG_mem j) _).symm
  have hπ_congr {u₁ u₂ : T'} (heq : u₁ = u₂)
      (hu₁ : ∀ α, coeff α (u₁ : _root_.MvPowerSeries σ K') ∈ E)
      (hu₂ : ∀ α, coeff α (u₂ : _root_.MvPowerSeries σ K') ∈ E) : π u₁ hu₁ = π u₂ hu₂ := by
    subst heq; rfl
  let φ : Module.Dual F M := b.constr F fun j ↦ algebraMap T F (g j)
  refine ⟨φ, fun y hy ↦ ?_, fun hφ0 ↦ ?_⟩
  · -- Step 4: Show `φ y ∈ Set.range (algebraMap T F)` for every `y ∈ M` integral over `T`.
    obtain ⟨fy, hfy⟩ := hy.exists_algebraMap_eq_iterateFrobenius (K := F) p he
    let ry : T' := tateRoot p e (fun _ ↦ rfl) fy
    have hry_pow : ry ^ q = Ψ fy := by
      rw [tateRoot_pow (fun _ ↦ rfl) hr fy, ← hΨ_def]
    have hι_y : ι y = algebraMap T' F' ry := by
      refine iterateFrobenius_inj F' p e ?_
      simp only [iterateFrobenius_def]
      rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p he y,
        ← hfy, hι_alg fy, ← hry_pow, map_pow]
    obtain ⟨s, hs⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T) (b.repr y)
    choose a ha using hs
    have hmul_T' : Ψ s * ry = ∑ j, Ψ (a j) * rootG j :=
      IsFractionRing.injective T' F' <| by
        rw [map_mul, ← hι_y, ← algebraMap_sum_mul_eq_mul b Ψ rootG ι hι_alg hι_b y s a ha]
    have hexp_ne : MvPowerSeries.expand q hq ((s : T) : _root_.MvPowerSeries σ K) ≠ 0 := fun h0 ↦
      nonZeroDivisors.ne_zero s.2 (Subtype.ext (MvPowerSeries.ext fun μ ↦ by
        rw [ZeroMemClass.coe_zero, map_zero, ← coeff_expand_smul q hq, h0, map_zero]))
    have hprod_eq : MvPowerSeries.map (algebraMap K K')
        (MvPowerSeries.expand q hq ((s : T) : _root_.MvPowerSeries σ K)) *
        (ry : _root_.MvPowerSeries σ K') =
        ((∑ j, Ψ (a j) * rootG j : T') : _root_.MvPowerSeries σ K') := by
      rw [← hmul_T', Subring.coe_mul, hΨ_def, coe_restrictedExpand, coe_restrictedMap,
        ← MvPowerSeries.map_expand]
    have hry_mem (α : σ →₀ ℕ) : coeff α (ry : _root_.MvPowerSeries σ K') ∈ E :=
      MvPowerSeries.coeff_mem_of_coeff_map_mul_mem hexp_ne
        (fun β ↦ by rw [hprod_eq]; exact hu_mem a β) α
    have hπ_eq : (s : T) * π ry hry_mem = ∑ j, a j * g j := by
      rw [hπ_lin, ← hπ_mul (s : T) ry hry_mem
        (coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso hΨ_def (s : T) hry_mem)]
      exact hπ_congr hmul_T' _ _
    have hs_F_ne : algebraMap T F s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    refine ⟨π ry hry_mem, mul_left_cancel₀ hs_F_ne ?_⟩
    rw [← map_mul, hπ_eq]
    exact (algebraMap_mul_constr_eq_algebraMap_sum b g y (s : T) a ha).symm
  · refine hπ_ne (IsFractionRing.injective T F ?_)
    dsimp only [φ] at hφ0
    rw [← hπ_lin, map_zero, ← algebraMap_mul_constr_eq_algebraMap_sum b g x₀ s₀ a₀ ha₀,
      hφ0, mul_zero]

/-- **Tate algebras are Japanese domains.** Over a complete nonarchimedean field `K` (of arbitrary
characteristic) and finitely many variables `σ`, the unit-polyradius Tate algebra `K⟨X₁, …, Xₙ⟩` is
a Japanese domain ([bosch-guntzer-remmert], §5.3.2, Theorem 1). -/
instance isJapanese {σ K : Type*} [Finite σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    Ring.IsJapanese (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) :=
  isJapanese_of_isIntegrallyClosed (fun _ : σ ↦ 1)

/-- Restricted-series rings `K{X / r}` in finitely many variables at radii in the divisible hull of
`|Kˣ|` over a complete nonarchimedean field `K` are Japanese domains. -/
theorem isJapanese_of_norm_mul_pow_eq_one {σ K : Type*} [Finite σ]
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

section Examples

/-!
### Non-vacuous instances of finite integral closure over Tate algebras

In at least one variable, the fraction field `F := GaussFractionField σ K (fun _ ↦ 1)` of the Tate
algebra `T := K⟨X₁, …, Xₙ⟩` admits genuine nontrivial finite extensions of both types:
* a degree-`2` separable extension defined by `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` (valid in every
  characteristic, including characteristic `2`), and
* in prime characteristic `p`, a nontrivial purely inseparable extension obtained by adjoining a
  `p`-th root of `Xᵢ`.

In both cases `TauCeti.MvPowerSeries.isJapanese` yields finiteness of `integralClosure T L` as a
`T`-module.
-/

universe u₁ u₂

/-- In any characteristic (including `2`), `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` defines a degree-`2` separable
extension `L` of the fraction field of `T := K⟨X₁, …, Xₙ⟩` in which `integralClosure T L` is a
finite `T`-module. -/
example (σ : Type u₁) (K : Type u₂) [Finite σ] [Nonempty σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    let T := IsRestricted.subring (R := K) (fun _ : σ ↦ 1)
    let F := GaussFractionField σ K (fun _ : σ ↦ 1)
    ∃ (L : Type (max u₁ u₂)) (_ : Field L) (_ : Algebra T L) (_ : Algebra F L)
      (_ : IsScalarTower T F L) (_ : FiniteDimensional F L) (_ : Algebra.IsSeparable F L),
      Module.finrank F L = 2 ∧ Module.Finite T (integralClosure T L) := by
  classical
  let c : σ → ℝ := fun _ ↦ 1
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let i₀ : σ := Classical.arbitrary σ
  let X₀ : T := ⟨X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
  have hx₀_ne : x₀ ≠ 0 := by
    rw [← norm_pos_iff, norm_algebraMap_gaussFractionField_X]; exact zero_lt_one
  let P : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (x₀ ^ 2) * Polynomial.X + Polynomial.C x₀
  have hP_deg : P.natDegree = 2 := by dsimp only [P]; compute_degree!
  have hP_monic : P.Monic := by dsimp only [P]; monicity!
  have hP_irr : Irreducible P :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hP_deg]; decide)
      fun z hz ↦ sq_add_algebraMap_X_sq_mul_add_algebraMap_X_ne_zero σ K c i₀ z <| by
        simpa only [P, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow,
          Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using hz
  have hP_sep : P.Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hP_irr]
    exact fun hderiv ↦ hx₀_ne (by simpa [P] using congrArg (Polynomial.eval 0) hderiv)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (P.map (algebraMap F (AlgebraicClosure F)))
    (by rw [Polynomial.degree_map_eq_of_injective (algebraMap F _).injective,
          Polynomial.degree_eq_natDegree hP_monic.ne_zero, hP_deg]; decide)
  have hβ_aeval : Polynomial.aeval β P = 0 := by rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
  have hmin : minpoly F β = P := (minpoly.eq_of_irreducible_of_monic hP_irr hβ_aeval hP_monic).symm
  have hβ_int : IsIntegral F β := ⟨P, hP_monic, hβ_aeval⟩
  have hβ_sep : IsSeparable F β := by rwa [IsSeparable, hmin]
  let L := F⟮β⟯
  have : Algebra.IsSeparable F L :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AlgebraicClosure F)).mpr hβ_sep
  have : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional hβ_int
  have hfin : Module.finrank F L = 2 := by
    rw [IntermediateField.adjoin.finrank hβ_int, hmin, hP_deg]
  let _ : Algebra T L := ((algebraMap F L).comp (algebraMap T F)).toAlgebra
  have : IsScalarTower T F L := ⟨fun t a y ↦ by
    rw [Algebra.smul_def t a, mul_smul, Algebra.smul_def t (a • y),
      RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← Algebra.smul_def]⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hfin, Ring.IsJapanese.finite_integralClosure F L⟩

/-- In prime characteristic `p`, adjoining a `p`-th root of `Xᵢ` produces a nontrivial finite purely
inseparable extension `M` of the fraction field of `T := K⟨X₁, …, Xₙ⟩` in which
`integralClosure T M` is a finite `T`-module. -/
example (σ : Type u₁) (K : Type u₂) [Finite σ] [Nonempty σ]
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    let T := IsRestricted.subring (R := K) (fun _ : σ ↦ 1)
    let F := GaussFractionField σ K (fun _ : σ ↦ 1)
    ∃ (M : Type (max u₁ u₂)) (_ : Field M) (_ : Algebra T M) (_ : Algebra F M)
      (_ : IsScalarTower T F M) (_ : FiniteDimensional F M) (_ : IsPurelyInseparable F M),
      1 < Module.finrank F M ∧ Module.Finite T (integralClosure T M) := by
  classical
  have hp : p.Prime := Fact.out
  let c : σ → ℝ := fun _ ↦ 1
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  have : ExpChar K p := .prime hp
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let i₀ : σ := Classical.arbitrary σ
  let X₀ : T := ⟨X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) x₀) hp.pos
  have hα_int : IsIntegral F α :=
    ⟨Polynomial.X ^ p - Polynomial.C x₀, Polynomial.monic_X_pow_sub_C x₀ hp.ne_zero, by simp [hα]⟩
  let M := F⟮α⟯
  have : IsPurelyInseparable F M := by
    rw [← le_perfectClosure_iff, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, x₀, by rw [pow_one, hα]⟩
  have : FiniteDimensional F M := IntermediateField.adjoin.finiteDimensional hα_int
  have hfin_gt : 1 < Module.finrank F M := by
    by_contra! hle
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp (le_antisymm hle Module.finrank_pos))
    exact pow_ne_algebraMap_gaussFractionField_X σ K c i₀ hp.ne_one z
      ((algebraMap F (AlgebraicClosure F)).injective (by rw [map_pow, hz, hα]))
  let _ : Algebra T M := ((algebraMap F M).comp (algebraMap T F)).toAlgebra
  have : IsScalarTower T F M := ⟨fun t a y ↦ by
    rw [Algebra.smul_def t a, mul_smul, Algebra.smul_def t (a • y),
      RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← Algebra.smul_def]⟩
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hfin_gt, Ring.IsJapanese.finite_integralClosure F M⟩

end Examples

end TauCeti.MvPowerSeries
