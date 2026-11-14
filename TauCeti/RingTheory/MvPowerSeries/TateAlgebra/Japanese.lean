/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Japanese
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField

import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Finsupp.Encodable
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import TauCeti.Analysis.Normed.Module.Bases.CountableType
import TauCeti.FieldTheory.PurelyInseparable.Exponent
import TauCeti.RingTheory.Finiteness.Dual
import TauCeti.RingTheory.IntegralClosure.PurelyInseparable
import TauCeti.RingTheory.MvPowerSeries.Convolution
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FrobeniusRoot
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.IntegrallyClosed
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Expand

/-!
# Restricted power series and Tate algebras are Japanese

Let `K` be a complete ultrametric normed field (allowing trivial or nontrivial valuation and
arbitrary characteristic), `σ` a finite variable type, and `c : σ → ℝ` a positive polyradius. This
file proves that the ring `T = K{X / c}` of restricted power series is a Japanese (N-2) domain
(`TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`): its integral closure in every finite
extension of its fraction field, inseparable extensions included, is a finite `T`-module.
Downstream, via affinoid Noether normalization (`TauCeti.RingTheory.Affinoid.Japanese`),
`isJapanese_isRestricted_subring` implies that all affinoid domains are Japanese, all affinoid
algebras are Nagata, and normalizations of reduced affinoid algebras are finite affinoid algebras.

## Proof outline

Since `T` is Noetherian (`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`),
`TauCeti.Ring.IsJapanese.of_isPurelyInseparable` reduces the statement to a finite purely
inseparable extension `M / F` (`F = GaussFractionField σ K c`) of exponent `e`, `q = p ^ e`, where
`p = ringExpChar K`.

1. Adjoining formal `q`-th roots of all scalars (`K' = FrobeniusRoot K p e`) and `q`-th roots of
   the variables (`T' = K'{X / c^{1/q}}`, `Ψ : T →+* T'`) embeds `M` over `F` into
   `F' = GaussFractionField σ K' (c^{1/q})` sending a denominator-cleared `F`-basis `b` of `M` into
   `T'` (`exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable`).
2. Because `T` is integrally closed (`isIntegrallyClosed_isRestricted_subring`, proved in
   `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.IntegrallyClosed` by pulling the integral quotient
   `qL` back from `L{X / c}` to `K{X / c}` along `MvPowerSeries.coeff_mem_of_coeff_map_mul_mem`),
   every `y ∈ integralClosure T M` satisfies `y ^ q ∈ T`, so extracting its `q`-th root produces a
   series `ζ(y) ∈ T'` mapping to `y` in `F'`.
3. Clearing denominators of the `b`-coordinates of `y` in `M` (`algebraMap_sum_mul_eq_mul`) and
   applying `MvPowerSeries.coeff_mem_of_coeff_map_mul_mem` confines all coefficients of `ζ(y)` to a
   single countably generated `K`-submodule `E ⊆ K'` independent of `y`.
4. Bounded `K`-linear functionals separate points of `E` (by
   `Submodule.separatingDual_span_of_countable` when `K` is nontrivially normed, and by boundedness
   of all algebraic linear functionals when the norm on `K` is trivial), so the `q`-adic
   component-dual maps `TauCeti.MvPowerSeries.IsRestrictedFamily.toSubringDualOfBound` produce
   `T`-linear functionals `integralClosure T M →ₗ[T] T` separating every nonzero element from `0`.
   The dual-evaluation criterion `TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval`
   ([bosch-guntzer-remmert], §4.1, Proposition 4) then shows that `integralClosure T M` is a finite
   `T`-module.

## Main results

* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_of_isEmpty`: in zero variables `K{X / c}`
  is Japanese without completeness or positivity hypotheses.
* `TauCeti.MvPowerSeries.finite_of_isIntegralClosure_isRestricted_subring_of_isPurelyInseparable`:
  finiteness of any integral closure of `K{X / c}` in a finite purely inseparable extension of
  `GaussFractionField σ K c`.
* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`: `K{X / c}` is Japanese over any complete
  ultrametric normed field `K` for finite `σ` and positive `c`.
* `TauCeti.MvPowerSeries.finite_of_isIntegralClosure_isRestricted_subring`: finiteness of any
  integral closure of `K{X / c}` in a finitely generated field extension of any fraction field of
  `K{X / c}`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.5.3, 4.1
  (Proposition 4), and 5.3.1.
* [Stacks Project, Lemma 10.161.12 (032N)](https://stacks.math.columbia.edu/tag/032N).
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section Empty

/-- In zero variables (`[IsEmpty σ]`), `K{X / c}` is Japanese without completeness of `K` or
positivity of `c`. -/
instance isJapanese_isRestricted_subring_of_isEmpty {σ : Type*} {K : Type*} [NormedField K]
    [IsUltrametricDist K] [IsEmpty σ] {c : σ → ℝ} :
    Ring.IsJapanese (IsRestricted.subring (R := K) c) :=
  (IsRestricted.isEmptyEquiv (R := K) c).symm.toRingEquiv.isJapanese

end Empty

section PurelyInseparableHelpers

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- On any countably generated `K`-submodule `E` of `FrobeniusRoot K p e` over a complete
ultrametric normed field `K` (whether trivially or nontrivially normed), bounded `K`-linear
functionals separate points of `E`. -/
private theorem exists_bounded_dual_ne_zero_frobeniusRoot [CompleteSpace K] (p : ℕ) [ExpChar K p]
    (e : ℕ) {S : Set (FrobeniusRoot K p e)} (hS : S.Countable) (x : Submodule.span K S)
    (hx : x ≠ 0) :
    ∃ (φ : Submodule.span K S →ₗ[K] K) (C : ℝ), (∀ y, ‖φ y‖ ≤ C * ‖y‖) ∧ φ x ≠ 0 := by
  by_cases hnt : ∃ a : K, 1 < ‖a‖
  · let : NontriviallyNormedField K := { ‹NormedField K› with non_trivial := hnt }
    have : SeparatingDual K (Submodule.span K S) :=
      Submodule.separatingDual_span_of_countable hS
    obtain ⟨f_dual, hf_ne⟩ := SeparatingDual.exists_ne_zero (R := K) hx
    exact ⟨f_dual.toLinearMap, ‖f_dual‖, f_dual.le_opNorm, hf_ne⟩
  · push Not at hnt
    have hK_eq_one {a : K} (ha : a ≠ 0) : ‖a‖ = 1 := by
      refine le_antisymm (hnt a) ?_
      have hmul := norm_mul a a⁻¹
      rw [mul_inv_cancel₀ ha, norm_one] at hmul
      nlinarith [hnt a⁻¹, norm_nonneg a]
    have hy_eq_one {y : Submodule.span K S} (hy : y ≠ 0) : ‖y‖ = 1 := by
      have hval_ne : FrobeniusRoot.val K p e (y : FrobeniusRoot K p e) ≠ 0 :=
        (map_ne_zero_iff _ (RingHom.injective _)).mpr (Subtype.coe_ne_coe.mpr hy)
      rw [← Submodule.norm_coe, FrobeniusRoot.norm_def, hK_eq_one hval_ne, Real.one_rpow]
    obtain ⟨φ, hφx⟩ := Module.Projective.exists_dual_ne_zero K hx
    refine ⟨φ, 1, fun y ↦ ?_, hφx⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · rw [hy_eq_one hy, mul_one]
      exact hnt (φ y)

/-- Since `T = K{X / c}` is integrally closed, extracting formal `p ^ e`-th roots of `y ^ p ^ e ∈ T`
gives an injective `T`-semilinear map `ζ : integralClosure T M → (FrobeniusRoot K p e){X / r}`
compatible with the fraction-field embedding `ι₀`. -/
private theorem exists_frobeniusRoot_integralClosure_map [Finite σ]
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [Algebra (IsRestricted.subring (R := K) c) M]
    [IsScalarTower (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p] [ExpChar (GaussFractionField σ K c) p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr_def : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) (hr : ∀ i, r i ^ p ^ e = c i) :
    let K' := FrobeniusRoot K p e
    let T := IsRestricted.subring (R := K) c
    let F := GaussFractionField σ K c
    let T' := IsRestricted.subring (R := K') r
    let F' := GaussFractionField σ K' r
    let Ψ := frobeniusRootRestrictedHom (K := K) p e hr
    letI : Algebra F F' :=
      (Ψ.gaussFractionFieldMap (frobeniusRootRestrictedHom_injective p e hr)).toAlgebra
    ∀ (ι₀ : M →ₐ[F] F'),
      ∃ ζ : integralClosure T M → T',
        (∀ y, algebraMap T' F' (ζ y) = ι₀ (y : M)) ∧
        (∀ y₁ y₂, ζ (y₁ + y₂) = ζ y₁ + ζ y₂) ∧
        (∀ (t : T) y, ζ (t • y) = Ψ t * ζ y) ∧
        (∀ {y}, y ≠ 0 → ζ y ≠ 0) := by
  intro K' T F T' F' Ψ ι₀
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have hΨ_inj : Function.Injective Ψ := frobeniusRootRestrictedHom_injective p e hr
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg (x : F) : algebraMap F F' x = Ψ.gaussFractionFieldMap hΨ_inj x := rfl
  let aOf (y : integralClosure T M) : T :=
    (IsIntegral.exists_algebraMap_eq_iterateFrobenius (A := T) (K := F) p he y.2).choose
  have haOf (y : integralClosure T M) :
      algebraMap T F (aOf y) = IsPurelyInseparable.iterateFrobenius F M p he (y : M) :=
    (IsIntegral.exists_algebraMap_eq_iterateFrobenius (A := T) (K := F) p he y.2).choose_spec
  let ζ (y : integralClosure T M) : T' := frobeniusRootRestrictedEquiv p e hr_def (aOf y)
  have hζ_alg (y : integralClosure T M) : algebraMap T' F' (ζ y) = ι₀ (y : M) := by
    refine iterateFrobenius_inj F' p e ?_
    simp only [iterateFrobenius_def]
    rw [← map_pow, frobeniusRootRestrictedEquiv_pow hr_def hr (aOf y),
      ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj, ← hF_alg, haOf, ← AlgHom.commutes ι₀,
      IsPurelyInseparable.algebraMap_iterateFrobenius F p he (y : M), map_pow]
  refine ⟨ζ, hζ_alg, fun y₁ y₂ ↦ IsFractionRing.injective T' F' ?_,
    fun t y ↦ IsFractionRing.injective T' F' ?_, fun {y} hy h0 ↦ hy ?_⟩
  · rw [map_add, hζ_alg (y₁ + y₂), hζ_alg y₁, hζ_alg y₂, AddMemClass.coe_add, map_add]
  · rw [map_mul, hζ_alg (t • y), hζ_alg y, Subalgebra.coe_smul, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply T F M, AlgHom.commutes, hF_alg,
      Ψ.gaussFractionFieldMap_algebraMap hΨ_inj]
  · exact ZeroMemClass.coe_eq_zero.mp <| (map_eq_zero_iff ι₀ ι₀.injective).mp <| by
      rw [← hζ_alg, h0, map_zero]

/-- Clearing denominators of the `b`-coordinates of `y` and descending along
`MvPowerSeries.coeff_mem_of_coeff_map_mul_mem` shows that any `z ∈ (FrobeniusRoot K p e){X / r}`
mapping to `ι y` has all power-series coefficients in `E` whenever the basis images `rootG j` do. -/
private theorem coeff_mem_of_algebraMap_eq_apply
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {M : Type*} [Field M] [Algebra (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p] (e : ℕ) (hr : ∀ i, r i ^ p ^ e = c i)
    {m : ℕ} (b : Module.Basis (Fin m) (GaussFractionField σ K c) M)
    (rootG : Fin m → IsRestricted.subring (R := FrobeniusRoot K p e) r)
    (ι : M →+* GaussFractionField σ (FrobeniusRoot K p e) r)
    (hι_alg : ∀ t : IsRestricted.subring (R := K) c,
      ι (algebraMap _ M (algebraMap _ (GaussFractionField σ K c) t)) =
        algebraMap _ (GaussFractionField σ (FrobeniusRoot K p e) r)
          (frobeniusRootRestrictedHom p e hr t))
    (hι_b : ∀ j, ι (b j) = algebraMap _ _ (rootG j))
    (E : Submodule K (FrobeniusRoot K p e))
    (hrootG_mem : ∀ (j : Fin m) (α : σ →₀ ℕ),
      coeff α (rootG j : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) ∈ E)
    {y : M} {z : IsRestricted.subring (R := FrobeniusRoot K p e) r}
    (hz : algebraMap _ _ z = ι y) (α : σ →₀ ℕ) :
    coeff α (z : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) ∈ E := by
  classical
  let K' := FrobeniusRoot K p e
  let T := IsRestricted.subring (R := K) c
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  let Ψ : T →+* T' := frobeniusRootRestrictedHom p e hr
  have hΨ_inj : Function.Injective Ψ := frobeniusRootRestrictedHom_injective p e hr
  have hq : p ^ e ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
    (Finset.univ.image (b.repr y))
  choose a ha using fun j : Fin m ↦ hs (b.repr y j) (Finset.mem_image_of_mem _ (by simp))
  have hs_ne : (s : T) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hclear : Ψ s * z = ∑ j, Ψ (a j) * rootG j :=
    IsFractionRing.injective T' F' <| by
      rw [map_mul, hz, ← algebraMap_sum_mul_eq_mul b Ψ rootG ι hι_alg hι_b y s a ha]
  have hexp_ne : _root_.MvPowerSeries.expand (p ^ e) hq ((s : T) : _root_.MvPowerSeries σ K) ≠ 0 :=
    fun h0 ↦ hΨ_inj.ne hs_ne <| by
      rw [Ψ.map_zero]
      exact Subtype.ext (by rw [coe_frobeniusRootRestrictedHom p e hr (s : T), h0, map_zero]; rfl)
  refine _root_.MvPowerSeries.coeff_mem_of_coeff_map_mul_mem E hexp_ne
    (g := (z : _root_.MvPowerSeries σ K')) (fun β ↦ ?_) α
  have hβ : _root_.MvPowerSeries.map (algebraMap K K')
      (_root_.MvPowerSeries.expand (p ^ e) hq ((s : T) : _root_.MvPowerSeries σ K)) *
        (z : _root_.MvPowerSeries σ K') =
      ((∑ j, Ψ (a j) * rootG j : T') : _root_.MvPowerSeries σ K') := by
    rw [← coe_frobeniusRootRestrictedHom p e hr (s : T), ← Subring.coe_mul, hclear]
  rw [hβ, AddSubmonoidClass.coe_finsetSum, map_sum]
  refine E.sum_mem fun j _ ↦ ?_
  rw [frobeniusRootRestrictedHom_apply]
  exact coeff_restrictedExpand_restrictedMap_mul_mem hq hr
    (fun x ↦ by rw [one_mul, FrobeniusRoot.norm_algebraMap]) E (a j) (hrootG_mem j) β

end PurelyInseparableHelpers

section Japanese

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Finiteness of normalization in purely inseparable extensions.** Over a complete ultrametric
normed field `K`, for finite `σ` and positive polyradius `c : σ → ℝ`, any integral closure `C` of
`T = K{X / c}` in a finite purely inseparable extension `M` of `GaussFractionField σ K c` is a
finite `T`-module. -/
theorem finite_of_isIntegralClosure_isRestricted_subring_of_isPurelyInseparable [Finite σ]
    {c : σ → ℝ} [∀ i, Fact (0 < c i)] (M : Type*) [Field M]
    [Algebra (GaussFractionField σ K c) M] [Algebra (IsRestricted.subring (R := K) c) M]
    [IsScalarTower (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (C : Type*) [CommRing C] [Algebra (IsRestricted.subring (R := K) c) C] [Algebra C M]
    [IsScalarTower (IsRestricted.subring (R := K) c) C M]
    [IsIntegralClosure C (IsRestricted.subring (R := K) c) M] :
    Module.Finite (IsRestricted.subring (R := K) c) C := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  -- Reduce from an abstract integral closure `C` to `integralClosure T M`.
  suffices Module.Finite T (integralClosure T M) from
    .equiv (IsIntegralClosure.equiv T (integralClosure T M) M C).toLinearEquiv
  obtain ⟨p, _⟩ := ExpChar.exists K
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let e := IsPurelyInseparable.exponent F M
  let q := p ^ e
  have hq : q ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  have hqR_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  -- Embed `M` over `F` into `F' = GaussFractionField σ (FrobeniusRoot K p e) r` (`r ^ q = c`).
  let K' := FrobeniusRoot K p e
  let r : σ → ℝ := fun i ↦ c i ^ ((q : ℝ)⁻¹)
  have hr_fact : ∀ i, Fact (0 < r i) := fun i ↦
    ⟨Real.rpow_pos_of_pos (Fact.out : 0 < c i) _⟩
  have hr (i : σ) : r i ^ q = c i := by
    dsimp only [r, q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < c i).le,
      inv_mul_cancel₀ hqR_ne, Real.rpow_one]
  let Ψ := frobeniusRootRestrictedHom (K := K) p e hr
  let _ : Algebra F (GaussFractionField σ K' r) :=
    (Ψ.gaussFractionFieldMap (frobeniusRootRestrictedHom_injective p e hr)).toAlgebra
  obtain ⟨m, b, rootG, ι₀, hι_alg, hι_b⟩ :=
    exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable M p e le_rfl
      (fun _ ↦ rfl) hr
  obtain ⟨ζ, hζ_alg, hζ_add, hζ_smul, hζ_ne⟩ :=
    exists_frobeniusRoot_integralClosure_map M p e le_rfl (fun _ ↦ rfl) hr ι₀
  -- All coefficients of `ζ y` lie in the countably generated `K`-submodule `E ⊆ K'`.
  let S : Set K' := Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
    coeff idx.2 (rootG idx.1 : _root_.MvPowerSeries σ K')
  let E : Submodule K K' := Submodule.span K S
  have hζ_mem (y : integralClosure T M) (α : σ →₀ ℕ) :
      coeff α (ζ y : _root_.MvPowerSeries σ K') ∈ E :=
    coeff_mem_of_algebraMap_eq_apply p e hr b rootG ι₀.toRingHom hι_alg hι_b E
      (fun j β ↦ Submodule.subset_span ⟨(j, β), rfl⟩) (hζ_alg y) α
  -- Separate nonzero elements of `integralClosure T M` via `T`-linear functionals (BGR §4.1).
  have : IsNoetherianRing T := isNoetherianRing_isRestricted_subring
  refine (TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval T F M (integralClosure T M)).mpr
    (Module.Dual.injective_eval_iff.mpr fun y₀ hy₀ ↦ ?_)
  obtain ⟨ν, hν, φ, B, hφ, hπ_ne⟩ :=
    exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero hq hr E
      (exists_bounded_dual_ne_zero_frobeniusRoot p e (Set.countable_range _))
      (hζ_ne hy₀) (hζ_mem y₀)
  let π := IsRestrictedFamily.toSubringDualOfBound (c := c) φ hφ
  refine ⟨{
    toFun y := π (restrictedExpandComponentFamily hq hr ν E (ζ y) (hζ_mem y))
    map_add' y₁ y₂ := by
      rw [← map_add, ← restrictedExpandComponentFamily_add hq hr ν E (ζ y₁) (ζ y₂)
        (hζ_mem y₁) (hζ_mem y₂) (hz₁₂ := fun α ↦ by
          rw [AddMemClass.coe_add, map_add]; exact E.add_mem (hζ_mem y₁ α) (hζ_mem y₂ α))]
      exact congrArg π (restrictedExpandComponentFamily_congr hq hr ν E (hζ_add y₁ y₂))
    map_smul' t y := by
      have h_iso (a : K) : ‖algebraMap K K' a‖ ≤ 1 * ‖a‖ := by
        rw [one_mul, FrobeniusRoot.norm_algebraMap]
      rw [RingHom.id_apply, ← map_smul,
        ← restrictedExpandComponentFamily_restrictedExpand_mul hq hr hν h_iso E t (ζ y)
          (hζ_mem y) (hz_mul := coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E t
            (hζ_mem y))]
      exact congrArg π (restrictedExpandComponentFamily_congr hq hr ν E
        ((hζ_smul t y).trans (congrArg (· * ζ y) (frobeniusRootRestrictedHom_apply p e hr t)))) },
    hπ_ne⟩

/-- **Restricted power series and Tate algebras are Japanese.** Over any complete ultrametric normed
field `K` (of arbitrary characteristic and trivial or nontrivial valuation), the ring `K{X / c}` of
restricted power series in finitely many variables at any positive polyradius `c` is a Japanese
(N-2) domain. In particular, the Tate algebra `K⟨X₁, …, Xₙ⟩` (`c = 1`) is Japanese. -/
instance isJapanese_isRestricted_subring [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    Ring.IsJapanese (IsRestricted.subring (R := K) c) :=
  have : IsNoetherianRing (IsRestricted.subring (R := K) c) :=
    isNoetherianRing_isRestricted_subring
  Ring.IsJapanese.of_isPurelyInseparable (GaussFractionField σ K c) fun M _ _ _ _ _ _ ↦
    finite_of_isIntegralClosure_isRestricted_subring_of_isPurelyInseparable M (integralClosure _ M)

/-- **Finiteness of normalization over restricted power series.** For any model `F` of the fraction
field of `K{X / c}` (`σ` finite, `c` positive, `K` complete ultrametric) and any finitely generated
field extension `L / F` (separable, inseparable, or transcendental), every integral closure `C` of
`K{X / c}` in `L` is a finite `K{X / c}`-module. -/
theorem finite_of_isIntegralClosure_isRestricted_subring [Finite σ] {c : σ → ℝ}
    [∀ i, Fact (0 < c i)] (F : Type*) (L : Type*) [Field F] [Field L]
    [Algebra (IsRestricted.subring (R := K) c) F]
    [IsFractionRing (IsRestricted.subring (R := K) c) F]
    [Algebra F L] [Algebra (IsRestricted.subring (R := K) c) L]
    [IsScalarTower (IsRestricted.subring (R := K) c) F L] [Algebra.EssFiniteType F L]
    (C : Type*) [CommRing C] [Algebra (IsRestricted.subring (R := K) c) C] [Algebra C L]
    [IsScalarTower (IsRestricted.subring (R := K) c) C L]
    [IsIntegralClosure C (IsRestricted.subring (R := K) c) L] :
    Module.Finite (IsRestricted.subring (R := K) c) C :=
  Ring.IsJapanese.finite_of_isIntegralClosure F L C

end Japanese

section Examples

open Polynomial
open scoped IntermediateField

universe u v

variable {σ : Type u} {K : Type v} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- In prime characteristic `p`, adjoining a `p`-th root of a coordinate variable `X i` (`Y^p - X_i
= 0`) defines a genuinely nontrivial (`finrank = p > 1`) purely inseparable field extension of
`GaussFractionField σ K c` in which the integral closure of `K{X / c}` is finite. -/
example (p : ℕ) [Fact p.Prime] [CharP K p] (i : σ) :
    ∃ (M : Type (max u v)) (_ : Field M) (_ : Algebra (GaussFractionField σ K c) M)
      (_ : Algebra (IsRestricted.subring (R := K) c) M),
      IsScalarTower (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) M ∧
      FiniteDimensional (GaussFractionField σ K c) M ∧
      IsPurelyInseparable (GaussFractionField σ K c) M ∧
      Module.finrank (GaussFractionField σ K c) M = p ∧
      Module.Finite (IsRestricted.subring (R := K) c)
        (integralClosure (IsRestricted.subring (R := K) c) M) := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  have hp_prime : p.Prime := Fact.out
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have : ExpChar F p := .prime hp_prime
  let xi : F := algebraMap T F ⟨_root_.MvPowerSeries.X i, isRestricted_X c i⟩
  let P : F[X] := Polynomial.X ^ p - Polynomial.C xi
  have hP_irr : Irreducible P := irreducible_X_pow_sub_C_of_prime hp_prime fun z ↦
    pow_ne_algebraMap_gaussFractionField_X σ K c i hp_prime.ne_one z
  have : Fact (Irreducible P) := ⟨hP_irr⟩
  have : FiniteDimensional F (AdjoinRoot P) := (AdjoinRoot.powerBasis hP_irr.ne_zero).finite
  have : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (algebraMap F (AdjoinRoot P)).injective p
  have : ExpChar (AdjoinRoot P) p := .prime hp_prime
  have hP_deg : P.natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hp_prime.pos), natDegree_X_pow]
  have hfinrank : Module.finrank F (AdjoinRoot P) = p :=
    ((AdjoinRoot.powerBasis hP_irr.ne_zero).finrank.trans
      (AdjoinRoot.powerBasis_dim hP_irr.ne_zero)).trans hP_deg
  -- Since `root P ^ p = xi ∈ F`, `AdjoinRoot P` equals its relative perfect closure over `F`.
  have hinsep : IsPurelyInseparable F (AdjoinRoot P) := by
    have htop : Subalgebra.perfectClosure F (AdjoinRoot P) p = ⊤ :=
      eq_top_iff.mpr <| (AdjoinRoot.adjoinRoot_eq_top (R := F) (f := P)).symm.trans_le <|
        Algebra.adjoin_le <| Set.singleton_subset_iff.mpr <|
          Subalgebra.mem_perfectClosure_iff.mpr <| by
            have h0 := AdjoinRoot.eval₂_root P
            rw [eval₂_sub, eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h0
            exact ⟨1, xi, by rw [pow_one, h0]; rfl⟩
    exact (isPurelyInseparable_iff_pow_mem F p).mpr fun y ↦
      Subalgebra.mem_perfectClosure_iff.mp (htop ▸ Algebra.mem_top)
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hinsep, hfinrank, Ring.IsJapanese.finite_integralClosure F (AdjoinRoot P)⟩

/-- In arbitrary characteristic (including characteristic `2`), `Y^2 + X_i^2 Y + X_i = 0` defines a
degree-`2` separable field extension of `GaussFractionField σ K c` in which the integral closure of
`K{X / c}` is finite. -/
example (i : σ) :
    ∃ (M : Type (max u v)) (_ : Field M) (_ : Algebra (GaussFractionField σ K c) M)
      (_ : Algebra (IsRestricted.subring (R := K) c) M),
      IsScalarTower (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) M ∧
      FiniteDimensional (GaussFractionField σ K c) M ∧
      Algebra.IsSeparable (GaussFractionField σ K c) M ∧
      Module.finrank (GaussFractionField σ K c) M = 2 ∧
      Module.Finite (IsRestricted.subring (R := K) c)
        (integralClosure (IsRestricted.subring (R := K) c) M) := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let xi : F := algebraMap T F ⟨_root_.MvPowerSeries.X i, isRestricted_X c i⟩
  have hxi_ne : xi ≠ 0 := by
    rw [← norm_pos_iff, norm_algebraMap_gaussFractionField_X]; exact Fact.out
  -- Step 1: `P = X^2 + xi^2 X + xi` is monic of degree `2`, rootless over `F`, irreducible,
  -- and separable (since `P'(0) = xi^2 ≠ 0`).
  let P : F[X] := Polynomial.X ^ 2 + Polynomial.C (xi ^ 2) * Polynomial.X + Polynomial.C xi
  have hP_deg : P.natDegree = 2 := by dsimp only [P]; compute_degree!
  have hP_monic : P.Monic := by dsimp only [P]; monicity!
  have hP_irr : Irreducible P :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hP_deg]; decide)
      (not_isRoot_X_sq_add_C_sq_mul_X_add_C σ K c i)
  have hP_sep : P.Separable := by
    rw [separable_iff_derivative_ne_zero hP_irr]
    exact fun hderiv ↦
      pow_ne_zero 2 hxi_ne (by simpa [P, eq_comm] using congrArg (Polynomial.eval 0) hderiv)
  -- Step 2: Conclude separability, dimension `2`, and finite normalization of `AdjoinRoot P`.
  have : Fact (Irreducible P) := ⟨hP_irr⟩
  have : FiniteDimensional F (AdjoinRoot P) := (AdjoinRoot.powerBasis hP_irr.ne_zero).finite
  have hmin : minpoly F (AdjoinRoot.powerBasis hP_irr.ne_zero).gen = P :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hP_monic hP_irr.ne_zero
  have hgen_sep : IsSeparable F (AdjoinRoot.powerBasis hP_irr.ne_zero).gen := by
    rwa [IsSeparable, hmin]
  have : Algebra.IsSeparable F F⟮(AdjoinRoot.powerBasis hP_irr.ne_zero).gen⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AdjoinRoot P)).mpr hgen_sep
  have hadj_top : F⟮(AdjoinRoot.powerBasis hP_irr.ne_zero).gen⟯ = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra F _
      (AdjoinRoot.powerBasis hP_irr.ne_zero).adjoin_gen_eq_top
  have : Algebra.IsSeparable F (AdjoinRoot P) :=
    AlgEquiv.Algebra.isSeparable
      ((IntermediateField.equivOfEq hadj_top).trans IntermediateField.topEquiv)
  have hfinrank : Module.finrank F (AdjoinRoot P) = 2 :=
    ((AdjoinRoot.powerBasis hP_irr.ne_zero).finrank.trans
      (AdjoinRoot.powerBasis_dim hP_irr.ne_zero)).trans hP_deg
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hfinrank, Ring.IsJapanese.finite_integralClosure F (AdjoinRoot P)⟩

end Examples

end TauCeti.MvPowerSeries
