/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Japanese
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import Mathlib.Data.Finsupp.Encodable
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import TauCeti.Analysis.Normed.Module.Bases.CountableType
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.RingTheory.Finiteness.Dual
import TauCeti.RingTheory.IntegralClosure.PurelyInseparable
import TauCeti.RingTheory.MvPowerSeries.Convolution
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField
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
algebras are Nagata, and normalizations of reduced affinoid algebras are finite modules (and
affinoid `K`-algebras when `K` is nontrivially normed).

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
   `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.IntegrallyClosed`), every `y ∈ integralClosure T M`
   satisfies `y ^ q ∈ T`, so extracting its `q`-th root produces a series `ζ(y) ∈ T'` mapping to
   `y` in `F'`.
3. Clearing denominators of the `b`-coordinates of `y` in `M` and applying
   `MvPowerSeries.coeff_mem_of_coeff_map_mul_mem` confines all coefficients of `ζ(y)` to a single
   countably generated `K`-submodule `E ⊆ K'` independent of `y`.
4. Bounded `K`-linear functionals separate points of `E`
   (`Submodule.exists_bounded_dual_ne_zero_span_of_countable`, handling both trivial and nontrivial
   norms on `K`), so the `q`-adic component-dual maps
   `TauCeti.MvPowerSeries.IsRestrictedFamily.toSubringDualOfBound` produce `T`-linear functionals
   `integralClosure T M →ₗ[T] T` separating every nonzero element from `0`. The dual-evaluation
   criterion `TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval` ([bosch-guntzer-remmert],
   §4.1, Proposition 4) then shows that `integralClosure T M` is a finite `T`-module.

## Main results

* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_of_isEmpty`: in zero variables `K{X / c}`
  is Japanese without completeness or positivity hypotheses;
  `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_iff_of_isEmpty` compares `R{X / c}` with
  `R` over any normed domain `R`.
* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`: `K{X / c}` is Japanese over any complete
  ultrametric normed field `K` for finite `σ` and positive `c`.

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

/-- With no variables, `IsRestricted.subring (R := R) c` is a Japanese domain if and only if `R`
is a Japanese domain. -/
@[simp]
theorem isJapanese_isRestricted_subring_iff_of_isEmpty {σ R : Type*}
    [NormedCommRing R] [IsUltrametricDist R] [IsDomain R] [IsEmpty σ] (c : σ → ℝ) :
    Ring.IsJapanese (IsRestricted.subring (R := R) c) ↔ Ring.IsJapanese R :=
  ⟨fun _ ↦ (IsRestricted.isEmptyEquiv (R := R) c).toRingEquiv.isJapanese,
    fun _ ↦ (IsRestricted.isEmptyEquiv (R := R) c).symm.toRingEquiv.isJapanese⟩

end Empty

section PurelyInseparableHelpers

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K]

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
    (p : ℕ) [ExpChar K p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr : ∀ i, r i ^ p ^ e = c i) :
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
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have hr_def (i : σ) : r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹) := by
    rw [← hr i, Real.pow_rpow_inv_natCast (Fact.out : 0 < r i).le (pow_pos (expChar_pos K p) e).ne']
  have hΨ_inj := frobeniusRootRestrictedHom_injective (K := K) p e hr
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg (x : F) : algebraMap F F' x = Ψ.gaussFractionFieldMap hΨ_inj x :=
    RingHom.congr_fun (RingHom.algebraMap_toAlgebra _) x
  have hΨ_alg (t : T) : Ψ.gaussFractionFieldMap hΨ_inj (algebraMap T F t) =
      algebraMap T' F' (Ψ t) :=
    Ψ.gaussFractionFieldMap_algebraMap hΨ_inj t
  choose aOf haOf using fun y : integralClosure T M ↦
    IsIntegral.exists_algebraMap_eq_iterateFrobenius (A := T) (K := F) p he y.property
  let ζ (y : integralClosure T M) : T' := frobeniusRootRestrictedEquiv p e hr_def (aOf y)
  have hζ_alg (y : integralClosure T M) : algebraMap T' F' (ζ y) = ι₀ (y : M) :=
    iterateFrobenius_inj F' p e <| by
      simp only [iterateFrobenius_def]
      rw [← map_pow, frobeniusRootRestrictedEquiv_pow hr_def hr (aOf y),
        ← hΨ_alg, ← hF_alg, haOf, ← AlgHom.commutes ι₀,
        IsPurelyInseparable.algebraMap_iterateFrobenius F p he (y : M), map_pow]
  refine ⟨ζ, hζ_alg, fun y₁ y₂ ↦ IsFractionRing.injective T' F' <| by simp [hζ_alg],
    fun t y ↦ IsFractionRing.injective T' F' <| by
      simp [hζ_alg, Algebra.smul_def, IsScalarTower.algebraMap_apply T F M, hF_alg, hΨ_alg],
    fun {y} hy h0 ↦ hy <| ZeroMemClass.coe_eq_zero.mp <| (map_eq_zero_iff ι₀ ι₀.injective).mp <| by
      rw [← hζ_alg, h0, map_zero]⟩

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
  let Ψ := frobeniusRootRestrictedHom (K := K) p e hr
  have hΨ_inj := frobeniusRootRestrictedHom_injective (K := K) p e hr
  have hq : p ^ e ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
    (Finset.univ.image (b.repr y))
  choose a ha using fun j : Fin m ↦ hs (b.repr y j) (Finset.mem_image_of_mem _ (by simp))
  have hclear : ∑ j, Ψ (a j) * rootG j = Ψ s * z :=
    IsFractionRing.injective (IsRestricted.subring (R := K') r) (GaussFractionField σ K' r) <| by
      rw [map_mul, hz]
      exact b.map_sum_mul_eq_map_mul_apply (algebraMap _ _) ι (hι_alg s)
        (fun j ↦ by rw [← Algebra.smul_def, ← ha j, hι_alg]) hι_b
  have hexp_ne : _root_.MvPowerSeries.expand (p ^ e) hq ((s : T) : _root_.MvPowerSeries σ K) ≠ 0 :=
    fun h0 ↦ hΨ_inj.ne (nonZeroDivisors.ne_zero s.property) <| by
      rw [Ψ.map_zero]
      exact Subtype.ext (by rw [coe_frobeniusRootRestrictedHom p e hr (s : T), h0, map_zero,
        ZeroMemClass.coe_zero])
  refine _root_.MvPowerSeries.coeff_mem_of_coeff_map_mul_mem E hexp_ne
    (g := (z : _root_.MvPowerSeries σ K')) (fun β ↦ ?_) α
  have hβ : _root_.MvPowerSeries.map (algebraMap K K')
      (_root_.MvPowerSeries.expand (p ^ e) hq ((s : T) : _root_.MvPowerSeries σ K)) *
        (z : _root_.MvPowerSeries σ K') =
      ((∑ j, Ψ (a j) * rootG j : IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') :=
    by rw [← coe_frobeniusRootRestrictedHom p e hr (s : T), ← Subring.coe_mul, ← hclear]
  rw [hβ, AddSubmonoidClass.coe_finsetSum, map_sum]
  refine E.sum_mem fun j _ ↦ ?_
  rw [frobeniusRootRestrictedHom_apply]
  exact coeff_restrictedExpand_restrictedMap_mul_mem hq hr
    (fun _ ↦ by rw [one_mul, FrobeniusRoot.norm_algebraMap]) E (a j) (hrootG_mem j) β

end PurelyInseparableHelpers

section Japanese

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Finiteness of normalization in purely inseparable extensions.** Over a complete ultrametric
normed field `K`, for finite `σ` and positive polyradius `c : σ → ℝ`, the integral closure of
`T = K{X / c}` in a finite purely inseparable extension `M` of `GaussFractionField σ K c` is a
finite `T`-module. -/
private theorem finite_integralClosure_isRestricted_subring_of_isPurelyInseparable [Finite σ]
    {c : σ → ℝ} [∀ i, Fact (0 < c i)] (M : Type*) [Field M]
    [Algebra (GaussFractionField σ K c) M] [Algebra (IsRestricted.subring (R := K) c) M]
    [IsScalarTower (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M] :
    Module.Finite (IsRestricted.subring (R := K) c)
      (integralClosure (IsRestricted.subring (R := K) c) M) := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  obtain ⟨p, _⟩ := ExpChar.exists K
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let e := IsPurelyInseparable.exponent F M
  let q := p ^ e
  have hq : q ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  -- Embed `M` over `F` into `F' = GaussFractionField σ (FrobeniusRoot K p e) r` (`r ^ q = c`).
  let K' := FrobeniusRoot K p e
  let r : σ → ℝ := fun i ↦ c i ^ ((q : ℝ)⁻¹)
  have hr_fact : ∀ i, Fact (0 < r i) := fun i ↦ ⟨Real.rpow_pos_of_pos (Fact.out : 0 < c i) _⟩
  have hr (i : σ) : r i ^ q = c i := Real.rpow_inv_natCast_pow (Fact.out : 0 < c i).le hq
  let Ψ := frobeniusRootRestrictedHom (K := K) p e hr
  let _ : Algebra F (GaussFractionField σ K' r) :=
    (Ψ.gaussFractionFieldMap (frobeniusRootRestrictedHom_injective p e hr)).toAlgebra
  obtain ⟨m, b, rootG, ι₀, hι_alg, hι_b⟩ :=
    exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable M p e le_rfl hr
  obtain ⟨ζ, hζ_alg, hζ_add, hζ_smul, hζ_ne⟩ :=
    exists_frobeniusRoot_integralClosure_map M p e le_rfl hr ι₀
  -- All coefficients of `ζ y` lie in the countably generated `K`-submodule `E ⊆ K'`.
  let E : Submodule K K' := Submodule.span K (Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
    coeff idx.2 (rootG idx.1 : _root_.MvPowerSeries σ K'))
  have hζ_mem (y : integralClosure T M) (α : σ →₀ ℕ) :
      coeff α (ζ y : _root_.MvPowerSeries σ K') ∈ E :=
    coeff_mem_of_algebraMap_eq_apply p e hr b rootG ι₀.toRingHom hι_alg hι_b E
      (fun j β ↦ Submodule.subset_span ⟨(j, β), rfl⟩) (hζ_alg y) α
  -- Separate nonzero elements of `integralClosure T M` via `T`-linear functionals (BGR §4.1).
  have : IsNoetherianRing T := isNoetherianRing_isRestricted_subring
  refine (TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval T F M (integralClosure T M)).mpr
    (TauCeti.Module.Dual.injective_eval_iff.mpr fun y₀ hy₀ ↦ ?_)
  obtain ⟨ν, hν, φ, _, hφ, hπ_ne⟩ :=
    exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero hq hr E
      (fun _ hx ↦ Submodule.exists_bounded_dual_ne_zero_span_of_countable
        (Set.countable_range _) hx)
      (hζ_ne hy₀) (hζ_mem y₀)
  let π := IsRestrictedFamily.toSubringDualOfBound (c := c) φ hφ
  have h_iso (a : K) : ‖algebraMap K K' a‖ ≤ 1 * ‖a‖ := by
    rw [one_mul, FrobeniusRoot.norm_algebraMap]
  refine ⟨{
    toFun y := π (restrictedExpandComponentFamily hq hr ν E (ζ y) (hζ_mem y))
    map_add' y₁ y₂ := by
      rw [← map_add, ← restrictedExpandComponentFamily_add hq hr ν E (ζ y₁) (ζ y₂)
        (hζ_mem y₁) (hζ_mem y₂) (hz₁₂ := fun α ↦ by
          rw [AddMemClass.coe_add, map_add]; exact E.add_mem (hζ_mem y₁ α) (hζ_mem y₂ α))]
      exact congrArg π (restrictedExpandComponentFamily_congr hq hr ν E (hζ_add y₁ y₂))
    map_smul' t y := by
      rw [RingHom.id_apply, ← map_smul, ← restrictedExpandComponentFamily_restrictedExpand_mul hq hr
        hν h_iso E t (ζ y) (hζ_mem y)
        (hz_mul := coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E t (hζ_mem y))]
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
    finite_integralClosure_isRestricted_subring_of_isPurelyInseparable M

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
  -- Since `root P ^ p = xi ∈ F`, `AdjoinRoot P` equals its relative perfect closure over `F`.
  have htop : Subalgebra.perfectClosure F (AdjoinRoot P) p = ⊤ :=
    eq_top_iff.mpr <| (AdjoinRoot.adjoinRoot_eq_top (R := F) (f := P)).symm.trans_le <|
      Algebra.adjoin_le <| Set.singleton_subset_iff.mpr <| Subalgebra.mem_perfectClosure_iff.mpr <|
        by
          have h0 : aeval (AdjoinRoot.root P) P = 0 :=
            (AdjoinRoot.aeval_eq (f := P) P).trans AdjoinRoot.mk_self
          rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h0
          exact ⟨1, xi, by rw [pow_one, h0]⟩
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (isPurelyInseparable_iff_pow_mem F p).mpr fun _ ↦
      Subalgebra.mem_perfectClosure_iff.mp (htop ▸ Algebra.mem_top),
    ((AdjoinRoot.powerBasis hP_irr.ne_zero).finrank.trans
      (AdjoinRoot.powerBasis_dim hP_irr.ne_zero)).trans hP_deg,
    Ring.IsJapanese.finite_integralClosure F (AdjoinRoot P)⟩

/-- In arbitrary characteristic (including characteristic `2`), adjoining a square root (when
`2 ≠ 0`) or cube root (when `2 = 0`) of a coordinate variable `X i` defines a nontrivial finite
separable field extension of `GaussFractionField σ K c` in which the integral closure of `K{X / c}`
is finite. -/
example (i : σ) :
    ∃ (M : Type (max u v)) (_ : Field M) (_ : Algebra (GaussFractionField σ K c) M)
      (_ : Algebra (IsRestricted.subring (R := K) c) M),
      IsScalarTower (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) M ∧
      FiniteDimensional (GaussFractionField σ K c) M ∧
      Algebra.IsSeparable (GaussFractionField σ K c) M ∧
      1 < Module.finrank (GaussFractionField σ K c) M ∧
      Module.Finite (IsRestricted.subring (R := K) c)
        (integralClosure (IsRestricted.subring (R := K) c) M) := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let xi : F := algebraMap T F ⟨_root_.MvPowerSeries.X i, isRestricted_X c i⟩
  let q : ℕ := if (2 : F) = 0 then 3 else 2
  have hq_prime : q.Prime := by
    dsimp only [q]; split_ifs <;> decide
  have hq_ne : (q : F) ≠ 0 := by
    dsimp only [q]
    split_ifs with h2
    · push_cast
      rw [show (3 : F) = (2 : F) + 1 by norm_num, h2, zero_add]
      exact one_ne_zero
    · simpa using h2
  let P : F[X] := Polynomial.X ^ q - Polynomial.C xi
  have hP_deg : P.natDegree = q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq_prime.pos), natDegree_X_pow]
  have hP_monic : P.Monic := Polynomial.monic_X_pow_sub_C xi hq_prime.ne_zero
  have hP_irr : Irreducible P := irreducible_X_pow_sub_C_of_prime hq_prime fun z ↦
    pow_ne_algebraMap_gaussFractionField_X σ K c i hq_prime.ne_one z
  have hP_sep : P.Separable := (separable_iff_derivative_ne_zero hP_irr).mpr fun hderiv ↦
    hq_ne (by simpa [P, Polynomial.derivative_X_pow] using congrArg (Polynomial.eval 1) hderiv)
  have : Fact (Irreducible P) := ⟨hP_irr⟩
  let pb := AdjoinRoot.powerBasis hP_irr.ne_zero
  have : FiniteDimensional F (AdjoinRoot P) := pb.finite
  have hmin : minpoly F pb.gen = P :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hP_monic hP_irr.ne_zero
  have hgen_sep : IsSeparable F pb.gen := by rwa [IsSeparable, hmin]
  have : Algebra.IsSeparable F F⟮pb.gen⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AdjoinRoot P)).mpr hgen_sep
  have hadj_top : F⟮pb.gen⟯ = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra F _ pb.adjoin_gen_eq_top
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    AlgEquiv.Algebra.isSeparable ((IntermediateField.equivOfEq hadj_top).trans
      IntermediateField.topEquiv),
    by
      have hfin : Module.finrank F (AdjoinRoot P) = q :=
        (pb.finrank.trans (AdjoinRoot.powerBasis_dim hP_irr.ne_zero)).trans hP_deg
      simpa only [F, hfin] using hq_prime.one_lt,
    Ring.IsJapanese.finite_integralClosure F (AdjoinRoot P)⟩

end Examples

end TauCeti.MvPowerSeries
