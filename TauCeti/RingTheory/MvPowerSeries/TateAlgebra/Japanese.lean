/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Japanese
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Finsupp.Encodable
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import TauCeti.Analysis.Normed.Module.Bases.CountableType
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.FieldTheory.PurelyInseparable.Exponent
import TauCeti.RingTheory.Finiteness.Dual
import TauCeti.RingTheory.IntegralClosure.PurelyInseparable
import TauCeti.RingTheory.MvPowerSeries.Convolution
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FrobeniusRoot
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Rescale
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.Topology.MetricSpace.Ultra.Completion

/-!
# Restricted power series and Tate algebras are integrally closed and Japanese

Let `K` be an ultrametric normed field, `σ` a finite variable type, and `c : σ → ℝ` a positive
polyradius.

1. **Integral closedness (`TauCeti.MvPowerSeries.isIntegrallyClosed_isRestricted_subring`).**
   Without completeness or nontriviality of the norm on `K`, the ring `T = K{X / c}` of restricted
   power series at polyradius `c` is integrally closed. Passing to the completion `L` of the
   Gauss-normed fraction field `GaussFractionField σ K c` produces invertible scalars of norm
   `c i`, so `L{X / c} ≃ₐ[L] L⟨X⟩` is a unique factorization domain and hence integrally closed;
   coefficientwise descent along `MvPowerSeries.coeff_mem_of_map_mul_coeff_mem` pulls denominators
   back from `L{X / c}` to `K{X / c}`.

2. **Japanese property (`TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`).**
   When `K` is complete (still allowing trivial or nontrivial valuation and arbitrary characteristic
   and positive polyradius `c`), `T = K{X / c}` is a Japanese (N-2) domain: its integral closure in
   every finite extension of its fraction field, inseparable extensions included, is a finite
   `T`-module.

   Since `T` is Noetherian (`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`),
   `TauCeti.Ring.IsJapanese.of_isPurelyInseparable` reduces the statement to a finite purely
   inseparable extension `M / F` (`F = GaussFractionField σ K c`) of exponent `e`, `q = p ^ e`,
   where `p = ringExpChar K`. Adjoining formal `q`-th roots of all scalars (`K' = FrobeniusRoot K p
   e`) and `q`-th roots of the variables (`T' = K'{X / c^{1/q}}`, `Ψ : T →+* T'`) embeds `M` over
   `F` into `F' = GaussFractionField σ K' (c^{1/q})`. Because `T` is integrally closed, every
   `y ∈ integralClosure T M` satisfies `y ^ q ∈ T`, so extracting its `q`-th root produces a series
   `ζ(y) ∈ T'` mapping to `y` in `F'`. Clearing denominators of a basis expansion of `y` in `M` and
   applying `MvPowerSeries.coeff_mem_of_map_mul_coeff_mem` confines all coefficients of `ζ(y)` to a
   single countably generated `K`-submodule `E ⊆ K'` independent of `y`. Bounded `K`-linear
   functionals separate points of `E` (by `Submodule.separatingDual_span_of_countable` when `K` is
   nontrivially normed, and by boundedness of all algebraic linear functionals when the norm on `K`
   is trivial), so the `q`-adic component-dual maps
   `TauCeti.MvPowerSeries.IsRestrictedFamily.toSubringDualOfBound` produce `T`-linear functionals
   `integralClosure T M →ₗ[T] T` separating every nonzero element from `0`. The dual-evaluation
   finiteness criterion `TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval` ([BGR] §4.1,
   Proposition 4) then shows that `integralClosure T M` is a finite `T`-module.

## Main results

* `TauCeti.MvPowerSeries.isIntegrallyClosed_isRestricted_subring`: `K{X / c}` is integrally closed
  for finite `σ` and positive `c` over any ultrametric normed field `K`.
* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring_of_isEmpty`: in zero variables `K{X / c}`
  is Japanese without completeness or positivity hypotheses.
* `TauCeti.MvPowerSeries.finite_integralClosure_isRestricted_subring_of_isPurelyInseparable`:
  finiteness of the integral closure of `K{X / c}` in a finite purely inseparable extension of
  `GaussFractionField σ K c`.
* `TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`: `K{X / c}` is Japanese over any complete
  ultrametric normed field `K` for finite `σ` and positive `c`.
* `TauCeti.MvPowerSeries.finite_integralClosure_isRestricted_subring`: finiteness of any integral
  closure of `K{X / c}` in a finite extension of any fraction field of `K{X / c}`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.5.3, 4.1
  (Proposition 4), and 5.3.1.
* [Stacks Project, Lemma 10.161.12 (032N)](https://stacks.math.columbia.edu/tag/032N).
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section IntegrallyClosed

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Over any ultrametric normed field `K` (complete or not), the ring `K{X / c}` of restricted power
series in finitely many variables at arbitrary positive polyradius `c` is integrally closed. -/
instance isIntegrallyClosed_isRestricted_subring [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    IsIntegrallyClosed (IsRestricted.subring (R := K) c) := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let L := (gaussFractionNorm σ K c).Completion
  have : IsUltrametricDist L :=
    ⟨fun x y z ↦ by
      simpa only [← (AbsoluteValue.Completion.isometry_toCompletion _).dist_eq] using
        dist_triangle_max _ _ _⟩
  let TL := IsRestricted.subring (R := L) c
  let FL := GaussFractionField σ L c
  -- Step 1: In `L = (gaussFractionNorm σ K c).Completion`, the coordinate elements `X i` give
  -- multiplicative units of norm `c i`, so `L{X / c} ≃ₐ[L] L⟨X⟩` is a UFD and integrally closed.
  have hTL_ic : IsIntegrallyClosed TL := by
    let u₀ (i : σ) : L := ((algebraMap T F ⟨X i, isRestricted_X c i⟩ : F) : L)
    have hu₀_norm (i : σ) : ‖u₀ i‖ = c i := by
      rw [← AbsoluteValue.Completion.norm_toCompletion, AbsoluteValue.Completion.toCompletion_coe,
        UniformSpace.Completion.norm_coe, norm_algebraMap_gaussFractionField_X]
    have hu₀_ne (i : σ) : u₀ i ≠ 0 :=
      norm_pos_iff.mp (by rw [hu₀_norm]; exact Fact.out)
    let u (i : σ) : Lˣ := Units.mk0 (u₀ i) (hu₀_ne i)
    have hu_mul (i : σ) : IsNormMulUnit (u i : L) :=
      (Units.isNormMulUnit_iff_norm_inv (u i)).mpr (by rw [Units.val_inv_eq_inv_val, norm_inv])
    have hrs (i : σ) : ‖(u i : L)‖ * (1 : ℝ) = c i := by
      rw [mul_one]; exact hu₀_norm i
    exact IsIntegrallyClosed.of_equiv (restrictedRescaleEquiv u hu_mul hrs).symm.toRingEquiv
  -- Step 2: Embed `T →+* TL` and `F →+* FL` isometrically via `algebraMap K L`.
  have hnorm_alg (a : K) : ‖algebraMap K L a‖ = ‖a‖ := by
    rw [AbsoluteValue.Completion.algebraMap_def, ← AbsoluteValue.Completion.norm_toCompletion,
      AbsoluteValue.Completion.toCompletion_coe, UniformSpace.Completion.norm_coe,
      norm_algebraMap']
  have h_iso (a : K) : ‖algebraMap K L a‖ ≤ 1 * ‖a‖ := by rw [one_mul, hnorm_alg]
  let ψ : T →+* TL := restrictedMap (algebraMap K L) h_iso
  have hψ_norm (f : T) : ‖ψ f‖ = ‖f‖ := norm_restrictedMap (algebraMap K L) h_iso hnorm_alg f
  have hψ_inj : Function.Injective ψ :=
    ((AddMonoidHomClass.isometry_iff_norm ψ).mpr hψ_norm).injective
  let Φ : F →+* FL := ψ.gaussFractionFieldMap hψ_inj
  -- Step 3: Pull back integral elements of `F` from `TL` to `T` coefficientwise.
  refine (isIntegrallyClosed_iff F).mpr fun {x} hx ↦ ?_
  have hΦx : IsIntegral TL (Φ x) := by
    obtain ⟨P, hPm, hPx⟩ := hx
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    have hcomp : Φ.comp (algebraMap T F) = (algebraMap TL FL).comp ψ :=
      RingHom.ext (ψ.gaussFractionFieldMap_algebraMap hψ_inj)
    rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hPx, map_zero]
  obtain ⟨qL, hqL⟩ := (isIntegrallyClosed_iff FL).mp hTL_ic hΦx
  obtain ⟨f, g, hg_mem, rfl⟩ := IsFractionRing.div_surjective T x
  have hg_ne : (g : T) ≠ 0 := nonZeroDivisors.ne_zero hg_mem
  have hψg_ne : algebraMap TL FL (ψ g) ≠ 0 := by
    refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ?_)
    exact fun h0 ↦ hg_ne (hψ_inj (h0.trans ψ.map_zero.symm))
  have hmul_TL : ψ g * qL = ψ f := by
    apply IsFractionRing.injective TL FL
    rw [map_mul, hqL, map_div₀, ψ.gaussFractionFieldMap_algebraMap hψ_inj f,
      ψ.gaussFractionFieldMap_algebraMap hψ_inj g, mul_div_cancel₀ _ hψg_ne]
  -- Step 4: Every coefficient of `qL` lies in `range (algebraMap K L)` by convolution descent.
  let E : Submodule K L := LinearMap.range (Algebra.linearMap K L)
  have hqL_mem : ∀ α, coeff α (qL : _root_.MvPowerSeries σ L) ∈ E := by
    refine _root_.MvPowerSeries.coeff_mem_of_map_mul_coeff_mem E
      (Subtype.coe_ne_coe.mpr hg_ne) (g := (qL : _root_.MvPowerSeries σ L)) fun α ↦ ?_
    have hcoeff := congrArg (fun h : TL ↦ coeff α (h : _root_.MvPowerSeries σ L)) hmul_TL
    rw [Subring.coe_mul, coe_restrictedMap, coeff_restrictedMap] at hcoeff
    rw [hcoeff]
    exact ⟨coeff α (f : _root_.MvPowerSeries σ K), rfl⟩
  choose cq hcq using hqL_mem
  let q_ser : _root_.MvPowerSeries σ K := fun α ↦ cq α
  have hcoeff_q (α : σ →₀ ℕ) : coeff α q_ser = cq α := rfl
  have hq_rest : IsRestricted c q_ser := by
    refine qL.2.congr fun α ↦ ?_
    have h1 : algebraMap K L (coeff α q_ser) = coeff α (qL : _root_.MvPowerSeries σ L) :=
      hcq α
    rw [← h1, hnorm_alg]
  let q : T := ⟨q_ser, hq_rest⟩
  have hψq : ψ q = qL := Subtype.ext <| _root_.MvPowerSeries.ext fun α ↦ by
    rw [coeff_restrictedMap, hcoeff_q]
    exact hcq α
  have hgq : (g : T) * q = f := hψ_inj (by rw [map_mul, hψq, hmul_TL])
  have hgF_ne : algebraMap T F g ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hg_mem
  exact ⟨q, (eq_div_iff hgF_ne).mpr (by rw [mul_comm, ← map_mul, hgq])⟩

end IntegrallyClosed

section Empty

/-- Without variables, `K{X / c}` is isomorphic to the field `K` and is therefore Japanese, without
requiring completeness of `K` or positivity of `c`. -/
theorem isJapanese_isRestricted_subring_of_isEmpty {σ : Type*} {K : Type*} [NormedField K]
    [IsUltrametricDist K] [IsEmpty σ] {c : σ → ℝ} :
    Ring.IsJapanese (IsRestricted.subring (R := K) c) :=
  (IsRestricted.isEmptyEquiv (R := K) c).symm.toRingEquiv.isJapanese

end Empty

section Japanese

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- On any countably generated `K`-submodule `E` of `FrobeniusRoot K p e` over a complete
ultrametric normed field `K` (whether trivially or nontrivially normed), bounded `K`-linear
functionals separate points of `E`. -/
private theorem exists_bounded_dual_ne_zero_frobeniusRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {S : Set (FrobeniusRoot K p e)} (hS : S.Countable) (x : Submodule.span K S) (hx : x ≠ 0) :
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
      change ‖(y : FrobeniusRoot K p e)‖ = 1
      rw [FrobeniusRoot.norm_def, hK_eq_one hval_ne, Real.one_rpow]
    obtain ⟨φ, hφx⟩ := Module.Projective.exists_dual_ne_zero K hx
    refine ⟨φ, 1, fun y ↦ ?_, hφx⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · rw [hy_eq_one hy, mul_one]
      exact hnt (φ y)

/-- **Finiteness of normalization in purely inseparable extensions.** Over a complete ultrametric
normed field `K`, for finite `σ` and positive polyradius `c : σ → ℝ`, the integral closure of
`T = K{X / c}` in any finite purely inseparable extension `M` of `GaussFractionField σ K c` is a
finite `T`-module. -/
theorem finite_integralClosure_isRestricted_subring_of_isPurelyInseparable [Finite σ]
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
  have : IsIntegrallyClosed T := isIntegrallyClosed_isRestricted_subring
  -- Reduce from an abstract integral closure `C` to `integralClosure T M`.
  suffices Module.Finite T (integralClosure T M) from
    .equiv (IsIntegralClosure.equiv T (integralClosure T M) M C).toLinearEquiv
  obtain ⟨p, _⟩ := ExpChar.exists K
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let e := IsPurelyInseparable.exponent F M
  let q := p ^ e
  have hq_pos : 0 < q := pow_pos (expChar_pos K p) e
  have hq : q ≠ 0 := hq_pos.ne'
  -- Construct the Frobenius-root overring `T' = K'{X / r}` with `r i ^ q = c i`.
  let K' := FrobeniusRoot K p e
  let qR : ℝ := (q : ℝ)
  have hqR_ne : qR ≠ 0 := Nat.cast_ne_zero.mpr hq
  let r : σ → ℝ := fun i ↦ c i ^ qR⁻¹
  have hr_fact : ∀ i, Fact (0 < r i) := fun i ↦
    ⟨Real.rpow_pos_of_pos (Fact.out : 0 < c i) _⟩
  have hr : ∀ i, r i ^ q = c i := fun i ↦ by
    dsimp only [r, qR, q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < c i).le,
      inv_mul_cancel₀ hqR_ne, Real.rpow_one]
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  let Ψ : T →+* T' := frobeniusRootRestrictedHom p e hr
  have hΨ_inj : Function.Injective Ψ := frobeniusRootRestrictedHom_injective p e hr
  let Φ : F →+* F' := Ψ.gaussFractionFieldMap hΨ_inj
  let : Algebra F F' := Φ.toAlgebra
  have hF_alg (x : F) : algebraMap F F' x = Φ x := rfl
  -- Choose a denominator-cleared `F`-basis `b` of `M` with `b j ^ q ∈ T` and embed `M →ₐ[F] F'`.
  let m := Module.finrank F M
  obtain ⟨w, g, hg⟩ :=
    IsPurelyInseparable.exists_iterateFrobenius_unitsSMul_eq_algebraMap T F M p (le_refl e)
      (Module.finBasis F M)
  let b := (Module.finBasis F M).unitsSMul w
  let rootG (j : Fin m) : T' := frobeniusRootRestrictedEquiv p e (fun _ ↦ rfl) (g j)
  have hrootG_pow (j : Fin m) : rootG j ^ q = Ψ (g j) :=
    frobeniusRootRestrictedEquiv_pow (fun _ ↦ rfl) hr (g j)
  have hspan_b : IntermediateField.adjoin F (Set.range b) = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    rw [← b.sum_repr y]
    refine sum_mem fun j _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  have ⟨ι₀⟩ : Nonempty (M →ₐ[F] F') :=
    IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq F M p (le_refl e) F' hspan_b <| by
      rintro _ ⟨j, rfl⟩
      exact ⟨algebraMap T' F' (rootG j), by
        rw [← map_pow, hrootG_pow, ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj, ← hF_alg, ← hg]⟩
  have hι₀_alg (t : T) : ι₀ (algebraMap T M t) = algebraMap T' F' (Ψ t) := by
    rw [IsScalarTower.algebraMap_apply T F M, AlgHom.commutes, hF_alg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj t
  have hι₀_b (j : Fin m) : ι₀ (b j) = algebraMap T' F' (rootG j) := by
    refine iterateFrobenius_inj F' p e ?_
    simp only [iterateFrobenius_def]
    rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p (le_refl e) (b j),
      AlgHom.commutes, hF_alg, ← map_pow, hrootG_pow, hg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj (g j)
  -- Since `T` is integrally closed, every `y ∈ integralClosure T M` has `y ^ q = a_y ∈ T`;
  -- define `ζ y ∈ T'` as its formal `q`-th root so that `algebraMap T' F' (ζ y) = ι₀ y`.
  let aOf (y : integralClosure T M) : T :=
    (IsIntegral.exists_algebraMap_eq_iterateFrobenius (A := T) (K := F) p (le_refl e) y.2).choose
  have haOf (y : integralClosure T M) :
      algebraMap T F (aOf y) = IsPurelyInseparable.iterateFrobenius F M p (le_refl e) (y : M) :=
    (IsIntegral.exists_algebraMap_eq_iterateFrobenius (A := T) (K := F) p (le_refl e)
      y.2).choose_spec
  let ζ (y : integralClosure T M) : T' := frobeniusRootRestrictedEquiv p e (fun _ ↦ rfl) (aOf y)
  have hζ_alg (y : integralClosure T M) : algebraMap T' F' (ζ y) = ι₀ (y : M) := by
    refine iterateFrobenius_inj F' p e ?_
    simp only [iterateFrobenius_def]
    rw [← map_pow, frobeniusRootRestrictedEquiv_pow (fun _ ↦ rfl) hr (aOf y),
      ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj, ← hF_alg, haOf, ← AlgHom.commutes ι₀,
      IsPurelyInseparable.algebraMap_iterateFrobenius F p (le_refl e) (y : M), map_pow]
  have hζ_add (y₁ y₂ : integralClosure T M) : ζ (y₁ + y₂) = ζ y₁ + ζ y₂ :=
    IsFractionRing.injective T' F' <| by
      rw [map_add, hζ_alg (y₁ + y₂), hζ_alg y₁, hζ_alg y₂, AddMemClass.coe_add, map_add]
  have hζ_smul (t : T) (y : integralClosure T M) : ζ (t • y) = Ψ t * ζ y :=
    IsFractionRing.injective T' F' <| by
      rw [map_mul, hζ_alg (t • y), hζ_alg y, Subalgebra.coe_smul, Algebra.smul_def, map_mul,
        hι₀_alg]
  have hζ_ne {y : integralClosure T M} (hy : y ≠ 0) : ζ y ≠ 0 := fun h0 ↦
    hy <| ZeroMemClass.coe_eq_zero.mp <| (map_eq_zero_iff ι₀ ι₀.injective).mp <| by
      rw [← hζ_alg, h0, map_zero]
  -- Confine all coefficients of `ζ y` to the countably generated `K`-submodule `E ⊆ K'` spanned
  -- by the coefficients of `rootG 0, …, rootG (m - 1)`.
  let S : Set K' := Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
    coeff idx.2 (rootG idx.1 : _root_.MvPowerSeries σ K')
  let E : Submodule K K' := Submodule.span K S
  have hrootG_mem (j : Fin m) (α : σ →₀ ℕ) :
      coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E :=
    Submodule.subset_span ⟨(j, α), rfl⟩
  have h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖ :=
    fun a ↦ by rw [one_mul, FrobeniusRoot.norm_algebraMap]
  have hΨ_def (t : T) : Ψ t = restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso t) :=
    frobeniusRootRestrictedHom_apply p e hr t
  have hζ_mem (y : integralClosure T M) (α : σ →₀ ℕ) :
      coeff α (ζ y : _root_.MvPowerSeries σ K') ∈ E := by
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
      (Finset.univ.image (b.repr (y : M)))
    choose a ha using fun j : Fin m ↦ hs (b.repr (y : M) j) (Finset.mem_image_of_mem _ (by simp))
    have hs_ne : (s : T) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have hclear : Ψ s * ζ y = ∑ j, Ψ (a j) * rootG j := by
      apply IsFractionRing.injective T' F'
      rw [map_mul, hζ_alg, ← b.sum_repr (y : M), map_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have haj : algebraMap T F (a j) = algebraMap T F s * b.repr (y : M) j := by
        simpa only [Algebra.smul_def] using ha j
      rw [Algebra.smul_def, map_mul, AlgHom.commutes ι₀, hF_alg, ← mul_assoc,
        ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj (s : T), ← map_mul Φ, ← haj,
        Ψ.gaussFractionFieldMap_algebraMap hΨ_inj (a j), hι₀_b j]
      exact (map_mul (algebraMap T' F') (Ψ (a j)) (rootG j)).symm
    have hexp_ne : _root_.MvPowerSeries.expand q hq ((s : T) : _root_.MvPowerSeries σ K) ≠ 0 := by
      intro h0
      refine hΨ_inj.ne hs_ne ?_
      rw [Ψ.map_zero]
      exact Subtype.ext (by rw [coe_frobeniusRootRestrictedHom p e hr (s : T), h0, map_zero]; rfl)
    refine _root_.MvPowerSeries.coeff_mem_of_map_mul_coeff_mem E hexp_ne
      (g := (ζ y : _root_.MvPowerSeries σ K')) (fun β ↦ ?_) α
    have hβ : _root_.MvPowerSeries.map (algebraMap K K')
        (_root_.MvPowerSeries.expand q hq ((s : T) : _root_.MvPowerSeries σ K)) *
          (ζ y : _root_.MvPowerSeries σ K') =
        ((∑ j, Ψ (a j) * rootG j : T') : _root_.MvPowerSeries σ K') := by
      rw [← coe_frobeniusRootRestrictedHom p e hr (s : T), ← Subring.coe_mul, hclear]
    rw [hβ, AddSubmonoidClass.coe_finsetSum, map_sum]
    refine E.sum_mem fun j _ ↦ ?_
    rw [hΨ_def]
    exact coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E (a j) (hrootG_mem j) β
  -- Conclude `Module.Finite T (integralClosure T M)` via BGR §4.1 Prop. 4: bounded `K`-linear
  -- functionals on `E` yield `T`-linear functionals separating every nonzero `y₀` from `0`.
  have : IsNoetherianRing T := isNoetherianRing_isRestricted_subring
  refine (TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval T F M (integralClosure T M)).mpr
    (Module.Dual.injective_eval_iff.mpr fun y₀ hy₀ ↦ ?_)
  have hsep : ∀ x : E, x ≠ 0 → ∃ (φ : E →ₗ[K] K) (C : ℝ), (∀ z, ‖φ z‖ ≤ C * ‖z‖) ∧ φ x ≠ 0 :=
    exists_bounded_dual_ne_zero_frobeniusRoot p e (Set.countable_range _)
  obtain ⟨ν, hν, φ, B, hφ, hπ_ne⟩ :=
    exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero hq hr E hsep
      (hζ_ne hy₀) (hζ_mem y₀)
  let π := IsRestrictedFamily.toSubringDualOfBound (c := c) φ hφ
  let L_dual : Module.Dual T (integralClosure T M) :=
    { toFun y := π (restrictedExpandComponentFamily hq hr ν E (ζ y) (hζ_mem y))
      map_add' y₁ y₂ := by
        have hcongr : restrictedExpandComponentFamily hq hr ν E (ζ (y₁ + y₂))
            (hζ_mem (y₁ + y₂)) =
            restrictedExpandComponentFamily hq hr ν E (ζ y₁) (hζ_mem y₁) +
              restrictedExpandComponentFamily hq hr ν E (ζ y₂) (hζ_mem y₂) := by
          rw [← restrictedExpandComponentFamily_add hq hr ν E (ζ y₁) (ζ y₂)
            (hζ_mem y₁) (hζ_mem y₂)]
          exact IsRestrictedFamily.ext fun α ↦ Subtype.ext <| by
            rw [← IsRestrictedFamily.coeff_apply (R := K),
              ← IsRestrictedFamily.coeff_apply (R := K),
              coe_coeff_restrictedExpandComponentFamily,
              coe_coeff_restrictedExpandComponentFamily, hζ_add]
        rw [hcongr, map_add]
      map_smul' t y := by
        have hcongr : restrictedExpandComponentFamily hq hr ν E (ζ (t • y))
            (hζ_mem (t • y)) =
            t • restrictedExpandComponentFamily hq hr ν E (ζ y) (hζ_mem y) := by
          rw [← restrictedExpandComponentFamily_restrictedExpand_mul hq hr hν h_iso E t (ζ y)
            (hζ_mem y)]
          exact IsRestrictedFamily.ext fun α ↦ Subtype.ext <| by
            rw [← IsRestrictedFamily.coeff_apply (R := K),
              ← IsRestrictedFamily.coeff_apply (R := K),
              coe_coeff_restrictedExpandComponentFamily,
              coe_coeff_restrictedExpandComponentFamily, hζ_smul, hΨ_def]
        rw [RingHom.id_apply, hcongr, map_smul] }
  exact ⟨L_dual, hπ_ne⟩

/-- **Restricted power series and Tate algebras are Japanese.** Over any complete ultrametric normed
field `K` (of arbitrary characteristic and trivial or nontrivial valuation), the ring `K{X / c}` of
restricted power series in finitely many variables at any positive polyradius `c` is a Japanese
(N-2) domain. In particular, the Tate algebra `K⟨X₁, …, Xₙ⟩` (`c = 1`) is Japanese. -/
instance isJapanese_isRestricted_subring [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    Ring.IsJapanese (IsRestricted.subring (R := K) c) :=
  have : IsNoetherianRing (IsRestricted.subring (R := K) c) :=
    isNoetherianRing_isRestricted_subring
  Ring.IsJapanese.of_isPurelyInseparable (GaussFractionField σ K c) fun M _ _ _ _ _ _ ↦
    finite_integralClosure_isRestricted_subring_of_isPurelyInseparable M (integralClosure _ M)

/-- **Finiteness of normalization over restricted power series.** For any model `F` of the fraction
field of `K{X / c}` (`σ` finite, `c` positive, `K` complete ultrametric) and any finite field
extension `L / F` (separable or inseparable), every integral closure `C` of `K{X / c}` in `L` is a
finite `K{X / c}`-module. -/
theorem finite_integralClosure_isRestricted_subring [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]
    (F : Type*) (L : Type*) [Field F] [Field L]
    [Algebra (IsRestricted.subring (R := K) c) F]
    [IsFractionRing (IsRestricted.subring (R := K) c) F]
    [Algebra F L] [Algebra (IsRestricted.subring (R := K) c) L]
    [IsScalarTower (IsRestricted.subring (R := K) c) F L] [FiniteDimensional F L]
    (C : Type*) [CommRing C] [Algebra (IsRestricted.subring (R := K) c) C] [Algebra C L]
    [IsScalarTower (IsRestricted.subring (R := K) c) C L]
    [IsIntegralClosure C (IsRestricted.subring (R := K) c) L] :
    Module.Finite (IsRestricted.subring (R := K) c) C :=
  have := Ring.IsJapanese.finite_integralClosure (R := IsRestricted.subring (R := K) c) F L
  .equiv (IsIntegralClosure.equiv (IsRestricted.subring (R := K) c)
    (integralClosure (IsRestricted.subring (R := K) c) L) L C).toLinearEquiv

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
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  let xi : F := algebraMap T F ⟨_root_.MvPowerSeries.X i, isRestricted_X c i⟩
  let P : F[X] := Polynomial.X ^ p - Polynomial.C xi
  have hp_prime : p.Prime := Fact.out
  have hP_irr : Irreducible P := irreducible_X_pow_sub_C_of_prime hp_prime fun z ↦
    pow_ne_algebraMap_gaussFractionField_X σ K c i hp_prime.ne_one z
  have : Fact (Irreducible P) := ⟨hP_irr⟩
  have : FiniteDimensional F (AdjoinRoot P) := (AdjoinRoot.powerBasis hP_irr.ne_zero).finite
  have : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (algebraMap F (AdjoinRoot P)).injective p
  have hP_deg : P.natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow p
    · rw [natDegree_C, natDegree_X_pow]; exact hp_prime.pos
  have hfinrank : Module.finrank F (AdjoinRoot P) = p :=
    ((AdjoinRoot.powerBasis hP_irr.ne_zero).finrank.trans
      (AdjoinRoot.powerBasis_dim hP_irr.ne_zero)).trans hP_deg
  have hinsep : IsPurelyInseparable F (AdjoinRoot P) := by
    refine (isPurelyInseparable_iff_pow_mem F p).mpr fun y ↦ ?_
    induction y using AdjoinRoot.induction_on with | ih Q => ?_
    refine ⟨1, Q.eval₂ (frobenius F p) xi, ?_⟩
    rw [pow_one]
    change AdjoinRoot.of P (Q.eval₂ (frobenius F p) xi) = (AdjoinRoot.mk P Q) ^ p
    symm
    induction Q using Polynomial.induction_on' with
    | add Q₁ Q₂ ih₁ ih₂ =>
      rw [map_add, eval₂_add, map_add, add_pow_char, ih₁, ih₂]
    | monomial k a =>
      have hroot_p : (AdjoinRoot.root P) ^ p = AdjoinRoot.of P xi := by
        have h0 := AdjoinRoot.eval₂_root P
        rw [eval₂_sub, eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h0
        exact h0
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
        mul_pow, ← pow_mul, mul_comm k p, pow_mul, hroot_p, ← map_pow, ← map_pow, ← map_mul,
        eval₂_mul, Polynomial.eval₂_C, eval₂_X_pow, frobenius_def]
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hinsep, hfinrank,
    finite_integralClosure_isRestricted_subring F (AdjoinRoot P)
      (integralClosure T (AdjoinRoot P))⟩

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
  let Xi : T := ⟨_root_.MvPowerSeries.X i, isRestricted_X c i⟩
  let xi : F := algebraMap T F Xi
  let P : F[X] := Polynomial.X ^ 2 + Polynomial.C (xi ^ 2) * Polynomial.X + Polynomial.C xi
  have hdeg_tail : (Polynomial.C (xi ^ 2) * Polynomial.X + Polynomial.C xi).natDegree <
      (Polynomial.X ^ 2 : F[X]).natDegree := by
    rw [natDegree_X_pow]
    refine (natDegree_add_le _ _).trans_lt (max_lt ?_ (by rw [natDegree_C]; omega))
    exact natDegree_mul_le.trans_lt (by rw [natDegree_C, natDegree_X]; omega)
  have hP_deg : P.natDegree = 2 := by
    have heq : P = Polynomial.X ^ 2 + (Polynomial.C (xi ^ 2) * Polynomial.X + Polynomial.C xi) :=
      add_assoc _ _ _
    rw [heq, natDegree_add_eq_left_of_natDegree_lt hdeg_tail, natDegree_X_pow]
  have hP_monic : P.Monic := by
    have heq : P = Polynomial.X ^ 2 + (Polynomial.C (xi ^ 2) * Polynomial.X + Polynomial.C xi) :=
      add_assoc _ _ _
    rw [heq]
    exact (monic_X_pow 2).add_of_left (degree_lt_degree hdeg_tail)
  have hno_root (z : F) : P.eval z ≠ 0 := by
    intro hz
    simp only [P, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hz
    obtain ⟨A, B, hB_mem, rfl⟩ := IsFractionRing.div_surjective T z
    have hB_F_ne : algebraMap T F B ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hB_mem
    have hclear : algebraMap T F (A ^ 2 + Xi ^ 2 * A * B + Xi * B ^ 2) = 0 := by
      have hmul : (algebraMap T F A) ^ 2 + xi ^ 2 * (algebraMap T F A) * (algebraMap T F B) +
          xi * (algebraMap T F B) ^ 2 = 0 := by
        have h1 := congrArg (· * (algebraMap T F B) ^ 2) hz
        field_simp at h1
        linear_combination h1
      simpa only [xi, map_add, map_mul, map_pow] using hmul
    let As : _root_.MvPowerSeries σ K := A
    let Bs : _root_.MvPowerSeries σ K := B
    have hser : As ^ 2 + _root_.MvPowerSeries.X i ^ 2 * As * Bs +
        _root_.MvPowerSeries.X i * Bs ^ 2 = 0 := by
      have hval := congrArg Subtype.val
        (IsFractionRing.injective T F (hclear.trans (map_zero _).symm))
      simpa only [As, Bs, Xi, Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow,
        ZeroMemClass.coe_zero] using hval
    have hB_ne : Bs ≠ 0 := Subtype.coe_ne_coe.mpr (nonZeroDivisors.ne_zero hB_mem)
    have hA_ne : As ≠ 0 := fun hA0 ↦ by
      rw [hA0, zero_pow two_ne_zero, mul_zero, zero_mul, zero_add, zero_add] at hser
      exact mul_ne_zero (_root_.MvPowerSeries.X_ne_zero i) (pow_ne_zero 2 hB_ne) hser
    obtain ⟨a, ha⟩ :=
      ENat.ne_top_iff_exists.mp (_root_.MvPowerSeries.order_eq_top_iff.not.mpr hA_ne)
    obtain ⟨b, hb⟩ :=
      ENat.ne_top_iff_exists.mp (_root_.MvPowerSeries.order_eq_top_iff.not.mpr hB_ne)
    have hord_A2 : (As ^ 2).order = ↑(2 * a) := by
      rw [_root_.MvPowerSeries.order_pow, ← ha, nsmul_eq_mul]; norm_cast
    have hord_XB2 : (_root_.MvPowerSeries.X i * Bs ^ 2).order = ↑(1 + 2 * b) := by
      rw [_root_.MvPowerSeries.order_mul, _root_.MvPowerSeries.order_X,
        _root_.MvPowerSeries.order_pow, ← hb, nsmul_eq_mul]
      norm_cast
    have hord_mid : (_root_.MvPowerSeries.X i ^ 2 * As * Bs).order = ↑(2 + a + b) := by
      rw [_root_.MvPowerSeries.order_mul, _root_.MvPowerSeries.order_mul,
        _root_.MvPowerSeries.order_pow, _root_.MvPowerSeries.order_X, ← ha, ← hb, nsmul_eq_mul]
      norm_cast
    have hord_ne : (As ^ 2).order ≠ (_root_.MvPowerSeries.X i * Bs ^ 2).order := by
      rw [hord_A2, hord_XB2]
      exact_mod_cast (by omega : 2 * a ≠ 1 + 2 * b)
    have heq_sum : As ^ 2 + _root_.MvPowerSeries.X i * Bs ^ 2 =
        -(_root_.MvPowerSeries.X i ^ 2 * As * Bs) :=
      eq_neg_of_add_eq_zero_left (by linear_combination hser)
    have hord_sum := _root_.MvPowerSeries.order_add_of_order_ne hord_ne
    rw [heq_sum, _root_.MvPowerSeries.order_neg, hord_mid, hord_A2, hord_XB2] at hord_sum
    rcases le_total (2 * a) (1 + 2 * b) with hle | hle
    · rw [min_eq_left (by exact_mod_cast hle)] at hord_sum
      have hnat : 2 + a + b = 2 * a := by exact_mod_cast hord_sum
      omega
    · rw [min_eq_right (by exact_mod_cast hle)] at hord_sum
      have hnat : 2 + a + b = 1 + 2 * b := by exact_mod_cast hord_sum
      omega
  have hP_irr : Irreducible P := by
    refine (hP_monic.irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).mpr ?_
    · rw [hP_deg]
    · rw [hP_deg]; decide
    · exact Multiset.eq_zero_of_forall_notMem fun z hz ↦ hno_root z (isRoot_of_mem_roots hz)
  have : Fact (Irreducible P) := ⟨hP_irr⟩
  have : FiniteDimensional F (AdjoinRoot P) := (AdjoinRoot.powerBasis hP_irr.ne_zero).finite
  have hP_sep : P.Separable := by
    rw [separable_iff_derivative_ne_zero hP_irr]
    intro hderiv
    have hcoeff0 : P.derivative.coeff 0 = xi ^ 2 := by
      simp only [P, derivative_add, derivative_X_pow, derivative_mul, derivative_C, zero_mul,
        zero_add, derivative_X, mul_one, coeff_add, coeff_C_zero, add_zero]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (by decide : 0 ≠ 2 - 1),
        mul_zero, zero_add]
    rw [hderiv, Polynomial.coeff_zero] at hcoeff0
    have hxi_ne : xi ≠ 0 := by
      refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ?_)
      exact Subtype.coe_ne_coe.mp (_root_.MvPowerSeries.X_ne_zero i)
    exact pow_ne_zero 2 hxi_ne hcoeff0.symm
  have hmin : minpoly F (AdjoinRoot.powerBasis hP_irr.ne_zero).gen = P :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hP_monic hP_irr.ne_zero
  have hgen_sep : IsSeparable F (AdjoinRoot.powerBasis hP_irr.ne_zero).gen := by
    unfold IsSeparable
    exact hmin.symm ▸ hP_sep
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
    inferInstance, hfinrank,
    finite_integralClosure_isRestricted_subring F (AdjoinRoot P)
      (integralClosure T (AdjoinRoot P))⟩

end Examples

end TauCeti.MvPowerSeries
