/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.FrobeniusRoot
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
public import TauCeti.FieldTheory.PurelyInseparable.Exponent
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

import Mathlib.Algebra.CharP.Reduced
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.Normed.Module.Bases.CountableType
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.RingTheory.MvPowerSeries.LexOrder
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# Purely inseparable extensions of Tate fraction fields via Frobenius roots

Let `K` be an ultrametric normed field of exponential characteristic `p`, `σ` a variable type, and
`c : σ → ℝ` a positive polyradius. Given `e : ℕ`, let `q := p ^ e`, `K' := FrobeniusRoot K p e`,
and `r i = c i ^ q⁻¹` (`r i ^ q = c i`). This file constructs the shared infrastructure for
analyzing finite purely inseparable extensions `M` of `F := GaussFractionField σ K c` of exponent at
most `e`:

1. `TauCeti.MvPowerSeries.tateRoot`: applying `FrobeniusRoot.root K p e` coefficientwise maps a
   restricted series `f ∈ K{X / c}` to an explicit `q`-th root in `K'{X / r}` with respect to the
   isometric Frobenius-expansion embedding `Ψ : K{X / c} →+* K'{X / r}`.
2. `TauCeti.MvPowerSeries.exists_isometric_ringHom_of_isPurelyInseparable`: embeds `M` into
   `GaussFractionField σ K' r` compatibly with `Ψ`, isometrically for `spectralNorm F M`, and
   sending an `F`-basis `b` of `M` into `K'{X / r}`.
3. `TauCeti.MvPowerSeries.exists_bounded_dual_ne_zero_span_of_countable_frobeniusRoot`: when `K` is
   complete (whether nontrivially or trivially normed), bounded `K`-linear functionals separate
   points on the `K`-span of any countable subset of `FrobeniusRoot K p e`.
4. `TauCeti.MvPowerSeries.exists_restricted_projection_of_ne_zero`: given a `K`-subspace
   `E ⊆ K'` whose nonzero vectors are separated by bounded `K`-linear functionals and a nonzero
   series `u₀ ∈ K'{X / r}` whose coefficients lie in `E`, extracting a `q`-adic component and
   applying a bounded functional coefficientwise yields a Gauss-norm-bounded projection back to
   `K{X / c}` that is `K{X / c}`-linear along `Ψ` and nonzero at `u₀`.

These constructions feed both characteristic-free weak stability of `GaussFractionField`
([bosch-guntzer-remmert], §5.3.1, Theorem 1) and the Japanese property of integrally closed
restricted-series rings ([bosch-guntzer-remmert], §5.3.2, Theorem 1).

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.5.3, 5.3.1, and
  5.3.2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology IntermediateField

section Embedding

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Applying `FrobeniusRoot.root K p e` coefficientwise maps `K{X / c}` into
`(FrobeniusRoot K p e){X / r}` when `r i = c i ^ (p ^ e)⁻¹`. -/
noncomputable def tateRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    IsRestricted.subring (R := FrobeniusRoot K p e) r :=
  ⟨MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K), by
    let qR : ℝ := ((p ^ e : ℕ) : ℝ)
    have hq_inv : 0 < qR⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e))
    have hlim :=
      ((Real.continuousAt_rpow_const 0 qR⁻¹ (Or.inr hq_inv.le)).tendsto.comp f.2)
    rw [Real.zero_rpow hq_inv.ne'] at hlim
    refine hlim.congr fun μ ↦ ?_
    dsimp only [Function.comp_apply, qR]
    rw [Real.mul_rpow (norm_nonneg _) (prod_pow_pos μ).le, coeff_map, FrobeniusRoot.norm_root,
      μ.prod_pow_rpow (fun i _ ↦ (Fact.out : 0 < c i).le)]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ by simp only [hr]⟩

/-- The underlying formal power series of `tateRoot` is
`MvPowerSeries.map (FrobeniusRoot.root K p e)`. -/
@[simp]
theorem coe_tateRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    (tateRoot p e hr f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K) := (rfl)

/-- Raising `tateRoot p e hr f` to the `p ^ e`-th power equals the Frobenius-expanded image of `f`.
-/
theorem tateRoot_pow {p : ℕ} [ExpChar K p] {e : ℕ}
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    tateRoot p e hr f ^ p ^ e =
      restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow
        (restrictedMap (algebraMap K (FrobeniusRoot K p e)) (C := 1)
          (fun a ↦ (one_mul ‖a‖).symm ▸ (FrobeniusRoot.norm_algebraMap a).le) f) := by
  have hp : p ≠ 0 := (expChar_pos K p).ne'
  have hhom : (iterateFrobenius (FrobeniusRoot K p e) p e).comp (FrobeniusRoot.root K p e) =
      algebraMap K (FrobeniusRoot K p e) := RingHom.ext FrobeniusRoot.root_pow_expChar_pow
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_tateRoot, coe_restrictedExpand, coe_restrictedMap,
    ← MvPowerSeries.map_iterateFrobenius_expand p hp _ e, ← MvPowerSeries.map_expand,
    MvPowerSeries.map_map, hhom, MvPowerSeries.map_expand]

/-- Embeds a finite purely inseparable extension `M` of `GaussFractionField σ K c` of exponent at
most `e` in exponential characteristic `p` isometrically (for `spectralNorm`) into
`GaussFractionField σ (FrobeniusRoot K p e) r` with `r i = c i ^ (p ^ e)⁻¹`, sending an `F`-basis
of `M` into restricted series over `FrobeniusRoot K p e`. -/
theorem exists_isometric_ringHom_of_isPurelyInseparable
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p] [ExpChar (GaussFractionField σ K c) p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr_def : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) (hr : ∀ i, r i ^ p ^ e = c i)
    (h_iso : ∀ a : K, ‖algebraMap K (FrobeniusRoot K p e) a‖ ≤ 1 * ‖a‖) :
    let K' := FrobeniusRoot K p e
    let T := IsRestricted.subring (R := K) c
    let F := GaussFractionField σ K c
    let T' := IsRestricted.subring (R := K') r
    let F' := GaussFractionField σ K' r
    ∃ (Ψ : T →+* T') (m : ℕ) (b : Module.Basis (Fin m) F M) (rootG : Fin m → T') (ι : M →+* F'),
      (∀ f, Ψ f = restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr
        (restrictedMap (algebraMap K K') h_iso f)) ∧
      (∀ f, ‖Ψ f‖ = ‖f‖) ∧
      (∀ f, ι (algebraMap F M (algebraMap T F f)) = algebraMap T' F' (Ψ f)) ∧
      (∀ y : M, ‖ι y‖ = spectralNorm F M y) ∧
      (∀ j : Fin m, ι (b j) = algebraMap T' F' (rootG j)) := by
  classical
  intro K' T F T' F'
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have hq : p ^ e ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  -- Step 1: Extend the isometric Tate-algebra map `Ψ : T →+* T'` across fractions to `F →+* F'`.
  let Ψ : T →+* T' :=
    (restrictedExpand (p ^ e) hq hr).toRingHom.comp (restrictedMap (algebraMap K K') h_iso)
  have hΨ_norm (f : T) : ‖Ψ f‖ = ‖f‖ := by
    dsimp only [Ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [norm_restrictedExpand, norm_restrictedMap _ _ FrobeniusRoot.norm_algebraMap]
  have hΨ_inj : Function.Injective Ψ :=
    ((AddMonoidHomClass.isometry_iff_norm Ψ).mpr hΨ_norm).injective
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg : algebraMap F F' = Ψ.gaussFractionFieldMap hΨ_inj := RingHom.algebraMap_toAlgebra _
  -- Step 2: Pick an `F`-basis `b` of `M` with `b j ^ p ^ e ∈ T` and `p ^ e`-th roots in `T'`.
  let m := Module.finrank F M
  obtain ⟨w, g, hg⟩ :=
    IsPurelyInseparable.exists_iterateFrobenius_unitsSMul_eq_algebraMap T F M p he
      (Module.finBasis F M)
  let b := (Module.finBasis F M).unitsSMul w
  let rootG (j : Fin m) : T' := tateRoot p e hr_def (g j)
  have hrootG_pow (j : Fin m) : rootG j ^ p ^ e = Ψ (g j) := tateRoot_pow hr_def hr (g j)
  -- Step 3: Embed `M` `F`-linearly into `F'` by sending `b` to the `p ^ e`-th roots `rootG`.
  have hspan_b : IntermediateField.adjoin F (Set.range b) = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    rw [← b.sum_repr y]
    refine sum_mem fun j _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  have ⟨ι₀⟩ : Nonempty (M →ₐ[F] F') :=
    IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq F M p he F' hspan_b <| by
      rintro _ ⟨j, rfl⟩
      exact ⟨algebraMap T' F' (rootG j), by
        rw [← map_pow, hrootG_pow, ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj, ← hF_alg, ← hg]⟩
  -- Step 4: Verify scalar compatibility, spectral-norm isometry, and images of the basis `b`.
  refine ⟨Ψ, m, b, rootG, ι₀.toRingHom, fun _ ↦ rfl, hΨ_norm, fun f ↦ ?_, fun y ↦ ?_, fun j ↦ ?_⟩
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, hF_alg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj f
  · obtain ⟨k, a, ha⟩ := IsPurelyInseparable.pow_mem F p y
    have hpk : p ^ k ≠ 0 := (pow_pos (expChar_pos K p) k).ne'
    refine (pow_left_inj₀ (norm_nonneg _) (spectralNorm_nonneg _) hpk).mp ?_
    have hι_pow : (ι₀ y) ^ p ^ k = Ψ.gaussFractionFieldMap hΨ_inj a := by
      rw [← map_pow, ← ha, AlgHom.commutes, hF_alg]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← norm_pow, hι_pow,
      Ψ.norm_gaussFractionFieldMap hΨ_inj hΨ_norm,
      TauCeti.spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hpk ha.symm]
  · refine iterateFrobenius_inj F' p e ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, iterateFrobenius_def]
    rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p he (b j),
      AlgHom.commutes, hF_alg, ← map_pow, hrootG_pow, hg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj (g j)

/-- Clearing denominators of `b.repr y` by `s` expresses `Ψ s * ι y` in `GaussFractionField σ K' r`
as the image of `∑ j, Ψ (a j) * rootG j`. -/
theorem algebraMap_sum_mul_eq_mul
    {K' : Type*} [NormedField K'] [IsUltrametricDist K']
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {M : Type*} [Field M] [Algebra (GaussFractionField σ K c) M]
    {m : ℕ} (b : Module.Basis (Fin m) (GaussFractionField σ K c) M)
    (Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r)
    (rootG : Fin m → IsRestricted.subring (R := K') r) (ι : M →+* GaussFractionField σ K' r)
    (hι_alg : ∀ f, ι (algebraMap _ M (algebraMap _ (GaussFractionField σ K c) f)) =
      algebraMap _ (GaussFractionField σ K' r) (Ψ f))
    (hι_b : ∀ j, ι (b j) = algebraMap _ (GaussFractionField σ K' r) (rootG j))
    (y : M) (s : IsRestricted.subring (R := K) c)
    (a : Fin m → IsRestricted.subring (R := K) c)
    (ha : ∀ j, algebraMap _ (GaussFractionField σ K c) (a j) = s • b.repr y j) :
    algebraMap _ (GaussFractionField σ K' r) (∑ j, Ψ (a j) * rootG j) =
      algebraMap _ (GaussFractionField σ K' r) (Ψ s) * ι y := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  rw [map_sum, ← b.sum_repr y, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have haj : algebraMap T F (a j) = algebraMap T F s * b.repr y j := by
    simpa only [Algebra.smul_def] using ha j
  rw [map_mul, ← hι_alg (a j), haj, map_mul, map_mul, hι_alg s, ← hι_b j, mul_assoc,
    ← map_mul ι, ← Algebra.smul_def (b.repr y j) (b j)]

/-- Evaluating a linear form `b.constr F (algebraMap T F ∘ g)` after clearing denominators of
`b.repr y` by `s` yields `algebraMap T F (∑ j, a j * g j)`. -/
theorem algebraMap_mul_constr_eq_algebraMap_sum
    {T F M ι : Type*} [CommSemiring T] [Field F] [Algebra T F] [AddCommGroup M] [Module F M]
    [Fintype ι] (b : Module.Basis ι F M) (g : ι → T)
    (y : M) (s : T) (a : ι → T)
    (ha : ∀ j, algebraMap T F (a j) = s • b.repr y j) :
    algebraMap T F s * b.constr F (fun j ↦ algebraMap T F (g j)) y =
      algebraMap T F (∑ j, a j * g j) := by
  classical
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, b.constr_basis, smul_eq_mul, ← mul_assoc,
    ← Algebra.smul_def s (b.repr y j), ← ha j, ← map_mul]

end Embedding

section Projection

/-- Over a complete ultrametric normed field `K` (nontrivially or trivially normed), bounded
`K`-linear functionals separate points on the `K`-span of any countable subset of
`FrobeniusRoot K p e`. -/
theorem exists_bounded_dual_ne_zero_span_of_countable_frobeniusRoot {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [ExpChar K p] (e : ℕ)
    {S : Set (FrobeniusRoot K p e)} (hS : S.Countable)
    {x : Submodule.span K S} (hx : x ≠ 0) :
    ∃ (f : Submodule.span K S →ₗ[K] K) (C : ℝ),
      0 ≤ C ∧ (∀ v, ‖f v‖ ≤ C * ‖v‖) ∧ f x ≠ 0 := by
  by_cases hnt : ∃ a : K, 1 < ‖a‖
  · let _ : NontriviallyNormedField K :=
      { __ := (inferInstance : NormedField K), non_trivial := hnt }
    have : SeparatingDual K (Submodule.span K S) := Submodule.separatingDual_span_of_countable hS
    obtain ⟨f, hfx⟩ := SeparatingDual.exists_ne_zero (R := K) hx
    exact ⟨f.toLinearMap, ‖f‖, norm_nonneg f, f.le_opNorm, hfx⟩
  · push Not at hnt
    have ha_norm {a : K} (ha : a ≠ 0) : ‖a‖ = 1 := by
      refine le_antisymm (hnt a) ?_
      have h1 : (1 : ℝ) = ‖a‖ * ‖a⁻¹‖ := by rw [← norm_mul, mul_inv_cancel₀ ha, norm_one]
      nlinarith [hnt a⁻¹, norm_nonneg a]
    have hv_norm {v : Submodule.span K S} (hv : v ≠ 0) : ‖v‖ = 1 := by
      have hval : FrobeniusRoot.val K p e v.1 ≠ 0 :=
        (map_ne_zero_iff _ FrobeniusRoot.val_injective).mpr (Subtype.coe_ne_coe.mpr hv)
      rw [← Submodule.norm_coe, FrobeniusRoot.norm_def, ha_norm hval, Real.one_rpow]
    obtain ⟨f, hfx⟩ := Module.Projective.exists_dual_ne_zero K hx
    refine ⟨f, 1, zero_le_one, fun v ↦ ?_, hfx⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [hv_norm hv, mul_one]
      exact hnt (f v)

variable {σ K K' : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K']

/-- Multiplying a restricted series `u ∈ K'{X / r}` whose coefficients lie in `E : Submodule K K'`
on the left by a Frobenius-expanded series `Ψ d` preserves coefficient membership in `E`. -/
theorem coeff_restrictedExpand_restrictedMap_mul_mem
    {c r : σ → ℝ} {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖)
    {Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r}
    (hΨ_def : ∀ f, Ψ f = restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso f))
    (d : IsRestricted.subring (R := K) c) {u : IsRestricted.subring (R := K') r}
    {E : Submodule K K'} (hu : ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E) (β : σ →₀ ℕ) :
    coeff β ((Ψ d * u : IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E := by
  rw [Subring.coe_mul, hΨ_def, coe_restrictedExpand, coe_restrictedMap,
    ← MvPowerSeries.map_expand]
  exact MvPowerSeries.coeff_map_mul_mem _ hu β

/-- Given `E : Submodule K K'` whose nonzero vectors are separated by bounded `K`-linear functionals
and a nonzero `u₀ ∈ K'{X / r}` with coefficients in `E`, extracting a `q`-adic component and
applying a bounded functional coefficientwise yields a Gauss-norm-bounded projection to `K{X / c}`
that is additive, `K{X / c}`-linear along `Ψ`, and nonzero at `u₀`. -/
theorem exists_restricted_projection_of_ne_zero
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖)
    {Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r}
    (hΨ_def : ∀ f, Ψ f = restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso f))
    {E : Submodule K K'}
    (hsep : ∀ {x : E}, x ≠ 0 → ∃ (f : E →ₗ[K] K) (C : ℝ),
      0 ≤ C ∧ (∀ v : E, ‖f v‖ ≤ C * ‖v‖) ∧ f x ≠ 0)
    {u₀ : IsRestricted.subring (R := K') r}
    (hu₀_mem : ∀ α, coeff α (u₀ : _root_.MvPowerSeries σ K') ∈ E) (hu₀_ne : u₀ ≠ 0) :
    let T := IsRestricted.subring (R := K) c
    let T' := IsRestricted.subring (R := K') r
    ∃ (π : (u : T') → (∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E) → T) (C_π : ℝ),
      (∀ {ι : Type*} (s : Finset ι) (u : ι → T')
        (hu : ∀ i, ∀ α, coeff α (u i : _root_.MvPowerSeries σ K') ∈ E)
        (hsum : ∀ α, coeff α ((∑ i ∈ s, u i : T') : _root_.MvPowerSeries σ K') ∈ E),
        π (∑ i ∈ s, u i) hsum = ∑ i ∈ s, π (u i) (hu i)) ∧
      (∀ (d : T) (u : T') (hu : ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E)
        (hdu : ∀ α, coeff α ((Ψ d * u : T') : _root_.MvPowerSeries σ K') ∈ E),
        π (Ψ d * u) hdu = d * π u hu) ∧
      (∀ (u : T') (hu : ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E),
        ‖π u hu‖ ≤ C_π * ‖u‖) ∧
      π u₀ hu₀_mem ≠ 0 := by
  classical
  intro T T'
  obtain ⟨ν, hν, hν_norm⟩ := exists_norm_restrictedExpandComponent_mul_prod_eq hq hr u₀
  have hcomp_ne : restrictedExpandComponent hq hr ν u₀ ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero, zero_mul] at hν_norm
    exact hu₀_ne (norm_eq_zero.mp hν_norm.symm)
  obtain ⟨μ, hμ_ne⟩ :
      ∃ μ, coeff μ (restrictedExpandComponent hq hr ν u₀ : _root_.MvPowerSeries σ K') ≠ 0 := by
    by_contra! hall
    exact hcomp_ne (Subtype.ext (MvPowerSeries.ext fun μ ↦ by
      rw [ZeroMemClass.coe_zero, map_zero]; exact hall μ))
  let wE (u : T') (hu : ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E) :
      IsRestrictedFamily.addSubgroup E c :=
    ⟨fun α ↦ ⟨coeff α (restrictedExpandComponent hq hr ν u : _root_.MvPowerSeries σ K'), by
        rw [coeff_restrictedExpandComponent]; exact hu (q • α + ν)⟩,
      IsRestrictedFamily.mem_addSubgroup.mpr <|
        ((isRestrictedFamily_coeff_iff _).mpr
          (restrictedExpandComponent hq hr ν u).2).of_norm_le (C := 1) fun _ ↦
            (one_mul _).symm.le⟩
  have hcoe_wE (u : T') (hu : ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E) (α : σ →₀ ℕ) :
      ((IsRestrictedFamily.coeff K α (wE u hu) : E) : K') =
        coeff α (restrictedExpandComponent hq hr ν u : _root_.MvPowerSeries σ K') := by
    rw [IsRestrictedFamily.coeff_apply]
  have hwE₀_ne : IsRestrictedFamily.coeff K μ (wE u₀ hu₀_mem) ≠ 0 :=
    Subtype.coe_ne_coe.mp (by rw [ZeroMemClass.coe_zero, hcoe_wE u₀ hu₀_mem]; exact hμ_ne)
  obtain ⟨f_dual, C_f, hCf_nonneg, hf_bound, hf_ne⟩ := hsep hwE₀_ne
  let π₀ : IsRestrictedFamily.addSubgroup E c →ₗ[K] T :=
    (IsRestrictedFamily.subringLinearEquiv.symm.toLinearMap.restrictScalars K).comp
      (IsRestrictedFamily.mapLinearMap f_dual hf_bound)
  have hπ₀_coeff (v : IsRestrictedFamily.addSubgroup E c) (α : σ →₀ ℕ) :
      coeff α (π₀ v : _root_.MvPowerSeries σ K) = f_dual (IsRestrictedFamily.coeff K α v) := by
    simp only [π₀, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap, IsRestrictedFamily.coeff_coe_subringLinearEquiv_symm_apply,
      IsRestrictedFamily.coe_mapLinearMap, Function.comp_apply, IsRestrictedFamily.coeff_apply]
  have hπ₀_smul (d : T) (v : IsRestrictedFamily.addSubgroup E c) : π₀ (d • v) = d * π₀ v := by
    dsimp only [π₀, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap]
    rw [IsRestrictedFamily.mapLinearMap_isRestrictedSubring_smul,
      IsRestrictedFamily.subringLinearEquiv.symm.map_smul, smul_eq_mul]
  refine ⟨fun u hu ↦ π₀ (wE u hu), C_f / ν.prod (r · ^ ·),
    fun s u hu hsum ↦ ?_, fun d u hu hdu ↦ ?_, fun u hu ↦ ?_, fun h0 ↦ ?_⟩
  · dsimp only
    have hwE_sum : wE (∑ i ∈ s, u i) hsum = ∑ i ∈ s, wE (u i) (hu i) := by
      apply Subtype.ext
      funext α
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Submodule.coe_sum]
      dsimp only [wE]
      rw [restrictedExpandComponent_sum, AddSubmonoidClass.coe_finsetSum, map_sum]
    rw [hwE_sum, map_sum]
  · dsimp only
    have hwE_mul : wE (Ψ d * u) hdu = d • wE u hu := by
      apply Subtype.ext
      funext α
      apply Subtype.ext
      dsimp only [wE]
      rw [hΨ_def, restrictedExpandComponent_restrictedExpand_mul hq hr hν _ u,
        IsRestrictedFamily.coe_isRestrictedSubring_smul,
        convSMul_apply, Submodule.coe_sum, Subring.coe_mul, coeff_mul]
      refine Finset.sum_congr rfl fun pq _ ↦ ?_
      rw [SetLike.val_smul, Algebra.smul_def, coeff_restrictedMap,
        ← IsRestrictedFamily.coeff_apply (R := K), hcoe_wE u hu]
    rw [hwE_mul, hπ₀_smul]
  · calc ‖π₀ (wE u hu)‖
        ≤ C_f * ‖restrictedExpandComponent hq hr ν u‖ := by
          refine norm_le_mul_of_norm_coeff_le fun α ↦ ?_
          rw [hπ₀_coeff, ← hcoe_wE u hu α, Submodule.norm_coe]
          exact hf_bound _
      _ ≤ C_f * (‖u‖ / ν.prod (r · ^ ·)) :=
          mul_le_mul_of_nonneg_left ((le_div_iff₀ (prod_pow_pos ν)).mpr
            (norm_restrictedExpandComponent_mul_prod_le hq hr ν _)) hCf_nonneg
      _ = (C_f / ν.prod (r · ^ ·)) * ‖u‖ := by ring
  · dsimp only at h0
    have hcoeff0 : coeff μ (π₀ (wE u₀ hu₀_mem) : _root_.MvPowerSeries σ K) = 0 := by
      rw [h0, ZeroMemClass.coe_zero, map_zero]
    rw [hπ₀_coeff] at hcoeff0
    exact hf_ne hcoeff0

end Projection

end TauCeti.MvPowerSeries
