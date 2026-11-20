/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.FrobeniusRoot
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
public import TauCeti.FieldTheory.PurelyInseparable.Exponent
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FrobeniusRoot

import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.Localization.Integer
import TauCeti.Analysis.Normed.Module.Bases.CountableType
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.RingTheory.MvPowerSeries.Convolution
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Expand

/-!
# Purely inseparable extensions of Tate fraction fields via Frobenius roots

Let `K` be an ultrametric normed field of exponential characteristic `p`, `σ` a variable type, and
`c : σ → ℝ` a positive polyradius. Given `e : ℕ`, let `q := p ^ e`, `K' := FrobeniusRoot K p e`,
and `r : σ → ℝ` a positive polyradius satisfying `r i ^ q = c i`. Building on the Frobenius-root
embedding in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FrobeniusRoot` and the `q`-adic
component-dual projections in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Expand`, this
file proves:

1. `TauCeti.MvPowerSeries.exists_ringHom_norm_eq_spectralNorm_of_isPurelyInseparable`: embeds a
   finite purely inseparable extension `M` of `F := GaussFractionField σ K c` of exponent at most
   `e` into `GaussFractionField σ K' r` compatibly with `frobeniusRootRestrictedHom`, satisfying
   `‖ι y‖ = spectralNorm F M y` and sending an `F`-basis of `M` into `K'{X / r}`.
2. `TauCeti.MvPowerSeries.exists_dual_norm_le_spectralNorm_of_isPurelyInseparable`: when `K` is
   complete (trivially or nontrivially normed) and `σ` is countable, every nonzero `x₀ : M` is
   separated from `0` by an `F`-linear functional `φ : Module.Dual F M` that is bounded by
   `spectralNorm F M` and sends every element of `M` whose `p ^ e`-th power lies in `K{X / c}` into
   `Set.range (algebraMap T F)`.

These results feed characteristic-free weak stability of `GaussFractionField`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §5.3.1, Theorem 1) for both trivially and
nontrivially normed complete fields `K`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §§3.5.3, 5.3.1, and 5.3.2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section SpectralEmbedding

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Embeds a finite purely inseparable extension `M` of `GaussFractionField σ K c` of exponent at
most `e` in exponential characteristic `p` into `GaussFractionField σ (FrobeniusRoot K p e) r`
(for positive `r` with `r i ^ p ^ e = c i`) compatibly with `frobeniusRootRestrictedHom`, with
`‖ι y‖ = spectralNorm F M y` and sending an `F`-basis of `M` into restricted series over
`FrobeniusRoot K p e`. -/
theorem exists_ringHom_norm_eq_spectralNorm_of_isPurelyInseparable
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr : ∀ i, r i ^ p ^ e = c i) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) (GaussFractionField σ K c) M)
      (rootG : Fin m → IsRestricted.subring (R := FrobeniusRoot K p e) r)
      (ι : M →+* GaussFractionField σ (FrobeniusRoot K p e) r),
      (∀ f, ι (algebraMap (GaussFractionField σ K c) M
          (algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) f)) =
        algebraMap (IsRestricted.subring (R := FrobeniusRoot K p e) r)
          (GaussFractionField σ (FrobeniusRoot K p e) r)
          (frobeniusRootRestrictedHom p e hr f)) ∧
      (∀ y : M, ‖ι y‖ = spectralNorm (GaussFractionField σ K c) M y) ∧
      (∀ j : Fin m, ι (b j) =
        algebraMap (IsRestricted.subring (R := FrobeniusRoot K p e) r)
          (GaussFractionField σ (FrobeniusRoot K p e) r) (rootG j)) := by
  classical
  let K' := FrobeniusRoot K p e
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let F' := GaussFractionField σ K' r
  let Ψ := frobeniusRootRestrictedHom (K := K) p e hr
  have hΨ_norm : ∀ f : T, ‖Ψ f‖ = ‖f‖ := norm_frobeniusRootRestrictedHom p e hr
  have hΨ_inj : Function.Injective Ψ := frobeniusRootRestrictedHom_injective p e hr
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg : algebraMap F F' = Ψ.gaussFractionFieldMap hΨ_inj := RingHom.algebraMap_toAlgebra _
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  obtain ⟨m, b, rootG, ι₀, hι_alg, hι_b⟩ :=
    exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable M p e he hr
  refine ⟨m, b, rootG, ι₀.toRingHom, hι_alg, fun y ↦ ?_, hι_b⟩
  obtain ⟨k, a, ha⟩ := IsPurelyInseparable.pow_mem F p y
  have hpk : p ^ k ≠ 0 := (pow_pos (expChar_pos K p) k).ne'
  refine (pow_left_inj₀ (norm_nonneg _) (spectralNorm_nonneg _) hpk).mp ?_
  have hι_pow : (ι₀ y) ^ p ^ k = Ψ.gaussFractionFieldMap hΨ_inj a := by
    rw [← map_pow, ← ha, AlgHom.commutes, hF_alg]
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← norm_pow, hι_pow,
    Ψ.norm_gaussFractionFieldMap hΨ_inj hΨ_norm,
    TauCeti.spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hpk ha.symm]

end SpectralEmbedding

section SeparatingDual

/-- For any finite purely inseparable extension `M` of `F := GaussFractionField σ K c` over a
complete ultrametric field `K` (trivially or nontrivially normed) and countable variable type `σ`,
every nonzero `x₀ : M` is separated from `0` by an `F`-linear functional `φ : Module.Dual F M`
that is bounded by `spectralNorm F M` and maps every element of `M` whose
`ringExpChar K ^ IsPurelyInseparable.exponent F M`-th power lies in `T := IsRestricted.subring c`
into `Set.range (algebraMap T F)`. -/
theorem exists_dual_norm_le_spectralNorm_of_isPurelyInseparable
    {σ K : Type*} [Countable σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {c : σ → ℝ} [∀ i, Fact (0 < c i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    {x₀ : M} (hx₀ : x₀ ≠ 0) :
    ∃ (φ : Module.Dual (GaussFractionField σ K c) M) (C : ℝ),
      0 ≤ C ∧
      (∀ y : M, ‖φ y‖ ≤ C * spectralNorm (GaussFractionField σ K c) M y) ∧
      (∀ y : M,
        y ^ (ringExpChar K ^ IsPurelyInseparable.exponent (GaussFractionField σ K c) M) ∈
          Set.range (algebraMap (GaussFractionField σ K c) M ∘
            algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c)) →
        φ y ∈ Set.range
          (algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c))) ∧
      φ x₀ ≠ 0 := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let p := ringExpChar K
  let e := IsPurelyInseparable.exponent F M
  set q := p ^ e
  have hq : q ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  let K' := FrobeniusRoot K p e
  let r : σ → ℝ := fun i ↦ c i ^ ((q : ℝ)⁻¹)
  have hr_fact : ∀ i, Fact (0 < r i) := fun i ↦ ⟨Real.rpow_pos_of_pos (Fact.out : 0 < c i) _⟩
  have hr (i : σ) : r i ^ q = c i := Real.rpow_inv_natCast_pow (Fact.out : 0 < c i).le hq
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  let Ψ := frobeniusRootRestrictedHom (K := K) p e hr
  have h_iso (a : K) : ‖algebraMap K K' a‖ ≤ 1 * ‖a‖ := by
    rw [one_mul, FrobeniusRoot.norm_algebraMap]
  have hΨ_def (t : T) : Ψ t = restrictedExpand q hq hr
      (restrictedMap (algebraMap K K') h_iso t) :=
    frobeniusRootRestrictedHom_apply p e hr t
  have hΨ_inj : Function.Injective Ψ := frobeniusRootRestrictedHom_injective p e hr
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  obtain ⟨m, b, rootG, ι, hι_alg, hι_norm, hι_b⟩ :=
    exists_ringHom_norm_eq_spectralNorm_of_isPurelyInseparable M p e le_rfl hr
  -- Span a countably generated `K`-subspace `E ⊆ K'` from all coefficients of `rootG`.
  let E : Submodule K K' := Submodule.span K (Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
    coeff idx.snd (rootG idx.fst : _root_.MvPowerSeries σ K'))
  have hrootG_mem (j : Fin m) (α : σ →₀ ℕ) :
      coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E :=
    Submodule.subset_span ⟨(j, α), rfl⟩
  have hterm_mem (a : Fin m → T) (j : Fin m) (α : σ →₀ ℕ) :
      coeff α ((Ψ (a j) * rootG j : T') : _root_.MvPowerSeries σ K') ∈ E := by
    rw [hΨ_def]
    exact coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E (a j) (hrootG_mem j) α
  have hsum_mem (a : Fin m → T) (α : σ →₀ ℕ) :
      coeff α ((∑ j, Ψ (a j) * rootG j : T') : _root_.MvPowerSeries σ K') ∈ E := by
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    exact E.sum_mem fun j _ ↦ hterm_mem a j α
  have hι_clear (z : M) (s : nonZeroDivisors T) (a : Fin m → T)
      (ha : ∀ j, algebraMap T F (a j) = (s : T) • b.repr z j) :
      algebraMap T' F' (∑ j, Ψ (a j) * rootG j) = algebraMap T' F' (Ψ (s : T)) * ι z :=
    b.map_sum_mul_eq_map_mul_apply (algebraMap T' F') ι (x := z) (r := algebraMap T F (s : T))
      (hι_alg (s : T))
      (fun j ↦ by rw [← Algebra.smul_def (s : T) (b.repr z j), ← ha j, hι_alg]) hι_b
  -- Clear denominators of `b.repr x₀` and separate `∑ j, Ψ (a₀ j) * rootG j` via `π`.
  obtain ⟨s₀, hs₀⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T) (b.repr x₀)
  choose a₀ ha₀ using hs₀
  have hu₀_ne : ∑ j, Ψ (a₀ j) * rootG j ≠ 0 := fun h0 ↦ by
    have hs₀_ne : algebraMap T' F' (Ψ (s₀ : T)) ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_algebraMap_gaussFractionField, norm_frobeniusRootRestrictedHom,
        norm_ne_zero_iff]
      exact nonZeroDivisors.ne_zero s₀.property
    have hmul : algebraMap T' F' (Ψ (s₀ : T)) * ι x₀ = 0 := by
      rw [← hι_clear x₀ s₀ a₀ ha₀, h0, map_zero]
    exact mul_ne_zero hs₀_ne ((map_ne_zero_iff ι ι.injective).mpr hx₀) hmul
  obtain ⟨ν, hν, φ_E, C_φ, hφ_E, hπ_ne⟩ :=
    exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero hq hr E
      (fun _ hx ↦ Submodule.exists_bounded_dual_ne_zero_span_of_countable
        (Set.countable_range _) hx)
      hu₀_ne (hsum_mem a₀)
  let C_φ' : ℝ := max C_φ 0
  have hC_φ' : 0 ≤ C_φ' := le_max_right _ _
  let π := IsRestrictedFamily.toSubringDualOfBound (c := c) φ_E hφ_E
  let wE (j : Fin m) := restrictedExpandComponentFamily hq hr ν E (rootG j) (hrootG_mem j)
  have hcomp_sum (a : Fin m → T) :
      restrictedExpandComponentFamily hq hr ν E (∑ j, Ψ (a j) * rootG j) (hsum_mem a) =
        ∑ j, a j • wE j := by
    rw [restrictedExpandComponentFamily_sum hq hr ν E Finset.univ _ (hterm_mem a)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← restrictedExpandComponentFamily_restrictedExpand_mul hq hr hν h_iso E (a j) (rootG j)
        (hrootG_mem j) (hz_mul := coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E
          (a j) (hrootG_mem j))]
    exact restrictedExpandComponentFamily_congr hq hr ν E
      (congrArg (· * rootG j) (hΨ_def (a j)))
  let g (j : Fin m) : T := π (wE j)
  have hπ_sum (a : Fin m → T) :
      ∑ j, a j * g j =
        π (restrictedExpandComponentFamily hq hr ν E (∑ j, Ψ (a j) * rootG j) (hsum_mem a)) := by
    rw [hcomp_sum a, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
  let φ : Module.Dual F M := b.constr F fun j ↦ algebraMap T F (g j)
  refine ⟨φ, C_φ' / ν.prod (r · ^ ·), div_nonneg hC_φ' (prod_pow_pos ν).le,
    fun y ↦ ?_, fun y ⟨fy, hfy⟩ ↦ ?_, fun hφ0 ↦ ?_⟩
  · -- Spectral-norm bound for `φ`.
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T)
      (b.repr y)
    choose a ha using hs
    have hu_norm : ‖∑ j, Ψ (a j) * rootG j‖ = ‖(s : T)‖ * spectralNorm F M y := by
      rw [← norm_algebraMap_gaussFractionField σ K' r _, hι_clear y s a ha, norm_mul,
        norm_algebraMap_gaussFractionField σ K' r _, norm_frobeniusRootRestrictedHom, hι_norm]
    have hs_pos : 0 < ‖(s : T)‖ := by
      rw [← norm_algebraMap_gaussFractionField σ K c (s : T), norm_pos_iff]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property
    refine le_of_mul_le_mul_left ?_ hs_pos
    calc ‖(s : T)‖ * ‖φ y‖
        = ‖algebraMap T F (s : T) * φ y‖ := by
          rw [norm_mul, norm_algebraMap_gaussFractionField σ K c _]
      _ = ‖∑ j, a j * g j‖ := by
          rw [b.algebraMap_mul_constr_eq_algebraMap_sum g y (s : T) a ha,
            norm_algebraMap_gaussFractionField σ K c _]
      _ ≤ (C_φ / ν.prod (r · ^ ·)) * ‖∑ j, Ψ (a j) * rootG j‖ := by
          rw [hπ_sum a]
          exact norm_toSubringDualOfBound_restrictedExpandComponentFamily_le hq hr ν E φ_E hφ_E _ _
      _ ≤ (C_φ' / ν.prod (r · ^ ·)) * ‖∑ j, Ψ (a j) * rootG j‖ :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (le_max_left C_φ 0) (prod_pow_pos ν).le)
            (norm_nonneg _)
      _ = ‖(s : T)‖ * ((C_φ' / ν.prod (r · ^ ·)) * spectralNorm F M y) := by rw [hu_norm]; ring
  · -- Membership in `Set.range (algebraMap T F)` whenever `y ^ q ∈ T`.
    let ry : T' := frobeniusRootRestrictedEquiv p e (fun _ ↦ rfl) fy
    have hι_y : ι y = algebraMap T' F' ry := iterateFrobenius_inj F' p e <| by
      simp only [iterateFrobenius_def]
      rw [← map_pow, ← hfy, Function.comp_apply, hι_alg fy,
        ← frobeniusRootRestrictedEquiv_pow (fun _ ↦ rfl) hr fy, map_pow]
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T)
      (b.repr y)
    choose a ha using hs
    have hmul_T' : Ψ (s : T) * ry = ∑ j, Ψ (a j) * rootG j := IsFractionRing.injective T' F' <| by
      rw [hι_clear y s a ha, map_mul, ← hι_y]
    have hexp_ne : _root_.MvPowerSeries.expand q hq ((s : T) : _root_.MvPowerSeries σ K) ≠ 0 :=
      fun h0 ↦ hΨ_inj.ne (nonZeroDivisors.ne_zero s.property) <| by
        rw [Ψ.map_zero]
        exact Subtype.ext <| by
          rw [coe_frobeniusRootRestrictedHom p e hr (s : T), h0, map_zero, ZeroMemClass.coe_zero]
    have hry_mem : ∀ α, coeff α (ry : _root_.MvPowerSeries σ K') ∈ E := by
      refine _root_.MvPowerSeries.coeff_mem_of_coeff_map_mul_mem E hexp_ne
        (g := (ry : _root_.MvPowerSeries σ K')) fun β ↦ ?_
      have hβ : _root_.MvPowerSeries.map (algebraMap K K')
          (_root_.MvPowerSeries.expand q hq ((s : T) : _root_.MvPowerSeries σ K)) *
            (ry : _root_.MvPowerSeries σ K') =
          ((∑ j, Ψ (a j) * rootG j : T') : _root_.MvPowerSeries σ K') := by
        rw [← coe_frobeniusRootRestrictedHom p e hr (s : T), ← Subring.coe_mul, ← hmul_T']
      rw [hβ]
      exact hsum_mem a β
    have hcomp_ry :
        restrictedExpandComponentFamily hq hr ν E (∑ j, Ψ (a j) * rootG j) (hsum_mem a) =
          (s : T) • restrictedExpandComponentFamily hq hr ν E ry hry_mem := by
      rw [← restrictedExpandComponentFamily_restrictedExpand_mul hq hr hν h_iso E (s : T) ry
          hry_mem (hz_mul := coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E (s : T)
            hry_mem)]
      exact restrictedExpandComponentFamily_congr hq hr ν E
        (hmul_T'.symm.trans (congrArg (· * ry) (hΨ_def (s : T))))
    have hπ_eq : (s : T) * π (restrictedExpandComponentFamily hq hr ν E ry hry_mem) =
        ∑ j, a j * g j := by
      rw [hπ_sum a, hcomp_ry, map_smul, smul_eq_mul]
    refine ⟨π (restrictedExpandComponentFamily hq hr ν E ry hry_mem),
      mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property) ?_⟩
    rw [← map_mul, hπ_eq]
    exact (b.algebraMap_mul_constr_eq_algebraMap_sum g y (s : T) a ha).symm
  · refine hπ_ne (IsFractionRing.injective T F ?_)
    change algebraMap T F
      (π (restrictedExpandComponentFamily hq hr ν E (∑ j, Ψ (a₀ j) * rootG j) (hsum_mem a₀))) =
      algebraMap T F 0
    rw [← hπ_sum a₀]
    dsimp only [φ] at hφ0
    rw [map_zero, ← b.algebraMap_mul_constr_eq_algebraMap_sum g x₀ (s₀ : T) a₀ ha₀, hφ0, mul_zero]

end SeparatingDual

end TauCeti.MvPowerSeries
