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

import Mathlib.Algebra.CharP.Reduced
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.Localization.Integer
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Purely inseparable extensions of Tate fraction fields via Frobenius roots

Let `K` be an ultrametric normed field of exponential characteristic `p`, `σ` a variable type, and
`c : σ → ℝ` a positive polyradius. Given `e : ℕ`, let `q := p ^ e`, `K' := FrobeniusRoot K p e`,
and `r : σ → ℝ` a positive polyradius satisfying `r i ^ q = c i`. Building on the general
base-changed expansion and coefficient-submodule separation infrastructure in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand`, this file constructs the Frobenius-root and
purely inseparable extension machinery for analyzing finite purely inseparable extensions `M` of
`F := GaussFractionField σ K c` of exponent at most `e`:

1. `TauCeti.MvPowerSeries.restrictedFrobeniusRoot`: applying `FrobeniusRoot.root K p e`
   coefficientwise gives a ring homomorphism `K{X / c} →+* K'{X / r}` extracting explicit `q`-th
   roots with respect to `TauCeti.MvPowerSeries.restrictedExpandAlgebraMap`.
2. `TauCeti.MvPowerSeries.exists_ringHom_norm_eq_spectralNorm_of_isPurelyInseparable`: embeds `M`
   into `GaussFractionField σ K' r` compatibly with `restrictedExpandAlgebraMap`, satisfying
   `‖ι y‖ = spectralNorm F M y` and sending an `F`-basis of `M` into `K'{X / r}`.
3. `TauCeti.MvPowerSeries.exists_dual_norm_le_spectralNorm_of_isPurelyInseparable`: when `K` is
   complete and `σ` is countable, every nonzero `x₀ : M` is separated from `0` by an `F`-linear
   functional `φ : Module.Dual F M` that is bounded by `spectralNorm F M` and sends every element
   of `M` whose `p ^ e`-th power lies in `K{X / c}` into `Set.range (algebraMap T F)`.

These constructions feed both characteristic-free weak stability of `GaussFractionField`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §5.3.1, Theorem 1) and the Japanese property of
integrally closed restricted-series rings (Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*,
§5.3.2, Theorem 1).

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §§3.5.3, 5.3.1, and 5.3.2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology IntermediateField

section FrobeniusRoot

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
private theorem rpow_inv_eq_of_pow_eq {p e : ℕ} [ExpChar K p] {c r : σ → ℝ}
    [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i) (i : σ) :
    c i ^ (((p ^ e : ℕ) : ℝ)⁻¹) = r i := by
  have hq : ((p ^ e : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_pos (expChar_pos K p) e).ne'
  rw [← hr i, ← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < r i).le,
    mul_inv_cancel₀ hq, Real.rpow_one]

private theorem norm_coeff_frobeniusRoot_mul_prod {p e : ℕ} [ExpChar K p] {c r : σ → ℝ}
    [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) (μ : σ →₀ ℕ) :
    ‖coeff μ (MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K))‖ *
        μ.prod (r · ^ ·) =
      (‖coeff μ (f : _root_.MvPowerSeries σ K)‖ * μ.prod (c · ^ ·)) ^ (((p ^ e : ℕ) : ℝ)⁻¹) := by
  have hc_pos (i : σ) : 0 < c i := hr i ▸ pow_pos (Fact.out : 0 < r i) _
  have hprod_nonneg : 0 ≤ μ.prod (c · ^ ·) :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc_pos i).le _
  rw [Real.mul_rpow (norm_nonneg _) hprod_nonneg, coeff_map, FrobeniusRoot.norm_root,
    μ.prod_pow_rpow fun i _ ↦ (hc_pos i).le]
  congr 1
  exact Finset.prod_congr rfl fun i _ ↦ by
    dsimp only
    rw [rpow_inv_eq_of_pow_eq (K := K) hr i]

/-- Applying `FrobeniusRoot.root K p e` coefficientwise gives a ring homomorphism
`K{X / c} →+* (FrobeniusRoot K p e){X / r}` whenever `r i ^ p ^ e = c i`. -/
noncomputable def restrictedFrobeniusRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i) :
    IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := FrobeniusRoot K p e) r :=
  ((MvPowerSeries.map (FrobeniusRoot.root K p e)).comp
    (IsRestricted.subring (R := K) c).subtype).codRestrict _ fun f ↦ by
    have hq_inv : 0 < (((p ^ e : ℕ) : ℝ)⁻¹) :=
      inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e))
    have hlim :=
      ((Real.continuousAt_rpow_const 0 (((p ^ e : ℕ) : ℝ)⁻¹) (Or.inr hq_inv.le)).tendsto.comp
        f.property)
    rw [Real.zero_rpow hq_inv.ne'] at hlim
    refine hlim.congr fun μ ↦ ?_
    exact (norm_coeff_frobeniusRoot_mul_prod hr f μ).symm

/-- The underlying formal power series of `restrictedFrobeniusRoot` is
`MvPowerSeries.map (FrobeniusRoot.root K p e)`. -/
theorem coe_restrictedFrobeniusRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) :
    (restrictedFrobeniusRoot p e hr f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K) :=
  (rfl)

/-- `restrictedFrobeniusRoot` acts coefficientwise by `FrobeniusRoot.root K p e`. -/
@[simp]
theorem coeff_restrictedFrobeniusRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) (μ : σ →₀ ℕ) :
    coeff μ (restrictedFrobeniusRoot p e hr f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      FrobeniusRoot.root K p e (coeff μ (f : _root_.MvPowerSeries σ K)) := by
  rw [coe_restrictedFrobeniusRoot, coeff_map]

/-- `restrictedFrobeniusRoot` sends scalar constants to their `p ^ e`-th roots in
`FrobeniusRoot K p e`. -/
@[simp]
theorem restrictedFrobeniusRoot_algebraMap (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i) (a : K) :
    restrictedFrobeniusRoot p e hr (algebraMap K (IsRestricted.subring (R := K) c) a) =
      algebraMap (FrobeniusRoot K p e) (IsRestricted.subring (R := FrobeniusRoot K p e) r)
        (FrobeniusRoot.root K p e a) := by
  apply Subtype.ext
  simp [coe_restrictedFrobeniusRoot, coe_algebraMap_isRestrictedSubring]

/-- `restrictedFrobeniusRoot` fixes each coordinate indeterminate `X i`. -/
@[simp]
theorem restrictedFrobeniusRoot_X (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i) (i : σ) :
    restrictedFrobeniusRoot p e hr
        (⟨X i, isRestricted_X c i⟩ : IsRestricted.subring (R := K) c) =
      ⟨X i, isRestricted_X r i⟩ := by
  apply Subtype.ext
  simp [coe_restrictedFrobeniusRoot]

/-- `restrictedFrobeniusRoot` is injective. -/
theorem restrictedFrobeniusRoot_injective (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i) :
    Function.Injective (restrictedFrobeniusRoot (σ := σ) (K := K) p e hr) := by
  intro f g h
  apply Subtype.ext
  ext μ
  have hμ := congrArg (fun u : IsRestricted.subring (R := FrobeniusRoot K p e) r ↦
    coeff μ (u : _root_.MvPowerSeries σ (FrobeniusRoot K p e))) h
  simp only [coeff_restrictedFrobeniusRoot] at hμ
  exact FrobeniusRoot.root_injective hμ

/-- `restrictedFrobeniusRoot` raises Gauss norms to the `(p ^ e)⁻¹`-th power. -/
@[simp]
theorem norm_restrictedFrobeniusRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) :
    ‖restrictedFrobeniusRoot p e hr f‖ = ‖f‖ ^ (((p ^ e : ℕ) : ℝ)⁻¹) := by
  have hq_pos : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) := Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e)
  have hq_inv : 0 < (((p ^ e : ℕ) : ℝ)⁻¹) := inv_pos.mpr hq_pos
  refine le_antisymm (norm_le_iff.2 fun μ ↦ ?_) ?_
  · rw [coe_restrictedFrobeniusRoot, norm_coeff_frobeniusRoot_mul_prod hr f μ]
    exact Real.rpow_le_rpow (mul_nonneg (norm_nonneg _) (prod_pow_pos μ).le)
      (norm_coeff_mul_prod_le f μ) hq_inv.le
  · rw [Real.rpow_inv_le_iff_of_pos (norm_nonneg _) (norm_nonneg _) hq_pos, norm_le_iff]
    intro μ
    rw [← Real.rpow_inv_le_iff_of_pos (mul_nonneg (norm_nonneg _) (prod_pow_pos μ).le)
      (norm_nonneg _) hq_pos, ← norm_coeff_frobeniusRoot_mul_prod hr f μ,
      ← coe_restrictedFrobeniusRoot p e hr f]
    exact norm_coeff_mul_prod_le (restrictedFrobeniusRoot p e hr f) μ

/-- Raising `restrictedFrobeniusRoot p e hr f` to the `p ^ e`-th power equals the
Frobenius-expanded image of `f` under `restrictedExpandAlgebraMap`. -/
theorem restrictedFrobeniusRoot_pow {p : ℕ} [ExpChar K p] {e : ℕ}
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] (hr : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) :
    restrictedFrobeniusRoot p e hr f ^ p ^ e =
      restrictedExpandAlgebraMap (K' := FrobeniusRoot K p e) (p ^ e)
        (pow_pos (expChar_pos K p) e).ne' hr f := by
  have hp : p ≠ 0 := (expChar_pos K p).ne'
  have hhom : (iterateFrobenius (FrobeniusRoot K p e) p e).comp (FrobeniusRoot.root K p e) =
      algebraMap K (FrobeniusRoot K p e) := RingHom.ext FrobeniusRoot.root_pow_expChar_pow
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_restrictedFrobeniusRoot, coe_restrictedExpandAlgebraMap,
    ← MvPowerSeries.map_iterateFrobenius_expand p hp _ e, ← MvPowerSeries.map_expand,
    MvPowerSeries.map_map, hhom, MvPowerSeries.map_expand]

/-- Embeds a finite purely inseparable extension `M` of `GaussFractionField σ K c` of exponent at
most `e` in exponential characteristic `p` into `GaussFractionField σ (FrobeniusRoot K p e) r`
(for positive `r` with `r i ^ p ^ e = c i`) compatibly with `restrictedExpandAlgebraMap`, with
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
          (restrictedExpandAlgebraMap (K' := FrobeniusRoot K p e) (p ^ e)
            (pow_pos (expChar_pos K p) e).ne' hr f)) ∧
      (∀ y : M, ‖ι y‖ = spectralNorm (GaussFractionField σ K c) M y) ∧
      (∀ j : Fin m, ι (b j) =
        algebraMap (IsRestricted.subring (R := FrobeniusRoot K p e) r)
          (GaussFractionField σ (FrobeniusRoot K p e) r) (rootG j)) := by
  classical
  let K' := FrobeniusRoot K p e
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  let Ψ := restrictedExpandAlgebraMap (K := K) (K' := K') (p ^ e)
    (pow_pos (expChar_pos K p) e).ne' hr
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have hΨ_norm (f : T) : ‖Ψ f‖ = ‖f‖ := norm_restrictedExpandAlgebraMap _ _ hr f
  have hΨ_inj : Function.Injective Ψ.toRingHom :=
    restrictedExpandAlgebraMap_injective _ _ hr
  let _ : Algebra F F' := (Ψ.toRingHom.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg : algebraMap F F' = Ψ.toRingHom.gaussFractionFieldMap hΨ_inj :=
    RingHom.algebraMap_toAlgebra _
  -- Pick an `F`-basis `b` of `M` whose `p ^ e`-th powers lie in `T`, with roots in `T'`.
  let m := Module.finrank F M
  obtain ⟨w, g, hg⟩ :=
    IsPurelyInseparable.exists_iterateFrobenius_unitsSMul_eq_algebraMap T F M p he
      (Module.finBasis F M)
  let b := (Module.finBasis F M).unitsSMul w
  let rootG (j : Fin m) : T' := restrictedFrobeniusRoot p e hr (g j)
  have hrootG_pow (j : Fin m) : rootG j ^ p ^ e = Ψ (g j) := restrictedFrobeniusRoot_pow hr (g j)
  -- Embed `M` `F`-linearly into `F'` by sending `b` to the `p ^ e`-th roots `rootG`.
  have hspan_b : IntermediateField.adjoin F (Set.range b) = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    rw [← b.sum_repr y]
    refine sum_mem fun j _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  have hΨ_map (f : T) :
      Ψ.toRingHom.gaussFractionFieldMap hΨ_inj (algebraMap T F f) = algebraMap T' F' (Ψ f) :=
    Ψ.toRingHom.gaussFractionFieldMap_algebraMap hΨ_inj f
  have ⟨ι₀⟩ : Nonempty (M →ₐ[F] F') :=
    IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq F M p he F' hspan_b <| by
      rintro _ ⟨j, rfl⟩
      exact ⟨algebraMap T' F' (rootG j), by
        rw [← map_pow, hrootG_pow, ← hΨ_map, ← hF_alg, ← hg]⟩
  refine ⟨m, b, rootG, ι₀.toRingHom, fun f ↦ ?_, fun y ↦ ?_, fun j ↦ ?_⟩
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, hF_alg, hΨ_map]
  · obtain ⟨k, a, ha⟩ := IsPurelyInseparable.pow_mem F p y
    have hpk : p ^ k ≠ 0 := (pow_pos (expChar_pos K p) k).ne'
    refine (pow_left_inj₀ (norm_nonneg _) (spectralNorm_nonneg _) hpk).mp ?_
    have hι_pow : (ι₀ y) ^ p ^ k = Ψ.toRingHom.gaussFractionFieldMap hΨ_inj a := by
      rw [← map_pow, ← ha, AlgHom.commutes, hF_alg]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← norm_pow, hι_pow,
      Ψ.toRingHom.norm_gaussFractionFieldMap hΨ_inj hΨ_norm,
      TauCeti.spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hpk ha.symm]
  · refine iterateFrobenius_inj F' p e ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, iterateFrobenius_def]
    rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p he (b j),
      AlgHom.commutes, hF_alg, ← map_pow, hrootG_pow, hg, hΨ_map]

end FrobeniusRoot

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
  have hqR_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  let K' := FrobeniusRoot K p e
  let r : σ → ℝ := fun i ↦ c i ^ ((q : ℝ)⁻¹)
  have hr_fact : ∀ i, Fact (0 < r i) := fun i ↦ ⟨Real.rpow_pos_of_pos (Fact.out : 0 < c i) _⟩
  have hr (i : σ) : r i ^ q = c i := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < c i).le, inv_mul_cancel₀ hqR_ne,
      Real.rpow_one]
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  let Ψ := restrictedExpandAlgebraMap (K := K) (K' := K') q hq hr
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  obtain ⟨m, b, rootG, ι, hι_alg, hι_norm, hι_b⟩ :=
    exists_ringHom_norm_eq_spectralNorm_of_isPurelyInseparable M p e le_rfl hr
  -- Span a countably generated `K`-subspace `E ⊆ K'` from all coefficients of `rootG`.
  let S : Set K' := Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
    coeff idx.2 (rootG idx.1 : _root_.MvPowerSeries σ K')
  let E : Submodule K K' := Submodule.span K S
  let rootGSub (j : Fin m) : restrictedCoeffSubmodule r E :=
    ⟨rootG j, mem_restrictedCoeffSubmodule.mpr fun α ↦ Submodule.subset_span ⟨(j, α), rfl⟩⟩
  let linComb (a : Fin m → T) : restrictedCoeffSubmodule r E :=
    ∑ j, ⟨Ψ (a j) * rootG j, mul_mem_restrictedCoeffSubmodule hq hr (a j) (rootGSub j).property⟩
  have hlin (a : Fin m → T) : (linComb a).val = ∑ j, Ψ (a j) * rootG j := by simp [linComb]
  have hmul_eq (z : M) (s : nonZeroDivisors T) (a : Fin m → T)
      (ha : ∀ j, algebraMap T F (a j) = (s : T) • b.repr z j) :
      algebraMap T' F' (linComb a).val = algebraMap T' F' (Ψ (s : T)) * ι z := by
    rw [hlin]
    exact b.algebraMap_sum_mul_eq_mul Ψ.toRingHom rootG ι hι_alg hι_b z (s : T) a ha
  -- Clear denominators of `b.repr x₀` and pick a separating bounded map `π` into `T`.
  obtain ⟨s₀, hs₀⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T) (b.repr x₀)
  choose a₀ ha₀ using hs₀
  have hu₀_ne : linComb a₀ ≠ 0 := fun h0 ↦ by
    have hs₀_ne : algebraMap T' F' (Ψ (s₀ : T)) ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_algebraMap_gaussFractionField, norm_restrictedExpandAlgebraMap,
        norm_ne_zero_iff]
      exact nonZeroDivisors.ne_zero s₀.property
    have hmul : algebraMap T' F' (Ψ (s₀ : T)) * ι x₀ = 0 := by
      rw [← hmul_eq x₀ s₀ a₀ ha₀, congrArg Subtype.val h0, ZeroMemClass.coe_zero, map_zero]
    exact mul_ne_zero hs₀_ne ((map_ne_zero_iff ι ι.injective).mpr hx₀) hmul
  obtain ⟨π, C_π, hC_π, hπ_mul, hπ_norm, hπ_ne⟩ :=
    exists_linearMap_restrictedCoeffSubmodule_ne_zero hq hr
      (FrobeniusRoot.exists_dual_norm_le_and_ne_zero_span_of_countable (Set.countable_range _))
      (linComb a₀) hu₀_ne
  let g (j : Fin m) : T := π (rootGSub j)
  have hπ_lin (a : Fin m → T) : ∑ j, a j * g j = π (linComb a) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ (hπ_mul (a j) (rootGSub j)).symm
  let φ : Module.Dual F M := b.constr F fun j ↦ algebraMap T F (g j)
  refine ⟨φ, C_π, hC_π, fun y ↦ ?_, fun y ⟨fy, hfy⟩ ↦ ?_, fun hφ0 ↦ ?_⟩
  · -- Spectral-norm bound for `φ`.
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T)
      (b.repr y)
    choose a ha using hs
    have hu_norm : ‖linComb a‖ = ‖(s : T)‖ * spectralNorm F M y := by
      rw [← Submodule.norm_coe, ← norm_algebraMap_gaussFractionField σ K' r _,
        hmul_eq y s a ha, norm_mul, norm_algebraMap_gaussFractionField σ K' r _,
        norm_restrictedExpandAlgebraMap, hι_norm]
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
      _ ≤ C_π * ‖linComb a‖ := by rw [hπ_lin]; exact hπ_norm (linComb a)
      _ = ‖(s : T)‖ * (C_π * spectralNorm F M y) := by rw [hu_norm]; ring
  · -- Membership in `Set.range (algebraMap T F)` whenever `y ^ q ∈ T`.
    let ry : T' := restrictedFrobeniusRoot p e hr fy
    have hι_y : ι y = algebraMap T' F' ry := iterateFrobenius_inj F' p e <| by
      simp only [iterateFrobenius_def]
      rw [← map_pow, ← hfy, Function.comp_apply, hι_alg fy, ← restrictedFrobeniusRoot_pow hr fy,
        map_pow]
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T)
      (b.repr y)
    choose a ha using hs
    have hmul_T' : Ψ (s : T) * ry = (linComb a).val := IsFractionRing.injective T' F' <| by
      rw [hmul_eq y s a ha, map_mul, ← hι_y]
    have hry_mem : ry ∈ restrictedCoeffSubmodule r E :=
      mem_restrictedCoeffSubmodule_of_mul_mem hq hr (nonZeroDivisors.ne_zero s.property)
        (hmul_T'.symm ▸ (linComb a).property)
    have hπ_eq : (s : T) * π ⟨ry, hry_mem⟩ = ∑ j, a j * g j := by
      rw [hπ_lin, ← hπ_mul (s : T) ⟨ry, hry_mem⟩]
      exact congrArg π (Subtype.ext hmul_T')
    refine ⟨π ⟨ry, hry_mem⟩,
      mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property) ?_⟩
    rw [← map_mul, hπ_eq]
    exact (b.algebraMap_mul_constr_eq_algebraMap_sum g y (s : T) a ha).symm
  · refine hπ_ne (IsFractionRing.injective T F ?_)
    dsimp only [φ] at hφ0
    rw [← hπ_lin, map_zero, ← b.algebraMap_mul_constr_eq_algebraMap_sum g x₀ (s₀ : T) a₀ ha₀,
      hφ0, mul_zero]

end SeparatingDual

end TauCeti.MvPowerSeries
