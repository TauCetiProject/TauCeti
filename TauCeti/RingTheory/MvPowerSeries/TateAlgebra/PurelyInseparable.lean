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
import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.LexOrder
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# Purely inseparable extensions of Tate fraction fields via Frobenius roots

Let `K` be an ultrametric normed field of exponential characteristic `p`, `σ` a variable type, and
`c : σ → ℝ` a positive polyradius. Given `e : ℕ`, let `q := p ^ e`, `K' := FrobeniusRoot K p e`,
and `r : σ → ℝ` a positive polyradius satisfying `r i ^ q = c i`. This file constructs the shared
infrastructure for analyzing finite purely inseparable extensions `M` of
`F := GaussFractionField σ K c` of exponent at most `e`:

1. `TauCeti.MvPowerSeries.restrictedExpandAlgebraMap`: the canonical `K`-algebra homomorphism
   `K{X / c} →ₐ[K] K'{X / r}` combining coefficient extension along `algebraMap K K'` with variable
   expansion `X i ↦ X i ^ q`.
2. `TauCeti.MvPowerSeries.restrictedFrobeniusRoot`: applying `FrobeniusRoot.root K p e`
   coefficientwise gives a ring homomorphism `K{X / c} →+* K'{X / r}` extracting explicit `q`-th
   roots with respect to `restrictedExpandAlgebraMap`.
3. `TauCeti.MvPowerSeries.exists_ringHom_norm_eq_spectralNorm_of_isPurelyInseparable`: embeds `M`
   into `GaussFractionField σ K' r` compatibly with `restrictedExpandAlgebraMap`, satisfying
   `‖ι y‖ = spectralNorm F M y` and sending an `F`-basis of `M` into `K'{X / r}`.
4. `TauCeti.MvPowerSeries.exists_dual_norm_le_spectralNorm_of_isPurelyInseparable`: when `K` is
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

section ExpandAlgebraMap

variable {σ K K' : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedCommRing K'] [IsUltrametricDist K'] [NormedAlgebra K K']
  {c r : σ → ℝ}

/-- Substituting `X i ↦ X i ^ q` and mapping coefficients along `algebraMap K K'` gives a
`K`-algebra homomorphism `K{X / c} →ₐ[K] K'{X / r}` whenever `r i ^ q = c i`. -/
noncomputable def restrictedExpandAlgebraMap (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) :
    IsRestricted.subring (R := K) c →ₐ[K] IsRestricted.subring (R := K') r where
  toRingHom :=
    (restrictedExpand q hq hr).toRingHom.comp
      (restrictedMap (algebraMap K K') (C := ‖(1 : K')‖) fun a ↦ by
        rw [Algebra.algebraMap_eq_smul_one, mul_comm]
        exact norm_smul_le a (1 : K'))
  commutes' a := Subtype.ext <| by
    rw [RingHom.toFun_eq_coe, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_restrictedExpand, coe_restrictedMap, coe_algebraMap_isRestrictedSubring,
      MvPowerSeries.map_C, expand_C,
      IsScalarTower.algebraMap_apply K K' (IsRestricted.subring (R := K') r),
      coe_algebraMap_isRestrictedSubring]

private theorem restrictedExpandAlgebraMap_eq (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (f : IsRestricted.subring (R := K) c) :
    restrictedExpandAlgebraMap (K' := K') q hq hr f =
      restrictedExpand q hq hr
        (restrictedMap (algebraMap K K') (C := ‖(1 : K')‖) (fun a ↦ by
          rw [Algebra.algebraMap_eq_smul_one, mul_comm]
          exact norm_smul_le a (1 : K')) f) :=
  rfl

/-- The underlying formal power series of `restrictedExpandAlgebraMap` is `expand q` composed with
`MvPowerSeries.map (algebraMap K K')`. -/
theorem coe_restrictedExpandAlgebraMap (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (f : IsRestricted.subring (R := K) c) :
    (restrictedExpandAlgebraMap (K' := K') q hq hr f : _root_.MvPowerSeries σ K') =
      expand q hq (MvPowerSeries.map (algebraMap K K') (f : _root_.MvPowerSeries σ K)) := by
  rw [restrictedExpandAlgebraMap_eq, coe_restrictedExpand, coe_restrictedMap]

/-- `restrictedExpandAlgebraMap` sends each coordinate indeterminate `X i` to `X i ^ q`. -/
@[simp]
theorem restrictedExpandAlgebraMap_X (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) (i : σ) :
    restrictedExpandAlgebraMap (K' := K') q hq hr
        (⟨X i, isRestricted_X c i⟩ : IsRestricted.subring (R := K) c) =
      (⟨X i, isRestricted_X r i⟩ : IsRestricted.subring (R := K') r) ^ q := by
  apply Subtype.ext
  simp [coe_restrictedExpandAlgebraMap]

/-- `restrictedExpandAlgebraMap` is injective whenever `algebraMap K K'` is injective. -/
theorem restrictedExpandAlgebraMap_injective [FaithfulSMul K K']
    (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) :
    Function.Injective (restrictedExpandAlgebraMap (σ := σ) (K := K) (K' := K') q hq hr) := by
  intro f g h
  apply Subtype.ext
  ext μ
  have hμ := congrArg (fun u : IsRestricted.subring (R := K') r ↦
    coeff (q • μ) (u : _root_.MvPowerSeries σ K')) h
  simp only [coe_restrictedExpandAlgebraMap, coeff_expand_smul, coeff_map] at hμ
  exact FaithfulSMul.algebraMap_injective K K' hμ

/-- Over a normed field `K` and a normed `K`-algebra `K'` with `‖1‖ = 1`,
`restrictedExpandAlgebraMap` preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedExpandAlgebraMap [NormOneClass K']
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (f : IsRestricted.subring (R := K) c) :
    ‖restrictedExpandAlgebraMap (K' := K') q hq hr f‖ = ‖f‖ := by
  rw [restrictedExpandAlgebraMap_eq, norm_restrictedExpand,
    norm_restrictedMap _ _ (norm_algebraMap' K')]

end ExpandAlgebraMap

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
      ((Real.continuousAt_rpow_const 0 (((p ^ e : ℕ) : ℝ)⁻¹) (Or.inr hq_inv.le)).tendsto.comp f.2)
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

section ComponentDual

variable {σ K K' : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K']

/-- The `K`-submodule of restricted series `K'{X / r}` whose coefficients all lie in `E`. -/
private def restrictedCoeffSubmodule (r : σ → ℝ) (E : Submodule K K') :
    Submodule K (IsRestricted.subring (R := K') r) where
  carrier := {u | ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E}
  zero_mem' _ := by simp
  add_mem' hu hv α := by simpa using E.add_mem (hu α) (hv α)
  smul_mem' a u hu α := by
    change coeff α ((algebraMap K (IsRestricted.subring (R := K') r) a * u :
      IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E
    rw [Subring.coe_mul, IsScalarTower.algebraMap_apply K K' (IsRestricted.subring (R := K') r),
      coe_algebraMap_isRestrictedSubring, coeff_C_mul, ← Algebra.smul_def]
    exact E.smul_mem a (hu α)

private theorem mul_mem_restrictedCoeffSubmodule {c r : σ → ℝ} {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} (d : IsRestricted.subring (R := K) c)
    {u : IsRestricted.subring (R := K') r} (hu : u ∈ restrictedCoeffSubmodule r E) :
    restrictedExpandAlgebraMap (K' := K') q hq hr d * u ∈ restrictedCoeffSubmodule r E := fun β ↦ by
  rw [Subring.coe_mul, coe_restrictedExpandAlgebraMap, ← MvPowerSeries.map_expand]
  exact MvPowerSeries.coeff_map_mul_mem _ hu β

private theorem mem_restrictedCoeffSubmodule_of_mul_mem {c r : σ → ℝ} {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} {d : IsRestricted.subring (R := K) c}
    (hd : d ≠ 0) {u : IsRestricted.subring (R := K') r}
    (hdu : restrictedExpandAlgebraMap (K' := K') q hq hr d * u ∈ restrictedCoeffSubmodule r E) :
    u ∈ restrictedCoeffSubmodule r E := by
  have hexp_ne : MvPowerSeries.expand q hq (d : _root_.MvPowerSeries σ K) ≠ 0 := by
    rw [← coe_restrictedExpand q hq hr d]
    exact Subtype.coe_ne_coe.mpr ((map_ne_zero_iff _ (restrictedExpand_injective q hq hr)).mpr hd)
  refine fun α ↦ MvPowerSeries.coeff_mem_of_coeff_map_mul_mem hexp_ne (fun β ↦ ?_) α
  simpa only [Subring.coe_mul, coe_restrictedExpandAlgebraMap, ← MvPowerSeries.map_expand] using
    hdu β

/-- Extracting the `ν`-th `q`-adic component sends `restrictedCoeffSubmodule r E` `K`-linearly into
`IsRestrictedFamily.addSubgroup E c`. -/
private noncomputable def restrictedExpandComponentFamily {c r : σ → ℝ} [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) (E : Submodule K K') (ν : σ →₀ ℕ) :
    restrictedCoeffSubmodule r E →ₗ[K] IsRestrictedFamily.addSubgroup E c where
  toFun u :=
    ⟨fun α ↦ ⟨coeff α (restrictedExpandComponent hq hr ν u.1 : _root_.MvPowerSeries σ K'), by
        rw [coeff_restrictedExpandComponent]; exact u.2 (q • α + ν)⟩,
      IsRestrictedFamily.mem_addSubgroup.mpr <|
        ((isRestrictedFamily_coeff_iff _).mpr
          (restrictedExpandComponent hq hr ν u.1).2).of_norm_le (C := 1) fun _ ↦
            (one_mul _).symm.le⟩
  map_add' u v := IsRestrictedFamily.ext fun α ↦ Subtype.ext <| by
    simp [restrictedExpandComponent_add]
  map_smul' a u := IsRestrictedFamily.ext fun α ↦ Subtype.ext <| by
    simp only [RingHom.id_apply, IsRestrictedFamily.coe_smul, Pi.smul_apply, SetLike.val_smul]
    change coeff α (restrictedExpandComponent hq hr ν (a • u.1) : _root_.MvPowerSeries σ K') =
      a • coeff α (restrictedExpandComponent hq hr ν u.1 : _root_.MvPowerSeries σ K')
    rw [Algebra.smul_def, coeff_restrictedExpandComponent, Subring.coe_mul,
      IsScalarTower.algebraMap_apply K K' (IsRestricted.subring (R := K') r),
      coe_algebraMap_isRestrictedSubring, coeff_C_mul, coeff_restrictedExpandComponent,
      ← Algebra.smul_def]

/-- Composing `restrictedExpandComponentFamily` with a norm-bounded `K`-linear functional on `E`
yields a `K`-linear map `restrictedCoeffSubmodule r E →ₗ[K] K{X / c}`. -/
private noncomputable def restrictedExpandComponentDual {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) (E : Submodule K K') (ν : σ →₀ ℕ)
    (f : E →ₗ[K] K) {C : ℝ} (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖) :
    restrictedCoeffSubmodule r E →ₗ[K] IsRestricted.subring (R := K) c :=
  (IsRestrictedFamily.subringLinearEquiv.symm.toLinearMap.restrictScalars K).comp
    ((IsRestrictedFamily.mapLinearMap f hf).comp (restrictedExpandComponentFamily hq hr E ν))

private theorem coeff_restrictedExpandComponentDual {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} (ν : σ →₀ ℕ)
    (f : E →ₗ[K] K) {C : ℝ} (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖)
    (u : restrictedCoeffSubmodule r E) (α : σ →₀ ℕ) :
    coeff α (restrictedExpandComponentDual hq hr E ν f hf u : _root_.MvPowerSeries σ K) =
      f ⟨coeff (q • α + ν) (u.1 : _root_.MvPowerSeries σ K'), u.2 (q • α + ν)⟩ := by
  simp only [restrictedExpandComponentDual, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap, IsRestrictedFamily.coeff_coe_subringLinearEquiv_symm_apply,
    IsRestrictedFamily.coe_mapLinearMap, Function.comp_apply, restrictedExpandComponentFamily,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  exact Subtype.ext (coeff_restrictedExpandComponent hq hr ν α u.1)

private theorem restrictedExpandComponentDual_mul {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'}
    {ν : σ →₀ ℕ} (hν : ∀ i, ν i < q)
    (f : E →ₗ[K] K) {C : ℝ} (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖)
    (d : IsRestricted.subring (R := K) c) (u : restrictedCoeffSubmodule r E) :
    restrictedExpandComponentDual hq hr E ν f hf
        ⟨restrictedExpandAlgebraMap (K' := K') q hq hr d * u.1,
          mul_mem_restrictedCoeffSubmodule hq hr d u.2⟩ =
      d * restrictedExpandComponentDual hq hr E ν f hf u := by
  classical
  have hw_mul :
      restrictedExpandComponentFamily hq hr E ν
          ⟨restrictedExpandAlgebraMap (K' := K') q hq hr d * u.1,
            mul_mem_restrictedCoeffSubmodule hq hr d u.2⟩ =
        d • restrictedExpandComponentFamily hq hr E ν u := by
    apply IsRestrictedFamily.ext
    intro α
    apply Subtype.ext
    dsimp only [restrictedExpandComponentFamily, LinearMap.coe_mk, AddHom.coe_mk]
    rw [restrictedExpandAlgebraMap_eq,
      restrictedExpandComponent_restrictedExpand_mul hq hr hν _ u.1,
      IsRestrictedFamily.coe_isRestrictedSubring_smul, convSMul_apply, Submodule.coe_sum,
      Subring.coe_mul, coeff_mul]
    refine Finset.sum_congr rfl fun pq _ ↦ ?_
    rw [SetLike.val_smul, Algebra.smul_def, coeff_restrictedMap]
  dsimp only [restrictedExpandComponentDual, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap]
  rw [hw_mul, IsRestrictedFamily.mapLinearMap_isRestrictedSubring_smul,
    IsRestrictedFamily.subringLinearEquiv.symm.map_smul, smul_eq_mul]

private theorem norm_restrictedExpandComponentDual_le {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} (ν : σ →₀ ℕ)
    (f : E →ₗ[K] K) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖)
    (u : restrictedCoeffSubmodule r E) :
    ‖restrictedExpandComponentDual hq hr E ν f hf u‖ ≤
      (C / ν.prod (r · ^ ·)) * ‖u.1‖ := by
  calc ‖restrictedExpandComponentDual hq hr E ν f hf u‖
      ≤ C * ‖restrictedExpandComponent hq hr ν u.1‖ := by
        refine norm_le_mul_of_norm_coeff_le fun α ↦ ?_
        rw [coeff_restrictedExpandComponentDual, coeff_restrictedExpandComponent]
        exact hf ⟨coeff (q • α + ν) (u.1 : _root_.MvPowerSeries σ K'), u.2 (q • α + ν)⟩
    _ ≤ C * (‖u.1‖ / ν.prod (r · ^ ·)) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ (prod_pow_pos ν)).mpr
          (norm_restrictedExpandComponent_mul_prod_le hq hr ν u.1)) hC
    _ = (C / ν.prod (r · ^ ·)) * ‖u.1‖ := by ring

private theorem exists_linearMap_restrictedCoeffSubmodule_ne_zero {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'}
    (hsep : ∀ {x : E}, x ≠ 0 → ∃ (f : E →ₗ[K] K) (C : ℝ),
      0 ≤ C ∧ (∀ v : E, ‖f v‖ ≤ C * ‖v‖) ∧ f x ≠ 0)
    (u₀ : restrictedCoeffSubmodule r E) (hu₀_ne : u₀.1 ≠ 0) :
    ∃ (π : restrictedCoeffSubmodule r E →ₗ[K] IsRestricted.subring (R := K) c) (C_π : ℝ),
      0 ≤ C_π ∧
      (∀ (d : IsRestricted.subring (R := K) c) (u : restrictedCoeffSubmodule r E),
        π ⟨restrictedExpandAlgebraMap (K' := K') q hq hr d * u.1,
          mul_mem_restrictedCoeffSubmodule hq hr d u.2⟩ = d * π u) ∧
      (∀ u : restrictedCoeffSubmodule r E, ‖π u‖ ≤ C_π * ‖u.1‖) ∧
      π u₀ ≠ 0 := by
  obtain ⟨ν, hν, hν_norm⟩ := exists_norm_restrictedExpandComponent_mul_prod_eq hq hr u₀.1
  have hcomp_ne : restrictedExpandComponent hq hr ν u₀.1 ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero, zero_mul] at hν_norm
    exact hu₀_ne (norm_eq_zero.mp hν_norm.symm)
  obtain ⟨μ, hμ_ne⟩ :
      ∃ μ, coeff μ (restrictedExpandComponent hq hr ν u₀.1 : _root_.MvPowerSeries σ K') ≠ 0 := by
    by_contra! hall
    exact hcomp_ne (Subtype.ext (MvPowerSeries.ext fun μ ↦ by
      rw [ZeroMemClass.coe_zero, map_zero]; exact hall μ))
  have hx_ne : (⟨coeff (q • μ + ν) (u₀.1 : _root_.MvPowerSeries σ K'), u₀.2 _⟩ : E) ≠ 0 := by
    refine Subtype.coe_ne_coe.mp ?_
    change coeff (q • μ + ν) (u₀.1 : _root_.MvPowerSeries σ K') ≠ 0
    rwa [← coeff_restrictedExpandComponent hq hr ν μ u₀.1]
  obtain ⟨f, C, hC, hf, hf_ne⟩ := hsep hx_ne
  refine ⟨restrictedExpandComponentDual hq hr E ν f hf, C / ν.prod (r · ^ ·),
    div_nonneg hC (prod_pow_pos ν).le,
    restrictedExpandComponentDual_mul hq hr hν f hf,
    norm_restrictedExpandComponentDual_le hq hr ν f hC hf, fun h0 ↦ hf_ne ?_⟩
  have hcoeff := congrArg (fun t : IsRestricted.subring (R := K) c ↦
    coeff μ (t : _root_.MvPowerSeries σ K)) h0
  simpa only [coeff_restrictedExpandComponentDual, ZeroMemClass.coe_zero, map_zero] using hcoeff

end ComponentDual

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
    ⟨rootG j, fun α ↦ Submodule.subset_span ⟨(j, α), rfl⟩⟩
  let linComb (a : Fin m → T) : restrictedCoeffSubmodule r E :=
    ∑ j, ⟨Ψ (a j) * rootG j, mul_mem_restrictedCoeffSubmodule hq hr (a j) (rootGSub j).2⟩
  have hlin (a : Fin m → T) : (linComb a).1 = ∑ j, Ψ (a j) * rootG j := by simp [linComb]
  have hmul_eq (z : M) (s : nonZeroDivisors T) (a : Fin m → T)
      (ha : ∀ j, algebraMap T F (a j) = (s : T) • b.repr z j) :
      algebraMap T' F' (linComb a).1 = algebraMap T' F' (Ψ (s : T)) * ι z := by
    rw [hlin]
    exact b.algebraMap_sum_mul_eq_mul Ψ.toRingHom rootG ι hι_alg hι_b z (s : T) a ha
  -- Clear denominators of `b.repr x₀` and pick a separating bounded map `π` into `T`.
  obtain ⟨s₀, hs₀⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T) (b.repr x₀)
  choose a₀ ha₀ using hs₀
  have hu₀_ne : (linComb a₀).1 ≠ 0 := fun h0 ↦ by
    have hs₀_ne : algebraMap T' F' (Ψ (s₀ : T)) ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_algebraMap_gaussFractionField, norm_restrictedExpandAlgebraMap,
        norm_ne_zero_iff]
      exact nonZeroDivisors.ne_zero s₀.2
    have hmul : algebraMap T' F' (Ψ (s₀ : T)) * ι x₀ = 0 := by
      rw [← hmul_eq x₀ s₀ a₀ ha₀, h0, map_zero]
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
    have hu_norm : ‖(linComb a).1‖ = ‖(s : T)‖ * spectralNorm F M y := by
      rw [← norm_algebraMap_gaussFractionField σ K' r _, hmul_eq y s a ha, norm_mul,
        norm_algebraMap_gaussFractionField σ K' r _, norm_restrictedExpandAlgebraMap, hι_norm]
    have hs_pos : 0 < ‖(s : T)‖ := by
      rw [← norm_algebraMap_gaussFractionField σ K c (s : T), norm_pos_iff]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    refine le_of_mul_le_mul_left ?_ hs_pos
    calc ‖(s : T)‖ * ‖φ y‖
        = ‖algebraMap T F (s : T) * φ y‖ := by
          rw [norm_mul, norm_algebraMap_gaussFractionField σ K c _]
      _ = ‖∑ j, a j * g j‖ := by
          rw [b.algebraMap_mul_constr_eq_algebraMap_sum g y (s : T) a ha,
            norm_algebraMap_gaussFractionField σ K c _]
      _ ≤ C_π * ‖(linComb a).1‖ := by rw [hπ_lin]; exact hπ_norm (linComb a)
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
    have hmul_T' : Ψ (s : T) * ry = (linComb a).1 := IsFractionRing.injective T' F' <| by
      rw [hmul_eq y s a ha, map_mul, ← hι_y]
    have hry_mem : ry ∈ restrictedCoeffSubmodule r E :=
      mem_restrictedCoeffSubmodule_of_mul_mem hq hr (nonZeroDivisors.ne_zero s.2)
        (hmul_T'.symm ▸ (linComb a).2)
    have hπ_eq : (s : T) * π ⟨ry, hry_mem⟩ = ∑ j, a j * g j := by
      rw [hπ_lin, ← hπ_mul (s : T) ⟨ry, hry_mem⟩]
      exact congrArg π (Subtype.ext hmul_T')
    refine ⟨π ⟨ry, hry_mem⟩,
      mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2) ?_⟩
    rw [← map_mul, hπ_eq]
    exact (b.algebraMap_mul_constr_eq_algebraMap_sum g y (s : T) a ha).symm
  · refine hπ_ne (IsFractionRing.injective T F ?_)
    dsimp only [φ] at hφ0
    rw [← hπ_lin, map_zero, ← b.algebraMap_mul_constr_eq_algebraMap_sum g x₀ (s₀ : T) a₀ ha₀,
      hφ0, mul_zero]

end SeparatingDual

end TauCeti.MvPowerSeries
