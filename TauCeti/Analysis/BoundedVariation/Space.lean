/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# The Banach space of functions of bounded variation

`TauCeti.MemBV μ Ω u` means that `u` is integrable on `Ω` and its variational total
variation is finite. `TauCeti.BV μ Ω` is the corresponding space of almost-everywhere
classes, with norm `‖u‖₁ + |Du|(Ω)`. It is built from Mathlib's `L¹` space, so equality
is equality almost everywhere on the domain, rather than equality of representatives.

The BV norm is complete, and the inclusion into `L¹` is a continuous injective linear map.
The domain and measure are parameters; total variation is defined by duality relative to
this measure. For additive Haar measures this is the classical distributional variation.
In particular the construction applies to Lebesgue measure on any open subset of a
finite-dimensional real inner product space.

## References

L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
Problems*, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Opens E}

/-- A function is globally of bounded variation on `Ω` when it is integrable there and
has finite variational total variation. -/
def MemBV (μ : Measure E) (Ω : Opens E) (u : E → ℝ) : Prop :=
  IntegrableOn u Ω μ ∧ totalVariationOn μ Ω u < ∞

/-- The integrability and finite-variation characterization of BV membership. -/
theorem memBV_iff {u : E → ℝ} : MemBV μ Ω u ↔
    IntegrableOn u Ω μ ∧ totalVariationOn μ Ω u < ∞ := (Iff.rfl)

/-- BV membership is unchanged by equality almost everywhere on the domain. -/
theorem memBV_congr_ae {u v : E → ℝ} (h : u =ᵐ[μ.restrict Ω] v) :
    MemBV μ Ω u ↔ MemBV μ Ω v := by
  rw [memBV_iff, memBV_iff, totalVariationOn_congr_ae h]
  exact and_congr (integrable_congr h) Iff.rfl

/-- The zero function belongs to BV. -/
@[simp]
theorem MemBV.zero : MemBV μ Ω 0 :=
  memBV_iff.mpr ⟨integrableOn_zero, by simp⟩

/-- Negation preserves BV membership. -/
theorem MemBV.neg {u : E → ℝ} (hu : MemBV μ Ω u) : MemBV μ Ω (-u) := by
  rcases memBV_iff.mp hu with ⟨hu, hfinite⟩
  exact memBV_iff.mpr ⟨hu.neg, by simpa using hfinite⟩

/-- BV membership is unchanged by negation. -/
@[simp]
theorem memBV_neg_iff {u : E → ℝ} : MemBV μ Ω (-u) ↔ MemBV μ Ω u :=
  ⟨fun hu => by simpa using hu.neg, MemBV.neg⟩

/-- Multiplication by a real scalar preserves BV membership. -/
theorem MemBV.smul {u : E → ℝ} (hu : MemBV μ Ω u) (c : ℝ) : MemBV μ Ω (c • u) := by
  rcases memBV_iff.mp hu with ⟨hu, hfinite⟩
  refine memBV_iff.mpr ⟨hu.smul c, ?_⟩
  rw [totalVariationOn_smul]
  exact ENNReal.mul_lt_top (by finiteness) hfinite

/-- The sum of two BV functions belongs to BV. -/
theorem MemBV.add [OpensMeasurableSpace E] {u v : E → ℝ}
    (hu : MemBV μ Ω u) (hv : MemBV μ Ω v) : MemBV μ Ω (u + v) := by
  rcases memBV_iff.mp hu with ⟨hu, hufinite⟩
  rcases memBV_iff.mp hv with ⟨hv, hvfinite⟩
  exact memBV_iff.mpr ⟨hu.add hv,
    (totalVariationOn_add_le hu.locallyIntegrableOn hv.locallyIntegrableOn).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hufinite, hvfinite⟩)⟩

/-- The difference of two BV functions belongs to BV. -/
theorem MemBV.sub [OpensMeasurableSpace E] {u v : E → ℝ}
    (hu : MemBV μ Ω u) (hv : MemBV μ Ω v) : MemBV μ Ω (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

variable [OpensMeasurableSpace E]

/-- The submodule of `L¹(Ω)` consisting of classes of finite total variation. Its inherited
`L¹` norm is distinct from the BV norm on `BV μ Ω`. -/
def bvSubmodule (μ : Measure E) (Ω : Opens E) : Submodule ℝ (E →₁[μ.restrict Ω] ℝ) where
  carrier := {u | totalVariationOn μ Ω u < ∞}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [totalVariationOn_congr_ae (Lp.coeFn_zero ℝ 1 (μ.restrict Ω)), totalVariationOn_zero]
    exact ENNReal.zero_lt_top
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    rw [totalVariationOn_congr_ae (Lp.coeFn_add u v)]
    exact (totalVariationOn_add_le (IntegrableOn.locallyIntegrableOn (L1.integrable_coeFn u))
      (IntegrableOn.locallyIntegrableOn (L1.integrable_coeFn v))).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hu, hv⟩)
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [totalVariationOn_congr_ae (Lp.coeFn_smul c u), totalVariationOn_smul]
    exact ENNReal.mul_lt_top (by finiteness) hu

/-- Almost-everywhere classes of integrable functions with finite total variation on `Ω`.
The wrapper gives this space its BV norm, independently of the weaker inherited `L¹` norm. -/
structure BV (μ : Measure E) (Ω : Opens E) where
  /-- The underlying finite-variation `L¹` class. -/
  toSubmodule : bvSubmodule μ Ω

/-- Membership in the finite-variation submodule is finiteness of total variation. -/
@[simp]
theorem mem_bvSubmodule_iff (u : E →₁[μ.restrict Ω] ℝ) :
    u ∈ bvSubmodule μ Ω ↔ totalVariationOn μ Ω u < ∞ := (Iff.rfl)

namespace BV

/-- The underlying `L¹` class of a BV function. -/
def toL1 (u : BV μ Ω) : E →₁[μ.restrict Ω] ℝ := u.toSubmodule.1

instance : CoeFun (BV μ Ω) (fun _ => E → ℝ) := ⟨fun u => u.toL1⟩

/-- BV classes are determined by their `L¹` classes. -/
theorem toL1_injective : Function.Injective (toL1 : BV μ Ω → E →₁[μ.restrict Ω] ℝ) := by
  rintro ⟨u⟩ ⟨v⟩ h
  congr 1
  exact Subtype.ext h

/-- Equality of BV classes is equality almost everywhere on `Ω`. -/
@[ext]
theorem ext {u v : BV μ Ω} (h : (u : E → ℝ) =ᵐ[μ.restrict Ω] v) : u = v :=
  toL1_injective (Lp.ext h)

/-- Every representative selected from a BV class is integrable on its domain. -/
theorem integrableOn (u : BV μ Ω) : IntegrableOn (u : E → ℝ) Ω μ :=
  L1.integrable_coeFn u.toL1

/-- Every BV class has finite total variation. -/
theorem totalVariationOn_lt_top (u : BV μ Ω) : totalVariationOn μ Ω u < ∞ :=
  u.toSubmodule.2

/-- The selected representative of a BV class belongs to the unbundled BV predicate. -/
theorem memBV (u : BV μ Ω) : MemBV μ Ω u :=
  memBV_iff.mpr ⟨u.integrableOn, u.totalVariationOn_lt_top⟩

/-- Form the almost-everywhere class of an integrable function of finite variation. -/
def ofFunction (u : E → ℝ) (hu : MemBV μ Ω u) : BV μ Ω :=
  BV.mk ⟨(memBV_iff.mp hu).1.toL1 u, (mem_bvSubmodule_iff _).mpr <| by
    rw [totalVariationOn_congr_ae (memBV_iff.mp hu).1.coeFn_toL1]
    exact (memBV_iff.mp hu).2⟩

/-- The `L¹` class of the BV class constructed from a function. -/
@[simp]
theorem toL1_ofFunction (u : E → ℝ) (hu : MemBV μ Ω u) :
    (ofFunction u hu).toL1 = (memBV_iff.mp hu).1.toL1 u := (rfl)

/-- Forming a BV class preserves the function almost everywhere on `Ω`. -/
theorem coeFn_ofFunction (u : E → ℝ) (hu : MemBV μ Ω u) :
    (ofFunction u hu : E → ℝ) =ᵐ[μ.restrict Ω] u :=
  (memBV_iff.mp hu).1.coeFn_toL1

/-- Construction of a BV class preserves its total variation. -/
theorem totalVariationOn_ofFunction (u : E → ℝ) (hu : MemBV μ Ω u) :
    totalVariationOn μ Ω (ofFunction u hu) = totalVariationOn μ Ω u :=
  totalVariationOn_congr_ae (coeFn_ofFunction u hu)

/-- Reconstructing a BV class from its representative gives the original class. -/
@[simp]
theorem ofFunction_coeFn (u : BV μ Ω) : ofFunction u u.memBV = u :=
  ext (coeFn_ofFunction u u.memBV)

instance : Zero (BV μ Ω) := ⟨BV.mk 0⟩
instance : Add (BV μ Ω) := ⟨fun u v => BV.mk (u.toSubmodule + v.toSubmodule)⟩
instance : Neg (BV μ Ω) := ⟨fun u => BV.mk (-u.toSubmodule)⟩
instance : Sub (BV μ Ω) := ⟨fun u v => BV.mk (u.toSubmodule - v.toSubmodule)⟩
instance : SMul ℝ (BV μ Ω) := ⟨fun c u => BV.mk (c • u.toSubmodule)⟩
instance : SMul ℕ (BV μ Ω) := ⟨fun c u => BV.mk (c • u.toSubmodule)⟩
instance : SMul ℤ (BV μ Ω) := ⟨fun c u => BV.mk (c • u.toSubmodule)⟩

@[simp] theorem toL1_zero : (0 : BV μ Ω).toL1 = 0 := (rfl)
@[simp] theorem toL1_add (u v : BV μ Ω) : (u + v).toL1 = u.toL1 + v.toL1 := (rfl)
@[simp] theorem toL1_neg (u : BV μ Ω) : (-u).toL1 = -u.toL1 := (rfl)
@[simp] theorem toL1_sub (u v : BV μ Ω) : (u - v).toL1 = u.toL1 - v.toL1 := (rfl)
@[simp] theorem toL1_smul (c : ℝ) (u : BV μ Ω) : (c • u).toL1 = c • u.toL1 := (rfl)
@[simp] theorem toL1_nsmul (c : ℕ) (u : BV μ Ω) : (c • u).toL1 = c • u.toL1 := (rfl)
@[simp] theorem toL1_zsmul (c : ℤ) (u : BV μ Ω) : (c • u).toL1 = c • u.toL1 := (rfl)

instance : AddCommGroup (BV μ Ω) :=
  Function.Injective.addCommGroup toL1 toL1_injective toL1_zero toL1_add toL1_neg toL1_sub
    (fun u n => toL1_nsmul n u) (fun u n => toL1_zsmul n u)

instance : Module ℝ (BV μ Ω) :=
  Function.Injective.module ℝ
    ({ toFun := toL1, map_zero' := toL1_zero, map_add' := toL1_add } :
      BV μ Ω →+ (E →₁[μ.restrict Ω] ℝ)) toL1_injective toL1_smul

/-- The zero BV class is represented by zero almost everywhere. -/
theorem coeFn_zero : (0 : BV μ Ω) =ᵐ[μ.restrict Ω] (0 : E → ℝ) :=
  Lp.coeFn_zero ℝ 1 (μ.restrict Ω)

/-- Negation of a BV class negates its representative almost everywhere. -/
theorem coeFn_neg (u : BV μ Ω) : (-u : BV μ Ω) =ᵐ[μ.restrict Ω] -(u : E → ℝ) :=
  Lp.coeFn_neg u.toL1

/-- Subtraction of BV classes subtracts their representatives almost everywhere. -/
theorem coeFn_sub (u v : BV μ Ω) : (u - v : BV μ Ω) =ᵐ[μ.restrict Ω]
    (u : E → ℝ) - v := Lp.coeFn_sub u.toL1 v.toL1

/-- The representative of a sum is almost everywhere the sum of the representatives. -/
theorem coeFn_add (u v : BV μ Ω) : (u + v : BV μ Ω) =ᵐ[μ.restrict Ω]
    (u : E → ℝ) + v := Lp.coeFn_add u.toL1 v.toL1

/-- The representative of a scalar multiple is almost everywhere the scaled representative. -/
theorem coeFn_smul (c : ℝ) (u : BV μ Ω) : (c • u : BV μ Ω) =ᵐ[μ.restrict Ω]
    c • (u : E → ℝ) := Lp.coeFn_smul c u.toL1

/-- The BV norm is the sum of the `L¹` norm and the real-valued total variation. -/
instance instNorm : Norm (BV μ Ω) where
  norm u := ‖u.toL1‖ + (totalVariationOn μ Ω u).toReal

/-- The characteristic formula for the BV norm. -/
theorem norm_def (u : BV μ Ω) :
    ‖u‖ = ‖u.toL1‖ + (totalVariationOn μ Ω u).toReal := (rfl)

private theorem norm_smul_eq (c : ℝ) (u : BV μ Ω) : ‖c • u‖ = ‖c‖ * ‖u‖ := by
  rw [norm_def, norm_def, toL1_smul,
    totalVariationOn_congr_ae (Lp.coeFn_smul c u.toL1), totalVariationOn_smul]
  simp [norm_smul, ENNReal.toReal_mul, mul_add]

/-- The `L¹`-plus-variation norm makes BV a normed additive commutative group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (BV μ Ω) :=
  let core : NormedSpace.Core ℝ (BV μ Ω) := {
    norm_nonneg u := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    norm_smul c u := by exact norm_smul_eq c u
    norm_triangle u v := by
      rw [norm_def, norm_def, norm_def, toL1_add,
        totalVariationOn_congr_ae (Lp.coeFn_add u.toL1 v.toL1)]
      have ht := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨u.totalVariationOn_lt_top.ne, v.totalVariationOn_lt_top.ne⟩)
        (totalVariationOn_add_le u.integrableOn.locallyIntegrableOn
          v.integrableOn.locallyIntegrableOn)
      rw [ENNReal.toReal_add u.totalVariationOn_lt_top.ne v.totalVariationOn_lt_top.ne] at ht
      linarith [norm_add_le u.toL1 v.toL1]
    norm_eq_zero_iff u := by
      constructor
      · intro h
        apply toL1_injective
        rw [toL1_zero]
        exact norm_eq_zero.mp (by
          have := ENNReal.toReal_nonneg (a := totalVariationOn μ Ω u)
          rw [norm_def] at h
          linarith [norm_nonneg u.toL1])
      · rintro rfl
        rw [norm_def, toL1_zero,
          totalVariationOn_congr_ae (Lp.coeFn_zero ℝ 1 (μ.restrict Ω))]
        simp }
  NormedAddCommGroup.ofCore core

/-- BV is a normed real vector space for its `L¹`-plus-variation norm. -/
instance instNormedSpace : NormedSpace ℝ (BV μ Ω) where
  norm_smul_le c u := by exact (norm_smul_eq c u).le

/-- The inclusion into `L¹` decreases the norm. -/
theorem norm_toL1_le (u : BV μ Ω) : ‖u.toL1‖ ≤ ‖u‖ := by
  rw [norm_def]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-- Forgetting finite variation gives a continuous linear inclusion into `L¹(Ω)`. -/
def toL1CLM : BV μ Ω →L[ℝ] (E →₁[μ.restrict Ω] ℝ) :=
  ({ toFun := toL1, map_add' := toL1_add, map_smul' := toL1_smul } :
    BV μ Ω →ₗ[ℝ] (E →₁[μ.restrict Ω] ℝ)).mkContinuous 1 (by
      intro u
      simpa using norm_toL1_le u)

@[simp]
theorem toL1CLM_apply (u : BV μ Ω) : toL1CLM u = u.toL1 := (rfl)

/-- The continuous linear inclusion into `L¹` is injective. -/
theorem toL1CLM_injective : Function.Injective (toL1CLM : BV μ Ω →L[ℝ] _) :=
  toL1_injective

private theorem variation_sub_limit_le {u : ℕ → BV μ Ω} {v : E →₁[μ.restrict Ω] ℝ}
    (hv : Tendsto (fun n => (u n).toL1) atTop (𝓝 v)) (N M : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n ≥ N, ‖u n - u M‖ ≤ C) :
    totalVariationOn μ Ω (v - (u M).toL1 : E →₁[μ.restrict Ω] ℝ) ≤ ENNReal.ofReal C := by
  apply totalVariationOn_le_of_tendsto_L1 (hv.sub tendsto_const_nhds)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← toL1_sub]
  apply (ENNReal.le_ofReal_iff_toReal_le (u n - u M).totalVariationOn_lt_top.ne hC).mpr
  exact (le_add_of_nonneg_left (norm_nonneg (u n - u M).toL1)).trans (hbound n hn)

/-- The BV norm is complete: every Cauchy sequence for the sum of the `L¹` norm and total
variation converges in that norm. -/
instance instCompleteSpace : CompleteSpace (BV μ Ω) :=
  Metric.complete_of_cauchySeq_tendsto fun u hu => by
    have huL1 : CauchySeq (fun n => (u n).toL1) :=
      (toL1CLM (μ := μ) (Ω := Ω)).uniformContinuous.comp_cauchySeq hu
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete huL1
    obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp hu 1 zero_lt_one
    have hvar : totalVariationOn μ Ω (v - (u N₀).toL1 : E →₁[μ.restrict Ω] ℝ) < ∞ :=
      (variation_sub_limit_le hv N₀ N₀ zero_le_one fun n hn => by
        simpa only [dist_eq_norm] using (hN₀ n hn N₀ le_rfl).le).trans_lt (by finiteness)
    have hvBV : MemBV μ Ω v := by
      apply memBV_iff.mpr
      refine ⟨L1.integrable_coeFn v, ?_⟩
      have hsum := totalVariationOn_add_le
        (IntegrableOn.locallyIntegrableOn (L1.integrable_coeFn (v - (u N₀).toL1)))
        (u N₀).integrableOn.locallyIntegrableOn
      have hae : ((v - (u N₀).toL1 : E →₁[μ.restrict Ω] ℝ) : E → ℝ) + u N₀
          =ᵐ[μ.restrict Ω] v := by
        filter_upwards [Lp.coeFn_sub v (u N₀).toL1] with x hx
        simp only [Pi.add_apply, hx, Pi.sub_apply, sub_add_cancel]
      rw [totalVariationOn_congr_ae hae] at hsum
      exact hsum.trans_lt (ENNReal.add_lt_top.mpr ⟨hvar, (u N₀).totalVariationOn_lt_top⟩)
    let f := ofFunction v hvBV
    have hf : f.toL1 = v := by
      exact Integrable.toL1_coeFn v (L1.integrable_coeFn v)
    refine ⟨f, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 4) (by positivity)
    have hsmall (n : ℕ) (hn : N ≤ n) : ‖f - u n‖ ≤ ε / 2 := by
      have hbound : ∀ m ≥ N, ‖u m - u n‖ ≤ ε / 4 := fun m hm => by
        simpa only [dist_eq_norm] using (hN m hm n hn).le
      have hvar' := variation_sub_limit_le hv N n (by positivity : 0 ≤ ε / 4) hbound
      have hL1 : ‖v - (u n).toL1‖ ≤ ε / 4 := by
        apply le_of_tendsto ((hv.sub tendsto_const_nhds).norm)
        filter_upwards [eventually_ge_atTop N] with m hm
        rw [← toL1_sub]
        exact (norm_toL1_le _).trans (hbound m hm)
      have hvarto := ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ ε / 4) hvar'
      rw [norm_def, toL1_sub, hf]
      linarith
    exact ⟨N, fun n hn => by
      rw [dist_comm, dist_eq_norm]
      exact (hsmall n hn).trans_lt (by linarith)⟩

end BV

end TauCeti
