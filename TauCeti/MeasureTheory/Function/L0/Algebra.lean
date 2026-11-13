/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.MeasureTheory.Function.L0.Convergence
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Topology.Sequences

/-!
# The topological real algebra of random variables

Real random variables form a commutative real algebra, with operations inherited from their
native almost-everywhere classes. On finite measure spaces the bounded integral metric is
translation invariant, subtraction is uniformly continuous, and multiplication and real scalar
multiplication are continuous without boundedness or integrability assumptions.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace TauCeti.L0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The commutative ring of real almost-everywhere classes, transported to `L0`. -/
instance instCommRing : CommRing (L0 μ) := by
  -- The native quotient has these operations but no ring instance at the pinned revision.
  -- Its injective germ map assembles them locally, without changing native instances.
  letI : CommRing (Ω →ₘ[μ] ℝ) := by
    letI : NatCast (Ω →ₘ[μ] ℝ) := ⟨fun n ↦ n • (1 : Ω →ₘ[μ] ℝ)⟩
    letI : IntCast (Ω →ₘ[μ] ℝ) := ⟨fun n ↦ n • (1 : Ω →ₘ[μ] ℝ)⟩
    apply AEEqFun.toGerm_injective.commRing AEEqFun.toGerm
      AEEqFun.zero_toGerm AEEqFun.one_toGerm AEEqFun.add_toGerm AEEqFun.mul_toGerm
      AEEqFun.neg_toGerm AEEqFun.sub_toGerm
      (fun _ _ ↦ AEEqFun.smul_toGerm _ _) (fun _ _ ↦ AEEqFun.smul_toGerm _ _)
      AEEqFun.pow_toGerm
    · intro n
      -- The locally chosen cast is scalar multiplication of the native unit.
      change (n • (1 : Ω →ₘ[μ] ℝ)).toGerm = n
      simp [AEEqFun.smul_toGerm]
    · intro n
      -- The locally chosen cast is scalar multiplication of the native unit.
      change (n • (1 : Ω →ₘ[μ] ℝ)).toGerm = n
      simp [AEEqFun.smul_toGerm]
  exact equivAEEqFun.commRing

/-- The real module of almost-everywhere classes, transported to `L0`. -/
instance instModule : Module ℝ (L0 μ) := equivAEEqFun.addEquiv.module ℝ

/-- The zero class in `L0` is the native zero class. -/
@[simp]
theorem toAEEqFun_zero : (0 : L0 μ).toAEEqFun = 0 := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_zero

/-- The unit class in `L0` is the native unit class. -/
@[simp]
theorem toAEEqFun_one : (1 : L0 μ).toAEEqFun = 1 := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).mulEquiv.map_one

/-- Addition on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_add (f g : L0 μ) : (f + g).toAEEqFun = f.toAEEqFun + g.toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_add f g

/-- Negation on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_neg (f : L0 μ) : (-f).toAEEqFun = -f.toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_neg f

/-- Subtraction on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_sub (f g : L0 μ) : (f - g).toAEEqFun = f.toAEEqFun - g.toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_sub f g

/-- Multiplication on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_mul (f g : L0 μ) : (f * g).toAEEqFun = f.toAEEqFun * g.toAEEqFun := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).mulEquiv.map_mul f g

/-- Forgetting the wrapper preserves finite sums. -/
@[simp]
theorem toAEEqFun_sum {ι : Type*} (s : Finset ι) (f : ι → L0 μ) :
    (∑ i ∈ s, f i).toAEEqFun = ∑ i ∈ s, (f i).toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    map_sum (equivAEEqFun (μ := μ)).addEquiv f s

/-- Forgetting the wrapper preserves finite products. -/
@[simp]
theorem toAEEqFun_prod {ι : Type*} (s : Finset ι) (f : ι → L0 μ) :
    (∏ i ∈ s, f i).toAEEqFun = ∏ i ∈ s, (f i).toAEEqFun := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    map_prod (equivAEEqFun (μ := μ)).mulEquiv f s

/-- Natural powers on `L0` are inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_pow (f : L0 μ) (n : ℕ) :
    (f ^ n).toAEEqFun = f.toAEEqFun ^ n := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    map_pow (equivAEEqFun (μ := μ)).mulEquiv f n

/-- Real scalar multiplication on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_smul (c : ℝ) (f : L0 μ) :
    (c • f).toAEEqFun = c • f.toAEEqFun := by
  simpa only [AddEquiv.linearEquiv_apply, Equiv.addEquiv_apply, equivAEEqFun_apply] using
    ((equivAEEqFun (μ := μ)).addEquiv.linearEquiv ℝ).map_smul c f

/-- The real algebra structure agrees with the transported module structure. -/
instance instAlgebra : Algebra ℝ (L0 μ) :=
  Algebra.ofModule
    (fun c f g ↦ equivAEEqFun.injective (by
      simp only [equivAEEqFun_apply, toAEEqFun_mul, toAEEqFun_smul]
      exact AEEqFun.induction_on₂ f.toAEEqFun g.toAEEqFun fun f hf g hg ↦ by
        simp only [AEEqFun.smul_mk, AEEqFun.mk_mul_mk, smul_mul_assoc]))
    (fun c f g ↦ equivAEEqFun.injective (by
      simp only [equivAEEqFun_apply, toAEEqFun_mul, toAEEqFun_smul]
      exact AEEqFun.induction_on₂ f.toAEEqFun g.toAEEqFun fun f hf g hg ↦ by
        simp only [AEEqFun.smul_mk, AEEqFun.mk_mul_mk, mul_smul_comm]))

/-- Real constants are the native constant almost-everywhere classes. -/
@[simp]
theorem toAEEqFun_algebraMap (c : ℝ) :
    (algebraMap ℝ (L0 μ) c).toAEEqFun = AEEqFun.const Ω c := by
  simp only [Algebra.algebraMap_eq_smul_one, toAEEqFun_smul, toAEEqFun_one,
    AEEqFun.one_def, AEEqFun.smul_mk, AEEqFun.const, AEEqFun.mk_eq_mk]
  filter_upwards with x
  simp

/-- The representative of a real constant agrees almost everywhere with that constant. -/
theorem coeFn_algebraMap (c : ℝ) :
    ((algebraMap ℝ (L0 μ) c) : Ω → ℝ) =ᵐ[μ] Function.const Ω c := by
  simpa only [← toAEEqFun_algebraMap] using (AEEqFun.coeFn_const Ω c (μ := μ))

/-- Natural-number constants have the corresponding constant representatives almost everywhere. -/
theorem coeFn_natCast (n : ℕ) :
    ((n : L0 μ) : Ω → ℝ) =ᵐ[μ] Function.const Ω (n : ℝ) := by
  simpa only [map_natCast] using (coeFn_algebraMap (μ := μ) (n : ℝ))

/-- Integer constants have the corresponding constant representatives almost everywhere. -/
theorem coeFn_intCast (n : ℤ) :
    ((n : L0 μ) : Ω → ℝ) =ᵐ[μ] Function.const Ω (n : ℝ) := by
  simpa only [map_intCast] using (coeFn_algebraMap (μ := μ) (n : ℝ))

/-- The representative of zero vanishes almost everywhere. -/
theorem coeFn_zero : ((0 : L0 μ) : Ω → ℝ) =ᵐ[μ] 0 := by
  simpa only [← toAEEqFun_zero] using (AEEqFun.coeFn_zero (α := Ω) (β := ℝ) (μ := μ))

/-- The representative of one equals one almost everywhere. -/
theorem coeFn_one : ((1 : L0 μ) : Ω → ℝ) =ᵐ[μ] 1 := by
  simpa only [← toAEEqFun_one] using (AEEqFun.coeFn_one (α := Ω) (β := ℝ) (μ := μ))

/-- Representatives of a negative agree almost everywhere with the pointwise negative. -/
theorem coeFn_neg (f : L0 μ) : ((-f : L0 μ) : Ω → ℝ) =ᵐ[μ] -f := by
  simpa only [← toAEEqFun_neg] using (AEEqFun.coeFn_neg f.toAEEqFun)

/-- Representatives of a difference agree almost everywhere with the pointwise difference. -/
theorem coeFn_sub (f g : L0 μ) : ((f - g : L0 μ) : Ω → ℝ) =ᵐ[μ] f - g := by
  simpa only [← toAEEqFun_sub] using (AEEqFun.coeFn_sub f.toAEEqFun g.toAEEqFun)

/-- Representatives of a power agree almost everywhere with the pointwise power. -/
theorem coeFn_pow (f : L0 μ) (n : ℕ) : ((f ^ n : L0 μ) : Ω → ℝ) =ᵐ[μ] f ^ n := by
  simpa only [← toAEEqFun_pow] using (AEEqFun.coeFn_pow f.toAEEqFun n)

/-- Representatives of a sum agree almost everywhere with the pointwise sum. -/
theorem coeFn_add (f g : L0 μ) : ((f + g : L0 μ) : Ω → ℝ) =ᵐ[μ] f + g := by
  filter_upwards [AEEqFun.coeFn_add f.toAEEqFun g.toAEEqFun] with x hx
  simpa only [toAEEqFun_add, Pi.add_apply] using hx

/-- Representatives of a product agree almost everywhere with the pointwise product. -/
theorem coeFn_mul (f g : L0 μ) : ((f * g : L0 μ) : Ω → ℝ) =ᵐ[μ] f * g := by
  filter_upwards [AEEqFun.coeFn_mul f.toAEEqFun g.toAEEqFun] with x hx
  simpa only [toAEEqFun_mul, Pi.mul_apply] using hx

/-- Representatives of a scalar multiple agree almost everywhere with the pointwise multiple. -/
theorem coeFn_smul (c : ℝ) (f : L0 μ) : ((c • f : L0 μ) : Ω → ℝ) =ᵐ[μ] c • (f : Ω → ℝ) := by
  filter_upwards [AEEqFun.coeFn_smul c f.toAEEqFun] with x hx
  simpa only [toAEEqFun_smul, Pi.smul_apply, smul_eq_mul] using hx

/-- A finite sum has the pointwise sum as its representative almost everywhere. -/
theorem coeFn_finsetSum {ι : Type*} (s : Finset ι) (f : ι → L0 μ) :
    ((∑ i ∈ s, f i : L0 μ) : Ω → ℝ) =ᵐ[μ] ∑ i ∈ s, (f i : Ω → ℝ) := by
  simpa only [← toAEEqFun_sum] using
    (AEEqFun.coeFn_finsetSum s (fun i ↦ (f i).toAEEqFun))

/-- A finite product has the pointwise product as its representative almost everywhere. -/
theorem coeFn_finsetProd {ι : Type*} (s : Finset ι) (f : ι → L0 μ) :
    ((∏ i ∈ s, f i : L0 μ) : Ω → ℝ) =ᵐ[μ] ∏ i ∈ s, (f i : Ω → ℝ) := by
  simpa only [← toAEEqFun_prod] using
    (AEEqFun.coeFn_finsetProd s (fun i ↦ (f i).toAEEqFun))

/-- Constructing a constant function gives the algebra's corresponding real constant. -/
@[simp]
theorem ofFun_const (c : ℝ) :
    ofFun (fun _ : Ω ↦ c) aestronglyMeasurable_const = algebraMap ℝ (L0 μ) c := by
  apply ext
  exact (coeFn_ofFun _ _).trans (coeFn_algebraMap c).symm

/-- Constructing a sum agrees with adding the constructed random variables. -/
@[simp]
theorem ofFun_add_ofFun (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ofFun f hf + ofFun g hg = ofFun (f + g) (hf.add hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_add, toAEEqFun_ofFun] using
    AEEqFun.mk_add_mk f g hf hg

/-- Constructing a product agrees with multiplying the constructed random variables. -/
@[simp]
theorem ofFun_mul_ofFun (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ofFun f hf * ofFun g hg = ofFun (f * g) (hf.mul hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_mul, toAEEqFun_ofFun] using
    AEEqFun.mk_mul_mk f g hf hg

/-- Constructing a scalar multiple agrees with scalar multiplication of a random variable. -/
@[simp]
theorem smul_ofFun (c : ℝ) (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    c • ofFun f hf = ofFun (c • f) (hf.const_smul c) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_smul, toAEEqFun_ofFun] using
    AEEqFun.smul_mk c f hf

/-- Constructing the zero function gives the zero random variable. -/
@[simp]
theorem ofFun_zero : ofFun (0 : Ω → ℝ) aestronglyMeasurable_const = (0 : L0 μ) := by
  apply equivAEEqFun.injective
  rw [equivAEEqFun_apply, equivAEEqFun_apply, toAEEqFun_zero]
  exact (toAEEqFun_ofFun _ _).trans AEEqFun.zero_def.symm

/-- Constructing the unit function gives the unit random variable. -/
@[simp]
theorem ofFun_one : ofFun (1 : Ω → ℝ) aestronglyMeasurable_const = (1 : L0 μ) := by
  apply equivAEEqFun.injective
  rw [equivAEEqFun_apply, equivAEEqFun_apply, toAEEqFun_one]
  exact (toAEEqFun_ofFun _ _).trans AEEqFun.one_def.symm

/-- Negation commutes with constructing a random variable. -/
@[simp]
theorem neg_ofFun (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    -ofFun f hf = ofFun (-f) hf.neg := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_neg, toAEEqFun_ofFun] using AEEqFun.neg_mk f hf

/-- Subtraction commutes with constructing random variables. -/
@[simp]
theorem ofFun_sub_ofFun (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ofFun f hf - ofFun g hg = ofFun (f - g) (hf.sub hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_sub, toAEEqFun_ofFun] using
    (AEEqFun.mk_sub f g hf hg).symm

/-- Natural powers commute with constructing a random variable. -/
@[simp]
theorem ofFun_pow (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    ofFun f hf ^ n = ofFun (f ^ n) (hf.pow n) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_pow, toAEEqFun_ofFun] using AEEqFun.mk_pow f hf n

/-- The image of the zero `Lp` function is zero. -/
@[simp]
theorem ofLp_zero {p : ℝ≥0∞} : ofLp (0 : Lp ℝ p μ) = (0 : L0 μ) := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The inclusion of `Lp` preserves addition. -/
@[simp]
theorem ofLp_add {p : ℝ≥0∞} (f g : Lp ℝ p μ) : ofLp (f + g) = ofLp f + ofLp g := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The inclusion of `Lp` preserves finite sums. -/
@[simp]
theorem ofLp_sum {p : ℝ≥0∞} {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ p μ) :
    ofLp (∑ i ∈ s, f i) = ∑ i ∈ s, ofLp (f i) := by
  apply toAEEqFun_injective
  simp

/-- The inclusion of `Lp` preserves negation. -/
@[simp]
theorem ofLp_neg {p : ℝ≥0∞} (f : Lp ℝ p μ) : ofLp (-f) = -ofLp f := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The inclusion of `Lp` preserves subtraction. -/
@[simp]
theorem ofLp_sub {p : ℝ≥0∞} (f g : Lp ℝ p μ) : ofLp (f - g) = ofLp f - ofLp g := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The inclusion of `Lp` preserves real scalar multiplication. -/
@[simp]
theorem ofLp_smul {p : ℝ≥0∞} (c : ℝ) (f : Lp ℝ p μ) : ofLp (c • f) = c • ofLp f := by
  apply ext
  have h := coeFn_smul c (ofLp f)
  simp only [coeFn_ofLp] at h ⊢
  exact (Lp.coeFn_smul c f).trans h.symm

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- Including a constant `Lp` function gives the corresponding real constant. -/
@[simp]
theorem ofLp_const {p : ℝ≥0∞} (c : ℝ) :
    ofLp (Lp.const p μ c) = algebraMap ℝ (L0 μ) c := by
  apply toAEEqFun_injective
  simp only [toAEEqFun_ofLp, Lp.const_val, toAEEqFun_algebraMap]

/-- Translation preserves the bounded integral metric. -/
instance instIsIsometricVAdd : IsIsometricVAdd (L0 μ) (L0 μ) where
  isometry_vadd f := Isometry.of_dist_eq fun g h ↦ by
    -- The canonical additive action is addition; this changes only its notation.
    change dist (f + g) (f + h) = dist g h
    rw [dist_def, dist_def]
    apply integral_congr_ae
    filter_upwards [coeFn_add f g, coeFn_add f h] with x hx hy
    simp only [hx, hy, Pi.add_apply, add_sub_add_left_eq_sub]

/-- Subtraction is uniformly continuous for the bounded integral metric. -/
instance instIsUniformAddGroup : IsUniformAddGroup (L0 μ) where
  uniformContinuous_sub := by
    apply LipschitzWith.uniformContinuous (K := 2)
    apply LipschitzWith.of_dist_le_mul
    intro f g
    calc
      dist (f.1 - f.2) (g.1 - g.2) ≤
          dist (f.1 - f.2) (g.1 - f.2) + dist (g.1 - f.2) (g.1 - g.2) :=
        dist_triangle _ _ _
      _ = dist f.1 g.1 + dist f.2 g.2 := by simp
      _ ≤ 2 * dist f g := by
        rw [Prod.dist_eq]
        have h₁ := le_max_left (dist f.1 g.1) (dist f.2 g.2)
        have h₂ := le_max_right (dist f.1 g.1) (dist f.2 g.2)
        linarith

private theorem continuous_binary {op : L0 μ → L0 μ → L0 μ} {φ : ℝ → ℝ → ℝ}
    (hφ : Continuous (Function.uncurry φ))
    (hop : ∀ f g, (op f g : Ω → ℝ) =ᵐ[μ] fun x ↦ φ (f x) (g x)) :
    Continuous (Function.uncurry op) := by
  apply continuous_iff_seqContinuous.2
  intro f g hfg
  apply tendsto_iff_tendstoInMeasure.2
  have h₁ := tendsto_iff_tendstoInMeasure.1 (continuous_fst.tendsto g |>.comp hfg)
  have h₂ := tendsto_iff_tendstoInMeasure.1 (continuous_snd.tendsto g |>.comp hfg)
  have h := h₁.continuous_comp₂ h₂ hφ
    (Eventually.of_forall fun n ↦ (hφ.comp_stronglyMeasurable
      ((f n).1.stronglyMeasurable.prodMk (f n).2.stronglyMeasurable)).aestronglyMeasurable)
  exact h.congr (fun n ↦ (hop (f n).1 (f n).2).symm) (hop g.1 g.2).symm

/-- Multiplication of real random variables is continuous for convergence in measure. -/
instance instContinuousMul : ContinuousMul (L0 μ) where
  continuous_mul := continuous_binary continuous_mul coeFn_mul

/-- The bounded integral topology makes real random variables a topological ring. -/
instance instIsTopologicalRing : IsTopologicalRing (L0 μ) where

/-- Joint real scalar multiplication is continuous for convergence in measure. -/
instance instContinuousSMul : ContinuousSMul ℝ (L0 μ) where
  continuous_smul := by
    apply continuous_iff_seqContinuous.2
    intro f g hfg
    apply tendsto_iff_tendstoInMeasure.2
    have h₁ : TendstoInMeasure μ (fun n (_ : Ω) ↦ (f n).1) atTop (fun _ ↦ g.1) :=
      tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
        (ae_of_all μ fun _ ↦ continuous_fst.tendsto g |>.comp hfg)
    have h₂ := tendsto_iff_tendstoInMeasure.1 (continuous_snd.tendsto g |>.comp hfg)
    have h := h₁.continuous_comp₂ h₂ continuous_mul
      (Eventually.of_forall fun n ↦
        ((f n).2.stronglyMeasurable.const_mul (f n).1).aestronglyMeasurable)
    exact h.congr (fun n ↦ (coeFn_smul (f n).1 (f n).2).symm)
      (coeFn_smul g.1 g.2).symm

end FiniteMeasure
end TauCeti.L0
