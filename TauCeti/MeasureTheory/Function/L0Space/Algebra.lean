/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.AEEqFun
public import TauCeti.MeasureTheory.Function.L0Space.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Algebraic, topological-algebraic, and `Lᵖ`-embedding structure on `L⁰(μ; E)`

Pointwise algebraic operations on `α →ₘ[μ] E` (`MeasureTheory.AEEqFun`) transfer along
`TauCeti.L0.equivAEEqFun` to `TauCeti.L0 E μ` for an arbitrary measure `μ`, giving additive group,
module, (commutative) semiring, (commutative) ring, and algebra instances together with bundled
equivalences (`addEquivAEEqFun`, `linearEquivAEEqFun`, `ringEquivAEEqFun`, `algEquivAEEqFun`).

On a finite measure space, isometric scalar actions and translations on `E` lift to `L0 E μ`
(`IsIsometricSMul`, `IsIsometricVAdd`), uniform additive groups and uniformly continuous constant
scalar actions lift to `IsUniformAddGroup (L0 E μ)` and `UniformContinuousConstSMul 𝕜 (L0 E μ)`,
and Lipschitz addition lifts to `LipschitzAdd (L0 E μ)` (providing `ContinuousAdd` on additive
monoids without negation). Combining `TauCeti.L0.tendsto_iff_tendstoInMeasure` with the algebraic
stability of `MeasureTheory.TendstoInMeasure` gives joint continuity of bounded scalar
multiplication (`ContinuousSMul 𝕜 (L0 E μ)`) and makes `L0 R μ` a topological semiring under
`[LipschitzAdd R]` and `[IsBoundedSMul R R]`, and a topological ring under `[IsUniformAddGroup R]`
and `[IsBoundedSMul R R]`.

For $1 \le p \le \infty$, the canonical inclusion `TauCeti.L0.ofLp : Lp E p μ → L0 E μ` is
continuous on finite measure spaces (`TauCeti.L0.continuous_ofLp`) via
`MeasureTheory.tendstoInMeasure_of_tendsto_Lp`, and bundles as a continuous linear map
`TauCeti.L0.ofLpCLM`. Closed-form distance formulas for indicator-constant classes
(`dist_indicatorConst_zero`, `dist_indicatorConst_one_zero`) evaluate the `L⁰` metric explicitly on
null-measurable indicators, and `tendsto_dist_natCast_zero_nhds_measureReal_univ` /
`not_exists_tendsto_natCast` show that the natural-number constant classes `(n : L0 ℝ μ)` have
distance to `0` tending to `μ.real Set.univ` and diverge whenever `μ ≠ 0`.

## Main declarations

* `TauCeti.L0.addEquivAEEqFun`, `linearEquivAEEqFun`, `ringEquivAEEqFun`, `algEquivAEEqFun`:
  algebraic equivalences between `L0` and `MeasureTheory.AEEqFun`.
* `TauCeti.L0.instIsIsometricSMul`, `instIsIsometricVAdd`, `instIsUniformAddGroup`,
  `instLipschitzAdd`, `instUniformContinuousConstSMul`, `instContinuousSMul`, `instContinuousMul`,
  `instIsTopologicalSemiring`, `instIsTopologicalRing`: isometric actions, uniform and Lipschitz
  structure, and continuity of algebraic operations on `L0` over finite measure spaces.
* `TauCeti.L0.ofLp`, `TauCeti.L0.continuous_ofLp`, `TauCeti.L0.ofLpCLM`: continuous linear
  inclusion of `Lp E p μ` into `L0 E μ` for `1 ≤ p`.
* `TauCeti.L0.indicatorConst`, `TauCeti.L0.dist_indicatorConst_zero`,
  `TauCeti.L0.tendsto_dist_natCast_zero_nhds_measureReal_univ`: indicator-constant classes and
  explicit `L⁰` distance asymptotics.
-/

public noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace L0

section Algebra

variable {α 𝕜 𝕜' E R : Type*} {mα : MeasurableSpace α} {μ : Measure α}

section Pointwise

variable [TopologicalSpace E]

@[to_additive]
instance instOne [One E] : One (L0 E μ) :=
  ⟨ofAEEqFun 1⟩

@[to_additive (attr := simp)]
theorem toAEEqFun_one [One E] : (1 : L0 E μ).toAEEqFun = 1 := by
  rfl

@[to_additive (attr := simp)]
theorem ofAEEqFun_one [One E] : (ofAEEqFun 1 : L0 E μ) = 1 := by
  rfl

@[to_additive (attr := simp)]
theorem const_one [One E] : const (μ := μ) α (1 : E) = 1 :=
  toAEEqFun_injective (by rw [toAEEqFun_const, toAEEqFun_one]; rfl)

@[to_additive]
theorem coeFn_one [One E] : ⇑(1 : L0 E μ) =ᵐ[μ] 1 := by
  rw [← coeFn_toAEEqFun, toAEEqFun_one]
  exact AEEqFun.coeFn_one

@[to_additive (attr := simp)]
theorem coeFn_one_eq [NeZero μ] [One E] (x : α) : (1 : L0 E μ) x = 1 := by
  rw [← coeFn_toAEEqFun, toAEEqFun_one]
  exact AEEqFun.coeFn_one_eq

instance instSMul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] : SMul 𝕜 (L0 E μ) :=
  ⟨fun c f ↦ ofAEEqFun (c • f.toAEEqFun)⟩

@[simp]
theorem toAEEqFun_smul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (f : L0 E μ) :
    (c • f).toAEEqFun = c • f.toAEEqFun := by
  rfl

@[simp]
theorem ofAEEqFun_smul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (f : α →ₘ[μ] E) :
    (ofAEEqFun (c • f) : L0 E μ) = c • ofAEEqFun f := by
  rfl

@[simp]
theorem smul_mk [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (f : α → E)
    (hf : AEStronglyMeasurable f μ) :
    c • mk (μ := μ) f hf = mk (c • f) (hf.const_smul c) :=
  toAEEqFun_injective (by rw [toAEEqFun_smul, toAEEqFun_mk, toAEEqFun_mk, AEEqFun.smul_mk])

@[simp]
theorem const_smul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (a : E) :
    const (μ := μ) α (c • a) = c • const α a := by
  rw [← mk_const, ← mk_const, smul_mk]
  rfl

/-- Representative of `c • f` in `L0 E μ` agrees with `c • ⇑f` almost everywhere. -/
theorem coeFn_smul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (f : L0 E μ) :
    ⇑(c • f) =ᵐ[μ] c • ⇑f := by
  rw [← coeFn_toAEEqFun, ← coeFn_toAEEqFun, toAEEqFun_smul]
  exact AEEqFun.coeFn_smul c f.toAEEqFun

instance instSMulCommClass [SMul 𝕜 E] [SMul 𝕜' E] [ContinuousConstSMul 𝕜 E]
    [ContinuousConstSMul 𝕜' E] [SMulCommClass 𝕜 𝕜' E] : SMulCommClass 𝕜 𝕜' (L0 E μ) :=
  ⟨fun a b f ↦ toAEEqFun_injective (smul_comm a b f.toAEEqFun)⟩

instance instIsScalarTower [SMul 𝕜 𝕜'] [SMul 𝕜 E] [SMul 𝕜' E] [ContinuousConstSMul 𝕜 E]
    [ContinuousConstSMul 𝕜' E] [IsScalarTower 𝕜 𝕜' E] : IsScalarTower 𝕜 𝕜' (L0 E μ) :=
  ⟨fun a b f ↦ toAEEqFun_injective (smul_assoc a b f.toAEEqFun)⟩

instance instIsCentralScalar [SMul 𝕜 E] [SMul 𝕜ᵐᵒᵖ E] [ContinuousConstSMul 𝕜 E]
    [IsCentralScalar 𝕜 E] : IsCentralScalar 𝕜 (L0 E μ) :=
  ⟨fun a f ↦ toAEEqFun_injective (op_smul_eq_smul a f.toAEEqFun)⟩

@[to_additive]
instance instMul [Mul E] [ContinuousMul E] : Mul (L0 E μ) :=
  ⟨fun f g ↦ ofAEEqFun (f.toAEEqFun * g.toAEEqFun)⟩

@[to_additive (attr := simp)]
theorem toAEEqFun_mul [Mul E] [ContinuousMul E] (f g : L0 E μ) :
    (f * g).toAEEqFun = f.toAEEqFun * g.toAEEqFun := by
  rfl

@[to_additive (attr := simp)]
theorem ofAEEqFun_mul [Mul E] [ContinuousMul E] (f g : α →ₘ[μ] E) :
    (ofAEEqFun (f * g) : L0 E μ) = ofAEEqFun f * ofAEEqFun g := by
  rfl

@[to_additive (attr := simp)]
theorem mk_mul_mk [Mul E] [ContinuousMul E] (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (μ := μ) f hf * mk (μ := μ) g hg = mk (f * g) (hf.mul hg) :=
  toAEEqFun_injective
    (by rw [toAEEqFun_mul, toAEEqFun_mk, toAEEqFun_mk, toAEEqFun_mk, AEEqFun.mk_mul_mk])

@[to_additive (attr := simp)]
theorem const_mul [Mul E] [ContinuousMul E] (a b : E) :
    const (μ := μ) α (a * b) = const α a * const α b := by
  rw [← mk_const, ← mk_const, ← mk_const, mk_mul_mk]
  rfl

@[to_additive]
theorem coeFn_mul [Mul E] [ContinuousMul E] (f g : L0 E μ) : ⇑(f * g) =ᵐ[μ] ⇑f * ⇑g := by
  rw [← coeFn_toAEEqFun, ← coeFn_toAEEqFun, ← coeFn_toAEEqFun, toAEEqFun_mul]
  exact AEEqFun.coeFn_mul f.toAEEqFun g.toAEEqFun

instance instPowNat [Monoid E] [ContinuousMul E] : Pow (L0 E μ) ℕ :=
  ⟨fun f n ↦ ofAEEqFun (f.toAEEqFun ^ n)⟩

@[simp]
theorem toAEEqFun_pow [Monoid E] [ContinuousMul E] (f : L0 E μ) (n : ℕ) :
    (f ^ n).toAEEqFun = f.toAEEqFun ^ n := by
  rfl

@[simp]
theorem ofAEEqFun_pow [Monoid E] [ContinuousMul E] (f : α →ₘ[μ] E) (n : ℕ) :
    (ofAEEqFun (f ^ n) : L0 E μ) = ofAEEqFun f ^ n := by
  rfl

@[simp]
theorem mk_pow [Monoid E] [ContinuousMul E] (f : α → E) (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    mk (μ := μ) f hf ^ n = mk (f ^ n) ((continuous_pow n).comp_aestronglyMeasurable hf) :=
  toAEEqFun_injective (by rw [toAEEqFun_pow, toAEEqFun_mk, toAEEqFun_mk, AEEqFun.mk_pow])

/-- Representative of `f ^ n` in `L0 E μ` agrees with `(⇑f) ^ n` almost everywhere. -/
theorem coeFn_pow [Monoid E] [ContinuousMul E] (f : L0 E μ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n := by
  rw [← coeFn_toAEEqFun, ← coeFn_toAEEqFun, toAEEqFun_pow]
  exact AEEqFun.coeFn_pow f.toAEEqFun n

instance instNeg [AddGroup E] [IsTopologicalAddGroup E] : Neg (L0 E μ) :=
  ⟨fun f ↦ ofAEEqFun (-f.toAEEqFun)⟩

@[simp]
theorem toAEEqFun_neg [AddGroup E] [IsTopologicalAddGroup E] (f : L0 E μ) :
    (-f).toAEEqFun = -f.toAEEqFun := by
  rfl

@[simp]
theorem ofAEEqFun_neg [AddGroup E] [IsTopologicalAddGroup E] (f : α →ₘ[μ] E) :
    (ofAEEqFun (-f) : L0 E μ) = -ofAEEqFun f := by
  rfl

@[simp]
theorem neg_mk [AddGroup E] [IsTopologicalAddGroup E] (f : α → E)
    (hf : AEStronglyMeasurable f μ) :
    -mk (μ := μ) f hf = mk (-f) hf.neg :=
  toAEEqFun_injective (by rw [toAEEqFun_neg, toAEEqFun_mk, toAEEqFun_mk, AEEqFun.neg_mk])

@[simp]
theorem const_neg [AddGroup E] [IsTopologicalAddGroup E] (a : E) :
    const (μ := μ) α (-a) = -const α a := by
  rw [← mk_const, ← mk_const, neg_mk]
  rfl

/-- Representative of `-f` in `L0 E μ` agrees with `-⇑f` almost everywhere. -/
theorem coeFn_neg [AddGroup E] [IsTopologicalAddGroup E] (f : L0 E μ) : ⇑(-f) =ᵐ[μ] -⇑f := by
  rw [← coeFn_toAEEqFun, ← coeFn_toAEEqFun, toAEEqFun_neg]
  exact AEEqFun.coeFn_neg f.toAEEqFun

instance instSub [AddGroup E] [IsTopologicalAddGroup E] : Sub (L0 E μ) :=
  ⟨fun f g ↦ ofAEEqFun (f.toAEEqFun - g.toAEEqFun)⟩

@[simp]
theorem toAEEqFun_sub [AddGroup E] [IsTopologicalAddGroup E] (f g : L0 E μ) :
    (f - g).toAEEqFun = f.toAEEqFun - g.toAEEqFun := by
  rfl

@[simp]
theorem ofAEEqFun_sub [AddGroup E] [IsTopologicalAddGroup E] (f g : α →ₘ[μ] E) :
    (ofAEEqFun (f - g) : L0 E μ) = ofAEEqFun f - ofAEEqFun g := by
  rfl

@[simp]
theorem mk_sub_mk [AddGroup E] [IsTopologicalAddGroup E] (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (μ := μ) f hf - mk (μ := μ) g hg = mk (f - g) (hf.sub hg) :=
  toAEEqFun_injective
    (by rw [toAEEqFun_sub, toAEEqFun_mk, toAEEqFun_mk, toAEEqFun_mk, AEEqFun.mk_sub])

@[simp]
theorem const_sub [AddGroup E] [IsTopologicalAddGroup E] (a b : E) :
    const (μ := μ) α (a - b) = const α a - const α b := by
  rw [← mk_const, ← mk_const, ← mk_const, mk_sub_mk]
  rfl

/-- Representative of `f - g` in `L0 E μ` agrees with `⇑f - ⇑g` almost everywhere. -/
theorem coeFn_sub [AddGroup E] [IsTopologicalAddGroup E] (f g : L0 E μ) :
    ⇑(f - g) =ᵐ[μ] ⇑f - ⇑g := by
  rw [← coeFn_toAEEqFun, ← coeFn_toAEEqFun, ← coeFn_toAEEqFun, toAEEqFun_sub]
  exact AEEqFun.coeFn_sub f.toAEEqFun g.toAEEqFun

instance instNatCast [NatCast E] : NatCast (L0 E μ) :=
  ⟨fun n ↦ ofAEEqFun n⟩

@[simp]
theorem toAEEqFun_natCast [NatCast E] (n : ℕ) : ((n : L0 E μ)).toAEEqFun = n := by
  rfl

@[simp]
theorem ofAEEqFun_natCast [NatCast E] (n : ℕ) :
    (ofAEEqFun (n : α →ₘ[μ] E) : L0 E μ) = n := by
  rfl

/-- Natural-number cast on `L0 E μ` is the constant class `const α n`. -/
theorem natCast_def [NatCast E] (n : ℕ) : (n : L0 E μ) = const α (n : E) :=
  toAEEqFun_injective (by rw [toAEEqFun_natCast, toAEEqFun_const, AEEqFun.natCast_def])

/-- Representative of `(n : L0 E μ)` agrees with the constant `(n : E)` almost everywhere. -/
theorem coeFn_natCast [NatCast E] (n : ℕ) : ⇑(n : L0 E μ) =ᵐ[μ] Function.const α (n : E) := by
  rw [← coeFn_toAEEqFun, toAEEqFun_natCast]
  exact AEEqFun.coeFn_natCast n

@[simp]
theorem coeFn_natCast_eq [NeZero μ] [NatCast E] (n : ℕ) (x : α) : (n : L0 E μ) x = n := by
  rw [← coeFn_toAEEqFun, toAEEqFun_natCast]
  exact AEEqFun.coeFn_natCast_eq n x

instance instIntCast [IntCast E] : IntCast (L0 E μ) :=
  ⟨fun n ↦ ofAEEqFun n⟩

@[simp]
theorem toAEEqFun_intCast [IntCast E] (n : ℤ) : ((n : L0 E μ)).toAEEqFun = n := by
  rfl

@[simp]
theorem ofAEEqFun_intCast [IntCast E] (n : ℤ) :
    (ofAEEqFun (n : α →ₘ[μ] E) : L0 E μ) = n := by
  rfl

/-- Integer cast on `L0 E μ` is the constant class `const α n`. -/
theorem intCast_def [IntCast E] (n : ℤ) : (n : L0 E μ) = const α (n : E) :=
  toAEEqFun_injective (by rw [toAEEqFun_intCast, toAEEqFun_const, AEEqFun.intCast_def])

/-- Representative of `(n : L0 E μ)` agrees with the constant `(n : E)` almost everywhere. -/
theorem coeFn_intCast [IntCast E] (n : ℤ) : ⇑(n : L0 E μ) =ᵐ[μ] Function.const α (n : E) := by
  rw [← coeFn_toAEEqFun, toAEEqFun_intCast]
  exact AEEqFun.coeFn_intCast n

@[simp]
theorem coeFn_intCast_eq [NeZero μ] [IntCast E] (n : ℤ) (x : α) : (n : L0 E μ) x = n := by
  rw [← coeFn_toAEEqFun, toAEEqFun_intCast]
  exact AEEqFun.coeFn_intCast_eq n x

instance instAddMonoid [AddMonoid E] [ContinuousAdd E] : AddMonoid (L0 E μ) :=
  toAEEqFun_injective.addMonoid toAEEqFun toAEEqFun_zero toAEEqFun_add fun _ _ ↦ toAEEqFun_smul _ _

instance instAddCommMonoid [AddCommMonoid E] [ContinuousAdd E] : AddCommMonoid (L0 E μ) :=
  toAEEqFun_injective.addCommMonoid toAEEqFun toAEEqFun_zero toAEEqFun_add
    fun _ _ ↦ toAEEqFun_smul _ _

instance instMonoid [Monoid E] [ContinuousMul E] : Monoid (L0 E μ) :=
  toAEEqFun_injective.monoid toAEEqFun toAEEqFun_one toAEEqFun_mul toAEEqFun_pow

instance instCommMonoid [CommMonoid E] [ContinuousMul E] : CommMonoid (L0 E μ) :=
  toAEEqFun_injective.commMonoid toAEEqFun toAEEqFun_one toAEEqFun_mul toAEEqFun_pow

instance instAddGroup [AddGroup E] [IsTopologicalAddGroup E] : AddGroup (L0 E μ) :=
  toAEEqFun_injective.addGroup toAEEqFun toAEEqFun_zero toAEEqFun_add toAEEqFun_neg toAEEqFun_sub
    (fun _ _ ↦ toAEEqFun_smul _ _) fun _ _ ↦ toAEEqFun_smul _ _

instance instAddCommGroup [AddCommGroup E] [IsTopologicalAddGroup E] : AddCommGroup (L0 E μ) :=
  toAEEqFun_injective.addCommGroup toAEEqFun toAEEqFun_zero toAEEqFun_add toAEEqFun_neg
    toAEEqFun_sub (fun _ _ ↦ toAEEqFun_smul _ _) fun _ _ ↦ toAEEqFun_smul _ _

/-- Canonical additive equivalence between `L0 E μ` and `α →ₘ[μ] E`. -/
def addEquivAEEqFun [Add E] [ContinuousAdd E] : L0 E μ ≃+ (α →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun
  map_add' := toAEEqFun_add

@[simp]
theorem addEquivAEEqFun_apply [Add E] [ContinuousAdd E] (f : L0 E μ) :
    addEquivAEEqFun f = f.toAEEqFun := by
  rfl

@[simp]
theorem addEquivAEEqFun_symm_apply [Add E] [ContinuousAdd E] (f : α →ₘ[μ] E) :
    addEquivAEEqFun.symm f = ofAEEqFun f := by
  rfl

instance instMulAction [Monoid 𝕜] [MulAction 𝕜 E] [ContinuousConstSMul 𝕜 E] :
    MulAction 𝕜 (L0 E μ) :=
  toAEEqFun_injective.mulAction toAEEqFun toAEEqFun_smul

instance instDistribMulAction [Monoid 𝕜] [AddMonoid E] [ContinuousAdd E] [DistribMulAction 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : DistribMulAction 𝕜 (L0 E μ) :=
  Function.Injective.distribMulAction (addEquivAEEqFun : L0 E μ ≃+ (α →ₘ[μ] E)).toAddMonoidHom
    addEquivAEEqFun.injective (by simp [toAEEqFun_smul])

instance instModule [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : Module 𝕜 (L0 E μ) :=
  Function.Injective.module 𝕜 (addEquivAEEqFun : L0 E μ ≃+ (α →ₘ[μ] E)).toAddMonoidHom
    addEquivAEEqFun.injective (by simp [toAEEqFun_smul])

/-- Canonical `𝕜`-linear equivalence between `L0 E μ` and `α →ₘ[μ] E`. -/
def linearEquivAEEqFun (𝕜 : Type*) [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : L0 E μ ≃ₗ[𝕜] (α →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun
  map_add' := toAEEqFun_add
  map_smul' _ _ := toAEEqFun_smul _ _

@[simp]
theorem linearEquivAEEqFun_apply [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] (f : L0 E μ) :
    linearEquivAEEqFun 𝕜 f = f.toAEEqFun := by
  rfl

@[simp]
theorem linearEquivAEEqFun_symm_apply [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E]
    [Module 𝕜 E] [ContinuousConstSMul 𝕜 E] (f : α →ₘ[μ] E) :
    (linearEquivAEEqFun (E := E) (μ := μ) 𝕜).symm f = ofAEEqFun f := by
  rfl

end Pointwise

section Ring

variable [TopologicalSpace R]

instance instSemiring [Semiring R] [IsTopologicalSemiring R] : Semiring (L0 R μ) :=
  toAEEqFun_injective.semiring toAEEqFun toAEEqFun_zero toAEEqFun_one toAEEqFun_add toAEEqFun_mul
    (fun _ _ ↦ toAEEqFun_smul _ _) toAEEqFun_pow toAEEqFun_natCast

instance instCommSemiring [CommSemiring R] [IsTopologicalSemiring R] : CommSemiring (L0 R μ) where
  __ := instSemiring
  __ := instCommMonoid

instance instRing [Ring R] [IsTopologicalRing R] : Ring (L0 R μ) :=
  toAEEqFun_injective.ring toAEEqFun toAEEqFun_zero toAEEqFun_one toAEEqFun_add toAEEqFun_mul
    toAEEqFun_neg toAEEqFun_sub (fun _ _ ↦ toAEEqFun_smul _ _) (fun _ _ ↦ toAEEqFun_smul _ _)
    toAEEqFun_pow toAEEqFun_natCast toAEEqFun_intCast

instance instCommRing [CommRing R] [IsTopologicalRing R] : CommRing (L0 R μ) where
  __ := instRing
  __ := instCommMonoid

/-- Canonical ring equivalence between `L0 R μ` and `α →ₘ[μ] R`. -/
def ringEquivAEEqFun [Add R] [Mul R] [ContinuousAdd R] [ContinuousMul R] :
    L0 R μ ≃+* (α →ₘ[μ] R) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun
  map_mul' := toAEEqFun_mul
  map_add' := toAEEqFun_add

@[simp]
theorem ringEquivAEEqFun_apply [Add R] [Mul R] [ContinuousAdd R] [ContinuousMul R] (f : L0 R μ) :
    ringEquivAEEqFun f = f.toAEEqFun := by
  rfl

@[simp]
theorem ringEquivAEEqFun_symm_apply [Add R] [Mul R] [ContinuousAdd R] [ContinuousMul R]
    (f : α →ₘ[μ] R) :
    ringEquivAEEqFun.symm f = ofAEEqFun f := by
  rfl

instance instAlgebra [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R] :
    Algebra 𝕜 (L0 R μ) where
  algebraMap :=
    { toFun c := ofAEEqFun (algebraMap 𝕜 (α →ₘ[μ] R) c)
      map_one' := by simp [← ofAEEqFun_one]
      map_mul' a b := by simp
      map_zero' := by simp [← ofAEEqFun_zero]
      map_add' a b := by simp }
  commutes' c f := toAEEqFun_injective (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAEEqFun_mul]
    exact Algebra.commutes c f.toAEEqFun)
  smul_def' c f := toAEEqFun_injective (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAEEqFun_smul, toAEEqFun_mul]
    exact Algebra.smul_def c f.toAEEqFun)

/-- `toAEEqFun` commutes with `algebraMap` from `𝕜`. -/
theorem toAEEqFun_algebraMap [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    (c : 𝕜) :
    (algebraMap 𝕜 (L0 R μ) c).toAEEqFun = algebraMap 𝕜 (α →ₘ[μ] R) c := by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem algebraMap_apply [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    (c : 𝕜) :
    algebraMap 𝕜 (L0 R μ) c = const α (algebraMap 𝕜 R c) :=
  toAEEqFun_injective (by rw [toAEEqFun_algebraMap, AEEqFun.algebraMap_apply, toAEEqFun_const])

/-- Canonical `𝕜`-algebra equivalence between `L0 R μ` and `α →ₘ[μ] R`. -/
def algEquivAEEqFun (𝕜 : Type*) [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R]
    [Algebra 𝕜 R] : L0 R μ ≃ₐ[𝕜] (α →ₘ[μ] R) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun
  map_mul' := toAEEqFun_mul
  map_add' := toAEEqFun_add
  commutes' := toAEEqFun_algebraMap

@[simp]
theorem algEquivAEEqFun_apply [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R]
    [Algebra 𝕜 R] (f : L0 R μ) :
    algEquivAEEqFun 𝕜 f = f.toAEEqFun := by
  rfl

@[simp]
theorem algEquivAEEqFun_symm_apply [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R]
    [Algebra 𝕜 R] (f : α →ₘ[μ] R) :
    (algEquivAEEqFun (R := R) (μ := μ) 𝕜).symm f = ofAEEqFun f := by
  rfl

end Ring

end Algebra

section TopologicalAlgebra

variable {α 𝕜 E R : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]

/-- An isometric scalar action on `E` lifts to an isometric scalar action on `L0 E μ`. -/
instance instIsIsometricSMul [PseudoMetricSpace E] [SMul 𝕜 E] [IsIsometricSMul 𝕜 E] :
    IsIsometricSMul 𝕜 (L0 E μ) :=
  ⟨fun c ↦ Isometry.of_dist_eq fun f g ↦ by
    rw [dist_def, dist_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_smul c f, coeFn_smul c g] with x hcf hcg
    simp [hcf, hcg]⟩

/-- Isometric left translation on `E` lifts to isometric left translation on `L0 E μ`. -/
instance instIsIsometricVAdd [PseudoMetricSpace E] [Add E] [ContinuousAdd E]
    [IsIsometricVAdd E E] : IsIsometricVAdd (L0 E μ) (L0 E μ) :=
  ⟨fun h ↦ Isometry.of_dist_eq fun f g ↦ by
    simp_rw [vadd_eq_add]
    rw [dist_def, dist_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_add h f, coeFn_add h g] with x hhf hhg
    simp [hhf, hhg]⟩

/-- Isometric right translation on `E` lifts to isometric right translation on `L0 E μ`. -/
instance instIsIsometricVAddOp [PseudoMetricSpace E] [Add E] [ContinuousAdd E]
    [IsIsometricVAdd Eᵃᵒᵖ E] : IsIsometricVAdd (L0 E μ)ᵃᵒᵖ (L0 E μ) :=
  ⟨fun h ↦ Isometry.of_dist_eq fun f g ↦ by
    simp_rw [AddOpposite.vadd_eq_add_unop]
    rw [dist_def, dist_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_add f h.unop, coeFn_add g h.unop] with x hfh hgh
    simp [hfh, hgh]⟩

/-- In `L0 E μ` over a topological additive group with isometric right translation,
`dist f g = dist (f - g) 0`. -/
theorem dist_eq_dist_sub_zero [AddGroup E] [PseudoMetricSpace E] [IsTopologicalAddGroup E]
    [IsIsometricVAdd Eᵃᵒᵖ E] (f g : L0 E μ) :
    dist f g = dist (f - g) 0 := by
  simpa [sub_eq_add_neg] using (dist_add_right f g (-g)).symm

/-- On a finite measure space, `L0 E μ` is a uniform additive group (and hence a topological
additive group) whenever `E` is a uniform additive group. -/
instance instIsUniformAddGroup [AddGroup E] [PseudoMetricSpace E] [IsUniformAddGroup E] :
    IsUniformAddGroup (L0 E μ) where
  uniformContinuous_sub := Metric.uniformContinuous_iff.mpr fun η hη ↦ by
    let ε : ℝ := η / (2 * (μ.real Set.univ + 1))
    have hden : 0 < μ.real Set.univ + 1 := by positivity
    have hε : 0 < ε := div_pos hη (by positivity)
    have hε_mass : ε * μ.real Set.univ < η / 2 := by
      calc ε * μ.real Set.univ
          < ε * (μ.real Set.univ + 1) := by gcongr; linarith
        _ = η / 2 := by
            dsimp [ε]
            field_simp [hden.ne']
    obtain ⟨δ, hδ, hsub⟩ := Metric.uniformContinuous_iff.mp
      (uniformContinuous_sub (α := E)) ε hε
    have h1δ : 0 < 1 + δ := by positivity
    refine ⟨δ / (1 + δ) * (η / 4), by positivity, fun {p q} hpq ↦ ?_⟩
    rw [Prod.dist_eq, max_lt_iff] at hpq
    have hae : {x | ε ≤ dist ((p.1 - p.2) x) ((q.1 - q.2) x)} ≤ᵐ[μ]
        ({x | δ ≤ dist (p.1 x) (q.1 x)} ∪ {x | δ ≤ dist (p.2 x) (q.2 x)} : Set α) := by
      filter_upwards [coeFn_sub p.1 p.2, coeFn_sub q.1 q.2] with x hpx hqx hx
      rw [hpx, hqx, Pi.sub_apply, Pi.sub_apply] at hx
      by_contra hnot
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
      exact hx.not_gt (hsub (a := (p.1 x, p.2 x)) (b := (q.1 x, q.2 x))
        (by rw [Prod.dist_eq]; exact max_lt hnot.1 hnot.2))
    have htail : μ.real {x | ε ≤ dist ((p.1 - p.2) x) ((q.1 - q.2) x)} ≤
        μ.real {x | δ ≤ dist (p.1 x) (q.1 x)} + μ.real {x | δ ≤ dist (p.2 x) (q.2 x)} :=
      calc μ.real {x | ε ≤ dist ((p.1 - p.2) x) ((q.1 - q.2) x)}
          ≤ μ.real ({x | δ ≤ dist (p.1 x) (q.1 x)} ∪ {x | δ ≤ dist (p.2 x) (q.2 x)}) := by
            rw [measureReal_def, measureReal_def]
            exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hae)
        _ ≤ μ.real {x | δ ≤ dist (p.1 x) (q.1 x)} + μ.real {x | δ ≤ dist (p.2 x) (q.2 x)} :=
            measureReal_union_le _ _
    have hm₁ : μ.real {x | δ ≤ dist (p.1 x) (q.1 x)} < η / 4 := by
      calc μ.real {x | δ ≤ dist (p.1 x) (q.1 x)}
          ≤ (1 + δ) / δ * dist p.1 q.1 := measureReal_ge_le_mul_dist hδ
        _ < (1 + δ) / δ * (δ / (1 + δ) * (η / 4)) :=
            mul_lt_mul_of_pos_left hpq.1 (div_pos h1δ hδ)
        _ = η / 4 := by field_simp [hδ.ne', h1δ.ne']
    have hm₂ : μ.real {x | δ ≤ dist (p.2 x) (q.2 x)} < η / 4 := by
      calc μ.real {x | δ ≤ dist (p.2 x) (q.2 x)}
          ≤ (1 + δ) / δ * dist p.2 q.2 := measureReal_ge_le_mul_dist hδ
        _ < (1 + δ) / δ * (δ / (1 + δ) * (η / 4)) :=
            mul_lt_mul_of_pos_left hpq.2 (div_pos h1δ hδ)
        _ = η / 4 := by field_simp [hδ.ne', h1δ.ne']
    calc dist (p.1 - p.2) (q.1 - q.2)
        ≤ ε * μ.real Set.univ + μ.real {x | ε ≤ dist ((p.1 - p.2) x) ((q.1 - q.2) x)} :=
          dist_le_mul_measureReal_univ_add_measureReal_ge hε.le
      _ < η / 2 + (η / 4 + η / 4) := by linarith
      _ = η := by ring

/-- On a finite measure space, addition on `L0 E μ` is Lipschitz whenever addition on `E` is
Lipschitz (giving `ContinuousAdd (L0 E μ)` on additive monoids and semirings without negation). -/
instance instLipschitzAdd [AddMonoid E] [PseudoMetricSpace E] [LipschitzAdd E] :
    LipschitzAdd (L0 E μ) where
  lipschitz_add := by
    let C : ℝ≥0 := LipschitzAdd.C E
    let K : ℝ≥0 := max C 1
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast le_max_right C 1
    have hCK : (C : ℝ) ≤ K := by exact_mod_cast le_max_left C 1
    have hscale : ∀ t : ℝ, 0 ≤ t → (K : ℝ) * t / (1 + (K : ℝ) * t) ≤ K * (t / (1 + t)) :=
      fun t ht ↦ by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_left (mul_nonneg K.coe_nonneg ht) (by positivity) (by nlinarith)
    refine ⟨2 * K, LipschitzWith.of_dist_le_mul fun p q ↦ ?_⟩
    have hae : ∀ᵐ x ∂μ,
        dist ((p.1 + p.2) x) ((q.1 + q.2) x) / (1 + dist ((p.1 + p.2) x) ((q.1 + q.2) x)) ≤
          (K : ℝ) * (dist (p.1 x) (q.1 x) / (1 + dist (p.1 x) (q.1 x))) +
            (K : ℝ) * (dist (p.2 x) (q.2 x) / (1 + dist (p.2 x) (q.2 x))) := by
      filter_upwards [coeFn_add p.1 p.2, coeFn_add q.1 q.2] with x hpx hqx
      rw [hpx, hqx, Pi.add_apply, Pi.add_apply]
      have hlip : dist (p.1 x + p.2 x) (q.1 x + q.2 x) ≤
          (K : ℝ) * dist (p.1 x) (q.1 x) + (K : ℝ) * dist (p.2 x) (q.2 x) := by
        calc dist (p.1 x + p.2 x) (q.1 x + q.2 x)
            ≤ (C : ℝ) * dist (p.1 x, p.2 x) (q.1 x, q.2 x) :=
              lipschitz_with_lipschitz_const_add (p.1 x, p.2 x) (q.1 x, q.2 x)
          _ ≤ (K : ℝ) * max (dist (p.1 x) (q.1 x)) (dist (p.2 x) (q.2 x)) := by
              rw [Prod.dist_eq]
              exact mul_le_mul_of_nonneg_right hCK (le_max_of_le_left dist_nonneg)
          _ ≤ (K : ℝ) * (dist (p.1 x) (q.1 x) + dist (p.2 x) (q.2 x)) :=
              mul_le_mul_of_nonneg_left
                (max_le (le_add_of_nonneg_right dist_nonneg) (le_add_of_nonneg_left dist_nonneg))
                K.coe_nonneg
          _ = (K : ℝ) * dist (p.1 x) (q.1 x) + (K : ℝ) * dist (p.2 x) (q.2 x) := by ring
      calc dist (p.1 x + p.2 x) (q.1 x + q.2 x) / (1 + dist (p.1 x + p.2 x) (q.1 x + q.2 x))
          ≤ ((K : ℝ) * dist (p.1 x) (q.1 x) + (K : ℝ) * dist (p.2 x) (q.2 x)) /
              (1 + ((K : ℝ) * dist (p.1 x) (q.1 x) + (K : ℝ) * dist (p.2 x) (q.2 x))) :=
            div_one_add_mono dist_nonneg hlip
        _ ≤ (K : ℝ) * dist (p.1 x) (q.1 x) / (1 + (K : ℝ) * dist (p.1 x) (q.1 x)) +
              (K : ℝ) * dist (p.2 x) (q.2 x) / (1 + (K : ℝ) * dist (p.2 x) (q.2 x)) :=
            div_one_add_add_le (mul_nonneg K.coe_nonneg dist_nonneg)
              (mul_nonneg K.coe_nonneg dist_nonneg)
        _ ≤ (K : ℝ) * (dist (p.1 x) (q.1 x) / (1 + dist (p.1 x) (q.1 x))) +
              (K : ℝ) * (dist (p.2 x) (q.2 x) / (1 + dist (p.2 x) (q.2 x))) :=
            add_le_add (hscale _ dist_nonneg) (hscale _ dist_nonneg)
    have hint₁ := (integrable_dist_div_one_add p.1 q.1).const_mul (K : ℝ)
    have hint₂ := (integrable_dist_div_one_add p.2 q.2).const_mul (K : ℝ)
    calc dist (p.1 + p.2) (q.1 + q.2)
        ≤ ∫ x, ((K : ℝ) * (dist (p.1 x) (q.1 x) / (1 + dist (p.1 x) (q.1 x))) +
            (K : ℝ) * (dist (p.2 x) (q.2 x) / (1 + dist (p.2 x) (q.2 x)))) ∂μ :=
          integral_mono_ae (integrable_dist_div_one_add (p.1 + p.2) (q.1 + q.2))
            (hint₁.add hint₂) hae
      _ = (K : ℝ) * dist p.1 q.1 + (K : ℝ) * dist p.2 q.2 := by
          rw [integral_add hint₁ hint₂, integral_const_mul, integral_const_mul, dist_def, dist_def]
      _ ≤ (K : ℝ) * dist p q + (K : ℝ) * dist p q := by
          rw [Prod.dist_eq]
          exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) K.coe_nonneg)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) K.coe_nonneg)
      _ = ↑(2 * K) * dist p q := by
          push_cast
          ring

/-- On a finite measure space, constant scalar multiplication on `L0 E μ` is uniformly continuous
whenever constant scalar multiplication on `E` is uniformly continuous. -/
instance instUniformContinuousConstSMul [SMul 𝕜 E] [PseudoMetricSpace E]
    [UniformContinuousConstSMul 𝕜 E] : UniformContinuousConstSMul 𝕜 (L0 E μ) where
  uniformContinuous_const_smul c := Metric.uniformContinuous_iff.mpr fun η hη ↦ by
    let ε : ℝ := η / (2 * (μ.real Set.univ + 1))
    have hden : 0 < μ.real Set.univ + 1 := by positivity
    have hε : 0 < ε := div_pos hη (by positivity)
    have hε_mass : ε * μ.real Set.univ < η / 2 := by
      calc ε * μ.real Set.univ
          < ε * (μ.real Set.univ + 1) := by gcongr; linarith
        _ = η / 2 := by
            dsimp [ε]
            field_simp [hden.ne']
    obtain ⟨δ, hδ, hsmul⟩ := Metric.uniformContinuous_iff.mp
      (uniformContinuous_const_smul (X := E) c) ε hε
    have h1δ : 0 < 1 + δ := by positivity
    refine ⟨δ / (1 + δ) * (η / 2), by positivity, fun {f g} hfg ↦ ?_⟩
    have hae : {x | ε ≤ dist ((c • f) x) ((c • g) x)} ≤ᵐ[μ] {x | δ ≤ dist (f x) (g x)} := by
      filter_upwards [coeFn_smul c f, coeFn_smul c g] with x hcf hcg hx
      rw [hcf, hcg, Pi.smul_apply, Pi.smul_apply] at hx
      by_contra! hlt
      exact hx.not_gt (hsmul hlt)
    have htail : μ.real {x | ε ≤ dist ((c • f) x) ((c • g) x)} < η / 2 := by
      calc μ.real {x | ε ≤ dist ((c • f) x) ((c • g) x)}
          ≤ μ.real {x | δ ≤ dist (f x) (g x)} := by
            rw [measureReal_def, measureReal_def]
            exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hae)
        _ ≤ (1 + δ) / δ * dist f g := measureReal_ge_le_mul_dist hδ
        _ < (1 + δ) / δ * (δ / (1 + δ) * (η / 2)) :=
            mul_lt_mul_of_pos_left hfg (div_pos h1δ hδ)
        _ = η / 2 := by field_simp [hδ.ne', h1δ.ne']
    calc dist (c • f) (c • g)
        ≤ ε * μ.real Set.univ + μ.real {x | ε ≤ dist ((c • f) x) ((c • g) x)} :=
          dist_le_mul_measureReal_univ_add_measureReal_ge hε.le
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring

/-- On a finite measure space, bounded scalar multiplication `𝕜 × L0 E μ → L0 E μ` is jointly
continuous. -/
instance instContinuousSMul [Zero 𝕜] [Zero E] [PseudoMetricSpace 𝕜] [PseudoMetricSpace E]
    [SMul 𝕜 E] [IsBoundedSMul 𝕜 E] : ContinuousSMul 𝕜 (L0 E μ) where
  continuous_smul := continuous_iff_continuousAt.mpr fun p ↦ by
    have hc : Tendsto (fun q : 𝕜 × L0 E μ ↦ q.1) (𝓝 p) (𝓝 p.1) := continuous_fst.continuousAt
    have hf := tendsto_iff_tendstoInMeasure.mp (continuous_snd.continuousAt (x := p))
    exact tendsto_iff_tendstoInMeasure.mpr <|
      (hc.smul_tendstoInMeasure p.2.aestronglyMeasurable hf).congr
        (fun q ↦ (coeFn_smul q.1 q.2).symm) (coeFn_smul p.1 p.2).symm

/-- On a finite measure space, bounded pointwise multiplication on `L0 R μ` is jointly
continuous. -/
instance instContinuousMul [Zero R] [Mul R] [PseudoMetricSpace R] [ContinuousMul R]
    [IsBoundedSMul R R] : ContinuousMul (L0 R μ) where
  continuous_mul := continuous_iff_continuousAt.mpr fun p ↦ by
    have h₁ := tendsto_iff_tendstoInMeasure.mp (continuous_fst.continuousAt (x := p))
    have h₂ := tendsto_iff_tendstoInMeasure.mp (continuous_snd.continuousAt (x := p))
    exact tendsto_iff_tendstoInMeasure.mpr <|
      (h₁.mul p.1.aestronglyMeasurable p.2.aestronglyMeasurable h₂).congr
        (fun q ↦ (coeFn_mul q.1 q.2).symm) (coeFn_mul p.1 p.2).symm

/-- On a finite measure space, `L0 R μ` is a topological semiring when `R` has Lipschitz addition
and bounded multiplication (`IsBoundedSMul R R`). -/
instance instIsTopologicalSemiring [Semiring R] [PseudoMetricSpace R] [IsTopologicalSemiring R]
    [LipschitzAdd R] [IsBoundedSMul R R] : IsTopologicalSemiring (L0 R μ) :=
  ⟨⟩

/-- On a finite measure space, `L0 R μ` is a topological ring when `R` is a uniform additive group
with bounded multiplication (`IsBoundedSMul R R`). -/
instance instIsTopologicalRing [Ring R] [PseudoMetricSpace R] [IsTopologicalRing R]
    [IsUniformAddGroup R] [IsBoundedSMul R R] : IsTopologicalRing (L0 R μ) :=
  { toIsTopologicalSemiring := ⟨⟩ }

end TopologicalAlgebra

section LpEmbedding

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞}

/-- Canonical inclusion of `Lp E p μ` into `L0 E μ`, forgetting the `Lᵖ`-integrability bound while
preserving the underlying `AEEqFun` equivalence class. -/
def ofLp (f : Lp E p μ) : L0 E μ :=
  ofAEEqFun f.1

@[simp]
theorem toAEEqFun_ofLp (f : Lp E p μ) : (ofLp f).toAEEqFun = f.1 := by
  rfl

@[simp]
theorem coeFn_ofLp (f : Lp E p μ) : ⇑(ofLp f) = ⇑f := by
  rw [← coeFn_toAEEqFun, toAEEqFun_ofLp]

/-- `L0.ofLp` is injective. -/
theorem ofLp_injective : Function.Injective (ofLp : Lp E p μ → L0 E μ) :=
  fun _ _ h ↦ Subtype.ext (by simpa only [toAEEqFun_ofLp] using congrArg toAEEqFun h)

@[simp]
theorem ofLp_inj (f g : Lp E p μ) : ofLp f = ofLp g ↔ f = g :=
  ofLp_injective.eq_iff

@[simp]
theorem ofLp_zero : ofLp (0 : Lp E p μ) = 0 :=
  toAEEqFun_injective (by rw [toAEEqFun_ofLp, toAEEqFun_zero, AddSubgroup.coe_zero])

@[simp]
theorem ofLp_eq_zero (f : Lp E p μ) : ofLp f = 0 ↔ f = 0 := by
  rw [← ofLp_zero, ofLp_inj]

@[simp]
theorem ofLp_const [IsFiniteMeasure μ] (c : E) : ofLp (Lp.const p μ c) = const α c :=
  toAEEqFun_injective (by rw [toAEEqFun_ofLp, Lp.const_val, toAEEqFun_const])

@[simp]
theorem ofLp_toLp {f : α → E} (hf : MemLp f p μ) :
    ofLp (hf.toLp f) = mk f hf.aestronglyMeasurable :=
  toAEEqFun_injective (by rw [toAEEqFun_ofLp, MemLp.toLp_val, toAEEqFun_mk])

@[simp]
theorem ofLp_add (f g : Lp E p μ) : ofLp (f + g) = ofLp f + ofLp g :=
  toAEEqFun_injective (by
    rw [toAEEqFun_ofLp, toAEEqFun_add, toAEEqFun_ofLp, toAEEqFun_ofLp, AddSubgroup.coe_add])

@[simp]
theorem ofLp_neg (f : Lp E p μ) : ofLp (-f) = -ofLp f :=
  toAEEqFun_injective (by rw [toAEEqFun_ofLp, toAEEqFun_neg, toAEEqFun_ofLp, AddSubgroup.coe_neg])

@[simp]
theorem ofLp_sub (f g : Lp E p μ) : ofLp (f - g) = ofLp f - ofLp g :=
  toAEEqFun_injective (by
    rw [toAEEqFun_ofLp, toAEEqFun_sub, toAEEqFun_ofLp, toAEEqFun_ofLp, AddSubgroup.coe_sub])

@[simp]
theorem ofLp_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (c : 𝕜) (f : Lp E p μ) : ofLp (c • f) = c • ofLp f := by
  refine ext ?_
  filter_upwards [Lp.coeFn_smul c f, coeFn_smul c (ofLp f)] with x h₁ h₂
  rw [coeFn_ofLp, h₁, h₂, Pi.smul_apply, Pi.smul_apply, coeFn_ofLp]

/-- `L0.ofLp` bundled as an additive monoid homomorphism. -/
def ofLpAddMonoidHom : Lp E p μ →+ L0 E μ where
  toFun := ofLp
  map_zero' := ofLp_zero
  map_add' := ofLp_add

@[simp]
theorem ofLpAddMonoidHom_apply (f : Lp E p μ) : ofLpAddMonoidHom f = ofLp f := by
  rfl

/-- `L0.ofLp` bundled as a `𝕜`-linear map. -/
def ofLpLinearMap (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    Lp E p μ →ₗ[𝕜] L0 E μ where
  toFun := ofLp
  map_add' := ofLp_add
  map_smul' := ofLp_smul

@[simp]
theorem ofLpLinearMap_apply {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : Lp E p μ) : ofLpLinearMap 𝕜 f = ofLp f := by
  rfl

/-- **Continuity of the `Lᵖ ↪ L⁰` inclusion.** For `1 ≤ p` and a finite measure `μ`, the canonical
inclusion `Lp E p μ → L0 E μ` is continuous. -/
@[fun_prop]
theorem continuous_ofLp [Fact (1 ≤ p)] [IsFiniteMeasure μ] :
    Continuous (ofLp : Lp E p μ → L0 E μ) :=
  continuous_iff_continuousAt.mpr fun f ↦ by
    rw [ContinuousAt, tendsto_iff_tendstoInMeasure]
    simp_rw [coeFn_ofLp]
    exact tendstoInMeasure_of_tendsto_Lp (continuousAt_id (x := f))

/-- Continuous `𝕜`-linear embedding of `Lp E p μ` into `L0 E μ` for `1 ≤ p` on a finite measure
space. -/
def ofLpCLM (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    [IsFiniteMeasure μ] : Lp E p μ →L[𝕜] L0 E μ where
  toLinearMap := ofLpLinearMap 𝕜
  cont := continuous_ofLp

@[simp]
theorem ofLpCLM_apply {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    [IsFiniteMeasure μ] (f : Lp E p μ) : ofLpCLM 𝕜 f = ofLp f := by
  rfl

end LpEmbedding

section ConstAndIndicator

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- In `L0 ℝ μ` on a finite measure space, the distance from the natural-number constant class
`(n : L0 ℝ μ)` to `0` converges to the total mass `μ.real Set.univ` as `n → ∞`. -/
theorem tendsto_dist_natCast_zero_nhds_measureReal_univ [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ ↦ dist (n : L0 ℝ μ) 0) atTop (𝓝 (μ.real Set.univ)) := by
  have hratio : Tendsto (fun n : ℕ ↦ (n : ℝ) / (1 + (n : ℝ))) atTop (𝓝 1) := by
    simpa only [add_comm] using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hmul : Tendsto (fun n : ℕ ↦ μ.real Set.univ * ((n : ℝ) / (1 + (n : ℝ)))) atTop
      (𝓝 (μ.real Set.univ)) := by
    simpa only [mul_one] using hratio.const_mul (μ.real Set.univ)
  refine hmul.congr fun n ↦ ?_
  rw [natCast_def, ← const_zero, dist_const_const, Real.dist_eq, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg n)]

/-- On a nonzero finite measure space, the sequence of constant classes `(n : L0 ℝ μ)` diverges in
`L0 ℝ μ`, even though `L0 ℝ μ` is bounded in diameter by `μ.real Set.univ`. -/
theorem not_exists_tendsto_natCast [IsFiniteMeasure μ] [NeZero μ] :
    ¬ ∃ f : L0 ℝ μ, Tendsto (fun n : ℕ ↦ (n : L0 ℝ μ)) atTop (𝓝 f) := by
  rintro ⟨f, hf⟩
  obtain ⟨ns, hns, hae⟩ := exists_seq_tendsto_ae_of_tendsto hf
  have hbot : ∀ᵐ _ ∂μ, False := by
    refine hae.mono fun x hx ↦ ?_
    simp only [coeFn_natCast_eq] at hx
    exact not_tendsto_nhds_of_tendsto_atTop
      (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop) _ hx
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hbot))

/-- Class in `L0 E μ` of the indicator `s.indicator (fun _ ↦ c)` of a null-measurable set `s`.
Unlike `MeasureTheory.indicatorConstLp`, no finiteness hypothesis on `μ s` is required. -/
def indicatorConst [TopologicalSpace E] [Zero E] {s : Set α} (hs : NullMeasurableSet s μ) (c : E) :
    L0 E μ :=
  mk (s.indicator fun _ ↦ c) (aestronglyMeasurable_const.indicator₀ hs)

/-- `indicatorConst hs c` is the `L0.mk` class of `s.indicator (fun _ ↦ c)`. -/
theorem indicatorConst_eq_mk [TopologicalSpace E] [Zero E] {s : Set α}
    (hs : NullMeasurableSet s μ) (c : E) :
    indicatorConst hs c =
      mk (s.indicator fun _ ↦ c) (aestronglyMeasurable_const.indicator₀ hs) := by
  rfl

@[simp]
theorem toAEEqFun_indicatorConst [TopologicalSpace E] [Zero E] {s : Set α}
    (hs : NullMeasurableSet s μ) (c : E) :
    (indicatorConst hs c).toAEEqFun =
      AEEqFun.mk (s.indicator fun _ ↦ c) (aestronglyMeasurable_const.indicator₀ hs) := by
  rw [indicatorConst_eq_mk, toAEEqFun_mk]

/-- The representative of `indicatorConst hs c` agrees with `s.indicator (fun _ ↦ c)` almost
everywhere. -/
theorem coeFn_indicatorConst [TopologicalSpace E] [Zero E] {s : Set α}
    (hs : NullMeasurableSet s μ) (c : E) :
    (indicatorConst hs c : α → E) =ᵐ[μ] s.indicator fun _ ↦ c := by
  rw [indicatorConst_eq_mk]
  exact coeFn_mk _ _

@[simp]
theorem indicatorConst_empty [TopologicalSpace E] [Zero E]
    (hs : NullMeasurableSet (∅ : Set α) μ) (c : E) :
    indicatorConst hs c = 0 := by
  rw [indicatorConst_eq_mk, ← const_zero, ← mk_const, mk_eq_mk]
  simp

@[simp]
theorem indicatorConst_zero [TopologicalSpace E] [Zero E] {s : Set α}
    (hs : NullMeasurableSet s μ) :
    indicatorConst hs (0 : E) = 0 := by
  rw [indicatorConst_eq_mk, ← const_zero, ← mk_const, mk_eq_mk]
  simp

@[simp]
theorem indicatorConst_univ [TopologicalSpace E] [Zero E]
    (hs : NullMeasurableSet (Set.univ : Set α) μ) (c : E) :
    indicatorConst hs c = const α c := by
  rw [indicatorConst_eq_mk, ← mk_const, mk_eq_mk]
  simp

/-- `indicatorConst` commutes with addition in the constant value. -/
theorem indicatorConst_add [TopologicalSpace E] [AddZeroClass E] [ContinuousAdd E] {s : Set α}
    (hs : NullMeasurableSet s μ) (c c' : E) :
    indicatorConst hs (c + c') = indicatorConst hs c + indicatorConst hs c' := by
  rw [indicatorConst_eq_mk, indicatorConst_eq_mk, indicatorConst_eq_mk, mk_add_mk, mk_eq_mk]
  exact Filter.EventuallyEq.of_eq (Set.indicator_add _ _ _)

/-- `indicatorConst` commutes with negation in the constant value. -/
theorem indicatorConst_neg [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] {s : Set α}
    (hs : NullMeasurableSet s μ) (c : E) :
    indicatorConst hs (-c) = -indicatorConst hs c := by
  rw [indicatorConst_eq_mk, indicatorConst_eq_mk, neg_mk, mk_eq_mk]
  exact Filter.EventuallyEq.of_eq (Set.indicator_neg _ _)

/-- `indicatorConst` commutes with subtraction in the constant value. -/
theorem indicatorConst_sub [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] {s : Set α}
    (hs : NullMeasurableSet s μ) (c c' : E) :
    indicatorConst hs (c - c') = indicatorConst hs c - indicatorConst hs c' := by
  rw [indicatorConst_eq_mk, indicatorConst_eq_mk, indicatorConst_eq_mk, mk_sub_mk, mk_eq_mk]
  exact Filter.EventuallyEq.of_eq (Set.indicator_sub _ _ _)

/-- Scalar multiplication commutes with `indicatorConst`. -/
theorem smul_indicatorConst {𝕜 : Type*} [TopologicalSpace E] [Zero E] [SMulZeroClass 𝕜 E]
    [ContinuousConstSMul 𝕜 E] {s : Set α} (hs : NullMeasurableSet s μ) (a : 𝕜) (c : E) :
    a • indicatorConst hs c = indicatorConst hs (a • c) := by
  rw [indicatorConst_eq_mk, indicatorConst_eq_mk, smul_mk, mk_eq_mk]
  exact Filter.EventuallyEq.of_eq (Set.indicator_const_smul s a fun _ ↦ c).symm

@[simp]
theorem ofLp_indicatorConstLp [NormedAddCommGroup E] {p : ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    ofLp (indicatorConstLp p hs hμs c) = indicatorConst hs.nullMeasurableSet c := by
  refine ext ?_
  rw [coeFn_ofLp]
  exact (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)).trans
    (coeFn_indicatorConst hs.nullMeasurableSet c).symm

/-- Closed-form `L⁰` distance from an indicator-constant class `indicatorConst hs c` to `0`:
`dist (indicatorConst hs c) 0 = μ.real s * (dist c 0 / (1 + dist c 0))`. -/
theorem dist_indicatorConst_zero [PseudoMetricSpace E] [Zero E] [IsFiniteMeasure μ] {s : Set α}
    (hs : NullMeasurableSet s μ) (c : E) :
    dist (indicatorConst hs c) 0 = μ.real s * (dist c 0 / (1 + dist c 0)) := by
  rw [indicatorConst_eq_mk, ← const_zero, ← mk_const, dist_mk_mk]
  have hpt : (fun x ↦ dist (s.indicator (fun _ : α ↦ c) x) 0 /
      (1 + dist (s.indicator (fun _ : α ↦ c) x) 0)) =
      s.indicator (fun _ : α ↦ dist c 0 / (1 + dist c 0)) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hpt, integral_indicator₀ hs, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]

/-- The real measure of the support `{x | indicatorConst hs c x ≠ 0}` equals `μ.real s` whenever
`c ≠ 0`. -/
theorem measureReal_indicatorConst_ne_zero [TopologicalSpace E] [Zero E] {s : Set α}
    (hs : NullMeasurableSet s μ) {c : E} (hc : c ≠ 0) :
    μ.real {x | indicatorConst hs c x ≠ 0} = μ.real s := by
  refine measureReal_congr ?_
  filter_upwards [coeFn_indicatorConst hs c] with x hx
  rw [Set.mem_ofPred_eq, hx, Set.indicator_apply_ne_zero]
  simp [hc]

/-- For a unit-height real indicator `1_s`, `dist (indicatorConst hs 1) 0 = μ.real s / 2`, half of
the disagreement measure `μ.real {x | indicatorConst hs 1 x ≠ 0} = μ.real s`. -/
theorem dist_indicatorConst_one_zero [IsFiniteMeasure μ] {s : Set α}
    (hs : NullMeasurableSet s μ) :
    dist (indicatorConst hs (1 : ℝ)) 0 = μ.real s / 2 := by
  rw [dist_indicatorConst_zero hs (1 : ℝ)]
  norm_num
  ring

end ConstAndIndicator

end L0

end TauCeti
