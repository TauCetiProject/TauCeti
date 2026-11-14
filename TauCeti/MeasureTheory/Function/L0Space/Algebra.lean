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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Algebraic, topological-algebraic, and `Lᵖ`-embedding structure on `L⁰(μ; E)`

Pointwise algebraic and order operations on `α →ₘ[μ] E` (`MeasureTheory.AEEqFun`) transfer along
`TauCeti.L0.equivAEEqFun` to `TauCeti.L0 E μ` for an arbitrary measure `μ`, giving additive group,
module, (commutative) semiring, (commutative) ring, algebra, and lattice instances together with
bundled equivalences (`addEquivAEEqFun`, `linearEquivAEEqFun`, `ringEquivAEEqFun`,
`algEquivAEEqFun`).

On a finite measure space, combining `TauCeti.L0.tendsto_iff_tendstoInMeasure` with the algebraic
stability of `MeasureTheory.TendstoInMeasure` upgrades `L0 E μ` to a topological additive group,
gives joint continuity of bounded scalar multiplication (`ContinuousSMul 𝕜 (L0 E μ)`), and makes
`L0 R μ` a topological (semi)ring whenever `R` is a seminormed ring.

For $1 \le p \le \infty$, the canonical inclusion `TauCeti.L0.ofLp : Lp E p μ → L0 E μ` is
continuous on finite measure spaces (`TauCeti.L0.continuous_ofLp`) via
`MeasureTheory.tendstoInMeasure_of_tendsto_Lp`, and bundles as a continuous linear map
`TauCeti.L0.ofLpCLM`. Closed-form distance formulas for constant classes (`dist_const_const`) and
indicator-constant classes (`dist_indicatorConst_zero`, `dist_indicatorConst_one_zero`) evaluate
the `L⁰` metric explicitly on constants and measurable indicators, showing in particular that the
sequence of natural-number constant classes `(n : L0 ℝ μ)` has distance to `0` tending to
`μ.real Set.univ` (`tendsto_dist_natCast_zero`) and diverges whenever `μ ≠ 0`
(`not_exists_tendsto_natCast`).

## Main declarations

* `TauCeti.L0.addEquivAEEqFun`, `linearEquivAEEqFun`, `ringEquivAEEqFun`, `algEquivAEEqFun`:
  algebraic equivalences between `L0` and `MeasureTheory.AEEqFun`.
* `TauCeti.L0.instIsTopologicalAddGroup`, `instContinuousSMul`, `instIsTopologicalSemiring`,
  `instIsTopologicalRing`: continuity of addition, negation, scalar multiplication, and
  multiplication on `L0` over finite measure spaces.
* `TauCeti.L0.ofLp`, `TauCeti.L0.continuous_ofLp`, `TauCeti.L0.ofLpCLM`,
  `MeasureTheory.MemLp.toL0`: continuous linear inclusion of `Lp E p μ` into `L0 E μ` for
  `1 ≤ p`.
* `TauCeti.L0.indicatorConst`, `TauCeti.L0.dist_const_const`,
  `TauCeti.L0.dist_indicatorConst_zero`: closed-form `L⁰` distances for constants and indicators.
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

instance instInhabited [Inhabited E] : Inhabited (L0 E μ) :=
  ⟨ofAEEqFun default⟩

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
def addEquivAEEqFun [AddMonoid E] [ContinuousAdd E] : L0 E μ ≃+ (α →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun
  map_add' := toAEEqFun_add

@[simp]
theorem addEquivAEEqFun_apply [AddMonoid E] [ContinuousAdd E] (f : L0 E μ) :
    addEquivAEEqFun f = f.toAEEqFun := by
  rfl

@[simp]
theorem addEquivAEEqFun_symm_apply [AddMonoid E] [ContinuousAdd E] (f : α →ₘ[μ] E) :
    addEquivAEEqFun.symm f = ofAEEqFun f := by
  rfl

instance instMulAction [Monoid 𝕜] [MulAction 𝕜 E] [ContinuousConstSMul 𝕜 E] :
    MulAction 𝕜 (L0 E μ) :=
  toAEEqFun_injective.mulAction toAEEqFun toAEEqFun_smul

instance instDistribMulAction [Monoid 𝕜] [AddMonoid E] [ContinuousAdd E] [DistribMulAction 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : DistribMulAction 𝕜 (L0 E μ) :=
  let toAEEqFunHom : L0 E μ →+ (α →ₘ[μ] E) :=
    { toFun := toAEEqFun, map_zero' := toAEEqFun_zero, map_add' := toAEEqFun_add }
  toAEEqFun_injective.distribMulAction toAEEqFunHom toAEEqFun_smul

instance instModule [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : Module 𝕜 (L0 E μ) :=
  let toAEEqFunHom : L0 E μ →+ (α →ₘ[μ] E) :=
    { toFun := toAEEqFun, map_zero' := toAEEqFun_zero, map_add' := toAEEqFun_add }
  toAEEqFun_injective.module 𝕜 toAEEqFunHom toAEEqFun_smul

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
def ringEquivAEEqFun [Semiring R] [IsTopologicalSemiring R] : L0 R μ ≃+* (α →ₘ[μ] R) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun
  map_mul' := toAEEqFun_mul
  map_add' := toAEEqFun_add

@[simp]
theorem ringEquivAEEqFun_apply [Semiring R] [IsTopologicalSemiring R] (f : L0 R μ) :
    ringEquivAEEqFun f = f.toAEEqFun := by
  rfl

@[simp]
theorem ringEquivAEEqFun_symm_apply [Semiring R] [IsTopologicalSemiring R] (f : α →ₘ[μ] R) :
    ringEquivAEEqFun.symm f = ofAEEqFun f := by
  rfl

instance instAlgebra [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    [ContinuousConstSMul 𝕜 R] : Algebra 𝕜 (L0 R μ) where
  algebraMap :=
    { toFun c := ofAEEqFun (algebraMap 𝕜 (α →ₘ[μ] R) c)
      map_one' := toAEEqFun_injective (by rw [toAEEqFun_ofAEEqFun, map_one, toAEEqFun_one])
      map_mul' a b := toAEEqFun_injective (by
        rw [toAEEqFun_ofAEEqFun, map_mul, toAEEqFun_mul, toAEEqFun_ofAEEqFun,
          toAEEqFun_ofAEEqFun])
      map_zero' := toAEEqFun_injective (by rw [toAEEqFun_ofAEEqFun, map_zero, toAEEqFun_zero])
      map_add' a b := toAEEqFun_injective (by
        rw [toAEEqFun_ofAEEqFun, map_add, toAEEqFun_add, toAEEqFun_ofAEEqFun,
          toAEEqFun_ofAEEqFun]) }
  commutes' c f := toAEEqFun_injective (by
    rw [toAEEqFun_mul, toAEEqFun_mul, toAEEqFun_ofAEEqFun]
    exact Algebra.commutes c f.toAEEqFun)
  smul_def' c f := toAEEqFun_injective (by
    rw [toAEEqFun_smul, toAEEqFun_mul, toAEEqFun_ofAEEqFun]
    exact Algebra.smul_def c f.toAEEqFun)

/-- `toAEEqFun` commutes with `algebraMap` from `𝕜`. -/
theorem toAEEqFun_algebraMap [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    [ContinuousConstSMul 𝕜 R] (c : 𝕜) :
    (algebraMap 𝕜 (L0 R μ) c).toAEEqFun = algebraMap 𝕜 (α →ₘ[μ] R) c :=
  toAEEqFun_ofAEEqFun _

@[simp]
theorem algebraMap_apply [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    [ContinuousConstSMul 𝕜 R] (c : 𝕜) :
    algebraMap 𝕜 (L0 R μ) c = const α (algebraMap 𝕜 R c) :=
  toAEEqFun_injective (by rw [toAEEqFun_algebraMap, AEEqFun.algebraMap_apply, toAEEqFun_const])

/-- Canonical `𝕜`-algebra equivalence between `L0 R μ` and `α →ₘ[μ] R`. -/
def algEquivAEEqFun (𝕜 : Type*) [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R]
    [Algebra 𝕜 R] [ContinuousConstSMul 𝕜 R] : L0 R μ ≃ₐ[𝕜] (α →ₘ[μ] R) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun
  map_mul' := toAEEqFun_mul
  map_add' := toAEEqFun_add
  commutes' := toAEEqFun_algebraMap

@[simp]
theorem algEquivAEEqFun_apply [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R]
    [Algebra 𝕜 R] [ContinuousConstSMul 𝕜 R] (f : L0 R μ) :
    algEquivAEEqFun 𝕜 f = f.toAEEqFun := by
  rfl

@[simp]
theorem algEquivAEEqFun_symm_apply [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R]
    [Algebra 𝕜 R] [ContinuousConstSMul 𝕜 R] (f : α →ₘ[μ] R) :
    (algEquivAEEqFun (R := R) (μ := μ) 𝕜).symm f = ofAEEqFun f := by
  rfl

end Ring

section Order

variable [TopologicalSpace E]

instance instLE [Preorder E] : LE (L0 E μ) :=
  ⟨fun f g ↦ f.toAEEqFun ≤ g.toAEEqFun⟩

/-- Order on `L0 E μ` is the almost-everywhere pointwise order inherited from `α →ₘ[μ] E`. -/
theorem le_def [Preorder E] {f g : L0 E μ} : f ≤ g ↔ f.toAEEqFun ≤ g.toAEEqFun :=
  (Iff.rfl)

@[simp]
theorem coeFn_le [Preorder E] {f g : L0 E μ} : (f : α → E) ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← coeFn_toAEEqFun, ← coeFn_toAEEqFun, AEEqFun.coeFn_le, le_def]

instance instPartialOrder [PartialOrder E] : PartialOrder (L0 E μ) :=
  PartialOrder.lift toAEEqFun toAEEqFun_injective

instance instSup [SemilatticeSup E] [ContinuousSup E] : Max (L0 E μ) :=
  ⟨fun f g ↦ ofAEEqFun (f.toAEEqFun ⊔ g.toAEEqFun)⟩

instance instInf [SemilatticeInf E] [ContinuousInf E] : Min (L0 E μ) :=
  ⟨fun f g ↦ ofAEEqFun (f.toAEEqFun ⊓ g.toAEEqFun)⟩

/-- Representative of `f ⊔ g` in `L0 E μ` agrees with `fun x ↦ f x ⊔ g x` almost everywhere. -/
theorem coeFn_sup [SemilatticeSup E] [ContinuousSup E] (f g : L0 E μ) :
    ⇑(f ⊔ g) =ᵐ[μ] fun x ↦ f x ⊔ g x := by
  simp_rw [← coeFn_toAEEqFun]
  exact AEEqFun.coeFn_sup f.toAEEqFun g.toAEEqFun

/-- Representative of `f ⊓ g` in `L0 E μ` agrees with `fun x ↦ f x ⊓ g x` almost everywhere. -/
theorem coeFn_inf [SemilatticeInf E] [ContinuousInf E] (f g : L0 E μ) :
    ⇑(f ⊓ g) =ᵐ[μ] fun x ↦ f x ⊓ g x := by
  simp_rw [← coeFn_toAEEqFun]
  exact AEEqFun.coeFn_inf f.toAEEqFun g.toAEEqFun

instance instLattice [Lattice E] [TopologicalLattice E] : Lattice (L0 E μ) where
  __ := instPartialOrder
  sup := max
  le_sup_left f g := AEEqFun.le_sup_left f.toAEEqFun g.toAEEqFun
  le_sup_right f g := AEEqFun.le_sup_right f.toAEEqFun g.toAEEqFun
  sup_le f g h := AEEqFun.sup_le f.toAEEqFun g.toAEEqFun h.toAEEqFun
  inf := min
  inf_le_left f g := AEEqFun.inf_le_left f.toAEEqFun g.toAEEqFun
  inf_le_right f g := AEEqFun.inf_le_right f.toAEEqFun g.toAEEqFun
  le_inf f g h := AEEqFun.le_inf f.toAEEqFun g.toAEEqFun h.toAEEqFun

end Order

end Algebra

section TopologicalAlgebra

variable {α 𝕜 E R : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]

/-- Translation invariance on the left of the `L⁰` metric for seminormed group targets. -/
@[simp]
theorem dist_add_left [SeminormedAddCommGroup E] (h f g : L0 E μ) :
    dist (h + f) (h + g) = dist f g := by
  rw [dist_def, dist_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_add h f, coeFn_add h g] with x hhf hhg
  simp [hhf, hhg]

/-- Translation invariance on the right of the `L⁰` metric for seminormed group targets. -/
@[simp]
theorem dist_add_right [SeminormedAddCommGroup E] (f g h : L0 E μ) :
    dist (f + h) (g + h) = dist f g := by
  rw [add_comm f h, add_comm g h, dist_add_left]

/-- Negation is an isometry of `L0 E μ` for seminormed group targets. -/
@[simp]
theorem dist_neg_neg [SeminormedAddCommGroup E] (f g : L0 E μ) :
    dist (-f) (-g) = dist f g := by
  rw [dist_def, dist_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_neg f, coeFn_neg g] with x hf hg
  simp [hf, hg]

/-- In `L0 E μ` over a seminormed group, `dist f g = dist (f - g) 0`. -/
theorem dist_eq_dist_sub_zero [SeminormedAddCommGroup E] (f g : L0 E μ) :
    dist f g = dist (f - g) 0 := by
  simpa [sub_eq_add_neg] using (dist_add_right f g (-g)).symm

instance instContinuousAdd [AddGroup E] [PseudoMetricSpace E] [IsUniformAddGroup E] :
    ContinuousAdd (L0 E μ) where
  continuous_add := continuous_iff_continuousAt.mpr fun p ↦ by
    have h₁ := tendsto_iff_tendstoInMeasure.mp (continuous_fst.continuousAt (x := p))
    have h₂ := tendsto_iff_tendstoInMeasure.mp (continuous_snd.continuousAt (x := p))
    exact tendsto_iff_tendstoInMeasure.mpr <|
      (h₁.add h₂).congr (fun q ↦ (coeFn_add q.1 q.2).symm) (coeFn_add p.1 p.2).symm

instance instContinuousNeg [AddGroup E] [PseudoMetricSpace E] [IsUniformAddGroup E] :
    ContinuousNeg (L0 E μ) where
  continuous_neg := continuous_iff_continuousAt.mpr fun f ↦ by
    have h := tendsto_iff_tendstoInMeasure.mp (continuousAt_id (x := f))
    exact tendsto_iff_tendstoInMeasure.mpr <|
      h.neg.congr (fun g ↦ (coeFn_neg g).symm) (coeFn_neg f).symm

instance instIsTopologicalAddGroup [AddGroup E] [PseudoMetricSpace E] [IsUniformAddGroup E] :
    IsTopologicalAddGroup (L0 E μ) :=
  ⟨⟩

instance instContinuousSMul [Zero 𝕜] [Zero E] [PseudoMetricSpace 𝕜] [PseudoMetricSpace E]
    [SMul 𝕜 E] [IsBoundedSMul 𝕜 E] : ContinuousSMul 𝕜 (L0 E μ) where
  continuous_smul := continuous_iff_continuousAt.mpr fun p ↦ by
    have hc : Tendsto (fun q : 𝕜 × L0 E μ ↦ q.1) (𝓝 p) (𝓝 p.1) := continuous_fst.continuousAt
    have hf := tendsto_iff_tendstoInMeasure.mp (continuous_snd.continuousAt (x := p))
    exact tendsto_iff_tendstoInMeasure.mpr <|
      (hc.smul_tendstoInMeasure p.2.aestronglyMeasurable hf).congr
        (fun q ↦ (coeFn_smul q.1 q.2).symm) (coeFn_smul p.1 p.2).symm

instance instContinuousMul [NonUnitalSeminormedRing R] : ContinuousMul (L0 R μ) where
  continuous_mul := continuous_iff_continuousAt.mpr fun p ↦ by
    have h₁ := tendsto_iff_tendstoInMeasure.mp (continuous_fst.continuousAt (x := p))
    have h₂ := tendsto_iff_tendstoInMeasure.mp (continuous_snd.continuousAt (x := p))
    exact tendsto_iff_tendstoInMeasure.mpr <|
      (h₁.mul p.1.aestronglyMeasurable p.2.aestronglyMeasurable h₂).congr
        (fun q ↦ (coeFn_mul q.1 q.2).symm) (coeFn_mul p.1 p.2).symm

instance instIsTopologicalSemiring [SeminormedRing R] : IsTopologicalSemiring (L0 R μ) :=
  ⟨⟩

instance instIsTopologicalRing [SeminormedRing R] : IsTopologicalRing (L0 R μ) :=
  ⟨⟩

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
theorem ofLp_zero : ofLp (0 : Lp E p μ) = 0 := by
  rfl

@[simp]
theorem ofLp_add (f g : Lp E p μ) : ofLp (f + g) = ofLp f + ofLp g := by
  rfl

@[simp]
theorem ofLp_neg (f : Lp E p μ) : ofLp (-f) = -ofLp f := by
  rfl

@[simp]
theorem ofLp_sub (f g : Lp E p μ) : ofLp (f - g) = ofLp f - ofLp g := by
  rfl

@[simp]
theorem ofLp_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (c : 𝕜) (f : Lp E p μ) : ofLp (c • f) = c • ofLp f := by
  rfl

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

end L0

end TauCeti

namespace MeasureTheory.MemLp

/-- Project a function `f` satisfying `MemLp f p μ` to its class in `TauCeti.L0 E μ`. -/
def toL0 {α E : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : α → E} (hf : MemLp f p μ) : TauCeti.L0 E μ :=
  TauCeti.L0.mk f hf.aestronglyMeasurable

/-- The representative of `hf.toL0` agrees with `f` almost everywhere. -/
theorem coeFn_toL0 {α E : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : α → E} (hf : MemLp f p μ) : (hf.toL0 : α → E) =ᵐ[μ] f :=
  TauCeti.L0.coeFn_mk f hf.aestronglyMeasurable

@[simp]
theorem ofLp_toLp {α E : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : α → E} (hf : MemLp f p μ) : TauCeti.L0.ofLp (hf.toLp f) = hf.toL0 := by
  apply TauCeti.L0.ext
  rw [TauCeti.L0.coeFn_ofLp]
  exact hf.coeFn_toLp.trans hf.coeFn_toL0.symm

end MeasureTheory.MemLp

namespace TauCeti.L0

section ConstAndIndicator

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- When `μ = 0`, `L0 E μ` is a subsingleton. -/
theorem subsingleton_of_measure_zero [TopologicalSpace E] (hμ : μ = 0) :
    Subsingleton (L0 E μ) :=
  ⟨fun f g ↦ ext (by simp [EventuallyEq, hμ])⟩

/-- On the zero measure, every `L⁰` distance is `0`. -/
theorem dist_eq_zero_of_measure_zero [PseudoMetricSpace E] [IsFiniteMeasure μ] (hμ : μ = 0)
    (f g : L0 E μ) : dist f g = 0 := by
  have := subsingleton_of_measure_zero (E := E) hμ
  rw [Subsingleton.elim f g, dist_self]

/-- Closed-form `L⁰` distance between two constant classes on a finite measure space:
`dist (const α a) (const α b) = μ.real Set.univ * (dist a b / (1 + dist a b))`. -/
theorem dist_const_const [PseudoMetricSpace E] [IsFiniteMeasure μ] (a b : E) :
    dist (const (μ := μ) α a) (const (μ := μ) α b) =
      μ.real Set.univ * (dist a b / (1 + dist a b)) := by
  rw [dist_def]
  have hcongr : (fun x ↦ dist (const (μ := μ) α a x) (const (μ := μ) α b x) /
      (1 + dist (const (μ := μ) α a x) (const (μ := μ) α b x))) =ᵐ[μ]
      fun _ : α ↦ dist a b / (1 + dist a b) := by
    filter_upwards [coeFn_const (μ := μ) α a, coeFn_const (μ := μ) α b] with x ha hb
    rw [ha, hb]
    rfl
  rw [integral_congr_ae hcongr, integral_const, smul_eq_mul]

/-- In `L0 ℝ μ` on a finite measure space, the distance from the natural-number constant class
`(n : L0 ℝ μ)` to `0` converges to the total mass `μ.real Set.univ` as `n → ∞`. -/
theorem tendsto_dist_natCast_zero [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ ↦ dist (n : L0 ℝ μ) 0) atTop (𝓝 (μ.real Set.univ)) := by
  have hratio : Tendsto (fun n : ℕ ↦ (n : ℝ) / (1 + (n : ℝ))) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ ↦ 1 - (1 + (n : ℝ))⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub <| by
        simpa only [Function.comp_def] using
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)
    rw [sub_zero] at hinv
    refine hinv.congr fun n ↦ ?_
    have hpos : (0 : ℝ) < 1 + (n : ℝ) := by positivity
    field_simp [hpos.ne']
    ring
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
  obtain ⟨ns, hns, hae⟩ := exists_seq_tendsto_ae hf
  have hbot : ∀ᵐ _ ∂μ, False := by
    refine hae.mono fun x hx ↦ ?_
    simp only [coeFn_natCast_eq] at hx
    exact not_tendsto_nhds_of_tendsto_atTop
      (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop) _ hx
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hbot))

/-- Class in `L0 E μ` of the indicator `s.indicator (fun _ ↦ c)` of a measurable set `s`. Unlike
`MeasureTheory.indicatorConstLp`, no finiteness hypothesis on `μ s` is required. -/
def indicatorConst [TopologicalSpace E] [Zero E] {s : Set α} (hs : MeasurableSet s) (c : E) :
    L0 E μ :=
  mk (s.indicator fun _ ↦ c) (stronglyMeasurable_const.indicator hs).aestronglyMeasurable

/-- The representative of `indicatorConst hs c` agrees with `s.indicator (fun _ ↦ c)` almost
everywhere. -/
theorem coeFn_indicatorConst [TopologicalSpace E] [Zero E] {s : Set α} (hs : MeasurableSet s)
    (c : E) : (indicatorConst (μ := μ) hs c : α → E) =ᵐ[μ] s.indicator fun _ ↦ c :=
  coeFn_mk _ _

@[simp]
theorem ofLp_indicatorConstLp [NormedAddCommGroup E] {p : ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    ofLp (indicatorConstLp p hs hμs c) = indicatorConst hs c := by
  refine ext ?_
  rw [coeFn_ofLp]
  exact (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)).trans
    (coeFn_indicatorConst hs c).symm

/-- Closed-form `L⁰` distance from an indicator-constant class `indicatorConst hs c` to `0`:
`dist (indicatorConst hs c) 0 = μ.real s * (dist c 0 / (1 + dist c 0))`. -/
theorem dist_indicatorConst_zero [PseudoMetricSpace E] [Zero E] [IsFiniteMeasure μ] {s : Set α}
    (hs : MeasurableSet s) (c : E) :
    dist (indicatorConst (μ := μ) hs c) 0 = μ.real s * (dist c 0 / (1 + dist c 0)) := by
  rw [indicatorConst, ← const_zero, ← mk_const, dist_mk_mk]
  have hpt : (fun x ↦ dist (s.indicator (fun _ : α ↦ c) x) 0 /
      (1 + dist (s.indicator (fun _ : α ↦ c) x) 0)) =
      s.indicator (fun _ : α ↦ dist c 0 / (1 + dist c 0)) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hpt, integral_indicator hs, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]

/-- The real measure of the support `{x | indicatorConst hs c x ≠ 0}` equals `μ.real s` whenever
`c ≠ 0`. -/
theorem measureReal_indicatorConst_ne_zero [TopologicalSpace E] [Zero E] {s : Set α}
    (hs : MeasurableSet s) {c : E} (hc : c ≠ 0) :
    μ.real {x | indicatorConst (μ := μ) hs c x ≠ 0} = μ.real s := by
  refine measureReal_congr ?_
  filter_upwards [coeFn_indicatorConst (μ := μ) hs c] with x hx
  rw [Set.mem_ofPred_eq, hx, Set.indicator_apply_ne_zero]
  simp [hc]

/-- For a unit-height real indicator `1_s`, `dist (indicatorConst hs 1) 0 = μ.real s / 2`, half of
the disagreement measure `μ.real {x | indicatorConst hs 1 x ≠ 0} = μ.real s`. -/
theorem dist_indicatorConst_one_zero [IsFiniteMeasure μ] {s : Set α} (hs : MeasurableSet s) :
    dist (indicatorConst (μ := μ) hs (1 : ℝ)) 0 = μ.real s / 2 := by
  rw [dist_indicatorConst_zero hs (1 : ℝ)]
  norm_num
  ring

end ConstAndIndicator

end TauCeti.L0
