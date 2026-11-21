/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.MeasureTheory.Function.L0.Convergence
public import TauCeti.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Topology.MetricSpace.Lipschitz.Basic

/-!
# Algebraic operations on random variables

Algebraic operations are inherited from the native almost-everywhere classes at their natural
topological assumptions, giving monoid, group, semiring, ring, module, and algebra instances
together with bundled equivalences (`addEquivAEEqFun`, `linearEquivAEEqFun`, `ringEquivAEEqFun`,
`algEquivAEEqFun`) and bundled `Lᵖ` embeddings (`ofLpAddMonoidHom`, `ofLpLinearMap`, `ofLpCLM`).

On finite measure spaces the bounded integral pseudometric is invariant under isometric scalar
actions and left/right translations, lifts uniform additive groups, Lipschitz addition, and
uniformly continuous constant scalar multiplication, and makes continuous multiplication and
scalar multiplication continuous for convergence in measure without integrability assumptions.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory.AEEqFun
open scoped Topology ENNReal NNReal

namespace TauCeti.L0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

variable {E : Type*} {𝕜 : Type*}

section Topological

variable [TopologicalSpace E]

/-- The native zero almost-everywhere class. -/
instance instZero [Zero E] : Zero (L0 E μ) := equivAEEqFun.zero

/-- The native unit almost-everywhere class. -/
instance instOne [One E] : One (L0 E μ) := equivAEEqFun.one

/-- Addition inherited from the native almost-everywhere quotient. -/
instance instAdd [Add E] [ContinuousAdd E] : Add (L0 E μ) := equivAEEqFun.add

/-- Negation inherited from the native almost-everywhere quotient. -/
instance instNeg [AddGroup E] [IsTopologicalAddGroup E] : Neg (L0 E μ) := equivAEEqFun.Neg

/-- Subtraction inherited from the native almost-everywhere quotient. -/
instance instSub [AddGroup E] [IsTopologicalAddGroup E] : Sub (L0 E μ) := equivAEEqFun.sub

/-- Multiplication inherited from the native almost-everywhere quotient. -/
instance instMul [Mul E] [ContinuousMul E] : Mul (L0 E μ) := equivAEEqFun.mul

/-- Scalar multiplication inherited from the native almost-everywhere quotient. -/
instance instSMul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] : SMul 𝕜 (L0 E μ) :=
  equivAEEqFun.smul 𝕜

/-- Natural powers inherited from the native almost-everywhere quotient. -/
instance instPow [Monoid E] [ContinuousMul E] : Pow (L0 E μ) ℕ := equivAEEqFun.pow ℕ

/-- Natural-number cast inherited from the native almost-everywhere quotient. -/
instance instNatCast [NatCast E] : NatCast (L0 E μ) :=
  ⟨fun n ↦ equivAEEqFun.symm (n : Ω →ₘ[μ] E)⟩

/-- Integer cast inherited from the native almost-everywhere quotient. -/
instance instIntCast [IntCast E] : IntCast (L0 E μ) :=
  ⟨fun n ↦ equivAEEqFun.symm (n : Ω →ₘ[μ] E)⟩

/-- The additive monoid of native almost-everywhere classes, transported to `L0`. -/
instance instAddMonoid [AddMonoid E] [ContinuousAdd E] : AddMonoid (L0 E μ) :=
  equivAEEqFun.addMonoid

/-- The commutative additive monoid of native almost-everywhere classes. -/
instance instAddCommMonoid [AddCommMonoid E] [ContinuousAdd E] :
    AddCommMonoid (L0 E μ) := equivAEEqFun.addCommMonoid

/-- The additive group of native almost-everywhere classes, transported to `L0`. -/
instance instAddGroup [AddGroup E] [IsTopologicalAddGroup E] : AddGroup (L0 E μ) :=
  equivAEEqFun.addGroup

/-- The additive group of native almost-everywhere classes, transported to `L0`. -/
instance instAddCommGroup [AddCommGroup E] [IsTopologicalAddGroup E] :
    AddCommGroup (L0 E μ) := equivAEEqFun.addCommGroup

/-- The monoid of native almost-everywhere classes, transported to `L0`. -/
instance instMonoid [Monoid E] [ContinuousMul E] : Monoid (L0 E μ) := equivAEEqFun.monoid

/-- The commutative monoid of native almost-everywhere classes, transported to `L0`. -/
instance instCommMonoid [CommMonoid E] [ContinuousMul E] : CommMonoid (L0 E μ) :=
  equivAEEqFun.commMonoid

/-- The zero class in `L0` is the native zero class. -/
@[simp]
theorem toAEEqFun_zero [Zero E] : (0 : L0 E μ).toAEEqFun = 0 := by
  simp only [← equivAEEqFun_apply, Equiv.zero_def, Equiv.apply_symm_apply]

/-- The unit class in `L0` is the native unit class. -/
@[simp]
theorem toAEEqFun_one [One E] : (1 : L0 E μ).toAEEqFun = 1 := by
  simp only [← equivAEEqFun_apply, Equiv.one_def, Equiv.apply_symm_apply]

/-- The native class vanishes exactly when the random variable does. -/
@[simp]
theorem toAEEqFun_eq_zero [Zero E] {f : L0 E μ} : f.toAEEqFun = 0 ↔ f = 0 := by
  rw [← toAEEqFun_zero, toAEEqFun_inj]

/-- The native class is one exactly when the random variable is one. -/
@[simp]
theorem toAEEqFun_eq_one [One E] {f : L0 E μ} : f.toAEEqFun = 1 ↔ f = 1 := by
  rw [← toAEEqFun_one, toAEEqFun_inj]

/-- The zero constant is zero. -/
@[simp]
theorem const_zero [Zero E] : const μ (0 : E) = 0 := by
  apply toAEEqFun_injective
  simp only [toAEEqFun_const, toAEEqFun_zero, AEEqFun.zero_def, AEEqFun.const]

/-- The unit constant is one. -/
@[simp]
theorem const_one [One E] : const μ (1 : E) = 1 := by
  apply toAEEqFun_injective
  simp only [toAEEqFun_const, toAEEqFun_one, AEEqFun.one_def, AEEqFun.const]

/-- Addition on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_add [Add E] [ContinuousAdd E] (f g : L0 E μ) :
    (f + g).toAEEqFun = f.toAEEqFun + g.toAEEqFun := by
  simp only [← equivAEEqFun_apply, Equiv.add_def, Equiv.apply_symm_apply]

/-- Negation on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_neg [AddGroup E] [IsTopologicalAddGroup E] (f : L0 E μ) :
    (-f).toAEEqFun = -f.toAEEqFun := by
  simp only [← equivAEEqFun_apply, Equiv.neg_def, Equiv.apply_symm_apply]

/-- Subtraction on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_sub [AddGroup E] [IsTopologicalAddGroup E] (f g : L0 E μ) :
    (f - g).toAEEqFun = f.toAEEqFun - g.toAEEqFun := by
  simp only [← equivAEEqFun_apply, Equiv.sub_def, Equiv.apply_symm_apply]

/-- Multiplication on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_mul [Mul E] [ContinuousMul E] (f g : L0 E μ) :
    (f * g).toAEEqFun = f.toAEEqFun * g.toAEEqFun := by
  simp only [← equivAEEqFun_apply, Equiv.mul_def, Equiv.apply_symm_apply]

/-- Natural powers on `L0` are inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_pow [Monoid E] [ContinuousMul E] (f : L0 E μ) (n : ℕ) :
    (f ^ n).toAEEqFun = f.toAEEqFun ^ n := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    map_pow (equivAEEqFun (μ := μ)).mulEquiv f n

/-- Scalar multiplication on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_smul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (f : L0 E μ) :
    (c • f).toAEEqFun = c • f.toAEEqFun := by
  simp only [← equivAEEqFun_apply, Equiv.smul_def, Equiv.apply_symm_apply]

/-- Natural-number constants retain their native constant class. -/
@[simp]
theorem toAEEqFun_natCast [NatCast E] (n : ℕ) :
    (n : L0 E μ).toAEEqFun = AEEqFun.const Ω (n : E) :=
  toAEEqFun_equivAEEqFun_symm (n : Ω →ₘ[μ] E)

/-- Integer constants retain their native constant class. -/
@[simp]
theorem toAEEqFun_intCast [IntCast E] (n : ℤ) :
    (n : L0 E μ).toAEEqFun = AEEqFun.const Ω (n : E) :=
  toAEEqFun_equivAEEqFun_symm (n : Ω →ₘ[μ] E)

/-- Natural-number cast on `L0 E μ` is the constant class `const μ n`. -/
theorem natCast_def [NatCast E] (n : ℕ) : (n : L0 E μ) = const μ (n : E) :=
  toAEEqFun_injective (by rw [toAEEqFun_natCast, toAEEqFun_const])

/-- Integer cast on `L0 E μ` is the constant class `const μ n`. -/
theorem intCast_def [IntCast E] (n : ℤ) : (n : L0 E μ) = const μ (n : E) :=
  toAEEqFun_injective (by rw [toAEEqFun_intCast, toAEEqFun_const])

/-- The semiring of almost-everywhere classes, transported to `L0`. -/
instance instSemiring [Semiring E] [IsTopologicalSemiring E] : Semiring (L0 E μ) :=
  equivAEEqFun.semiring

/-- The commutative semiring of almost-everywhere classes, transported to `L0`. -/
instance instCommSemiring [CommSemiring E] [IsTopologicalSemiring E] : CommSemiring (L0 E μ) :=
  equivAEEqFun.commSemiring

/-- The ring of almost-everywhere classes, transported to `L0`. -/
instance instRing [Ring E] [IsTopologicalRing E] : Ring (L0 E μ) :=
  equivAEEqFun.ring

/-- The commutative ring of native almost-everywhere classes. -/
instance instCommRing [CommRing E] [IsTopologicalRing E] : CommRing (L0 E μ) :=
  equivAEEqFun.commRing

/-- Canonical additive equivalence between `L0 E μ` and `Ω →ₘ[μ] E`. -/
def addEquivAEEqFun [Add E] [ContinuousAdd E] : L0 E μ ≃+ (Ω →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := equivAEEqFun.symm
  left_inv := equivAEEqFun_symm_toAEEqFun
  right_inv := toAEEqFun_equivAEEqFun_symm
  map_add' := toAEEqFun_add

/-- Applying `addEquivAEEqFun` forgets the wrapper. -/
@[simp]
theorem addEquivAEEqFun_apply [Add E] [ContinuousAdd E] (f : L0 E μ) :
    addEquivAEEqFun f = f.toAEEqFun := (rfl)

/-- The inverse of `addEquivAEEqFun` wraps a native almost-everywhere class. -/
@[simp]
theorem addEquivAEEqFun_symm_apply [Add E] [ContinuousAdd E] (f : Ω →ₘ[μ] E) :
    (addEquivAEEqFun (E := E) (μ := μ)).symm f = equivAEEqFun.symm f := (rfl)

/-- Canonical ring equivalence between `L0 E μ` and `Ω →ₘ[μ] E`. -/
def ringEquivAEEqFun [Add E] [Mul E] [ContinuousAdd E] [ContinuousMul E] :
    L0 E μ ≃+* (Ω →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := equivAEEqFun.symm
  left_inv := equivAEEqFun_symm_toAEEqFun
  right_inv := toAEEqFun_equivAEEqFun_symm
  map_mul' := toAEEqFun_mul
  map_add' := toAEEqFun_add

/-- Applying `ringEquivAEEqFun` forgets the wrapper. -/
@[simp]
theorem ringEquivAEEqFun_apply [Add E] [Mul E] [ContinuousAdd E] [ContinuousMul E] (f : L0 E μ) :
    ringEquivAEEqFun f = f.toAEEqFun := (rfl)

/-- The inverse of `ringEquivAEEqFun` wraps a native almost-everywhere class. -/
@[simp]
theorem ringEquivAEEqFun_symm_apply [Add E] [Mul E] [ContinuousAdd E] [ContinuousMul E]
    (f : Ω →ₘ[μ] E) :
    (ringEquivAEEqFun (E := E) (μ := μ)).symm f = equivAEEqFun.symm f := (rfl)

/-- Forgetting the wrapper preserves finite sums. -/
@[simp]
theorem toAEEqFun_sum [AddCommMonoid E] [ContinuousAdd E] {ι : Type*} (s : Finset ι)
    (f : ι → L0 E μ) :
    (∑ i ∈ s, f i).toAEEqFun = ∑ i ∈ s, (f i).toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    map_sum (equivAEEqFun (μ := μ)).addEquiv f s

/-- Forgetting the wrapper preserves finite products. -/
@[simp]
theorem toAEEqFun_prod [CommMonoid E] [ContinuousMul E] {ι : Type*} (s : Finset ι)
    (f : ι → L0 E μ) :
    (∏ i ∈ s, f i).toAEEqFun = ∏ i ∈ s, (f i).toAEEqFun := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    map_prod (equivAEEqFun (μ := μ)).mulEquiv f s

/-- The native scalar action preserves the monoid action laws. -/
instance instMulAction [Monoid 𝕜] [MulAction 𝕜 E] [ContinuousConstSMul 𝕜 E] :
    MulAction 𝕜 (L0 E μ) := equivAEEqFun.mulAction 𝕜

/-- Distribution is inherited from the native almost-everywhere classes. -/
instance instDistribMulAction [Monoid 𝕜] [AddMonoid E] [ContinuousAdd E]
    [DistribMulAction 𝕜 E] [ContinuousConstSMul 𝕜 E] : DistribMulAction 𝕜 (L0 E μ) :=
  toAEEqFun_injective.distribMulAction
    { toFun := toAEEqFun, map_zero' := toAEEqFun_zero, map_add' := toAEEqFun_add }
    toAEEqFun_smul

/-- Commuting scalar actions descend to almost-everywhere classes. -/
instance instSMulCommClass {𝕜' : Type*} [SMul 𝕜 E] [SMul 𝕜' E]
    [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜' E] [SMulCommClass 𝕜 𝕜' E] :
    SMulCommClass 𝕜 𝕜' (L0 E μ) := equivAEEqFun.smulCommClass 𝕜 𝕜'

/-- Scalar towers descend to almost-everywhere classes. -/
instance instIsScalarTower {𝕜' : Type*} [SMul 𝕜 𝕜'] [SMul 𝕜 E] [SMul 𝕜' E]
    [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    IsScalarTower 𝕜 𝕜' (L0 E μ) := equivAEEqFun.isScalarTower 𝕜 𝕜'

/-- Central scalar actions descend to almost-everywhere classes. -/
instance instIsCentralScalar [SMul 𝕜 E] [SMul 𝕜ᵐᵒᵖ E] [ContinuousConstSMul 𝕜 E]
    [IsCentralScalar 𝕜 E] : IsCentralScalar 𝕜 (L0 E μ) :=
  equivAEEqFun.isCentralScalar 𝕜

/-- The module of almost-everywhere classes, using the native scalar action. -/
instance instModule [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : Module 𝕜 (L0 E μ) :=
  -- Preserve the native scalar action rather than selecting an action through `AddEquiv`.
  toAEEqFun_injective.module 𝕜
    { toFun := toAEEqFun, map_zero' := toAEEqFun_zero, map_add' := toAEEqFun_add }
    toAEEqFun_smul

/-- Canonical `𝕜`-linear equivalence between `L0 E μ` and `Ω →ₘ[μ] E`. -/
def linearEquivAEEqFun (𝕜 : Type*) [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : L0 E μ ≃ₗ[𝕜] (Ω →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := equivAEEqFun.symm
  left_inv := equivAEEqFun_symm_toAEEqFun
  right_inv := toAEEqFun_equivAEEqFun_symm
  map_add' := toAEEqFun_add
  map_smul' _ _ := toAEEqFun_smul _ _

/-- Applying `linearEquivAEEqFun` forgets the wrapper. -/
@[simp]
theorem linearEquivAEEqFun_apply [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] (f : L0 E μ) :
    linearEquivAEEqFun 𝕜 f = f.toAEEqFun := (rfl)

/-- The inverse of `linearEquivAEEqFun` wraps a native almost-everywhere class. -/
@[simp]
theorem linearEquivAEEqFun_symm_apply [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E]
    [Module 𝕜 E] [ContinuousConstSMul 𝕜 E] (f : Ω →ₘ[μ] E) :
    (linearEquivAEEqFun (E := E) (μ := μ) 𝕜).symm f = equivAEEqFun.symm f := (rfl)

/-- The algebra structure on `L0 E μ`, transferred from `Ω →ₘ[μ] E` so `algebraMap` agrees
definitionally with `NatCast`/`IntCast`. -/
instance instAlgebra [CommSemiring 𝕜] [Semiring E] [IsTopologicalSemiring E] [Algebra 𝕜 E] :
    Algebra 𝕜 (L0 E μ) where
  algebraMap :=
    { toFun c := equivAEEqFun.symm (algebraMap 𝕜 (Ω →ₘ[μ] E) c)
      map_one' := toAEEqFun_injective (by simp only [toAEEqFun_equivAEEqFun_symm, toAEEqFun_one,
        map_one])
      map_mul' a b := toAEEqFun_injective (by simp only [toAEEqFun_equivAEEqFun_symm, toAEEqFun_mul,
        map_mul])
      map_zero' := toAEEqFun_injective (by simp only [toAEEqFun_equivAEEqFun_symm, toAEEqFun_zero,
        map_zero])
      map_add' a b := toAEEqFun_injective (by simp only [toAEEqFun_equivAEEqFun_symm, toAEEqFun_add,
        map_add]) }
  commutes' c f := toAEEqFun_injective (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAEEqFun_mul,
      toAEEqFun_equivAEEqFun_symm]
    exact Algebra.commutes c f.toAEEqFun)
  smul_def' c f := toAEEqFun_injective (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAEEqFun_smul, toAEEqFun_mul,
      toAEEqFun_equivAEEqFun_symm]
    exact Algebra.smul_def c f.toAEEqFun)

/-- Algebra constants are the native constant almost-everywhere classes. -/
theorem toAEEqFun_algebraMap [CommSemiring 𝕜] [Semiring E] [IsTopologicalSemiring E] [Algebra 𝕜 E]
    (c : 𝕜) :
    (algebraMap 𝕜 (L0 E μ) c).toAEEqFun = AEEqFun.const Ω (algebraMap 𝕜 E c) :=
  toAEEqFun_equivAEEqFun_symm (algebraMap 𝕜 (Ω →ₘ[μ] E) c)

/-- Canonical `𝕜`-algebra equivalence between `L0 E μ` and `Ω →ₘ[μ] E`. -/
def algEquivAEEqFun (𝕜 : Type*) [CommSemiring 𝕜] [Semiring E] [IsTopologicalSemiring E]
    [Algebra 𝕜 E] : L0 E μ ≃ₐ[𝕜] (Ω →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := equivAEEqFun.symm
  left_inv := equivAEEqFun_symm_toAEEqFun
  right_inv := toAEEqFun_equivAEEqFun_symm
  map_mul' := toAEEqFun_mul
  map_add' := toAEEqFun_add
  commutes' _ := toAEEqFun_equivAEEqFun_symm _

/-- Applying `algEquivAEEqFun` forgets the wrapper. -/
@[simp]
theorem algEquivAEEqFun_apply [CommSemiring 𝕜] [Semiring E] [IsTopologicalSemiring E]
    [Algebra 𝕜 E] (f : L0 E μ) :
    algEquivAEEqFun 𝕜 f = f.toAEEqFun := (rfl)

/-- The inverse of `algEquivAEEqFun` wraps a native almost-everywhere class. -/
@[simp]
theorem algEquivAEEqFun_symm_apply [CommSemiring 𝕜] [Semiring E] [IsTopologicalSemiring E]
    [Algebra 𝕜 E] (f : Ω →ₘ[μ] E) :
    (algEquivAEEqFun (E := E) (μ := μ) 𝕜).symm f = equivAEEqFun.symm f := (rfl)

/-- The representative of an algebra constant agrees almost everywhere with that constant. -/
theorem coeFn_algebraMap [CommSemiring 𝕜] [Semiring E] [IsTopologicalSemiring E] [Algebra 𝕜 E]
    (c : 𝕜) :
    ((algebraMap 𝕜 (L0 E μ) c) : Ω → E) =ᵐ[μ] Function.const Ω (algebraMap 𝕜 E c) := by
  simpa only [← toAEEqFun_algebraMap] using (AEEqFun.coeFn_const Ω (algebraMap 𝕜 E c) (μ := μ))

/-- The representative of zero vanishes almost everywhere. -/
theorem coeFn_zero [Zero E] : ((0 : L0 E μ) : Ω → E) =ᵐ[μ] 0 := by
  simpa only [← toAEEqFun_zero] using (AEEqFun.coeFn_zero (α := Ω) (β := E) (μ := μ))

/-- On a nonzero measure space, the chosen representative of `0` is identically `0`. -/
theorem coeFn_zero_eq [NeZero μ] [Zero E] (x : Ω) : (0 : L0 E μ) x = 0 := by
  rw [← const_zero, coeFn_const_eq]

/-- The representative of one equals one almost everywhere. -/
theorem coeFn_one [One E] : ((1 : L0 E μ) : Ω → E) =ᵐ[μ] 1 := by
  simpa only [← toAEEqFun_one] using (AEEqFun.coeFn_one (α := Ω) (β := E) (μ := μ))

/-- On a nonzero measure space, the chosen representative of `1` is identically `1`. -/
theorem coeFn_one_eq [NeZero μ] [One E] (x : Ω) : (1 : L0 E μ) x = 1 := by
  rw [← const_one, coeFn_const_eq]

/-- Representatives of a negative agree almost everywhere with the pointwise negative. -/
theorem coeFn_neg [AddGroup E] [IsTopologicalAddGroup E] (f : L0 E μ) :
    ((-f : L0 E μ) : Ω → E) =ᵐ[μ] -f := by
  simpa only [← toAEEqFun_neg] using (AEEqFun.coeFn_neg f.toAEEqFun)

/-- Representatives of a difference agree almost everywhere with the pointwise difference. -/
theorem coeFn_sub [AddGroup E] [IsTopologicalAddGroup E] (f g : L0 E μ) :
    ((f - g : L0 E μ) : Ω → E) =ᵐ[μ] f - g := by
  simpa only [← toAEEqFun_sub] using (AEEqFun.coeFn_sub f.toAEEqFun g.toAEEqFun)

/-- Representatives of a power agree almost everywhere with the pointwise power. -/
theorem coeFn_pow [Monoid E] [ContinuousMul E] (f : L0 E μ) (n : ℕ) :
    ((f ^ n : L0 E μ) : Ω → E) =ᵐ[μ] f ^ n := by
  simpa only [← toAEEqFun_pow] using (AEEqFun.coeFn_pow f.toAEEqFun n)

/-- Representatives of a sum agree almost everywhere with the pointwise sum. -/
theorem coeFn_add [Add E] [ContinuousAdd E] (f g : L0 E μ) :
    ((f + g : L0 E μ) : Ω → E) =ᵐ[μ] f + g := by
  filter_upwards [AEEqFun.coeFn_add f.toAEEqFun g.toAEEqFun] with x hx
  simpa only [toAEEqFun_add, Pi.add_apply] using hx

/-- Representatives of a product agree almost everywhere with the pointwise product. -/
theorem coeFn_mul [Mul E] [ContinuousMul E] (f g : L0 E μ) :
    ((f * g : L0 E μ) : Ω → E) =ᵐ[μ] f * g := by
  filter_upwards [AEEqFun.coeFn_mul f.toAEEqFun g.toAEEqFun] with x hx
  simpa only [toAEEqFun_mul, Pi.mul_apply] using hx

/-- Representatives of a scalar multiple agree almost everywhere with the pointwise multiple. -/
theorem coeFn_smul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (f : L0 E μ) :
    ((c • f : L0 E μ) : Ω → E) =ᵐ[μ] c • (f : Ω → E) := by
  filter_upwards [AEEqFun.coeFn_smul c f.toAEEqFun] with x hx
  simpa only [toAEEqFun_smul, Pi.smul_apply] using hx

/-- Natural-number constants have constant representatives almost everywhere. -/
theorem coeFn_natCast [NatCast E] (n : ℕ) :
    ((n : L0 E μ) : Ω → E) =ᵐ[μ] Function.const Ω (n : E) := by
  rw [natCast_def]
  exact coeFn_const (n : E)

/-- On a nonzero measure space, the chosen representative of `(n : L0 E μ)` is identically `n`. -/
theorem coeFn_natCast_eq [NeZero μ] [NatCast E] (n : ℕ) (x : Ω) : (n : L0 E μ) x = n := by
  rw [natCast_def, coeFn_const_eq]

/-- Integer constants have constant representatives almost everywhere. -/
theorem coeFn_intCast [IntCast E] (n : ℤ) :
    ((n : L0 E μ) : Ω → E) =ᵐ[μ] Function.const Ω (n : E) := by
  rw [intCast_def]
  exact coeFn_const (n : E)

/-- On a nonzero measure space, the chosen representative of `(n : L0 E μ)` is identically `n`. -/
theorem coeFn_intCast_eq [NeZero μ] [IntCast E] (n : ℤ) (x : Ω) : (n : L0 E μ) x = n := by
  rw [intCast_def, coeFn_const_eq]

/-- Numerals retain their native constant class. -/
@[simp]
theorem toAEEqFun_ofNat [NatCast E] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : L0 E μ).toAEEqFun = AEEqFun.const Ω (ofNat(n) : E) :=
  toAEEqFun_natCast n

/-- Numeral representatives equal the corresponding constant almost everywhere. -/
theorem coeFn_ofNat [NatCast E] (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : L0 E μ) : Ω → E) =ᵐ[μ] Function.const Ω (ofNat(n) : E) :=
  coeFn_natCast n

/-- A finite sum has the pointwise sum as its representative almost everywhere. -/
theorem coeFn_finsetSum [AddCommMonoid E] [ContinuousAdd E] {ι : Type*} (s : Finset ι)
    (f : ι → L0 E μ) :
    ((∑ i ∈ s, f i : L0 E μ) : Ω → E) =ᵐ[μ] ∑ i ∈ s, (f i : Ω → E) := by
  simpa only [← toAEEqFun_sum] using
    (AEEqFun.coeFn_finsetSum s (fun i ↦ (f i).toAEEqFun))

/-- A finite product has the pointwise product as its representative almost everywhere. -/
theorem coeFn_finsetProd [CommMonoid E] [ContinuousMul E] {ι : Type*} (s : Finset ι)
    (f : ι → L0 E μ) :
    ((∏ i ∈ s, f i : L0 E μ) : Ω → E) =ᵐ[μ] ∏ i ∈ s, (f i : Ω → E) := by
  simpa only [← toAEEqFun_prod] using
    (AEEqFun.coeFn_finsetProd s (fun i ↦ (f i).toAEEqFun))

/-- Constant random variables agree with the algebra constants. -/
@[simp]
theorem algebraMap_eq_const [CommSemiring 𝕜] [Semiring E] [IsTopologicalSemiring E] [Algebra 𝕜 E]
    (c : 𝕜) :
    algebraMap 𝕜 (L0 E μ) c = const μ (algebraMap 𝕜 E c) := by
  apply toAEEqFun_injective
  simp only [toAEEqFun_const, toAEEqFun_algebraMap]

/-- Constructing a sum agrees with adding the constructed random variables. -/
@[simp]
theorem ofFun_add_ofFun [Add E] [ContinuousAdd E] (f g : Ω → E) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ofFun f hf + ofFun g hg = ofFun (f + g) (hf.add hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_add, toAEEqFun_ofFun] using
    AEEqFun.mk_add_mk f g hf hg

/-- Constructing a product agrees with multiplying the constructed random variables. -/
@[simp]
theorem ofFun_mul_ofFun [Mul E] [ContinuousMul E] (f g : Ω → E) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ofFun f hf * ofFun g hg = ofFun (f * g) (hf.mul hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_mul, toAEEqFun_ofFun] using
    AEEqFun.mk_mul_mk f g hf hg

/-- Constructing a scalar multiple agrees with scalar multiplication of a random variable. -/
@[simp]
theorem smul_ofFun [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) :
    c • ofFun f hf = ofFun (c • f) (hf.const_smul c) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_smul, toAEEqFun_ofFun] using
    AEEqFun.smul_mk c f hf

/-- Constructing the zero function gives the zero random variable. -/
@[simp]
theorem ofFun_zero [Zero E] : ofFun (0 : Ω → E) aestronglyMeasurable_const = (0 : L0 E μ) := by
  apply equivAEEqFun.injective
  rw [equivAEEqFun_apply, equivAEEqFun_apply, toAEEqFun_zero]
  exact (toAEEqFun_ofFun _ _).trans AEEqFun.zero_def.symm

/-- Constructing the unit function gives the unit random variable. -/
@[simp]
theorem ofFun_one [One E] : ofFun (1 : Ω → E) aestronglyMeasurable_const = (1 : L0 E μ) := by
  apply equivAEEqFun.injective
  rw [equivAEEqFun_apply, equivAEEqFun_apply, toAEEqFun_one]
  exact (toAEEqFun_ofFun _ _).trans AEEqFun.one_def.symm

/-- A constructed random variable vanishes exactly when its function vanishes almost everywhere. -/
@[simp]
theorem ofFun_eq_zero [Zero E] {f : Ω → E} {hf : AEStronglyMeasurable f μ} :
    ofFun f hf = 0 ↔ f =ᵐ[μ] 0 := by
  rw [← toAEEqFun_eq_zero, toAEEqFun_ofFun, AEEqFun.zero_def]
  exact AEEqFun.mk_eq_mk

/-- A constructed random variable is one exactly when its function is one almost everywhere. -/
@[simp]
theorem ofFun_eq_one [One E] {f : Ω → E} {hf : AEStronglyMeasurable f μ} :
    ofFun f hf = 1 ↔ f =ᵐ[μ] 1 := by
  rw [← toAEEqFun_eq_one, toAEEqFun_ofFun, AEEqFun.one_def]
  exact AEEqFun.mk_eq_mk

/-- Negation commutes with constructing a random variable. -/
@[simp]
theorem neg_ofFun [AddGroup E] [IsTopologicalAddGroup E] (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) :
    -ofFun f hf = ofFun (-f) hf.neg := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_neg, toAEEqFun_ofFun] using AEEqFun.neg_mk f hf

/-- Subtraction commutes with constructing random variables. -/
@[simp]
theorem ofFun_sub_ofFun [AddGroup E] [IsTopologicalAddGroup E] (f g : Ω → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ofFun f hf - ofFun g hg = ofFun (f - g) (hf.sub hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_sub, toAEEqFun_ofFun] using
    (AEEqFun.mk_sub f g hf hg).symm

/-- Natural powers commute with constructing a random variable. -/
@[simp]
theorem ofFun_pow [Monoid E] [ContinuousMul E] (f : Ω → E) (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    ofFun f hf ^ n = ofFun (f ^ n) (hf.pow n) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_pow, toAEEqFun_ofFun] using AEEqFun.mk_pow f hf n

/-- Addition of constant random variables agrees with the constant of the sum. -/
@[simp]
theorem const_add [Add E] [ContinuousAdd E] (a b : E) :
    const μ (a + b) = const μ a + const μ b := by
  rw [← ofFun_const, ← ofFun_const, ← ofFun_const, ofFun_add_ofFun]
  rfl

/-- Negation of a constant random variable agrees with the constant of the negation. -/
@[simp]
theorem const_neg [AddGroup E] [IsTopologicalAddGroup E] (a : E) :
    const μ (-a) = -const μ a := by
  rw [← ofFun_const, ← ofFun_const, neg_ofFun]
  rfl

/-- Subtraction of constant random variables agrees with the constant of the difference. -/
@[simp]
theorem const_sub [AddGroup E] [IsTopologicalAddGroup E] (a b : E) :
    const μ (a - b) = const μ a - const μ b := by
  rw [← ofFun_const, ← ofFun_const, ← ofFun_const, ofFun_sub_ofFun]
  rfl

/-- Multiplication of constant random variables agrees with the constant of the product. -/
@[simp]
theorem const_mul [Mul E] [ContinuousMul E] (a b : E) :
    const μ (a * b) = const μ a * const μ b := by
  rw [← ofFun_const, ← ofFun_const, ← ofFun_const, ofFun_mul_ofFun]
  rfl

/-- Scalar multiplication of a constant random variable agrees with the scaled constant. -/
@[simp]
theorem const_smul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) (a : E) :
    const μ (c • a) = c • const μ a := by
  rw [← ofFun_const, ← ofFun_const, smul_ofFun]
  rfl

end Topological

/-- The image of the zero `Lp` function is zero. -/
@[simp]
theorem ofLp_zero [NormedAddCommGroup E] {p : ℝ≥0∞} : ofLp (0 : Lp E p μ) = (0 : L0 E μ) := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The `Lp` inclusion detects zero. -/
@[simp]
theorem ofLp_eq_zero [NormedAddCommGroup E] {p : ℝ≥0∞} {f : Lp E p μ} :
    ofLp f = 0 ↔ f = 0 := by
  rw [← ofLp_zero, ofLp_inj]

/-- The `Lp` inclusion preserves natural multiples. -/
@[simp]
theorem ofLp_nsmul [NormedAddCommGroup E] {p : ℝ≥0∞} (n : ℕ) (f : Lp E p μ) :
    ofLp (n • f) = n • ofLp f := by
  apply toAEEqFun_injective
  simp

/-- The inclusion of `Lp` preserves addition. -/
@[simp]
theorem ofLp_add [NormedAddCommGroup E] {p : ℝ≥0∞} (f g : Lp E p μ) :
    ofLp (f + g) = ofLp f + ofLp g := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The inclusion of `Lp` preserves finite sums. -/
@[simp]
theorem ofLp_sum [NormedAddCommGroup E] {p : ℝ≥0∞} {ι : Type*} (s : Finset ι) (f : ι → Lp E p μ) :
    ofLp (∑ i ∈ s, f i) = ∑ i ∈ s, ofLp (f i) := by
  apply toAEEqFun_injective
  simp

/-- The inclusion of `Lp` preserves negation. -/
@[simp]
theorem ofLp_neg [NormedAddCommGroup E] {p : ℝ≥0∞} (f : Lp E p μ) : ofLp (-f) = -ofLp f := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The inclusion of `Lp` preserves subtraction. -/
@[simp]
theorem ofLp_sub [NormedAddCommGroup E] {p : ℝ≥0∞} (f g : Lp E p μ) :
    ofLp (f - g) = ofLp f - ofLp g := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

/-- The inclusion of `Lp` preserves scalar multiplication. -/
@[simp]
theorem ofLp_smul [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} (c : 𝕜) (f : Lp E p μ) : ofLp (c • f) = c • ofLp f := by
  apply ext
  have h := coeFn_smul c (ofLp f)
  simp only [coeFn_ofLp] at h ⊢
  exact (Lp.coeFn_smul c f).trans h.symm

/-- `L0.ofLp` bundled as an additive monoid homomorphism. -/
def ofLpAddMonoidHom [NormedAddCommGroup E] {p : ℝ≥0∞} : Lp E p μ →+ L0 E μ where
  toFun := ofLp
  map_zero' := ofLp_zero
  map_add' := ofLp_add

/-- Applying `ofLpAddMonoidHom` computes `ofLp`. -/
@[simp]
theorem ofLpAddMonoidHom_apply [NormedAddCommGroup E] {p : ℝ≥0∞} (f : Lp E p μ) :
    ofLpAddMonoidHom f = ofLp f := (rfl)

/-- `L0.ofLp` bundled as a `𝕜`-linear map. -/
def ofLpLinearMap (𝕜 : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} : Lp E p μ →ₗ[𝕜] L0 E μ where
  toFun := ofLp
  map_add' := ofLp_add
  map_smul' := ofLp_smul

/-- Applying `ofLpLinearMap` computes `ofLp`. -/
@[simp]
theorem ofLpLinearMap_apply [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} (f : Lp E p μ) :
    ofLpLinearMap 𝕜 f = ofLp f := (rfl)

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- Including a constant `Lp` function gives the corresponding constant random variable. -/
@[simp]
theorem ofLp_const [NormedAddCommGroup E] {p : ℝ≥0∞} (c : E) :
    ofLp (Lp.const p μ c) = const μ c := by
  apply toAEEqFun_injective
  simp only [toAEEqFun_ofLp, Lp.const_val, toAEEqFun_const]

/-- Continuous `𝕜`-linear embedding of `Lp E p μ` into `L0 E μ` for `1 ≤ p` on a finite measure
space. -/
def ofLpCLM (𝕜 : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] : Lp E p μ →L[𝕜] L0 E μ where
  toLinearMap := ofLpLinearMap 𝕜
  cont := continuous_ofLp

/-- Applying `ofLpCLM` computes `ofLp`. -/
@[simp]
theorem ofLpCLM_apply [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp E p μ) :
    ofLpCLM 𝕜 f = ofLp f := (rfl)

section PseudoMetric

variable [PseudoMetricSpace E]

/-- Addition of random variables is continuous for convergence in measure. -/
instance instContinuousAdd [Add E] [ContinuousAdd E] : ContinuousAdd (L0 E μ) where
  continuous_add := by
    have heq : (Function.uncurry (· + ·) : L0 E μ × L0 E μ → L0 E μ) =
        Function.uncurry (comp₂ (· + ·) continuous_add) := by
      funext f
      exact ext ((coeFn_add f.1 f.2).trans (coeFn_comp₂ _ _ _ _).symm)
    -- Present the pointwise operation as its uncurried map so that heq applies.
    change Continuous (Function.uncurry _)
    rw [heq]
    exact continuous_comp₂ _ _

/-- Negation of random variables is continuous for convergence in measure. -/
instance instContinuousNeg [AddGroup E] [IsTopologicalAddGroup E] : ContinuousNeg (L0 E μ) where
  continuous_neg := by
    have heq : (Neg.neg : L0 E μ → L0 E μ) = comp Neg.neg continuous_neg := by
      funext f
      exact ext ((coeFn_neg f).trans (coeFn_comp _ _ _).symm)
    rw [heq]
    exact continuous_comp _ _

/-- The bounded integral topology preserves the topological additive group structure. -/
instance instIsTopologicalAddGroup [AddGroup E] [IsTopologicalAddGroup E] :
    IsTopologicalAddGroup (L0 E μ) where

/-- An isometric scalar action on `E` lifts to an isometric scalar action on `L0 E μ`. -/
instance instIsIsometricSMul [SMul 𝕜 E] [IsIsometricSMul 𝕜 E] :
    IsIsometricSMul 𝕜 (L0 E μ) where
  isometry_smul c := Isometry.of_dist_eq fun f g ↦ by
    rw [dist_def, dist_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_smul c f, coeFn_smul c g] with x hcf hcg
    simp only [hcf, hcg, Pi.smul_apply, (isometry_smul E c).dist_eq]

/-- Translation preserves the bounded integral pseudometric for an isometric additive codomain. -/
instance instIsIsometricVAdd [Add E] [ContinuousAdd E]
    [IsIsometricVAdd E E] : IsIsometricVAdd (L0 E μ) (L0 E μ) where
  isometry_vadd f := Isometry.of_dist_eq fun g h ↦ by
    -- The canonical additive action is addition; this changes only its notation.
    change dist (f + g) (f + h) = dist g h
    rw [dist_def, dist_def]
    apply integral_congr_ae
    filter_upwards [coeFn_add f g, coeFn_add f h] with x hx hy
    simp only [hx, hy, Pi.add_apply, dist_add_left]

/-- Isometric right translation on `E` lifts to isometric right translation on `L0 E μ`. -/
instance instIsIsometricVAddOp [Add E] [ContinuousAdd E]
    [IsIsometricVAdd Eᵃᵒᵖ E] : IsIsometricVAdd (L0 E μ)ᵃᵒᵖ (L0 E μ) where
  isometry_vadd h := Isometry.of_dist_eq fun f g ↦ by
    simp_rw [AddOpposite.vadd_eq_add_unop]
    rw [dist_def, dist_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_add f h.unop, coeFn_add g h.unop] with x hfh hgh
    simp only [hfh, hgh, Pi.add_apply, dist_add_right]

/-- In `L0 E μ` over a topological additive group with isometric right translation,
`dist f g = dist (f - g) 0`. -/
theorem dist_eq_dist_sub_zero [AddGroup E] [IsTopologicalAddGroup E]
    [IsIsometricVAdd Eᵃᵒᵖ E] (f g : L0 E μ) :
    dist f g = dist (f - g) 0 := by
  simpa [sub_eq_add_neg] using (dist_add_right f g (-g)).symm

/-- Uniform continuity of subtraction passes to convergence in measure. -/
instance instIsUniformAddGroup [AddGroup E] [IsUniformAddGroup E] :
    IsUniformAddGroup (L0 E μ) where
  uniformContinuous_sub := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    let η := ε / (2 * (μ.real Set.univ + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨δ, hδ, hsub⟩ := Metric.uniformContinuous_iff.mp
      (IsUniformAddGroup.uniformContinuous_sub (α := E)) η hη
    let C := (1 + δ) / δ
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨ε / (4 * C), div_pos hε (mul_pos (by norm_num) hC), ?_⟩
    intro f g hfg
    have h₁ : dist f.1 g.1 < ε / (4 * C) :=
      (le_max_left _ _).trans_lt (by simpa only [Prod.dist_eq] using hfg)
    have h₂ : dist f.2 g.2 < ε / (4 * C) :=
      (le_max_right _ _).trans_lt (by simpa only [Prod.dist_eq] using hfg)
    -- Outside the two exceptional sets, uniform continuity controls subtraction pointwise.
    have hbad : ∀ᵐ x ∂μ, η < dist ((f.1 - f.2) x) ((g.1 - g.2) x) →
        x ∈ {x | δ ≤ dist (f.1 x) (g.1 x)} ∪ {x | δ ≤ dist (f.2 x) (g.2 x)} := by
      filter_upwards [coeFn_sub f.1 f.2, coeFn_sub g.1 g.2] with x hf hg
      intro hx
      by_contra h
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
      have hs := hsub (a := (f.1 x, f.2 x)) (b := (g.1 x, g.2 x))
        (by simpa only [Prod.dist_eq, max_lt_iff] using h)
      exact (not_lt_of_gt hx) (by simpa only [hf, hg, Pi.sub_apply] using hs)
    have hmeasure : μ.real {x | η < dist ((f.1 - f.2) x) ((g.1 - g.2) x)} ≤
        C * dist f.1 g.1 + C * dist f.2 g.2 := by
      have hs : {x | η < dist ((f.1 - f.2) x) ((g.1 - g.2) x)} ≤ᵐ[μ]
          {x | δ ≤ dist (f.1 x) (g.1 x)} ∪ {x | δ ≤ dist (f.2 x) (g.2 x)} := by
        filter_upwards [hbad] with x hx
        exact hx
      apply le_trans (ENNReal.toReal_mono (by finiteness) (measure_mono_ae hs))
      exact (measureReal_union_le _ _).trans (add_le_add
        (measureReal_ge_le_mul_dist f.1 g.1 hδ)
        (measureReal_ge_le_mul_dist f.2 g.2 hδ))
    -- The bounded integral is small on the good set and the exceptional sets have small mass.
    have hmass : η * μ.real Set.univ < ε / 2 := by
      dsimp [η]
      have hm := measureReal_nonneg (μ := μ) (s := Set.univ)
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith [hm]
    have hb₁ : C * dist f.1 g.1 < ε / 4 := by
      have := (lt_div_iff₀ (by positivity : 0 < 4 * C)).mp h₁
      nlinarith
    have hb₂ : C * dist f.2 g.2 < ε / 4 := by
      have := (lt_div_iff₀ (by positivity : 0 < 4 * C)).mp h₂
      nlinarith
    have hb := dist_le_mul_measureReal_univ_add_measureReal_gt
      (f.1 - f.2) (g.1 - g.2) hη.le
    linarith

/-- On a finite measure space, addition on `L0 E μ` is Lipschitz whenever addition on `E` is
Lipschitz. -/
instance instLipschitzAdd [AddMonoid E] [LipschitzAdd E] : LipschitzAdd (L0 E μ) where
  lipschitz_add := by
    let K : ℝ≥0 := max (LipschitzAdd.C E) 1
    have hK1 : 1 ≤ K := le_max_right _ _
    have hlip : LipschitzWith K (fun p : E × E ↦ p.1 + p.2) :=
      (lipschitzWith_lipschitz_const_add_edist (β := E)).weaken (le_max_left _ _)
    refine ⟨2 * K, LipschitzWith.of_dist_le_mul fun p q ↦ ?_⟩
    have hae : ∀ᵐ x ∂μ,
        dist ((p.1 + p.2) x) ((q.1 + q.2) x) / (1 + dist ((p.1 + p.2) x) ((q.1 + q.2) x)) ≤
          (K : ℝ) * (dist (p.1 x) (q.1 x) / (1 + dist (p.1 x) (q.1 x))) +
            (K : ℝ) * (dist (p.2 x) (q.2 x) / (1 + dist (p.2 x) (q.2 x))) := by
      filter_upwards [coeFn_add p.1 p.2, coeFn_add q.1 q.2] with x hpx hqx
      rw [hpx, hqx, Pi.add_apply, Pi.add_apply]
      exact hlip.dist_div_one_add_dist_prod_le hK1 (p.1 x, p.2 x) (q.1 x, q.2 x)
    have hint₁ := (integrable_dist_div_one_add_dist p.1 q.1).const_mul (K : ℝ)
    have hint₂ := (integrable_dist_div_one_add_dist p.2 q.2).const_mul (K : ℝ)
    calc dist (p.1 + p.2) (q.1 + q.2)
        ≤ ∫ x, ((K : ℝ) * (dist (p.1 x) (q.1 x) / (1 + dist (p.1 x) (q.1 x))) +
            (K : ℝ) * (dist (p.2 x) (q.2 x) / (1 + dist (p.2 x) (q.2 x)))) ∂μ :=
          integral_mono_ae (integrable_dist_div_one_add_dist (p.1 + p.2) (q.1 + q.2))
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

/-- Multiplication of random variables is continuous for convergence in measure. -/
instance instContinuousMul [Mul E] [ContinuousMul E] : ContinuousMul (L0 E μ) where
  continuous_mul := by
    have heq : (Function.uncurry (· * ·) : L0 E μ × L0 E μ → L0 E μ) =
        Function.uncurry (comp₂ (· * ·) continuous_mul) := by
      funext f
      exact ext ((coeFn_mul f.1 f.2).trans (coeFn_comp₂ _ _ _ _).symm)
    -- Present the pointwise operation as its uncurried map so that heq applies.
    change Continuous (Function.uncurry _)
    rw [heq]
    exact continuous_comp₂ _ _

/-- The bounded integral topology preserves the topological semiring structure. -/
instance instIsTopologicalSemiring [Semiring E] [IsTopologicalSemiring E] :
    IsTopologicalSemiring (L0 E μ) where

/-- The bounded integral topology preserves the topological ring structure. -/
instance instIsTopologicalRing [Ring E] [IsTopologicalRing E] :
    IsTopologicalRing (L0 E μ) where

/-- Multiplication by a fixed scalar is continuous without a topology on the scalars. -/
instance instContinuousConstSMul [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] :
    ContinuousConstSMul 𝕜 (L0 E μ) where
  continuous_const_smul c := by
    have heq : (fun f : L0 E μ ↦ c • f) = comp (c • ·) (continuous_const_smul c) := by
      funext f
      exact ext ((coeFn_smul c f).trans (coeFn_comp _ _ _).symm)
    rw [heq]
    exact continuous_comp _ _

/-- On a finite measure space, constant scalar multiplication on `L0 E μ` is uniformly continuous
whenever constant scalar multiplication on `E` is uniformly continuous. -/
instance instUniformContinuousConstSMul [SMul 𝕜 E] [UniformContinuousConstSMul 𝕜 E] :
    UniformContinuousConstSMul 𝕜 (L0 E μ) where
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
        _ ≤ (1 + δ) / δ * dist f g := measureReal_ge_le_mul_dist f g hδ
        _ < (1 + δ) / δ * (δ / (1 + δ) * (η / 2)) :=
            mul_lt_mul_of_pos_left hfg (div_pos h1δ hδ)
        _ = η / 2 := by field_simp [hδ.ne', h1δ.ne']
    calc dist (c • f) (c • g)
        ≤ ε * μ.real Set.univ + μ.real {x | ε ≤ dist ((c • f) x) ((c • g) x)} :=
          dist_le_mul_measureReal_univ_add_measureReal_ge (c • f) (c • g) hε.le
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring

/-- Joint scalar multiplication is continuous for convergence in measure. -/
instance instContinuousSMul [PseudoMetricSpace 𝕜] [SMul 𝕜 E] [ContinuousSMul 𝕜 E] :
    ContinuousSMul 𝕜 (L0 E μ) where
  continuous_smul := by
    apply continuous_iff_continuousAt.2
    intro g
    apply tendsto_iff_tendstoInMeasure.2
    have h₁ : TendstoInMeasure μ (fun f : 𝕜 × L0 E μ ↦ fun _ : Ω ↦ f.1)
        (𝓝 g) (fun _ ↦ g.1) := by
      rw [tendstoInMeasure_iff_dist]
      intro ε hε
      apply tendsto_const_nhds.congr'
      filter_upwards [(continuous_fst.tendsto g).eventually
        (Metric.ball_mem_nhds g.1 hε)] with f hf
      have hempty : {_x : Ω | ε ≤ dist f.1 g.1} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun _ hx ↦ (not_le_of_gt hf) hx
      simp only [hempty, measure_empty]
    have h₂ := tendsto_iff_tendstoInMeasure.1 (continuous_snd.tendsto g)
    have h := h₁.continuous_comp₂ h₂ continuous_smul
      (Eventually.of_forall fun f ↦ (f.2.stronglyMeasurable.const_smul f.1).aestronglyMeasurable)
    exact h.congr (fun f ↦ (coeFn_smul f.1 f.2).symm) (coeFn_smul g.1 g.2).symm

end PseudoMetric

/-- In `L0 ℝ μ` on a finite measure space, the distance from the natural-number constant class
`(n : L0 ℝ μ)` to `0` converges to the total mass `μ.real Set.univ` as `n → ∞`. -/
theorem tendsto_dist_natCast_zero_nhds_measureReal_univ :
    Tendsto (fun n : ℕ ↦ dist (n : L0 ℝ μ) 0) atTop (𝓝 (μ.real Set.univ)) := by
  have hratio : Tendsto (fun n : ℕ ↦ (n : ℝ) / (1 + (n : ℝ))) atTop (𝓝 1) := by
    simpa only [add_comm] using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hmul : Tendsto (fun n : ℕ ↦ μ.real Set.univ * ((n : ℝ) / (1 + (n : ℝ)))) atTop
      (𝓝 (μ.real Set.univ)) := by
    simpa only [mul_one] using hratio.const_mul (μ.real Set.univ)
  refine hmul.congr fun n ↦ ?_
  rw [natCast_def, ← const_zero, dist_const, Real.dist_eq, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg n)]

/-- On a nonzero finite measure space, the sequence of constant classes `(n : L0 ℝ μ)` diverges in
`L0 ℝ μ`, even though `L0 ℝ μ` is bounded in diameter by `μ.real Set.univ`. -/
theorem not_exists_tendsto_natCast [NeZero μ] :
    ¬ ∃ f : L0 ℝ μ, Tendsto (fun n : ℕ ↦ (n : L0 ℝ μ)) atTop (𝓝 f) := by
  rintro ⟨f, hf⟩
  obtain ⟨ns, hns, hae⟩ := exists_seq_tendsto_ae_of_tendsto hf
  have hbot : ∀ᵐ _ ∂μ, False := by
    refine hae.mono fun x hx ↦ ?_
    simp only [coeFn_natCast_eq] at hx
    exact not_tendsto_nhds_of_tendsto_atTop
      (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop) _ hx
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hbot))

end FiniteMeasure
end TauCeti.L0
