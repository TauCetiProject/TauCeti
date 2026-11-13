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

/-!
# Algebraic operations on random variables

Algebraic operations are inherited from the native almost-everywhere classes at their natural
topological assumptions. On finite measure spaces the bounded integral pseudometric is translation
invariant for isometric additive codomains. Continuous multiplication and scalar multiplication
remain continuous for convergence in measure without integrability assumptions.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

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

/-- The additive monoid of native almost-everywhere classes, transported to `L0`. -/
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

/-- The ring of almost-everywhere classes, transported to `L0`. -/
instance instRing [Ring E] [IsTopologicalRing E] : Ring (L0 E μ) := by
  -- The native quotient has the operations but no ring instance at the pinned revision.
  letI : Ring (Ω →ₘ[μ] E) := by
    letI : NatCast (Ω →ₘ[μ] E) := ⟨fun n ↦ n • (1 : Ω →ₘ[μ] E)⟩
    letI : IntCast (Ω →ₘ[μ] E) := ⟨fun n ↦ n • (1 : Ω →ₘ[μ] E)⟩
    apply AEEqFun.toGerm_injective.ring AEEqFun.toGerm
      AEEqFun.zero_toGerm AEEqFun.one_toGerm AEEqFun.add_toGerm AEEqFun.mul_toGerm
      AEEqFun.neg_toGerm AEEqFun.sub_toGerm
      (fun _ _ ↦ AEEqFun.smul_toGerm _ _) (fun _ _ ↦ AEEqFun.smul_toGerm _ _)
      AEEqFun.pow_toGerm
    · intro n
      -- The locally chosen cast is scalar multiplication of the native unit.
      change (n • (1 : Ω →ₘ[μ] E)).toGerm = n
      simp [AEEqFun.smul_toGerm]
    · intro n
      -- The locally chosen cast is scalar multiplication of the native unit.
      change (n • (1 : Ω →ₘ[μ] E)).toGerm = n
      simp [AEEqFun.smul_toGerm]
  exact equivAEEqFun.ring

/-- The zero class in `L0` is the native zero class. -/
@[simp]
theorem toAEEqFun_zero [Zero E] : (0 : L0 E μ).toAEEqFun = 0 := by
  simp only [← equivAEEqFun_apply, Equiv.zero_def, Equiv.apply_symm_apply]

/-- The unit class in `L0` is the native unit class. -/
@[simp]
theorem toAEEqFun_one [One E] : (1 : L0 E μ).toAEEqFun = 1 := by
  simp only [← equivAEEqFun_apply, Equiv.one_def, Equiv.apply_symm_apply]

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

/-- The commutative ring of native almost-everywhere classes. -/
instance instCommRing [CommRing E] [IsTopologicalRing E] : CommRing (L0 E μ) where
  mul_comm f g := equivAEEqFun.injective (by
    simp only [equivAEEqFun_apply, toAEEqFun_mul]
    exact mul_comm _ _)

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

/-- The module of almost-everywhere classes, using the native scalar action. -/
instance instModule [Semiring 𝕜] [AddCommMonoid E] [ContinuousAdd E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : Module 𝕜 (L0 E μ) :=
  -- Preserve the native scalar action rather than selecting an action through `AddEquiv`.
  toAEEqFun_injective.module 𝕜
    { toFun := toAEEqFun, map_zero' := toAEEqFun_zero, map_add' := toAEEqFun_add }
    toAEEqFun_smul

/-- The algebra structure agrees with the transported module structure. -/
instance instAlgebra [CommSemiring 𝕜] [Ring E] [IsTopologicalRing E] [Algebra 𝕜 E]
    [ContinuousConstSMul 𝕜 E] : Algebra 𝕜 (L0 E μ) :=
  Algebra.ofModule
    (fun c f g ↦ equivAEEqFun.injective (by
      simp only [equivAEEqFun_apply, toAEEqFun_mul, toAEEqFun_smul]
      exact AEEqFun.induction_on₂ f.toAEEqFun g.toAEEqFun fun f hf g hg ↦ by
        simp only [AEEqFun.smul_mk, AEEqFun.mk_mul_mk, smul_mul_assoc]))
    (fun c f g ↦ equivAEEqFun.injective (by
      simp only [equivAEEqFun_apply, toAEEqFun_mul, toAEEqFun_smul]
      exact AEEqFun.induction_on₂ f.toAEEqFun g.toAEEqFun fun f hf g hg ↦ by
        simp only [AEEqFun.smul_mk, AEEqFun.mk_mul_mk, mul_smul_comm]))

/-- Algebra constants are the native constant almost-everywhere classes. -/
@[simp]
theorem toAEEqFun_algebraMap [CommSemiring 𝕜] [Ring E] [IsTopologicalRing E] [Algebra 𝕜 E]
    [ContinuousConstSMul 𝕜 E] (c : 𝕜) :
    (algebraMap 𝕜 (L0 E μ) c).toAEEqFun = AEEqFun.const Ω (algebraMap 𝕜 E c) := by
  simp only [Algebra.algebraMap_eq_smul_one, toAEEqFun_smul, toAEEqFun_one,
    AEEqFun.one_def, AEEqFun.smul_mk, AEEqFun.const, AEEqFun.mk_eq_mk]
  filter_upwards with _
  simp

/-- The representative of an algebra constant agrees almost everywhere with that constant. -/
theorem coeFn_algebraMap [CommSemiring 𝕜] [Ring E] [IsTopologicalRing E] [Algebra 𝕜 E]
    [ContinuousConstSMul 𝕜 E] (c : 𝕜) :
    ((algebraMap 𝕜 (L0 E μ) c) : Ω → E) =ᵐ[μ] Function.const Ω (algebraMap 𝕜 E c) := by
  simpa only [← toAEEqFun_algebraMap] using (AEEqFun.coeFn_const Ω (algebraMap 𝕜 E c) (μ := μ))

/-- The representative of zero vanishes almost everywhere. -/
theorem coeFn_zero [Zero E] : ((0 : L0 E μ) : Ω → E) =ᵐ[μ] 0 := by
  simpa only [← toAEEqFun_zero] using (AEEqFun.coeFn_zero (α := Ω) (β := E) (μ := μ))

/-- The representative of one equals one almost everywhere. -/
theorem coeFn_one [One E] : ((1 : L0 E μ) : Ω → E) =ᵐ[μ] 1 := by
  simpa only [← toAEEqFun_one] using (AEEqFun.coeFn_one (α := Ω) (β := E) (μ := μ))

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
theorem coeFn_natCast [Ring E] [IsTopologicalRing E] (n : ℕ) :
    ((n : L0 E μ) : Ω → E) =ᵐ[μ] Function.const Ω (n : E) := by
  filter_upwards [coeFn_smul n (1 : L0 E μ), coeFn_one (E := E) (μ := μ)] with _x hx h1
  simpa only [nsmul_one, Pi.smul_apply, Pi.one_apply, h1, Function.const_apply] using hx

/-- Integer constants have constant representatives almost everywhere. -/
theorem coeFn_intCast [Ring E] [IsTopologicalRing E] (n : ℤ) :
    ((n : L0 E μ) : Ω → E) =ᵐ[μ] Function.const Ω (n : E) := by
  filter_upwards [coeFn_smul n (1 : L0 E μ), coeFn_one (E := E) (μ := μ)] with _x hx h1
  simpa only [zsmul_one, Pi.smul_apply, Pi.one_apply, h1, Function.const_apply] using hx

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

/-- Constructing a constant function gives the corresponding algebra constant. -/
@[simp]
theorem ofFun_const [CommRing E] [IsTopologicalRing E] (c : E) :
    ofFun (fun _ : Ω ↦ c) aestronglyMeasurable_const = algebraMap E (L0 E μ) c := by
  apply ext
  refine (coeFn_ofFun _ _).trans ?_
  simpa only [Algebra.algebraMap_self_apply, ← Function.const_def] using
    (coeFn_algebraMap (𝕜 := E) (E := E) c).symm

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

end Topological

/-- The image of the zero `Lp` function is zero. -/
@[simp]
theorem ofLp_zero [NormedAddCommGroup E] {p : ℝ≥0∞} : ofLp (0 : Lp E p μ) = (0 : L0 E μ) := by
  apply equivAEEqFun.injective
  simp [equivAEEqFun_apply]

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

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- Including a constant `Lp` function gives the corresponding algebra constant. -/
@[simp]
theorem ofLp_const [NormedCommRing E] {p : ℝ≥0∞} (c : E) :
    ofLp (Lp.const p μ c) = algebraMap E (L0 E μ) c := by
  apply toAEEqFun_injective
  simp only [toAEEqFun_ofLp, Lp.const_val, toAEEqFun_algebraMap,
    Algebra.algebraMap_self_apply]

section PseudoMetric

variable [PseudoMetricSpace E]

private theorem continuous_binary {op : L0 E μ → L0 E μ → L0 E μ} {φ : E → E → E}
    (hφ : Continuous (Function.uncurry φ))
    (hop : ∀ f g, (op f g : Ω → E) =ᵐ[μ] fun x ↦ φ (f x) (g x)) :
    Continuous (Function.uncurry op) := by
  apply continuous_iff_continuousAt.2
  intro g
  apply tendsto_iff_tendstoInMeasure.2
  have h₁ := tendsto_iff_tendstoInMeasure.1 (continuous_fst.tendsto g)
  have h₂ := tendsto_iff_tendstoInMeasure.1 (continuous_snd.tendsto g)
  have h := h₁.continuous_comp₂ h₂ hφ
    (Eventually.of_forall fun f ↦ (hφ.comp_stronglyMeasurable
      (f.1.stronglyMeasurable.prodMk f.2.stronglyMeasurable)).aestronglyMeasurable)
  exact h.congr (fun f ↦ (hop f.1 f.2).symm) (hop g.1 g.2).symm

/-- Addition of random variables is continuous for convergence in measure. -/
instance instContinuousAdd [Add E] [ContinuousAdd E] : ContinuousAdd (L0 E μ) where
  continuous_add := continuous_binary continuous_add coeFn_add

/-- Negation of random variables is continuous for convergence in measure. -/
instance instContinuousNeg [AddGroup E] [IsTopologicalAddGroup E] : ContinuousNeg (L0 E μ) where
  continuous_neg := by
    apply continuous_iff_continuousAt.2
    intro g
    apply tendsto_iff_tendstoInMeasure.2
    have hid : Tendsto (fun f : L0 E μ ↦ f) (𝓝 g) (𝓝 g) := tendsto_id
    have h := (tendsto_iff_tendstoInMeasure.1 hid).continuous_comp
      continuous_neg (Eventually.of_forall fun f ↦ f.aestronglyMeasurable.neg)
    exact h.congr (fun f ↦ (coeFn_neg f).symm) (coeFn_neg g).symm

/-- The bounded integral topology preserves the topological additive group structure. -/
instance instIsTopologicalAddGroup [AddGroup E] [IsTopologicalAddGroup E] :
    IsTopologicalAddGroup (L0 E μ) where

/-- Translation preserves the bounded integral pseudometric for an isometric additive codomain. -/
instance instIsIsometricVAdd [AddCommGroup E] [IsTopologicalAddGroup E]
    [IsIsometricVAdd E E] : IsIsometricVAdd (L0 E μ) (L0 E μ) where
  isometry_vadd f := Isometry.of_dist_eq fun g h ↦ by
    -- The canonical additive action is addition; this changes only its notation.
    change dist (f + g) (f + h) = dist g h
    rw [dist_def, dist_def]
    apply integral_congr_ae
    filter_upwards [coeFn_add f g, coeFn_add f h] with x hx hy
    simp only [hx, hy, Pi.add_apply, dist_add_left]

/-- Subtraction is uniformly continuous when codomain translations are isometries. -/
instance instIsUniformAddGroup [AddCommGroup E] [IsTopologicalAddGroup E]
    [IsIsometricVAdd E E] : IsUniformAddGroup (L0 E μ) where
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

/-- Multiplication of random variables is continuous for convergence in measure. -/
instance instContinuousMul [Mul E] [ContinuousMul E] : ContinuousMul (L0 E μ) where
  continuous_mul := continuous_binary continuous_mul coeFn_mul

/-- The bounded integral topology preserves the topological ring structure. -/
instance instIsTopologicalRing [Ring E] [IsTopologicalRing E] :
    IsTopologicalRing (L0 E μ) where

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
end FiniteMeasure
end TauCeti.L0
