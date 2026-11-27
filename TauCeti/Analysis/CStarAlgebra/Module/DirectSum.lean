/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.FiniteSum
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Hilbert direct sums of C⋆-modules

For an arbitrary (possibly infinite or uncountable) index type `ι` and a family `E : ι → Type*`
of `CStarModule`s over a (possibly nonunital) C⋆-algebra `A`, this file constructs the Hilbert
direct sum `TauCeti.HilbertDirectSum A E`, consisting of dependent families `x : ∀ i, E i` whose
diagonal inner products `⟪x i, x i⟫_A` are unconditionally summable in the norm topology of `A`.
Building on the finite orthogonal sum infrastructure and finite-sum estimates in
`TauCeti.Analysis.CStarAlgebra.Module.FiniteSum`, off-diagonal inner products `⟪x i, y i⟫_A` are
unconditionally summable in `A` whenever the diagonal series converge, and unconditional
summability is preserved under coordinatewise addition and scalar actions. Consequently
`HilbertDirectSum A E` is a `CStarModule A` under `⟪x, y⟫_A = ∑' i, ⟪x i, y i⟫_A`, complete
whenever every summand `E i` is complete.

Every element `x` is the unconditional norm sum `∑' i, single A E i (x i)` of its coordinates,
so finitely supported families are dense; when `ι` is finite, `HilbertDirectSum A E` agrees
isometrically and inner-product-preservingly with `C⋆ᵐᵒᵈ(A, Π i, E i)`. Finally, the `ℓ²` sum
`lp E 2` of families whose squared coordinate norms are summable (`Summable (fun i ↦ ‖x i‖ ^ 2)`)
includes contractively, injectively, and with dense range into `HilbertDirectSum A E`, and agrees
isometrically with `HilbertDirectSum ℂ E` via `equivLp` when `A = ℂ`. Right Hilbert `B`-modules are
covered throughout by taking `A = Bᵐᵒᵖ`.

## Main declarations

* `TauCeti.HilbertDirectSum`: the Hilbert direct sum `⊕ᵢ E i` of a family of `CStarModule`s,
  equipped with `CStarModule A`, `NormedAddCommGroup`, `NormedSpace ℂ`, and `CompleteSpace`
  (when `[∀ i, CompleteSpace (E i)]`).
* `TauCeti.HilbertDirectSum.single`, `TauCeti.HilbertDirectSum.evalCLM`,
  `TauCeti.HilbertDirectSum.trunc`: coordinate inclusions, coordinate projections, and finite-set
  truncations, with `hasSum_single`, `continuousLinearMap_ext_single`, `mem_range_ofDFinsupp_iff`,
  and `denseRange_ofDFinsupp`.
* `TauCeti.HilbertDirectSum.equivWithCStarModulePi`: agreement with `C⋆ᵐᵒᵈ(A, Π i, E i)` when
  `[Fintype ι]`.
* `TauCeti.HilbertDirectSum.ofLp`, `TauCeti.HilbertDirectSum.equivLp`: contractive, injective
  continuous linear map `lp E 2 →L[ℂ] HilbertDirectSum A E` (via `norm_sq_le_tsum_norm_sq`) with
  `mem_range_ofLp_iff` and dense range (`denseRange_ofLp`), and complex linear isometric
  equivalence `HilbertDirectSum ℂ E ≃ₗᵢ[ℂ] lp E 2` when `A = ℂ` (via `hasSum_norm_sq` and
  `norm_sq_eq_tsum_norm_sq`).

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1,
  pp. 6–7.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.14.
-/

public section

noncomputable section

open Filter Topology Finset
open scoped ENNReal NNReal WithCStarModule

/-! ### Hilbert direct sums over arbitrary index sets -/

namespace TauCeti

/-- The Hilbert direct sum `⊕ᵢ E i` of a family of `CStarModule`s over `A`, consisting of
dependent families `x : ∀ i, E i` whose diagonal inner products `⟪x i, x i⟫_A` are unconditionally
summable in `A`. For right Hilbert `B`-modules, take `A = Bᵐᵒᵖ`. -/
structure HilbertDirectSum (A : Type*) {ι : Type*} (E : ι → Type*)
    [TopologicalSpace A] [AddCommMonoid A] [∀ i, Inner A (E i)] where
  /-- The underlying coordinate family. -/
  toFun : ∀ i, E i
  /-- Unconditional summability of the diagonal inner products `⟪x i, x i⟫_A` in `A`. -/
  summable_inner_self' : Summable fun i ↦ inner A (toFun i) (toFun i)

namespace HilbertDirectSum

section DFunLike

variable {A ι : Type*} {E : ι → Type*}
  [TopologicalSpace A] [AddCommMonoid A] [∀ i, Inner A (E i)]

instance instDFunLike : DFunLike (HilbertDirectSum A E) ι E where
  coe x := x.toFun
  coe_injective x y h := by cases x; cases y; congr

@[simp]
theorem mk_apply (f : ∀ i, E i) (hf : Summable fun i ↦ inner A (f i) (f i)) (i : ι) :
    (⟨f, hf⟩ : HilbertDirectSum A E) i = f i := (rfl)

@[ext]
theorem ext {x y : HilbertDirectSum A E} (h : ∀ i, x i = y i) : x = y :=
  DFunLike.ext x y h

/-- The diagonal inner products `⟪x i, x i⟫_A` of any `x : HilbertDirectSum A E` are
unconditionally summable in `A`. -/
theorem summable_inner_self (x : HilbertDirectSum A E) :
    Summable fun i ↦ inner A (x i) (x i) :=
  x.summable_inner_self'

instance instInner : Inner A (HilbertDirectSum A E) where
  inner x y := ∑' i, inner A (x i) (y i)

/-- The `A`-valued inner product `⟪x, y⟫_A` is the unconditional sum `∑' i, ⟪x i, y i⟫_A`. -/
theorem inner_def (x y : HilbertDirectSum A E) :
    inner A x y = ∑' i, inner A (x i) (y i) := (rfl)

end DFunLike

section Norm

variable {A ι : Type*} {E : ι → Type*}
  [TopologicalSpace A] [AddCommMonoid A] [Norm A] [∀ i, Inner A (E i)]

instance instNorm : Norm (HilbertDirectSum A E) where
  norm x := √‖inner A x x‖

/-- The norm on `HilbertDirectSum A E` is `√‖∑' i, ⟪x i, x i⟫_A‖`. -/
theorem norm_def (x : HilbertDirectSum A E) :
    ‖x‖ = √‖∑' i, inner A (x i) (x i)‖ := (rfl)

end Norm

section Algebraic

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  [∀ i, AddCommGroup (E i)] [∀ i, Norm (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

instance instZero : Zero (HilbertDirectSum A E) where
  zero := ⟨0, by simp [summable_zero]⟩

instance instNeg : Neg (HilbertDirectSum A E) where
  neg x := ⟨fun i ↦ -x i, by simpa using x.summable_inner_self⟩

instance instSMulComplex : SMul ℂ (HilbertDirectSum A E) where
  smul c x := ⟨fun i ↦ c • x i, by
    have h : (fun i ↦ inner A (c • x i) (c • x i)) =
        fun i ↦ (star c * c) • inner A (x i) (x i) := by
      ext i; simp [smul_smul, mul_comm]
    rw [h]
    exact x.summable_inner_self.const_smul (star c * c)⟩

instance instSMulNat : SMul ℕ (HilbertDirectSum A E) where
  smul n x := ⟨fun i ↦ n • x i, by
    have h : (fun i ↦ inner A (n • x i) (n • x i)) =
        fun i ↦ inner A ((n : ℂ) • x i) ((n : ℂ) • x i) := by
      ext i; rw [Nat.cast_smul_eq_nsmul]
    rw [h]
    exact ((n : ℂ) • x).summable_inner_self⟩

instance instSMulInt : SMul ℤ (HilbertDirectSum A E) where
  smul z x := ⟨fun i ↦ z • x i, by
    have h : (fun i ↦ inner A (z • x i) (z • x i)) =
        fun i ↦ inner A ((z : ℂ) • x i) ((z : ℂ) • x i) := by
      ext i; rw [Int.cast_smul_eq_zsmul]
    rw [h]
    exact ((z : ℂ) • x).summable_inner_self⟩

instance instSMulCoeff : SMul A (HilbertDirectSum A E) where
  smul a x := ⟨fun i ↦ a • x i, by
    have h : (fun i ↦ inner A (a • x i) (a • x i)) =
        fun i ↦ ContinuousLinearMap.mulLeftRight ℂ A a (star a) (inner A (x i) (x i)) := by
      ext i
      simp [CStarModule.inner_op_smul_left, mul_assoc]
    rw [h]
    exact (ContinuousLinearMap.mulLeftRight ℂ A a (star a)).summable x.summable_inner_self⟩

@[simp] theorem zero_apply (i : ι) : (0 : HilbertDirectSum A E) i = 0 := (rfl)
@[simp] theorem neg_apply (x : HilbertDirectSum A E) (i : ι) : (-x) i = -x i := (rfl)
@[simp] theorem smul_complex_apply (c : ℂ) (x : HilbertDirectSum A E) (i : ι) :
    (c • x) i = c • x i := (rfl)
@[simp] theorem nsmul_apply (n : ℕ) (x : HilbertDirectSum A E) (i : ι) :
    (n • x) i = n • x i := (rfl)
@[simp] theorem zsmul_apply (z : ℤ) (x : HilbertDirectSum A E) (i : ι) :
    (z • x) i = z • x i := (rfl)
@[simp] theorem smul_coeff_apply (a : A) (x : HilbertDirectSum A E) (i : ι) :
    (a • x) i = a • x i := (rfl)

end Algebraic

section CStarModule

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, AddCommGroup (E i)] [∀ i, Norm (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

/-- For `x, y : HilbertDirectSum A E`, the coordinatewise inner products `⟪x i, y i⟫_A` are
unconditionally summable in the norm topology of `A`. -/
theorem summable_inner (x y : HilbertDirectSum A E) :
    Summable fun i ↦ inner A (x i) (y i) :=
  CStarModule.summable_inner_of_summable_inner_self x.summable_inner_self y.summable_inner_self

instance instAdd : Add (HilbertDirectSum A E) where
  add x y := ⟨fun i ↦ x i + y i,
    CStarModule.summable_inner_add_self x.summable_inner_self y.summable_inner_self⟩

instance instSub : Sub (HilbertDirectSum A E) where
  sub x y := x + -y

@[simp] theorem add_apply (x y : HilbertDirectSum A E) (i : ι) : (x + y) i = x i + y i := (rfl)
@[simp] theorem sub_apply (x y : HilbertDirectSum A E) (i : ι) : (x - y) i = x i - y i :=
  sub_eq_add_neg (x i) (y i) |>.symm

instance instAddCommGroup : AddCommGroup (HilbertDirectSum A E) :=
  DFunLike.coe_injective.addCommGroup _
    (rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun x y ↦ funext fun i ↦ sub_apply x y i)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
theorem sum_apply {κ : Type*} (s : Finset κ) (f : κ → HilbertDirectSum A E) (i : ι) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i :=
  map_sum (⟨⟨fun x : HilbertDirectSum A E ↦ x i, zero_apply i⟩,
    fun x y ↦ add_apply x y i⟩ : HilbertDirectSum A E →+ E i) f s

instance instModuleComplex : Module ℂ (HilbertDirectSum A E) :=
  DFunLike.coe_injective.module ℂ ⟨⟨DFunLike.coe, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

/-- The coordinatewise inner products `⟪x i, y i⟫_A` have unconditional sum `⟪x, y⟫_A`. -/
theorem hasSum_inner (x y : HilbertDirectSum A E) :
    HasSum (fun i ↦ inner A (x i) (y i)) (inner A x y) :=
  (summable_inner x y).hasSum

instance instCStarModule : CStarModule A (HilbertDirectSum A E) where
  inner_add_right {x y z} := by
    simp only [inner_def, add_apply, CStarModule.inner_add_right]
    exact (summable_inner x y).tsum_add (summable_inner x z)
  inner_self_nonneg {x} := tsum_nonneg fun i ↦ CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, inner_def]⟩
    ext i
    refine (CStarModule.inner_self (A := A)).mp (le_antisymm ?_ CStarModule.inner_self_nonneg)
    exact (x.summable_inner_self.le_tsum i fun _ _ ↦ CStarModule.inner_self_nonneg).trans_eq h
  inner_op_smul_right {a x y} := by
    simp only [inner_def, smul_coeff_apply, CStarModule.inner_op_smul_right]
    exact ((ContinuousLinearMap.mul ℂ A a).map_tsum (summable_inner x y)).symm
  inner_smul_right_complex {c x y} := by
    simp only [inner_def, smul_complex_apply, CStarModule.inner_smul_right_complex]
    exact (summable_inner x y).tsum_const_smul c
  star_inner x y := by
    rw [inner_def, inner_def, ← (summable_inner x y).hasSum.star.tsum_eq]
    simp_rw [CStarModule.star_inner]
  norm_eq_sqrt_norm_inner_self _ := (rfl)

instance instNormedAddCommGroup : NormedAddCommGroup (HilbertDirectSum A E) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

instance instNormedSpaceComplex : NormedSpace ℂ (HilbertDirectSum A E) :=
  NormedSpace.ofCore (CStarModule.normedSpaceCore A)

instance instIsScalarTowerComplex : IsScalarTower ℂ A (HilbertDirectSum A E) :=
  CStarModule.isScalarTower A (HilbertDirectSum A E)

instance instSMulCommClassComplex : SMulCommClass ℂ A (HilbertDirectSum A E) :=
  CStarModule.smulCommClass A (HilbertDirectSum A E)

instance instSMulCommClassCoeffComplex : SMulCommClass A ℂ (HilbertDirectSum A E) :=
  SMulCommClass.symm ℂ A (HilbertDirectSum A E)

/-- Every finite partial sum of diagonal inner products is bounded above by the full inner
product `⟪x, x⟫_A` in the C⋆-algebra order. -/
theorem sum_inner_self_le (s : Finset ι) (x : HilbertDirectSum A E) :
    ∑ i ∈ s, inner A (x i) (x i) ≤ inner A x x :=
  x.summable_inner_self.sum_le_tsum s fun _ _ ↦ CStarModule.inner_self_nonneg

/-- Every finite partial sum of diagonal inner products has norm at most `‖x‖ ^ 2`. -/
theorem norm_sum_inner_self_le_norm_sq (s : Finset ι) (x : HilbertDirectSum A E) :
    ‖∑ i ∈ s, inner A (x i) (x i)‖ ≤ ‖x‖ ^ 2 := by
  rw [CStarModule.norm_sq_eq A]
  refine CStarAlgebra.norm_le_norm_of_le_of_nonneg (sum_inner_self_le s x) ?_
  exact Finset.sum_nonneg fun _ _ ↦ CStarModule.inner_self_nonneg

/-- The finite-subset C⋆-module seminorm `√‖∑ i ∈ s, ⟪x i, x i⟫_A‖` is at most `‖x‖`. -/
theorem sqrt_norm_sum_inner_self_le_norm (s : Finset ι) (x : HilbertDirectSum A E) :
    √‖∑ i ∈ s, inner A (x i) (x i)‖ ≤ ‖x‖ := by
  calc √‖∑ i ∈ s, inner A (x i) (x i)‖
      ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt (norm_sum_inner_self_le_norm_sq s x)
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg x)

/-- Every coordinate of `x : HilbertDirectSum A E` has norm at most `‖x‖`. -/
theorem norm_apply_le (x : HilbertDirectSum A E) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  simpa [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x i)] using
    sqrt_norm_sum_inner_self_le_norm {i} x

omit [StarOrderedRing A] in
/-- Whenever the squared coordinate norms of `x : HilbertDirectSum A E` are summable,
`‖x‖ ^ 2 ≤ ∑' i, ‖x i‖ ^ 2`. -/
theorem norm_sq_le_tsum_norm_sq (x : HilbertDirectSum A E)
    (hx : Summable fun i ↦ ‖x i‖ ^ 2) :
    ‖x‖ ^ 2 ≤ ∑' i, ‖x i‖ ^ 2 := by
  rw [norm_def, Real.sq_sqrt (norm_nonneg _)]
  refine (norm_tsum_le_tsum_norm ?_).trans_eq
    (tsum_congr fun i ↦ (CStarModule.norm_sq_eq A).symm)
  simpa only [← CStarModule.norm_sq_eq A] using hx

end CStarModule

section CompleteSpace

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

omit [StarOrderedRing A] in
/-- If `x : ∀ i, E i` lies in the `ℓ²` sum (`Memℓp x 2`), then the norms of its diagonal
inner products `‖⟪x i, x i⟫_A‖` are summable. -/
theorem _root_.Memℓp.summable_norm_inner_self {x : ∀ i, E i} (hx : Memℓp x 2) :
    Summable fun i ↦ ‖inner A (x i) (x i)‖ := by
  simpa [CStarModule.norm_sq_eq A] using memℓp_two_iff.mp hx

omit [StarOrderedRing A] in
/-- If `x : ∀ i, E i` lies in the `ℓ²` sum (`Memℓp x 2`), then its diagonal inner products
`⟪x i, x i⟫_A` are unconditionally summable in the norm topology of `A`. -/
theorem _root_.Memℓp.summable_inner_self {x : ∀ i, E i} (hx : Memℓp x 2) :
    Summable fun i ↦ inner A (x i) (x i) :=
  (hx.summable_norm_inner_self (A := A)).of_norm

variable (A E) in
/-- Coordinate projection from `HilbertDirectSum A E` onto the `i`-th summand `E i`. -/
def evalCLM (i : ι) : HilbertDirectSum A E →L[ℂ] E i :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ x i
      map_add' := fun x y ↦ add_apply x y i
      map_smul' := fun c x ↦ smul_complex_apply c x i }
    1 fun x ↦ by simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using norm_apply_le x i

@[simp]
theorem evalCLM_apply (i : ι) (x : HilbertDirectSum A E) : evalCLM A E i x = x i := (rfl)

/-! #### Completeness -/

/-- If `u n i → lim i` for each coordinate `i` and `‖u m - u n‖ ≤ r` eventually in `n`, then
every finite subset `s` satisfies `√‖∑ i ∈ s, ⟪u m i - lim i, u m i - lim i⟫_A‖ ≤ r`. -/
private theorem sqrt_norm_sum_inner_sub_limit_le
    {u : ℕ → HilbertDirectSum A E} {lim : ∀ i, E i}
    (hlim : ∀ i, Tendsto (fun n ↦ u n i) atTop (𝓝 (lim i)))
    {m N : ℕ} {r : ℝ} (hr : ∀ n ≥ N, ‖u m - u n‖ ≤ r) (s : Finset ι) :
    √‖∑ i ∈ s, inner A (u m i - lim i) (u m i - lim i)‖ ≤ r := by
  have htend : Tendsto
      (fun n ↦ √‖∑ i ∈ s, inner A (u m i - u n i) (u m i - u n i)‖) atTop
      (𝓝 √‖∑ i ∈ s, inner A (u m i - lim i) (u m i - lim i)‖) := by
    refine (Real.continuous_sqrt.comp continuous_norm).tendsto _ |>.comp ?_
    refine tendsto_finsetSum s fun i _ ↦ ?_
    let _ : NormedSpace ℂ (E i) := .ofCore (CStarModule.normedSpaceCore A)
    have hsub : Tendsto (fun n ↦ u m i - u n i) atTop (𝓝 (u m i - lim i)) :=
      tendsto_const_nhds.sub (hlim i)
    exact CStarModule.continuous_inner.tendsto _ |>.comp (hsub.prodMk_nhds hsub)
  refine le_of_tendsto htend (eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩)
  simpa only [sub_apply] using (sqrt_norm_sum_inner_self_le_norm s (u m - u n)).trans (hr n hn)

/-- The coordinatewise limit `lim` of a Cauchy sequence in `HilbertDirectSum A E` has diagonal
inner products unconditionally summable in the norm topology of `A`. -/
private theorem summable_inner_self_of_cauchySeq
    {u : ℕ → HilbertDirectSum A E} (hu : CauchySeq u) {lim : ∀ i, E i}
    (hlim : ∀ i, Tendsto (fun n ↦ u n i) atTop (𝓝 (lim i))) :
    Summable fun i ↦ inner A (lim i) (lim i) := by
  classical
  rw [summable_iff_vanishing_norm]
  intro ε hε
  set δ := √ε / 3
  have hδ : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu δ hδ
  have hN_le : ∀ n ≥ N, ‖u N - u n‖ ≤ δ := fun n hn ↦
    (dist_eq_norm (u N) (u n) ▸ hN N le_rfl n hn).le
  obtain ⟨s₀, hs₀⟩ := (summable_iff_vanishing_norm.mp (u N).summable_inner_self) (δ ^ 2)
    (by positivity)
  refine ⟨s₀, fun t ht ↦ ?_⟩
  have h₁ : √‖∑ i ∈ t, inner A (lim i - u N i) (lim i - u N i)‖ ≤ δ := by
    have hsymm : (∑ i ∈ t, inner A (lim i - u N i) (lim i - u N i)) =
        ∑ i ∈ t, inner A (u N i - lim i) (u N i - lim i) :=
      Finset.sum_congr rfl fun i _ ↦ by
        rw [← neg_sub (u N i) (lim i), CStarModule.inner_neg_left, CStarModule.inner_neg_right,
          neg_neg]
    rw [hsymm]
    exact sqrt_norm_sum_inner_sub_limit_le hlim hN_le t
  have h₂ : √‖∑ i ∈ t, inner A (u N i) (u N i)‖ ≤ δ :=
    (Real.sqrt_le_sqrt (hs₀ t ht).le).trans_eq (Real.sqrt_sq hδ.le)
  have h₃ : √‖∑ i ∈ t, inner A (lim i) (lim i)‖ ≤ 2 * δ := by
    calc √‖∑ i ∈ t, inner A (lim i) (lim i)‖
        = √‖∑ i ∈ t, inner A ((lim i - u N i) + u N i) ((lim i - u N i) + u N i)‖ := by
          simp only [sub_add_cancel]
      _ ≤ √‖∑ i ∈ t, inner A (lim i - u N i) (lim i - u N i)‖ +
          √‖∑ i ∈ t, inner A (u N i) (u N i)‖ :=
        CStarModule.sqrt_norm_sum_inner_add_le t (fun i ↦ lim i - u N i) (u N)
      _ ≤ δ + δ := add_le_add h₁ h₂
      _ = 2 * δ := (two_mul δ).symm
  calc ‖∑ i ∈ t, inner A (lim i) (lim i)‖
      = (√‖∑ i ∈ t, inner A (lim i) (lim i)‖) ^ 2 := (Real.sq_sqrt (norm_nonneg _)).symm
    _ ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h₃ 2
    _ = 4 / 9 * ε := by
        dsimp [δ]
        rw [mul_pow, div_pow, Real.sq_sqrt hε.le]
        ring
    _ < ε := by linarith

/-- `HilbertDirectSum A E` is complete whenever every summand `E i` is complete. -/
instance instCompleteSpace [∀ i, CompleteSpace (E i)] :
    CompleteSpace (HilbertDirectSum A E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hu_coord : ∀ i, CauchySeq (fun n ↦ u n i) := fun i ↦
    (evalCLM A E i).uniformContinuous.comp_cauchySeq hu
  choose lim hlim using fun i ↦ cauchySeq_tendsto_of_complete (hu_coord i)
  let y : HilbertDirectSum A E := ⟨lim, summable_inner_self_of_cauchySeq hu hlim⟩
  refine ⟨y, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  set r := ε / 2
  have hr_pos : 0 < r := half_pos hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu r hr_pos
  refine ⟨N, fun m hm ↦ ?_⟩
  have hm_le : ∀ n ≥ N, ‖u m - u n‖ ≤ r := fun n hn ↦
    (dist_eq_norm (u m) (u n) ▸ hN m hm n hn).le
  have htsum : ‖inner A (u m - y) (u m - y)‖ ≤ r ^ 2 := by
    refine le_of_tendsto (continuous_norm.tendsto _ |>.comp (u m - y).summable_inner_self.hasSum)
      (Eventually.of_forall fun s ↦ ?_)
    have hs := sqrt_norm_sum_inner_sub_limit_le hlim hm_le s
    calc ‖∑ i ∈ s, inner A ((u m - y) i) ((u m - y) i)‖
        = (√‖∑ i ∈ s, inner A (u m i - lim i) (u m i - lim i)‖) ^ 2 := by
          simp only [sub_apply, y, mk_apply]
          exact (Real.sq_sqrt (norm_nonneg _)).symm
      _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [dist_eq_norm, CStarModule.norm_eq_sqrt_norm_inner_self (A := A)]
  exact (Real.sqrt_le_sqrt htsum).trans_eq (Real.sqrt_sq hr_pos.le) |>.trans_lt (half_lt_self hε)

end CompleteSpace

section Coordinates

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

/-! #### Coordinate inclusions, projections, truncations, and finite-support density -/

variable (A E) in
/-- Coordinate inclusion of the `i`-th summand `E i` into `HilbertDirectSum A E` as a complex
linear isometry. -/
def single [DecidableEq ι] (i : ι) : E i →ₗᵢ[ℂ] HilbertDirectSum A E where
  toLinearMap :=
    { toFun := fun y ↦ ⟨Pi.single i y, summable_of_ne_finset_zero (s := {i}) fun j hj ↦ by
        rw [Finset.mem_singleton] at hj
        simp [Pi.single_eq_of_ne hj]⟩
      map_add' := fun y₁ y₂ ↦ by ext j; exact congrFun (Pi.single_add i y₁ y₂) j
      map_smul' := fun c y ↦ by ext j; exact congrFun (Pi.single_smul i c y) j }
  norm_map' y := by
    rw [norm_def, tsum_eq_single i (fun j hj ↦ by simp [Pi.single_eq_of_ne hj])]
    simp [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) y]

/-- Evaluating `HilbertDirectSum.single A E i y` at coordinate `j` gives `Pi.single i y j`. -/
theorem single_apply [DecidableEq ι] (i : ι) (y : E i) (j : ι) :
    single A E i y j = Pi.single i y j := (rfl)

@[simp]
theorem single_apply_same [DecidableEq ι] (i : ι) (y : E i) :
    single A E i y i = y := by
  simp [single_apply]

@[simp]
theorem single_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) (y : E i) :
    single A E i y j = 0 := by
  simp [single_apply, h]

@[simp]
theorem inner_single_left [DecidableEq ι] (i : ι) (y : E i) (x : HilbertDirectSum A E) :
    inner A (single A E i y) x = inner A y (x i) := by
  rw [inner_def, tsum_eq_single i (fun j hj ↦ by simp [single_apply_of_ne hj])]
  simp

@[simp]
theorem inner_single_right [DecidableEq ι] (x : HilbertDirectSum A E) (i : ι) (y : E i) :
    inner A x (single A E i y) = inner A (x i) y := by
  rw [inner_def, tsum_eq_single i (fun j hj ↦ by simp [single_apply_of_ne hj])]
  simp

/-- The `i`-th coordinate inclusion and projection on `HilbertDirectSum A E` form a C⋆-module
adjoint pair. -/
theorem isAdjointPair_single_evalCLM [DecidableEq ι] (i : ι) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (single A E i) (evalCLM A E i) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun y x ↦ by
    simpa only [evalCLM_apply] using inner_single_left i y x

@[simp]
theorem single_smul [DecidableEq ι] (i : ι) (a : A) (y : E i) :
    single A E i (a • y) = a • single A E i y :=
  (isAdjointPair_single_evalCLM i).map_smul_coeff_cstarModule a y

variable (A E) in
/-- Orthogonal projection onto the coordinates in a finite subset `s : Finset ι`. -/
def trunc [DecidableEq ι] (s : Finset ι) : HilbertDirectSum A E →L[ℂ] HilbertDirectSum A E :=
  ∑ i ∈ s, (single A E i).toContinuousLinearMap.comp (evalCLM A E i)

@[simp]
theorem trunc_empty [DecidableEq ι] : trunc A E ∅ = 0 := by
  simp [trunc]

/-- The finite-coordinate truncation `trunc A E s x` is the finite sum
`∑ i ∈ s, single A E i (x i)`. -/
theorem trunc_eq_sum_single [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) :
    trunc A E s x = ∑ i ∈ s, single A E i (x i) := by
  simp [trunc]

@[simp]
theorem trunc_apply [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) (i : ι) :
    trunc A E s x i = if i ∈ s then x i else 0 := by
  simp [trunc_eq_sum_single, single_apply]

@[simp]
theorem trunc_single [DecidableEq ι] (s : Finset ι) (i : ι) (y : E i) :
    trunc A E s (single A E i y) = if i ∈ s then single A E i y else 0 := by
  by_cases hi : i ∈ s <;> ext j <;> rcases eq_or_ne j i with rfl | hj <;> simp [*]

/-- Pairing a finite-coordinate truncation on the left restricts the inner-product sum to `s`. -/
theorem inner_trunc_left [DecidableEq ι] (s : Finset ι) (x y : HilbertDirectSum A E) :
    inner A (trunc A E s x) y = ∑ i ∈ s, inner A (x i) (y i) := by
  rw [trunc_eq_sum_single, CStarModule.inner_sum_left (A := A)]
  simp

/-- Pairing a finite-coordinate truncation on the right restricts the inner-product sum to `s`. -/
theorem inner_trunc_right [DecidableEq ι] (s : Finset ι) (x y : HilbertDirectSum A E) :
    inner A x (trunc A E s y) = ∑ i ∈ s, inner A (x i) (y i) := by
  rw [trunc_eq_sum_single, CStarModule.inner_sum_right (A := A)]
  simp

/-- Every finite-coordinate truncation `trunc A E s` is self-adjoint as a C⋆-module operator. -/
theorem isAdjointPair_trunc [DecidableEq ι] (s : Finset ι) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (trunc A E s) (trunc A E s) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦
    (inner_trunc_left s x y).trans (inner_trunc_right s x y).symm

@[simp]
theorem trunc_smul [DecidableEq ι] (s : Finset ι) (a : A) (x : HilbertDirectSum A E) :
    trunc A E s (a • x) = a • trunc A E s x :=
  (isAdjointPair_trunc s).map_smul_coeff_cstarModule a x

@[simp]
theorem trunc_trunc [DecidableEq ι] (s t : Finset ι) (x : HilbertDirectSum A E) :
    trunc A E s (trunc A E t x) = trunc A E (s ∩ t) x := by
  ext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht]

/-- Pairing two finite-coordinate truncations restricts the inner-product sum to `s ∩ t`. -/
theorem inner_trunc_trunc [DecidableEq ι] (s t : Finset ι) (x y : HilbertDirectSum A E) :
    inner A (trunc A E s x) (trunc A E t y) = ∑ i ∈ s ∩ t, inner A (x i) (y i) := by
  rw [(isAdjointPair_trunc s).inner_eq_cstarModule, trunc_trunc, inner_trunc_right]

/-- The diagonal inner product of the truncation error `x - trunc A E s x` is the tail
`⟪x, x⟫_A - ∑ i ∈ s, ⟪x i, x i⟫_A`. -/
theorem inner_sub_trunc_self [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) :
    inner A (x - trunc A E s x) (x - trunc A E s x) =
      inner A x x - ∑ i ∈ s, inner A (x i) (x i) := by
  simp only [CStarModule.inner_sub_left (A := A), CStarModule.inner_sub_right (A := A)]
  rw [inner_trunc_trunc, inner_trunc_left, inner_trunc_right]
  simp

/-- Every finite-coordinate truncation does not increase the norm of a vector. -/
theorem norm_trunc_apply_le [DecidableEq ι] (s : Finset ι) (x : HilbertDirectSum A E) :
    ‖trunc A E s x‖ ≤ ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A), inner_trunc_trunc, Finset.inter_self]
  exact sqrt_norm_sum_inner_self_le_norm s x

/-- Every finite-coordinate truncation `trunc A E s` is a contraction. -/
theorem norm_trunc_le [DecidableEq ι] (s : Finset ι) : ‖trunc A E s‖ ≤ 1 :=
  (trunc A E s).opNorm_le_bound zero_le_one fun x ↦ by
    simpa only [one_mul] using norm_trunc_apply_le s x

/-- Every vector `x : HilbertDirectSum A E` is the unconditional norm sum of its coordinate
vectors `single A E i (x i)`. -/
theorem hasSum_single [DecidableEq ι] (x : HilbertDirectSum A E) :
    HasSum (fun i ↦ single A E i (x i)) x := by
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ s : Finset ι,
      ‖∑ i ∈ s, single A E i (x i) - x‖ = √‖inner A x x - ∑ i ∈ s, inner A (x i) (x i)‖ :=
    fun s ↦ by
      rw [← trunc_eq_sum_single, norm_sub_rev,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A), inner_sub_trunc_self]
  simp_rw [hnorm]
  have hlim : Tendsto (fun s : Finset ι ↦ ‖inner A x x - ∑ i ∈ s, inner A (x i) (x i)‖)
      (SummationFilter.unconditional ι).filter (𝓝 0) := by
    simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp (hasSum_inner x x)
  simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hlim

/-- Continuous linear maps out of `HilbertDirectSum A E` into a Hausdorff space are determined by
their values on the coordinate inclusions `single A E i y`. -/
theorem continuousLinearMap_ext_single [DecidableEq ι] {F : Type*} [AddCommMonoid F] [Module ℂ F]
    [TopologicalSpace F] [T2Space F] {f g : HilbertDirectSum A E →L[ℂ] F}
    (h : ∀ i (y : E i), f (single A E i y) = g (single A E i y)) : f = g :=
  ContinuousLinearMap.ext fun x ↦
    ((hasSum_single x).mapL f).unique (by simpa only [h] using (hasSum_single x).mapL g)

/-- Finite-coordinate truncations `trunc A E s x` converge in norm to `x` along `atTop`. -/
theorem tendsto_trunc [DecidableEq ι] (x : HilbertDirectSum A E) :
    Tendsto (fun s : Finset ι ↦ trunc A E s x) atTop (𝓝 x) := by
  have h := x.hasSum_single
  rwa [HasSum, SummationFilter.unconditional_filter,
    funext fun s ↦ (trunc_eq_sum_single s x).symm] at h

variable (A E) in
/-- Complex-linear inclusion of finitely supported dependent families `Π₀ i, E i` into
`HilbertDirectSum A E`. -/
def ofDFinsupp [DecidableEq ι] : (Π₀ i, E i) →ₗ[ℂ] HilbertDirectSum A E :=
  DFinsupp.lsum ℂ fun i ↦ (single A E i).toLinearMap

@[simp]
theorem ofDFinsupp_single [DecidableEq ι] (i : ι) (y : E i) :
    ofDFinsupp A E (DFinsupp.single i y) = single A E i y := by
  simp [ofDFinsupp]

@[simp]
theorem ofDFinsupp_apply [DecidableEq ι] (f : Π₀ i, E i) (i : ι) :
    ofDFinsupp A E f i = f i := by
  have h : (evalCLM A E i).toLinearMap.comp (ofDFinsupp A E) = DFinsupp.lapply i :=
    DFinsupp.lhom_ext fun j y ↦ by
      simp only [LinearMap.comp_apply, ofDFinsupp_single, ContinuousLinearMap.coe_coe,
        evalCLM_apply, single_apply, DFinsupp.lapply_apply]
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [hij, hij.symm]
  exact LinearMap.congr_fun h f

/-- The complex-linear inclusion `ofDFinsupp A E` of finitely supported families is injective. -/
theorem ofDFinsupp_injective [DecidableEq ι] : Function.Injective (ofDFinsupp A E) :=
  fun _ _ h ↦ DFinsupp.ext fun i ↦ by simpa only [ofDFinsupp_apply] using congrArg (· i) h

/-- An element of `HilbertDirectSum A E` lies in the range of `ofDFinsupp A E` if and only if it
has finite coordinate support. -/
theorem mem_range_ofDFinsupp_iff [DecidableEq ι] {x : HilbertDirectSum A E} :
    x ∈ Set.range (ofDFinsupp A E) ↔ {i | x i ≠ 0}.Finite := by
  refine ⟨?_, fun hx ↦ ⟨DFinsupp.mk hx.toFinset fun i ↦ x i, ?_⟩⟩
  · rintro ⟨f, rfl⟩
    exact f.finite_support.subset fun i hi ↦ by simpa [ofDFinsupp_apply] using hi
  · ext i
    rw [ofDFinsupp_apply, DFinsupp.mk_apply]
    split_ifs with hi
    · rfl
    · exact (not_not.mp (hx.mem_toFinset.not.mp hi)).symm

/-- Finitely supported families form a dense complex subspace of `HilbertDirectSum A E`. -/
theorem denseRange_ofDFinsupp [DecidableEq ι] : DenseRange (ofDFinsupp A E) := by
  intro x
  refine mem_closure_of_tendsto (tendsto_trunc x) (Eventually.of_forall fun s ↦ ?_)
  refine ⟨∑ i ∈ s, DFinsupp.single i (x i), ?_⟩
  simp [map_sum, trunc_eq_sum_single]

/-- Elements with finite coordinate support are dense in `HilbertDirectSum A E`. -/
theorem dense_setOf_finite_support :
    Dense {x : HilbertDirectSum A E | {i | x i ≠ 0}.Finite} := by
  classical
  have h : {x : HilbertDirectSum A E | {i | x i ≠ 0}.Finite} = Set.range (ofDFinsupp A E) :=
    Set.ext fun _ ↦ (mem_range_ofDFinsupp_iff (A := A) (E := E)).symm
  rw [h]
  exact denseRange_ofDFinsupp

/-! #### Agreement with Mathlib's finite `WithCStarModule` product -/

section Finite

variable [Fintype ι]

variable (A E) in
/-- When `ι` is finite, `HilbertDirectSum A E` agrees with Mathlib's finite orthogonal sum
`C⋆ᵐᵒᵈ(A, Π i, E i)` via an `A`-equivariant, inner-product-preserving complex linear isometric
equivalence. -/
def equivWithCStarModulePi : HilbertDirectSum A E ≃ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, Π i, E i) where
  toFun x := (WithCStarModule.equiv A (Π i, E i)).symm ⇑x
  invFun z := ⟨WithCStarModule.equiv A (Π i, E i) z,
    hasSum_fintype (fun i ↦
      inner A (WithCStarModule.equiv A (Π i, E i) z i)
        (WithCStarModule.equiv A (Π i, E i) z i)) |>.summable⟩
  map_add' _ _ := WithCStarModule.ext fun _ ↦ by simp
  map_smul' _ _ := WithCStarModule.ext fun _ ↦ by simp
  left_inv _ := by ext i; simp
  right_inv z := (WithCStarModule.equiv A (Π i, E i)).symm_apply_apply z
  norm_map' _ := by simp [WithCStarModule.pi_norm, norm_def, tsum_fintype]

@[simp]
theorem equivWithCStarModulePi_apply (x : HilbertDirectSum A E) (i : ι) :
    equivWithCStarModulePi A E x i = x i := (rfl)

@[simp]
theorem equivWithCStarModulePi_symm_apply (z : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι) :
    (equivWithCStarModulePi A E).symm z i = z i := (rfl)

@[simp]
theorem inner_equivWithCStarModulePi (x y : HilbertDirectSum A E) :
    inner A (equivWithCStarModulePi A E x) (equivWithCStarModulePi A E y) = inner A x y := by
  simp [WithCStarModule.pi_inner, inner_def, tsum_fintype]

@[simp]
theorem inner_equivWithCStarModulePi_symm (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) :
    inner A ((equivWithCStarModulePi A E).symm x)
      ((equivWithCStarModulePi A E).symm y) = inner A x y := by
  rw [← inner_equivWithCStarModulePi (A := A) (E := E)]
  simp

@[simp]
theorem equivWithCStarModulePi_smul (a : A) (x : HilbertDirectSum A E) :
    equivWithCStarModulePi A E (a • x) = a • equivWithCStarModulePi A E x :=
  WithCStarModule.ext fun _ ↦ by simp

@[simp]
theorem equivWithCStarModulePi_symm_smul (a : A) (z : C⋆ᵐᵒᵈ(A, Π i, E i)) :
    (equivWithCStarModulePi A E).symm (a • z) =
      a • (equivWithCStarModulePi A E).symm z := by
  apply (equivWithCStarModulePi A E).injective
  simp

@[simp]
theorem equivWithCStarModulePi_single [DecidableEq ι] (i : ι) (y : E i) :
    equivWithCStarModulePi A E (single A E i y) = WithCStarModule.single A E i y :=
  WithCStarModule.ext fun _ ↦ by simp [single_apply, WithCStarModule.single_apply]

@[simp]
theorem equivWithCStarModulePi_symm_single [DecidableEq ι] (i : ι) (y : E i) :
    (equivWithCStarModulePi A E).symm (WithCStarModule.single A E i y) = single A E i y := by
  apply (equivWithCStarModulePi A E).injective
  simp

end Finite

end Coordinates

section EvalOpNorm

variable {A ι : Type*} {E : ι → Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul A (E i)] [∀ i, CStarModule A (E i)]

/-- Every coordinate projection `evalCLM A E i` on `HilbertDirectSum A E` is a contraction. -/
theorem norm_evalCLM_le (i : ι) : ‖evalCLM A E i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! #### Contractive injective inclusion of the `ℓ²` sum `lp E 2` with dense range -/

variable (A E) in
/-- The contractive injective inclusion with dense range from the `ℓ²` sum `lp E 2` of families
with `Summable (fun i ↦ ‖x i‖ ^ 2)` into `HilbertDirectSum A E`. -/
def ofLp : lp E 2 →L[ℂ] HilbertDirectSum A E :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨⇑x, x.prop.summable_inner_self⟩
      map_add' := fun _ _ ↦ by ext i; rfl
      map_smul' := fun _ _ ↦ by ext i; rfl }
    1 fun x ↦ by
      let y : HilbertDirectSum A E := ⟨⇑x, x.prop.summable_inner_self⟩
      have hsq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 :=
        (norm_sq_le_tsum_norm_sq y (memℓp_two_iff.mp x.prop)).trans_eq (lp.norm_sq_eq_tsum x).symm
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using
        (pow_le_pow_iff_left₀ (norm_nonneg y) (norm_nonneg x) two_ne_zero).mp hsq

@[simp]
theorem ofLp_apply (x : lp E 2) (i : ι) : ofLp A E x i = x i := (rfl)

/-- The canonical inclusion `lp E 2 →L[ℂ] HilbertDirectSum A E` is a contraction. -/
theorem norm_ofLp_le : ‖ofLp A E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The Hilbert direct sum norm of `ofLp A E x` is bounded above by the `ℓ²` sum norm `‖x‖`. -/
theorem norm_ofLp_apply_le (x : lp E 2) : ‖ofLp A E x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (ofLp A E).le_of_opNorm_le norm_ofLp_le x

/-- The canonical inclusion `lp E 2 →L[ℂ] HilbertDirectSum A E` is injective. -/
theorem ofLp_injective : Function.Injective (ofLp A E) := fun x y h ↦ by
  ext i
  exact congrArg (fun z : HilbertDirectSum A E ↦ z i) h

/-- An element of `HilbertDirectSum A E` lies in the range of `ofLp A E` if and only if its
coordinate family lies in `lp E 2` (`Memℓp ⇑x 2`). -/
theorem mem_range_ofLp_iff {x : HilbertDirectSum A E} :
    x ∈ Set.range (ofLp A E) ↔ Memℓp ⇑x 2 :=
  ⟨by rintro ⟨y, rfl⟩; exact y.prop, fun hx ↦ ⟨⟨⇑x, hx⟩, by ext i; rfl⟩⟩

@[simp]
theorem ofLp_single [DecidableEq ι] (i : ι) (y : E i) :
    ofLp A E (lp.single 2 i y) = single A E i y := by
  ext j
  simp [single_apply]

/-- The contractive inclusion `lp E 2 →L[ℂ] HilbertDirectSum A E` has dense range. -/
theorem denseRange_ofLp : DenseRange (ofLp A E) := by
  classical
  intro x
  refine mem_closure_of_tendsto (tendsto_trunc x) (Eventually.of_forall fun s ↦ ?_)
  exact ⟨∑ i ∈ s, lp.single 2 i (x i), by simp [map_sum, trunc_eq_sum_single]⟩

end EvalOpNorm

/-! #### Isometric equivalence with `lp E 2` when `A = ℂ` -/

section Complex

open scoped ComplexOrder

section NormSq

variable {ι : Type*} {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Norm (E i)] [∀ i, Module ℂ (E i)] [∀ i, CStarModule ℂ (E i)]

/-- Over `A = ℂ`, the squared coordinate norms `‖x i‖ ^ 2` have unconditional sum `‖x‖ ^ 2`. -/
theorem hasSum_norm_sq (x : HilbertDirectSum ℂ E) :
    HasSum (fun i ↦ ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
  refine Complex.hasSum_ofReal.mp ?_
  have h := hasSum_inner x x
  rw [CStarModule.inner_self_eq_norm_sq_complex x] at h
  simpa only [CStarModule.inner_self_eq_norm_sq_complex] using h

/-- Over `A = ℂ`, the squared norm on `HilbertDirectSum ℂ E` is `∑' i, ‖x i‖ ^ 2`. -/
theorem norm_sq_eq_tsum_norm_sq (x : HilbertDirectSum ℂ E) :
    ‖x‖ ^ 2 = ∑' i, ‖x i‖ ^ 2 :=
  (hasSum_norm_sq x).tsum_eq.symm

end NormSq

section Memℓp

variable {ι : Type*} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, CStarModule ℂ (E i)]

/-- Over `A = ℂ`, every element of `HilbertDirectSum ℂ E` lies in the `ℓ²` sum `lp E 2`
(`Memℓp ⇑x 2`). -/
theorem memℓp_two (x : HilbertDirectSum ℂ E) : Memℓp ⇑x 2 :=
  memℓp_two_iff.mpr (hasSum_norm_sq x).summable

end Memℓp

section EquivLp

variable {ι : Type*} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CStarModule ℂ (E i)]

variable (E) in
/-- Over `A = ℂ`, the Hilbert direct sum `HilbertDirectSum ℂ E` is complex linearly isometrically
equivalent to the `ℓ²` sum `lp E 2` (inverse to `ofLp ℂ E`). -/
def equivLp : HilbertDirectSum ℂ E ≃ₗᵢ[ℂ] lp E 2 where
  toFun x := ⟨⇑x, memℓp_two x⟩
  invFun z := ofLp ℂ E z
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl
  left_inv _ := by ext i; simp
  right_inv _ := by ext i; simp
  norm_map' x := by
    set z : lp E 2 := ⟨⇑x, memℓp_two x⟩
    have hz : ∀ i, z i = x i := fun _ ↦ rfl
    refine (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg x)).mp ?_
    calc ‖z‖ ^ 2 = ∑' i, ‖z i‖ ^ 2 := lp.norm_sq_eq_tsum z
      _ = ∑' i, ‖x i‖ ^ 2 := tsum_congr fun i ↦ by rw [hz i]
      _ = ‖x‖ ^ 2 := (norm_sq_eq_tsum_norm_sq x).symm

@[simp]
theorem equivLp_apply (x : HilbertDirectSum ℂ E) (i : ι) : equivLp E x i = x i := (rfl)

@[simp]
theorem equivLp_symm_apply (x : lp E 2) (i : ι) : (equivLp E).symm x i = x i := (rfl)

/-- As a continuous linear map, `(equivLp E).symm` coincides with `ofLp ℂ E`. -/
theorem equivLp_symm_toContinuousLinearMap :
    (equivLp E).symm.toLinearIsometry.toContinuousLinearMap = ofLp ℂ E := by
  ext x i
  simp

@[simp]
theorem equivLp_ofLp (x : lp E 2) : equivLp E (ofLp ℂ E x) = x := by
  ext i
  simp

@[simp]
theorem ofLp_equivLp (x : HilbertDirectSum ℂ E) : ofLp ℂ E (equivLp E x) = x := by
  ext i
  simp

@[simp]
theorem equivLp_single [DecidableEq ι] (i : ι) (y : E i) :
    equivLp E (single ℂ E i y) = lp.single 2 i y := by
  ext j
  simp [single_apply]

@[simp]
theorem equivLp_symm_single [DecidableEq ι] (i : ι) (y : E i) :
    (equivLp E).symm (lp.single 2 i y) = single ℂ E i y := by
  apply (equivLp E).injective
  simp

end EquivLp

end Complex

end HilbertDirectSum

end TauCeti
