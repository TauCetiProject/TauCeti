/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Multiplication by bounded continuous operator-valued functions on `Lᵖ`

Let `X` be a topological space with a Borel measure `μ` that is inner regular with respect to
compact sets on sets of finite measure, for instance the Haar measure `MeasureTheory.Measure.haar`
of a locally compact group. A bounded continuous function `F : X →ᵇ (E →L[𝕜] E')` acts on
`Lᵖ(X, E)`, for `1 ≤ p < ∞`, by pointwise application, `f ↦ (x ↦ F x (f x))`. This file bundles
that action as `BoundedContinuousFunction.mulLp F μ p hp`, a bounded operator of norm at most
`‖F‖`. When `p = 2` and `E = E' = H` is a Hilbert space, `F ↦ F.mulLp μ 2 _` is a unital
⋆-homomorphism `BoundedContinuousFunction.mulL2StarAlgHom` from `X →ᵇ (H →L[𝕜] H)` to the bounded
operators on `L²(X, H)`. These operators carry the coefficient representation of the regular
covariant representation of a C⋆-dynamical system on `L²(G, H)`.

A bounded continuous scalar function `φ : X →ᵇ 𝕜` acts through the symbol `x ↦ φ x • 1`, giving
the operator `BoundedContinuousFunction.smulLp φ μ p hp` of pointwise multiplication by `φ`. Its
adjoint on `L²` is multiplication by `star φ` (`BoundedContinuousFunction.adjoint_smulLp`). Bounded
weights act on `L²` in this way in weighted energy estimates for elliptic operators.

The symbol is not regarded as an element of `L∞`: on a locally compact group that is not
σ-compact, a Haar measure is not σ-finite, and a continuous operator-valued function need not be
a.e. strongly measurable. Mathlib's Hölder multiplication `ContinuousLinearMap.holderL` therefore
does not apply. Each `f ∈ Lᵖ` with `p < ∞` vanishes outside a σ-finite set, however, and there
inner regularity makes `x ↦ F x (f x)` a.e. strongly measurable,
`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_clm_apply`; this is why `p = ∞` is
excluded. For scalar symbols in `L∞` see `MeasureTheory.Lp.multiplicationOperator`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace BoundedContinuousFunction

variable {X 𝕜 E E' : Type*} [TopologicalSpace X] [MeasurableSpace X] [R1Space X] [BorelSpace X]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {μ : Measure X} [μ.InnerRegularCompactLTTop]

/-- Pointwise application of a bounded continuous operator-valued function to an `Lᵖ` function,
`x ↦ F x (f x)`, is again in `Lᵖ` for `0 < p < ∞`. -/
theorem memLp_apply (F : X →ᵇ (E →L[𝕜] E')) {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (f : Lp E p μ) : MemLp (fun x ↦ F x (f x)) p μ :=
  (Lp.memLp f).of_le_mul (c := ‖F‖)
    (AEFinStronglyMeasurable.aestronglyMeasurable_clm_apply
      ((Lp.memLp f).aefinStronglyMeasurable hp₀ hp) F.continuous)
    (.of_forall fun x ↦ (F x).le_of_opNorm_le (F.norm_coe_le_norm x) _)

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)

variable (μ p) in
/-- Pointwise application of a bounded continuous operator-valued function `F`, as a bounded
operator `f ↦ (x ↦ F x (f x))` from `Lᵖ(X, E)` to `Lᵖ(X, E')` for `1 ≤ p < ∞`. -/
def mulLp (F : X →ᵇ (E →L[𝕜] E')) : Lp E p μ →L[𝕜] Lp E' p μ :=
  LinearMap.mkContinuous
    { toFun f := (F.memLp_apply (zero_lt_one.trans_le Fact.out).ne' hp f).toLp
      map_add' f g := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx]
        simp
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp [hx] }
    ‖F‖ fun f ↦ Lp.norm_le_mul_norm_of_ae_le_mul <| by
      filter_upwards [MemLp.coeFn_toLp (F.memLp_apply (zero_lt_one.trans_le Fact.out).ne' hp f)]
        with x hx
      rw [LinearMap.coe_mk, AddHom.coe_mk, hx]
      exact (F x).le_of_opNorm_le (F.norm_coe_le_norm x) _

/-- The multiplication operator acts by pointwise application almost everywhere. -/
theorem coeFn_mulLp (F : X →ᵇ (E →L[𝕜] E')) (f : Lp E p μ) :
    F.mulLp μ p hp f =ᵐ[μ] fun x ↦ F x (f x) :=
  MemLp.coeFn_toLp (F.memLp_apply (zero_lt_one.trans_le Fact.out).ne' hp f)

variable {hp}

/-- Multiplication operators are determined by their pointwise action: an `Lᵖ` class equal almost
everywhere to `x ↦ F x (f x)` is `F.mulLp μ p hp f`. -/
theorem mulLp_eq_iff {F : X →ᵇ (E →L[𝕜] E')} {f : Lp E p μ} {g : Lp E' p μ} :
    F.mulLp μ p hp f = g ↔ (fun x ↦ F x (f x)) =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ (F.coeFn_mulLp hp f).symm, fun h ↦ Lp.ext ((F.coeFn_mulLp hp f).trans h)⟩

/-- The operator norm of a multiplication operator is at most the supremum norm of its symbol. -/
theorem norm_mulLp_le (F : X →ᵇ (E →L[𝕜] E')) : ‖F.mulLp μ p hp‖ ≤ ‖F‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg F) _

@[simp]
theorem mulLp_zero : (0 : X →ᵇ (E →L[𝕜] E')).mulLp μ p hp = 0 := by
  ext1 f
  rw [mulLp_eq_iff, _root_.zero_apply]
  filter_upwards [Lp.coeFn_zero E' p μ] with x hx
  rw [hx]
  simp

@[simp]
theorem mulLp_add (F G : X →ᵇ (E →L[𝕜] E')) :
    (F + G).mulLp μ p hp = F.mulLp μ p hp + G.mulLp μ p hp := by
  ext1 f
  rw [mulLp_eq_iff, _root_.add_apply]
  filter_upwards [Lp.coeFn_add (F.mulLp μ p hp f) (G.mulLp μ p hp f), F.coeFn_mulLp hp f,
    G.coeFn_mulLp hp f] with x hx hF hG
  rw [hx]
  simp [hF, hG]

@[simp]
theorem mulLp_smul (c : 𝕜) (F : X →ᵇ (E →L[𝕜] E')) :
    (c • F).mulLp μ p hp = c • F.mulLp μ p hp := by
  ext1 f
  rw [mulLp_eq_iff, _root_.smul_apply]
  filter_upwards [Lp.coeFn_smul c (F.mulLp μ p hp f), F.coeFn_mulLp hp f] with x hx hF
  simp [hx, hF]

/-- Multiplication by the constant identity function is the identity operator. -/
@[simp]
theorem mulLp_one : (1 : X →ᵇ (E →L[𝕜] E)).mulLp μ p hp = 1 := by
  ext1 f
  rw [mulLp_eq_iff]
  simp

/-- Multiplication operators compose by pointwise composition of their symbols. -/
@[simp]
theorem mulLp_mul (F G : X →ᵇ (E →L[𝕜] E)) :
    (F * G).mulLp μ p hp = F.mulLp μ p hp * G.mulLp μ p hp := by
  ext1 f
  rw [mulLp_eq_iff, mul_apply_eq_comp]
  filter_upwards [F.coeFn_mulLp hp (G.mulLp μ p hp f), G.coeFn_mulLp hp f] with x hF hG
  simp [hF, hG]

/-! ### Scalar symbols -/

variable (μ p hp) in
/-- Pointwise multiplication by a bounded continuous scalar function `φ`, as a bounded operator
`f ↦ (x ↦ φ x • f x)` on `Lᵖ(X, E)` for `1 ≤ p < ∞`. It is multiplication by the operator-valued
symbol `x ↦ φ x • 1`, the image of `φ` under the algebra map `𝕜 → (E →L[𝕜] E)` applied
pointwise. -/
def smulLp (φ : X →ᵇ 𝕜) : Lp E p μ →L[𝕜] Lp E p μ :=
  mulLp μ p hp <| AlgHom.compLeftContinuousBounded 𝕜 (Algebra.ofId 𝕜 (E →L[𝕜] E))
    (AddMonoidHomClass.lipschitz_of_bound _ 1 fun c ↦ by
      rw [Algebra.ofId_apply, norm_algebraMap, mul_comm]
      exact mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg c)) φ

variable (hp) in
/-- Multiplication by a scalar function acts by pointwise multiplication almost everywhere. -/
theorem coeFn_smulLp (φ : X →ᵇ 𝕜) (f : Lp E p μ) :
    φ.smulLp μ p hp f =ᵐ[μ] fun x ↦ φ x • f x := by
  rw [smulLp]
  refine (coeFn_mulLp hp _ f).trans (.of_forall fun x ↦ ?_)
  simp only [AlgHom.compLeftContinuousBounded_apply_apply, Algebra.ofId_apply,
    Algebra.algebraMap_eq_smul_one, _root_.smul_apply, one_apply_eq_self]

/-- Multiplication by `φ` has norm at most the supremum norm of `φ`. -/
theorem norm_smulLp_apply_le (φ : X →ᵇ 𝕜) (f : Lp E p μ) :
    ‖φ.smulLp μ p hp f‖ ≤ ‖φ‖ * ‖f‖ :=
  Lp.norm_le_mul_norm_of_ae_le_mul <| by
    filter_upwards [coeFn_smulLp hp φ f] with x hx
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)

/-- Multiplication operators are monotone in the pointwise norm of their scalar symbols. -/
theorem norm_smulLp_apply_le_norm_smulLp_apply {φ ψ : X →ᵇ 𝕜} (h : ∀ x, ‖φ x‖ ≤ ‖ψ x‖)
    (f : Lp E p μ) : ‖φ.smulLp μ p hp f‖ ≤ ‖ψ.smulLp μ p hp f‖ :=
  Lp.norm_le_norm_of_ae_le <| by
    filter_upwards [coeFn_smulLp hp φ f, coeFn_smulLp hp ψ f] with x h₁ h₂
    rw [h₁, h₂, norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)

@[simp]
theorem smulLp_add (φ ψ : X →ᵇ 𝕜) :
    (φ + ψ).smulLp μ p hp = φ.smulLp μ p hp + ψ.smulLp μ p hp (E := E) := by
  simp only [smulLp, map_add, mulLp_add]

@[simp]
theorem smulLp_smul (c : 𝕜) (φ : X →ᵇ 𝕜) :
    (c • φ).smulLp μ p hp = c • φ.smulLp μ p hp (E := E) := by
  simp only [smulLp, map_smul, mulLp_smul]

@[simp]
theorem smulLp_zero : (0 : X →ᵇ 𝕜).smulLp μ p hp = (0 : Lp E p μ →L[𝕜] Lp E p μ) := by
  simp only [smulLp, map_zero, mulLp_zero]

/-- Multiplication by the constant function `1` is the identity operator. -/
@[simp]
theorem smulLp_one : (1 : X →ᵇ 𝕜).smulLp μ p hp = (1 : Lp E p μ →L[𝕜] Lp E p μ) := by
  simp only [smulLp, map_one, mulLp_one]

/-- Multiplication by a constant function is multiplication by the constant. -/
@[simp]
theorem smulLp_const (c : 𝕜) :
    (const X c).smulLp μ p hp = c • (1 : Lp E p μ →L[𝕜] Lp E p μ) := by
  rw [← smulLp_one (hp := hp), ← smulLp_smul]
  congr 1
  ext x
  simp

/-- Multiplication operators by scalar functions compose by multiplying the functions. -/
@[simp]
theorem smulLp_mul (φ ψ : X →ᵇ 𝕜) :
    (φ * ψ).smulLp μ p hp = φ.smulLp μ p hp * ψ.smulLp μ p hp (E := E) := by
  simp only [smulLp, map_mul, mulLp_mul]

section Real

variable [NormedSpace ℝ E]

/-- Multiplication by a real function `φ` is dominated by multiplication by any `ψ ≥ |φ|`. -/
theorem norm_smulLp_apply_le_of_abs_le {φ ψ : X →ᵇ ℝ} (h : ∀ x, |φ x| ≤ ψ x) (f : Lp E p μ) :
    ‖φ.smulLp μ p hp f‖ ≤ ‖ψ.smulLp μ p hp f‖ :=
  norm_smulLp_apply_le_norm_smulLp_apply (fun x ↦ by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (h x).trans (le_abs_self _)) f

end Real

end Lp

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The adjoint of multiplication by `F` is multiplication by the pointwise adjoint `star F`. -/
@[simp]
theorem adjoint_mulLp (F : X →ᵇ (H →L[𝕜] H)) :
    ContinuousLinearMap.adjoint (F.mulLp μ 2 ENNReal.ofNat_ne_top) =
      (star F).mulLp μ 2 ENNReal.ofNat_ne_top := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(star F).coeFn_mulLp ENNReal.ofNat_ne_top f,
    F.coeFn_mulLp ENNReal.ofNat_ne_top g] with x hF hG
  simp [hF, hG, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- The adjoint of multiplication by a scalar function `φ` is multiplication by `star φ`. -/
@[simp]
theorem adjoint_smulLp (φ : X →ᵇ 𝕜) :
    ContinuousLinearMap.adjoint (φ.smulLp μ 2 ENNReal.ofNat_ne_top (E := H)) =
      (star φ).smulLp μ 2 ENNReal.ofNat_ne_top := by
  rw [smulLp, smulLp, adjoint_mulLp]
  congr 1
  ext1 x
  rw [star_apply, AlgHom.compLeftContinuousBounded_apply_apply,
    AlgHom.compLeftContinuousBounded_apply_apply, Algebra.ofId_apply, Algebra.ofId_apply,
    star_apply, algebraMap_star_comm]

/-- Moving a scalar multiplication operator across the `L²` inner product conjugates its
symbol. -/
theorem inner_smulLp_apply_left (φ : X →ᵇ 𝕜) (f g : Lp H 2 μ) :
    ⟪φ.smulLp μ 2 ENNReal.ofNat_ne_top f, g⟫_𝕜 =
      ⟪f, (star φ).smulLp μ 2 ENNReal.ofNat_ne_top g⟫_𝕜 := by
  rw [← adjoint_smulLp, ContinuousLinearMap.adjoint_inner_right]

variable (μ) in
/-- Multiplication of `L²(X, H)` by bounded continuous operator-valued functions, as a unital
⋆-homomorphism into the bounded operators on `L²(X, H)`. -/
def mulL2StarAlgHom : (X →ᵇ (H →L[𝕜] H)) →⋆ₐ[𝕜] (Lp H 2 μ →L[𝕜] Lp H 2 μ) where
  toFun F := F.mulLp μ 2 ENNReal.ofNat_ne_top
  map_one' := mulLp_one
  map_mul' := mulLp_mul
  map_zero' := mulLp_zero
  map_add' := mulLp_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mulLp_smul, mulLp_one]
  map_star' F := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_mulLp]

@[simp]
theorem mulL2StarAlgHom_apply (F : X →ᵇ (H →L[𝕜] H)) :
    mulL2StarAlgHom μ F = F.mulLp μ 2 ENNReal.ofNat_ne_top :=
  (rfl)

end Hilbert

end BoundedContinuousFunction
