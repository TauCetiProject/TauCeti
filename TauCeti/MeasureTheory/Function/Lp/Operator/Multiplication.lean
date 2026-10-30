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
