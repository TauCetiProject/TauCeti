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
# Multiplication by bounded continuous operator-valued functions on `L²`

Let `X` be a topological space with a Borel measure `μ` that is inner regular with respect to
compact sets on sets of finite measure, for instance the Haar measure `MeasureTheory.Measure.haar`
of a locally compact group. A bounded continuous function `F : X →ᵇ (E →L[𝕜] E')` acts on
`L²(X, E)` by pointwise application, `f ↦ (x ↦ F x (f x))`. This file bundles that action as
`BoundedContinuousFunction.mulL2 F μ`, a bounded operator of norm at most `‖F‖`. When `E = E' = H`
is a Hilbert space, `F ↦ F.mulL2 μ` is a unital ⋆-homomorphism
`BoundedContinuousFunction.mulL2StarAlgHom` from `X →ᵇ (H →L[𝕜] H)` to the bounded operators on
`L²(X, H)`. These operators carry the coefficient representation of the regular covariant
representation of a C⋆-dynamical system on `L²(G, H)`.

The symbol is not regarded as an element of `L∞`: on a locally compact group that is not
σ-compact, a Haar measure is not σ-finite, and a continuous operator-valued function need not be
a.e. strongly measurable. Mathlib's Hölder multiplication `ContinuousLinearMap.holderL` therefore
does not apply. Each `f ∈ L²` vanishes outside a σ-finite set, however, and there inner regularity
makes `x ↦ F x (f x)` a.e. strongly measurable,
`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_clm_apply`. For scalar symbols in
`L∞` see `MeasureTheory.Lp.multiplicationOperator`.
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

private theorem memLp_apply (F : X →ᵇ (E →L[𝕜] E')) (f : Lp E 2 μ) :
    MemLp (fun x ↦ F x (f x)) 2 μ :=
  (Lp.memLp f).of_le_mul (c := ‖F‖)
    (AEFinStronglyMeasurable.aestronglyMeasurable_clm_apply
      ((Lp.memLp f).aefinStronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top) F.continuous)
    (.of_forall fun x ↦ (F x).le_of_opNorm_le (F.norm_coe_le_norm x) _)

variable (μ) in
/-- Pointwise application of a bounded continuous operator-valued function `F`, as a bounded
operator `f ↦ (x ↦ F x (f x))` from `L²(X, E)` to `L²(X, E')`. -/
def mulL2 (F : X →ᵇ (E →L[𝕜] E')) : Lp E 2 μ →L[𝕜] Lp E' 2 μ :=
  LinearMap.mkContinuous
    { toFun f := (F.memLp_apply f).toLp
      map_add' f g := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx, Pi.add_apply, map_add, Pi.add_apply]
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx, Pi.smul_apply, map_smul, Pi.smul_apply] }
    ‖F‖ fun f ↦ Lp.norm_le_mul_norm_of_ae_le_mul <| by
      filter_upwards [MemLp.coeFn_toLp (F.memLp_apply f)] with x hx
      rw [LinearMap.coe_mk, AddHom.coe_mk, hx]
      exact (F x).le_of_opNorm_le (F.norm_coe_le_norm x) _

/-- The multiplication operator acts by pointwise application almost everywhere. -/
theorem coeFn_mulL2 (F : X →ᵇ (E →L[𝕜] E')) (f : Lp E 2 μ) :
    F.mulL2 μ f =ᵐ[μ] fun x ↦ F x (f x) :=
  MemLp.coeFn_toLp (F.memLp_apply f)

/-- Multiplication operators are determined by their pointwise action: an `L²` class equal almost
everywhere to `x ↦ F x (f x)` is `F.mulL2 μ f`. -/
theorem mulL2_eq_iff {F : X →ᵇ (E →L[𝕜] E')} {f : Lp E 2 μ} {g : Lp E' 2 μ} :
    F.mulL2 μ f = g ↔ (fun x ↦ F x (f x)) =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ (F.coeFn_mulL2 f).symm, fun h ↦ Lp.ext ((F.coeFn_mulL2 f).trans h)⟩

/-- The operator norm of a multiplication operator is at most the supremum norm of its symbol. -/
theorem norm_mulL2_le (F : X →ᵇ (E →L[𝕜] E')) : ‖F.mulL2 μ‖ ≤ ‖F‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg F) _

@[simp]
theorem mulL2_zero : (0 : X →ᵇ (E →L[𝕜] E')).mulL2 μ = 0 := by
  ext1 f
  rw [mulL2_eq_iff, _root_.zero_apply]
  filter_upwards [Lp.coeFn_zero E' 2 μ] with x hx
  rw [hx, coe_zero, Pi.zero_apply, _root_.zero_apply, Pi.zero_apply]

@[simp]
theorem mulL2_add (F G : X →ᵇ (E →L[𝕜] E')) : (F + G).mulL2 μ = F.mulL2 μ + G.mulL2 μ := by
  ext1 f
  rw [mulL2_eq_iff, _root_.add_apply]
  filter_upwards [Lp.coeFn_add (F.mulL2 μ f) (G.mulL2 μ f), F.coeFn_mulL2 f, G.coeFn_mulL2 f]
    with x hx hF hG
  rw [hx, Pi.add_apply, hF, hG, coe_add, Pi.add_apply, _root_.add_apply]

@[simp]
theorem mulL2_smul (c : 𝕜) (F : X →ᵇ (E →L[𝕜] E')) : (c • F).mulL2 μ = c • F.mulL2 μ := by
  ext1 f
  rw [mulL2_eq_iff, _root_.smul_apply]
  filter_upwards [Lp.coeFn_smul c (F.mulL2 μ f), F.coeFn_mulL2 f] with x hx hF
  rw [hx, Pi.smul_apply, hF]
  simp

/-- Multiplication by the constant identity function is the identity operator. -/
@[simp]
theorem mulL2_one : (1 : X →ᵇ (E →L[𝕜] E)).mulL2 μ = 1 := by
  ext1 f
  rw [mulL2_eq_iff]
  simp

/-- Multiplication operators compose by pointwise composition of their symbols. -/
@[simp]
theorem mulL2_mul (F G : X →ᵇ (E →L[𝕜] E)) : (F * G).mulL2 μ = F.mulL2 μ * G.mulL2 μ := by
  ext1 f
  rw [mulL2_eq_iff, mul_apply_eq_comp]
  filter_upwards [F.coeFn_mulL2 (G.mulL2 μ f), G.coeFn_mulL2 f] with x hF hG
  simp [hF, hG]

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The adjoint of multiplication by `F` is multiplication by the pointwise adjoint `star F`. -/
@[simp]
theorem adjoint_mulL2 (F : X →ᵇ (H →L[𝕜] H)) :
    ContinuousLinearMap.adjoint (F.mulL2 μ) = (star F).mulL2 μ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(star F).coeFn_mulL2 f, F.coeFn_mulL2 g] with x hF hG
  simp [hF, hG, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

variable (μ) in
/-- Multiplication of `L²(X, H)` by bounded continuous operator-valued functions, as a unital
⋆-homomorphism into the bounded operators on `L²(X, H)`. -/
def mulL2StarAlgHom : (X →ᵇ (H →L[𝕜] H)) →⋆ₐ[𝕜] (Lp H 2 μ →L[𝕜] Lp H 2 μ) where
  toFun F := F.mulL2 μ
  map_one' := mulL2_one
  map_mul' := mulL2_mul
  map_zero' := mulL2_zero
  map_add' := mulL2_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mulL2_smul, mulL2_one]
  map_star' F := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_mulL2]

@[simp]
theorem mulL2StarAlgHom_apply (F : X →ᵇ (H →L[𝕜] H)) : mulL2StarAlgHom μ F = F.mulL2 μ :=
  (rfl)

end Hilbert

end BoundedContinuousFunction
