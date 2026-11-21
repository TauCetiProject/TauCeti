/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Compact

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Calculus.ParametricIntegral.Segment
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# C¹ jets on a compact set

Let `K` be a compact subset of a real normed space `E` and `V` a real normed space. A *C¹ jet* on
`K` is a pair `(f, D)` of continuous maps `f : K → V` and `D : K → (E →L[ℝ] V)` satisfying the
*segment identity*

`f y - f x = ∫₀¹ D (x + t (y - x)) (y - x) dt`

whenever the segment `[x, y]` lies in `K`. The jets form a closed subspace of the `ℓ¹` product
`C(K, V) × C(K, E →L[ℝ] V)`, so they carry the norm `‖f‖_∞ + ‖D‖_∞` and form a Banach space when
`V` is complete. When `V` is a normed space over a further field `𝕜`, for instance `𝕜 = ℂ`, the
jets form a normed `𝕜`-space; this is how complex-valued `C¹` functions on a compact convex body
are made into a complex Banach space, on which transfer operators act.

Working with jets instead of functions on `E` makes the boundary convention explicit: the
derivative is part of the data, defined on all of `K`, and controlled in the sup norm up to the
boundary. On a compact convex set the derivative component is a derivative within `K` at every
point of `K` (`TauCeti.C1Jet.hasFDerivWithinAt`), so, when within-derivatives on `K` are unique,
it is determined by the values (`TauCeti.C1Jet.ext_value`) and the jets are exactly the pairs
`(f, fderivWithin ℝ f K)` of functions that are `C¹` on `K` (`TauCeti.C1Jet.ofContDiffOn` and
`TauCeti.C1Jet.ofContDiffOn_eq`). Convexity with nonempty interior gives unique within-derivatives
(`uniqueDiffOn_convex`).

## Main definitions

* `TauCeti.c1JetSubmodule 𝕜 K V`: the jets, as a `𝕜`-submodule of
  `WithLp 1 (C(K, V) × C(K, E →L[ℝ] V))`.
* `TauCeti.C1Jet 𝕜 K V`: the normed `𝕜`-space of jets, with components `TauCeti.C1Jet.value`
  and `TauCeti.C1Jet.deriv`.
* `TauCeti.C1Jet.evalCLM`, `TauCeti.C1Jet.derivEvalCLM`: evaluation of the value and of the
  derivative at a point, continuous linear maps of norm at most one.
* `TauCeti.C1Jet.ofContDiffOn`: the jet `(f, fderivWithin ℝ f K)` of a function `C¹` on `K`.

## Main results

* `TauCeti.C1Jet.norm_def`: `‖j‖ = ‖j.value‖ + ‖j.deriv‖`.
* `TauCeti.isClosed_c1JetSubmodule` and `TauCeti.C1Jet.instCompleteSpace`: the jets form a
  Banach space when `V` is complete.
* `TauCeti.C1Jet.norm_value_sub_le`, `TauCeti.C1Jet.lipschitzWith_value`: the value is Lipschitz
  along segments in `K`, with constant `‖j.deriv‖`.
* `TauCeti.C1Jet.norm_value_sub_sub_deriv_le`: the first-order Taylor remainder along a segment is
  controlled by the oscillation of the derivative on that segment.
* `TauCeti.C1Jet.hasFDerivWithinAt`, `TauCeti.C1Jet.contDiffOn`, `TauCeti.C1Jet.fderivWithin_eq`:
  on a compact convex set, every extension of the value is `C¹` on `K`, with derivative within `K`
  given by the derivative component.
* `TauCeti.C1Jet.ext_value`: with unique within-derivatives, a jet is determined by its values.

## References

* A. Gamburd, M. Magee, R. Ronan, *An asymptotic formula for integer points on Markoff–Hurwitz
  varieties*, Ann. of Math. 190 (2019), §4.2, where the transfer operators act on the space of
  `C¹` functions on the ordered simplex with the norm `‖f‖_∞ + ‖∇f‖_∞`.
-/

public section

noncomputable section

open AffineMap MeasureTheory Set
open scoped unitInterval

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} [CompactSpace K]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]

section Submodule

variable (𝕜 V) in
/-- The integral `∫₀¹ D (x + t (y - x)) (y - x) dt` along a segment `[x, y]` contained in `K`,
as a linear functional of `D`. -/
private def segmentIntegralₗ {x y : K} (h : segment ℝ (x : E) y ⊆ K) :
    C(K, E →L[ℝ] V) →ₗ[𝕜] V where
  toFun D :=
    ∫ t : I, D ⟨lineMap (x : E) y (t : ℝ), h (lineMap_mem_segment ℝ _ _ t.property)⟩ ((y : E) - x)
  map_add' D D' := by
    simp only [ContinuousMap.add_apply, add_apply]
    refine integral_add ?_ ?_ <;>
      exact (by fun_prop : Continuous _).integrable_of_hasCompactSupport (.of_compactSpace _)
  map_smul' c D := by
    simp only [ContinuousMap.smul_apply, smul_apply, RingHom.id_apply]
    exact integral_smul c _

variable (𝕜 V) in
/-- The integral `∫₀¹ D (x + t (y - x)) (y - x) dt` along a segment `[x, y]` contained in `K`,
as a continuous linear functional of `D`. -/
private def segmentIntegral {x y : K} (h : segment ℝ (x : E) y ⊆ K) :
    C(K, E →L[ℝ] V) →L[𝕜] V :=
  (segmentIntegralₗ 𝕜 V h).mkContinuous ‖(y : E) - x‖ fun D : C(K, E →L[ℝ] V) ↦ by
    refine (norm_integral_le_of_norm_le_const (C := ‖D‖ * ‖(y : E) - x‖)
      (.of_forall fun t ↦ ?_)).trans ?_
    · exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm _) (norm_nonneg _))
    · simp [mul_comm]

private theorem segmentIntegral_apply {x y : K} (h : segment ℝ (x : E) y ⊆ K)
    (D : C(K, E →L[ℝ] V)) :
    segmentIntegral 𝕜 V h D =
      ∫ t : I, D ⟨lineMap (x : E) y (t : ℝ), h (lineMap_mem_segment ℝ _ _ t.property)⟩
        ((y : E) - x) :=
  (rfl)

variable (𝕜 V) in
/-- The defect `f y - f x - ∫₀¹ D (x + t (y - x)) (y - x) dt` of the segment identity. -/
private def segmentDefect {x y : K} (h : segment ℝ (x : E) y ⊆ K) :
    WithLp 1 (C(K, V) × C(K, E →L[ℝ] V)) →L[𝕜] V :=
  (ContinuousMap.evalCLM 𝕜 y - ContinuousMap.evalCLM 𝕜 x : C(K, V) →L[𝕜] V).comp
      (WithLp.fstL 1 𝕜 _ _) - (segmentIntegral 𝕜 V h).comp (WithLp.sndL 1 𝕜 _ _)

variable (𝕜 K V) in
/-- The `C¹` jets on `K`: the pairs `(f, D)` in the `ℓ¹` product `C(K, V) × C(K, E →L[ℝ] V)`
with `f y - f x = ∫₀¹ D (x + t (y - x)) (y - x) dt` whenever the segment `[x, y]` lies in `K`. -/
def c1JetSubmodule : Submodule 𝕜 (WithLp 1 (C(K, V) × C(K, E →L[ℝ] V))) :=
  ⨅ (x : K) (y : K) (h : segment ℝ (x : E) y ⊆ K),
    LinearMap.ker (segmentDefect 𝕜 V h : WithLp 1 (C(K, V) × C(K, E →L[ℝ] V)) →ₗ[𝕜] V)

theorem mem_c1JetSubmodule_iff {J : WithLp 1 (C(K, V) × C(K, E →L[ℝ] V))} :
    J ∈ c1JetSubmodule 𝕜 K V ↔ ∀ (x y : K) (h : segment ℝ (x : E) y ⊆ K),
      J.fst y - J.fst x =
        ∫ t : I, J.snd ⟨lineMap (x : E) y (t : ℝ), h (lineMap_mem_segment ℝ _ _ t.property)⟩
          ((y : E) - x) := by
  simp only [c1JetSubmodule, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    segmentDefect, sub_apply, ContinuousLinearMap.comp_apply, WithLp.fstL_apply,
    WithLp.sndL_apply, ContinuousMap.evalCLM_apply, segmentIntegral_apply, sub_eq_zero]

theorem isClosed_c1JetSubmodule :
    IsClosed (c1JetSubmodule 𝕜 K V : Set (WithLp 1 (C(K, V) × C(K, E →L[ℝ] V)))) := by
  simp only [c1JetSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun h ↦
    ContinuousLinearMap.isClosed_ker _

end Submodule

variable (𝕜 K V) in
/-- The normed `𝕜`-space of `C¹` jets on `K`: pairs `(f, D)` of continuous maps `f : K → V` and
`D : K → (E →L[ℝ] V)` with `f y - f x = ∫₀¹ D (x + t (y - x)) (y - x) dt` whenever the segment
`[x, y]` lies in `K`, normed by `‖f‖_∞ + ‖D‖_∞`. -/
-- This is a type synonym rather than an abbreviation: instance search on the submodule itself
-- does not find `Submodule.normedSpace`, because unifying the two module structures on
-- `C(K, E →L[ℝ] V)` fails at instance transparency. The instances are provided below.
@[expose] def C1Jet : Type _ := c1JetSubmodule 𝕜 K V

namespace C1Jet

/-- The jets on `K` form a normed additive group, a subgroup of the `ℓ¹` product. -/
instance instNormedAddCommGroup : NormedAddCommGroup (C1Jet 𝕜 K V) :=
  inferInstanceAs (NormedAddCommGroup (c1JetSubmodule 𝕜 K V))

/-- The jets on `K` form a normed `𝕜`-space. -/
instance instNormedSpace : NormedSpace 𝕜 (C1Jet 𝕜 K V) where
  toModule := inferInstanceAs (Module 𝕜 (c1JetSubmodule 𝕜 K V))
  norm_smul_le c j :=
    norm_smul_le c ((show c1JetSubmodule 𝕜 K V from j) : WithLp 1 (C(K, V) × C(K, E →L[ℝ] V)))

/-- The underlying pair `(f, D)` of a jet. -/
private def toProd (j : C1Jet 𝕜 K V) : WithLp 1 (C(K, V) × C(K, E →L[ℝ] V)) :=
  (show c1JetSubmodule 𝕜 K V from j).val

private theorem toProd_mem (j : C1Jet 𝕜 K V) : toProd j ∈ c1JetSubmodule 𝕜 K V :=
  (show c1JetSubmodule 𝕜 K V from j).property

private theorem toProd_injective : Function.Injective (toProd (𝕜 := 𝕜) (K := K) (V := V)) :=
  fun _ _ h ↦ Subtype.ext h

private theorem norm_toProd (j : C1Jet 𝕜 K V) : ‖toProd j‖ = ‖j‖ :=
  (rfl)

/-- The value component `f : K → V` of a jet. -/
def value (j : C1Jet 𝕜 K V) : C(K, V) :=
  (toProd j).fst

/-- The derivative component `D : K → (E →L[ℝ] V)` of a jet. -/
def deriv (j : C1Jet 𝕜 K V) : C(K, E →L[ℝ] V) :=
  (toProd j).snd

@[ext]
theorem ext {j j' : C1Jet 𝕜 K V} (hv : j.value = j'.value) (hd : j.deriv = j'.deriv) :
    j = j' :=
  toProd_injective (WithLp.ofLp_injective _ (Prod.ext hv hd))

/-- **The segment identity**: `f y - f x = ∫₀¹ D (x + t (y - x)) (y - x) dt` whenever the segment
`[x, y]` lies in `K`. -/
theorem sub_eq_integral (j : C1Jet 𝕜 K V) {x y : K} (h : segment ℝ (x : E) y ⊆ K) :
    j.value y - j.value x =
      ∫ t : I, j.deriv ⟨lineMap (x : E) y (t : ℝ), h (lineMap_mem_segment ℝ _ _ t.property)⟩
        ((y : E) - x) :=
  mem_c1JetSubmodule_iff.1 (toProd_mem j) x y h

/-- The jet with value `f` and derivative `D`, given the segment identity. -/
def mk (f : C(K, V)) (D : C(K, E →L[ℝ] V))
    (h : ∀ (x y : K) (h : segment ℝ (x : E) y ⊆ K), f y - f x =
      ∫ t : I, D ⟨lineMap (x : E) y (t : ℝ), h (lineMap_mem_segment ℝ _ _ t.property)⟩
        ((y : E) - x)) :
    C1Jet 𝕜 K V :=
  (⟨WithLp.toLp 1 (f, D), mem_c1JetSubmodule_iff.2 h⟩ : c1JetSubmodule 𝕜 K V)

@[simp]
theorem value_mk (f : C(K, V)) (D : C(K, E →L[ℝ] V)) (h) :
    (mk f D h : C1Jet 𝕜 K V).value = f :=
  (rfl)

@[simp]
theorem deriv_mk (f : C(K, V)) (D : C(K, E →L[ℝ] V)) (h) :
    (mk f D h : C1Jet 𝕜 K V).deriv = D :=
  (rfl)

@[simp]
theorem value_zero : (0 : C1Jet 𝕜 K V).value = 0 :=
  (rfl)

@[simp]
theorem deriv_zero : (0 : C1Jet 𝕜 K V).deriv = 0 :=
  (rfl)

@[simp]
theorem value_add (j j' : C1Jet 𝕜 K V) : (j + j').value = j.value + j'.value :=
  (rfl)

@[simp]
theorem deriv_add (j j' : C1Jet 𝕜 K V) : (j + j').deriv = j.deriv + j'.deriv :=
  (rfl)

@[simp]
theorem value_neg (j : C1Jet 𝕜 K V) : (-j).value = -j.value :=
  (rfl)

@[simp]
theorem deriv_neg (j : C1Jet 𝕜 K V) : (-j).deriv = -j.deriv :=
  (rfl)

@[simp]
theorem value_sub (j j' : C1Jet 𝕜 K V) : (j - j').value = j.value - j'.value :=
  (rfl)

@[simp]
theorem deriv_sub (j j' : C1Jet 𝕜 K V) : (j - j').deriv = j.deriv - j'.deriv :=
  (rfl)

@[simp]
theorem value_smul (c : 𝕜) (j : C1Jet 𝕜 K V) : (c • j).value = c • j.value :=
  (rfl)

@[simp]
theorem deriv_smul (c : 𝕜) (j : C1Jet 𝕜 K V) : (c • j).deriv = c • j.deriv :=
  (rfl)

/-! ### The norm -/

/-- The norm of a jet is `‖f‖_∞ + ‖D‖_∞`. -/
theorem norm_def (j : C1Jet 𝕜 K V) : ‖j‖ = ‖j.value‖ + ‖j.deriv‖ := by
  rw [← norm_toProd j]
  exact WithLp.prod_norm_eq_of_L1 (toProd j)

theorem norm_value_le (j : C1Jet 𝕜 K V) : ‖j.value‖ ≤ ‖j‖ := by
  have := norm_nonneg j.deriv
  rw [norm_def]
  linarith

theorem norm_deriv_le (j : C1Jet 𝕜 K V) : ‖j.deriv‖ ≤ ‖j‖ := by
  have := norm_nonneg j.value
  rw [norm_def]
  linarith

theorem norm_value_apply_le (j : C1Jet 𝕜 K V) (x : K) : ‖j.value x‖ ≤ ‖j‖ :=
  (j.value.norm_coe_le_norm x).trans j.norm_value_le

theorem norm_deriv_apply_le (j : C1Jet 𝕜 K V) (x : K) : ‖j.deriv x‖ ≤ ‖j‖ :=
  (j.deriv.norm_coe_le_norm x).trans j.norm_deriv_le

/-- The jets form a Banach space when `V` is complete. -/
instance instCompleteSpace [CompleteSpace V] : CompleteSpace (C1Jet 𝕜 K V) :=
  isClosed_c1JetSubmodule.completeSpace_coe

/-! ### Evaluation -/

variable (𝕜) in
/-- Evaluation of the value of a jet at a point, as a continuous linear map. -/
def evalCLM (x : K) : C1Jet 𝕜 K V →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun := fun j ↦ j.value x
      map_add' := fun j j' ↦ by simp
      map_smul' := fun c j ↦ by simp }
    1 fun j ↦ by simpa using j.norm_value_apply_le x

variable (𝕜) in
/-- Evaluation of the derivative of a jet at a point, as a continuous linear map. -/
def derivEvalCLM (x : K) : C1Jet 𝕜 K V →L[𝕜] E →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := fun j ↦ j.deriv x
      map_add' := fun j j' ↦ by simp
      map_smul' := fun c j ↦ by simp }
    1 fun j ↦ by simpa using j.norm_deriv_apply_le x

@[simp]
theorem evalCLM_apply (x : K) (j : C1Jet 𝕜 K V) : evalCLM 𝕜 x j = j.value x :=
  (rfl)

@[simp]
theorem derivEvalCLM_apply (x : K) (j : C1Jet 𝕜 K V) : derivEvalCLM 𝕜 x j = j.deriv x :=
  (rfl)

theorem norm_evalCLM_le (x : K) : ‖(evalCLM 𝕜 x : C1Jet 𝕜 K V →L[𝕜] V)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun j ↦ by
    simpa using j.norm_value_apply_le x

theorem norm_derivEvalCLM_le (x : K) :
    ‖(derivEvalCLM 𝕜 x : C1Jet 𝕜 K V →L[𝕜] E →L[ℝ] V)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun j ↦ by
    simpa using j.norm_deriv_apply_le x

/-! ### Estimates along segments -/

/-- **The Lipschitz bound**: along a segment `[x, y]` in `K`, the value of a jet changes by at
most `‖D‖_∞ ‖y - x‖`. -/
theorem norm_value_sub_le (j : C1Jet 𝕜 K V) {x y : K} (h : segment ℝ (x : E) y ⊆ K) :
    ‖j.value y - j.value x‖ ≤ ‖j.deriv‖ * ‖(y : E) - x‖ := by
  rw [j.sub_eq_integral h]
  refine (norm_integral_le_of_norm_le_const (C := ‖j.deriv‖ * ‖(y : E) - x‖)
    (.of_forall fun t ↦ ?_)).trans (by simp)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (j.deriv.norm_coe_le_norm _) (norm_nonneg _))

/-- On a convex set, the value of a jet is Lipschitz with constant `‖D‖_∞`. -/
theorem lipschitzWith_value (j : C1Jet 𝕜 K V) (hK : Convex ℝ K) :
    LipschitzWith ‖j.deriv‖₊ j.value :=
  LipschitzWith.of_dist_le_mul fun y x ↦ by
    simpa [dist_eq_norm, Subtype.dist_eq] using
      j.norm_value_sub_le (hK.segment_subset x.property y.property)

/-- **The first-order Taylor bound along a segment.** If `‖D z - D x‖ ≤ C` at every point `z` of
a segment `[x, y]` in `K`, then `‖f y - f x - D x (y - x)‖ ≤ C ‖y - x‖`. -/
theorem norm_value_sub_sub_deriv_le [CompleteSpace V] (j : C1Jet 𝕜 K V) {x y : K}
    (h : segment ℝ (x : E) y ⊆ K) {C : ℝ}
    (hC : ∀ z : K, (z : E) ∈ segment ℝ (x : E) y → ‖j.deriv z - j.deriv x‖ ≤ C) :
    ‖j.value y - j.value x - j.deriv x ((y : E) - x)‖ ≤ C * ‖(y : E) - x‖ := by
  have hint (D : C(K, E →L[ℝ] V)) : Integrable (fun t : I ↦
      D ⟨lineMap (x : E) y (t : ℝ), h (lineMap_mem_segment ℝ _ _ t.property)⟩ ((y : E) - x)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hconst : j.deriv x ((y : E) - x) = ∫ _ : I, j.deriv x ((y : E) - x) := by
    rw [integral_const, probReal_univ, one_smul]
  rw [j.sub_eq_integral h, hconst, ← integral_sub (hint _) (integrable_const _)]
  refine (norm_integral_le_of_norm_le_const (C := C * ‖(y : E) - x‖)
    (.of_forall fun t ↦ ?_)).trans (by simp)
  rw [← sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (hC _ (lineMap_mem_segment ℝ _ _ t.property)) (norm_nonneg _))

/-! ### Jets and derivatives within `K` -/

/-- On a convex set, the derivative component of a jet is the derivative within `K` of every
function on `E` extending its value. -/
theorem hasFDerivWithinAt [CompleteSpace V] (j : C1Jet 𝕜 K V) (hK : Convex ℝ K) {g : E → V}
    (hg : ∀ x : K, g x = j.value x) (x : K) : HasFDerivWithinAt g (j.deriv x) K x := by
  refine .of_isLittleO <| Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hD⟩ := Metric.continuous_iff.1 j.deriv.continuous x ε hε
  filter_upwards [inter_mem_nhdsWithin K (Metric.ball_mem_nhds (x : E) hδ),
    self_mem_nhdsWithin] with y hy hyK
  lift y to K using hyK
  rw [hg, hg]
  refine j.norm_value_sub_sub_deriv_le (hK.segment_subset x.property y.property) fun z hz ↦ ?_
  rw [← dist_eq_norm]
  refine (hD z ?_).le
  rw [Subtype.dist_eq, dist_eq_norm]
  exact (norm_sub_le_of_mem_segment hz).trans_lt (mem_ball_iff_norm.1 hy.2)

/-- On a convex set, every function on `E` extending the value of a jet is `C¹` on `K`. -/
theorem contDiffOn [CompleteSpace V] (j : C1Jet 𝕜 K V) (hK : Convex ℝ K) {g : E → V}
    (hg : ∀ x : K, g x = j.value x) : ContDiffOn ℝ 1 g K := by
  classical
  -- Extend the derivative component by zero off `K`; only its values on `K` matter.
  let D : E → E →L[ℝ] V := fun z ↦ if hz : z ∈ K then j.deriv ⟨z, hz⟩ else 0
  have hD (x : K) : D x = j.deriv x := dite_eq_left x.property
  have hDc : ContinuousOn D K := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact j.deriv.continuous.congr fun x ↦ (hD x).symm
  have h := (contDiffOn_succ_iff_hasFDerivWithinAt (𝕜 := ℝ) (n := 0) (f := g) (s := K)
    (by simp)).2 fun x hx ↦ ⟨K, by simpa [insert_eq_of_mem hx] using self_mem_nhdsWithin,
      by simp, D, fun y hy ↦ hD ⟨y, hy⟩ ▸ j.hasFDerivWithinAt hK hg ⟨y, hy⟩,
      contDiffOn_zero.2 hDc⟩
  simpa using h

/-- On a convex set with unique within-derivatives, the derivative component of a jet is the
derivative within `K` of every function on `E` extending its value. -/
theorem fderivWithin_eq [CompleteSpace V] (j : C1Jet 𝕜 K V) (hK : Convex ℝ K)
    (hKu : UniqueDiffOn ℝ K) {g : E → V} (hg : ∀ x : K, g x = j.value x) (x : K) :
    fderivWithin ℝ g K x = j.deriv x :=
  (j.hasFDerivWithinAt hK hg x).fderivWithin (hKu x x.property)

/-- On a convex set with unique within-derivatives, a jet is determined by its values. -/
theorem ext_value [CompleteSpace V] (hK : Convex ℝ K) (hKu : UniqueDiffOn ℝ K)
    {j j' : C1Jet 𝕜 K V} (h : j.value = j'.value) : j = j' := by
  classical
  let g : E → V := fun z ↦ if hz : z ∈ K then j.value ⟨z, hz⟩ else 0
  have hg (x : K) : g x = j.value x := dite_eq_left x.property
  refine ext h (ContinuousMap.ext fun x ↦ ?_)
  rw [← j.fderivWithin_eq hK hKu hg, ← j'.fderivWithin_eq hK hKu (fun y ↦ (hg y).trans (by rw [h]))]

variable (𝕜) in
/-- The jet `(f, fderivWithin ℝ f K)` of a function that is `C¹` on a set `K` with unique
within-derivatives. -/
def ofContDiffOn [CompleteSpace V] (hKu : UniqueDiffOn ℝ K) {f : E → V}
    (hf : ContDiffOn ℝ 1 f K) : C1Jet 𝕜 K V :=
  mk ⟨K.domRestrict f, hf.continuousOn.domRestrict⟩
    ⟨K.domRestrict (fderivWithin ℝ f K), (hf.continuousOn_fderivWithin hKu le_rfl).domRestrict⟩
    fun x y h ↦ by
      -- The fundamental theorem of calculus along the segment `[x, y]`, which is star-convex
      -- with respect to `x`, with the derivative within `K` restricted to the segment.
      have hftc := ((convex_segment (x : E) y).starConvex (left_mem_segment ℝ _ _))
        |>.sub_eq_intervalIntegral_lineMap_apply
          ((hf.continuousOn_fderivWithin hKu le_rfl).mono h)
          (fun z hz ↦ ((hf.differentiableOn one_ne_zero z (h hz)).hasFDerivWithinAt).mono h)
          (right_mem_segment ℝ _ _)
      rw [intervalIntegral_eq_integral_unitInterval] at hftc
      exact hftc

@[simp]
theorem value_ofContDiffOn_apply [CompleteSpace V] (hKu : UniqueDiffOn ℝ K) {f : E → V}
    (hf : ContDiffOn ℝ 1 f K) (x : K) : (ofContDiffOn 𝕜 hKu hf).value x = f x :=
  (rfl)

@[simp]
theorem deriv_ofContDiffOn_apply [CompleteSpace V] (hKu : UniqueDiffOn ℝ K) {f : E → V}
    (hf : ContDiffOn ℝ 1 f K) (x : K) :
    (ofContDiffOn 𝕜 hKu hf).deriv x = fderivWithin ℝ f K x :=
  (rfl)

/-- On a convex set with unique within-derivatives, every jet is the jet of a function that is
`C¹` on `K`: of any extension of its value. -/
theorem ofContDiffOn_eq [CompleteSpace V] (j : C1Jet 𝕜 K V) (hK : Convex ℝ K)
    (hKu : UniqueDiffOn ℝ K) {g : E → V} (hg : ∀ x : K, g x = j.value x) :
    ofContDiffOn 𝕜 hKu (j.contDiffOn hK hg) = j :=
  ext_value hK hKu (ContinuousMap.ext fun x ↦ (value_ofContDiffOn_apply hKu _ x).trans (hg x))

end C1Jet

end TauCeti
