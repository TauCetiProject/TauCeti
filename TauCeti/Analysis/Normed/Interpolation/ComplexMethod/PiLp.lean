/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple.PiLp
public import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Endpoints
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Poisson
import TauCeti.Analysis.Normed.Lp.PiLp.Holder
import TauCeti.MeasureTheory.Integral.ZeroAtInfty.PiLp

/-!
# Complex interpolation of finite vector-valued sequence spaces

Given a finite index type `ι`, exponents `1 ≤ q₀, q₁, q ≤ ∞`, a family of compatible couples
`C : ∀ i : ι, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)` whose ambient spaces `V i` are `T₁`
topological spaces with continuous addition, and `θ : ℝ` satisfying
`q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹`, we prove the finite-index case of
**Bergh–Löfström, Theorem 5.1.2** (including `∞` endpoints), with no completeness, duality, or
density assumptions on `C i`:

`(piLp C q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ)`.

For `θ ∈ [0, 1]`, the exponent relation reduces to `1 / q = (1 - θ) / q₀ + θ / q₁`; outside
`[0, 1]`, both spaces are zero (`eq_zero_of_notMem`) and the isometry holds degenerately.

## Main declarations

* `CompatibleCouple.piLpStripTracesEquiv`: coordinatewise equivalence for boundary traces.
* `CompatibleCouple.ComplexMethodSpace.piLpContinuousLinearEquiv`: coordinatewise continuous linear
  equivalence `(piLp C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`.
* `CompatibleCouple.ComplexMethodSpace.piLpEquiv`: **Bergh–Löfström, Theorem 5.1.2**, upgrading
  `piLpContinuousLinearEquiv` to a linear isometric equivalence under the exponent relation.
* `CompatibleCouple.ComplexMethodSpace.piLpReflEquiv`: `[PiLp q₀ X, PiLp q₁ X]_θ ≃ₗᵢ[ℂ] PiLp q X`
  for `0 ≤ θ ≤ 1`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math.
  **24** (1964), 113–190, §13.6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorem 5.1.2).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines MeasureTheory Set TauCeti.Complex.HadamardThreeLines
open scoped ENNReal ZeroAtInfty

namespace TauCeti

namespace CompatibleCouple

section ComplexTraces

variable {ι : Type*} [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]

section
variable (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ : ℝ≥0∞)
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

private def piLpStripTracesFwd : (piLp C q₀ q₁).stripTraces →L[ℂ] ∀ i, (C i).stripTraces :=
  ContinuousLinearMap.pi fun i => stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i)
    (fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i)

private def piLpStripTracesInv : (∀ i, (C i).stripTraces) →L[ℂ] (piLp C q₀ q₁).stripTraces := by
  classical
  exact ∑ i : ι, (stripTracesMap (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (fstToSum_singleCLM_interFst_eq_sndToSum_singleCLM_interSnd C q₀ q₁ i)).comp
    (ContinuousLinearMap.proj i)

private theorem piLpStripTracesFwd_apply_fst (g : (piLp C q₀ q₁).stripTraces) (i : ι) (t : ℝ) :
    (piLpStripTracesFwd C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by simp [piLpStripTracesFwd]

private theorem piLpStripTracesFwd_apply_snd (g : (piLp C q₀ q₁).stripTraces) (i : ι) (t : ℝ) :
    (piLpStripTracesFwd C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by simp [piLpStripTracesFwd]

private theorem piLpStripTracesInv_apply_fst (h : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
    ((piLpStripTracesInv C q₀ q₁ h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).1 t := by
  classical
  simp only [piLpStripTracesInv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Submodule.coe_sum, Prod.fst_sum, WithLp.ofLp_sum,
    stripTracesMap_apply_fst, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

private theorem piLpStripTracesInv_apply_snd (h : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
    ((piLpStripTracesInv C q₀ q₁ h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).2 t := by
  classical
  simp only [piLpStripTracesInv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Submodule.coe_sum, Prod.snd_sum, WithLp.ofLp_sum,
    stripTracesMap_apply_snd, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

/-- Admissible boundary traces for `CompatibleCouple.piLp C q₀ q₁` identify canonically with tuples
of admissible boundary traces `∀ i, (C i).stripTraces` via coordinatewise projection. -/
def piLpStripTracesEquiv : (piLp C q₀ q₁).stripTraces ≃L[ℂ] ∀ i, (C i).stripTraces :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpStripTracesFwd C q₀ q₁)
    (piLpStripTracesInv C q₀ q₁)
    (ContinuousLinearMap.ext fun _ => funext fun _ => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun _ => by
        simp [piLpStripTracesFwd_apply_fst, piLpStripTracesInv_apply_fst])
      (ZeroAtInftyContinuousMap.ext fun _ => by
        simp [piLpStripTracesFwd_apply_snd, piLpStripTracesInv_apply_snd])))
    (ContinuousLinearMap.ext fun _ => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun _ => PiLp.ext fun _ => by
        simp [piLpStripTracesInv_apply_fst, piLpStripTracesFwd_apply_fst])
      (ZeroAtInftyContinuousMap.ext fun _ => PiLp.ext fun _ => by
        simp [piLpStripTracesInv_apply_snd, piLpStripTracesFwd_apply_snd])))

private theorem piLpStripTracesEquiv_apply (g : (piLp C q₀ q₁).stripTraces) :
    piLpStripTracesEquiv C q₀ q₁ g = piLpStripTracesFwd C q₀ q₁ g := rfl

@[simp] theorem piLpStripTracesEquiv_apply_fst (g : (piLp C q₀ q₁).stripTraces) (i : ι) (t : ℝ) :
    (piLpStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by
  simp [piLpStripTracesEquiv, piLpStripTracesFwd_apply_fst]

@[simp] theorem piLpStripTracesEquiv_apply_snd (g : (piLp C q₀ q₁).stripTraces) (i : ι) (t : ℝ) :
    (piLpStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by
  simp [piLpStripTracesEquiv, piLpStripTracesFwd_apply_snd]

@[simp] theorem piLpStripTracesEquiv_symm_apply_fst (h : ∀ i, (C i).stripTraces) (t : ℝ) (i : ι) :
    (((piLpStripTracesEquiv C q₀ q₁).symm h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) i =
      (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t := by
  rw [← piLpStripTracesEquiv_apply_fst, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem piLpStripTracesEquiv_symm_apply_snd (h : ∀ i, (C i).stripTraces) (t : ℝ) (i : ι) :
    (((piLpStripTracesEquiv C q₀ q₁).symm h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) i =
      (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t := by
  rw [← piLpStripTracesEquiv_apply_snd, ContinuousLinearEquiv.apply_symm_apply]

/-- `stripFunction` evaluation at `z` commutes coordinatewise with `piLpStripTracesEquiv`. -/
@[simp] theorem stripFunction_piLpStripTracesEquiv_apply (g : (piLp C q₀ q₁).stripTraces)
    (i : ι) (z : ℂ) :
    (C i).stripFunction (piLpStripTracesEquiv C q₀ q₁ g i) z =
      piLpSumEquiv C q₀ q₁ ((piLp C q₀ q₁).stripFunction g z) i := by
  rw [← stripEval_apply, ← stripEval_apply, piLpStripTracesEquiv_apply, piLpStripTracesFwd,
    ContinuousLinearMap.pi_apply, stripEval_stripTracesMap (PiLp.proj q₀ X₀ i)
      (PiLp.proj q₁ X₁ i) (fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i),
    ← piLpSumEquiv_apply_eq_sumLift]

/-- `stripFunction` evaluation at `z` on a trace pair assembled with
`(piLpStripTracesEquiv C q₀ q₁).symm h` projects coordinatewise to `(C i).stripFunction (h i) z`. -/
@[simp] theorem piLpSumEquiv_stripFunction_piLpStripTracesEquiv_symm (h : ∀ i, (C i).stripTraces)
    (z : ℂ) (i : ι) : piLpSumEquiv C q₀ q₁
      ((piLp C q₀ q₁).stripFunction ((piLpStripTracesEquiv C q₀ q₁).symm h) z) i =
    (C i).stripFunction (h i) z := by
  rw [← stripFunction_piLpStripTracesEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end

end ComplexTraces

namespace ComplexMethodSpace

section PiLpEquiv

variable {ι : Type*} [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]

section
variable (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ q : ℝ≥0∞)
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)

private def piLpCLEFwd :
    (piLp C q₀ q₁).ComplexMethodSpace θ →L[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  (PiLp.continuousLinearEquiv q ℂ (fun i => (C i).ComplexMethodSpace θ)).symm
    |>.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      map θ (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i)
        (fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i))

private def piLpCLEInv :
    PiLp q (fun i => (C i).ComplexMethodSpace θ) →L[ℂ] (piLp C q₀ q₁).ComplexMethodSpace θ := by
  classical
  exact ∑ i : ι, (map θ (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (fstToSum_singleCLM_interFst_eq_sndToSum_singleCLM_interSnd C q₀ q₁ i)).comp
    (PiLp.proj q (fun j => (C j).ComplexMethodSpace θ) i)

private theorem piLpCLEFwd_mk (g : (piLp C q₀ q₁).stripTraces) :
    piLpCLEFwd C q₀ q₁ q θ (mk θ g) =
      WithLp.toLp q fun i => mk θ (piLpStripTracesEquiv C q₀ q₁ g i) := by
  refine PiLp.ext fun i => ?_
  simp only [piLpCLEFwd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.pi_apply, map_mk, PiLp.toLp_apply]
  exact congrArg (mk θ) (Subtype.ext (Prod.ext
    (ZeroAtInftyContinuousMap.ext fun _ => by simp [piLpStripTracesEquiv_apply_fst])
    (ZeroAtInftyContinuousMap.ext fun _ => by simp [piLpStripTracesEquiv_apply_snd])))

private theorem piLpCLEInv_mk (h : ∀ i, (C i).stripTraces) :
    piLpCLEInv C q₀ q₁ q θ (WithLp.toLp q fun i => mk θ (h i)) =
      mk θ ((piLpStripTracesEquiv C q₀ q₁).symm h) := by
  classical
  simp only [piLpCLEInv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, map_mk, ← map_sum]
  refine congrArg (mk θ) (Subtype.ext (Prod.ext
    (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => ?_)
    (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => ?_)))
  · simp only [Submodule.coe_sum, Prod.fst_sum, FunLike.coe_sum, Finset.sum_apply, WithLp.ofLp_sum,
      stripTracesMap_apply_fst, PiLp.singleCLM_apply, piLpStripTracesEquiv_symm_apply_fst]
    rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]
  · simp only [Submodule.coe_sum, Prod.snd_sum, FunLike.coe_sum, Finset.sum_apply, WithLp.ofLp_sum,
      stripTracesMap_apply_snd, PiLp.singleCLM_apply, piLpStripTracesEquiv_symm_apply_snd]
    rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

/-- Coordinatewise continuous linear equivalence between `(piLp C q₀ q₁).ComplexMethodSpace θ` and
`PiLp q (fun i => (C i).ComplexMethodSpace θ)`. Unlike `piLpEquiv`, this topological isomorphism
requires no relation between `q₀`, `q₁`, `q`, and `θ`, and no `1 ≤ q` assumption on `q`. -/
def piLpContinuousLinearEquiv :
    (piLp C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpCLEFwd C q₀ q₁ q θ) (piLpCLEInv C q₀ q₁ q θ)
    (ContinuousLinearMap.ext fun v => by
      choose h hh using fun i => mk_surjective (v i)
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        show v = WithLp.toLp q fun i => mk θ (h i) from PiLp.ext fun i => (hh i).symm,
        piLpCLEInv_mk, piLpCLEFwd_mk]
      exact PiLp.ext fun i => by simp)
    (ContinuousLinearMap.ext fun u => by
      obtain ⟨g, rfl⟩ := mk_surjective u; simp [piLpCLEFwd_mk, piLpCLEInv_mk])

private theorem piLpContinuousLinearEquiv_apply (u : (piLp C q₀ q₁).ComplexMethodSpace θ) :
    piLpContinuousLinearEquiv C q₀ q₁ q θ u = piLpCLEFwd C q₀ q₁ q θ u := rfl

@[simp] theorem piLpContinuousLinearEquiv_mk_apply (g : (piLp C q₀ q₁).stripTraces) (i : ι) :
    piLpContinuousLinearEquiv C q₀ q₁ q θ (mk θ g) i = mk θ (piLpStripTracesEquiv C q₀ q₁ g i) := by
  rw [piLpContinuousLinearEquiv_apply, piLpCLEFwd_mk, PiLp.toLp_apply]

@[simp] theorem toSum_piLpContinuousLinearEquiv_apply (u : (piLp C q₀ q₁).ComplexMethodSpace θ)
    (i : ι) : toSum (piLpContinuousLinearEquiv C q₀ q₁ q θ u i) =
    piLpSumEquiv C q₀ q₁ (toSum u) i := by obtain ⟨g, rfl⟩ := mk_surjective u; simp [toSum_mk]

@[simp] theorem piLpContinuousLinearEquiv_symm_mk (h : ∀ i, (C i).stripTraces) :
    (piLpContinuousLinearEquiv C q₀ q₁ q θ).symm (WithLp.toLp q fun i => mk θ (h i)) =
      mk θ ((piLpStripTracesEquiv C q₀ q₁).symm h) := by
  refine (piLpContinuousLinearEquiv C q₀ q₁ q θ).injective (PiLp.ext fun i => ?_)
  rw [ContinuousLinearEquiv.apply_symm_apply, PiLp.toLp_apply,
    piLpContinuousLinearEquiv_mk_apply, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem toSum_piLpContinuousLinearEquiv_symm
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    toSum ((piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v) =
      (piLpSumEquiv C q₀ q₁).symm fun i => toSum (v i) := by
  refine (piLpSumEquiv C q₀ q₁).injective (funext fun i => ?_)
  rw [ContinuousLinearEquiv.apply_symm_apply, ← toSum_piLpContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply]

end

/-! ### Forward and inverse norm bounds on `piLpContinuousLinearEquiv` -/

section
variable (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ : ℝ≥0∞}
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

private theorem norm_piLpContinuousLinearEquiv_zero (u : (piLp C q₀ q₁).ComplexMethodSpace 0) :
    ‖piLpContinuousLinearEquiv C q₀ q₁ q₀ 0 u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  calc ‖piLpContinuousLinearEquiv C q₀ q₁ q₀ 0 (mk 0 g)‖
      = ‖WithLp.toLp q₀ fun i => ‖(g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 0 i‖‖ := by
        rw [← PiLp.norm_norm (piLpContinuousLinearEquiv C q₀ q₁ q₀ 0 (mk 0 g))]
        simp only [piLpContinuousLinearEquiv_mk_apply, norm_mk_zero, piLpStripTracesEquiv_apply_fst]
    _ = ‖mk 0 g‖ := (PiLp.norm_norm _).trans (norm_mk_zero g).symm

private theorem norm_piLpContinuousLinearEquiv_one (u : (piLp C q₀ q₁).ComplexMethodSpace 1) :
    ‖piLpContinuousLinearEquiv C q₀ q₁ q₁ 1 u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  calc ‖piLpContinuousLinearEquiv C q₀ q₁ q₁ 1 (mk 1 g)‖
      = ‖WithLp.toLp q₁ fun i => ‖(g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 0 i‖‖ := by
        rw [← PiLp.norm_norm (piLpContinuousLinearEquiv C q₀ q₁ q₁ 1 (mk 1 g))]
        simp only [piLpContinuousLinearEquiv_mk_apply, norm_mk_one, piLpStripTracesEquiv_apply_snd]
    _ = ‖mk 1 g‖ := (PiLp.norm_norm _).trans (norm_mk_one g).symm

private theorem norm_piLpContinuousLinearEquiv_le {q : ℝ≥0∞} [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLp C q₀ q₁).ComplexMethodSpace θ) :
    ‖piLpContinuousLinearEquiv C q₀ q₁ q θ u‖ ≤ ‖u‖ := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
    · obtain rfl : q₀ = q := (inv_injective (by simpa using hq)).symm
      exact (norm_piLpContinuousLinearEquiv_zero C u).le
    · rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
      · obtain rfl : q₁ = q := (inv_injective (by simpa using hq)).symm
        exact (norm_piLpContinuousLinearEquiv_one C u).le
      · have hθoo : θ ∈ Ioo (0 : ℝ) 1 := ⟨hθ0, hθ1⟩
        refine le_of_forall_gt fun r hr => ?_
        obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
        let a (i : ι) := (1 - θ)⁻¹ * ∫ t, ‖g.val.1 t i‖ * stripPoisson₀ θ t
        let b (i : ι) := θ⁻¹ * ∫ t, ‖g.val.2 t i‖ * stripPoisson₁ θ t
        have ha_norm := (ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le g.val.1
          (sub_pos.2 hθ1) (integrable_stripPoisson₀ θ) (ae_of_all _ fun t =>
            (stripPoisson₀_pos hθoo t).le) (integral_stripPoisson₀ ⟨hθ0, hθ1.le⟩)).trans
          ((norm_fst_le g.val).trans_eq (Submodule.norm_coe g))
        have hb_norm := (ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le g.val.2 hθ0
          (integrable_stripPoisson₁ θ) (ae_of_all _ fun t =>
            (stripPoisson₁_pos hθoo t).le) (integral_stripPoisson₁ ⟨hθ0.le, hθ1⟩)).trans
          ((norm_snd_le g.val).trans_eq (Submodule.norm_coe g))
        refine ((PiLp.norm_mono (y := WithLp.toLp q fun i => a i ^ (1 - θ) * b i ^ θ)
          fun i => ?_).trans (TauCeti.norm_toLp_rpow_mul_rpow_le
            (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
            (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' (Ioo_subset_Icc_self hθoo) hq
            (fun i => mul_nonneg (inv_pos.2 (sub_pos.2 hθ1)).le (integral_nonneg fun t =>
              mul_nonneg (norm_nonneg _) (stripPoisson₀_pos hθoo t).le))
            (fun i => mul_nonneg (inv_pos.2 hθ0).le (integral_nonneg fun t =>
              mul_nonneg (norm_nonneg _) (stripPoisson₁_pos hθoo t).le)))).trans_lt
          (lt_of_le_of_lt ?_ hg)
        · simpa [piLpContinuousLinearEquiv_mk_apply] using
            (norm_mk_le_integral_stripPoisson_rpow_mul_rpow hθoo
              (piLpStripTracesEquiv C q₀ q₁ g i)).trans (le_abs_self _)
        · exact (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha_norm (sub_pos.2 hθ1).le)
            (Real.rpow_le_rpow (norm_nonneg _) hb_norm hθ0.le) (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq (by rw [← Real.rpow_add_of_nonneg
              (norm_nonneg _) (sub_pos.2 hθ1).le hθ0.le, sub_add_cancel, Real.rpow_one])
  · rw [eq_zero_of_notMem hθ u, map_zero, norm_zero, norm_zero]

private theorem norm_piLpCLE_symm_le_of_mk {q : ℝ≥0∞} {θ : ℝ}
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) {B : ℝ}
    (g : ∀ i, (C i).stripTraces) (hg_mk : ∀ i, mk θ (g i) = v i)
    (hG : ‖((piLpStripTracesEquiv C q₀ q₁).symm g).val‖ ≤ B) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ B := by
  have hv : v = WithLp.toLp q fun i => mk θ (g i) := PiLp.ext fun i => (hg_mk i).symm
  rw [hv, piLpContinuousLinearEquiv_symm_mk]
  exact (norm_mk_le _).trans ((Submodule.norm_coe _).symm.trans_le hG)

private theorem norm_symm_le_of_eq_top {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : (∞ : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp ∞ (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ ∞ θ).symm v‖ ≤ ‖v‖ := by
  obtain ⟨rfl, rfl⟩ := (TauCeti.eq_top_iff_of_inv_eq hθ hq).1 rfl
  refine le_of_forall_pos_le_add fun ε hε => ?_
  choose g hg_mk hg_norm using fun i =>
    norm_lt_iff.1 ((PiLp.norm_apply_le v i).trans_lt (lt_add_of_pos_right ‖v‖ hε))
  have hB : 0 ≤ ‖v‖ + ε := add_nonneg (norm_nonneg v) hε.le
  refine norm_piLpCLE_symm_le_of_mk C v g hg_mk (norm_prod_le_iff.2 ⟨
    (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => (PiLp.norm_ofLp _).symm.trans_le <|
      (pi_norm_le_iff_of_nonneg hB).2 fun i => by
        simpa using (norm_stripTraces_fst_apply_le (g i) t).trans (hg_norm i).le,
    (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => (PiLp.norm_ofLp _).symm.trans_le <|
      (pi_norm_le_iff_of_nonneg hB).2 fun i => by
        simpa using (norm_stripTraces_snd_apply_le (g i) t).trans (hg_norm i).le⟩)

private theorem norm_symm_le_of_ne_top {q : ℝ≥0∞} [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq_top : q ≠ ∞) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ ‖v‖ := by
  cases isEmpty_or_nonempty ι
  · rw [Subsingleton.elim v 0, map_zero, norm_zero, norm_zero]
  have hq₀ : q₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
  have hq₁ : q₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne'
  have hα := TauCeti.one_sub_mul_toReal_mul_inv_add_mul_eq_one_of_inv_eq hq₀ hq₁ hq_top
    ⟨hθ.1.le, hθ.2.le⟩ hq
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨b, B, hB, hB_le, hb, hsum⟩ :=
    PiLp.exists_pos_le_norm_add_and_norm_apply_lt_and_sum_rpow_eq hq_top v hε
  choose g hg_eq hg using fun i => norm_lt_iff.1 (hb i).2
  choose g' hg'_eq hg'_0 hg'_1 using fun i =>
    exists_stripTraces_rescale hα (hb i).1 hB (g i) (hg i).le
  refine (norm_piLpCLE_symm_le_of_mk C v g' (fun i => (hg'_eq i).trans (hg_eq i))
    (norm_prod_le_iff.2 ⟨
      (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
        (PiLp.norm_mono (y := WithLp.toLp q₀ fun i => B * (b i / B) ^ (q.toReal * (q₀⁻¹).toReal))
          fun i => by simpa using (hg'_0 i t).trans (le_abs_self _)).trans
          (TauCeti.norm_toLp_mul_div_rpow_le hq₀ hB (fun i => (hb i).1) hsum),
      (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
        (PiLp.norm_mono (y := WithLp.toLp q₁ fun i => B * (b i / B) ^ (q.toReal * (q₁⁻¹).toReal))
          fun i => by simpa using (hg'_1 i t).trans (le_abs_self _)).trans
          (TauCeti.norm_toLp_mul_div_rpow_le hq₁ hB (fun i => (hb i).1) hsum)⟩)).trans hB_le

private theorem norm_piLpContinuousLinearEquiv_symm_le {q : ℝ≥0∞} [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ ‖v‖ := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
    · obtain rfl : q₀ = q := (inv_injective (by simpa using hq)).symm
      exact (norm_piLpContinuousLinearEquiv_zero C _).symm.trans_le (by simp)
    · rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
      · obtain rfl : q₁ = q := (inv_injective (by simpa using hq)).symm
        exact (norm_piLpContinuousLinearEquiv_one C _).symm.trans_le (by simp)
      · rcases eq_or_ne q ∞ with rfl | hq_top
        · exact norm_symm_le_of_eq_top C ⟨hθ0, hθ1⟩ hq v
        · exact norm_symm_le_of_ne_top C ⟨hθ0, hθ1⟩ hq_top hq v
  · rw [eq_zero_of_notMem hθ ((piLpContinuousLinearEquiv C q₀ q₁ q θ).symm v), norm_zero]
    exact norm_nonneg v

end

/-! ### Main linear isometric equivalences -/

section
variable (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ q : ℝ≥0∞}
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
  (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)

/-- **Bergh–Löfström, Theorem 5.1.2 (finite index sets, including `∞` endpoints).**
For a finite family of compatible couples `C i` (`i : ι`) whose ambient spaces `V i` are `T₁`
topological spaces with continuous addition, exponents `1 ≤ q₀, q₁, q ≤ ∞`, and `θ : ℝ`
satisfying `q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹`, complex
interpolation commutes isometrically with `PiLp`:
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`.

For `θ ∈ [0, 1]`, the exponent hypothesis reduces to `1 / q = (1 - θ) / q₀ + θ / q₁`;
for `θ ∉ [0, 1]`, both interpolation spaces are zero (`eq_zero_of_notMem`). -/
def piLpEquiv :
    (piLp C q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  LinearIsometryEquiv.ofBounds (piLpContinuousLinearEquiv C q₀ q₁ q θ).toLinearEquiv
    (norm_piLpContinuousLinearEquiv_le C hq)
    (norm_piLpContinuousLinearEquiv_symm_le C hq)

@[simp] theorem coe_piLpEquiv :
    (piLpEquiv C hq : (piLp C q₀ q₁).ComplexMethodSpace θ →
      PiLp q (fun i => (C i).ComplexMethodSpace θ)) = piLpContinuousLinearEquiv C q₀ q₁ q θ :=
  (rfl)

@[simp] theorem coe_piLpEquiv_symm :
    ((piLpEquiv C hq).symm : PiLp q (fun i => (C i).ComplexMethodSpace θ) →
      (piLp C q₀ q₁).ComplexMethodSpace θ) = (piLpContinuousLinearEquiv C q₀ q₁ q θ).symm :=
  (rfl)

end

end PiLpEquiv

section Refl

variable {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, NormedAddCommGroup (X i)]
  [∀ i, NormedSpace ℂ (X i)] {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)]
  {θ : ℝ} (hθ : θ ∈ Icc 0 1)
  (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)

/-- **Complex interpolation of finite vector-valued sequence spaces (`[ℓ_{q₀}^N(E), ℓ_{q₁}^N(E)]_θ =
ℓ_q^N(E)` with equal norms).** For a finite family of complex normed spaces `X : ι → Type*`,
exponents `1 ≤ q₀, q₁, q ≤ ∞`, and `0 ≤ θ ≤ 1` satisfying `1 / q = (1 - θ) / q₀ + θ / q₁`, the
complex interpolation space of `(PiLp q₀ X, PiLp q₁ X)` is canonically linearly isometric to
`PiLp q X`. -/
def piLpReflEquiv : (piLp (fun i => refl ℂ (X i)) q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q X :=
  (piLpEquiv (fun i => refl ℂ (X i)) hq).trans
    (LinearIsometryEquiv.piLpCongrRight q fun _ => reflEquiv hθ)

@[simp] theorem piLpReflEquiv_apply_apply
    (u : (piLp (fun i => refl ℂ (X i)) q₀ q₁).ComplexMethodSpace θ) (i : ι) :
    piLpReflEquiv X hθ hq u i =
      (piLp (fun i => refl ℂ (X i)) q₀ q₁).sumSpaceEmbed (toSum u) i := by
  rw [piLpReflEquiv, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    PiLp.toLp_apply, reflEquiv_apply, coe_piLpEquiv,
    toSum_piLpContinuousLinearEquiv_apply (fun j => refl ℂ (X j)),
    sumSpaceEmbed_piLpSumEquiv_apply (fun j => refl ℂ (X j))]

@[simp] theorem sumSpaceEmbed_toSum_piLpReflEquiv_symm (x : PiLp q X) (i : ι) :
    (piLp (fun i => refl ℂ (X i)) q₀ q₁).sumSpaceEmbed
        (toSum ((piLpReflEquiv X hθ hq).symm x)) i = x i := by
  rw [← piLpReflEquiv_apply_apply X hθ hq, LinearIsometryEquiv.apply_symm_apply]

end Refl

end ComplexMethodSpace

end CompatibleCouple

end TauCeti
