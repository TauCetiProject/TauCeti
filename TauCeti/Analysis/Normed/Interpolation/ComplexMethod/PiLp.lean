/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple.PiLp
public import TauCeti.Analysis.Normed.Interpolation.PiLp
public import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
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

`(piLpFamily C q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun i => (C i).ComplexMethodSpace θ)`.

For `θ ∈ [0, 1]`, the exponent relation reduces to `1 / q = (1 - θ) / q₀ + θ / q₁`; outside
`[0, 1]`, both spaces are zero (`eq_zero_of_notMem`) and the isometry holds degenerately.

We also specialize to a single compatible couple `(C.piLp ι q₀ q₁)`
(`CompatibleCouple.ComplexMethodSpace.piLpEquiv`), retain the explicit `ℓ^q → [ℓ^{q₀}, ℓ^{q₁}]_θ`
inclusion `ComplexMethodSpace.ofPiLp` and coordinate projections `ComplexMethodSpace.piLpProj`, and
record the constant-couple specialization `[PiLp q₀ X, PiLp q₁ X]_θ ≃ₗᵢ[ℂ] PiLp q X`
(`CompatibleCouple.ComplexMethodSpace.piLpReflEquiv`).

## Main declarations

* `CompatibleCouple.piLpFamilyStripTracesEquiv`: coordinatewise equivalence for boundary traces.
* `CompatibleCouple.ComplexMethodSpace.piLpFamilyContinuousLinearEquiv`: coordinatewise continuous
  linear equivalence
  `(piLpFamily C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`.
* `CompatibleCouple.ComplexMethodSpace.piLpFamilyEquiv`: **Bergh–Löfström, Theorem 5.1.2** for
  families of couples, upgrading `piLpFamilyContinuousLinearEquiv` to a linear isometric equivalence
  under the exponent relation.
* `CompatibleCouple.ComplexMethodSpace.piLpEquiv`: **Bergh–Löfström, Theorem 5.1.2** for a single
  compatible couple `(C.piLp ι q₀ q₁)`.
* `CompatibleCouple.ComplexMethodSpace.piLpReflEquiv`: `[PiLp q₀ X, PiLp q₁ X]_θ ≃ₗᵢ[ℂ] PiLp q X`
  for `0 ≤ θ ≤ 1`.
* `CompatibleCouple.ComplexMethodSpace.ofPiLp` and `ComplexMethodSpace.piLpProj`: the inclusion
  `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` and coordinate projections on `C.piLp ι q₀ q₁`.

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

private def piLpFamilyStripTracesFwd :
    (piLpFamily C q₀ q₁).stripTraces →L[ℂ] ∀ i, (C i).stripTraces :=
  ContinuousLinearMap.pi fun i => stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i)
    (fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i)

private def piLpFamilyStripTracesInv :
    (∀ i, (C i).stripTraces) →L[ℂ] (piLpFamily C q₀ q₁).stripTraces := by
  classical
  exact ∑ i : ι, (stripTracesMap (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (fstToSum_singleCLM_interFst_eq_sndToSum_singleCLM_interSnd C q₀ q₁ i)).comp
    (ContinuousLinearMap.proj i)

private theorem piLpFamilyStripTracesFwd_apply_fst (g : (piLpFamily C q₀ q₁).stripTraces)
    (i : ι) (t : ℝ) :
    (piLpFamilyStripTracesFwd C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by
  simp [piLpFamilyStripTracesFwd]

private theorem piLpFamilyStripTracesFwd_apply_snd (g : (piLpFamily C q₀ q₁).stripTraces)
    (i : ι) (t : ℝ) :
    (piLpFamilyStripTracesFwd C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by
  simp [piLpFamilyStripTracesFwd]

private theorem piLpFamilyStripTracesInv_apply_fst (h : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
    ((piLpFamilyStripTracesInv C q₀ q₁ h :
        C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).1 t := by
  classical
  simp only [piLpFamilyStripTracesInv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Submodule.coe_sum,
    Prod.fst_sum, WithLp.ofLp_sum, stripTracesMap_apply_fst, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

private theorem piLpFamilyStripTracesInv_apply_snd (h : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
    ((piLpFamilyStripTracesInv C q₀ q₁ h :
        C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).2 t := by
  classical
  simp only [piLpFamilyStripTracesInv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Submodule.coe_sum,
    Prod.snd_sum, WithLp.ofLp_sum, stripTracesMap_apply_snd, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

/-- Admissible boundary traces for `CompatibleCouple.piLpFamily C q₀ q₁` identify canonically with
tuples of admissible boundary traces `∀ i, (C i).stripTraces` via coordinatewise projection. -/
def piLpFamilyStripTracesEquiv :
    (piLpFamily C q₀ q₁).stripTraces ≃L[ℂ] ∀ i, (C i).stripTraces :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpFamilyStripTracesFwd C q₀ q₁)
    (piLpFamilyStripTracesInv C q₀ q₁)
    (ContinuousLinearMap.ext fun _ => funext fun _ => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun _ => by
        simp [piLpFamilyStripTracesFwd_apply_fst, piLpFamilyStripTracesInv_apply_fst])
      (ZeroAtInftyContinuousMap.ext fun _ => by
        simp [piLpFamilyStripTracesFwd_apply_snd, piLpFamilyStripTracesInv_apply_snd])))
    (ContinuousLinearMap.ext fun _ => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun _ => PiLp.ext fun _ => by
        simp [piLpFamilyStripTracesInv_apply_fst, piLpFamilyStripTracesFwd_apply_fst])
      (ZeroAtInftyContinuousMap.ext fun _ => PiLp.ext fun _ => by
        simp [piLpFamilyStripTracesInv_apply_snd, piLpFamilyStripTracesFwd_apply_snd])))

private theorem piLpFamilyStripTracesEquiv_apply (g : (piLpFamily C q₀ q₁).stripTraces) :
    piLpFamilyStripTracesEquiv C q₀ q₁ g = piLpFamilyStripTracesFwd C q₀ q₁ g := rfl

@[simp] theorem piLpFamilyStripTracesEquiv_apply_fst (g : (piLpFamily C q₀ q₁).stripTraces)
    (i : ι) (t : ℝ) :
    (piLpFamilyStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by
  simp [piLpFamilyStripTracesEquiv, piLpFamilyStripTracesFwd_apply_fst]

@[simp] theorem piLpFamilyStripTracesEquiv_apply_snd (g : (piLpFamily C q₀ q₁).stripTraces)
    (i : ι) (t : ℝ) :
    (piLpFamilyStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by
  simp [piLpFamilyStripTracesEquiv, piLpFamilyStripTracesFwd_apply_snd]

@[simp] theorem piLpFamilyStripTracesEquiv_symm_apply_fst (h : ∀ i, (C i).stripTraces)
    (t : ℝ) (i : ι) :
    (((piLpFamilyStripTracesEquiv C q₀ q₁).symm h :
        C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) i =
      (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t := by
  rw [← piLpFamilyStripTracesEquiv_apply_fst, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem piLpFamilyStripTracesEquiv_symm_apply_snd (h : ∀ i, (C i).stripTraces)
    (t : ℝ) (i : ι) :
    (((piLpFamilyStripTracesEquiv C q₀ q₁).symm h :
        C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) i =
      (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t := by
  rw [← piLpFamilyStripTracesEquiv_apply_snd, ContinuousLinearEquiv.apply_symm_apply]

/-- `stripFunction` evaluation at `z` commutes coordinatewise with
`piLpFamilyStripTracesEquiv`. -/
@[simp] theorem stripFunction_piLpFamilyStripTracesEquiv_apply
    (g : (piLpFamily C q₀ q₁).stripTraces) (i : ι) (z : ℂ) :
    (C i).stripFunction (piLpFamilyStripTracesEquiv C q₀ q₁ g i) z =
      piLpFamilySumEquiv C q₀ q₁ ((piLpFamily C q₀ q₁).stripFunction g z) i := by
  rw [← stripEval_apply, ← stripEval_apply, piLpFamilyStripTracesEquiv_apply,
    piLpFamilyStripTracesFwd, ContinuousLinearMap.pi_apply,
    stripEval_stripTracesMap (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i)
      (fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i),
    ← piLpFamilySumEquiv_apply_eq_sumLift]

/-- `stripFunction` evaluation at `z` on a trace pair assembled with
`(piLpFamilyStripTracesEquiv C q₀ q₁).symm h` projects coordinatewise to
`(C i).stripFunction (h i) z`. -/
@[simp] theorem piLpFamilySumEquiv_stripFunction_piLpFamilyStripTracesEquiv_symm
    (h : ∀ i, (C i).stripTraces) (z : ℂ) (i : ι) : piLpFamilySumEquiv C q₀ q₁
      ((piLpFamily C q₀ q₁).stripFunction ((piLpFamilyStripTracesEquiv C q₀ q₁).symm h) z) i =
    (C i).stripFunction (h i) z := by
  rw [← stripFunction_piLpFamilyStripTracesEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end

end ComplexTraces

namespace ComplexMethodSpace

section PiLpFamilyEquiv

variable {ι : Type*} [Fintype ι]
variable {X₀ X₁ V : ι → Type*}
  [∀ i, NormedAddCommGroup (X₀ i)] [∀ i, NormedSpace ℂ (X₀ i)]
  [∀ i, NormedAddCommGroup (X₁ i)] [∀ i, NormedSpace ℂ (X₁ i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, ContinuousAdd (V i)] [∀ i, T1Space (V i)]

section
variable (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) (q₀ q₁ q : ℝ≥0∞)
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (θ : ℝ)

private def piLpFamilyCLEFwd :
    (piLpFamily C q₀ q₁).ComplexMethodSpace θ →L[ℂ]
      PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  (PiLp.continuousLinearEquiv q ℂ (fun i => (C i).ComplexMethodSpace θ)).symm
    |>.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      map θ (PiLp.proj q₀ X₀ i) (PiLp.proj q₁ X₁ i)
        (fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i))

private def piLpFamilyCLEInv :
    PiLp q (fun i => (C i).ComplexMethodSpace θ) →L[ℂ]
      (piLpFamily C q₀ q₁).ComplexMethodSpace θ := by
  classical
  exact ∑ i : ι, (map θ (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (fstToSum_singleCLM_interFst_eq_sndToSum_singleCLM_interSnd C q₀ q₁ i)).comp
    (PiLp.proj q (fun j => (C j).ComplexMethodSpace θ) i)

private theorem piLpFamilyCLEFwd_mk (g : (piLpFamily C q₀ q₁).stripTraces) :
    piLpFamilyCLEFwd C q₀ q₁ q θ (mk θ g) =
      WithLp.toLp q fun i => mk θ (piLpFamilyStripTracesEquiv C q₀ q₁ g i) := by
  refine PiLp.ext fun i => ?_
  simp only [piLpFamilyCLEFwd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.pi_apply, map_mk, PiLp.toLp_apply]
  exact congrArg (mk θ) (Subtype.ext (Prod.ext
    (ZeroAtInftyContinuousMap.ext fun _ => by simp [piLpFamilyStripTracesEquiv_apply_fst])
    (ZeroAtInftyContinuousMap.ext fun _ => by simp [piLpFamilyStripTracesEquiv_apply_snd])))

private theorem piLpFamilyCLEInv_mk (h : ∀ i, (C i).stripTraces) :
    piLpFamilyCLEInv C q₀ q₁ q θ (WithLp.toLp q fun i => mk θ (h i)) =
      mk θ ((piLpFamilyStripTracesEquiv C q₀ q₁).symm h) := by
  classical
  simp only [piLpFamilyCLEInv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, map_mk, ← map_sum]
  refine congrArg (mk θ) (Subtype.ext (Prod.ext
    (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => ?_)
    (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => ?_)))
  · simp only [Submodule.coe_sum, Prod.fst_sum, FunLike.coe_sum, Finset.sum_apply, WithLp.ofLp_sum,
      stripTracesMap_apply_fst, PiLp.singleCLM_apply, piLpFamilyStripTracesEquiv_symm_apply_fst]
    rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]
  · simp only [Submodule.coe_sum, Prod.snd_sum, FunLike.coe_sum, Finset.sum_apply, WithLp.ofLp_sum,
      stripTracesMap_apply_snd, PiLp.singleCLM_apply, piLpFamilyStripTracesEquiv_symm_apply_snd]
    rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

/-- Coordinatewise continuous linear equivalence between `(piLpFamily C q₀ q₁).ComplexMethodSpace θ`
and `PiLp q (fun i => (C i).ComplexMethodSpace θ)`. Unlike `piLpFamilyEquiv`, this topological
isomorphism requires no relation between `q₀`, `q₁`, `q`, and `θ`, and no `1 ≤ q` assumption on
`q`. -/
def piLpFamilyContinuousLinearEquiv :
    (piLpFamily C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ]
      PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpFamilyCLEFwd C q₀ q₁ q θ)
    (piLpFamilyCLEInv C q₀ q₁ q θ)
    (ContinuousLinearMap.ext fun v => by
      choose h hh using fun i => mk_surjective (v i)
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        show v = WithLp.toLp q fun i => mk θ (h i) from PiLp.ext fun i => (hh i).symm,
        piLpFamilyCLEInv_mk, piLpFamilyCLEFwd_mk]
      exact PiLp.ext fun i => by simp)
    (ContinuousLinearMap.ext fun u => by
      obtain ⟨g, rfl⟩ := mk_surjective u; simp [piLpFamilyCLEFwd_mk, piLpFamilyCLEInv_mk])

private theorem piLpFamilyContinuousLinearEquiv_apply
    (u : (piLpFamily C q₀ q₁).ComplexMethodSpace θ) :
    piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ u = piLpFamilyCLEFwd C q₀ q₁ q θ u := rfl

@[simp] theorem piLpFamilyContinuousLinearEquiv_mk_apply
    (g : (piLpFamily C q₀ q₁).stripTraces) (i : ι) :
    piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ (mk θ g) i =
      mk θ (piLpFamilyStripTracesEquiv C q₀ q₁ g i) := by
  rw [piLpFamilyContinuousLinearEquiv_apply, piLpFamilyCLEFwd_mk, PiLp.toLp_apply]

@[simp] theorem toSum_piLpFamilyContinuousLinearEquiv_apply
    (u : (piLpFamily C q₀ q₁).ComplexMethodSpace θ) (i : ι) :
    toSum (piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ u i) =
      piLpFamilySumEquiv C q₀ q₁ (toSum u) i := by
  obtain ⟨g, rfl⟩ := mk_surjective u; simp [toSum_mk]

@[simp] theorem piLpFamilyContinuousLinearEquiv_symm_mk (h : ∀ i, (C i).stripTraces) :
    (piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm (WithLp.toLp q fun i => mk θ (h i)) =
      mk θ ((piLpFamilyStripTracesEquiv C q₀ q₁).symm h) := by
  refine (piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).injective (PiLp.ext fun i => ?_)
  rw [ContinuousLinearEquiv.apply_symm_apply, PiLp.toLp_apply,
    piLpFamilyContinuousLinearEquiv_mk_apply, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem toSum_piLpFamilyContinuousLinearEquiv_symm
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    toSum ((piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm v) =
      (piLpFamilySumEquiv C q₀ q₁).symm fun i => toSum (v i) := by
  refine (piLpFamilySumEquiv C q₀ q₁).injective (funext fun i => ?_)
  rw [ContinuousLinearEquiv.apply_symm_apply, ← toSum_piLpFamilyContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply]

end

/-! ### Forward and inverse norm bounds on `piLpFamilyContinuousLinearEquiv` -/

section
variable (C : ∀ i, CompatibleCouple ℂ (X₀ i) (X₁ i) (V i)) {q₀ q₁ : ℝ≥0∞}
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

private theorem norm_piLpFamilyContinuousLinearEquiv_zero
    (u : (piLpFamily C q₀ q₁).ComplexMethodSpace 0) :
    ‖piLpFamilyContinuousLinearEquiv C q₀ q₁ q₀ 0 u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  calc ‖piLpFamilyContinuousLinearEquiv C q₀ q₁ q₀ 0 (mk 0 g)‖
      = ‖WithLp.toLp q₀ fun i => ‖(g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 0 i‖‖ := by
        rw [← PiLp.norm_norm (piLpFamilyContinuousLinearEquiv C q₀ q₁ q₀ 0 (mk 0 g))]
        simp only [piLpFamilyContinuousLinearEquiv_mk_apply, norm_mk_zero,
          piLpFamilyStripTracesEquiv_apply_fst]
    _ = ‖mk 0 g‖ := (PiLp.norm_norm _).trans (norm_mk_zero g).symm

private theorem norm_piLpFamilyContinuousLinearEquiv_one
    (u : (piLpFamily C q₀ q₁).ComplexMethodSpace 1) :
    ‖piLpFamilyContinuousLinearEquiv C q₀ q₁ q₁ 1 u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  calc ‖piLpFamilyContinuousLinearEquiv C q₀ q₁ q₁ 1 (mk 1 g)‖
      = ‖WithLp.toLp q₁ fun i => ‖(g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 0 i‖‖ := by
        rw [← PiLp.norm_norm (piLpFamilyContinuousLinearEquiv C q₀ q₁ q₁ 1 (mk 1 g))]
        simp only [piLpFamilyContinuousLinearEquiv_mk_apply, norm_mk_one,
          piLpFamilyStripTracesEquiv_apply_snd]
    _ = ‖mk 1 g‖ := (PiLp.norm_norm _).trans (norm_mk_one g).symm

private theorem norm_piLpFamilyContinuousLinearEquiv_le {q : ℝ≥0∞} [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (u : (piLpFamily C q₀ q₁).ComplexMethodSpace θ) :
    ‖piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ u‖ ≤ ‖u‖ := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
    · obtain rfl : q₀ = q := (inv_injective (by simpa using hq)).symm
      exact (norm_piLpFamilyContinuousLinearEquiv_zero C u).le
    · rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
      · obtain rfl : q₁ = q := (inv_injective (by simpa using hq)).symm
        exact (norm_piLpFamilyContinuousLinearEquiv_one C u).le
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
        · simpa [piLpFamilyContinuousLinearEquiv_mk_apply] using
            (norm_mk_le_integral_stripPoisson_rpow_mul_rpow hθoo
              (piLpFamilyStripTracesEquiv C q₀ q₁ g i)).trans (le_abs_self _)
        · exact (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha_norm (sub_pos.2 hθ1).le)
            (Real.rpow_le_rpow (norm_nonneg _) hb_norm hθ0.le) (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq (by rw [← Real.rpow_add_of_nonneg
              (norm_nonneg _) (sub_pos.2 hθ1).le hθ0.le, sub_add_cancel, Real.rpow_one])
  · rw [eq_zero_of_notMem hθ u, map_zero, norm_zero, norm_zero]

private theorem norm_piLpFamilyCLE_symm_le_of_mk {q : ℝ≥0∞} {θ : ℝ}
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) {B : ℝ}
    (g : ∀ i, (C i).stripTraces) (hg_mk : ∀ i, mk θ (g i) = v i)
    (hG : ‖((piLpFamilyStripTracesEquiv C q₀ q₁).symm g).val‖ ≤ B) :
    ‖(piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ B := by
  have hv : v = WithLp.toLp q fun i => mk θ (g i) := PiLp.ext fun i => (hg_mk i).symm
  rw [hv, piLpFamilyContinuousLinearEquiv_symm_mk]
  exact (norm_mk_le _).trans ((Submodule.norm_coe _).symm.trans_le hG)

private theorem norm_symm_le_of_eq_top {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq : (∞ : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp ∞ (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpFamilyContinuousLinearEquiv C q₀ q₁ ∞ θ).symm v‖ ≤ ‖v‖ := by
  obtain ⟨rfl, rfl⟩ := (TauCeti.eq_top_iff_of_inv_eq hθ hq).1 rfl
  refine le_of_forall_pos_le_add fun ε hε => ?_
  choose g hg_mk hg_norm using fun i =>
    norm_lt_iff.1 ((PiLp.norm_apply_le v i).trans_lt (lt_add_of_pos_right ‖v‖ hε))
  have hB : 0 ≤ ‖v‖ + ε := add_nonneg (norm_nonneg v) hε.le
  refine norm_piLpFamilyCLE_symm_le_of_mk C v g hg_mk (norm_prod_le_iff.2 ⟨
    (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => (PiLp.norm_ofLp _).symm.trans_le <|
      (pi_norm_le_iff_of_nonneg hB).2 fun i => by
        simpa using (norm_stripTraces_fst_apply_le (g i) t).trans (hg_norm i).le,
    (ZeroAtInftyContinuousMap.norm_le hB).2 fun t => (PiLp.norm_ofLp _).symm.trans_le <|
      (pi_norm_le_iff_of_nonneg hB).2 fun i => by
        simpa using (norm_stripTraces_snd_apply_le (g i) t).trans (hg_norm i).le⟩)

private theorem norm_symm_le_of_ne_top {q : ℝ≥0∞} [Fact (1 ≤ q)] {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hq_top : q ≠ ∞) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ ‖v‖ := by
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
  refine (norm_piLpFamilyCLE_symm_le_of_mk C v g' (fun i => (hg'_eq i).trans (hg_eq i))
    (norm_prod_le_iff.2 ⟨
      (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
        (PiLp.norm_mono (y := WithLp.toLp q₀ fun i => B * (b i / B) ^ (q.toReal * (q₀⁻¹).toReal))
          fun i => by simpa using (hg'_0 i t).trans (le_abs_self _)).trans
          (TauCeti.norm_toLp_mul_div_rpow_le hq₀ hB (fun i => (hb i).1) hsum),
      (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t =>
        (PiLp.norm_mono (y := WithLp.toLp q₁ fun i => B * (b i / B) ^ (q.toReal * (q₁⁻¹).toReal))
          fun i => by simpa using (hg'_1 i t).trans (le_abs_self _)).trans
          (TauCeti.norm_toLp_mul_div_rpow_le hq₁ hB (fun i => (hb i).1) hsum)⟩)).trans hB_le

private theorem norm_piLpFamilyContinuousLinearEquiv_symm_le {q : ℝ≥0∞} [Fact (1 ≤ q)] {θ : ℝ}
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) :
    ‖(piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ ‖v‖ := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
    · obtain rfl : q₀ = q := (inv_injective (by simpa using hq)).symm
      exact (norm_piLpFamilyContinuousLinearEquiv_zero C _).symm.trans_le (by simp)
    · rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
      · obtain rfl : q₁ = q := (inv_injective (by simpa using hq)).symm
        exact (norm_piLpFamilyContinuousLinearEquiv_one C _).symm.trans_le (by simp)
      · rcases eq_or_ne q ∞ with rfl | hq_top
        · exact norm_symm_le_of_eq_top C ⟨hθ0, hθ1⟩ hq v
        · exact norm_symm_le_of_ne_top C ⟨hθ0, hθ1⟩ hq_top hq v
  · rw [eq_zero_of_notMem hθ ((piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm v), norm_zero]
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
def piLpFamilyEquiv :
    (piLpFamily C q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  LinearIsometryEquiv.ofBounds (piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).toLinearEquiv
    (norm_piLpFamilyContinuousLinearEquiv_le C hq)
    (norm_piLpFamilyContinuousLinearEquiv_symm_le C hq)

@[simp] theorem coe_piLpFamilyEquiv :
    (piLpFamilyEquiv C hq : (piLpFamily C q₀ q₁).ComplexMethodSpace θ →
      PiLp q (fun i => (C i).ComplexMethodSpace θ)) =
      piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ :=
  (rfl)

@[simp] theorem coe_piLpFamilyEquiv_symm :
    ((piLpFamilyEquiv C hq).symm : PiLp q (fun i => (C i).ComplexMethodSpace θ) →
      (piLpFamily C q₀ q₁).ComplexMethodSpace θ) =
      (piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm :=
  (rfl)

end

end PiLpFamilyEquiv

section ConstantCoupleEquiv

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V) {ι : Type*} [Fintype ι]
  {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
  (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)

/-- Canonical linear isometric identification between the complex interpolation space of
`C.piLp ι q₀ q₁` and that of `piLpFamily (fun _ : ι => C) q₀ q₁`. -/
private def piLpToFamilyEquiv (θ : ℝ) :
    (C.piLp ι q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      (piLpFamily (fun _ : ι => C) q₀ q₁).ComplexMethodSpace θ :=
  let e₀ := ContinuousLinearEquiv.refl ℂ (PiLp q₀ fun _ : ι => X₀)
  let e₁ := ContinuousLinearEquiv.refl ℂ (PiLp q₁ fun _ : ι => X₁)
  let h : ∀ x : (C.piLp ι q₀ q₁).inter,
      (piLpFamily (fun _ : ι => C) q₀ q₁).fstToSum (e₀ ((C.piLp ι q₀ q₁).interFst x)) =
        (piLpFamily (fun _ : ι => C) q₀ q₁).sndToSum (e₁ ((C.piLp ι q₀ q₁).interSnd x)) :=
    fun x => sumSpace_ext _ <| by
      ext k; simpa [e₀, e₁] using congrFun ((C.piLp ι q₀ q₁).embed₀_interFst x) k
  let hsymm : ∀ y : (piLpFamily (fun _ : ι => C) q₀ q₁).inter,
      (C.piLp ι q₀ q₁).fstToSum (e₀.symm ((piLpFamily (fun _ : ι => C) q₀ q₁).interFst y)) =
        (C.piLp ι q₀ q₁).sndToSum (e₁.symm ((piLpFamily (fun _ : ι => C) q₀ q₁).interSnd y)) :=
    fun y => sumSpace_ext _ <| by
      ext k; simpa [e₀, e₁] using congrFun ((piLpFamily (fun _ : ι => C) q₀ q₁).embed₀_interFst y) k
  let e := mapEquiv θ e₀ e₁ h hsymm
  LinearIsometryEquiv.ofBounds e.toLinearEquiv
    (fun u => (norm_mapEquiv (e₀ := e₀) (e₁ := e₁) (h := h) (hsymm := hsymm)
      (fun _ => rfl) (fun _ => rfl) u).le)
    (fun v => by
      have hnorm := norm_mapEquiv (e₀ := e₀) (e₁ := e₁) (h := h) (hsymm := hsymm)
        (fun _ => rfl) (fun _ => rfl) (e.symm v)
      change ‖e.symm v‖ ≤ ‖v‖
      rw [← hnorm, ContinuousLinearEquiv.apply_symm_apply])

private theorem toSum_piLpToFamilyEquiv (θ : ℝ)
    (u : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) (k : ι) :
    (piLpFamily (fun _ : ι => C) q₀ q₁).sumSpaceEmbed (toSum (piLpToFamilyEquiv C θ u)) k =
      (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum u) k := by
  let e₀ := ContinuousLinearEquiv.refl ℂ (PiLp q₀ fun _ : ι => X₀)
  let e₁ := ContinuousLinearEquiv.refl ℂ (PiLp q₁ fun _ : ι => X₁)
  let h : ∀ x : (C.piLp ι q₀ q₁).inter,
      (piLpFamily (fun _ : ι => C) q₀ q₁).fstToSum (e₀ ((C.piLp ι q₀ q₁).interFst x)) =
        (piLpFamily (fun _ : ι => C) q₀ q₁).sndToSum (e₁ ((C.piLp ι q₀ q₁).interSnd x)) :=
    fun x => sumSpace_ext _ <| by
      ext j; simpa [e₀, e₁] using congrFun ((C.piLp ι q₀ q₁).embed₀_interFst x) j
  let hsymm : ∀ y : (piLpFamily (fun _ : ι => C) q₀ q₁).inter,
      (C.piLp ι q₀ q₁).fstToSum (e₀.symm ((piLpFamily (fun _ : ι => C) q₀ q₁).interFst y)) =
        (C.piLp ι q₀ q₁).sndToSum (e₁.symm ((piLpFamily (fun _ : ι => C) q₀ q₁).interSnd y)) :=
    fun y => sumSpace_ext _ <| by
      ext j; simpa [e₀, e₁] using congrFun ((piLpFamily (fun _ : ι => C) q₀ q₁).embed₀_interFst y) j
  have hu := toSum_mapEquiv (θ := θ) e₀ e₁ h hsymm u
  change (piLpFamily (fun _ : ι => C) q₀ q₁).sumSpaceEmbed
      (toSum (mapEquiv θ e₀ e₁ h hsymm u)) k =
    (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum u) k
  rw [hu]
  obtain ⟨x₀, x₁, hx⟩ := (C.piLp ι q₀ q₁).exists_fstToSum_add_sndToSum_eq (toSum u)
  rw [← hx]
  simp [e₀, e₁]

/-- **Bergh–Löfström, Theorem 5.1.2 (for a single compatible couple, including `∞` endpoints).**
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun _ : ι => [X₀, X₁]_θ)` for `1 ≤ q₀, q₁, q ≤ ∞`
and `q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹`. -/
def piLpEquiv :
    (C.piLp ι q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      PiLp q (fun _ : ι => C.ComplexMethodSpace θ) :=
  (piLpToFamilyEquiv C θ).trans (piLpFamilyEquiv (fun _ : ι => C) hq)

@[simp] theorem piLpEquiv_apply_sumSpaceEmbed_toSum
    (u : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) (k : ι) :
    C.sumSpaceEmbed (toSum (piLpEquiv C hq u k)) =
      (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum u) k := by
  have h1 : toSum (piLpEquiv C hq u k) =
      piLpFamilySumEquiv (fun _ : ι => C) q₀ q₁ (toSum (piLpToFamilyEquiv C θ u)) k :=
    toSum_piLpFamilyContinuousLinearEquiv_apply (fun _ : ι => C) q₀ q₁ q θ
      (piLpToFamilyEquiv C θ u) k
  rw [h1, sumSpaceEmbed_piLpFamilySumEquiv_apply (fun _ : ι => C), toSum_piLpToFamilyEquiv]

@[simp] theorem sumSpaceEmbed_toSum_piLpEquiv_symm
    (v : PiLp q (fun _ : ι => C.ComplexMethodSpace θ)) (k : ι) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum ((piLpEquiv C hq).symm v)) k =
      C.sumSpaceEmbed (toSum (v k)) := by
  rw [← piLpEquiv_apply_sumSpaceEmbed_toSum C hq ((piLpEquiv C hq).symm v) k,
    LinearIsometryEquiv.apply_symm_apply]

end ConstantCoupleEquiv

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
def piLpReflEquiv :
    (piLpFamily (fun i => refl ℂ (X i)) q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q X :=
  (piLpFamilyEquiv (fun i => refl ℂ (X i)) hq).trans
    (LinearIsometryEquiv.piLpCongrRight q fun _ => reflEquiv hθ)

@[simp] theorem piLpReflEquiv_apply_apply
    (u : (piLpFamily (fun i => refl ℂ (X i)) q₀ q₁).ComplexMethodSpace θ) (i : ι) :
    piLpReflEquiv X hθ hq u i =
      (piLpFamily (fun i => refl ℂ (X i)) q₀ q₁).sumSpaceEmbed (toSum u) i := by
  rw [piLpReflEquiv, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    PiLp.toLp_apply, reflEquiv_apply, coe_piLpFamilyEquiv,
    toSum_piLpFamilyContinuousLinearEquiv_apply (fun j => refl ℂ (X j)),
    sumSpaceEmbed_piLpFamilySumEquiv_apply (fun j => refl ℂ (X j))]

@[simp] theorem sumSpaceEmbed_toSum_piLpReflEquiv_symm (x : PiLp q X) (i : ι) :
    (piLpFamily (fun i => refl ℂ (X i)) q₀ q₁).sumSpaceEmbed
        (toSum ((piLpReflEquiv X hθ hq).symm x)) i = x i := by
  rw [← piLpReflEquiv_apply_apply X hθ hq, LinearIsometryEquiv.apply_symm_apply]

end Refl

end ComplexMethodSpace

section Inclusion

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V} {ι : Type*} [Fintype ι]
  {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {θ : ℝ}

/-- On a boundary line `re w = j`, the multiplier `b ^ ((w - θ) s)` turns a bound `‖x‖ ≤ c` with
`c = N b` into `‖b ^ ((w - θ) s) • x‖ ≤ N b ^ r` for the exponent `r = (j - θ) s + 1`. -/
private theorem norm_cpow_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b N c : ℝ} (hb : 0 < b) (hc : c = N * b) {w : ℂ} {j s r : ℝ} (hw : w.re = j)
    (hr : (j - θ) * s + 1 = r) {x : E} (hx : ‖x‖ ≤ c) :
    ‖(b : ℂ) ^ ((w - θ) * (s : ℂ)) • x‖ ≤ ‖N * b ^ r‖ := by
  have hre : ((w - θ) * (s : ℂ)).re = (j - θ) * s := by
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero, hw]
  calc ‖(b : ℂ) ^ ((w - θ) * (s : ℂ)) • x‖ = b ^ ((j - θ) * s) * ‖x‖ := by
        rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hb, hre]
    _ ≤ b ^ ((j - θ) * s) * c := by gcongr
    _ = N * b ^ r := by rw [← hr, Real.rpow_add_one hb.ne', hc]; ring
    _ ≤ ‖N * b ^ r‖ := Real.le_norm_self _

/-- Coordinatewise bounded-boundary strip functions `F k`, multiplied by entire scalars `m k`
bounded on the strip, assemble into a bounded-boundary strip function `z ↦ (m k z • F k z)_k` of
the couple `(ℓ^{q₀}(X₀), ℓ^{q₁}(X₁))`. -/
private theorem isBoundedStripFunction_sum_sumSingle_smul [DecidableEq ι]
    {F : ι → ℂ → C.SumSpace}
    {g : ι → BoundedContinuousFunction ℝ X₀ × BoundedContinuousFunction ℝ X₁}
    (hF : ∀ k, C.IsBoundedStripFunction (F k) (g k)) {m : ι → ℂ → ℂ}
    (hm : ∀ k, Differentiable ℂ (m k)) {K : ι → ℝ}
    (hK : ∀ k, ∀ z ∈ verticalClosedStrip 0 1, ‖m k z‖ ≤ K k)
    {G : BoundedContinuousFunction ℝ (PiLp q₀ fun _ : ι => X₀) ×
      BoundedContinuousFunction ℝ (PiLp q₁ fun _ : ι => X₁)}
    (hG₀ : ∀ t, G.1 t = WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t)
    (hG₁ : ∀ t, G.2 t = WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t) :
    (C.piLp ι q₀ q₁).IsBoundedStripFunction
      (∑ k, fun z => C.sumSingle q₀ q₁ k (m k z • F k z)) G := by
  choose M hM using fun k => (hF k).exists_norm_le
  refine ⟨Finset.sum_induction _ (fun f => DiffContOnCl ℂ f (verticalStrip 0 1))
      (fun _ _ => DiffContOnCl.add) diffContOnCl_const fun k _ =>
        (C.sumSingle q₀ q₁ k).differentiable.comp_diffContOnCl
          ((hm k).diffContOnCl.smul (hF k).diffContOnCl),
    isBounded_iff_forall_norm_le.2 ⟨∑ k : ι, ‖C.sumSingle q₀ q₁ k‖ * (K k * M k), ?_⟩,
    fun t => ?_, fun t => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine ((C.sumSingle q₀ q₁ k).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_smul]
    exact mul_le_mul (hK k z hz) (hM k z hz) (norm_nonneg _) ((norm_nonneg _).trans (hK k z hz))
  · conv_rhs => rw [← PiLp.univ_sum_single (G.1 t)]
    simp [hG₀, map_sum, (hF _).apply_mul_I]
  · conv_rhs => rw [← PiLp.univ_sum_single (G.2 t)]
    simp [hG₁, map_sum, (hF _).apply_one_add_mul_I]

/-- The core estimate: if `c k > ‖u k‖_θ` and the families `(N (c k / N) ^ r_j)_k` have
`ℓ^{q_j}` norm at most `N`, for exponents with `(1 - θ) r₀ + θ r₁ = 1`, then `u` is an element of
`[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at most `N`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt (hθ : θ ∈ Icc 0 1) {r₀ r₁ : ℝ}
    (hr : (1 - θ) * r₀ + θ * r₁ = 1) (u : ι → C.ComplexMethodSpace θ) {c : ι → ℝ}
    (hc : ∀ k, ‖u k‖ < c k) {N : ℝ} (hN : 0 < N)
    (h₀ : ‖WithLp.toLp q₀ fun k => N * (c k / N) ^ r₀‖ ≤ N)
    (h₁ : ‖WithLp.toLp q₁ fun k => N * (c k / N) ^ r₁‖ ≤ N) :
    ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧ ‖v‖ ≤ N := by
  classical
  choose F g hF hFθ hg using fun k =>
    (ComplexMethodSpace.norm_lt_iff_exists_isBoundedStripFunction hθ).1 (hc k)
  have hb (k : ι) : 0 < c k / N := div_pos ((norm_nonneg _).trans_lt (hc k)) hN
  have hcN (k : ι) : c k = N * (c k / N) := by field_simp
  set m : ι → ℂ → ℂ := fun k z => ((c k / N : ℝ) : ℂ) ^ ((z - θ) * ((r₁ - r₀ : ℝ) : ℂ))
  have hm (k : ι) : Differentiable ℂ (m k) :=
    ((differentiable_id.sub_const _).mul_const _).const_cpow (.inl (by exact_mod_cast (hb k).ne'))
  have hb₀ (k : ι) (t : ℝ) : ‖m k (t * I) • (g k).1 t‖ ≤ ‖N * (c k / N) ^ r₀‖ :=
    norm_cpow_smul_le (j := 0) (hb k) (hcN k) (by simp) (by linear_combination -hr)
      (((g k).1.norm_coe_le_norm t).trans ((norm_fst_le _).trans (hg k).le))
  have hb₁ (k : ι) (t : ℝ) : ‖m k (1 + t * I) • (g k).2 t‖ ≤ ‖N * (c k / N) ^ r₁‖ :=
    norm_cpow_smul_le (j := 1) (hb k) (hcN k) (by simp) (by linear_combination -hr)
      (((g k).2.norm_coe_le_norm t).trans ((norm_snd_le _).trans (hg k).le))
  have hG₀ (t : ℝ) : ‖WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t‖ ≤ N :=
    (PiLp.norm_mono fun k => hb₀ k t).trans h₀
  have hG₁ (t : ℝ) : ‖WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t‖ ≤ N :=
    (PiLp.norm_mono fun k => hb₁ k t).trans h₁
  let G₀ : BoundedContinuousFunction ℝ (PiLp q₀ fun _ : ι => X₀) :=
    .ofNormedAddCommGroup (fun t => WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t)
      ((PiLp.continuous_toLp _ _).comp <| continuous_pi fun k =>
        (((hm k).continuous).comp (by fun_prop)).smul (g k).1.continuous)
      N hG₀
  let G₁ : BoundedContinuousFunction ℝ (PiLp q₁ fun _ : ι => X₁) :=
    .ofNormedAddCommGroup (fun t => WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t)
      ((PiLp.continuous_toLp _ _).comp <| continuous_pi fun k =>
        (((hm k).continuous).comp (by fun_prop)).smul (g k).2.continuous)
      N hG₁
  have hΦ := isBoundedStripFunction_sum_sumSingle_smul (G := (G₀, G₁)) hF hm
    (fun k _ hz => Complex.HadamardThreeLines.norm_ofReal_cpow_sub_mul_le (hb k) hθ (r₁ - r₀) hz)
    (fun _ => rfl) (fun _ => rfl)
  obtain ⟨v, hv⟩ :=
    (ComplexMethodSpace.exists_toSum_eq_iff_isBoundedStripFunction hθ).2 ⟨_, _, hΦ, rfl⟩
  refine ⟨v, ?_, (ComplexMethodSpace.norm_le_of_isBoundedStripFunction hθ hΦ hv).trans ?_⟩
  · rw [hv]
    simp [m, ← hFθ, map_sum, Finset.univ_sum_single]
  · exact norm_prod_le_iff.2 ⟨BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hN.le hG₀,
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hN.le hG₁⟩

variable [Fact (1 ≤ q)]

/-- For every family `c` strictly dominating the coordinate norms of `u ∈ ℓ^q([X₀, X₁]_θ)`, `u` is
an element of `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at most `‖c‖_{ℓ^q}`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp [Nonempty ι]
    (hθ : θ ∈ Icc 0 1) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ)
    {c : ι → ℝ} (hc : ∀ k, ‖u k‖ < c k) : ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧
        ‖v‖ ≤ ‖WithLp.toLp q c‖ := by
  have hc₀ (k : ι) : 0 < c k := (norm_nonneg _).trans_lt (hc k)
  have hN : 0 < ‖WithLp.toLp q c‖ := PiLp.norm_toLp_pos (hc₀ (Classical.arbitrary ι))
  by_cases hqt : q = ∞
  · obtain ⟨rfl, rfl⟩ := hq_top hqt
    subst hqt
    have hcN : (fun k => ‖WithLp.toLp ∞ c‖ * (c k / ‖WithLp.toLp ∞ c‖) ^ (1 : ℝ)) = c := by
      ext k
      rw [Real.rpow_one]
      field_simp
    exact exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt hθ (r₀ := 1) (r₁ := 1) (by ring) u hc
      hN (by rw [hcN]) (by rw [hcN])
  have hne (p : ℝ≥0∞) [Fact (1 ≤ p)] : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq₀ : q.toReal ≠ 0 := ((ENNReal.toReal_pos_iff_ne_top q).2 hqt).ne'
  have hθq := inv_toReal_eq_of_inv_eq (hne q₀) (hne q₁) hθ hq
  refine exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt hθ ?_ u hc hN
    (PiLp.norm_toLp_mul_div_rpow hqt (hne q₀) hc₀).le
    (PiLp.norm_toLp_mul_div_rpow hqt (hne q₁) hc₀).le
  calc (1 - θ) * (q.toReal / q₀.toReal) + θ * (q.toReal / q₁.toReal)
      = q.toReal * ((1 - θ) * q₀.toReal⁻¹ + θ * q₁.toReal⁻¹) := by ring
    _ = 1 := by rw [← hθq, mul_inv_cancel₀ hq₀]

/-- Every family `u ∈ ℓ^q([X₀, X₁]_θ)` is an element of `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at
most `‖u‖`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le (hθ : θ ∈ Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧ ‖v‖ ≤ ‖u‖ := by
  cases isEmpty_or_nonempty ι
  · exact ⟨0, funext isEmptyElim, by simp⟩
  obtain ⟨v, hv, -⟩ := exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp hθ hq hq_top u
    (c := fun k => ‖u k‖ + 1) fun k => by linarith
  refine ⟨v, hv, le_of_forall_pos_lt_add fun δ hδ => ?_⟩
  set K := ‖WithLp.toLp q fun _ : ι => (1 : ℝ)‖
  have hε : 0 < δ / (K + 1) := div_pos hδ (by positivity)
  obtain ⟨v', hv', hnorm⟩ := exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp hθ hq hq_top u
    (c := fun k => ‖u k‖ + δ / (K + 1)) fun k => by linarith
  obtain rfl : v' = v := ComplexMethodSpace.ext (sumSpace_ext _ (hv'.trans hv.symm))
  have hsplit : (WithLp.toLp q fun k => ‖u k‖ + δ / (K + 1)) =
      WithLp.toLp q (fun k => ‖u k‖) + (δ / (K + 1)) • WithLp.toLp q fun _ : ι => (1 : ℝ) :=
    WithLp.ofLp_injective q <| funext fun k => by simp
  calc ‖v'‖ ≤ ‖WithLp.toLp q fun k => ‖u k‖ + δ / (K + 1)‖ := hnorm
    _ ≤ ‖u‖ + δ / (K + 1) * K := by
        rw [hsplit]
        refine (norm_add_le _ _).trans_eq ?_
        rw [PiLp.norm_norm, norm_smul, Real.norm_of_nonneg hε.le]
    _ < ‖u‖ + δ := by
        have : δ * K / (K + 1) < δ := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        rw [div_mul_eq_mul_div]
        linarith

variable (hθ : θ ∈ Icc 0 1) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
  (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞)

private theorem sumSpaceEmbed_toSum_choose (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum
        (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose) =
      fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k)) :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.1

namespace ComplexMethodSpace

/-- **Complex interpolation of finite `ℓ^q` sums, `ℓ^q([X₀, X₁]_θ) ⊆ [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`.**
For `0 ≤ θ ≤ 1` and `1 / q = (1 - θ) / q₀ + θ / q₁` (with `q < ∞` unless `q₀ = q₁ = ∞`), the
inclusion of the finite families of elements of `[X₀, X₁]_θ`, normed in `ℓ^q`, into the complex
interpolation space of the couple `(ℓ^{q₀}(ι; X₀), ℓ^{q₁}(ι; X₁))`. It lies over the identity of
`ι → V` (`sumSpaceEmbed_toSum_ofPiLp`) and has norm at most one (`norm_ofPiLp_le`). -/
def ofPiLp : (PiLp q fun _ : ι => C.ComplexMethodSpace θ) →L[ℂ]
    (C.piLp ι q₀ q₁).ComplexMethodSpace θ :=
  LinearMap.mkContinuous
    { toFun u := (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose
      map_add' u w := ext <| sumSpace_ext _ <| by
        simp only [map_add, sumSpaceEmbed_toSum_choose hθ hq hq_top]
        ext k
        simp
      map_smul' a u := ext <| sumSpace_ext _ <| by
        simp only [map_smul, sumSpaceEmbed_toSum_choose hθ hq hq_top]
        ext k
        simp }
    1 fun u => by
      simpa using (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.2

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` lies over the identity of
`ι → V`: the element it produces has coordinates `u k`. -/
@[simp]
theorem sumSpaceEmbed_toSum_ofPiLp (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum (ofPiLp hθ hq hq_top u)) =
      fun k => C.sumSpaceEmbed (toSum (u k)) :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.1

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` does not increase norms:
`‖u‖_{[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ} ≤ ‖(‖u k‖_θ)_k‖_{ℓ^q}`. -/
theorem norm_ofPiLp_le (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    ‖ofPiLp hθ hq hq_top u‖ ≤ ‖u‖ :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.2

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` has operator norm at most one. -/
theorem opNorm_ofPiLp_le :
    ‖(ofPiLp hθ hq hq_top : (PiLp q fun _ : ι => C.ComplexMethodSpace θ) →L[ℂ]
      (C.piLp ι q₀ q₁).ComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_ofPiLp_le hθ hq hq_top u

variable (q₀ q₁) in
/-- The projection `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ → [X₀, X₁]_θ` onto the `k`-th coordinate, induced
by the coordinate projections of `ℓ^{q₀}(X₀)` and `ℓ^{q₁}(X₁)`. It lies over the coordinate
projection of the sum spaces (`toSum_piLpProj`) and does not increase norms
(`norm_piLpProj_le`). -/
def piLpProj (k : ι) : (C.piLp ι q₀ q₁).ComplexMethodSpace θ →L[ℂ] C.ComplexMethodSpace θ :=
  map θ (PiLp.proj q₀ (fun _ : ι => X₀) k) (PiLp.proj q₁ (fun _ : ι => X₁) k) fun x =>
    sumSpace_ext _ <| by simpa using congrFun ((C.piLp ι q₀ q₁).embed₀_interFst x) k

/-- The coordinate projection of the complex interpolation spaces lies over the coordinate
projection of the sum spaces. -/
@[simp]
theorem toSum_piLpProj (k : ι) (v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :
    toSum (piLpProj q₀ q₁ k v) = C.sumProj q₀ q₁ k (toSum v) := by
  rw [piLpProj, toSum_map]
  exact DFunLike.congr_fun ((C.piLp ι q₀ q₁).sumLift_unique _ _ _
    (by ext; simp) (by ext; simp)).symm (toSum v)

/-- The coordinate projection `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ → [X₀, X₁]_θ` does not increase norms. -/
theorem norm_piLpProj_le (k : ι) (v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :
    ‖piLpProj q₀ q₁ k v‖ ≤ ‖v‖ :=
  norm_map_le_of_norm_le _ _ _ (fun x => PiLp.norm_apply_le x k) (fun x => PiLp.norm_apply_le x k) v

/-- The coordinate projections are left inverse to the inclusion
`ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`. -/
@[simp]
theorem piLpProj_ofPiLp (k : ι) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    piLpProj q₀ q₁ k (ofPiLp hθ hq hq_top u) = u k :=
  ext <| sumSpace_ext _ <| by simp

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` is injective. -/
theorem ofPiLp_injective :
    Function.Injective (ofPiLp hθ hq hq_top :
      (PiLp q fun _ : ι => C.ComplexMethodSpace θ) → (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :=
  fun u w h => WithLp.ofLp_injective q <| funext fun k => by
    simpa using congrArg (piLpProj q₀ q₁ k) h

end ComplexMethodSpace

end Inclusion

end CompatibleCouple

end TauCeti
