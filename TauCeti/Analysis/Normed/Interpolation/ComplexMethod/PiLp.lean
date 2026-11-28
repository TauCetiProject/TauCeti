/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple.PiLp
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

We also specialize to a single compatible couple
`C.piLp ι q₀ q₁ = piLpFamily (fun _ : ι => C) q₀ q₁`
(`CompatibleCouple.ComplexMethodSpace.piLpEquiv`) and record the constant-couple specialization
`[PiLp q₀ X, PiLp q₁ X]_θ ≃ₗᵢ[ℂ] PiLp q X` (`CompatibleCouple.ComplexMethodSpace.piLpReflEquiv`).

## Main declarations

* `CompatibleCouple.piLpFamilyStripTracesEquiv`: coordinatewise equivalence for boundary traces.
* `CompatibleCouple.ComplexMethodSpace.piLpFamilyContinuousLinearEquiv`: coordinatewise continuous
  linear equivalence
  `(piLpFamily C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ] PiLp q (fun i => [X₀ i, X₁ i]_θ)`.
* `CompatibleCouple.ComplexMethodSpace.piLpFamilyEquiv`: **Bergh–Löfström, Theorem 5.1.2** for
  families of couples, upgrading `piLpFamilyContinuousLinearEquiv` to a linear isometric equivalence
  under the exponent relation.
* `CompatibleCouple.ComplexMethodSpace.piLpEquiv`: **Bergh–Löfström, Theorem 5.1.2** for a single
  compatible couple `C.piLp ι q₀ q₁`.
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

namespace TauCeti.CompatibleCouple

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
    (∀ i, (C i).stripTraces) →L[ℂ] (piLpFamily C q₀ q₁).stripTraces := by classical
  exact ∑ i : ι, (stripTracesMap (PiLp.singleCLM q₀ ℂ X₀ i) (PiLp.singleCLM q₁ ℂ X₁ i)
    (fstToSum_singleCLM_interFst_eq_sndToSum_singleCLM_interSnd C q₀ q₁ i)).comp
    (ContinuousLinearMap.proj i)

private theorem piLpFamilyStripTracesInv_apply_fst (h : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
    ((piLpFamilyStripTracesInv C q₀ q₁ h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).1 t := by classical
  simp only [piLpFamilyStripTracesInv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Submodule.coe_sum,
    Prod.fst_sum, WithLp.ofLp_sum, stripTracesMap_apply_fst, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

private theorem piLpFamilyStripTracesInv_apply_snd (h : ∀ i, (C i).stripTraces) (t : ℝ) (j : ι) :
    ((piLpFamilyStripTracesInv C q₀ q₁ h : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) j =
      (h j : C₀(ℝ, X₀ j) × C₀(ℝ, X₁ j)).2 t := by classical
  simp only [piLpFamilyStripTracesInv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Submodule.coe_sum,
    Prod.snd_sum, WithLp.ofLp_sum, stripTracesMap_apply_snd, PiLp.singleCLM_apply]
  rw [Fintype.sum_eq_single j (fun _ h => PiLp.single_eq_of_ne _ h.symm _), PiLp.single_eq_same]

/-- Admissible boundary traces for `CompatibleCouple.piLpFamily C q₀ q₁` identify canonically with
tuples of admissible boundary traces `∀ i, (C i).stripTraces` via coordinatewise projection. -/
def piLpFamilyStripTracesEquiv : (piLpFamily C q₀ q₁).stripTraces ≃L[ℂ] ∀ i, (C i).stripTraces :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpFamilyStripTracesFwd C q₀ q₁)
    (piLpFamilyStripTracesInv C q₀ q₁)
    (ContinuousLinearMap.ext fun _ => funext fun _ => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun _ => by simp [piLpFamilyStripTracesFwd,
        piLpFamilyStripTracesInv_apply_fst])
      (ZeroAtInftyContinuousMap.ext fun _ => by simp [piLpFamilyStripTracesFwd,
        piLpFamilyStripTracesInv_apply_snd])))
    (ContinuousLinearMap.ext fun _ => Subtype.ext (Prod.ext
      (ZeroAtInftyContinuousMap.ext fun _ => PiLp.ext fun _ => by
        simp [piLpFamilyStripTracesInv_apply_fst, piLpFamilyStripTracesFwd])
      (ZeroAtInftyContinuousMap.ext fun _ => PiLp.ext fun _ => by
        simp [piLpFamilyStripTracesInv_apply_snd, piLpFamilyStripTracesFwd])))

private theorem piLpFamilyStripTracesEquiv_apply_eq_fwd (g : (piLpFamily C q₀ q₁).stripTraces) :
    piLpFamilyStripTracesEquiv C q₀ q₁ g = piLpFamilyStripTracesFwd C q₀ q₁ g := (rfl)

@[simp] theorem piLpFamilyStripTracesEquiv_apply_fst (g : (piLpFamily C q₀ q₁).stripTraces)
    (i : ι) (t : ℝ) : (piLpFamilyStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t i := by
  simp [piLpFamilyStripTracesEquiv_apply_eq_fwd, piLpFamilyStripTracesFwd]

@[simp] theorem piLpFamilyStripTracesEquiv_apply_snd (g : (piLpFamily C q₀ q₁).stripTraces)
    (i : ι) (t : ℝ) : (piLpFamilyStripTracesEquiv C q₀ q₁ g i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t =
      (g : C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t i := by
  simp [piLpFamilyStripTracesEquiv_apply_eq_fwd, piLpFamilyStripTracesFwd]

@[simp] theorem piLpFamilyStripTracesEquiv_symm_apply_fst (h : ∀ i, (C i).stripTraces)
    (t : ℝ) (i : ι) : (((piLpFamilyStripTracesEquiv C q₀ q₁).symm h :
      C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).1 t) i = (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).1 t := by
  rw [← piLpFamilyStripTracesEquiv_apply_fst, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem piLpFamilyStripTracesEquiv_symm_apply_snd (h : ∀ i, (C i).stripTraces)
    (t : ℝ) (i : ι) : (((piLpFamilyStripTracesEquiv C q₀ q₁).symm h :
      C₀(ℝ, PiLp q₀ X₀) × C₀(ℝ, PiLp q₁ X₁)).2 t) i = (h i : C₀(ℝ, X₀ i) × C₀(ℝ, X₁ i)).2 t := by
  rw [← piLpFamilyStripTracesEquiv_apply_snd, ContinuousLinearEquiv.apply_symm_apply]

/-- `stripFunction` evaluation at `z` commutes coordinatewise with
`piLpFamilyStripTracesEquiv`. -/
@[simp] theorem stripFunction_piLpFamilyStripTracesEquiv_apply
    (g : (piLpFamily C q₀ q₁).stripTraces) (i : ι) (z : ℂ) :
    (C i).stripFunction (piLpFamilyStripTracesEquiv C q₀ q₁ g i) z =
      piLpFamilySumEquiv C q₀ q₁ ((piLpFamily C q₀ q₁).stripFunction g z) i := by
  rw [← stripEval_apply, ← stripEval_apply, piLpFamilyStripTracesEquiv_apply_eq_fwd,
    piLpFamilyStripTracesFwd, ContinuousLinearMap.pi_apply, stripEval_stripTracesMap _ _ _,
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
    |>.toContinuousLinearMap.comp (ContinuousLinearMap.pi fun i => map θ (PiLp.proj q₀ X₀ i)
      (PiLp.proj q₁ X₁ i) (fstToSum_proj_interFst_eq_sndToSum_proj_interSnd C q₀ q₁ i))

private def piLpFamilyCLEInv :
    PiLp q (fun i => (C i).ComplexMethodSpace θ) →L[ℂ]
      (piLpFamily C q₀ q₁).ComplexMethodSpace θ := by classical
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
      mk θ ((piLpFamilyStripTracesEquiv C q₀ q₁).symm h) := by classical
  simp only [piLpFamilyCLEInv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, map_mk, ← map_sum]
  refine congrArg (mk θ) (Subtype.ext (Prod.ext
    (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => by
      simpa [piLpFamilyStripTracesInv] using piLpFamilyStripTracesInv_apply_fst C q₀ q₁ h t j)
    (ZeroAtInftyContinuousMap.ext fun t => PiLp.ext fun j => by
      simpa [piLpFamilyStripTracesInv] using piLpFamilyStripTracesInv_apply_snd C q₀ q₁ h t j)))

/-- Coordinatewise continuous linear equivalence between `(piLpFamily C q₀ q₁).ComplexMethodSpace θ`
and `PiLp q (fun i => (C i).ComplexMethodSpace θ)`. Unlike `piLpFamilyEquiv`, this topological
isomorphism requires no relation between `q₀`, `q₁`, `q`, and `θ`, and no `1 ≤ q` assumption on
`q`. -/
def piLpFamilyContinuousLinearEquiv : (piLpFamily C q₀ q₁).ComplexMethodSpace θ ≃L[ℂ]
    PiLp q (fun i => (C i).ComplexMethodSpace θ) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (piLpFamilyCLEFwd C q₀ q₁ q θ)
    (piLpFamilyCLEInv C q₀ q₁ q θ)
    (ContinuousLinearMap.ext fun v => by
      choose h hh using fun i => mk_surjective (v i)
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        show v = WithLp.toLp q fun i => mk θ (h i) from PiLp.ext fun i => (hh i).symm,
        piLpFamilyCLEInv_mk, piLpFamilyCLEFwd_mk]; exact PiLp.ext fun i => by simp)
    (ContinuousLinearMap.ext fun u => by
      obtain ⟨g, rfl⟩ := mk_surjective u; simp [piLpFamilyCLEFwd_mk, piLpFamilyCLEInv_mk])

private theorem piLpFamilyContinuousLinearEquiv_apply_eq_fwd
    (u : (piLpFamily C q₀ q₁).ComplexMethodSpace θ) :
    piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ u = piLpFamilyCLEFwd C q₀ q₁ q θ u := (rfl)

@[simp] theorem piLpFamilyContinuousLinearEquiv_mk_apply (g : (piLpFamily C q₀ q₁).stripTraces)
    (i : ι) : piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ (mk θ g) i =
      mk θ (piLpFamilyStripTracesEquiv C q₀ q₁ g i) := by
  rw [piLpFamilyContinuousLinearEquiv_apply_eq_fwd, piLpFamilyCLEFwd_mk, PiLp.toLp_apply]

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
  exact (PiLp.norm_norm _).symm.trans (by simp [norm_mk_zero])

private theorem norm_piLpFamilyContinuousLinearEquiv_one
    (u : (piLpFamily C q₀ q₁).ComplexMethodSpace 1) :
    ‖piLpFamilyContinuousLinearEquiv C q₀ q₁ q₁ 1 u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  exact (PiLp.norm_norm _).symm.trans (by simp [norm_mk_one])

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
        have ha := (ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le g.val.1
          (sub_pos.2 hθ1) (integrable_stripPoisson₀ θ) (ae_of_all _ fun t =>
            (stripPoisson₀_pos hθoo t).le) (integral_stripPoisson₀ ⟨hθ0, hθ1.le⟩)).trans
          ((norm_fst_le g.val).trans_eq (Submodule.norm_coe g))
        have hb := (ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le g.val.2 hθ0
          (integrable_stripPoisson₁ θ) (ae_of_all _ fun t =>
            (stripPoisson₁_pos hθoo t).le) (integral_stripPoisson₁ ⟨hθ0.le, hθ1⟩)).trans
          ((norm_snd_le g.val).trans_eq (Submodule.norm_coe g))
        -- coordinatewise Poisson log-convexity bound
        have hcoord (i : ι) : ‖piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ (mk θ g) i‖ ≤
            ‖WithLp.toLp q (fun j => a j ^ (1 - θ) * b j ^ θ) i‖ := by
          simpa [a, b, piLpFamilyContinuousLinearEquiv_mk_apply] using
            (norm_mk_le_integral_stripPoisson_rpow_mul_rpow hθoo
              (piLpFamilyStripTracesEquiv C q₀ q₁ g i)).trans (le_abs_self _)
        -- PiLp Hölder step combining the weighted `L^{q₀}` and `L^{q₁}` coordinate norms
        have hholder : ‖WithLp.toLp q fun i => a i ^ (1 - θ) * b i ^ θ‖ ≤
            ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ :=
          TauCeti.norm_toLp_rpow_mul_rpow_le (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
            (zero_lt_one.trans_le (Fact.out : 1 ≤ q₁)).ne' (Ioo_subset_Icc_self hθoo) hq
            (fun i => mul_nonneg (inv_pos.2 (sub_pos.2 hθ1)).le (integral_nonneg fun t =>
              mul_nonneg (norm_nonneg _) (stripPoisson₀_pos hθoo t).le))
            (fun i => mul_nonneg (inv_pos.2 hθ0).le (integral_nonneg fun t =>
              mul_nonneg (norm_nonneg _) (stripPoisson₁_pos hθoo t).le))
        -- combine the global `a` and `b` bounds `ha` and `hb`
        have hcomb : ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ ≤ ‖g‖ :=
          (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha (sub_pos.2 hθ1).le)
            (Real.rpow_le_rpow (norm_nonneg _) hb hθ0.le) (by positivity) (by positivity)).trans_eq
            (by rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (sub_pos.2 hθ1).le hθ0.le,
              sub_add_cancel, Real.rpow_one])
        exact ((PiLp.norm_mono hcoord).trans hholder).trans_lt (hcomb.trans_lt hg)
  · rw [eq_zero_of_notMem hθ u, map_zero, norm_zero, norm_zero]

private theorem norm_piLpFamilyCLE_symm_le_of_mk {q : ℝ≥0∞} {θ : ℝ}
    (v : PiLp q (fun i => (C i).ComplexMethodSpace θ)) {B : ℝ}
    (g : ∀ i, (C i).stripTraces) (hg_mk : ∀ i, mk θ (g i) = v i)
    (hG : ‖((piLpFamilyStripTracesEquiv C q₀ q₁).symm g).val‖ ≤ B) :
    ‖(piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm v‖ ≤ B := by
  rw [show v = WithLp.toLp q fun i => mk θ (g i) from PiLp.ext fun i => (hg_mk i).symm,
    piLpFamilyContinuousLinearEquiv_symm_mk]
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
      (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t => (PiLp.norm_mono fun i => by
        simpa using (hg'_0 i t).trans (le_abs_self _)).trans
        (TauCeti.norm_toLp_mul_div_rpow_le hq₀ hB (fun i => (hb i).1) hsum),
      (ZeroAtInftyContinuousMap.norm_le hB.le).2 fun t => (PiLp.norm_mono fun i => by
        simpa using (hg'_1 i t).trans (le_abs_self _)).trans
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

@[simp] theorem coe_piLpFamilyEquiv : (piLpFamilyEquiv C hq :
      (piLpFamily C q₀ q₁).ComplexMethodSpace θ → PiLp q (fun i => (C i).ComplexMethodSpace θ)) =
    piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ := (rfl)

@[simp] theorem coe_piLpFamilyEquiv_symm : ((piLpFamilyEquiv C hq).symm :
      PiLp q (fun i => (C i).ComplexMethodSpace θ) → (piLpFamily C q₀ q₁).ComplexMethodSpace θ) =
    (piLpFamilyContinuousLinearEquiv C q₀ q₁ q θ).symm := (rfl)

end

end PiLpFamilyEquiv

section ConstantCoupleEquiv

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V) {ι : Type*} [Fintype ι]
  {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)] {θ : ℝ}
  (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)

/-- **Bergh–Löfström, Theorem 5.1.2 (for a single compatible couple, including `∞` endpoints).**
`[PiLp q₀ X₀, PiLp q₁ X₁]_θ ≃ₗᵢ[ℂ] PiLp q (fun _ : ι => [X₀, X₁]_θ)` for `1 ≤ q₀, q₁, q ≤ ∞`
and `q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹`. -/
def piLpEquiv :
    (C.piLp ι q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] PiLp q (fun _ : ι => C.ComplexMethodSpace θ) :=
  piLpFamilyEquiv (fun _ : ι => C) hq

@[simp] theorem piLpEquiv_apply_sumSpaceEmbed_toSum (u : (C.piLp ι q₀ q₁).ComplexMethodSpace θ)
    (k : ι) : C.sumSpaceEmbed (toSum (piLpEquiv C hq u k)) =
      (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum u) k := by
  rw [piLpEquiv, coe_piLpFamilyEquiv,
    toSum_piLpFamilyContinuousLinearEquiv_apply (fun _ : ι => C),
    sumSpaceEmbed_piLpFamilySumEquiv_apply (fun _ : ι => C)]

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
def piLpReflEquiv : (piLpFamily (fun i => refl ℂ (X i)) q₀ q₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
    PiLp q X :=
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

end TauCeti.CompatibleCouple
