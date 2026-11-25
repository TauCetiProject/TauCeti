/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.Convergence
public import TauCeti.Geometry.MeasureTheory.Varifold.LineVarifold
public import TauCeti.Topology.Sets.Opens
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Checks for varifold convergence

Examples of varifold convergence for varifolds on a finite-dimensional real inner product space
`E` in the Euclidean form `Measure ((⊤ : Opens E) × G(E, k))`, with varifold convergence
`TauCeti.VarifoldTendsto` (convergence against compactly supported continuous functions).

* *Moving Dirac masses.* `δ_{((j+1)⁻¹ e, P)} → δ_{(0, P)}` (`varifoldTendsto_dirac_inv_add_one`),
  and the limit is not `δ_{(0, P')}` for `P' ≠ P` (`not_varifoldTendsto_dirac_of_ne`); this needs
  `G(E, k)` to have two points, so `0 < k < dim E`.
* *Mass escaping to infinity.* `δ_{(j e, P)} → 0` for `e ≠ 0` (`varifoldTendsto_dirac_smul`): the
  masses are all `1` and the limit has mass `0`, so the mass is only lower semicontinuous.
* *Alternating lifts and rotating lines.* Two different line varifolds with the same weight, such
  as the `x`-axis of `ℝ²` with the horizontal plane and with the vertical plane, alternate along a
  sequence with constant weights and no varifold limit (`not_varifoldTendsto_alternate`,
  `not_varifoldTendsto_alternate_axis`); lines through `0` whose unit directions converge, with
  their own tangent lines, converge to the varifold of the limit line
  (`varifoldTendsto_verticalLift_self`, from `Euclidean.varifoldTendsto_lineVarifold`), for
  instance the lines at angles `θ_j → θ` in `ℝ²` (`varifoldTendsto_verticalLift_angleVector`).
* *The local mass bound is necessary.* `j δ_p` has no convergent subsequence for any point `p`
  (`not_varifoldTendsto_natCast_smul_dirac`).
-/

open MeasureTheory Set TopologicalSpace Filter Metric Module Euclidean
open scoped ENNReal Topology CompactlySupported

public noncomputable section

namespace TauCeti.Examples.VarifoldConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

/-- The point `(x, P)` of `E × G(E, k)`, with `x` in the open set `⊤`. -/
abbrev pt (x : E) (P : grassmannian ℝ E k) : (⊤ : Opens E) × grassmannian ℝ E k :=
  (⟨x, trivial⟩, P)

/-! ### Moving Dirac masses -/

/-- **`δ_{((j+1)⁻¹ e, P)} → δ_{(0, P)}`.** -/
theorem varifoldTendsto_dirac_inv_add_one (e : E) (P : grassmannian ℝ E k) :
    VarifoldTendsto (fun j : ℕ => Measure.dirac (pt (((j : ℝ) + 1)⁻¹ • e) P))
      (Measure.dirac (pt 0 P)) := by
  have h : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹ • e) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const e
  exact varifoldTendsto_dirac ((tendsto_subtype_rng.2 h).prodMk_nhds tendsto_const_nhds)

/-- A sequence of Dirac varifolds at points converging to `(x, P)` does not converge to
`δ_{(x, P')}` for `P' ≠ P`: limits are unique and `δ_{(x, P)} ≠ δ_{(x, P')}`. -/
theorem not_varifoldTendsto_dirac_of_ne {y : ℕ → (⊤ : Opens E) × grassmannian ℝ E k}
    {x : E} {P P' : grassmannian ℝ E k} (hy : Tendsto y atTop (𝓝 (pt x P))) (hPP' : P ≠ P') :
    ¬VarifoldTendsto (fun j => Measure.dirac (y j)) (Measure.dirac (pt x P')) := by
  intro h
  have := (varifoldTendsto_dirac hy).unique h
  rw [dirac_eq_dirac_iff] at this
  exact hPP' (Prod.ext_iff.1 this).2

/-! ### Mass escaping to infinity -/

/-- **`δ_{(j e, P)} → 0`** for `e ≠ 0`: the Dirac masses leave every compact set. -/
theorem varifoldTendsto_dirac_smul {e : E} (he : e ≠ 0) (P : grassmannian ℝ E k) :
    VarifoldTendsto (fun j : ℕ => Measure.dirac (pt ((j : ℝ) • e) P)) 0 := by
  refine varifoldTendsto_dirac_zero (tendsto_cocompact_of_tendsto_dist_comp_atTop (pt 0 P) ?_)
  have hnorm : Tendsto (fun j : ℕ => ‖(j : ℝ) • e‖) atTop atTop := by
    simp_rw [norm_smul, Real.norm_natCast]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (norm_pos_iff.2 he)
  simpa [Prod.dist_eq, Subtype.dist_eq] using hnorm

/-- The masses `δ_{(j e, P)}(E × G(E, k)) = 1` do not tend to the mass `0` of the limit. -/
example (x : E) (P : grassmannian ℝ E k) :
    Measure.dirac (pt x P) univ = 1 ∧ (0 : Measure ((⊤ : Opens E) × grassmannian ℝ E k)) univ = 0 :=
  ⟨measure_univ, rfl⟩

/-! ### Alternating sequences and rotating lines -/

/-- A sequence alternating between two different regular measures has no varifold limit among
the regular measures: its even and odd subsequences are constant. -/
theorem not_varifoldTendsto_alternate {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [T2Space Y] [LocallyCompactSpace Y] [BorelSpace Y] {V₁ V₂ ν : Measure Y} [V₁.Regular]
    [V₂.Regular] [ν.Regular] (h : V₁ ≠ V₂) :
    ¬VarifoldTendsto (fun j => if Even j then V₁ else V₂) ν := by
  intro hν
  have h₁ := hν.comp (φ := fun j => 2 * j)
    (tendsto_atTop_mono (fun j => show j ≤ 2 * j by omega) tendsto_id)
  have h₂ := hν.comp (φ := fun j => 2 * j + 1)
    (tendsto_atTop_mono (fun j => show j ≤ 2 * j + 1 by omega) tendsto_id)
  have e₁ : ((fun j => if Even j then V₁ else V₂) ∘ fun j => 2 * j) = fun _ => V₁ := by
    funext j
    simp
  have e₂ : ((fun j => if Even j then V₁ else V₂) ∘ fun j => 2 * j + 1) = fun _ => V₂ := by
    funext j
    simp
  rw [e₁] at h₁
  rw [e₂] at h₂
  exact h (((varifoldTendsto_const V₁).unique h₁).trans ((varifoldTendsto_const V₂).unique h₂).symm)

/-- **Lines through `0` with converging unit directions converge**, each carrying its own tangent
line. -/
theorem varifoldTendsto_verticalLift_self {u : ℕ → E} {u₀ : E} (hu : ∀ j, ‖u j‖ = 1)
    (hu₀' : ‖u₀‖ = 1) (hu₀ : Tendsto u atTop (𝓝 u₀)) :
    VarifoldTendsto (fun j => verticalLift 0 (u j) (u j) (norm_ne_zero_iff.1 (hu j ▸ one_ne_zero)))
      (verticalLift 0 u₀ u₀ (norm_ne_zero_iff.1 (hu₀' ▸ one_ne_zero))) := by
  simp only [verticalLift_def]
  exact varifoldTendsto_lineVarifold hu hu₀ (grassmannian.tendsto_spanLine _ _ hu₀)

/-- The unit vector `(cos θ, sin θ)` of `ℝ²`. -/
def angleVector (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos θ, Real.sin θ]

/-- `(cos θ, sin θ)` is a unit vector. -/
theorem norm_angleVector (θ : ℝ) : ‖angleVector θ‖ = 1 := by
  simp [angleVector, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- **The lines of `ℝ²` through `0` at angles `θ_j → θ` converge to the line at angle `θ`**, each
carrying its own tangent line. -/
theorem varifoldTendsto_verticalLift_angleVector {θ : ℕ → ℝ} {θ₀ : ℝ}
    (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    VarifoldTendsto
      (fun j => verticalLift 0 (angleVector (θ j)) (angleVector (θ j))
        (norm_ne_zero_iff.1 (norm_angleVector (θ j) ▸ one_ne_zero)))
      (verticalLift 0 (angleVector θ₀) (angleVector θ₀)
        (norm_ne_zero_iff.1 (norm_angleVector θ₀ ▸ one_ne_zero))) := by
  refine varifoldTendsto_verticalLift_self (fun j => norm_angleVector _) (norm_angleVector θ₀) ?_
  have hc : Continuous angleVector := by
    unfold angleVector
    fun_prop
  exact (hc.tendsto θ₀).comp hθ

/-- **The horizontal and the vertical lift of the `x`-axis alternate without a limit.** The
`x`-axis of `ℝ²` lifted with the horizontal plane and with the vertical plane, two different
varifolds (with the same weight), alternate along a sequence that converges to no varifold. -/
theorem not_varifoldTendsto_alternate_axis
    {ν : Measure ((⊤ : Opens (EuclideanSpace ℝ (Fin 2))) ×
      grassmannian ℝ (EuclideanSpace ℝ (Fin 2)) 1)} [IsFiniteMeasureOnCompacts ν] :
    ¬VarifoldTendsto (fun j => if Even j then
        verticalLift 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) (by simp)
      else verticalLift 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) (by simp)) ν := by
  set e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  set e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  have he₀ : e₀ ≠ 0 := by simp [e₀]
  have he₁ : e₁ ≠ 0 := by simp [e₁]
  have := isFiniteMeasureOnCompacts_verticalLift (a := 0) he₀ he₀
  have := isFiniteMeasureOnCompacts_verticalLift (a := 0) he₀ he₁
  refine not_varifoldTendsto_alternate fun h => ?_
  rw [verticalLift_def, verticalLift_def] at h
  have h₁ : e₁ ∈ ℝ ∙ e₀ :=
    (grassmannian.spanLine_inj he₀ he₁).1 (lineVarifold_injective _ _ h) ▸
      Submodule.mem_span_singleton_self e₁
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h₁
  simpa [e₀, e₁] using congrArg (· 1) hc

/-! ### The local mass bound is necessary -/

/-- **`j δ_p` has no convergent subsequence**: along any subsequence the masses of the compact
set `{p}` are unbounded. -/
theorem not_varifoldTendsto_natCast_smul_dirac (p : (⊤ : Opens E) × grassmannian ℝ E k)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (ν : Measure ((⊤ : Opens E) × grassmannian ℝ E k)) :
    ¬VarifoldTendsto (fun j => ((φ j : NNReal) • Measure.dirac p)) ν := by
  intro h
  refine h.iSup_measure_ne_top (isCompact_singleton (x := p)) (eq_top_iff.2 ?_)
  calc (⊤ : ℝ≥0∞) = ⨆ j : ℕ, (j : ℝ≥0∞) := ENNReal.iSup_natCast.symm
    _ ≤ ⨆ j, ((φ j : NNReal) • Measure.dirac p) {p} := by
      refine iSup_mono fun j => ?_
      simp only [smul_apply, Measure.dirac_apply_of_mem (mem_singleton p), smul_eq_mul,
        mul_one, ENNReal.smul_def]
      exact_mod_cast hφ.id_le j

end TauCeti.Examples.VarifoldConvergence
