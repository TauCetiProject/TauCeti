/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Operator fields with Lᵖ orbits

If every orbit of a field `A : S → X →L[𝕜] Y` belongs to `Lᵖ`, the map sending
`x` to the class of `s ↦ A s x` is automatically bounded when `X` and `Y` are
Banach spaces and `1 ≤ p`. No measurability into the operator-norm topology or
common pointwise bound on `A` is required. The closed graph theorem applies
because Lᵖ convergence admits an almost everywhere convergent subsequence.
The proof uses `LinearMap.continuous_of_seq_closed_graph` and
`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`.

The map is characterized by its almost everywhere orbit formula, commutes with
bounded maps in either space, and has the expected bound under an Lᵖ majorant.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.1, for orbitwise measurable operator fields.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TauCeti

variable {S 𝕜 X Y Z : Type*} [MeasurableSpace S] {μ : Measure S}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded orbit map of an operator field all of whose orbits belong to Lᵖ.
The measure is arbitrary, and the exponent may be infinity. -/
noncomputable def orbitLpCLM (A : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ) : X →L[𝕜] Lp Y p μ := by
  let T : X →ₗ[𝕜] Lp Y p μ :=
    { toFun := fun x ↦ (hA x).toLp (fun s ↦ A s x)
      map_add' := fun x y ↦ by
        simpa only [map_add, Pi.add_def] using (hA x).toLp_add (hA y)
      map_smul' := fun c x ↦ by
        simpa only [map_smul, Pi.smul_def, RingHom.id_apply] using (hA x).toLp_const_smul c }
  refine ⟨T, T.continuous_of_seq_closed_graph fun u x y hu hy ↦ ?_⟩
  obtain ⟨n, hn, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
  apply Lp.ext
  have hrep : ∀ᵐ s ∂μ, ∀ k, T (u (n k)) s = A s (u (n k)) :=
    ae_all_iff.2 fun k ↦ (hA (u (n k))).coeFn_toLp
  have hx : ∀ᵐ s ∂μ, T x s = A s x := (hA x).coeFn_toLp
  filter_upwards [hlim, hrep, hx] with s hs hseq hx
  rw [hx]
  have hpoint : Tendsto (fun k ↦ A s (u (n k))) atTop (𝓝 (A s x)) := by
    simpa only [Function.comp_def] using
      (((A s).continuous.tendsto x).comp (hu.comp hn.tendsto_atTop))
  exact tendsto_nhds_unique (by simpa only [Function.comp_apply, hseq] using hs)
    hpoint

/-- The orbit map sends a vector to the Lᵖ class of its orbit. -/
@[simp]
theorem orbitLpCLM_apply (A : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ) (x : X) :
    orbitLpCLM A hA x = (hA x).toLp (fun s ↦ A s x) := by
  rfl

/-- The representative of the bounded orbit map agrees almost everywhere with the orbit. -/
theorem coeFn_orbitLpCLM (A : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ) (x : X) :
    orbitLpCLM A hA x =ᵐ[μ] fun s ↦ A s x := by
  rw [orbitLpCLM_apply]
  exact (hA x).coeFn_toLp

/-- The almost everywhere orbit formula uniquely characterizes the bounded orbit map. -/
theorem eq_orbitLpCLM_iff (A : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ) (T : X →L[𝕜] Lp Y p μ) :
    T = orbitLpCLM A hA ↔ ∀ x, T x =ᵐ[μ] fun s ↦ A s x := by
  refine ⟨fun h x ↦ h ▸ coeFn_orbitLpCLM A hA x, fun h ↦ ?_⟩
  ext x
  exact (h x).trans (coeFn_orbitLpCLM A hA x).symm

/-- Orbitwise almost everywhere equality of operator fields gives equal bounded orbit maps.
The exceptional null set may depend on the vector. -/
theorem orbitLpCLM_congr (A B : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ)
    (hB : ∀ x, MemLp (fun s ↦ B s x) p μ)
    (h : ∀ x, (fun s ↦ A s x) =ᵐ[μ] fun s ↦ B s x) :
    orbitLpCLM A hA = orbitLpCLM B hB := by
  apply (eq_orbitLpCLM_iff B hB _).2
  exact fun x ↦ (coeFn_orbitLpCLM A hA x).trans (h x)

/-- An Lᵖ majorant of the operator field bounds the norm of its orbit map. It is enough
to have the estimate almost everywhere separately for each vector. -/
theorem norm_orbitLpCLM_le (A : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ) (g : Lp ℝ p μ)
    (hbound : ∀ x, ∀ᵐ s ∂μ, ‖A s x‖ ≤ ‖g s‖ * ‖x‖) :
    ‖orbitLpCLM A hA‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖orbitLpCLM A hA x‖ ≤ ‖x‖ * ‖g‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [coeFn_orbitLpCLM A hA x, hbound x] with s hs hb
      simpa only [hs, mul_comm] using hb
    _ = ‖g‖ * ‖x‖ := mul_comm _ _

variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

/-- Bounded postcomposition of an operator field induces postcomposition on its orbit map. -/
theorem orbitLpCLM_postcomp (A : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ) (B : Y →L[𝕜] Z) :
    orbitLpCLM (fun s ↦ B.comp (A s)) (fun x ↦ B.comp_memLp' (hA x)) =
      (B.compLpL p μ).comp (orbitLpCLM A hA) := by
  symm
  apply (eq_orbitLpCLM_iff _ _ _).2
  intro x
  simpa only [ContinuousLinearMap.comp_apply, Function.comp_def] using
    (B.coeFn_compLpL (orbitLpCLM A hA x)).trans
      ((coeFn_orbitLpCLM A hA x).fun_comp B)

/-- Bounded precomposition of an operator field induces precomposition on its orbit map. -/
theorem orbitLpCLM_precomp (A : S → X →L[𝕜] Y)
    (hA : ∀ x, MemLp (fun s ↦ A s x) p μ) (B : Z →L[𝕜] X) :
    orbitLpCLM (fun s ↦ (A s).comp B) (fun x ↦ hA (B x)) =
      (orbitLpCLM A hA).comp B := by
  symm
  apply (eq_orbitLpCLM_iff _ _ _).2
  intro x
  simpa only [ContinuousLinearMap.comp_apply] using coeFn_orbitLpCLM A hA (B x)

end TauCeti
