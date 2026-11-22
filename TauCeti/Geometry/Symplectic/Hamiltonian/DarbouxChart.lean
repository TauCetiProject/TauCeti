/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Canonical conjugate variables in a Darboux chart

Let `σ` be a smooth two-form on a manifold `M`, with the conventions `ι_{X_f} σ = df` and
`{f, g} = σ(X_f, X_g) = df(X_g)`. A **Darboux chart** (`TauCeti.SmoothTwoForm.IsDarbouxChart`) is
a partial diffeomorphism `chart` from `M` to `(ι → ℝ) × (ι → ℝ)`, with coordinates `(q, p)`,
pulling `∑ᵢ dqᵢ ∧ dpᵢ` back to `σ` on its source. The positions `q` of a Darboux chart are
**canonical conjugate variables** of its momenta `p`. On the source of the chart:

* `σ` is nondegenerate (`TauCeti.SmoothTwoForm.IsDarbouxChart.isInvertible_flat`);
* the Hamiltonian vector field of a function equal to the momentum `pᵢ` is the coordinate field
  `∂/∂qᵢ`, and that of a function equal to the position `qᵢ` is `-∂/∂pᵢ`
  (`TauCeti.SmoothTwoForm.IsDarbouxChart.mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd`,
  `TauCeti.SmoothTwoForm.IsDarbouxChart.mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst`);
* the coordinates satisfy the canonical relations `{qᵢ, pⱼ} = δᵢⱼ`, `{qᵢ, qⱼ} = 0` and
  `{pᵢ, pⱼ} = 0`
  (`TauCeti.SmoothTwoForm.IsDarbouxChart.poissonBracket_eq_ite_of_eqOn_fst_of_eqOn_snd`,
  `TauCeti.SmoothTwoForm.IsDarbouxChart.poissonBracket_eq_zero_of_eqOn_fst`,
  `TauCeti.SmoothTwoForm.IsDarbouxChart.poissonBracket_eq_zero_of_eqOn_snd`);
* the Hamiltonian flow of the momentum `pᵢ` translates the position `qᵢ` at unit speed and fixes
  the other coordinates, as long as it stays in the chart (`TauCeti.SmoothTwoForm.IsDarbouxChart.`
  `apply_eq_add_smul_single_of_isMIntegralCurveOn_hamiltonianVectorField`).

These are stated for any function agreeing with a coordinate on the source, so that they apply to
functions that are only known to be coordinates of some Darboux chart, such as the commuting
functions of the Carathéodory–Jacobi–Lie theorem
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_snd_castAdd_eq`). No completeness of the
Hamiltonian vector fields is needed.

## References

* P. Libermann and C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, Mathematics and
  its Applications 35, D. Reidel, 1987, Chapter III.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

open Set Filter Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι]
  {chart : PartialDiffeomorph I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) M ((ι → ℝ) × (ι → ℝ)) ∞} {y : M}

variable (σ chart) in
/-- A **Darboux chart** for a two-form `σ`: a partial diffeomorphism `chart` from `M` to
`(ι → ℝ) × (ι → ℝ)`, with coordinates `(q, p)`, pulling the standard form `∑ᵢ dqᵢ ∧ dpᵢ` back to
`σ` on its source. -/
structure IsDarbouxChart : Prop where
  /-- On the source, `σ(v, w) = ∑ᵢ (dqᵢ(v) dpᵢ(w) - dqᵢ(w) dpᵢ(v))`. -/
  eval₂_eq : ∀ y ∈ chart.source, ∀ v w : TangentSpace I y, SmoothBundleForm.eval₂ σ y v w =
    ∑ i, ((mvfderiv I chart y v).1 i * (mvfderiv I chart y w).2 i -
      (mvfderiv I chart y w).1 i * (mvfderiv I chart y v).2 i)

namespace IsDarbouxChart

variable (hform : σ.IsDarbouxChart chart)

include hform

/-- **A two-form with a Darboux chart is nondegenerate on its source.** If a partial
diffeomorphism to `(ι → ℝ) × (ι → ℝ)` pulls `∑ᵢ dqᵢ ∧ dpᵢ` back to `σ` on its source, then the flat
map of `σ` is invertible at every point of that source. -/
theorem isInvertible_flat (hy : y ∈ chart.source) : (σ.flat y).IsInvertible := by
  classical
  have hbij := chart.bijective_mvfderiv (by simp) hy
  have : FiniteDimensional ℝ E :=
    (LinearEquiv.ofBijective (mvfderiv I chart y).toLinearMap hbij).symm.finiteDimensional
  rw [isInvertible_flat_iff]
  refine (SmoothForm.isAlt_bilinFormAt σ y).isRefl.nondegenerate_iff_separatingLeft.2
    fun v hv ↦ hbij.1 ?_
  -- Pairing with vectors whose images are `(0, eₗ)` and `(eₗ, 0)` reads off the coordinates
  -- `(dq v)ₗ` and `-(dp v)ₗ` of the image of `v`, which therefore vanish.
  rw [map_zero]
  ext l
  · obtain ⟨w, hw⟩ := hbij.2 (0, Pi.single l 1)
    have h := hv w
    rw [SmoothForm.bilinFormAt_apply, hform.eval₂_eq y hy, hw] at h
    simpa [Pi.single_apply] using h
  · obtain ⟨w, hw⟩ := hbij.2 (Pi.single l 1, 0)
    have h := hv w
    rw [SmoothForm.bilinFormAt_apply, hform.eval₂_eq y hy, hw] at h
    simpa [Pi.single_apply] using h

/-- **The Hamiltonian vector field of a momentum is the conjugate position field.** In a Darboux
chart, if `f` equals the momentum `pᵢ` on the source, then at every point of the source the chart
sends the Hamiltonian vector field of `f` to `(eᵢ, 0)`: `X_f = ∂/∂qᵢ`. -/
theorem mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd [DecidableEq ι] {f : M → ℝ} {i : ι}
    (hf : EqOn f (fun z ↦ (chart z).2 i) chart.source) (hy : y ∈ chart.source) :
    mvfderiv I chart y (σ.hamiltonianVectorField f y) = (Pi.single i 1, 0) := by
  have hd := chart.mdifferentiableAt (by simp) hy
  obtain ⟨v, hv⟩ := (chart.bijective_mvfderiv (by simp) hy).2 (Pi.single i 1, 0)
  rw [(hamiltonianVectorField_eq_iff_of_isInvertible_flat
    (hform.isInvertible_flat hy)).2 fun w ↦ ?_, hv]
  rw [(hf.eventuallyEq_of_mem (chart.open_source.mem_nhds hy)).mvfderiv_eq,
    ← mvfderiv_apply_apply (Φ := fun z ↦ (chart z).2)
      ((ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).differentiableAt.comp_mdifferentiableAt hd),
    hd.mvfderiv_snd_apply, hform.eval₂_eq y hy, hv]
  simp [Pi.single_apply]

/-- **The Hamiltonian vector field of a position is minus the conjugate momentum field.** In a
Darboux chart, if `f` equals the position `qᵢ` on the source, then at every point of the source the
chart sends the Hamiltonian vector field of `f` to `(0, -eᵢ)`: `X_f = -∂/∂pᵢ`. -/
theorem mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst [DecidableEq ι] {f : M → ℝ} {i : ι}
    (hf : EqOn f (fun z ↦ (chart z).1 i) chart.source) (hy : y ∈ chart.source) :
    mvfderiv I chart y (σ.hamiltonianVectorField f y) = (0, -Pi.single i 1) := by
  have hd := chart.mdifferentiableAt (by simp) hy
  obtain ⟨v, hv⟩ := (chart.bijective_mvfderiv (by simp) hy).2 (0, -Pi.single i 1)
  rw [(hamiltonianVectorField_eq_iff_of_isInvertible_flat
    (hform.isInvertible_flat hy)).2 fun w ↦ ?_, hv]
  rw [(hf.eventuallyEq_of_mem (chart.open_source.mem_nhds hy)).mvfderiv_eq,
    ← mvfderiv_apply_apply (Φ := fun z ↦ (chart z).1)
      ((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).differentiableAt.comp_mdifferentiableAt hd),
    hd.mvfderiv_fst_apply, hform.eval₂_eq y hy, hv]
  simp [Pi.single_apply]

/-- **The canonical relation `{qᵢ, pⱼ} = δᵢⱼ`.** In a Darboux chart, if `f` equals the position `qᵢ`
and `g` the momentum `pⱼ` on the source, then their Poisson bracket at every point of the source
is `1` when `i = j` and `0` otherwise. -/
theorem poissonBracket_eq_ite_of_eqOn_fst_of_eqOn_snd [DecidableEq ι] {f g : M → ℝ} {i j : ι}
    (hf : EqOn f (fun z ↦ (chart z).1 i) chart.source)
    (hg : EqOn g (fun z ↦ (chart z).2 j) chart.source) (hy : y ∈ chart.source) :
    σ.poissonBracket f g y = if i = j then 1 else 0 := by
  rw [poissonBracket_def, hform.eval₂_eq y hy,
    hform.mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst hf hy,
    hform.mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hg hy]
  simp [Pi.single_apply]

/-- **The canonical relation `{qᵢ, qⱼ} = 0`.** In a Darboux chart, functions equal on the source to
positions Poisson-commute at every point of the source. -/
theorem poissonBracket_eq_zero_of_eqOn_fst {f g : M → ℝ} {i j : ι}
    (hf : EqOn f (fun z ↦ (chart z).1 i) chart.source)
    (hg : EqOn g (fun z ↦ (chart z).1 j) chart.source) (hy : y ∈ chart.source) :
    σ.poissonBracket f g y = 0 := by
  classical
  rw [poissonBracket_def, hform.eval₂_eq y hy,
    hform.mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst hf hy,
    hform.mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst hg hy]
  simp

/-- **The canonical relation `{pᵢ, pⱼ} = 0`.** In a Darboux chart, functions equal on the source to
momenta Poisson-commute at every point of the source. -/
theorem poissonBracket_eq_zero_of_eqOn_snd {f g : M → ℝ} {i j : ι}
    (hf : EqOn f (fun z ↦ (chart z).2 i) chart.source)
    (hg : EqOn g (fun z ↦ (chart z).2 j) chart.source) (hy : y ∈ chart.source) :
    σ.poissonBracket f g y = 0 := by
  classical
  rw [poissonBracket_def, hform.eval₂_eq y hy,
    hform.mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hf hy,
    hform.mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hg hy]
  simp

/-- **The Hamiltonian flow of a momentum translates its conjugate position.** In a Darboux chart,
let `f` equal the momentum `pᵢ` on the source, and let `γ` be an integral curve of the Hamiltonian
vector field of `f` on a preconnected set of times `s`, such as an interval, staying in the source.
Then in the chart `γ` moves along the `qᵢ`-axis at unit speed:
`chart (γ t) = chart (γ t₀) + (t - t₀) • (eᵢ, 0)`. -/
theorem apply_eq_add_smul_single_of_isMIntegralCurveOn_hamiltonianVectorField
    [DecidableEq ι] {f : M → ℝ} {i : ι}
    (hf : EqOn f (fun z ↦ (chart z).2 i) chart.source) {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (σ.hamiltonianVectorField f) s) (hs : IsPreconnected s)
    (hγs : ∀ t ∈ s, γ t ∈ chart.source) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    chart (γ t) = chart (γ t₀) + (t - t₀) • ((Pi.single i 1, 0) : (ι → ℝ) × (ι → ℝ)) :=
  hγ.apply_eq_add_smul_of_mvfderiv_apply_eq hs
    (fun u hu ↦ chart.mdifferentiableAt (by simp) (hγs u hu))
    (fun u hu ↦ hform.mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hf (hγs u hu)) ht₀ ht

end IsDarbouxChart

end SmoothTwoForm

end TauCeti
