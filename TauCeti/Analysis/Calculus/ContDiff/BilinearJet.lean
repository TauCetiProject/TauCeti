/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.Calculus.ContDiff.Prod

/-!
# Continuity of the coordinate `2`-jet of a family of bilinear forms

If a family of bilinear-form valued maps agrees, on an open set of parameter-point pairs, with
`C^2` coefficients in a basis, then its Gram matrix and its first and second derivatives in the
point variable are continuous there (`TauCeti.continuousAt_jets_of_eqOn_contDiffOn`).
-/

public section

open Filter Topology

namespace TauCeti

/-- **Continuity of the coordinate `2`-jet of a family of bilinear forms.** If a family `K` of
bilinear-form valued maps on `W` agrees on an open set `V` of parameter-point pairs with the
`C^2` coefficients `F i j` in a basis `b`, then its Gram matrix and its first and second
derivatives in the point variable are continuous at any point of `V`. -/
theorem continuousAt_jets_of_eqOn_contDiffOn {𝕜 P W ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕜 W) (K : P → W → W →L[𝕜] W →L[𝕜] 𝕜) (F : ι → ι → P × W → 𝕜)
    {V : Set (P × W)} (hV : IsOpen V) {w₀ : P × W} (hw₀ : w₀ ∈ V)
    (hF : ∀ i j, ContDiffOn 𝕜 2 (F i j) V) (hK : ∀ r ∈ V, ∀ i j, K r.1 r.2 (b i) (b j) = F i j r) :
    ContinuousAt (fun q : P × W ↦ LinearMap.toMatrix₂ b b (K q.1 q.2).toBilinForm) w₀ ∧
    ContinuousAt (fun q : P × W ↦ fun k i j ↦
      fderiv 𝕜 (fun z ↦ K q.1 z (b i) (b j)) q.2 (b k)) w₀ ∧
    ContinuousAt (fun q : P × W ↦ fun m k i j ↦ fderiv 𝕜 (fun z ↦ fderiv 𝕜
      (fun z' ↦ K q.1 z' (b i) (b j)) z (b k)) q.2 (b m)) w₀ := by
  let D (i j k) : P × W → 𝕜 := fun r ↦ fderiv 𝕜 (fun z ↦ F i j (r.1, z)) r.2 (b k)
  have hmem {r : P × W} (hr : r ∈ V) : ∀ᶠ z in 𝓝 r.2, (r.1, z) ∈ V :=
    (hV.preimage (Continuous.prodMk_right r.1)).mem_nhds hr
  have hD (i j k) {r} (hr : r ∈ V) : ContDiffAt 𝕜 1 (D i j k) r :=
    contDiffAt_fderiv_snd_apply ((hF i j).contDiffAt (hV.mem_nhds hr)) (by norm_cast) _
  have hd₁ (i j) {r : P × W} (hr : r ∈ V) :
      fderiv 𝕜 (fun z ↦ K r.1 z (b i) (b j)) r.2 = fderiv 𝕜 (fun z ↦ F i j (r.1, z)) r.2 := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hmem hr] with z hz
    exact hK (r.1, z) hz i j
  have hd₂ (i j k) {r : P × W} (hr : r ∈ V) :
      fderiv 𝕜 (fun z ↦ fderiv 𝕜 (fun z' ↦ K r.1 z' (b i) (b j)) z (b k)) r.2 =
        fderiv 𝕜 (fun z ↦ D i j k (r.1, z)) r.2 := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hmem hr] with z hz
    rw [hd₁ i j (r := (r.1, z)) hz]
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousAt.congr (f := fun r ↦ Matrix.of fun i j ↦ F i j r) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
      exact (hF i j).continuousOn.continuousAt (hV.mem_nhds hw₀)
    · ext i j
      simp [LinearMap.toMatrix₂_apply, hK r hr]
  · refine ContinuousAt.congr (f := fun r k i j ↦ D i j k r) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
      exact (hD i j k hw₀).continuousAt
    · funext k i j
      simp only [D, hd₁ i j hr]
  · refine ContinuousAt.congr
      (f := fun r m k i j ↦ fderiv 𝕜 (fun z ↦ D i j k (r.1, z)) r.2 (b m)) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun m ↦ continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦
        continuousAt_pi.2 fun j ↦ ?_
      exact (contDiffAt_fderiv_snd_apply (hD i j k hw₀) (m := 0) (by norm_num) _).continuousAt
    · funext m k i j
      simp only [hd₂ i j k hr]

end TauCeti
