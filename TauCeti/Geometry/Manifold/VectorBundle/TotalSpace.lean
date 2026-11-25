/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Smoothness of maps into a fibre bundle by comparison of fibre coordinates

A map `g` into the total space of a fibre bundle is `C^n` at a point if its base map is `C^n`
there and, near that point, its fibre coordinates in the preferred trivialization agree with the
fibre coordinates of a `C^n` map `h` into another bundle with the same model fibre and base model
(`Bundle.contMDiffAt_totalSpace_of_eventuallyEq`). This is how fibrewise identifications of two
bundles that agree in local frames are shown to be smooth.
-/

public section

open Bundle Filter Topology
open scoped Manifold

namespace Bundle

variable {n : WithTop ℕ∞} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EX HX X EB HB B₁ B₂ G : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B₁] [ChartedSpace HB B₁] [TopologicalSpace B₂] [ChartedSpace HB B₂]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E₁ : B₁ → Type*} [TopologicalSpace (TotalSpace G E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle G E₁]
  {E₂ : B₂ → Type*} [TopologicalSpace (TotalSpace G E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle G E₂]

/-- A map into a fibre bundle is `C^n` at a point if its base map is `C^n` there and, near that
point, its fibre coordinates agree with those of a map into another bundle that is `C^n` there. -/
theorem contMDiffAt_totalSpace_of_eventuallyEq {g : X → TotalSpace G E₂}
    {h : X → TotalSpace G E₁} {p : X} (hg : ContMDiffAt IX IB n (fun x ↦ (g x).proj) p)
    (hh : ContMDiffAt IX (IB.prod 𝓘(𝕜, G)) n h p)
    (hco : ∀ᶠ q in 𝓝 p, (trivializationAt G E₂ (g p).proj (g q)).2 =
      (trivializationAt G E₁ (h p).proj (h q)).2) :
    ContMDiffAt IX (IB.prod 𝓘(𝕜, G)) n g p := by
  rw [Bundle.contMDiffAt_totalSpace_iff]
  exact ⟨hg, (Bundle.contMDiffAt_totalSpace_iff.mp hh).2.congr_of_eventuallyEq hco⟩

/-- A map into a fibre bundle is `C^n` if its base map is `C^n` and, near each point, its fibre
coordinates agree with those of a `C^n` map into another bundle. -/
theorem contMDiff_totalSpace_of_eventuallyEq {g : X → TotalSpace G E₂}
    {h : X → TotalSpace G E₁} (hg : ContMDiff IX IB n fun x ↦ (g x).proj)
    (hh : ContMDiff IX (IB.prod 𝓘(𝕜, G)) n h)
    (hco : ∀ p, ∀ᶠ q in 𝓝 p, (trivializationAt G E₂ (g p).proj (g q)).2 =
      (trivializationAt G E₁ (h p).proj (h q)).2) :
    ContMDiff IX (IB.prod 𝓘(𝕜, G)) n g :=
  fun p ↦ contMDiffAt_totalSpace_of_eventuallyEq (hg p) (hh p) (hco p)

end Bundle
