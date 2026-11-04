/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# `C^n` local fibre coordinates of finite-rank bundle cores

For a point-indexed finite-rank vector-bundle core `E : FiniteRankBundleCore 𝕜 B` over a charted
space `B`, the preferred trivialization at a base point `x` is the chart `E.core.localTriv x`
(`FiniteRankBundleCore.trivializationAt_core`). Consequently, the fibre coordinate in
`E.core.localTriv p₀.proj` is `C^n` at every total-space point `p₀`, without any smoothness
hypothesis on the base atlas or on the transition functions of `E`.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]

/-- For any point-indexed finite-rank core `E`, the fibre coordinate in the chart at `p₀.proj` is
`C^n` at `p₀`. -/
theorem contMDiffAt_localTriv_snd (E : FiniteRankBundleCore 𝕜 B) (p₀ : E.core.TotalSpace) :
    ContMDiffAt (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) 𝓘(𝕜, Fin E.rank → 𝕜) n
      (fun p : E.core.TotalSpace ↦ (E.core.localTriv p₀.proj p).2) p₀ := by
  simpa only [E.trivializationAt_core] using
    p₀.contMDiffAt_trivializationAt_snd (IB := IB) (n := n)

end TauCeti.FiniteRankBundleCore
