/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Topology.UniformSpace.Ascoli

/-!
# Pointwise closure extension and compact uniform convergence for eventually Lipschitz families

Mathlib's `LipschitzWith.uniformEquicontinuous` and `LipschitzOnWith.uniformEquicontinuousOn`
require a common Lipschitz constant across the entire index type `ι`. When convergence is taken
along a filter `l : Filter ι` (for instance along an approximate unit that is only *eventually*
norm-bounded), a common Lipschitz bound `∀ᶠ i in l, LipschitzWith K (F i)` (or `LipschitzOnWith`)
only holds eventually along `l`. Restricting `l` to the subtype of `K`-Lipschitz indices upgrades:

* pointwise convergence on a subset `s` to any point `x ∈ closure s` at which the limit map has a
  limit along `𝓝[s] x` (`TauCeti.tendsto_of_mem_closure_of_lipschitzWith`, via
  `EquicontinuousAt.tendsto_of_mem_closure`);
* pointwise convergence on a compact set `s` to uniform convergence on `s`
  (`TauCeti.tendstoUniformlyOn_of_lipschitzOnWith` and
  `TauCeti.tendstoUniformlyOn_of_lipschitzWith`, via
  `EquicontinuousOn.tendstoUniformlyOn_of_tendsto`).
-/

public section

open Filter Topology
open scoped NNReal

namespace TauCeti

variable {ι X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- If a family `F : ι → X → Y` is eventually `K`-Lipschitz along `l : Filter ι`, converges
pointwise to `f` on `s`, and `f` tends to `z` along `𝓝[s] x` at a point `x ∈ closure s`, then
`F · x` tends to `z` along `l`. -/
theorem tendsto_of_mem_closure_of_lipschitzWith {l : Filter ι} {F : ι → X → Y} {f : X → Y}
    {K : ℝ≥0} (hF : ∀ᶠ i in l, LipschitzWith K (F i)) {s : Set X} {x : X} {z : Y}
    (hf : Tendsto f (𝓝[s] x) (𝓝 z)) (hs : ∀ y ∈ s, Tendsto (F · y) l (𝓝 (f y)))
    (hx : x ∈ closure s) : Tendsto (F · x) l (𝓝 z) := by
  let S : Set ι := {i | LipschitzWith K (F i)}
  have hmap : (l.comap ((↑) : S → ι)).map ((↑) : S → ι) = l :=
    map_comap_of_mem (hF.mono fun i hi => ⟨⟨i, hi⟩, rfl⟩)
  have heq : EquicontinuousAt (fun j : S => F j.1) x :=
    (LipschitzWith.uniformEquicontinuous (fun j : S => F j.1) K fun j => j.2).equicontinuous x
  have hmem : Tendsto (fun j : S => F j.1 x) (l.comap (↑)) (𝓝 z) :=
    heq.tendsto_of_mem_closure hf (fun y hy => (hs y hy).comp tendsto_comap) hx
  rwa [← hmap, tendsto_map'_iff]

/-- If a family `F : ι → X → Y` is eventually `K`-Lipschitz on a compact set `s` along
`l : Filter ι` and converges pointwise to `f` on `s`, then `F` converges uniformly to `f` on `s`
along `l`. -/
theorem tendstoUniformlyOn_of_lipschitzOnWith {l : Filter ι} {F : ι → X → Y} {f : X → Y}
    {s : Set X} {K : ℝ≥0} (hF : ∀ᶠ i in l, LipschitzOnWith K (F i) s) (hs : IsCompact s)
    (hpt : ∀ x ∈ s, Tendsto (F · x) l (𝓝 (f x))) : TendstoUniformlyOn F f l s := by
  let S : Set ι := {i | LipschitzOnWith K (F i) s}
  have hmap : (l.comap ((↑) : S → ι)).map ((↑) : S → ι) = l :=
    map_comap_of_mem (hF.mono fun i hi => ⟨⟨i, hi⟩, rfl⟩)
  have heq : EquicontinuousOn (fun j : S => F j.1) s :=
    (LipschitzOnWith.uniformEquicontinuousOn (fun j : S => F j.1) K fun j => j.2).equicontinuousOn
  have hunif : TendstoUniformlyOn (fun j : S => F j.1) f (l.comap (↑)) s :=
    heq.tendstoUniformlyOn_of_tendsto hs fun x hx => (hpt x hx).comp tendsto_comap
  exact fun u hu => by rw [← hmap, eventually_map]; exact hunif u hu

/-- If a family `F : ι → X → Y` is eventually `K`-Lipschitz along `l : Filter ι` and converges
pointwise to `f` on a compact set `s`, then `F` converges uniformly to `f` on `s` along `l`. -/
theorem tendstoUniformlyOn_of_lipschitzWith {l : Filter ι} {F : ι → X → Y} {f : X → Y}
    {s : Set X} {K : ℝ≥0} (hF : ∀ᶠ i in l, LipschitzWith K (F i)) (hs : IsCompact s)
    (hpt : ∀ x ∈ s, Tendsto (F · x) l (𝓝 (f x))) : TendstoUniformlyOn F f l s :=
  tendstoUniformlyOn_of_lipschitzOnWith (hF.mono fun _ h => h.lipschitzOnWith) hs hpt

end TauCeti
