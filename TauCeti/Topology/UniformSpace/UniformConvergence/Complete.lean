/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform limits of uniformly Cauchy families into complete spaces

A family of functions into a complete uniform space that is uniformly Cauchy on every set in a
collection `𝔖` along a nontrivial filter `l` converges uniformly on every `s ∈ 𝔖` to a common limit
function (`TauCeti.exists_forall_tendstoUniformlyOn_of_uniformCauchySeqOn`). Specializing to a
single set gives `UniformCauchySeqOn.exists_tendstoUniformlyOn`.
-/

public section

open Filter Set Topology

variable {ι α β : Type*} [UniformSpace β] {l : Filter ι} {F : ι → α → β}

namespace TauCeti

/-- A family of functions into a complete uniform space that is uniformly Cauchy on every set
`s ∈ 𝔖` along a nontrivial filter `l` converges uniformly on every `s ∈ 𝔖` to a common limit
function `f`. -/
theorem exists_forall_tendstoUniformlyOn_of_uniformCauchySeqOn [CompleteSpace β] [l.NeBot]
    {𝔖 : Set (Set α)} (hF : ∀ s ∈ 𝔖, UniformCauchySeqOn F l s) :
    ∃ f : α → β, ∀ s ∈ 𝔖, TendstoUniformlyOn F f l s := by
  classical
  obtain ⟨i₀, -⟩ := l.nonempty_of_mem univ_mem
  have hex : ∀ x ∈ ⋃₀ 𝔖, ∃ y : β, Tendsto (fun i ↦ F i x) l (𝓝 y) :=
    fun x ⟨s, hs, hx⟩ ↦ CompleteSpace.complete ((hF s hs).cauchy_map hx)
  let f : α → β := fun x ↦ if hx : x ∈ ⋃₀ 𝔖 then (hex x hx).choose else F i₀ x
  refine ⟨f, fun s hs ↦ (hF s hs).tendstoUniformlyOn_of_tendsto fun x hx ↦ ?_⟩
  have hxU : x ∈ ⋃₀ 𝔖 := ⟨s, hs, hx⟩
  simpa only [f, hxU, ↓reduceDIte] using (hex x hxU).choose_spec

end TauCeti

/-- A uniformly Cauchy family of functions on `s` into a complete uniform space along a nontrivial
filter `l` converges uniformly on `s` to some limit function `f`. -/
theorem UniformCauchySeqOn.exists_tendstoUniformlyOn [CompleteSpace β] [l.NeBot] {s : Set α}
    (hF : UniformCauchySeqOn F l s) :
    ∃ f : α → β, TendstoUniformlyOn F f l s := by
  obtain ⟨f, hf⟩ := TauCeti.exists_forall_tendstoUniformlyOn_of_uniformCauchySeqOn (𝔖 := {s})
    (by simpa using hF)
  exact ⟨f, hf s rfl⟩
