/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Smooth fibre translation of the total space of a vector bundle

Translation by a section `s` of a vector bundle `V → B` is the self-map of the total space that
covers the identity of the base and sends `v ∈ V x` to `v + s x`. It is `C^n` as soon as the
section is `C^n` (`Bundle.contMDiff_totalSpace_mk_add_section`). In a trivialization it is an
affine map of the model fibre, so smoothness follows from Mathlib's characterization
`Bundle.contMDiffAt_totalSpace` of `C^n` maps into a total space. No `C^n` vector bundle
structure is needed: only the fibrewise linearity of the trivializations is used.

Fibrewise multiplication by a scalar is treated in `TauCeti.Geometry.Manifold.VectorBundle.Scalar`
(`ContMDiff.smul_totalSpace`).
-/

public section

open Bundle Filter
open scoped Manifold Topology

namespace Bundle

variable {𝕜 B F EB HB : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] {n : WithTop ℕ∞}

/-- Near `z₀`, the base point of a point of the total space lies in the base set of the preferred
trivialization at the base point of `z₀`. -/
private theorem eventually_proj_mem_baseSet (z₀ : TotalSpace F V) :
    ∀ᶠ z in 𝓝 z₀, z.proj ∈ (trivializationAt F V z₀.proj).baseSet :=
  (FiberBundle.continuous_proj F V).continuousAt.preimage_mem_nhds
    ((trivializationAt F V z₀.proj).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' z₀.proj))

/-- The fibre coordinate in the preferred trivialization at the base point of `z₀` is `C^n` near
`z₀`, as a function on the total space. -/
private theorem contMDiffAt_trivializationAt_snd (z₀ : TotalSpace F V) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
      (fun z : TotalSpace F V ↦ (trivializationAt F V z₀.proj z).2) z₀ :=
  (contMDiffAt_totalSpace.mp (contMDiffAt_id (I := IB.prod 𝓘(𝕜, F)) (n := n) (x := z₀))).2

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- **Fibre translation by a smooth section is smooth.** If `s` is a `C^n` section of a vector
bundle `V`, the self-map `v ↦ v + s x` of the total space, `v ∈ V x`, is `C^n`. -/
theorem contMDiff_totalSpace_mk_add_section {s : ∀ x, V x}
    (hs : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun x ↦ TotalSpace.mk' F x (s x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      fun z : TotalSpace F V ↦ TotalSpace.mk' F z.proj (z.2 + s z.proj) := by
  intro z₀
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_proj V, ?_⟩
  -- In the trivialization at `z₀`, the fibre coordinate is that of `z` plus that of `s`.
  have hsec := ((contMDiffAt_section z₀.proj).mp (hs z₀.proj)).comp z₀ (contMDiffAt_proj V)
  refine ((contMDiffAt_trivializationAt_snd z₀).add hsec).congr_of_eventuallyEq ?_
  filter_upwards [eventually_proj_mem_baseSet z₀] with z hz
  exact ((trivializationAt F V z₀.proj).linear 𝕜 hz).map_add z.2 (s z.proj)

end Bundle
