/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local
public import TauCeti.Geometry.Manifold.LinearSlice
import TauCeti.Geometry.Manifold.Immersion
import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Stable and unstable manifolds of an adapted pseudo-gradient

Let `f` be a function on a compact boundaryless manifold `M` of dimension `n`, and `X` a
pseudo-gradient field adapted to `f`. For every critical point `x` of index `k`, the stable set
`W^s(x)` of the flow of `X` is flattened by charts of `M` onto a linear subspace of dimension
`n - k` (`TauCeti.IsAdaptedPseudoGradient.exists_stableSet_chart`). These slice charts make
`W^s(x)` a smooth manifold of dimension `n - k`, with the subspace topology and a smooth inclusion
into `M`.
When `f` is a Morse function, the same holds for the unstable set `W^u(x)`, in dimension `k`.

The slice charts come from the local picture: near `x`, `W^s(x)` is a coordinate subspace of a Morse
chart (`TauCeti.IsAdaptedPseudoGradient.exists_forall_mem_stableSet_iff`). A point `p` of `W^s(x)`
reaches that neighbourhood at some time `T`, and the Morse chart composed with the time-`T` map of
the flow is a slice chart at `p`. The unstable side follows by reversing time: `-X` is a
pseudo-gradient adapted to `-f` (`TauCeti.IsAdaptedPseudoGradient.neg`), and its flow is the
reversed flow.

## Main declarations

* `TauCeti.MorseChart.stableSubspace`: the coordinate subspace of the positive weights of a Morse
  chart, of dimension `n - k`.
* `TauCeti.IsAdaptedPseudoGradient.exists_stableSet_chart`: slice charts for `W^s(x)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_stableSet_isManifold` and
  `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_isManifold`: the manifold structures, of
  dimensions `n - k` and `k`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The coordinates of negative weight of a Morse chart, as a linear map. -/
noncomputable def negativeCoord : E →ₗ[ℝ] ({i // φ.weight i < 0} → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Subtype.val : {i // φ.weight i < 0} → Fin (Module.finrank ℝ E)) ∘ₗ
    (φ.coord : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The coordinates of negative weight of a vector. -/
@[simp]
theorem negativeCoord_apply (v : E) (i : {i // φ.weight i < 0}) :
    φ.negativeCoord v i = φ.coord v i := by
  simp [negativeCoord, LinearMap.funLeft_apply]

/-- The **stable subspace** of a Morse chart: the vectors whose coordinates of negative weight
vanish. -/
noncomputable def stableSubspace : Submodule ℝ E :=
  LinearMap.ker φ.negativeCoord

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A vector lies in the stable subspace when its coordinates of negative weight vanish. -/
@[simp]
theorem mem_stableSubspace {v : E} :
    v ∈ φ.stableSubspace ↔ ∀ i, φ.weight i < 0 → φ.coord v i = 0 := by
  rw [stableSubspace, LinearMap.mem_ker, negativeCoord, funext_iff]
  simp [LinearMap.funLeft_apply]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The stable subspace has dimension `n - k`, where `k` is the Morse index. -/
theorem finrank_stableSubspace_add_manifoldMorseIndex :
    Module.finrank ℝ φ.stableSubspace + manifoldMorseIndex 𝓘(ℝ, E) f x =
      Module.finrank ℝ E := by
  have hsurj : Surjective φ.negativeCoord :=
    (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ Subtype.val_injective).comp
      φ.coord.surjective
  have h := LinearMap.finrank_range_add_finrank_ker φ.negativeCoord
  have hr : Module.finrank ℝ (LinearMap.range φ.negativeCoord) =
      manifoldMorseIndex 𝓘(ℝ, E) f x := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
      ← φ.ncard_weight_neg, Set.ncard_eq_toFinset_card', Fintype.card_subtype,
      Set.toFinset_ofPred]
  rw [stableSubspace]
  omega

end MorseChart

namespace IsAdaptedPseudoGradient

variable [CompactSpace M] [T2Space M]

/-- **Slice charts for the stable manifold.** Let `φ` be a Morse chart at `x` in which `X` is
linear. Every point of `W^s(x)` lies in the source of a chart of the maximal atlas that flattens
`W^s(x)` onto the stable subspace of `φ`. -/
theorem exists_stableSet_chart (hX : IsAdaptedPseudoGradient f X)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {p : M} (hp : p ∈ hX.flow.stableSet x) :
    ∃ q : OpenPartialHomeomorph M E, p ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      ∀ z ∈ q.source, z ∈ hX.flow.stableSet x ↔ q z ∈ φ.stableSubspace := by
  obtain ⟨ε, hε, hloc⟩ := hX.exists_forall_mem_stableSet_iff φ hφ hf
  set D := φ.toChart.source ∩ φ.toChart ⁻¹' {v : E | ‖φ.coord v‖ < ε} with hDdef
  have hcoord : Continuous fun v : E ↦ φ.coord v := φ.coordL.continuous.congr φ.coordL_apply
  have hD : IsOpen D := φ.toChart.continuousOn.isOpen_inter_preimage φ.toChart.open_source
    (isOpen_lt (continuous_norm.comp hcoord) continuous_const)
  have hxD : x ∈ D := ⟨φ.mem_source, by simpa using hε⟩
  obtain ⟨T, hT⟩ := ((Flow.mem_stableSet.1 hp).eventually (hD.mem_nhds hxD)).exists
  refine ⟨(hX.flowDiffeomorph T).toHomeomorph.transOpenPartialHomeomorph (φ.toChart.restr D),
    ?_, ?_, ?_⟩
  · rw [Homeomorph.transOpenPartialHomeomorph_source, OpenPartialHomeomorph.restr_source,
      hD.interior_eq, mem_preimage, Diffeomorph.coe_toHomeomorph, flowDiffeomorph_apply]
    exact ⟨hT.1, hT⟩
  · exact mem_maximalAtlas_diffeomorph_transOpenPartialHomeomorph _
      (restr_mem_maximalAtlas _ φ.mem_maximalAtlas hD)
  · intro z hz
    simp only [Homeomorph.transOpenPartialHomeomorph_source, OpenPartialHomeomorph.restr_source,
      hD.interior_eq, mem_preimage, Diffeomorph.coe_toHomeomorph, flowDiffeomorph_apply] at hz
    have hzD : hX.flow T z ∈ D := hz.2
    simp only [Homeomorph.transOpenPartialHomeomorph_apply, OpenPartialHomeomorph.restr_apply,
      Diffeomorph.coe_toHomeomorph, comp_apply, flowDiffeomorph_apply, φ.mem_stableSubspace]
    rw [← hloc _ hzD.1 hzD.2, Flow.apply_mem_stableSet_iff]

/-- **The stable set is a manifold of dimension `n - k`.** For a critical point `x` of index
`k`, the stable set `W^s(x)` of the flow of an adapted pseudo-gradient carries a smooth
manifold structure modelled on a subspace of dimension `n - k`, with its subspace topology and a
smooth inclusion into `M`. -/
theorem exists_stableSet_isManifold (hX : IsAdaptedPseudoGradient f X)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E ∧
      ∃ C : ChartedSpace L (hX.flow.stableSet x), letI := C
        IsManifold 𝓘(ℝ, L) ∞ (hX.flow.stableSet x) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ (Subtype.val : hX.flow.stableSet x → M) := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  obtain ⟨N, hN⟩ := φ.stableSubspace.exists_isCompl
  refine ⟨φ.stableSubspace, φ.finrank_stableSubspace_add_manifoldMorseIndex, ?_⟩
  refine exists_isManifold_of_linearSubspaceCharts
    (Submodule.IsCompl.isTopCompl_of_isClosed hN
      φ.stableSubspace.closed_of_finiteDimensional N.closed_of_finiteDimensional)
    fun y ↦ ?_
  obtain ⟨q, hyq, hq, hmem⟩ := hX.exists_stableSet_chart hf φ hφ y.2
  exact ⟨q, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, hmem⟩

/-- **The unstable set is a manifold of dimension `k`.** For a critical point `x` of index
`k` of a Morse function, the unstable set `W^u(x)` of the flow of an adapted pseudo-gradient
carries a smooth manifold structure modelled on a subspace of dimension `k`, with its subspace
topology and a smooth inclusion into `M`. -/
theorem exists_unstableSet_isManifold (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E, Module.finrank ℝ L = manifoldMorseIndex 𝓘(ℝ, E) f x ∧
      ∃ C : ChartedSpace L (hX.flow.unstableSet x), letI := C
        IsManifold 𝓘(ℝ, L) ∞ (hX.flow.unstableSet x) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ (Subtype.val : hX.flow.unstableSet x → M) := by
  obtain ⟨L, hL, hman⟩ := (hX.neg hf).exists_stableSet_isManifold
    (hf.neg.contMDiff.mdifferentiable (by simp)) (mfderiv_neg_eq_zero_iff.2 hx)
  have hidx := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  rw [hX.unstableSet_eq_stableSet_neg hf]
  exact ⟨L, by omega, hman⟩

end IsAdaptedPseudoGradient

end TauCeti
