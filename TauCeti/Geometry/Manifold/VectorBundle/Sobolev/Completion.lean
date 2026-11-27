/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic
public import TauCeti.Analysis.Normed.Operator.RangeClosure
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Schwartz
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CutoffFrame
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# Sobolev spaces of sections of a vector bundle as completions of smooth sections

Let `M` be a manifold modelled on `ℝⁿ` and `E → M` a smooth complex vector bundle with model fibre
`V` and a basis `(b_k)` of `V`. A smooth section `u` of `E` is read in a chart `eᵢ` of the maximal
atlas, a trivialization `tᵢ` of `E` and a cutoff `ψᵢ` with compact support in the chart target
through its frame coefficients: the Schwartz functions

`ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ eᵢ⁻¹)`

on `ℝⁿ`, where `ρᵢ b_k*(tᵢ u)` is the cut-off frame coefficient `x ↦ ρᵢ(x) b_k*(tᵢ,ₓ (u x))`
(`Bundle.Trivialization.cutoffFrameCoeff`) for a smooth function `ρᵢ` supported in the base set of
`tᵢ`. When `ρᵢ = 1` on `eᵢ⁻¹(supp ψᵢ)` the reading does not depend on `ρᵢ`. For a real order `s`,
the **chart readings** of `u` are the tuple of these readings in the Hilbert sum `⨁ᵢₖ H^s(ℝⁿ)`
(`TauCeti.sectionChartReading`), whose norm is `(∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ eᵢ⁻¹)‖²_{H^s})^{1/2}`.

The **Sobolev space** `H^s(M; E)` of these data is the closure of the chart readings of all smooth
sections (`TauCeti.sectionChartSobolevSpace`), an instance of the closure of the range of a linear
map (`LinearMap.rangeClosure`): a closed subspace of `⨁ᵢₖ H^s(ℝⁿ)`, hence a Hilbert space, in which
the smooth sections are dense (`LinearMap.denseRange_toRangeClosure`).
When the readings `ψᵢ ∘ eᵢ` of the cutoffs on `M` add up to `1`, which forces `M` to be compact,
it is the completion of the smooth sections in Taylor's norm for the Sobolev spaces of sections
of a vector bundle over a compact manifold. This is the bundle version of the Sobolev space
`TauCeti.chartSobolevSpace` of functions, and the space on which operators between sections of
bundles, such as pseudodifferential operators, act once they satisfy an a priori estimate in the
chart-reading norms (`TauCeti.sectionChartSobolevExtension`).

* For `r ≤ s`, the inclusions `H^s(ℝⁿ) ⊆ H^r(ℝⁿ)` give the inclusion `H^s(M; E) ⊆ H^r(M; E)`
  (`TauCeti.sectionChartSobolevInclusion`), which restricts to the identity on smooth sections.
  It is injective (`TauCeti.sectionChartSobolevInclusion_injective`) with dense range
  (`LinearMap.denseRange_rangeClosureMap`), and does not increase norms
  (`TauCeti.norm_sectionChartSobolevInclusion_apply_le`).
* **Rellich's theorem.** For `r < s` this inclusion is compact
  (`TauCeti.isCompactOperator_sectionChartSobolevInclusion`): the component of index `(i, k)` of
  every chart reading is fixed by a Schwartz function equal to `1` on the support of `ψᵢ`
  (`TauCeti.smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`), so componentwise the
  inclusion is multiplication by that function, compact by the Euclidean Rellich theorem for a
  common compact support in a finite Hilbert sum
  (`BesselPotentialSpace.isCompactOperator_rangeClosureMap_piMap_inclusion`).
* **Extension of operators.** A linear map `P` from the smooth sections of `E` to those of a second
  bundle `F` extends to a continuous linear map `H^s(M; E) → H^q(M; F)` when it satisfies an a
  priori estimate `‖P u‖_{H^q} ≤ C ‖u‖_{H^s}` in the chart-reading norms
  (`LinearMap.rangeClosureExtension_toRangeClosure`); the extension is unique
  (`LinearMap.rangeClosureExtension_eq`), and extensions add and compose
  (`LinearMap.rangeClosureExtension_add`, `LinearMap.rangeClosureExtension_comp`).

Such data exist on every compact manifold
(`TauCeti.exists_sum_cutoffPullback_eq_one_and_baseSet_cutoff`). Up to isomorphism the space does
not depend on them (`TauCeti.sectionChartSobolevSpaceCongr`); this follows from the Sobolev
estimate for the identity, a pseudodifferential operator of order `0`, and is proved next to that
estimate.

## Main definitions

* `TauCeti.sectionChartReading`: the chart readings of a smooth section, in `⨁ᵢₖ H^s(ℝⁿ)`.
* `TauCeti.sectionChartSobolevSpace`: the closure of the chart readings of smooth sections.
* `TauCeti.toSectionChartSobolevSpace`: a smooth section as an element of `H^s(M; E)`.
* `TauCeti.sectionChartSobolevInclusion`: the inclusion `H^s(M; E) ⊆ H^r(M; E)` for `r ≤ s`.
* `TauCeti.sectionChartSobolevExtension`: the continuous extension `H^s(M; E) → H^q(M; F)` of an
  operator on smooth sections satisfying an a priori estimate.

## Main results

* `TauCeti.toSectionChartSobolevSpace_injective`: for a chart partition, a smooth section is
  determined by its element of `H^s(M; E)`.
* `TauCeti.sectionChartSobolevInclusion_injective`: the inclusion `H^s(M; E) ⊆ H^r(M; E)` is
  injective.
* `TauCeti.isCompactOperator_sectionChartSobolevInclusion`: the Rellich theorem,
  `H^s(M; E) ⊆ H^r(M; E)` is compact for `r < s`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces of sections of vector bundles over compact manifolds, defined through charts,
  local frames and a partition of unity).
-/

public section

noncomputable section

open Bundle Set TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {ι κ : Type*} {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
  (t : ι → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t i)]
  (ρ : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
  (b : Module.Basis κ ℂ V)

/-- The **chart readings** of a smooth section `u` of `E` of order `s`: the tuple of its readings
`ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ eᵢ⁻¹)` in the charts `eᵢ`, trivializations `tᵢ` and basis vectors `b_k`, in
the Hilbert sum `⨁ᵢₖ H^s(ℝⁿ)`. -/
def sectionChartReading (s : ℝ) :
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] PiLp 2 fun _ : ι × κ ↦ H^{s}(CoordinateSpace n) where
  toFun u := WithLp.toLp 2 fun ik ↦ SchwartzMap.toBesselPotentialSpaceCLM s 2
    ((e ik.1).cutoffPushforwardSchwartz (he ik.1) (ψ ik.1)
      ((t ik.1).cutoffFrameCoeff (ρ ik.1) (hρ ik.1) (b.coord ik.2).toContinuousLinearMap u))
  map_add' u v := by
    ext1 ik
    simp
  map_smul' c u := by
    ext1 ik
    simp

@[simp]
theorem sectionChartReading_apply (s : ℝ) (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (ik : ι × κ) :
    sectionChartReading he ψ t ρ hρ b s u ik = SchwartzMap.toBesselPotentialSpaceCLM s 2
      ((e ik.1).cutoffPushforwardSchwartz (he ik.1) (ψ ik.1)
        ((t ik.1).cutoffFrameCoeff (ρ ik.1) (hρ ik.1) (b.coord ik.2).toContinuousLinearMap u)) :=
  (rfl)

/-- The componentwise inclusion `⨁ᵢₖ H^s(ℝⁿ) ⊆ ⨁ᵢₖ H^r(ℝⁿ)` sends the chart readings of order `s`
to those of order `r`. -/
theorem piMap_inclusion_sectionChartReading {r s : ℝ} (h : r ≤ s)
    (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    PiLp.piMap 2 (fun _ ↦ BesselPotentialSpace.inclusion h)
        (sectionChartReading he ψ t ρ hρ b s u) =
      sectionChartReading he ψ t ρ hρ b r u := by
  ext1 ik
  simp

variable [Fintype ι] [Fintype κ]

/-- The **Sobolev space** `H^s(M; E)` of the charts `eᵢ`, cutoffs `ψᵢ`, trivializations `tᵢ` and the
basis `(b_k)`: the closure in the Hilbert sum `⨁ᵢₖ H^s(ℝⁿ)` of the chart readings of the smooth
sections of `E` (`LinearMap.rangeClosure`). It is closed, hence a Hilbert space. -/
abbrev sectionChartSobolevSpace (s : ℝ) :
    Submodule ℂ (PiLp 2 fun _ : ι × κ ↦ H^{s}(CoordinateSpace n)) :=
  (sectionChartReading he ψ t ρ hρ b s).rangeClosure

/-- A smooth section `u` of `E` as an element of the Sobolev space `H^s(M; E)`: its chart
readings. Smooth sections are dense in `H^s(M; E)` (`LinearMap.denseRange_toRangeClosure`). -/
abbrev toSectionChartSobolevSpace (s : ℝ) :
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] sectionChartSobolevSpace he ψ t ρ hρ b s :=
  (sectionChartReading he ψ t ρ hρ b s).toRangeClosure

/-- **A smooth section is determined by its element of `H^s(M; E)`** when the readings `ψᵢ ∘ eᵢ` of
the cutoffs on `M`, extended by `0`, add up to `1` and each `ρᵢ` is `1` on `eᵢ⁻¹(supp ψᵢ)`: its
readings `ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ eᵢ⁻¹)` are then its components, and they determine `u`. -/
theorem toSectionChartSobolevSpace_injective [T2Space M]
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e i).symm y) = 1) (s : ℝ) :
    Function.Injective (toSectionChartSobolevSpace he ψ t ρ hρ b s) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦
    eq_zero_of_forall_cutoffPushforwardSchwartz_cutoffFrameCoeff_eq_zero he ψ hψ t ρ hρ hρψ b
      fun i k ↦ SchwartzMap.toBesselPotentialSpaceCLM_injective s 2 ?_
  simpa using congrArg (fun z : sectionChartSobolevSpace he ψ t ρ hρ b s ↦
    (z : PiLp 2 fun _ : ι × κ ↦ H^{s}(CoordinateSpace n)) (i, k)) hu

/-! ### The inclusions between the Sobolev spaces -/

variable {r s : ℝ}

/-- The inclusion `H^s(M; E) ⊆ H^r(M; E)` for `r ≤ s`: the inclusion `H^s(ℝⁿ) ⊆ H^r(ℝⁿ)`
(`BesselPotentialSpace.inclusion`) in every component, which sends the chart readings of order
`s` of a smooth section to those of order `r` (`TauCeti.piMap_inclusion_sectionChartReading`). -/
abbrev sectionChartSobolevInclusion (h : r ≤ s) :
    sectionChartSobolevSpace he ψ t ρ hρ b s →L[ℂ] sectionChartSobolevSpace he ψ t ρ hρ b r :=
  (sectionChartReading he ψ t ρ hρ b s).rangeClosureMap (sectionChartReading he ψ t ρ hρ b r)
    (PiLp.piMap 2 fun _ ↦ BesselPotentialSpace.inclusion h)
    (piMap_inclusion_sectionChartReading he ψ t ρ hρ b h)

/-- The inclusion `H^s(M; E) ⊆ H^r(M; E)` does not increase norms. -/
theorem norm_sectionChartSobolevInclusion_apply_le (h : r ≤ s)
    (x : sectionChartSobolevSpace he ψ t ρ hρ b s) :
    ‖sectionChartSobolevInclusion he ψ t ρ hρ b h x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (sectionChartSobolevInclusion he ψ t ρ hρ b h).le_of_opNorm_le
    ((LinearMap.norm_rangeClosureMap_le _).trans
      (PiLp.norm_piMap_le zero_le_one fun _ ↦ BesselPotentialSpace.norm_inclusion_le h)) x

/-- The inclusion `H^s(M; E) ⊆ H^r(M; E)` is injective. -/
theorem sectionChartSobolevInclusion_injective (h : r ≤ s) :
    Function.Injective (sectionChartSobolevInclusion he ψ t ρ hρ b h) :=
  LinearMap.rangeClosureMap_injective _
    (PiLp.piMap_injective 2 fun _ ↦ BesselPotentialSpace.inclusion_injective h)

/-- The inclusion `H^s(M; E) ⊆ H^s(M; E)` is the identity. -/
@[simp]
theorem sectionChartSobolevInclusion_self :
    sectionChartSobolevInclusion he ψ t ρ hρ b (le_refl s) = 1 :=
  LinearMap.rangeClosure_ext _ fun u ↦ by simp

/-- The inclusions `H^s(M; E) ⊆ H^r(M; E) ⊆ H^q(M; E)` compose to the inclusion
`H^s(M; E) ⊆ H^q(M; E)`. -/
@[simp]
theorem sectionChartSobolevInclusion_comp_sectionChartSobolevInclusion {q : ℝ} (h₁ : r ≤ s)
    (h₂ : q ≤ r) :
    sectionChartSobolevInclusion he ψ t ρ hρ b h₂ ∘L sectionChartSobolevInclusion he ψ t ρ hρ b h₁ =
      sectionChartSobolevInclusion he ψ t ρ hρ b (h₂.trans h₁) :=
  LinearMap.rangeClosure_ext _ fun u ↦ by simp

/-! ### The Rellich theorem -/

/-- **The Rellich theorem.** For real orders `r < s`, the inclusion `H^s(M; E) ⊆ H^r(M; E)` is a
compact operator: the component of index `(i, k)` of every chart reading is fixed by a Schwartz
function equal to `1` on the support of `ψᵢ`. -/
theorem isCompactOperator_sectionChartSobolevInclusion (h : r < s) :
    IsCompactOperator (sectionChartSobolevInclusion he ψ t ρ hρ b h.le) := by
  -- A Schwartz function `θ` equal to `1` on the finitely many compact supports of the `ψᵢ`.
  obtain ⟨θ, -, -, hθ1⟩ := (isCompact_iUnion fun i ↦
    (ψ i).hasCompactSupport.isCompact).exists_schwartzMap_cutoff isOpen_univ (subset_univ _)
  exact BesselPotentialSpace.isCompactOperator_rangeClosureMap_piMap_inclusion θ h
    (fun u ik ↦ smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz (he ik.1)
      (fun y hy ↦ hθ1.self_of_nhdsSet y (mem_iUnion_of_mem ik.1 hy)) s _)
    (piMap_inclusion_sectionChartReading he ψ t ρ hρ b h.le)

/-! ### Extending operators by continuity -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {ι' κ' : Type*} [Fintype ι'] [Fintype κ'] {e' : ι' → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he' : ∀ j, e' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (φ : ∀ j, 𝓓(⟨(e' j).target, (e' j).open_target⟩, ℝ))
  (t' : ι' → Trivialization W (π W F)) [∀ j, MemTrivializationAtlas (t' j)]
  (χ : ι' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet)
  (b' : Module.Basis κ' ℂ W)

/-- The **extension of an operator** `P` from the smooth sections of `E` to those of `F` to a
continuous linear map `H^s(M; E) → H^q(M; F)`, from the Sobolev space of the data `eᵢ`, `ψᵢ`,
`tᵢ`, `ρᵢ`, `(b_k)` to that of the data `e'ⱼ`, `φⱼ`, `t'ⱼ`, `χⱼ`, `(b'ₗ)`, by continuity from the
dense smooth sections (`LinearMap.rangeClosureExtension`). It extends `P` exactly when `P`
satisfies an a priori estimate `‖P u‖_{H^q} ≤ C ‖u‖_{H^s}` in the chart-reading norms
(`LinearMap.rangeClosureExtension_toRangeClosure`), and it is then the unique continuous extension
(`LinearMap.rangeClosureExtension_eq`); extensions add and compose. -/
abbrev sectionChartSobolevExtension
    (P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯)
    (s q : ℝ) :
    sectionChartSobolevSpace he ψ t ρ hρ b s →L[ℂ] sectionChartSobolevSpace he' φ t' χ hχ b' q :=
  (sectionChartReading he ψ t ρ hρ b s).rangeClosureExtension
    (sectionChartReading he' φ t' χ hχ b' q) P

end TauCeti
