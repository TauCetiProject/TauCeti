/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
public import Mathlib.Topology.Compactness.CountablyCompact
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Reparametrization
public import TauCeti.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.ContinuousMap.UnparametrizedMap

/-!
# Unparametrized maps of the projective line

Let `𝕜` be a proper nontrivially normed field, such as `ℂ`, and `X` a metrizable space. The group
`PSL(2, 𝕜)` of Möbius transformations acts on the nonconstant continuous maps `u : OnePoint 𝕜 → X`
(`TauCeti.NonconstantMap (OnePoint 𝕜) X`, with the compact-open topology) by reparametrization,
`g • u = u ∘ (g⁻¹ • ·)`. This file shows that this action is **proper**, so that the spaces
`TauCeti.UnparametrizedMap PSL(2, 𝕜) (OnePoint 𝕜) X` of unparametrized maps and
`TauCeti.MarkedUnparametrizedMap PSL(2, 𝕜) (OnePoint 𝕜) X` of one-marked unparametrized maps are
Hausdorff. For `𝕜 = ℂ` these are the spaces of unparametrized and one-marked continuous spheres in
`X`; the moduli spaces of unparametrized pseudoholomorphic spheres are subsets of them. The action,
its continuity and the evaluation and forgetful maps on the orbit spaces hold for any group acting
on any space and are in `TauCeti.Topology.ContinuousMap.UnparametrizedMap`; properness is what is
specific to Möbius transformations.

For compact sets `U` and `V` of maps, the Möbius transformations `g` with `g • U ∩ V` nonempty form
a compact set. This rests on the sequential properness of the reparametrization action
(`OnePoint.exists_tendsto_psl_of_smul_eq`, from `OnePoint.exists_tendsto_psl_of_tendsto`): a
sequence `g n` with `g n • u n = v n`, `u n → u₀` and `v n → v₀` cannot escape to infinity, since
otherwise `v₀` would be constant, so a subsequence converges. The space of maps is metrizable, so
sequences suffice to detect compact sets in it, and `PSL(2, 𝕜)` is second countable, so sequential
compactness implies compactness there.

The action on pairs `g • (u, z) = (g • u, g • z)` of a map and a point of the projective line is
then proper too, because a proper action times a continuous one is proper
(`TauCeti.properSMul_prod`), so both orbit spaces are Hausdorff
(`t2Space_quotient_mulAction_of_properSMul`).

Freeness of the action on maps with an injective point is
`Matrix.ProjectiveSpecialLinearGroup.eq_of_forall_apply_smul_eq_apply_smul`. The properness proved
here passes to every invariant subspace with the subspace topology
(`Topology.IsEmbedding.properSMul`). The sequential statement
`OnePoint.exists_tendsto_psl_of_smul_eq` also applies to sequences converging in any finer
topology, such as a `C^∞` topology on pseudoholomorphic spheres.

## Main results

* `OnePoint.exists_tendsto_psl_of_smul_eq`: the sequential properness of the reparametrization
  action.
* `OnePoint.instProperSMulNonconstantMap`: the reparametrization action on nonconstant maps into
  a metrizable space is proper, so `TauCeti.UnparametrizedMap PSL(2, 𝕜) (OnePoint 𝕜) X` and
  `TauCeti.MarkedUnparametrizedMap PSL(2, 𝕜) (OnePoint 𝕜) X` are Hausdorff.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012 (the moduli spaces of unparametrized and
  marked spheres and their evaluation maps).
-/

public section

open Filter Function Topology TopologicalSpace
open TauCeti (NonconstantMap)
open scoped MatrixGroups Pointwise

namespace OnePoint

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜] [DecidableEq 𝕜]
  [TopologicalSpace X]

/-- **Sequential properness of the reparametrization action.** If `g n • u n = v n` with `u n → u₀`
and `v n → v₀`, then a subsequence of `g n` converges, to some `g₀` with `g₀ • u₀ = v₀`. -/
theorem exists_tendsto_psl_of_smul_eq [T2Space X] {u v : ℕ → NonconstantMap (OnePoint 𝕜) X}
    {u₀ v₀ : NonconstantMap (OnePoint 𝕜) X} {g : ℕ → PSL(2, 𝕜)} (hu : Tendsto u atTop (𝓝 u₀))
    (hv : Tendsto v atTop (𝓝 v₀)) (huv : ∀ n, g n • u n = v n) :
    ∃ (φ : ℕ → ℕ) (g₀ : PSL(2, 𝕜)), StrictMono φ ∧ Tendsto (g ∘ φ) atTop (𝓝 g₀) ∧
      g₀ • u₀ = v₀ := by
  -- Apply the properness theorem for maps to the inverses `(g n)⁻¹`, along which `u n`
  -- reparametrizes to `v n`.
  obtain ⟨φ, h₀, hφ, hconv, hh₀⟩ := exists_tendsto_psl_of_tendsto (g := fun n ↦ (g n)⁻¹)
    (u := fun n ↦ u n) (u₀ := u₀) (v₀ := v₀)
    (fun y ↦ (ContinuousEval.continuous_eval.tendsto (u₀, y)).comp
      ((hu.comp tendsto_fst).prodMk_nhds tendsto_snd))
    (fun z ↦ by
      simpa [comp_def, ← huv] using
        (ContinuousEval.continuous_eval.tendsto (v₀, z)).comp (hv.prodMk_nhds tendsto_const_nhds))
    (map_continuous v₀) v₀.exists_apply_ne
  refine ⟨φ, h₀⁻¹, hφ, by simpa [comp_def] using hconv.inv, NonconstantMap.ext fun z ↦ ?_⟩
  simp [hh₀]

/-- **The reparametrization action on nonconstant maps into a metrizable space is proper.** For
compact sets `U` and `V` of maps, the Möbius transformations `g` with `g • U ∩ V` nonempty form a
sequentially compact, hence compact, subset of the second countable group `PSL(2, 𝕜)`. -/
instance instProperSMulNonconstantMap [MetrizableSpace X] :
    ProperSMul PSL(2, 𝕜) (NonconstantMap (OnePoint 𝕜) X) := by
  refine MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty.2 fun {U V} hU hV ↦ ?_
  refine IsCountablyCompact.isCompact (IsSeqCompact.isCountablyCompact fun g hg ↦ ?_)
  -- Pick `u n ∈ U` with `g n • u n ∈ V`, then pass to a subsequence along which both converge.
  choose u hu hgu using fun n ↦ (hg n : ((g n • U) ∩ V).Nonempty)
  choose u' hu' hu'u using hu
  obtain ⟨u₀, hu₀, φ₁, hφ₁, hconv₁⟩ := hU.tendsto_subseq hu'
  obtain ⟨v₀, hv₀, φ₂, hφ₂, hconv₂⟩ := hV.tendsto_subseq fun n ↦ hgu (φ₁ n)
  obtain ⟨φ₃, g₀, hφ₃, hconv₃, hg₀⟩ := exists_tendsto_psl_of_smul_eq
    (g := g ∘ φ₁ ∘ φ₂) (u := u' ∘ φ₁ ∘ φ₂) (hconv₁.comp hφ₂.tendsto_atTop) hconv₂
    fun n ↦ hu'u (φ₁ (φ₂ n))
  exact ⟨g₀, ⟨v₀, ⟨u₀, hu₀, hg₀⟩, hv₀⟩, φ₁ ∘ φ₂ ∘ φ₃, hφ₁.comp (hφ₂.comp hφ₃), hconv₃⟩

end OnePoint
