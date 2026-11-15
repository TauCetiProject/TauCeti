/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.StrongTopology
public import TauCeti.Analysis.LocallyConvex.Bipolar

/-!
# Canonical evaluation into the strong bidual of a locally convex space

Every topological vector space `E` over a normed field `𝕜` admits the canonical linear evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`, sending a
vector `x` to `f ↦ f x`. Unlike the normed setting, this map is neither automatically continuous
nor automatically isometric, because the strong dual carries the topology of uniform convergence on
von Neumann bounded subsets rather than a single operator norm.

Over `ℝ` or `ℂ` (`RCLike 𝕜`), local convexity for the canonical partial order on `𝕜` agrees with
real local convexity (`TauCeti.locallyConvexSpace_RCLike_iff`), and the geometric Hahn–Banach
theorem supplies `SeparatingDual 𝕜 E` for every `T₁` locally convex space. Without any
barrelledness, completeness, or separation assumption, canonical evaluation on a locally convex
space has continuous inverse on its image (`TauCeti.comap_applyₗ_le_nhds`): the polar `U°` of a
closed absolutely convex neighborhood `U` of `0` is von Neumann bounded in `StrongDual 𝕜 E`
(`StrongDual.isVonNBounded_polar`), and functionals bounded by `1` on `U°` pull back under
evaluation to the bipolar `U°° = U` (`AbsConvex.bipolar_eq_closure`). Consequently, whenever
canonical evaluation is continuous, it is inducing (`TauCeti.isInducing_applyₗ_of_continuous`), a
topological embedding when `E` is `T₁` (`TauCeti.isEmbedding_applyₗ_of_continuous`), and a
topological linear isomorphism `E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` as soon as it is surjective
(`TauCeti.strongBidualEquivOfSurjective`).

On a barrelled space `E`, every von Neumann bounded set of continuous semilinear operators into a
polynormable space is equicontinuous (`Bornology.IsVonNBounded.equicontinuous`) by the
Banach–Steinhaus theorem (`PolynormableSpace.banach_steinhaus`). Hence `ContinuousLinearMap.applyₗ`
is continuous (`TauCeti.continuous_applyₗ`), bundling canonical evaluation into
`TauCeti.strongEval 𝕜 E : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` and upgrading surjectivity on a
barrelled `T₁` locally convex space directly to `TauCeti.strongBidualEquivOfBarrelled`.

Finally, canonical evaluation intertwines every continuous linear map `u : E →L[𝕜] F` with its
double strong transpose `precomp 𝕜 (precomp 𝕜 u)`
(`ContinuousLinearMap.precomp_precomp_applyₗ_apply`), recovering `u` when both spaces carry
canonical bidual isomorphisms
(`ContinuousLinearMap.symm_comp_precomp_precomp_comp_of_forall_apply_eq`). When
`e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` agrees with canonical evaluation,
`e.arrowCongr (.refl 𝕜 𝕜)` — whose inverse sends `Ξ` to `Ξ ∘ e`, the strong transpose of `e` —
agrees with canonical evaluation on `StrongDual 𝕜 E`
(`ContinuousLinearEquiv.toLinearMap_arrowCongr_refl_of_forall_apply_eq`), showing that the strong
dual of a reflexive space is canonically reflexive.

## Main declarations

* `TauCeti.locallyConvexSpace_RCLike_iff`: local convexity over `𝕜` (`RCLike 𝕜`) agrees with local
  convexity over `ℝ`.
* `TauCeti.comap_applyₗ_le_nhds`: inverse continuity of canonical strong-bidual evaluation on any
  locally convex space over `ℝ` or `ℂ`.
* `Bornology.IsVonNBounded.equicontinuous`: von Neumann bounded families of operators out of a
  barrelled space into a polynormable space are equicontinuous.
* `TauCeti.continuous_applyₗ`, `TauCeti.strongEval`: continuity of evaluation into the space of
  operators on a barrelled space, and the bundled strong-bidual map.
* `TauCeti.strongBidualEquivOfSurjective`, `TauCeti.strongBidualEquivOfBarrelled`: topological
  linear isomorphisms `E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` from surjectivity of evaluation.
* `ContinuousLinearMap.precomp_precomp_applyₗ_apply`: naturality of canonical evaluation with
  respect to the double strong transpose.
* `ContinuousLinearEquiv.toLinearMap_arrowCongr_refl_of_forall_apply_eq`: the inverse of the strong
  transpose of a canonical bidual isomorphism is the canonical bidual evaluation of the strong dual.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter IV, §2, nos. 2–3, and §3, no. 2.
* H. H. Schaefer, *Topological Vector Spaces*, Chapter IV, §5.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Set Topology Uniformity
open scoped ComplexOrder

namespace Bornology

section Uniform

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [Module 𝕜₁ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜₁ E]
  [BarrelledSpace 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F] [UniformSpace F] [IsUniformAddGroup F] [PolynormableSpace 𝕜₂ F]

/-- Every von Neumann bounded set of continuous semilinear maps from a barrelled space into a
polynormable space is uniformly equicontinuous: evaluation at each point sends a bounded set of
operators to a bounded subset of the codomain, so the Banach–Steinhaus theorem applies. -/
protected theorem IsVonNBounded.uniformEquicontinuous {S : Set (E →SL[σ₁₂] F)}
    (hS : IsVonNBounded 𝕜₂ S) : UniformEquicontinuous fun f : S ↦ (f.1 : E → F) := by
  refine PolynormableSpace.banach_steinhaus (𝓕 := fun f : S ↦ f.1) fun x ↦ ?_
  refine (ContinuousLinearMap.isVonNBounded_image2_apply hS (isVonNBounded_singleton x)).subset ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨f.1, f.2, x, mem_singleton x, rfl⟩

end Uniform

section Topological

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F] [UniformSpace F] [IsUniformAddGroup F] [PolynormableSpace 𝕜₂ F]

/-- Every von Neumann bounded set of continuous semilinear maps from a barrelled topological
vector space into a uniformly topologized polynormable space is equicontinuous. -/
protected theorem IsVonNBounded.equicontinuous {S : Set (E →SL[σ₁₂] F)}
    (hS : IsVonNBounded 𝕜₂ S) : Equicontinuous fun f : S ↦ (f.1 : E → F) := by
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have _ : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact hS.uniformEquicontinuous.equicontinuous

end Topological

end Bornology

namespace TauCeti

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

/-- Over `ℝ` or `ℂ`, local convexity with respect to the canonical order on `𝕜` is equivalent to
local convexity over `ℝ`. -/
theorem locallyConvexSpace_RCLike_iff : LocallyConvexSpace 𝕜 E ↔ LocallyConvexSpace ℝ E := by
  simp_rw [locallyConvexSpace_iff, convex_RCLike_iff_convex_real]

/-- In a `T₁` locally convex topological vector space over `ℝ` or `ℂ`, continuous `𝕜`-linear
functionals separate points. -/
instance instSeparatingDualOfLocallyConvexSpace [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace ℝ E] [T1Space E] : SeparatingDual 𝕜 E :=
  ⟨fun x hx ↦
    RCLike.geometric_hahn_banach_point_point hx |>.imp fun _ hf hf' ↦ by simp [hf'] at hf⟩

end RCLike

section Injectivity

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousSMul 𝕜 E] [SeparatingDual 𝕜 E]

/-- When continuous functionals separate points of `E`, canonical evaluation into the strong bidual
is injective. -/
theorem applyₗ_id_injective :
    Function.Injective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  (injective_iff_map_eq_zero _).2 fun _ hx ↦
    SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun f ↦ congr($hx f)

end Injectivity

section InverseContinuity

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

variable (𝕜) in
/-- In any locally convex space over `ℝ` or `ℂ`, the pullback of `𝓝 0` along canonical evaluation
into the strong bidual is finer than or equal to `𝓝 (0 : E)`: the polar of a closed absolutely
convex `0`-neighborhood `U` is bounded in `StrongDual 𝕜 E`, and the strong-bidual closed unit ball
on `U°` pulls back to `U°° = U`. -/
theorem comap_applyₗ_le_nhds_zero :
    Filter.comap (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)) (𝓝 0) ≤ 𝓝 (0 : E) := by
  have : LocallyConvexSpace 𝕜 E := locallyConvexSpace_RCLike_iff.2 ‹_›
  intro W hW
  obtain ⟨U, ⟨hU, hUclosed, hUabs⟩, hUW⟩ := (nhds_hasBasis_absConvex_closed 𝕜 E).mem_iff.1 hW
  refine ⟨{Φ : StrongDual 𝕜 (StrongDual 𝕜 E) |
      MapsTo Φ (StrongDual.polar 𝕜 U) (Metric.closedBall (0 : 𝕜) 1)},
    ContinuousLinearMap.eventually_nhds_zero_mapsTo (StrongDual.isVonNBounded_polar hU)
      (Metric.closedBall_mem_nhds 0 one_pos), fun x hx ↦ hUW ?_⟩
  have hne : U.Nonempty := ⟨0, mem_of_mem_nhds hU⟩
  rw [← hUclosed.closure_eq, ← hUabs.bipolar_eq_closure hne]
  intro f hf
  simpa [Metric.mem_closedBall, dist_zero_right] using hx hf

variable (𝕜) in
/-- Canonical evaluation from a locally convex space over `ℝ` or `ℂ` into its strong bidual has
continuous inverse on its range: the pullback of the strong-bidual neighborhood filter at the
evaluation of `x` is finer than or equal to `𝓝 x`. -/
theorem comap_applyₗ_le_nhds (x : E) :
    Filter.comap (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))
        (𝓝 (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) x)) ≤ 𝓝 x := by
  let ev : E →ₗ[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)
  change comap ev (𝓝 (ev x)) ≤ 𝓝 x
  rw [← nhds_translation_sub x, ← nhds_translation_sub (ev x), comap_comap]
  have hcomp : ((· - ev x) ∘ ev) = (ev ∘ (· - x)) := funext fun z ↦ (map_sub ev z x).symm
  rw [hcomp, ← comap_comap]
  exact comap_mono (comap_applyₗ_le_nhds_zero 𝕜)

/-- If canonical evaluation from a locally convex space over `ℝ` or `ℂ` into its strong bidual is
continuous, then it is inducing. -/
theorem isInducing_applyₗ_of_continuous
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    IsInducing (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  isInducing_iff_nhds.2 fun x ↦
    le_antisymm (hcont.tendsto x).le_comap (comap_applyₗ_le_nhds 𝕜 x)

/-- If canonical evaluation from a `T₁` locally convex space over `ℝ` or `ℂ` into its strong
bidual is continuous, then it is a topological embedding. -/
theorem isEmbedding_applyₗ_of_continuous [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    IsEmbedding (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ⟨isInducing_applyₗ_of_continuous hcont, applyₗ_id_injective⟩

/-- On a `T₁` locally convex space over `ℝ` or `ℂ`, if canonical evaluation into the strong bidual
is continuous and surjective, it is a topological linear isomorphism. -/
def strongBidualEquivOfSurjective [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  let e := LinearEquiv.ofBijective
    (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    ⟨applyₗ_id_injective, hsurj⟩
  { toLinearEquiv := e
    continuous_toFun := hcont
    continuous_invFun := (isInducing_applyₗ_of_continuous hcont).continuous_iff.2 <|
      continuous_id.congr fun Φ ↦ (e.apply_symm_apply Φ).symm }

@[simp]
theorem strongBidualEquivOfSurjective_apply_apply [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (x : E) (f : StrongDual 𝕜 E) :
    strongBidualEquivOfSurjective hcont hsurj x f = f x :=
  (rfl)

@[simp]
theorem toLinearMap_strongBidualEquivOfSurjective [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    (strongBidualEquivOfSurjective hcont hsurj).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  (rfl)

end InverseContinuity

section Barrelled

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜₂ F] [PolynormableSpace 𝕜₂ F]

/-- On a barrelled space, the evaluation map `x ↦ (f ↦ f x)` into `(E →SL[σ₁₂] F) →L[𝕜₂] F` is
continuous when `F` is polynormable: every von Neumann bounded subset of `E →SL[σ₁₂] F` is
equicontinuous at `0`. -/
theorem continuous_applyₗ : Continuous (ContinuousLinearMap.applyₗ F σ₁₂ :
    E → (E →SL[σ₁₂] F) →L[𝕜₂] F) := by
  let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  refine continuous_of_continuousAt_zero (ContinuousLinearMap.applyₗ F σ₁₂).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, ContinuousLinearMap.nhds_zero_eq]
  simp only [tendsto_iInf, tendsto_principal]
  intro S hS V hV
  rw [nhds_eq_comap_uniformity] at hV
  obtain ⟨U, hU, hUV⟩ := hV
  filter_upwards [hS.equicontinuous 0 U hU] with x hx f hf
  apply hUV
  simpa using hx ⟨f, hf⟩

variable (𝕜₁ E) in
/-- Canonical evaluation of a barrelled space into its strong bidual, bundled as a continuous
linear map. -/
def strongEval : E →L[𝕜₁] StrongDual 𝕜₁ (StrongDual 𝕜₁ E) :=
  { ContinuousLinearMap.applyₗ 𝕜₁ (RingHom.id 𝕜₁) with
    cont := continuous_applyₗ }

@[simp]
theorem strongEval_apply_apply (x : E) (f : StrongDual 𝕜₁ E) :
    strongEval 𝕜₁ E x f = f x :=
  (rfl)

@[simp]
theorem toLinearMap_strongEval :
    (strongEval 𝕜₁ E).toLinearMap = ContinuousLinearMap.applyₗ 𝕜₁ (RingHom.id 𝕜₁) :=
  (rfl)

end Barrelled

section BarrelledRCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [BarrelledSpace 𝕜 E]

/-- Canonical evaluation from a barrelled locally convex space over `ℝ` or `ℂ` into its strong
bidual is inducing. -/
theorem isInducing_strongEval : IsInducing (strongEval 𝕜 E) :=
  isInducing_applyₗ_of_continuous (strongEval 𝕜 E).continuous

/-- Canonical evaluation from a barrelled `T₁` locally convex space over `ℝ` or `ℂ` into its
strong bidual is a topological embedding. -/
theorem isEmbedding_strongEval [T1Space E] : IsEmbedding (strongEval 𝕜 E) :=
  isEmbedding_applyₗ_of_continuous (strongEval 𝕜 E).continuous

/-- On a barrelled `T₁` locally convex space over `ℝ` or `ℂ`, surjectivity of canonical evaluation
into the strong bidual yields a topological linear isomorphism
`E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`. -/
def strongBidualEquivOfBarrelled [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  strongBidualEquivOfSurjective (strongEval 𝕜 E).continuous hsurj

@[simp]
theorem strongBidualEquivOfBarrelled_apply_apply [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (x : E) (f : StrongDual 𝕜 E) :
    strongBidualEquivOfBarrelled hsurj x f = f x :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_strongBidualEquivOfBarrelled [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    (strongBidualEquivOfBarrelled hsurj).toContinuousLinearMap = strongEval 𝕜 E :=
  (rfl)

@[simp]
theorem toLinearMap_strongBidualEquivOfBarrelled [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    (strongBidualEquivOfBarrelled hsurj).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  (rfl)

end BarrelledRCLike

end TauCeti

namespace ContinuousLinearMap

section ApplyLinear

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousSMul 𝕜 F]

/-- **Naturality of canonical strong-bidual evaluation.** Applying the double strong transpose
`precomp 𝕜 (precomp 𝕜 u)` of `u : E →L[𝕜] F` to the evaluation at `x` gives the evaluation at
`u x`. -/
theorem precomp_precomp_applyₗ_apply (u : E →L[𝕜] F) (x : E) :
    precomp 𝕜 (precomp 𝕜 u) (applyₗ 𝕜 (RingHom.id 𝕜) x) = applyₗ 𝕜 (RingHom.id 𝕜) (u x) := by
  ext ψ
  rfl

/-- Linear-map form of the naturality of canonical strong-bidual evaluation under the double
strong transpose. -/
theorem precomp_precomp_comp_applyₗ (u : E →L[𝕜] F) :
    (precomp 𝕜 (precomp 𝕜 u)).toLinearMap.comp (applyₗ 𝕜 (RingHom.id 𝕜)) =
      (applyₗ 𝕜 (RingHom.id 𝕜)).comp u.toLinearMap := by
  ext x ψ
  rfl

end ApplyLinear

section EvaluationMaps

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- Any two continuous linear maps into the strong biduals that agree pointwise with canonical
evaluation intertwine `u : E →L[𝕜] F` with its double strong transpose
`precomp 𝕜 (precomp 𝕜 u)`. -/
theorem precomp_precomp_comp_of_forall_apply_eq (u : E →L[𝕜] F)
    {e₁ : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)} {e₂ : F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)}
    (he₁ : ∀ x (φ : StrongDual 𝕜 E), e₁ x φ = φ x)
    (he₂ : ∀ y (ψ : StrongDual 𝕜 F), e₂ y ψ = ψ y) :
    (precomp 𝕜 (precomp 𝕜 u)).comp e₁ = e₂.comp u := by
  ext x ψ
  simp [he₁, he₂]

/-- When `E` and `F` carry topological linear isomorphisms with their strong biduals agreeing with
canonical evaluation, conjugating the double strong transpose `precomp 𝕜 (precomp 𝕜 u)` by these
isomorphisms recovers `u`. -/
theorem symm_comp_precomp_precomp_comp_of_forall_apply_eq (u : E →L[𝕜] F)
    {e₁ : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)} {e₂ : F ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)}
    (he₁ : ∀ x (φ : StrongDual 𝕜 E), e₁ x φ = φ x)
    (he₂ : ∀ y (ψ : StrongDual 𝕜 F), e₂ y ψ = ψ y) :
    e₂.symm.toContinuousLinearMap.comp
      ((precomp 𝕜 (precomp 𝕜 u)).comp e₁.toContinuousLinearMap) = u := by
  ext x
  rw [comp_apply, comp_apply, ContinuousLinearEquiv.coe_coe, e₂.symm_apply_eq]
  ext ψ
  simp [he₁, he₂]

end EvaluationMaps

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- If `e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` agrees pointwise with canonical evaluation,
then `e.arrowCongr (.refl 𝕜 𝕜)` — the inverse of the strong transpose of `e` — agrees pointwise
with canonical evaluation on `StrongDual 𝕜 E`. -/
theorem arrowCongr_refl_apply_of_forall_apply_eq (e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (he : ∀ x (φ : StrongDual 𝕜 E), e x φ = φ x) (φ : StrongDual 𝕜 E)
    (Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    e.arrowCongr (.refl 𝕜 𝕜) φ Ψ = Ψ φ := by
  rw [arrowCongr_apply, refl_apply, ← he (e.symm Ψ) φ, e.apply_symm_apply]

/-- If `e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` agrees pointwise with canonical evaluation,
then the inverse of the strong transpose of `e` is the canonical bidual evaluation map of
`StrongDual 𝕜 E`. -/
theorem toLinearMap_arrowCongr_refl_of_forall_apply_eq
    (e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (he : ∀ x (φ : StrongDual 𝕜 E), e x φ = φ x) :
    (e.arrowCongr (.refl 𝕜 𝕜)).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) := by
  ext φ Ψ
  exact e.arrowCongr_refl_apply_of_forall_apply_eq he φ Ψ

end ContinuousLinearEquiv
