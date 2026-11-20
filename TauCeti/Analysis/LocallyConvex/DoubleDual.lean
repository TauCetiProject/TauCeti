/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.Barrelled
public import TauCeti.Analysis.LocallyConvex.Bipolar
public import TauCeti.Analysis.LocallyConvex.Separation

/-!
# Canonical evaluation into the strong bidual of a locally convex space

Every topological vector space `E` over a normed field `𝕜` admits the canonical linear evaluation
`ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)`, sending a
vector `x` to `f ↦ f x`. Unlike the normed setting, this map is neither automatically continuous
nor automatically isometric, because the strong dual carries the topology of uniform convergence on
von Neumann bounded subsets rather than a single operator norm.

Over `ℝ` or `ℂ` (`RCLike 𝕜`), without any barrelledness, completeness, or separation assumption,
canonical evaluation on a locally convex space is inverse-continuous at the origin
(`TauCeti.comap_applyₗ_le_nhds_zero`): the polar `U°` of a closed absolutely convex neighborhood
`U` of `0` is von Neumann bounded in `StrongDual 𝕜 E` (`StrongDual.isVonNBounded_polar`), and
functionals bounded by `1` on `U°` pull back under evaluation to the bipolar `U°° = U`
(`AbsConvex.bipolar_eq_closure`). More generally, any map `ev : E → StrongDual 𝕜 G` that recovers
canonical evaluation along a continuous linear map `p : StrongDual 𝕜 E →L[𝕜] G`,
`ev x (p φ) = φ x`, factors `applyₗ` through the continuous transpose `precomp 𝕜 p` and hence
satisfies `comap ev (𝓝 0) ≤ 𝓝 0` (`TauCeti.comap_le_nhds_zero_of_forall_apply_eq`). By
`IsTopologicalAddGroup.isInducing_iff_nhds_zero`, a continuous additive homomorphism with this
property is inducing (`TauCeti.isInducing_of_forall_apply_eq_of_continuous`), a topological
embedding when `E` is `T₁` (`TauCeti.isEmbedding_of_forall_apply_eq_of_continuous`), and — when
`ev` is linear and surjective — a topological linear isomorphism `E ≃L[𝕜] StrongDual 𝕜 G`
(`TauCeti.strongDualEquivOfForallApplyEq`). Taking `p = .id 𝕜 _` gives the strong-bidual cases
`TauCeti.isInducing_applyₗ_of_continuous`, `TauCeti.isEmbedding_applyₗ_of_continuous`, and
`TauCeti.strongBidualEquivOfContinuousOfSurjective`.

On a barrelled space `E`, every von Neumann bounded set of continuous semilinear operators into a
polynormable space is equicontinuous (`Bornology.IsVonNBounded.equicontinuous`). Hence
`ContinuousLinearMap.applyₗ` is continuous (`TauCeti.continuous_applyₗ`), bundling canonical
evaluation into `TauCeti.strongEval 𝕜 E : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` and upgrading
surjectivity on a barrelled `T₁` locally convex space directly to
`TauCeti.strongBidualEquivOfSurjective`.

Finally, canonical evaluation intertwines every continuous linear map `u : E →L[𝕜] F` with its
double strong transpose `precomp G (precomp G u)`
(`ContinuousLinearMap.applyₗ_comp_precomp`, `ContinuousLinearMap.precomp_precomp_comp_applyₗ`),
recovering `u` when both spaces carry canonical bidual isomorphisms
(`ContinuousLinearMap.symm_comp_precomp_precomp_comp_of_forall_apply_eq`). When
`e : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` agrees with canonical evaluation,
`e.arrowCongr (.refl 𝕜 𝕜)` — whose inverse sends `Ξ` to `Ξ ∘ e`, the strong transpose of `e` —
agrees with canonical evaluation on `StrongDual 𝕜 E`
(`ContinuousLinearEquiv.toLinearMap_arrowCongr_refl_of_forall_apply_eq`), showing that the strong
dual of a reflexive space is canonically reflexive.

## Main declarations

* `TauCeti.comap_applyₗ_le_nhds_zero`, `TauCeti.comap_le_nhds_zero_of_forall_apply_eq`: inverse
  continuity at `0` of canonical strong-bidual evaluation and of general evaluation maps over `ℝ`
  or `ℂ`.
* `TauCeti.isInducing_of_forall_apply_eq_of_continuous`,
  `TauCeti.strongDualEquivOfForallApplyEq`: inducing property and `E ≃L[𝕜] StrongDual 𝕜 G`
  constructor for continuous evaluation maps.
* `TauCeti.continuous_applyₗ`, `TauCeti.strongEval`: continuity of evaluation on a barrelled space
  `E` into `(E →SL[σ₁₂] F) →L[𝕜₂] F` for polynormable `F`, and the bundled strong-bidual map.
* `TauCeti.strongBidualEquivOfContinuousOfSurjective`, `TauCeti.strongBidualEquivOfSurjective`:
  topological linear isomorphisms `E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)` from surjectivity of
  evaluation.
* `ContinuousLinearMap.applyₗ_comp_precomp`, `ContinuousLinearMap.precomp_precomp_comp_applyₗ`:
  naturality of canonical evaluation with respect to the double strong transpose.
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

namespace TauCeti

section Injectivity

/-- Any map `ev : E → H` into a family of `𝕜`-valued functions on `G` that recovers every
`φ : StrongDual 𝕜 E` along some map `p : StrongDual 𝕜 E → G` is injective when continuous
functionals separate points of `E`. -/
theorem injective_of_forall_apply_eq {𝕜 E G H : Type*} [Ring 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [SeparatingDual 𝕜 E] [FunLike H G 𝕜]
    {ev : E → H} {p : StrongDual 𝕜 E → G}
    (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x) :
    Function.Injective ev := fun x y hxy ↦
  (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun φ ↦ by
    rw [← hev x φ, ← hev y φ, hxy]

end Injectivity

section InverseContinuity

variable {𝕜 E G F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [FunLike F E (StrongDual 𝕜 G)] [AddMonoidHomClass F E (StrongDual 𝕜 G)]

variable (𝕜) in
/-- In any locally convex space over `ℝ` or `ℂ`, the pullback of `𝓝 0` along canonical evaluation
into the strong bidual is finer than or equal to `𝓝 (0 : E)`. -/
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

/-- For any map `ev : E → StrongDual 𝕜 G` from a locally convex space over `ℝ` or `ℂ` that
recovers canonical evaluation along a continuous linear map `p : StrongDual 𝕜 E →L[𝕜] G`, the
pullback of `𝓝 0` along `ev` is finer than or equal to `𝓝 (0 : E)`. -/
theorem comap_le_nhds_zero_of_forall_apply_eq {ev : E → StrongDual 𝕜 G}
    {p : StrongDual 𝕜 E →L[𝕜] G} (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x) :
    Filter.comap ev (𝓝 0) ≤ 𝓝 (0 : E) := by
  have hcomp : ContinuousLinearMap.precomp 𝕜 p ∘ ev =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) := by
    ext x φ
    simp [hev]
  calc Filter.comap ev (𝓝 0)
      ≤ Filter.comap ev (Filter.comap (ContinuousLinearMap.precomp 𝕜 p) (𝓝 0)) :=
        Filter.comap_mono
          ((ContinuousLinearMap.precomp 𝕜 p).continuous.tendsto' 0 0 (map_zero _)).le_comap
    _ = Filter.comap (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜)) (𝓝 0) := by
        rw [Filter.comap_comap, hcomp]
    _ ≤ 𝓝 (0 : E) := comap_applyₗ_le_nhds_zero 𝕜

/-- Any continuous additive homomorphism `ev` from a locally convex space over `ℝ` or `ℂ` into
`StrongDual 𝕜 G` that recovers canonical evaluation along a continuous linear map
`p : StrongDual 𝕜 E →L[𝕜] G` is inducing. -/
theorem isInducing_of_forall_apply_eq_of_continuous {ev : F}
    {p : StrongDual 𝕜 E →L[𝕜] G} (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x)
    (hcont : Continuous ev) :
    IsInducing ev :=
  IsTopologicalAddGroup.isInducing_iff_nhds_zero.2 <|
    le_antisymm (by simpa using (hcont.tendsto 0).le_comap)
      (comap_le_nhds_zero_of_forall_apply_eq hev)

/-- Any continuous additive homomorphism `ev` from a `T₁` locally convex space over `ℝ` or `ℂ` into
`StrongDual 𝕜 G` that recovers canonical evaluation along a continuous linear map
`p : StrongDual 𝕜 E →L[𝕜] G` is a topological embedding. -/
theorem isEmbedding_of_forall_apply_eq_of_continuous [T1Space E] {ev : F}
    {p : StrongDual 𝕜 E →L[𝕜] G} (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x)
    (hcont : Continuous ev) :
    IsEmbedding ev :=
  ⟨isInducing_of_forall_apply_eq_of_continuous hev hcont, injective_of_forall_apply_eq hev⟩

/-- On a `T₁` locally convex space over `ℝ` or `ℂ`, any continuous surjective linear map
`ev : E →ₗ[𝕜] StrongDual 𝕜 G` that recovers canonical evaluation along a continuous linear map
`p : StrongDual 𝕜 E →L[𝕜] G` upgrades to a topological linear isomorphism
`E ≃L[𝕜] StrongDual 𝕜 G`. -/
def strongDualEquivOfForallApplyEq [T1Space E] {ev : E →ₗ[𝕜] StrongDual 𝕜 G}
    {p : StrongDual 𝕜 E →L[𝕜] G} (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x)
    (hcont : Continuous ev) (hsurj : Function.Surjective ev) :
    E ≃L[𝕜] StrongDual 𝕜 G :=
  ContinuousLinearEquiv.ofIsHomeomorph
    (LinearEquiv.ofBijective ev ⟨injective_of_forall_apply_eq hev, hsurj⟩)
    (isHomeomorph_iff_isEmbedding_surjective.2
      ⟨isEmbedding_of_forall_apply_eq_of_continuous hev hcont, hsurj⟩)

@[simp]
theorem coe_strongDualEquivOfForallApplyEq [T1Space E] {ev : E →ₗ[𝕜] StrongDual 𝕜 G}
    {p : StrongDual 𝕜 E →L[𝕜] G} (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x)
    (hcont : Continuous ev) (hsurj : Function.Surjective ev) :
    ⇑(strongDualEquivOfForallApplyEq hev hcont hsurj) = ev :=
  (rfl)

@[simp]
theorem toLinearMap_strongDualEquivOfForallApplyEq [T1Space E] {ev : E →ₗ[𝕜] StrongDual 𝕜 G}
    {p : StrongDual 𝕜 E →L[𝕜] G} (hev : ∀ x (φ : StrongDual 𝕜 E), ev x (p φ) = φ x)
    (hcont : Continuous ev) (hsurj : Function.Surjective ev) :
    (strongDualEquivOfForallApplyEq hev hcont hsurj).toLinearMap = ev :=
  (rfl)

/-- If canonical evaluation from a locally convex space over `ℝ` or `ℂ` into its strong bidual is
continuous, then it is inducing. -/
theorem isInducing_applyₗ_of_continuous
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    IsInducing (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  isInducing_of_forall_apply_eq_of_continuous
    (ev := (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)))
    (p := .id 𝕜 _) (fun _ _ ↦ rfl) hcont

/-- If canonical evaluation from a `T₁` locally convex space over `ℝ` or `ℂ` into its strong
bidual is continuous, then it is a topological embedding. -/
theorem isEmbedding_applyₗ_of_continuous [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    IsEmbedding (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  isEmbedding_of_forall_apply_eq_of_continuous
    (ev := (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)))
    (p := .id 𝕜 _) (fun _ _ ↦ rfl) hcont

/-- On a `T₁` locally convex space over `ℝ` or `ℂ`, if canonical evaluation into the strong bidual
is continuous and surjective, it is a topological linear isomorphism. -/
def strongBidualEquivOfContinuousOfSurjective [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  strongDualEquivOfForallApplyEq (p := .id 𝕜 _) (fun _ _ ↦ rfl) hcont hsurj

@[simp]
theorem strongBidualEquivOfContinuousOfSurjective_apply_apply [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (x : E) (f : StrongDual 𝕜 E) :
    strongBidualEquivOfContinuousOfSurjective hcont hsurj x f = f x :=
  (rfl)

@[simp]
theorem toLinearMap_strongBidualEquivOfContinuousOfSurjective [T1Space E]
    (hcont : Continuous (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    (strongBidualEquivOfContinuousOfSurjective hcont hsurj).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  (rfl)

end InverseContinuity

section Barrelled

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [PolynormableSpace 𝕜₂ F]

/-- On a barrelled space, the evaluation map `x ↦ (f ↦ f x)` into `(E →SL[σ₁₂] F) →L[𝕜₂] F` is
continuous when `F` is polynormable. The isometric ring homomorphism `σ₁₂` makes `𝕜₂`
nontrivially normed, so no such assumption is needed on `𝕜₂`. -/
theorem continuous_applyₗ : Continuous (ContinuousLinearMap.applyₗ F σ₁₂ :
    E → (E →SL[σ₁₂] F) →L[𝕜₂] F) := by
  let _ : NontriviallyNormedField 𝕜₂ :=
    { ‹NormedField 𝕜₂› with
      non_trivial :=
        let ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := 𝕜₁)
        ⟨σ₁₂ c, by rwa [RingHomIsometric.norm_map]⟩ }
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
def strongBidualEquivOfSurjective [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  strongBidualEquivOfContinuousOfSurjective (strongEval 𝕜 E).continuous hsurj

@[simp]
theorem strongBidualEquivOfSurjective_apply_apply [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E)))
    (x : E) (f : StrongDual 𝕜 E) :
    strongBidualEquivOfSurjective hsurj x f = f x :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_strongBidualEquivOfSurjective [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    (strongBidualEquivOfSurjective hsurj).toContinuousLinearMap = strongEval 𝕜 E :=
  (rfl)

@[simp]
theorem toLinearMap_strongBidualEquivOfSurjective [T1Space E]
    (hsurj : Function.Surjective (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :
      E → StrongDual 𝕜 (StrongDual 𝕜 E))) :
    (strongBidualEquivOfSurjective hsurj).toLinearMap =
      ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) :=
  (rfl)

end BarrelledRCLike

end TauCeti

namespace ContinuousLinearMap

section ApplyLinear

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- **Naturality of canonical evaluation.** Composing canonical evaluation at `x` with
`precomp G u` gives canonical evaluation at `u x`. Together with `precomp_apply`, this lets
`simp` reduce `precomp G (precomp G u) (applyₗ G (RingHom.id 𝕜) x)` to
`applyₗ G (RingHom.id 𝕜) (u x)`. -/
@[simp]
theorem applyₗ_comp_precomp (u : E →L[𝕜] F) (x : E) :
    (applyₗ G (RingHom.id 𝕜) x).comp (precomp G u) = applyₗ G (RingHom.id 𝕜) (u x) := by
  ext ψ
  simp

/-- Linear-map form of the naturality of canonical evaluation under `precomp G (precomp G u)`. -/
theorem precomp_precomp_comp_applyₗ (u : E →L[𝕜] F) :
    (precomp G (precomp G u)).toLinearMap.comp (applyₗ G (RingHom.id 𝕜)) =
      (applyₗ G (RingHom.id 𝕜)).comp u.toLinearMap := by
  ext x ψ
  simp

end ApplyLinear

section EvaluationMaps

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- Any two continuous linear maps `E → (E →L[𝕜] G) →L[𝕜] G` and `F → (F →L[𝕜] G) →L[𝕜] G` that
agree pointwise with canonical evaluation intertwine `u : E →L[𝕜] F` with its double transpose
`precomp G (precomp G u)`; for `G = 𝕜` these are maps into the strong biduals. -/
theorem precomp_precomp_comp_of_forall_apply_eq (u : E →L[𝕜] F)
    {e₁ : E →L[𝕜] (E →L[𝕜] G) →L[𝕜] G} {e₂ : F →L[𝕜] (F →L[𝕜] G) →L[𝕜] G}
    (he₁ : ∀ x (φ : E →L[𝕜] G), e₁ x φ = φ x)
    (he₂ : ∀ y (ψ : F →L[𝕜] G), e₂ y ψ = ψ y) :
    (precomp G (precomp G u)).comp e₁ = e₂.comp u := by
  ext x ψ
  simp [he₁, he₂]

/-- When `E` and `F` carry topological linear isomorphisms with `(E →L[𝕜] G) →L[𝕜] G` and
`(F →L[𝕜] G) →L[𝕜] G` (for `G = 𝕜`, their strong biduals) agreeing with canonical evaluation,
conjugating the double transpose `precomp G (precomp G u)` by these isomorphisms recovers `u`. -/
theorem symm_comp_precomp_precomp_comp_of_forall_apply_eq (u : E →L[𝕜] F)
    {e₁ : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G} {e₂ : F ≃L[𝕜] (F →L[𝕜] G) →L[𝕜] G}
    (he₁ : ∀ x (φ : E →L[𝕜] G), e₁ x φ = φ x)
    (he₂ : ∀ y (ψ : F →L[𝕜] G), e₂ y ψ = ψ y) :
    e₂.symm.toContinuousLinearMap.comp
      ((precomp G (precomp G u)).comp e₁.toContinuousLinearMap) = u := by
  ext x
  rw [comp_apply, comp_apply, ContinuousLinearEquiv.coe_coe, e₂.symm_apply_eq]
  ext ψ
  simp [he₁, he₂]

end EvaluationMaps

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E G : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- If `e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G` agrees pointwise with canonical evaluation, then
`e.arrowCongr (.refl 𝕜 G)` agrees pointwise with canonical evaluation on `E →L[𝕜] G`. For `G = 𝕜`,
`e` is a strong-bidual isomorphism and `e.arrowCongr (.refl 𝕜 𝕜)` is the inverse of its strong
transpose. -/
theorem arrowCongr_refl_apply_of_forall_apply_eq (e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G)
    (he : ∀ x (φ : E →L[𝕜] G), e x φ = φ x) (φ : E →L[𝕜] G) (Ψ : (E →L[𝕜] G) →L[𝕜] G) :
    e.arrowCongr (.refl 𝕜 G) φ Ψ = Ψ φ := by
  rw [arrowCongr_apply, refl_apply, ← he (e.symm Ψ) φ, e.apply_symm_apply]

/-- If `e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G` agrees pointwise with canonical evaluation, then the
underlying linear map of `e.arrowCongr (.refl 𝕜 G)` is canonical evaluation on `E →L[𝕜] G`; for
`G = 𝕜`, the inverse of the strong transpose of a canonical bidual isomorphism is the canonical
bidual evaluation map of `StrongDual 𝕜 E`. -/
theorem toLinearMap_arrowCongr_refl_of_forall_apply_eq [ContinuousSMul 𝕜 G]
    (e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G) (he : ∀ x (φ : E →L[𝕜] G), e x φ = φ x) :
    (e.arrowCongr (.refl 𝕜 G)).toLinearMap = ContinuousLinearMap.applyₗ G (RingHom.id 𝕜) := by
  ext φ Ψ
  exact e.arrowCongr_refl_apply_of_forall_apply_eq he φ Ψ

end ContinuousLinearEquiv
