/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Topology.ContinuousMap.Polynormable

/-!
# Extension scalars in the native section frame topology

The existing section module over a normed field extension acts continuously for the existing
frame topology. The native frame jet is linear over the extension field when the actual bundle
frames are linear over that field. Its induced topology is therefore polynormable over the
extension field as well as locally convex over the real numbers when the base field is real.
-/

public noncomputable section

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, Module 𝕜' (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [VectorBundle 𝕜' F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I]

/-- Actual extension-linear bundle frames commute with constant extension scalars on sections. -/
theorem frameCoordinates_smul_apply_ofNormedAlgebra
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet)
    (c : 𝕜') (s : Cₛ^n⟮I; F, V⟯) (x : U) :
    e.frameCoordinates hU (c • s) x = c • e.frameCoordinates hU s x := by
  rw [frameCoordinates_apply, frameCoordinates_apply]
  have hs : (c • s : Cₛ^n⟮I; F, V⟯) x = c • s x :=
    congrFun (ContMDiffSection.coe_smul_of_normedAlgebra c s) x
  rw [hs]
  exact (e.linear 𝕜' (hU x.2)).map_smul c (s x)

end Bundle.Trivialization

namespace ContMDiffSection

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, Module 𝕜' (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [VectorBundle 𝕜' F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The existing frame jet commutes with constant extension scalars, at every derivative order. -/
theorem frameJet_smul_ofNormedAlgebra (c : 𝕜') (s : Cₛ^n⟮I; F, V⟯) :
    frameJet (I := I) e U hU (c • s) = c • frameJet (I := I) e U hU s := by
  funext i x m
  rw [frameJet_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, frameJet_apply]
  apply ContinuousMap.ext
  intro z
  erw [ContinuousMap.smul_apply]
  erw [ContMDiffMap.chartIteratedFDeriv_self_target_apply,
    ContMDiffMap.chartIteratedFDeriv_self_target_apply]
  have hf : ((e i).frameCoordinates (hU i) (c • s) : U i → F) ∘
        (extChartAt I x).symm =
      c • (((e i).frameCoordinates (hU i) s : U i → F) ∘ (extChartAt I x).symm) := by
    funext y
    exact (e i).frameCoordinates_smul_apply_ofNormedAlgebra (hU i) c s
      ((extChartAt I x).symm y)
  rw [hf]
  exact iteratedFDerivWithin_const_smul_apply
    (((e i).frameCoordinates (hU i) s).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm x) |>.contDiffOn z z.2 |>.of_le m.2)
    (uniqueDiffOn_extChartAt_target x) z.2

/-- The existing frame jet, regarded as linear over the extension field. Its underlying map
and its compact-open jet codomain are unchanged. -/
def frameJetLinearMapOfNormedAlgebra : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜']
    ∀ (i : ι) (x : U i) (m : {m : ℕ // m ≤ n}),
      C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×(m : ℕ)]→L[𝕜] F) where
  toFun := frameJet (I := I) e U hU
  map_add' := (frameJet (I := I) e U hU).map_add
  map_smul' c s := frameJet_smul_ofNormedAlgebra e U hU c s

/-- The extension-linear view evaluates to the same native frame jet. -/
@[simp]
theorem frameJetLinearMapOfNormedAlgebra_apply (s : Cₛ^n⟮I; F, V⟯) :
    frameJetLinearMapOfNormedAlgebra (𝕜' := 𝕜') (I := I) e U hU s =
      frameJet (I := I) e U hU s := by
  rfl

/-- The existing frame topology is induced by extension-field seminorms. No compactness,
countability, finite-rank or completeness hypothesis is required. -/
theorem polynormableSpace_frameTopology_ofNormedAlgebra :
    let _ := frameTopology (I := I) (n := n) e U hU
    PolynormableSpace 𝕜' Cₛ^n⟮I; F, V⟯ := by
  rw [frameTopology_eq_induced_frameJet]
  exact PolynormableSpace.induced
    (frameJetLinearMapOfNormedAlgebra (𝕜' := 𝕜') (I := I) (n := n) e U hU)

/-- Constant extension-scalar multiplication is jointly continuous for the existing frame
topology, provided the actual frames are extension-linear. -/
theorem continuousSMul_frameTopology_ofNormedAlgebra :
    let _ := frameTopology (I := I) (n := n) e U hU
    ContinuousSMul 𝕜' Cₛ^n⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ : PolynormableSpace 𝕜' Cₛ^n⟮I; F, V⟯ :=
    polynormableSpace_frameTopology_ofNormedAlgebra (𝕜' := 𝕜') e U hU
  infer_instance

end ContMDiffSection
