/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Core.Basic
public import TauCeti.Topology.VectorBundle.Core.Congr
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Smooth comparison for point-indexed cores and model-fibre congruences

This file lifts the total-space homeomorphisms `TauCeti.pointIndexedCoreHomeomorph` and
`VectorBundleCore.congrModelHomeomorph` of `TauCeti.Topology.VectorBundle.Core.Basic` and
`TauCeti.Topology.VectorBundle.Core.Congr` to `C^n` diffeomorphisms (and in particular
biholomorphisms for `𝕜 = ℂ` and `n = ∞`), without any smoothness or completeness hypothesis on the
underlying bundle or core:

* `TauCeti.pointIndexedCoreDiffeomorph`: `C^n` diffeomorphism between
  `(pointIndexedCore 𝕜 F E).TotalSpace` and `TotalSpace F E` over the identity of the base;
* `VectorBundleCore.congrModelDiffeomorph`: `C^n` diffeomorphism between
  `(Z.congrModel e).TotalSpace` and `Z.TotalSpace` over the identity of the base, acting by
  `e.symm` on each fibre.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B]

variable (𝕜 F) in
/-- Reconstruction of a point-indexed coordinate core is `C^n` diffeomorphic to the original
bundle over the identity of the base, fibrewise `𝕜`-linear via `pointIndexedCoreFiberEquiv`. No
smoothness hypothesis on `E` is required. -/
noncomputable def pointIndexedCoreDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (pointIndexedCore 𝕜 F E).TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, F)⟯
      TotalSpace F E where
  toFun p := ⟨p.proj, pointIndexedCoreFiberEquiv 𝕜 F E p.proj p.snd⟩
  invFun p := ⟨p.proj, (pointIndexedCoreFiberEquiv 𝕜 F E p.proj).symm p.snd⟩
  left_inv p := by dsimp only; rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by dsimp only; rw [ContinuousLinearEquiv.apply_symm_apply]
  contMDiff_toFun p₀ := by
    rw [Bundle.contMDiffAt_totalSpace_iff]
    refine ⟨(contMDiff_proj (pointIndexedCore 𝕜 F E).Fiber).contMDiffAt, ?_⟩
    have hp₀ := (pointIndexedCore 𝕜 F E).mem_source_at p₀.proj p₀.snd
    rw [pointIndexedCore_localTrivAt] at hp₀
    have hU := ((pointIndexedCore 𝕜 F E).localTriv p₀.proj).open_source.mem_nhds hp₀
    refine (p₀.contMDiffAt_trivializationAt_snd (IB := IB) (n := n)).congr_of_eventuallyEq ?_
    filter_upwards [hU] with q hq
    rw [pointIndexedCore_trivializationAt]
    exact (congrArg (fun p ↦ (trivializationAt F E p₀.proj p).2)
      (pointIndexedCoreHomeomorph_apply 𝕜 F E q).symm).trans <|
      congrArg Prod.snd (trivializationAt_pointIndexedCoreHomeomorph 𝕜 F E p₀.proj q
        ((pointIndexedCore_localTriv_baseSet 𝕜 F E p₀.proj) ▸
          ((pointIndexedCore 𝕜 F E).localTriv p₀.proj).mem_source.1 hq))
  contMDiff_invFun p₀ := by
    rw [Bundle.contMDiffAt_totalSpace_iff, pointIndexedCore_trivializationAt]
    refine ⟨(contMDiff_proj E).contMDiffAt, ?_⟩
    have hU := (trivializationAt F E p₀.proj).open_source.mem_nhds
      (FiberBundle.mem_trivializationAt_proj_source (x := p₀))
    refine (p₀.contMDiffAt_trivializationAt_snd (IB := IB) (n := n)).congr_of_eventuallyEq ?_
    filter_upwards [hU] with q hq
    exact (congrArg (fun p ↦ ((pointIndexedCore 𝕜 F E).localTriv p₀.proj p).2)
      (pointIndexedCoreHomeomorph_symm_apply 𝕜 F E q).symm).trans <|
      congrArg Prod.snd (localTriv_pointIndexedCoreHomeomorph_symm 𝕜 F E p₀.proj q
        ((trivializationAt F E p₀.proj).mem_source.1 hq))

variable (𝕜 F) in
@[simp]
theorem pointIndexedCoreDiffeomorph_toHomeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (pointIndexedCoreDiffeomorph 𝕜 F E IB n).toHomeomorph = pointIndexedCoreHomeomorph 𝕜 F E :=
  Homeomorph.ext fun p ↦ (pointIndexedCoreHomeomorph_apply 𝕜 F E p).symm

variable (𝕜 F) in
@[simp]
theorem pointIndexedCoreDiffeomorph_apply (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (p : (pointIndexedCore 𝕜 F E).TotalSpace) :
    pointIndexedCoreDiffeomorph 𝕜 F E IB n p =
      ⟨p.proj, pointIndexedCoreFiberEquiv 𝕜 F E p.proj p.snd⟩ := (rfl)

variable (𝕜 F) in
@[simp]
theorem pointIndexedCoreDiffeomorph_symm_apply (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
    (p : TotalSpace F E) :
    (pointIndexedCoreDiffeomorph 𝕜 F E IB n).symm p =
      ⟨p.proj, (pointIndexedCoreFiberEquiv 𝕜 F E p.proj).symm p.snd⟩ := (rfl)

end TauCeti

namespace VectorBundleCore

variable {𝕜 B F F' ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B]

/-- Transporting the model fibre of a `VectorBundleCore` along `e : F ≃L[𝕜] F'` induces a `C^n`
diffeomorphism of total spaces over the identity of the base, acting on fibres by `e.symm`. No
smoothness hypothesis on `Z` is required. -/
noncomputable def congrModelDiffeomorph (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] F')
    (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (Z.congrModel e).TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, F'), IB.prod 𝓘(𝕜, F)⟯ Z.TotalSpace where
  toFun p := ⟨p.proj, e.symm p.snd⟩
  invFun p := ⟨p.proj, e p.snd⟩
  left_inv p := by rcases p with ⟨x, v⟩; exact congrArg (TotalSpace.mk' F' x) (e.apply_symm_apply v)
  right_inv p := by rcases p with ⟨x, v⟩; exact congrArg (TotalSpace.mk' F x) (e.symm_apply_apply v)
  contMDiff_toFun p₀ := by
    rw [Bundle.contMDiffAt_totalSpace_iff]
    refine ⟨(contMDiff_proj (Z.congrModel e).Fiber).contMDiffAt, ?_⟩
    refine (e.symm.contDiff.comp_contMDiffAt
      (p₀.contMDiffAt_trivializationAt_snd (IB := IB) (n := n))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
    dsimp only [Function.comp_apply]
    simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
      indexAt_congrModel]
    have hq := congrArg (fun p : B × F' ↦ e.symm p.2)
      (Z.localTriv_congrModel_congrModelHomeomorph e (Z.indexAt p₀.proj)
        ((Z.congrModelHomeomorph e).symm q))
    rw [(Z.congrModelHomeomorph e).apply_symm_apply, congrModelHomeomorph_symm_apply,
      e.symm_apply_apply] at hq
    exact hq.symm
  contMDiff_invFun p₀ := by
    rw [Bundle.contMDiffAt_totalSpace_iff]
    refine ⟨(contMDiff_proj Z.Fiber).contMDiffAt, ?_⟩
    refine (e.contDiff.comp_contMDiffAt
      (p₀.contMDiffAt_trivializationAt_snd (IB := IB) (n := n))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
    dsimp only [Function.comp_apply]
    simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
      indexAt_congrModel]
    have hq := congrArg Prod.snd
      (Z.localTriv_congrModel_congrModelHomeomorph e (Z.indexAt p₀.proj) q)
    rw [congrModelHomeomorph_apply] at hq
    exact hq

@[simp]
theorem congrModelDiffeomorph_toHomeomorph (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] F')
    (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (Z.congrModelDiffeomorph e IB n).toHomeomorph = (Z.congrModelHomeomorph e).symm :=
  Homeomorph.ext fun p ↦ (Z.congrModelHomeomorph_symm_apply e p).symm

@[simp]
theorem congrModelDiffeomorph_apply (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] F')
    (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) (p : (Z.congrModel e).TotalSpace) :
    Z.congrModelDiffeomorph e IB n p = ⟨p.proj, e.symm p.snd⟩ := (rfl)

@[simp]
theorem congrModelDiffeomorph_symm_apply (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] F')
    (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) (p : Z.TotalSpace) :
    (Z.congrModelDiffeomorph e IB n).symm p = ⟨p.proj, e p.snd⟩ := (rfl)

end VectorBundleCore
