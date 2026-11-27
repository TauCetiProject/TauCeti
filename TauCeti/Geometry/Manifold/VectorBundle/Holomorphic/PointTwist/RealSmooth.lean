/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars

/-!
# The smooth real structure of a point twist

Let `X` be a Riemann surface and `E → X` a complex vector bundle with model fibre `F`. The signed
point twist `E(±x)` (`TauCeti.signedPointTwistCore`) is glued from the trivializations of `E` and
the centred chart coordinate `φ - φ x` at `x`, which is holomorphic. When `E` is a holomorphic
bundle, `E(±x)` is one too (`TauCeti.signedPointTwistCore.isContMDiff`). This file treats a
complex vector bundle `E` whose structure is only *real* `C^n`: its underlying real bundle
(`VectorBundle.restrictScalars`) is a `C^n` vector bundle over the real manifold underlying `X`,
modelled on `𝓘(ℝ, ℂ)`, as for the bundles on which real Cauchy–Riemann operators act. Then the
underlying real bundle of `E(±x)` is a `C^n` vector bundle on the same real manifold
(`TauCeti.signedPointTwistCore.contMDiffVectorBundle_real`): its real coordinate changes are those
of `E`, multiplied by the scalar transition function of the twist, which is holomorphic and hence
real `C^n`.

Consequently multiplication by the canonical section of `𝒪(x)` sends real-`C^n` sections of `E`
to real-`C^n` sections of `E(x)` (`TauCeti.contMDiff_pointTwistMul_section_real`), and away from `x`
a section of `E(±x)` is real `C^n` exactly when its image in `E` under `pointTwistDiv` is
(`TauCeti.contMDiffAt_signedPointTwist_section_iff_of_ne_real`).

This is the setting of the reduction of a smooth complex line bundle `L` over a compact Riemann
surface to a twist of the trivial bundle, in the proof of the Riemann–Roch formula for real
Cauchy–Riemann operators (McDuff–Salamon, Theorem C.1.10): `L` is twisted at the zeros of a
generic smooth section, and only the real smooth structure of `L` is available.

## Main results

* `TauCeti.signedPointTwistCore.contMDiffVectorBundle_real`: the point twists of a real-`C^n`
  complex vector bundle are real-`C^n` vector bundles.
* `TauCeti.contMDiff_pointTwistMul_section_real`: multiplication by the canonical section of
  `𝒪(x)` preserves real-`C^n` sections.
* `TauCeti.contMDiffAt_signedPointTwist_section_iff_of_ne_real`: away from `x`, the real-`C^n`
  sections of `E(±x)` are those of `E`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 1, Section 1
  (divisors and line bundles).
-/

public section

noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ∞ω}
  [IsManifold 𝓘(ℂ) n X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  {E : X → Type*} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, Module ℝ (E z)]
  [∀ z, IsScalarTower ℝ ℂ (E z)] [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

local instance instVectorBundleRealPointTwistRealSmooth : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

local instance instVectorBundleRealSignedPointTwistCoreRealSmooth (x : X) (s : Bool) :
    VectorBundle ℝ F (signedPointTwistCore F E x s).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F _

variable [ContMDiffVectorBundle n F E 𝓘(ℝ, ℂ)]

/-- **The point twists of a real-`C^n` complex bundle are real-`C^n`.** If the underlying real
bundle of a complex vector bundle `E` over a Riemann surface is a `C^n` vector bundle over the
underlying real manifold, so is the underlying real bundle of the signed point twist `E(±x)`: its
real coordinate changes are those of `E` multiplied by the holomorphic scalar transition function
of the twist. -/
instance signedPointTwistCore.contMDiffVectorBundle_real (x : X) (s : Bool) :
    ContMDiffVectorBundle n F (signedPointTwistCore F E x s).Fiber 𝓘(ℝ, ℂ) where
  contMDiffOn_coordChangeL := by
    intro e e' he he'
    -- The real coordinate changes of the twist are its complex ones, with scalars restricted.
    have hR (z : X) : (e.coordChangeL ℝ e' z : F →L[ℝ] F) =
        (e.coordChangeL ℂ e' z : F →L[ℂ] F).restrictScalars ℝ :=
      (Trivialization.restrictScalars_coordChangeL ℝ ℂ e e').symm
    simp_rw [hR]
    obtain ⟨i, rfl⟩ := he.out
    obtain ⟨j, rfl⟩ := he'.out
    set S := (signedPointTwistCore F E x s).baseSet i ∩ (signedPointTwistCore F E x s).baseSet j
    -- The scalar transition function of the twist is holomorphic, hence real `C^n`.
    have hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (signedPointTwistFactor x s i.2 j.2)
        (pointTwistBaseSet x i.2 ∩ pointTwistBaseSet x j.2) := by
      simpa only [modelWithCornersSelf_restrictScalars] using
        (contMDiffOn_signedPointTwistFactor x s i.2 j.2).restrictScalars ℝ
    -- The real coordinate changes of `E` are real `C^n`.
    have hc := contMDiffOn_coordChangeL (IB := 𝓘(ℝ, ℂ)) (n := n) (F := F) (E := E)
      (trivializationAt F E i.1) (trivializationAt F E j.1)
    -- Multiplication by a complex scalar on `F` is real linear in the scalar.
    have hm := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).contMDiff.comp_contMDiffOn
      (hf.mono fun _ (hz : _ ∈ S) ↦
        ⟨(mem_signedPointTwistCore_baseSet.1 hz.1).2, (mem_signedPointTwistCore_baseSet.1 hz.2).2⟩)
    have hc' := hc.mono fun _ (hz : _ ∈ S) ↦
      ⟨(mem_signedPointTwistCore_baseSet.1 hz.1).1, (mem_signedPointTwistCore_baseSet.1 hz.2).1⟩
    refine (hm.clm_comp hc').congr fun z (hz : z ∈ S) ↦ ?_
    ext v
    rw [ContinuousLinearMap.coe_restrictScalars']
    -- The complex coordinate change of the twist is the coordinate change of its core.
    refine ((signedPointTwistCore F E x s).localTriv_coordChange_eq i j hz v).trans ?_
    rw [signedPointTwistCore_coordChange, smul_apply,
      ← Trivialization.restrictScalars_coordChangeL ℝ ℂ (trivializationAt F E i.1)
        (trivializationAt F E j.1)]
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.coe_restrictScalars']

/-- Multiplication by the canonical section of `𝒪(x)` sends a section of `E` that is real `C^n`
at `z₀` to a section of the point twist `E(x)` that is real `C^n` at `z₀`. -/
theorem contMDiffAt_pointTwistMul_section_real {x z₀ : X} {σ : ∀ z, E z}
    (hσ : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n (fun z ↦ TotalSpace.mk' F z (σ z)) z₀) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (E := (pointTwistCore F E x).Fiber) z
        (pointTwistMul F E x z (σ z))) z₀ := by
  classical
  have hz₀ := (pointTwistCore F E x).mem_baseSet_at z₀
  rw [signedPointTwistCore_indexAt] at hz₀
  refine ((trivializationAt F (pointTwistCore F E x).Fiber z₀).contMDiffAt_section_iff
    (E := (pointTwistCore F E x).Fiber) (s := fun z ↦ pointTwistMul F E x z (σ z))
    (mem_baseSet_trivializationAt F _ z₀)).2 ?_
  rw [signedPointTwistCore_trivializationAt]
  rw [(trivializationAt F E z₀).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt F E z₀)] at hσ
  -- The scalar `pointTwistFactor x false b` is holomorphic, hence real `C^n`.
  have hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (pointTwistFactor x false (decide (z₀ = x))) z₀ := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((contMDiffOn_pointTwistFactor_false x _).contMDiffAt
        ((isOpen_pointTwistBaseSet x _).mem_nhds
          (mem_pointTwistBaseSet_decide x z₀))).restrictScalars ℝ
  have hm := ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).contMDiff.contMDiffAt.comp z₀
    hf).clm_apply hσ
  refine hm.congr_of_eventuallyEq ?_
  filter_upwards [((pointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
  rw [Function.comp_apply, ContinuousLinearMap.lsmul_apply]
  exact pointTwistCore_localTriv_pointTwistMul hz (σ z)

/-- Multiplication by the canonical section of `𝒪(x)` sends real-`C^n` sections of `E` to
real-`C^n` sections of the point twist `E(x)`. -/
theorem contMDiff_pointTwistMul_section_real {x : X} {σ : ∀ z, E z}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n (fun z ↦ TotalSpace.mk' F z (σ z))) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F (E := (pointTwistCore F E x).Fiber) z
        (pointTwistMul F E x z (σ z))) :=
  fun z₀ ↦ contMDiffAt_pointTwistMul_section_real (hσ z₀)

/-- Away from `x`, a section of the signed point twist `E(±x)` is real `C^n` at `z₀` exactly when
its image under `pointTwistDiv`, a section of `E`, is. -/
theorem contMDiffAt_signedPointTwist_section_iff_of_ne_real {x z₀ : X} {s : Bool} (h : z₀ ≠ x)
    {τ : ∀ z, (signedPointTwistCore F E x s).Fiber z} :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)) z₀ ↔
      ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n
        (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) z₀ := by
  have hz₀ : z₀ ∈ (signedPointTwistCore F E x s).baseSet (z₀, false) :=
    mem_signedPointTwistCore_baseSet.2 ⟨mem_baseSet_trivializationAt F E z₀, by simpa using h⟩
  rw [(trivializationAt F (signedPointTwistCore F E x s).Fiber z₀).contMDiffAt_section_iff
      (mem_baseSet_trivializationAt F _ z₀),
    (trivializationAt F E z₀).contMDiffAt_section_iff (mem_baseSet_trivializationAt F E z₀),
    signedPointTwistCore_trivializationAt_of_ne h]
  refine Filter.EventuallyEq.contMDiffAt_iff ?_
  filter_upwards [((signedPointTwistCore F E x s).isOpen_baseSet _).mem_nhds hz₀] with z hz
  exact (trivializationAt_pointTwistDiv hz (τ z)).symm

end TauCeti
