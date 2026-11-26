/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.Topology.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Local subbundle frames for the image of an injective differential

For a `C^n` map `f : M → N` (`m + 1 ≤ n`) whose differential `mfderiv I J f x` is injective at
every `x : M`, pushing forward local frames of `TangentSpace I` along `mfderiv I J f` yields `C^m`
local subbundle frames of `x ↦ (mfderiv I J f x).toLinearMap.range` inside `f *ᵖ TangentSpace J`
(`ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis`,
`ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv`). In particular, every `C^n` immersion
(`n ≠ 0`) of a finite-dimensional manifold admits `C^m` local subbundle frames for its differential
image (`Manifold.IsImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Proposition 10.34.
-/

public noncomputable section

open Bundle Set Function Topology
open scoped Manifold ContDiff

variable {𝕜 E V H G M N K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [FunLike K M N] [ContinuousMapClass K M N] {f : K} {n m : ℕ∞ω}
  [IsManifold J 1 N] [IsManifold I (m + 1) M]

/-- **Local subbundle frames for the image of an injective differential.** If `f : M → N` is `C^n`
with `m + 1 ≤ n` and `mfderiv I J f x` is injective at every `x : M`, then pushing forward local
frames of `TangentSpace I` associated with any basis `b : Module.Basis ι 𝕜 E` gives `C^m` local
subbundle frames of `(mfderiv I J f x).toLinearMap.range` inside `f *ᵖ TangentSpace J`. -/
theorem ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis {ι : Type*}
    (b : Module.Basis ι 𝕜 E) (hf : ContMDiff I J n f) (hm : m + 1 ≤ n)
    (hinj : ∀ x, Injective (mfderiv I J (f : M → N) x)) :
    TauCeti.HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V ι
      (fun x ↦ (mfderiv I J (f : M → N) x).toLinearMap.range) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  have hfm : ContMDiff I J m f := hf.of_le ((le_add_right le_rfl).trans hm)
  have hTf := ContMDiff.contMDiff_tangentMap hf hm
  refine TauCeti.hasLocalContMDiffSubbundleFrames_iff.2 fun x₀ ↦ ?_
  let e := trivializationAt E (TangentSpace I) x₀
  let A (x : M) : TangentSpace I x →ₗ[𝕜] ((f : M → N) *ᵖ (TangentSpace J)) x :=
    (mfderiv I J (f : M → N) x).toLinearMap
  let X (i : ι) (x : M) : ((f : M → N) *ᵖ (TangentSpace J)) x := A x (e.localFrame b i x)
  have hX (i : ι) : ContMDiffOn I (I.prod 𝓘(𝕜, V)) m
      (fun y ↦ TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) y (X i y)) e.baseSet :=
    fun x hx ↦ ((Pullback.contMDiffAt_iff f hfm.contMDiffAt).2 ⟨contMDiffAt_id,
      hTf.contMDiffAt.comp x ((e.contMDiffOn_localFrame_baseSet (I := I) (n := m) b i).contMDiffAt
        (e.open_baseSet.mem_nhds hx))⟩).contMDiffWithinAt
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x₀, X,
    ⟨fun i ↦ (hX i).continuousOn, fun {x} hx ↦ ?_, fun {x} hx ↦
      e.span_range_localFrame_map b (A x) hx⟩, hX⟩
  have hframe : (fun i ↦ e.localFrame b i x) = e.basisAt b hx :=
    funext fun _ ↦ e.localFrame_apply_of_mem_baseSet b hx
  exact (hframe ▸ (e.basisAt b hx).linearIndependent).map' (A x) (LinearMap.ker_eq_bot.2 (hinj x))

/-- Finite-dimensional specialization of
`ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis` using `Module.finBasis 𝕜 E`. -/
theorem ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv [FiniteDimensional 𝕜 E]
    (hf : ContMDiff I J n f) (hm : m + 1 ≤ n)
    (hinj : ∀ x, Injective (mfderiv I J (f : M → N) x)) :
    TauCeti.HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V
      (Fin (Module.finrank 𝕜 E)) (fun x ↦ (mfderiv I J (f : M → N) x).toLinearMap.range) :=
  ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv_of_basis (Module.finBasis 𝕜 E) hf hm hinj

/-- A `C^n` immersion (`n ≠ 0`, `m + 1 ≤ n`) of a finite-dimensional manifold `M` has `C^m` local
subbundle frames for `(mfderiv I J f x).toLinearMap.range` inside `f *ᵖ TangentSpace J`. -/
theorem Manifold.IsImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv
    [FiniteDimensional 𝕜 E] (hf : Manifold.IsImmersion I J n f) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    TauCeti.HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V
      (Fin (Module.finrank 𝕜 E)) (fun x ↦ (mfderiv I J (f : M → N) x).toLinearMap.range) :=
  ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv hf.contMDiff hm (hf.mfderiv_injective hn)
