/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Immersion stability for compactly supported variations

Injectivity of the differential is open in a jointly `C²` family. Compactness makes the
parameter interval uniform over the support of a variation, and outside its support the
differential stays unchanged. These facts ensure that local chart variations are admissible
variations through immersions after restricting their parameter interval.
-/

public section

open Bundle Filter Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
  {F : ℝ → M → N} {x : M}

/-- Injectivity of the source differential persists near an immersed point in a `C²` family. -/
theorem eventually_injective_mfderiv_family
    (hF : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry F) (0, x))
    (hinj : Injective (mfderiv I J (F 0) x)) :
    ∀ᶠ p : ℝ × M in 𝓝 (0, x), Injective (mfderiv I J (F p.1) p.2) := by
  have hG : ContMDiffAt ((𝓘(ℝ).prod I).prod I) J 2
      (uncurry fun (p : ℝ × M) (y : M) ↦ F p.1 y) ((0, x), x) :=
    hF.comp ((0, x), x)
      ((contMDiffAt_fst.comp ((0, x), x) contMDiffAt_fst).prodMk contMDiffAt_snd)
  let A := inTangentCoordinates I J (fun p : ℝ × M ↦ p.2) (uncurry F)
    (fun p ↦ mfderiv I J (F p.1) p.2) (0, x)
  have hA : ContinuousAt A (0, x) :=
    (hG.mfderiv (fun (p : ℝ × M) (y : M) ↦ F p.1 y) (fun p ↦ p.2)
      contMDiffAt_snd (m := 1) (by norm_num)).continuousAt
  have hcoord (p : ℝ × M)
      (hx : p.2 ∈ (trivializationAt E (TangentSpace I) x).baseSet)
      (hy : F p.1 p.2 ∈ (trivializationAt E' (TangentSpace J) (F 0 x)).baseSet) :
      Injective (A p) ↔ Injective (mfderiv I J (F p.1) p.2) := by
    dsimp only [A, inTangentCoordinates, uncurry]
    rw [ContinuousLinearMap.inCoordinates_eq hx hy]
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp]
  have hA0 : Injective (A (0, x)) :=
    (hcoord (0, x) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)
      (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (F 0 x))).mpr hinj
  have hAn := hA.preimage_mem_nhds (ContinuousLinearMap.isOpen_injective.mem_nhds hA0)
  have hxn := (show ContinuousAt (fun p : ℝ × M ↦ p.2) (0, x) from
    continuousAt_snd).preimage_mem_nhds
    ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x))
  have hyn := hF.continuousAt.preimage_mem_nhds
    ((trivializationAt E' (TangentSpace J) (F 0 x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (F 0 x)))
  filter_upwards [hAn, hxn, hyn] with p hp hx hy
  exact (hcoord p hx hy).mp hp

/-- A compactly supported `C²` variation of an immersion remains immersive for a uniform
parameter neighborhood of zero. -/
theorem eventually_injective_mfderiv_of_compactSupport {K : Set M}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry F) (0, x))
    (hinj : ∀ x, Injective (mfderiv I J (F 0) x))
    (hK : IsCompact K) (hKc : IsClosed K)
    (hFK : ∀ t, ∀ x ∉ K, F t x = F 0 x) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x, Injective (mfderiv I J (F t) x) := by
  have hnear := hK.eventually_forall_of_forall_eventually
    (P := fun t x ↦ Injective (mfderiv I J (F t) x)) (x₀ := (0 : ℝ))
    (fun x _ ↦ eventually_injective_mfderiv_family (hF x) (hinj x))
  filter_upwards [hnear] with t ht x
  by_cases hx : x ∈ K
  · exact ht x hx
  · have heq : F t =ᶠ[𝓝 x] F 0 := by
      filter_upwards [hKc.isOpen_compl.mem_nhds hx] with y hy using hFK t y hy
    rw [heq.mfderiv_eq]
    exact hinj x

end TauCeti.Manifold
