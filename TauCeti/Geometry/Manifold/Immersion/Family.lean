/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Stability of injective differentials in `C¹` families

Injectivity of the differential is open in a jointly `C¹` family of maps `F t : M → N`.
If the family is constant in `t` outside a closed compact set, compactness makes the
parameter neighborhood uniform: every map of the family near an immersed parameter has an
injective differential at every point.
-/

public section

open Bundle Filter Function Set
open scoped ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {F : ℝ → M → N} {t₀ : ℝ} {x : M}

/-- Injectivity of the source differential persists near an immersed point in a `C¹` family. -/
theorem ContMDiffAt.eventually_injective_mfderiv
    (hF : ContMDiffAt (𝓘(ℝ).prod I) J 1 (uncurry F) (t₀, x))
    (hinj : Injective (mfderiv I J (F t₀) x)) :
    ∀ᶠ p : ℝ × M in 𝓝 (t₀, x), Injective (mfderiv I J (F p.1) p.2) := by
  have hG : ContMDiffAt ((𝓘(ℝ).prod I).prod I) J 1
      (uncurry fun (p : ℝ × M) (y : M) ↦ F p.1 y) ((t₀, x), x) :=
    hF.comp ((t₀, x), x)
      ((contMDiffAt_fst.comp ((t₀, x), x) contMDiffAt_fst).prodMk contMDiffAt_snd)
  let A := inTangentCoordinates I J (fun p : ℝ × M ↦ p.2) (uncurry F)
    (fun p ↦ mfderiv I J (F p.1) p.2) (t₀, x)
  have hA : ContinuousAt A (t₀, x) :=
    (hG.mfderiv (fun (p : ℝ × M) (y : M) ↦ F p.1 y) (fun p ↦ p.2)
      contMDiffAt_snd (m := 0) (by norm_num)).continuousAt
  have hcoord (p : ℝ × M)
      (hx : p.2 ∈ (trivializationAt E (TangentSpace I) x).baseSet)
      (hy : F p.1 p.2 ∈ (trivializationAt E' (TangentSpace J) (F t₀ x)).baseSet) :
      Injective (A p) ↔ Injective (mfderiv I J (F p.1) p.2) := by
    dsimp only [A, inTangentCoordinates, uncurry]
    rw [ContinuousLinearMap.inCoordinates_eq hx hy]
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp]
  have hA0 : Injective (A (t₀, x)) :=
    (hcoord (t₀, x) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)
      (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (F t₀ x))).mpr hinj
  have hAn := hA.preimage_mem_nhds (ContinuousLinearMap.isOpen_injective.mem_nhds hA0)
  have hxn := (show ContinuousAt (fun p : ℝ × M ↦ p.2) (t₀, x) from
    continuousAt_snd).preimage_mem_nhds
    ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x))
  have hyn := hF.continuousAt.preimage_mem_nhds
    ((trivializationAt E' (TangentSpace J) (F t₀ x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (F t₀ x)))
  filter_upwards [hAn, hxn, hyn] with p hp hx hy
  exact (hcoord p hx hy).mp hp

namespace TauCeti

/-- A `C¹` family of maps that is constant in the parameter outside a closed compact set `K`
has injective differentials everywhere, for all parameters in a neighborhood of `t₀`,
provided `F t₀` has injective differentials everywhere. -/
theorem eventually_forall_injective_mfderiv_of_isCompact {K : Set M}
    (hF : ∀ x ∈ K, ContMDiffAt (𝓘(ℝ).prod I) J 1 (uncurry F) (t₀, x))
    (hinj : ∀ x, Injective (mfderiv I J (F t₀) x))
    (hK : IsCompact K) (hKc : IsClosed K)
    (hFK : ∀ t, ∀ x ∉ K, F t x = F t₀ x) :
    ∀ᶠ t in 𝓝 t₀, ∀ x, Injective (mfderiv I J (F t) x) := by
  have hnear := hK.eventually_forall_of_forall_eventually
    (P := fun t x ↦ Injective (mfderiv I J (F t) x)) (x₀ := t₀)
    (fun x hx ↦ (hF x hx).eventually_injective_mfderiv (hinj x))
  filter_upwards [hnear] with t ht x
  by_cases hx : x ∈ K
  · exact ht x hx
  · have heq : F t =ᶠ[𝓝 x] F t₀ := by
      filter_upwards [hKc.isOpen_compl.mem_nhds hx] with y hy using hFK t y hy
    rw [heq.mfderiv_eq]
    exact hinj x

end TauCeti
