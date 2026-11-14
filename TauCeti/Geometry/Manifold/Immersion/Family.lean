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

For a source manifold with finite-dimensional model space over a complete nontrivially normed
field, injectivity of the source differential persists in jointly `C¹` families. The target
model space may be infinite-dimensional, and the parameter may range over a manifold.

The results give uniform stability on compact subsets and for families fixed off a closed
compact set near the base parameter. For real variations, this keeps induced metrics and the
associated variational functionals defined near the base parameter.
-/

public section

open Bundle Filter Function Set
open scoped ContDiff Manifold Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  {F : P → M → N} {t₀ : P} {x : M} {n : ℕ∞ω}

/-- For a source with finite-dimensional model space, injectivity of the source differential
persists near a point where the family is jointly `Cⁿ`, with `1 ≤ n`. -/
theorem ContMDiffAt.eventually_injective_mfderiv
    (hF : ContMDiffAt (IP.prod I) J n (uncurry F) (t₀, x)) (hn : 1 ≤ n)
    (hinj : Injective (mfderiv I J (F t₀) x)) :
    ∀ᶠ p : P × M in 𝓝 (t₀, x), Injective (mfderiv I J (F p.1) p.2) := by
  have hG : ContMDiffAt ((IP.prod I).prod I) J 1
      (uncurry fun (p : P × M) (y : M) ↦ F p.1 y) ((t₀, x), x) :=
    (hF.of_le hn).comp ((t₀, x), x)
      ((contMDiffAt_fst.comp ((t₀, x), x) contMDiffAt_fst).prodMk contMDiffAt_snd)
  let A := inTangentCoordinates I J (fun p : P × M ↦ p.2) (uncurry F)
    (fun p ↦ mfderiv I J (F p.1) p.2) (t₀, x)
  have hA : ContinuousAt A (t₀, x) :=
    (hG.mfderiv (fun (p : P × M) (y : M) ↦ F p.1 y) (fun p ↦ p.2)
      contMDiffAt_snd (m := 0) (by norm_num)).continuousAt
  have hcoord (p : P × M)
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
  have hproj : ContinuousAt (fun p : P × M ↦ p.2) (t₀, x) := continuousAt_snd
  have hxn := hproj.preimage_mem_nhds
    ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x))
  have hyn := hF.continuousAt.preimage_mem_nhds
    ((trivializationAt E' (TangentSpace J) (F t₀ x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace J) (F t₀ x)))
  filter_upwards [hAn, hxn, hyn] with p hp hx hy
  exact (hcoord p hx hy).mp hp

namespace TauCeti

/-- For a source with finite-dimensional model space, injectivity of the source differentials
on a compact set persists uniformly near the base parameter. Joint `Cⁿ` regularity, with
`1 ≤ n`, is needed only at base-parameter points of the compact set. -/
theorem eventually_forall_injective_mfderiv_of_isCompact {K : Set M}
    (hF : ∀ x ∈ K, ContMDiffAt (IP.prod I) J n (uncurry F) (t₀, x))
    (hn : 1 ≤ n) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Injective (mfderiv I J (F t₀) x)) :
    ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, Injective (mfderiv I J (F t) x) :=
  hK.eventually_forall_of_forall_eventually
    (fun x hx ↦ (hF x hx).eventually_injective_mfderiv hn (hinj x hx))

/-- For a compact source with finite-dimensional model space, injective source differentials
persist uniformly in a family that is jointly `Cⁿ`, with `1 ≤ n`, at the base parameter. -/
theorem eventually_forall_injective_mfderiv [CompactSpace M]
    (hF : ∀ x, ContMDiffAt (IP.prod I) J n (uncurry F) (t₀, x))
    (hn : 1 ≤ n) (hinj : ∀ x, Injective (mfderiv I J (F t₀) x)) :
    ∀ᶠ t in 𝓝 t₀, ∀ x, Injective (mfderiv I J (F t) x) := by
  simpa only [mem_univ, forall_const] using
    eventually_forall_injective_mfderiv_of_isCompact
      (fun x _ ↦ hF x) hn isCompact_univ (fun x _ ↦ hinj x)

/-- For a source with finite-dimensional model space, injective source differentials persist
everywhere if the family agrees with its base map off a closed compact set near the base
parameter. Joint `Cⁿ` regularity, with `1 ≤ n`, is needed only at `(t₀, x)` for `x ∈ K`. -/
theorem eventually_forall_injective_mfderiv_of_isCompact_of_eventually_eq {K : Set M}
    (hF : ∀ x ∈ K, ContMDiffAt (IP.prod I) J n (uncurry F) (t₀, x))
    (hn : 1 ≤ n) (hinj : ∀ x, Injective (mfderiv I J (F t₀) x))
    (hK : IsCompact K) (hKc : IsClosed K)
    (hFK : ∀ᶠ t in 𝓝 t₀, ∀ x ∉ K, F t x = F t₀ x) :
    ∀ᶠ t in 𝓝 t₀, ∀ x, Injective (mfderiv I J (F t) x) := by
  have hnear := eventually_forall_injective_mfderiv_of_isCompact hF hn hK
    (fun x _ ↦ hinj x)
  filter_upwards [hnear, hFK] with t ht hFt x
  by_cases hx : x ∈ K
  · exact ht x hx
  · have heq : F t =ᶠ[𝓝 x] F t₀ := by
      filter_upwards [hKc.isOpen_compl.mem_nhds hx] with y hy using hFt y hy
    rw [heq.mfderiv_eq]
    exact hinj x

end TauCeti
