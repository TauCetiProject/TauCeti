/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Sequences
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import TauCeti.Topology.Sequences.Basic

/-!
# Convergence and neighborhoods in the weak topology

A family converges in `WeakSpace 𝕜 E` exactly when its values under every continuous linear
functional converge (`TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto`). This lets
weak convergence be used without unfolding the definition of `WeakSpace` as a `WeakBilin` space.
No injectivity of the duality pairing is needed, since the weak topology is induced by the
evaluations. Sequential closedness of an image `toWeakSpace 𝕜 E '' s` likewise translates directly
to closure of `s` under limits of weakly convergent sequences
(`TauCeti.isSeqClosed_toWeakSpace_image_iff`).

When the weak topology is Hausdorff, weak convergence implies convergence in the original topology
for families that eventually stay in a compact set
(`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`): on a compact set the two topologies agree.

If a linear map `J : E →ₗ[𝕜] F` has infinite-dimensional range, the common kernel of any finite
family of continuous linear functionals on `E` contains a vector `v` with `J v ≠ 0`, so every weak
neighborhood of `x : E` contains an entire affine line `x + 𝕜 • v` along which `J v ≠ 0`
(`LinearMap.exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace`). In particular, in an
infinite-dimensional topological vector space every weak neighborhood contains a nontrivial affine
line (`TauCeti.exists_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace`, and at `0`
`TauCeti.exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, §3.2, Proposition 3.5.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.5.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- A family converges weakly exactly when its values under every continuous linear functional
converge. -/
theorem tendsto_toWeakSpace_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {u : α → E}
    {x : E} :
    Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E x)) ↔
      ∀ f : StrongDual 𝕜 E, Tendsto (fun n ↦ f (u n)) l (𝓝 (f x)) :=
  (IsInducing.induced _).tendsto_nhds_iff.trans tendsto_pi_nhds

/-- Sequential closedness of `toWeakSpace 𝕜 E '' s` in `WeakSpace 𝕜 E` is equivalent to closure of
`s` under limits of weakly convergent sequences in `E`. -/
theorem isSeqClosed_toWeakSpace_image_iff {s : Set E} :
    IsSeqClosed (toWeakSpace 𝕜 E '' s) ↔
      ∀ ⦃u : ℕ → E⦄ ⦃x : E⦄, (∀ n, u n ∈ s) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) → x ∈ s :=
  (toWeakSpace 𝕜 E).toEquiv.isSeqClosed_image_iff

/-- If the weak topology is Hausdorff, a family that eventually stays in a compact set and
converges weakly to `a` converges to `a` in the original topology. -/
theorem tendsto_of_tendsto_toWeakSpace_of_isCompact [T2Space (WeakSpace 𝕜 E)] {α : Type*}
    {l : Filter α} {K : Set E} (hK : IsCompact K) {u : α → E} (hu : ∀ᶠ n in l, u n ∈ K) {a : E}
    (h : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E a))) :
    Tendsto u l (𝓝 a) := by
  refine hK.tendsto_nhds_of_unique_mapClusterPt hu fun y _ hy ↦ (toWeakSpace 𝕜 E).injective ?_
  -- A cluster point in the original topology is a weak cluster point, and the weak topology is
  -- Hausdorff.
  have hy' : MapClusterPt (toWeakSpace 𝕜 E y) l (fun n ↦ toWeakSpace 𝕜 E (u n)) :=
    hy.tendsto_comp ((toWeakSpaceCLM 𝕜 E).continuous.tendsto y)
  exact eq_of_nhds_neBot (hy'.neBot.mono (inf_le_inf_left _ h))

end TauCeti

section WeakNeighborhoods

variable {𝕜 E F : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F]

namespace LinearMap

/-- If `J : E →ₗ[𝕜] F` has infinite-dimensional range, every weak neighborhood of `x : E`
contains an entire affine line `x + 𝕜 • v` along which `J v ≠ 0`. -/
theorem exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace (J : E →ₗ[𝕜] F)
    (hJ : ¬ FiniteDimensional 𝕜 (LinearMap.range J)) (x : E) {U : Set (WeakSpace 𝕜 E)}
    (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ v : E, J v ≠ 0 ∧ ∀ k : 𝕜, toWeakSpace 𝕜 E (x + k • v) ∈ U := by
  have hind : IsInducing
      (fun (w : WeakSpace 𝕜 E) (f : StrongDual 𝕜 E) ↦ f ((toWeakSpace 𝕜 E).symm w)) := ⟨rfl⟩
  rw [hind.nhds_eq_comap] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.1 hU
  rw [nhds_pi] at hW
  obtain ⟨S, t, ht, hSt⟩ := Filter.mem_pi'.1 hW
  -- The evaluation map on the finite set `S` has finite-dimensional image, so its kernel cannot
  -- be contained in `ker J`.
  let Φ : E →ₗ[𝕜] (S → 𝕜) := LinearMap.pi fun f : S ↦ f.val.toLinearMap
  have hv : ∃ v : E, Φ v = 0 ∧ J v ≠ 0 := by
    by_contra h
    push Not at h
    have hker : LinearMap.ker Φ ≤ LinearMap.ker J := fun v hv ↦ h v hv
    have hfinQ : FiniteDimensional 𝕜 (E ⧸ LinearMap.ker Φ) :=
      Φ.quotKerEquivRange.symm.finiteDimensional
    have hrange : LinearMap.range ((LinearMap.ker Φ).liftQ J hker) = LinearMap.range J :=
      Submodule.range_liftQ (LinearMap.ker Φ) J hker
    exact hJ (hrange ▸ Module.Finite.range ((LinearMap.ker Φ).liftQ J hker))
  obtain ⟨v, hvΦ, hJv⟩ := hv
  refine ⟨v, hJv, fun k ↦ hWU (hSt fun f hf ↦ ?_)⟩
  have hfv : f v = 0 := congr_fun hvΦ ⟨f, hf⟩
  have hfx : f x ∈ t f := by simpa using mem_of_mem_nhds (ht f)
  simpa [hfv] using hfx

end LinearMap

namespace TauCeti

/-- In an infinite-dimensional topological vector space, every weak neighborhood of `x` contains
a nontrivial affine line `x + 𝕜 • v` (`v ≠ 0`). -/
theorem exists_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace
    (hE : ¬ FiniteDimensional 𝕜 E) (x : E) {U : Set (WeakSpace 𝕜 E)}
    (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ v : E, v ≠ 0 ∧ ∀ k : 𝕜, toWeakSpace 𝕜 E (x + k • v) ∈ U := by
  have hrange : ¬ FiniteDimensional 𝕜 (LinearMap.range (LinearMap.id (R := 𝕜) (M := E))) := by
    rw [LinearMap.range_id]
    exact fun _ ↦ hE (Submodule.topEquiv (R := 𝕜) (M := E)).finiteDimensional
  exact LinearMap.id.exists_apply_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace hrange x hU

/-- In an infinite-dimensional space, every weak neighbourhood of `0` contains the line through
some nonzero vector. -/
theorem exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero
    (hE : ¬ FiniteDimensional 𝕜 E) {U : Set (WeakSpace 𝕜 E)} (hU : U ∈ 𝓝 0) :
    ∃ x : E, x ≠ 0 ∧ ∀ c : 𝕜, toWeakSpace 𝕜 E (c • x) ∈ U := by
  simpa only [zero_add] using
    exists_ne_zero_add_smul_mem_of_mem_nhds_toWeakSpace hE 0 (by simpa only [map_zero] using hU)

end TauCeti

end WeakNeighborhoods
