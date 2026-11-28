/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.Equiv.Fin

/-!
# Subspaces of equal dimension are exchanged by an automorphism

In a finite-dimensional Hausdorff topological vector space over a complete field, two subspaces of
the same dimension are mapped onto each other by a continuous linear automorphism: apply the
purely algebraic exchange lemma (`Submodule.exists_linearEquiv_mem_iff`) and use that linear maps
on such a space are continuous. (Over an incomplete field the latter fails: a finite-dimensional
space can carry inequivalent norms.)

On a finite coordinate space `ι → 𝕜` carrying the product topology, every linear map is already
continuous (`LinearMap.continuous_on_pi`), so no completeness or norm assumption on `𝕜` is needed
(`Submodule.exists_continuousLinearEquiv_mem_iff_pi`). In particular, every linear subspace `W` of
`Fin n → 𝕜` is the preimage of the coordinate subspace
`{y | ∀ i : Fin n, Module.finrank 𝕜 W ≤ i.val → y i = 0}` under a continuous linear equivalence
(`Submodule.exists_continuousLinearEquiv_preimage_coordSubspace`).

## Main results

* `Submodule.exists_continuousLinearEquiv_mem_iff`: exchange of equal-dimension subspaces in a
  finite-dimensional Hausdorff topological vector space over a complete nontrivially normed field.
* `Submodule.exists_continuousLinearEquiv_mem_iff_pi`: exchange of equal-dimension subspaces in a
  finite coordinate space `ι → 𝕜` over any division ring with continuous addition and
  multiplication.
* `Submodule.exists_continuousLinearEquiv_preimage_coordSubspace`: every linear subspace of
  `Fin n → 𝕜` is the preimage of the standard coordinate subspace of the same dimension under a
  continuous linear equivalence.
-/

public section

namespace Submodule

section CompleteSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-- **Subspaces of equal dimension are exchanged by an automorphism.** In a finite-dimensional
Hausdorff topological vector space over a complete field, two subspaces of the same dimension are
mapped onto each other by a continuous linear automorphism. -/
theorem exists_continuousLinearEquiv_mem_iff
    (V L : Submodule 𝕜 E) (h : Module.finrank 𝕜 V = Module.finrank 𝕜 L) :
    ∃ Φ : E ≃L[𝕜] E, ∀ z, z ∈ V ↔ Φ z ∈ L :=
  let ⟨g, hg⟩ := V.exists_linearEquiv_mem_iff L h
  ⟨g.toContinuousLinearEquiv, hg⟩

end CompleteSpace

section Pi

variable {𝕜 : Type*} [DivisionRing 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousMul 𝕜]

/-- **Subspaces of equal dimension in a coordinate space are exchanged by a continuous
automorphism.** On a finite coordinate space `ι → 𝕜` over any division ring with continuous
addition and multiplication, two subspaces of the same dimension are mapped onto each other by a
continuous linear equivalence. Unlike `Submodule.exists_continuousLinearEquiv_mem_iff`, no
completeness or norm assumption on `𝕜` is needed because every linear map out of `ι → 𝕜` is
continuous for the product topology (`LinearMap.continuous_on_pi`). -/
theorem exists_continuousLinearEquiv_mem_iff_pi {ι : Type*} [Finite ι]
    (V L : Submodule 𝕜 (ι → 𝕜)) (h : Module.finrank 𝕜 V = Module.finrank 𝕜 L) :
    ∃ Φ : (ι → 𝕜) ≃L[𝕜] (ι → 𝕜), ∀ z, z ∈ V ↔ Φ z ∈ L :=
  let ⟨g, hg⟩ := V.exists_linearEquiv_mem_iff L h
  ⟨{ g with
    continuous_toFun := g.toLinearMap.continuous_on_pi
    continuous_invFun := g.symm.toLinearMap.continuous_on_pi }, hg⟩

/-- Every linear subspace `W` of `Fin n → 𝕜` over a division ring with continuous addition and
multiplication is the preimage of the coordinate subspace
`{y | ∀ i : Fin n, Module.finrank 𝕜 W ≤ i.val → y i = 0}` under a continuous linear equivalence
of `Fin n → 𝕜`. -/
theorem exists_continuousLinearEquiv_preimage_coordSubspace {n : ℕ}
    (W : Submodule 𝕜 (Fin n → 𝕜)) :
    ∃ e : (Fin n → 𝕜) ≃L[𝕜] Fin n → 𝕜,
      e ⁻¹' {y : Fin n → 𝕜 | ∀ i : Fin n, Module.finrank 𝕜 W ≤ i.val → y i = 0} =
        (W : Set (Fin n → 𝕜)) := by
  set d := Module.finrank 𝕜 W
  have hd : d ≤ n := by simpa using W.finrank_le
  let f : (Fin d → 𝕜) →ₗ[𝕜] Fin n → 𝕜 :=
    (TauCeti.splitAt (𝕜 := 𝕜) hd).symm.toLinearEquiv.toLinearMap.comp
      (LinearMap.inl 𝕜 (Fin d → 𝕜) (Fin (n - d) → 𝕜))
  have hfinj : Function.Injective f :=
    (TauCeti.splitAt (𝕜 := 𝕜) hd).symm.injective.comp (LinearMap.inl_injective)
  have hL_dim : Module.finrank 𝕜 W = Module.finrank 𝕜 (LinearMap.range f) := by
    rw [LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hfinj).symm, Module.finrank_fin_fun]
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_mem_iff_pi W (LinearMap.range f) hL_dim
  refine ⟨e, Set.ext fun z ↦ ?_⟩
  rw [Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe, he z,
    ← TauCeti.splitAt_snd_eq_zero_iff (𝕜 := 𝕜) hd]
  constructor
  · intro hz
    refine ⟨(TauCeti.splitAt (𝕜 := 𝕜) hd (e z)).fst, ?_⟩
    exact (TauCeti.splitAt (𝕜 := 𝕜) hd).injective (by simp [f, Prod.ext_iff, hz])
  · rintro ⟨v, hv⟩
    simpa [f] using congrArg (fun y ↦ (TauCeti.splitAt (𝕜 := 𝕜) hd y).snd) hv.symm

end Pi

end Submodule
