/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The weak topology and the canonical bidual map

The canonical map from a seminormed space with its weak topology to its weak-star bidual is
inducing: the weak topology is the topology pulled back from the weak-star bidual. This holds
without assuming that the seminorm separates points.

When the scalar field is proper, a norm-bounded set has weakly compact closure if the
weak-star closure of its bidual image lies in the range of the canonical map. This extends Mathlib's
`NormedSpace.isCompact_closure_of_isBounded` to seminormed spaces, using the inducing property
to transfer Banach–Alaoglu compactness back to the weak topology.
In particular, in a reflexive seminormed space over a proper field, where the canonical map is
surjective, every norm-bounded set has weakly compact closure
(`TauCeti.isCompact_closure_toWeakSpace`).

Finally, every linear map from a vector space into the bidual of a normed space lifts into the
space on the subspace of vectors sent into the canonical image (`LinearMap.exists_lift_doubleDual`).
-/

public section

open Bornology Set Topology

namespace NormedSpace

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The canonical bidual map induces the weak topology from the weak-star topology,
including when the seminorm on the source does not separate points. -/
theorem isInducing_inclusionInDoubleDualWeak :
    IsInducing (inclusionInDoubleDualWeak 𝕜 E) where
  -- Both topologies are induced by evaluation against the continuous dual.
  eq_induced := Eq.symm induced_compose

/-- An element of the bidual lies in the canonical image of `E` iff it does when viewed in the
weak-star bidual. -/
theorem toWeakDual_mem_range_inclusionInDoubleDualWeak_iff
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    StrongDual.toWeakDual Φ ∈ range (inclusionInDoubleDualWeak 𝕜 E) ↔
      Φ ∈ range (inclusionInDoubleDual 𝕜 E) := by
  simp only [mem_range, inclusionInDoubleDualWeak_apply, EmbeddingLike.apply_eq_iff_eq,
    (toWeakSpace 𝕜 E).symm.surjective.exists]

variable [ProperSpace 𝕜]

/-- A norm-bounded set in a seminormed space has weakly compact closure if the weak-star
closure of its canonical bidual image lies in the range of the canonical map. -/
theorem isCompact_closure_weakSpace_of_isBounded (s : Set (WeakSpace 𝕜 E))
    (hs : IsBounded ((toWeakSpace 𝕜 E) ⁻¹' s))
    (hrange : closure (inclusionInDoubleDualWeak 𝕜 E '' s) ⊆
      range (inclusionInDoubleDualWeak 𝕜 E)) :
    IsCompact (closure s) := by
  rw [(isInducing_inclusionInDoubleDualWeak 𝕜 E).closure_eq_preimage_closure_image]
  apply (isInducing_inclusionInDoubleDualWeak 𝕜 E).isCompact_preimage' _ hrange
  -- The bundled Lipschitz bound on the bidual map exceeds the default elaboration budget
  -- for these seminormed hypotheses. A direct ball bound avoids that instance comparison.
  apply WeakDual.isCompact_of_bounded_of_closed _ isClosed_closure
  apply WeakDual.isBounded_closure
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hs
  refine (WeakDual.isBounded_closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) r).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_preimage, inclusionInDoubleDualWeak_apply, StrongDual.toStrongDual_toWeakDual,
    mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))]
  exact (double_dual_bound 𝕜 E _).trans (hr _ (by simpa using hx))

end NormedSpace

namespace TauCeti

open NormedSpace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In a reflexive seminormed space over a proper nontrivially normed field, every norm-bounded
set has weakly compact closure. -/
theorem isCompact_closure_toWeakSpace
    (hE : Function.Surjective (inclusionInDoubleDual 𝕜 E)) {s : Set E} (hs : IsBounded s) :
    IsCompact (closure (toWeakSpace 𝕜 E '' s)) := by
  apply NormedSpace.isCompact_closure_weakSpace_of_isBounded 𝕜 E
  · simpa only [preimage_image_eq _ (toWeakSpace 𝕜 E).injective] using hs
  · intro φ _
    obtain ⟨x, hx⟩ := hE (WeakDual.toStrongDual φ)
    refine ⟨toWeakSpace 𝕜 E x, ?_⟩
    apply WeakDual.toStrongDual.injective
    simpa only [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toStrongDual_toWeakDual] using hx

end TauCeti

namespace LinearMap

open NormedSpace

variable {𝕜 E V : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [AddCommGroup V] [Module 𝕜 V]

/-- A linear map `ι : V → E**` lifts into `E` on the subspace `F₀` of the vectors that it maps
into the canonical image of `E`: there is a linear map `A : F₀ → E` whose canonical image is
`ι`, and every `v` with `ι v` equal to the canonical image of `x` lies in `F₀`. -/
theorem exists_lift_doubleDual (ι : V →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) :
    ∃ (F₀ : Submodule 𝕜 V) (A : F₀ →ₗ[𝕜] E),
      (∀ φ : F₀, inclusionInDoubleDual 𝕜 E (A φ) = ι φ) ∧
        ∀ v x, ι v = inclusionInDoubleDual 𝕜 E x → v ∈ F₀ := by
  let J := inclusionInDoubleDual 𝕜 E
  have hJ : Function.Injective J := (inclusionInDoubleDualLi 𝕜 (E := E)).injective
  let F₀ : Submodule 𝕜 V := (LinearMap.range (J : E →ₗ[𝕜] _)).comap ι
  exact ⟨F₀, LinearMap.codRestrictOfInjective (ι ∘ₗ F₀.subtype) J hJ fun φ ↦ φ.2,
    fun φ ↦ LinearMap.codRestrictOfInjective_comp_apply (ι ∘ₗ F₀.subtype) (J : E →ₗ[𝕜] _)
      hJ _ φ, fun v x hv ↦ ⟨x, hv.symm⟩⟩

end LinearMap
