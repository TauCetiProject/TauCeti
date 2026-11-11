/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.WeakDual
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded

/-!
# Approximation by weakly compact sets

**Grothendieck's lemma**: in a real or complex Banach space, a set `A` has weakly compact closure
as soon as, for every `ε > 0`, it lies within norm distance `ε` of some weakly compact set.

The canonical image of `A` in the bidual then lies in the weak-star compact set
`J(K) + ε B**` for a weakly compact `K`, so every weak-star cluster point of this image lies within
`ε` of the canonical image `J(E)`. As `J(E)` is norm closed, these cluster points lie in `J(E)`,
and the bidual criterion `NormedSpace.isCompact_closure_of_isBounded` applies.

This is the standard way to prove weak compactness by truncation: for example, a uniformly
integrable subset of `L¹` lies within `ε` of a ball of `L²`, which is weakly compact.

## Main statements

* `TauCeti.isCompact_closure_toWeakSpace_of_forall_exists_isCompact`: Grothendieck's lemma.

## References

* A. Grothendieck, *Sur les applications linéaires faiblement compactes d'espaces du type C(K)*,
  Canad. J. Math. **5** (1953), 129–173.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.2.
-/

public section

open Bornology Metric NormedSpace Set
open scoped Pointwise

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Grothendieck's lemma.** In a real or complex Banach space, a set has weakly compact closure
if, for every `ε > 0`, each of its points lies within norm distance `ε` of a fixed weakly compact
set. -/
theorem isCompact_closure_toWeakSpace_of_forall_exists_isCompact [CompleteSpace E] {A : Set E}
    (h : ∀ ε > 0, ∃ K : Set E, IsCompact (toWeakSpace 𝕜 E '' K) ∧
      ∀ x ∈ A, ∃ y ∈ K, ‖x - y‖ ≤ ε) :
    IsCompact (closure (toWeakSpace 𝕜 E '' A)) := by
  apply isCompact_closure_of_isBounded 𝕜 E
  · -- `A` lies in the `1`-neighbourhood of a weakly compact, hence bounded, set.
    rw [preimage_image_eq _ (toWeakSpace 𝕜 E).injective]
    obtain ⟨K, hK, hAK⟩ := h 1 one_pos
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded_toWeakSpace_preimage
    refine isBounded_iff_forall_norm_le.2 ⟨R + 1, fun x hx ↦ ?_⟩
    obtain ⟨y, hy, hxy⟩ := hAK x hx
    have hyR : ‖y‖ ≤ R := hR y (mem_image_of_mem _ hy)
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  · intro φ hφ
    set J := inclusionInDoubleDual 𝕜 E
    -- Every weak-star cluster point `φ` lies within `ε` of the canonical image, for every `ε`.
    have hclose : ∀ ε > 0, ∃ y : E, ‖WeakDual.toStrongDual φ - J y‖ ≤ ε := by
      intro ε hε
      obtain ⟨K, hK, hAK⟩ := h ε hε
      have hcpt : IsCompact (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' K) +
          WeakDual.toStrongDual ⁻¹' closedBall 0 ε) :=
        (hK.image (inclusionInDoubleDualWeak 𝕜 E).continuous).add
          (WeakDual.isCompact_closedBall 0 ε)
      have hsub : inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' A) ⊆
          inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' K) +
            WeakDual.toStrongDual ⁻¹' closedBall 0 ε := by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        obtain ⟨y, hy, hxy⟩ := hAK x hx
        refine ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, StrongDual.toWeakDual (J (x - y)), ?_, ?_⟩
        · rw [mem_preimage, StrongDual.toStrongDual_toWeakDual,
            mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))]
          exact (double_dual_bound 𝕜 E (x - y)).trans hxy
        · apply WeakDual.toStrongDual.injective
          simp [inclusionInDoubleDualWeak_apply, J]
      obtain ⟨_, ⟨_, ⟨y, -, rfl⟩, rfl⟩, ψ, hψ, hsum⟩ :=
        closure_minimal hsub hcpt.isClosed hφ
      rw [mem_preimage, mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))] at hψ
      have hdiff : WeakDual.toStrongDual φ - J y = WeakDual.toStrongDual ψ := by
        rw [← hsum]
        ext f
        simp [inclusionInDoubleDualWeak_apply, J]
      exact ⟨y, hdiff ▸ hψ⟩
    -- The canonical image of a Banach space is norm closed in the bidual.
    have hJ : IsClosed (range J) :=
      (inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.isComplete_range.isClosed
    obtain ⟨x, hx⟩ : WeakDual.toStrongDual φ ∈ range J := by
      refine hJ.closure_subset
        ((Metric.mem_closure_iff (α := StrongDual 𝕜 (StrongDual 𝕜 E))).2 fun ε hε ↦ ?_)
      obtain ⟨y, hy⟩ := hclose (ε / 2) (half_pos hε)
      exact ⟨J y, mem_range_self y, by
        rw [dist_eq_norm (E := StrongDual 𝕜 (StrongDual 𝕜 E))]; linarith⟩
    refine ⟨toWeakSpace 𝕜 E x, WeakDual.toStrongDual.injective ?_⟩
    simpa [inclusionInDoubleDualWeak_apply, J] using hx

end TauCeti
