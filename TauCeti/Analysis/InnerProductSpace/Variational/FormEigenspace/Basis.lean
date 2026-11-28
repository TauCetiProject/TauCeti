/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.Variational.FormEigenspace.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic

/-!
# Variational eigenspaces of a Hilbert eigenbasis

For a Hilbert basis of form-domain images, each variational eigenspace is spanned by the
representatives of the basis vectors at that energy. Compactness makes each such family finite.
-/

public section

open Set Submodule
open scoped InnerProductSpace

namespace TauCeti.CompactFormPair

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (P : CompactFormPair 𝕜 V H)

/-- Each variational eigenspace is spanned by the form-domain representatives of the Hilbert
basis vectors at that eigenvalue. This also applies to finite Hilbert bases. -/
theorem formEigenspace_eq_span_of_hilbertBasis {ι : Type*}
    (b : HilbertBasis ι 𝕜 H) {u : ι → V} (hb : ⇑b = P.inclusion ∘ u)
    (heig : ∀ i, u i ∈ P.formEigenspace (P.energy (u i))) (lam : ℝ) :
    P.formEigenspace lam = span 𝕜 (u '' {i | P.energy (u i) = lam}) := by
  let t := {i | P.energy (u i) = lam}
  have hfinite : t.Finite :=
    (P.finite_setOf_energy_le_of_orthonormal (hb ▸ b.orthonormal) lam).subset fun _ hi ↦ hi.le
  refine le_antisymm (fun v hv ↦ ?_) (span_le.2 ?_)
  · have horth : P.inclusion v ∈ (span 𝕜 (b '' tᶜ))ᗮ := by
      refine (mem_orthogonalBilin_span (B := innerₛₗ 𝕜)).2 ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [innerₛₗ_apply_apply, congrFun hb i]
      exact inner_inclusion_eq_zero_of_mem_formEigenspace hi (heig i) hv
    let : FiniteDimensional 𝕜 (span 𝕜 (b '' t)) :=
      FiniteDimensional.span_of_finite 𝕜 (hfinite.image b)
    rw [b.orthogonal_span_image, compl_compl, topologicalClosure_eq_self, hb, image_comp,
      ← ContinuousLinearMap.coe_coe, ← Submodule.map_span] at horth
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 horth
    exact P.injective hwv ▸ hw
  · rintro _ ⟨i, hi, rfl⟩
    exact hi ▸ heig i

end TauCeti.CompactFormPair
