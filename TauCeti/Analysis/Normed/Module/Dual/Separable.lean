/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.Basic
import TauCeti.Analysis.Normed.Module.Dual.Submodule
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# Spaces with a separable dual

A real or complex normed space whose dual is separable is itself separable. The converse fails:
`ℓ¹` is separable while its dual `ℓ^∞` is not.

Separability of the dual is the hypothesis of the theorem that separable dual spaces have the
Radon–Nikodým property. Its proof tests dual-valued functions against a countable dense subset of
the predual, whose existence is the theorem proved here.

A separable dual has a countable norming set `t` in the closed unit ball of the predual
(`TopologicalSpace.IsSeparable.exists_countable_norming`). A functional vanishing on the closed
span of `t` therefore has norm zero; by the Hahn–Banach theorem this closed span is the whole
space.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 3.26.
-/

public section

open Set TopologicalSpace

namespace TauCeti

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A real or complex normed space whose dual is separable is separable. -/
theorem separableSpace_of_separableSpace_strongDual [SeparableSpace (StrongDual 𝕜 E)] :
    SeparableSpace E := by
  obtain ⟨t, ht, htne, -, hnorm⟩ :=
    (isSeparable_univ_iff.2 ‹SeparableSpace (StrongDual 𝕜 E)›).exists_countable_norming
  set K := (Submodule.span 𝕜 t).topologicalClosure
  -- A functional vanishing on `K` vanishes on the norming set `t`, so it is zero.
  have hK : ∀ z, z ∈ K := by
    by_contra! ⟨z, hz⟩
    obtain ⟨f, hf₀, hfz⟩ :=
      Submodule.exists_dual_forall_mem_eq_zero_eq_one
        (Submodule.span 𝕜 t).isClosed_topologicalClosure hz
    have hft : (fun x ↦ ‖f x‖) '' t = {0} := by
      rw [← htne.image_const 0]
      exact image_congr fun x hx ↦ by
        simp [hf₀ x (Submodule.le_topologicalClosure _ (Submodule.subset_span hx))]
    have hf : f = 0 := norm_eq_zero.1 <| by rw [hnorm f (mem_univ f), hft, csSup_singleton]
    simp [hf] at hfz
  have hsep : IsSeparable (K : Set E) := by
    have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
    rw [Submodule.topologicalClosure_coe]
    exact ht.isSeparable.span.closure
  have hKu : (K : Set E) = univ := eq_univ_of_forall hK
  rw [hKu] at hsep
  exact isSeparable_univ_iff.1 hsep

end TauCeti
