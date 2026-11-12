/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.Dual.Submodule
public import TauCeti.Analysis.Normed.Module.Dual.Quotient

/-!
# Reflexivity of subspaces and quotients

Closed subspaces and quotients of reflexive real or complex normed spaces are
reflexive. The statements use surjectivity of the canonical continuous bidual map.
Completeness is a consequence of reflexivity, rather than an additional hypothesis.

For a subspace, extend its bidual functional by precomposition with restriction.
The representing ambient vector lies in the subspace, since by Hahn–Banach a vector
outside a closed subspace is detected by a continuous functional vanishing on it.
For a quotient, use the identification of its dual with an annihilator and
Hahn–Banach extension from that annihilator.
The latter proof also applies to the seminormed quotient by a nonclosed submodule.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

open Function NormedSpace

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A closed subspace of a reflexive space is reflexive. -/
theorem surjective_inclusionInDoubleDual (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E))
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) :
    Surjective (inclusionInDoubleDual 𝕜 S) := by
  intro Φ
  obtain ⟨x, hx⟩ := hE (Φ.comp (ContinuousLinearMap.precomp 𝕜 S.subtypeL))
  have hxS : x ∈ S := by
    -- Otherwise some `f` vanishing on `S` has `f x = 1`, but `hx` gives `f x = Φ 0 = 0`.
    by_contra hxS
    obtain ⟨f, hfS, hf⟩ := exists_dual_forall_mem_eq_zero_eq_one hS hxS
    have hres : f.comp S.subtypeL = 0 := ContinuousLinearMap.ext fun y ↦ hfS y y.2
    have h := congrArg (fun Ψ ↦ Ψ f) hx
    simp only [dual_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precomp_apply, hres, map_zero, hf] at h
    exact one_ne_zero h
  refine ⟨⟨x, hxS⟩, ContinuousLinearMap.ext fun f ↦ ?_⟩
  obtain ⟨g, hg⟩ := S.surjective_precomp_subtypeL f
  have h := congrArg (fun Ψ ↦ Ψ g) hx
  rw [dual_def, ← hg]
  simpa only [dual_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply, Submodule.subtypeL_apply] using h

/-- Quotients of reflexive spaces are reflexive. The quotient is allowed to be
seminormed, so the submodule need not be closed. -/
theorem surjective_inclusionInDoubleDual_quotient (S : Submodule 𝕜 E)
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) :
    Surjective (inclusionInDoubleDual 𝕜 (E ⧸ S)) := by
  intro Φ
  let A := S.orthogonalBilin (topDualPairing 𝕜 E).flip
  let e := S.quotientDualEquivAnnihilator
  obtain ⟨Ψ, hΨ, -⟩ :=
    exists_extension_norm_eq A (Φ.comp e.symm.toLinearIsometry.toContinuousLinearMap)
  obtain ⟨x, hx⟩ := hE Ψ
  refine ⟨Submodule.Quotient.mk x, ContinuousLinearMap.ext fun f ↦ ?_⟩
  have h := hΨ (e f)
  rw [← hx] at h
  simpa only [e, dual_def, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.symm_apply_apply, quotientDualEquivAnnihilator_apply] using h

end Submodule
