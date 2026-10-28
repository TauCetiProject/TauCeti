/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.Dual.Submodule
public import TauCeti.Analysis.Normed.Module.Dual.Quotient
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Reflexivity of subspaces and quotients

Closed subspaces and quotients of reflexive real or complex normed spaces are
reflexive. The statements use surjectivity of the canonical continuous bidual map.
Completeness is a consequence of reflexivity, rather than an additional hypothesis.

For a subspace, extend its bidual functional by precomposition with restriction.
The representing ambient vector lies in the subspace, since continuous functionals
on the Hausdorff quotient separate points. For a quotient, use the identification
of its dual with an annihilator and Hahn–Banach extension from that annihilator.
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
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let := hS
  intro Φ
  obtain ⟨x, hx⟩ := hE (Φ.comp (ContinuousLinearMap.precomp 𝕜 S.subtypeL))
  have hxS : x ∈ S := by
    apply (Submodule.Quotient.mk_eq_zero S).1
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜)
    intro f
    have hres : (f.comp S.mkQL).comp S.subtypeL = 0 := by
      ext y
      simp [(Submodule.Quotient.mk_eq_zero S).2 y.property]
    have h := congrArg (fun Ψ ↦ Ψ (f.comp S.mkQL)) hx
    simpa only [dual_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precomp_apply, hres, map_zero, mkQL_apply, mkQ_apply] using h
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
