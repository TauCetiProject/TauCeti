/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The dual of a submodule

Restricting continuous linear functionals from `E` to a submodule `S` is precomposition with the
inclusion `S.subtypeL`. Its kernel is the annihilator of `S`, and by the Hahn–Banach theorem it is
surjective. Moreover, the quotient norm of a functional modulo the annihilator equals the norm of
its restriction, since a norm-preserving extension of the restriction is a representative of the
same class. Hence restriction descends to an isometric identification of the quotient of the
continuous dual of `E` by the annihilator of `S` with the continuous dual of `S`. This is the
counterpart of the identification of the dual of `E ⧸ S` with the annihilator of `S`.

The annihilator is Mathlib's `Submodule.orthogonalBilin` for `topDualPairing`. No completeness or
closedness assumption is needed, and `E` may be seminormed. The kernel computation holds over any
nontrivially normed field; surjectivity and the isometry use the Hahn–Banach theorem
`exists_extension_norm_eq`, so they are stated over fields satisfying `IsRCLikeNormedField`.
Over such fields, a vector outside a closed submodule is also separated from it by a continuous
linear functional vanishing on the submodule.

This is the standard subspace-duality theorem; see Megginson, *An Introduction to Banach Space
Theory*, §2.6. It is the continuous analogue of Mathlib's algebraic
`Subspace.quotAnnihilatorEquiv`.
-/

public section

namespace Submodule

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Restriction to a submodule kills exactly the annihilator of that submodule. -/
theorem ker_precomp_subtypeL (S : Submodule 𝕜 E) :
    (ContinuousLinearMap.precomp 𝕜 S.subtypeL).ker =
      S.orthogonalBilin (topDualPairing 𝕜 E).flip := by
  ext f
  simp [ContinuousLinearMap.ext_iff]

section HahnBanach

variable [IsRCLikeNormedField 𝕜]

/-- Every continuous linear functional on a submodule is the restriction of a continuous linear
functional on the whole space. -/
theorem surjective_precomp_subtypeL (S : Submodule 𝕜 E) :
    Function.Surjective
      (ContinuousLinearMap.precomp 𝕜 S.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 S) := by
  intro g
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq S g
  exact ⟨f, ContinuousLinearMap.ext hf⟩

/-- A vector outside a closed submodule is detected by a continuous linear functional vanishing on
the submodule. -/
theorem exists_dual_forall_mem_eq_zero_ne_zero {S : Submodule 𝕜 E} (hS : IsClosed (S : Set E))
    {x : E} (hx : x ∉ S) : ∃ f : StrongDual 𝕜 E, (∀ y ∈ S, f y = 0) ∧ f x ≠ 0 := by
  let := IsRCLikeNormedField.rclike 𝕜
  let := hS
  by_contra! h
  refine hx ((Submodule.Quotient.mk_eq_zero S).1
    (SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun f ↦ ?_))
  exact h (f.comp S.mkQL) fun y hy ↦ by simp [(Submodule.Quotient.mk_eq_zero S).2 hy]

/-- The continuous dual of a submodule is isometrically the quotient of the continuous dual of
the whole space by the annihilator of the submodule. The map sends the class of a functional to
its restriction. -/
noncomputable def quotientAnnihilatorEquivDual (S : Submodule 𝕜 E) :
    (StrongDual 𝕜 E ⧸ S.orthogonalBilin (topDualPairing 𝕜 E).flip) ≃ₗᵢ[𝕜] StrongDual 𝕜 S where
  toLinearEquiv := (quotEquivOfEq _ _ S.ker_precomp_subtypeL.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ S.surjective_precomp_subtypeL)
  norm_map' q := by
    obtain ⟨f, rfl⟩ := mkQ_surjective _ q
    simp only [mkQ_apply, LinearEquiv.trans_apply, quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.precomp_apply]
    apply le_antisymm
    · -- Any representative of the class restricts to the same functional.
      refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨g, hg, hlt⟩ := Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk f :
        StrongDual 𝕜 E ⧸ S.orthogonalBilin (topDualPairing 𝕜 E).flip) hε
      have hres : g.comp S.subtypeL = f.comp S.subtypeL := by
        have hfg := (Submodule.Quotient.eq _).mp hg
        ext x
        simpa [sub_eq_zero] using (mem_orthogonalBilin.mp hfg) x x.2
      calc
        ‖f.comp S.subtypeL‖ = ‖g.comp S.subtypeL‖ := by rw [hres]
        _ ≤ ‖g‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun x ↦ g.le_opNorm x
        _ < _ := hlt
    · -- A norm-preserving extension of the restriction represents the same class.
      obtain ⟨g, hg, hnorm⟩ := exists_extension_norm_eq S (f.comp S.subtypeL)
      have hclass : (Submodule.Quotient.mk f :
          StrongDual 𝕜 E ⧸ S.orthogonalBilin (topDualPairing 𝕜 E).flip) =
          Submodule.Quotient.mk g := by
        refine (Submodule.Quotient.eq _).mpr (mem_orthogonalBilin.mpr fun x hx ↦ ?_)
        simpa [sub_eq_zero] using (hg ⟨x, hx⟩).symm
      rw [hclass, ← hnorm]
      exact Submodule.Quotient.norm_mk_le _ g

/-- The identification of the dual of a submodule restricts a representative functional. -/
@[simp]
theorem quotientAnnihilatorEquivDual_mk (S : Submodule 𝕜 E) (f : StrongDual 𝕜 E) :
    S.quotientAnnihilatorEquivDual (Submodule.Quotient.mk f) = f.comp S.subtypeL := (rfl)

/-- The inverse identification sends the restriction of a functional to its class. -/
@[simp]
theorem quotientAnnihilatorEquivDual_symm_comp_subtypeL (S : Submodule 𝕜 E)
    (f : StrongDual 𝕜 E) :
    S.quotientAnnihilatorEquivDual.symm (f.comp S.subtypeL) = Submodule.Quotient.mk f := by
  rw [LinearIsometryEquiv.symm_apply_eq, quotientAnnihilatorEquivDual_mk]

/-- The identification of the dual of a submodule is natural under a commuting square of
continuous linear maps. The square condition says that `Ts` is the restriction of `T` to maps
from `S` to `R`; on representatives, the induced map of quotients is precomposition with `T`. -/
theorem quotientAnnihilatorEquivDual_naturality (S : Submodule 𝕜 E) (R : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (Ts : S →L[𝕜] R) (h : R.subtypeL.comp Ts = T.comp S.subtypeL)
    (f : StrongDual 𝕜 F) :
    (R.quotientAnnihilatorEquivDual (Submodule.Quotient.mk f)).comp Ts =
      S.quotientAnnihilatorEquivDual (Submodule.Quotient.mk (f.comp T)) := by
  simp only [quotientAnnihilatorEquivDual_mk, ContinuousLinearMap.comp_assoc, h]

end HahnBanach

end Submodule
