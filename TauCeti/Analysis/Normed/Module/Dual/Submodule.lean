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

The annihilator is Mathlib's `Submodule.orthogonalBilin` for `topDualPairing`, and the duals carry
the topology of bounded convergence. The kernel computation holds over any normed field, for any
topology on `E`. Surjectivity uses the Hahn–Banach theorem `StrongDual.exists_extension`, so it is
stated for polynormable spaces (including all seminormed spaces) over fields satisfying
`IsRCLikeNormedField`. The isometry is stated for seminormed spaces over such fields and uses the
norm-preserving Hahn–Banach theorem `exists_extension_norm_eq`; no completeness or closedness
assumption is needed. Over such fields, a vector outside a closed submodule of a seminormed space
is also sent to `1` by a continuous linear functional vanishing on the submodule.

This is the standard subspace-duality theorem; see Megginson, *An Introduction to Banach Space
Theory*, §2.6. It is the continuous analogue of Mathlib's algebraic
`Subspace.quotAnnihilatorEquiv`.
-/

public section

namespace Submodule

section Topological

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-- Restriction to a submodule kills exactly the annihilator of that submodule. -/
theorem ker_precomp_subtypeL (S : Submodule 𝕜 E) :
    (ContinuousLinearMap.precomp 𝕜 S.subtypeL).ker =
      S.orthogonalBilin (topDualPairing 𝕜 E).flip := by
  ext f
  simp [ContinuousLinearMap.ext_iff]

end Topological

section Polynormable

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [PolynormableSpace 𝕜 E]

/-- Every continuous linear functional on a submodule is the restriction of a continuous linear
functional on the whole space. -/
theorem surjective_precomp_subtypeL (S : Submodule 𝕜 E) :
    Function.Surjective
      (ContinuousLinearMap.precomp 𝕜 S.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 S) :=
  fun g ↦ (StrongDual.exists_extension S g).imp fun _ ↦ ContinuousLinearMap.ext

end Polynormable

section HahnBanach

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A vector outside a closed submodule is sent to `1` by a continuous linear functional vanishing
on the submodule. -/
theorem exists_dual_forall_mem_eq_zero_eq_one {S : Submodule 𝕜 E} (hS : IsClosed (S : Set E))
    {x : E} (hx : x ∉ S) : ∃ f : StrongDual 𝕜 E, (∀ y ∈ S, f y = 0) ∧ f x = 1 := by
  -- As `S` is closed, `E ⧸ S` is a normed space, so it has a separating dual over the `RCLike`
  -- structure of `𝕜`; a functional on it sending the class of `x` to `1` pulls back to `E`.
  let := IsRCLikeNormedField.rclike 𝕜
  obtain ⟨f, hf⟩ := SeparatingDual.exists_eq_one (R := 𝕜)
    (mt (Submodule.Quotient.mk_eq_zero S).1 hx)
  refine ⟨f.comp S.mkQL, fun y hy ↦ by simp [(Submodule.Quotient.mk_eq_zero S).2 hy], ?_⟩
  rwa [ContinuousLinearMap.comp_apply, mkQL_apply, mkQ_apply]

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
        _ ≤ ‖g‖ * ‖S.subtypeL‖ := g.opNorm_comp_le _
        _ ≤ ‖g‖ := mul_le_of_le_one_right (norm_nonneg g) S.norm_subtypeL_le
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
