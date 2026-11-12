/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Quotient
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# The dual of a quotient

Precomposition with the quotient projection identifies the continuous dual of `E ⧸ S`
isometrically with the annihilator of `S` in the continuous dual of `E`. The inverse descends
an annihilating functional to the quotient. Evaluation formulas in both directions and
naturality under commuting quotient squares make the identification usable without unfolding
its construction.

The annihilator is Mathlib's `Submodule.orthogonalBilin` for `topDualPairing`, rather than a
separate submodule construction. No completeness or closedness assumption is needed: a
quotient by a nonclosed submodule is allowed to be seminormed.

This is the standard quotient-duality theorem; see Megginson, *An Introduction to Banach Space
Theory*, §2.6. The construction uses Mathlib's `Submodule.liftQL`.
-/

public section

namespace Submodule

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The continuous dual of a quotient is isometrically the annihilator of its defining
submodule. The forward map is precomposition with the quotient projection. -/
def quotientDualEquivAnnihilator (S : Submodule 𝕜 E) :
    StrongDual 𝕜 (E ⧸ S) ≃ₗᵢ[𝕜] S.orthogonalBilin (topDualPairing 𝕜 E).flip where
  toFun f := ⟨f.comp S.mkQL, by
    intro x hx
    simp [(Submodule.Quotient.mk_eq_zero S).mpr hx]⟩
  invFun f := S.liftQL f.1 (mem_orthogonalBilin_iff_le_ker_flip.mp f.2)
  left_inv f := by
    ext x
    obtain ⟨x, rfl⟩ := S.mkQ_surjective x
    exact S.liftQ_apply _ x
  right_inv f := by
    apply Subtype.ext
    ext x
    exact S.liftQ_apply _ (h := mem_orthogonalBilin_iff_le_ker_flip.mp f.2) x
  map_add' f g := by rfl
  map_smul' c f := by rfl
  norm_map' f := S.norm_comp_mkQL f

/-- The quotient-duality map evaluates by applying the functional to the quotient class. -/
@[simp]
theorem quotientDualEquivAnnihilator_apply (S : Submodule 𝕜 E)
    (f : StrongDual 𝕜 (E ⧸ S)) (x : E) :
    (S.quotientDualEquivAnnihilator f : StrongDual 𝕜 E) x = f (Submodule.Quotient.mk x) := (rfl)

/-- The inverse quotient-duality map evaluates an annihilating functional on a representative. -/
@[simp]
theorem quotientDualEquivAnnihilator_symm_apply_mk (S : Submodule 𝕜 E)
    (f : S.orthogonalBilin (topDualPairing 𝕜 E).flip) (x : E) :
    S.quotientDualEquivAnnihilator.symm f (Submodule.Quotient.mk x) =
      (f : StrongDual 𝕜 E) x := (rfl)

/-- Forgetting the annihilator subtype recovers precomposition with the quotient projection. -/
theorem coe_quotientDualEquivAnnihilator (S : Submodule 𝕜 E)
    (f : StrongDual 𝕜 (E ⧸ S)) :
    (S.quotientDualEquivAnnihilator f : StrongDual 𝕜 E) = f.comp S.mkQL := by
  ext x
  simp

/-- The adjoint of the quotient projection has range exactly the annihilator. -/
theorem range_precomp_mkQL (S : Submodule 𝕜 E) :
    (ContinuousLinearMap.precomp 𝕜 S.mkQL).range =
      S.orthogonalBilin (topDualPairing 𝕜 E).flip := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact (S.quotientDualEquivAnnihilator g).property
  · intro hf
    refine ⟨S.quotientDualEquivAnnihilator.symm ⟨f, hf⟩, ?_⟩
    ext x
    simp

/-- Quotient duality is natural under a commuting square of continuous linear maps.
The square condition says that `Tq` is the map on quotients induced by `T`. -/
theorem quotientDualEquivAnnihilator_naturality (S : Submodule 𝕜 E) (R : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (Tq : E ⧸ S →L[𝕜] F ⧸ R)
    (h : Tq.comp S.mkQL = R.mkQL.comp T) (f : StrongDual 𝕜 (F ⧸ R)) :
    (S.quotientDualEquivAnnihilator (f.comp Tq) : StrongDual 𝕜 E) =
      (R.quotientDualEquivAnnihilator f : StrongDual 𝕜 F).comp T := by
  ext x
  simpa using congrArg (fun g : E →L[𝕜] F ⧸ R ↦ f (g x)) h

end Submodule
