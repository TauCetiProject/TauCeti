/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.Analysis.Normed.Module.Quotient
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The dual of a quotient

Precomposition with the quotient projection identifies the continuous dual of `E ⧸ S`
isometrically with the annihilator of `S` in the continuous dual of `E`
(`Submodule.subtypeL_comp_quotientDualEquivAnnihilator`). The inverse descends
an annihilating functional to the quotient. Evaluation formulas in both directions and
naturality under commuting quotient squares make the identification usable without unfolding
its construction. In particular, restricting the adjoint of an operator `T` to the annihilator
of `S` and precomposing with the quotient-duality map gives the adjoint of `S.mkQL ∘L T`
(`Submodule.precomp_comp_subtypeL_comp_quotientDualEquivAnnihilator`). On any topological vector
space over a topological field, when `E ⧸ S` is finite-dimensional the annihilator has rank at
most the codimension of `S` (`Submodule.rank_orthogonalBilin_topDualPairing_flip_le`).

The annihilator is Mathlib's `Submodule.orthogonalBilin` for `topDualPairing`, rather than a
separate submodule construction. No completeness or closedness assumption is needed: a
quotient by a nonclosed submodule is allowed to be seminormed.

This is the standard quotient-duality theorem; see Megginson, *An Introduction to Banach Space
Theory*, §2.6. The construction uses Mathlib's `Submodule.liftQL`.
-/

public section

namespace Submodule

section Topological

universe u v

/-- The annihilator of a submodule of finite codimension has rank at most that codimension. -/
theorem rank_orthogonalBilin_topDualPairing_flip_le {𝕜 : Type u} {E : Type v}
    [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] (S : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 (E ⧸ S)] :
    Module.rank 𝕜 (S.orthogonalBilin (topDualPairing 𝕜 E).flip) ≤
      Cardinal.lift.{u} (Module.rank 𝕜 (E ⧸ S)) := by
  let i : S.orthogonalBilin (topDualPairing 𝕜 E).flip →ₗ[𝕜] StrongDual 𝕜 (E ⧸ S) :=
    { toFun f := S.liftQL f.val (mem_orthogonalBilin_iff_le_ker_flip.mp f.property)
      map_add' f g := by ext x; obtain ⟨x, rfl⟩ := S.mkQ_surjective x; rfl
      map_smul' c f := by ext x; obtain ⟨x, rfl⟩ := S.mkQ_surjective x; rfl }
  have hi : Function.Injective i := fun f g h ↦ Subtype.ext <| ContinuousLinearMap.ext fun x ↦
    congrArg (· (Submodule.Quotient.mk x)) h
  exact (LinearMap.rank_le_of_injective i hi).trans TauCeti.rank_strongDual_le

end Topological

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
  invFun f := S.liftQL f.val (mem_orthogonalBilin_iff_le_ker_flip.mp f.property)
  left_inv f := by
    ext x
    obtain ⟨x, rfl⟩ := S.mkQ_surjective x
    exact S.liftQ_apply _ x
  right_inv f := by
    apply Subtype.ext
    ext x
    exact S.liftQ_apply _ (h := mem_orthogonalBilin_iff_le_ker_flip.mp f.property) x
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

/-- Composing the quotient-duality identification with the annihilator inclusion gives the adjoint
of the quotient projection `S.mkQL`. -/
@[simp]
theorem subtypeL_comp_quotientDualEquivAnnihilator (S : Submodule 𝕜 E) :
    (S.orthogonalBilin (topDualPairing 𝕜 E).flip).subtypeL.comp
        (S.quotientDualEquivAnnihilator :
          StrongDual 𝕜 (E ⧸ S) →L[𝕜] S.orthogonalBilin (topDualPairing 𝕜 E).flip) =
      ContinuousLinearMap.precomp 𝕜 S.mkQL := by
  ext g x
  simp

/-- Restricting the adjoint of `T` to the annihilator of `S` and precomposing with the
quotient-duality identification gives the adjoint of `S.mkQL ∘L T`. -/
theorem precomp_comp_subtypeL_comp_quotientDualEquivAnnihilator {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [Module 𝕜 G] (S : Submodule 𝕜 F) (T : G →L[𝕜] F) :
    ((ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 G).comp
        (S.orthogonalBilin (topDualPairing 𝕜 F).flip).subtypeL).comp
      (S.quotientDualEquivAnnihilator :
        StrongDual 𝕜 (F ⧸ S) →L[𝕜] S.orthogonalBilin (topDualPairing 𝕜 F).flip) =
      ContinuousLinearMap.precomp 𝕜 (S.mkQL.comp T) := by
  ext g x
  simp

end Submodule
