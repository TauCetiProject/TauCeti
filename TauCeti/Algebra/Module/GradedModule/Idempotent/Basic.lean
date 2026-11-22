/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Retract
public import TauCeti.Algebra.Category.GradedModuleCat.Free.Coordinates
import Mathlib.LinearAlgebra.Projection

/-!
# Graded retracts from degree-zero idempotents on shifted free modules

Over any `ℤ`-graded `k`-algebra `A` (`𝒜 : ℤ → Submodule k A`), a degree-zero idempotent
endomorphism `p : (I → A) →ₗ[A] (I → A)` (`[Fintype I]`) exhibits
`GradedModuleCat.rangeObjOfPiEnd s p hhom` as a graded retract of `GradedModuleCat.free 𝒜 s` via
`TauCeti.retractRangeOfPiIdempotent`.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti

universe uk uA uI

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- A degree-zero idempotent `p` on `I → A` exhibits `GradedModuleCat.rangeObjOfPiEnd s p hhom`
as a graded retract of `GradedModuleCat.free 𝒜 s`. -/
@[expose]
noncomputable def retractRangeOfPiIdempotent {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    Retract (GradedModuleCat.rangeObjOfPiEnd s p hhom) (GradedModuleCat.free 𝒜 s) :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := GradedModuleCat.freeEndOfPiEnd s p hhom
  have hp' : IsIdempotentElem p'.hom :=
    IsIdempotentElem.map (show IsIdempotentElem (p : Module.End A (I → A)) from hp)
      eF.symm.conjRingEquiv
  { i := GradedModuleCat.ofHom (LinearMap.range p'.hom).subtype
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        rw [add_zero]
        exact (InternalGrading.mem_submodule_piece _ _ _).mp hx)
    r := GradedModuleCat.ofHom p'.hom.rangeRestrict
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        rw [add_zero]
        exact (InternalGrading.mem_submodule_piece _ _ _).mpr (GradedModuleCat.map_mem p' hx))
    retract := GradedModuleCat.hom_ext <| LinearMap.ext fun z ↦
      Subtype.ext ((LinearMap.IsIdempotentElem.mem_range_iff hp').mp z.property) }

end TauCeti
