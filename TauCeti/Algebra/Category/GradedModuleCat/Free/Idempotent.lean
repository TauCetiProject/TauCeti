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
`TauCeti.GradedModuleCat.retractRangeOfPiIdempotent`.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA uI

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- A degree-zero idempotent `p` on `I → A` exhibits `rangeObjOfPiEnd s p hhom` as a graded
retract of `free 𝒜 s`. -/
@[expose]
noncomputable def retractRangeOfPiIdempotent {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    Retract (rangeObjOfPiEnd s p hhom) (free 𝒜 s) :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := freeEndOfPiEnd s p hhom
  have hp_idem : IsIdempotentElem (p : Module.End A (I → A)) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, hp]
  have hp' : IsIdempotentElem p'.hom := by
    rw [hom_freeEndOfPiEnd]
    exact IsIdempotentElem.map hp_idem eF.symm.conjRingEquiv
  { i := submoduleι (free 𝒜 s) (LinearMap.range p'.hom) p'.isHomogeneous.isHomogeneous_range
    r := ofHom p'.hom.rangeRestrict
      (LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
        rw [add_zero]
        exact (mem_rangeObjOfPiEnd_piece_iff s p hhom).mpr (map_mem p' hx))
    retract := hom_ext <| LinearMap.ext fun z ↦
      Subtype.ext ((LinearMap.IsIdempotentElem.mem_range_iff hp').mp z.property) }

/-- The inclusion of `retractRangeOfPiIdempotent` is the subtype coercion into `free 𝒜 s`. -/
@[simp]
theorem retractRangeOfPiIdempotent_i_hom_apply {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    (x : rangeObjOfPiEnd s p hhom) :
    (retractRangeOfPiIdempotent s p hp hhom).i.hom x = x.val :=
  rfl

/-- Applying the retraction of `retractRangeOfPiIdempotent` and coercing to `free 𝒜 s` computes
`freeEndOfPiEnd`. -/
@[simp]
theorem coe_retractRangeOfPiIdempotent_r_hom_apply {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    (x : free 𝒜 s) :
    ((retractRangeOfPiIdempotent s p hp hhom).r.hom x).val =
      (freeEndOfPiEnd s p hhom).hom x :=
  rfl

/-- Composing the retraction and inclusion of `retractRangeOfPiIdempotent` recovers the transported
endomorphism `freeEndOfPiEnd`. -/
@[reassoc (attr := simp)]
theorem retractRangeOfPiIdempotent_r_comp_i {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    (retractRangeOfPiIdempotent s p hp hhom).r ≫ (retractRangeOfPiIdempotent s p hp hhom).i =
      freeEndOfPiEnd s p hhom :=
  hom_ext (LinearMap.subtype_comp_rangeRestrict _)

end TauCeti.GradedModuleCat
