/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Free.Basic

/-!
# Shifted-free coordinate transport in `GradedModuleCat`

Let `A` be a `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`), and view the finite function
module `I → A` (`[Fintype I]`) as the shifted free graded `A`-module with `j`th summand in
shift `s j : ℤ`, so its homogeneous elements of degree `d` are the tuples `v : I → A` satisfying
`∀ j, v j ∈ 𝒜 (d - s j)`.

Transporting `I → A` to `GradedModuleCat.free 𝒜 s` via `DirectSum.linearEquivFunOnFintype` gives
a coordinate membership criterion and graded endomorphisms and range objects in
`GradedModuleCat 𝒜` for any degree-zero endomorphism of `I → A`:

* `TauCeti.GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff`: tuple membership in
  the degree-`p` piece of `free 𝒜 d`.
* `TauCeti.GradedModuleCat.freeEndOfPiEnd`, `TauCeti.GradedModuleCat.rangeObjOfPiEnd`,
  `TauCeti.GradedModuleCat.rangeEquivRangeObj`: graded endomorphism and graded range object in
  `GradedModuleCat 𝒜` associated to a degree-zero endomorphism of `I → A`.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA uI

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Under `DirectSum.linearEquivFunOnFintype`, a tuple `v : I → A` lies in the degree-`p` piece
of `free 𝒜 d` exactly when its `i`-th coordinate lies in `𝒜 (p - d i)`.
This is not a simp lemma: the direct-sum and shift simp lemmas already simplify its left side. -/
theorem linearEquivFunOnFintype_symm_mem_free_piece_iff (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
    {I : Type uI} (d : I → ℤ) [Fintype I] (p : ℤ) (v : I → A) :
    dsimp% only ((DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm v ∈
      (free 𝒜 d).grading.piece p) ↔ ∀ i, v i ∈ 𝒜 (p - d i) := by
  rw [mem_free_piece_iff]
  refine forall_congr' fun i ↦ ?_
  rw [← DirectSum.linearEquivFunOnFintype_apply A, LinearEquiv.apply_symm_apply]

omit [GradedAlgebra 𝒜] in
/-- Transporting a degree-zero endomorphism of `I → A` to `GradedModuleCat.free 𝒜 s`. -/
noncomputable def freeEndOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    free 𝒜 s ⟶ free 𝒜 s :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  ofHom (eF.symm.conjRingEquiv p) <|
    LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
      rw [add_zero]
      exact (linearEquivFunOnFintype_symm_mem_free_piece_iff 𝒜 s q _).mpr
        (hhom q (eF x) ((mem_free_piece_iff 𝒜 s q x).mp hx))

/-- The underlying `A`-linear endomorphism of `freeEndOfPiEnd` is the conjugation of `p` by
`DirectSum.linearEquivFunOnFintype`. -/
theorem hom_freeEndOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    (freeEndOfPiEnd s p hhom).hom =
      ((DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm.conjRingEquiv p :
        Module.End A (free 𝒜 s)) := by
  rfl

/-- Applying `freeEndOfPiEnd` to a tuple transported by `(DirectSum.linearEquivFunOnFintype).symm`
applies `p` to the tuple. -/
@[simp]
theorem hom_freeEndOfPiEnd_apply {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    (v : I → A) :
    (freeEndOfPiEnd s p hhom).hom
      ((DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm v) =
      (DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm (p v) := by
  rw [hom_freeEndOfPiEnd]
  simp [LinearEquiv.conjRingEquiv, LinearEquiv.arrowCongrAddEquiv]

/-- The graded range object in `GradedModuleCat 𝒜` of a degree-zero endomorphism of `I → A`. -/
@[expose]
noncomputable def rangeObjOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    GradedModuleCat.{max uA uI} 𝒜 :=
  let p' := freeEndOfPiEnd s p hhom
  (free 𝒜 s).submoduleObj (LinearMap.range p'.hom) p'.isHomogeneous.isHomogeneous_range

/-- An element of `rangeObjOfPiEnd s p hhom` has degree `q` exactly when it has degree `q` in
`free 𝒜 s`. -/
theorem mem_rangeObjOfPiEnd_piece_iff {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    {q : ℤ} {x : rangeObjOfPiEnd s p hhom} :
    x ∈ (rangeObjOfPiEnd s p hhom).grading.piece q ↔
      x.val ∈ (free 𝒜 s).grading.piece q :=
  InternalGrading.mem_submodule_piece _ _ _

/-- `A`-linear identification `LinearMap.range p ≃ₗ[A] rangeObjOfPiEnd s p hhom`. -/
noncomputable def rangeEquivRangeObj {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    LinearMap.range p ≃ₗ[A] rangeObjOfPiEnd s p hhom :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := freeEndOfPiEnd s p hhom
  eF.symm.ofSubmodules (LinearMap.range p) (LinearMap.range p'.hom) <| by
    -- Align the coerced `RingEquiv` `eF.symm.conjRingEquiv p` with the linear composite.
    have hp' : p'.hom = eF.symm.toLinearMap ∘ₗ p ∘ₗ eF.toLinearMap :=
      LinearMap.ext fun _ ↦ rfl
    rw [hp', ← LinearMap.range_comp, ← LinearMap.comp_assoc, LinearEquiv.range_comp]

/-- Applying `rangeEquivRangeObj` transforms the underlying tuple by
`(DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm`. -/
@[simp]
theorem coe_rangeEquivRangeObj_apply {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    (x : LinearMap.range p) :
    (rangeEquivRangeObj s p hhom x).val =
      (DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm x.val :=
  LinearEquiv.ofSubmodules_apply _ _ x

end TauCeti.GradedModuleCat
