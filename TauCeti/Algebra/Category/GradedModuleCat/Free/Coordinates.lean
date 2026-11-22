/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
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
* `TauCeti.GradedModuleCat.homogeneous_of_apply_eq_smul`: a rank-one endomorphism
  `v ↦ v i₀ • w` with `∀ j, w j ∈ 𝒜 (s i₀ - s j)` is homogeneous of degree zero on the shifted
  free module `I → A`.
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
@[expose]
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

/-- The graded range object in `GradedModuleCat 𝒜` of a degree-zero endomorphism of `I → A`. -/
@[expose]
noncomputable def rangeObjOfPiEnd {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    GradedModuleCat.{max uA uI} 𝒜 :=
  let _ := (free 𝒜 s).gradedSMul
  let p' := freeEndOfPiEnd s p hhom
  { carrier := LinearMap.range p'.hom
    isAddCommGroup := Submodule.addCommGroup _
    isModule := Submodule.module _
    isModuleBase := Submodule.module' _
    grading := (free 𝒜 s).grading.submodule (LinearMap.range p'.hom)
      p'.isHomogeneous.isHomogeneous_range
    gradedSMul := ⟨fun {_ _} _ _ ha hx ↦ by
      rw [InternalGrading.mem_submodule_piece] at hx ⊢
      exact SetLike.GradedSMul.smul_mem (B := (free 𝒜 s).grading.piece) ha hx⟩ }

/-- `A`-linear identification `LinearMap.range p ≃ₗ[A] rangeObjOfPiEnd s p hhom`. -/
noncomputable def rangeEquivRangeObj {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    LinearMap.range p ≃ₗ[A] rangeObjOfPiEnd s p hhom :=
  let eF := DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)
  let p' := freeEndOfPiEnd s p hhom
  eF.symm.ofSubmodules (LinearMap.range p) (LinearMap.range p'.hom) <| by
    dsimp [p', freeEndOfPiEnd]
    change Submodule.map eF.symm.toLinearMap (LinearMap.range p) =
      LinearMap.range (eF.symm.toLinearMap ∘ₗ p ∘ₗ eF.toLinearMap)
    rw [← LinearMap.range_comp, ← LinearMap.comp_assoc, LinearEquiv.range_comp]

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

/-- If `p v = v i₀ • w` and `∀ j, w j ∈ 𝒜 (s i₀ - s j)`, then `p` is homogeneous of degree zero on
the shifted module `I → A` with shifts `s`. -/
theorem homogeneous_of_apply_eq_smul {I : Type uI} (s : I → ℤ) {p : (I → A) →ₗ[A] (I → A)}
    (i₀ : I) {w : I → A} (hp : ∀ v, p v = v i₀ • w) (hw : ∀ j, w j ∈ 𝒜 (s i₀ - s j))
    (d : ℤ) (v : I → A) (hv : ∀ j, v j ∈ 𝒜 (d - s j)) (j : I) :
    p v j ∈ 𝒜 (d - s j) := by
  rw [hp, Pi.smul_apply, smul_eq_mul]
  simpa [sub_add_sub_cancel] using SetLike.mul_mem_graded (hv i₀) (hw j)

end TauCeti.GradedModuleCat
