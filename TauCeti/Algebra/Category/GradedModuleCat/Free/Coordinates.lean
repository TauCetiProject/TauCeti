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

* `TauCeti.GradedModuleCat.linearEquivFunOnFintype_symm_mem_free_piece_iff`,
  `TauCeti.GradedModuleCat.linearEquivFunOnFintype_trans_piCongrLeft_symm_mem_free_piece_iff`:
  tuple membership in the degree-`p` piece of `free 𝒜 d` and its reindexing along an
  equivalence.
* `TauCeti.GradedModuleCat.homogeneous_of_apply_eq_smul`: rank-one coordinatewise maps
  `v ↦ v i₀ • w` preserve shifted degree-zero homogeneity.
* `TauCeti.GradedModuleCat.freeEndOfPiEnd`, `TauCeti.GradedModuleCat.rangeObjOfPiEnd`,
  `TauCeti.GradedModuleCat.rangeEquivRangeObj`,
  `TauCeti.GradedModuleCat.mem_rangeObjOfPiEnd_piece_iff_coord`: graded endomorphism and graded
  range object in `GradedModuleCat 𝒜` associated to a degree-zero endomorphism of `I → A`.
-/

public section

open CategoryTheory _root_.DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA uI

/-- If `p v = v i₀ • w` and `∀ j, w j ∈ 𝒜 (s i₀ - s j)`, then `p` preserves shifted homogeneity
of degree zero on the shifted module `I → A` with shifts `s`. -/
theorem homogeneous_of_apply_eq_smul {A I σ : Type*} [Semiring A] [SetLike σ A]
    {𝒜 : ℤ → σ} [SetLike.GradedMul 𝒜] (s : I → ℤ) {p : (I → A) →ₗ[A] (I → A)}
    (i₀ : I) {w : I → A} (hp : ∀ v, p v = v i₀ • w) (hw : ∀ j, w j ∈ 𝒜 (s i₀ - s j))
    (d : ℤ) (v : I → A) (hv : ∀ j, v j ∈ 𝒜 (d - s j)) (j : I) :
    p v j ∈ 𝒜 (d - s j) := by
  rw [hp, Pi.smul_apply, smul_eq_mul]
  simpa [sub_add_sub_cancel] using SetLike.mul_mem_graded (hv i₀) (hw j)

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

/-- Under `(DirectSum.linearEquivFunOnFintype A α _).trans (LinearEquiv.piCongrLeft A _ e)`,
the inverse image of a tuple `u : β → A` lies in the degree-`p` piece of `free 𝒜 (d ∘ e)`
exactly when `∀ b, u b ∈ 𝒜 (p - d b)`. -/
theorem linearEquivFunOnFintype_trans_piCongrLeft_symm_mem_free_piece_iff
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
    {α β : Type*} [Fintype α] (e : α ≃ β) (d : β → ℤ) (p : ℤ) (u : β → A) :
    ((DirectSum.linearEquivFunOnFintype A α (fun _ ↦ A)).trans
      (LinearEquiv.piCongrLeft A (fun _ ↦ A) e)).symm u ∈
        (free 𝒜 (d ∘ e)).grading.piece p ↔ ∀ b, u b ∈ 𝒜 (p - d b) := by
  rw [LinearEquiv.symm_trans_apply, linearEquivFunOnFintype_symm_mem_free_piece_iff]
  simp only [LinearEquiv.piCongrLeft, LinearEquiv.symm_symm, LinearEquiv.piCongrLeft'_apply,
    Equiv.symm_symm, Function.comp_apply]
  exact e.forall_congr_right (q := fun b ↦ u b ∈ 𝒜 (p - d b))

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
  mem_submoduleObj_piece_iff (free 𝒜 s) _ _

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

/-- An element `x` of `LinearMap.range p`, transported via `rangeEquivRangeObj`, has degree `q`
in `rangeObjOfPiEnd s p hhom` exactly when its `j`-th coordinate lies in `𝒜 (q - s j)`. -/
theorem mem_rangeObjOfPiEnd_piece_iff_coord {I : Type uI} [Fintype I] (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    {q : ℤ} {x : LinearMap.range p} :
    rangeEquivRangeObj s p hhom x ∈ (rangeObjOfPiEnd s p hhom).grading.piece q ↔
      ∀ j, x.val j ∈ 𝒜 (q - s j) := by
  rw [mem_rangeObjOfPiEnd_piece_iff, coe_rangeEquivRangeObj_apply,
    linearEquivFunOnFintype_symm_mem_free_piece_iff]

end TauCeti.GradedModuleCat
