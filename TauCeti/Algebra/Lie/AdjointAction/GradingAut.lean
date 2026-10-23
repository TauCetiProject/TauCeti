/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Lie.Weights.Eigenvector

/-!
# The grading automorphisms attached to an integral semisimple element

Let `L` be a Lie algebra over a commutative ring `R` and let `h ∈ L` be an element whose adjoint
action is diagonalizable with integer eigenvalues: `L` is the internal direct sum of the
eigenspaces `L(j)` of `ad h` at the integers `j`. The bracket adds eigenvalues
(`TauCeti.lie_mem_eigenspace_toEnd_add`, in `TauCeti.Algebra.Lie.Weights.Eigenvector`), so
`L = ⨁ⱼ L(j)` is a `ℤ`-graded Lie algebra, and every unit `s` of `R` defines a Lie automorphism
`TauCeti.gradingAut` of `L` acting on `L(j)` by `s ^ j`.

When `L` is the Lie algebra of an algebraic group `G` over a field of characteristic zero and `h`
is the differential of a cocharacter `λ : 𝔾ₘ → G`, the eigenspace `L(j)` is the weight space of
`Ad ∘ λ` of weight `j`, so `Ad (λ s)` acts on `L(j)` by `s ^ j`. Since the `L(j)` span `L`,
`Ad (λ s)` is the grading automorphism at `s`. This is how the adjoint action of the cocharacter
attached to an `sl₂` triple enters the geometry of nilpotent orbits, for instance in the
contracting action on a Slodowy slice (`TauCeti.Algebra.Lie.Sl2.SlodowySlice`).

## Main definitions

* `TauCeti.gradingAut hh s`: the Lie automorphism of `L` acting on `L(j)` by `s ^ j`, where
  `hh` states that the integer eigenspaces of `ad h` form an internal direct sum.

## Main results

* `TauCeti.gradingAut_apply_of_mem`: the characterizing property of `TauCeti.gradingAut`.
* `TauCeti.gradingAut_mul_apply`, `TauCeti.gradingAut_one_apply` and `TauCeti.gradingAut_symm`:
  `s ↦ gradingAut hh s` is a group homomorphism from `Rˣ` to the automorphisms of `L`.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

section Grading

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {h : L}
  (hh : DirectSum.IsInternal fun j : ℤ ↦ (ad R L h).eigenspace (j : R))

/-- The linear endomorphism of `L` acting on the `j`-eigenspace of `ad h` by `s ^ j`: decompose,
scale each component, and add the components back up. -/
private noncomputable def gradingMap (s : Rˣ) : L →ₗ[R] L :=
  DirectSum.coeLinearMap (fun j : ℤ ↦ (ad R L h).eigenspace (j : R)) ∘ₗ
    DirectSum.lmap (fun j : ℤ ↦ ((s ^ j : Rˣ) : R) • LinearMap.id) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hh).symm.toLinearMap

private theorem gradingMap_apply_of_mem (s : Rˣ) {j : ℤ} {x : L}
    (hx : x ∈ (ad R L h).eigenspace (j : R)) :
    gradingMap hh s x = ((s ^ j : Rˣ) : R) • x := by
  have hsymm : (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hh).symm x =
      DirectSum.lof R ℤ (fun j : ℤ ↦ (ad R L h).eigenspace (j : R)) j ⟨x, hx⟩ := by
    simpa using LinearEquiv.ofBijective_symm_apply_apply (DirectSum.coeLinearMap _) (h := hh)
      (DirectSum.lof R ℤ (fun j : ℤ ↦ (ad R L h).eigenspace (j : R)) j ⟨x, hx⟩)
  simp [gradingMap, hsymm]

private theorem gradingMap_gradingMap (s r : Rˣ) (x : L) :
    gradingMap hh s (gradingMap hh r x) = gradingMap hh (s * r) x := by
  refine LinearMap.congr_fun (LinearMap.ext_of_iSup_eq_top hh.submodule_iSup_eq_top
    (f := gradingMap hh s ∘ₗ gradingMap hh r) fun j y hy ↦ ?_) x
  rw [LinearMap.comp_apply, gradingMap_apply_of_mem hh r hy, map_smul,
    gradingMap_apply_of_mem hh s hy, gradingMap_apply_of_mem hh (s * r) hy]
  simp [smul_smul, mul_zpow, mul_comm]

private theorem gradingMap_one (x : L) : gradingMap hh 1 x = x :=
  LinearMap.congr_fun (LinearMap.ext_of_iSup_eq_top hh.submodule_iSup_eq_top
    (f := gradingMap hh 1) (g := LinearMap.id) fun j y hy ↦ by
      simp [gradingMap_apply_of_mem hh 1 hy]) x

/-- `gradingMap hh s` preserves brackets with an eigenvector of `ad h`. -/
private theorem gradingMap_lie_of_mem (s : Rˣ) {i : ℤ} {x : L}
    (hx : x ∈ (ad R L h).eigenspace (i : R)) (y : L) :
    gradingMap hh s ⁅x, y⁆ = ⁅gradingMap hh s x, gradingMap hh s y⁆ := by
  -- Both sides are linear in `y`, so it suffices to compare them on eigenvectors.
  refine LinearMap.congr_fun (LinearMap.ext_of_iSup_eq_top hh.submodule_iSup_eq_top
    (f := gradingMap hh s ∘ₗ ad R L x) (g := ad R L (gradingMap hh s x) ∘ₗ gradingMap hh s)
    fun j y hy ↦ ?_) y
  have hxy : ⁅x, y⁆ ∈ (ad R L h).eigenspace ((i + j : ℤ) : R) := by
    rw [ad_eq_toEnd] at hy ⊢
    rw [Int.cast_add]
    exact lie_mem_eigenspace_toEnd_add hx hy
  simp only [LinearMap.comp_apply, ad_apply]
  rw [gradingMap_apply_of_mem hh s hxy, gradingMap_apply_of_mem hh s hx,
    gradingMap_apply_of_mem hh s hy]
  simp [smul_smul, zpow_add, mul_comm]

private theorem gradingMap_lie (s : Rˣ) (x y : L) :
    gradingMap hh s ⁅x, y⁆ = ⁅gradingMap hh s x, gradingMap hh s y⁆ := by
  -- Both sides are linear in `y`; on an eigenvector `y` use antisymmetry and the previous lemma.
  refine LinearMap.congr_fun (LinearMap.ext_of_iSup_eq_top hh.submodule_iSup_eq_top
    (f := gradingMap hh s ∘ₗ ad R L x) (g := ad R L (gradingMap hh s x) ∘ₗ gradingMap hh s)
    fun j y hy ↦ ?_) y
  simp only [LinearMap.comp_apply, ad_apply]
  rw [← lie_skew, map_neg, gradingMap_lie_of_mem hh s hy, lie_skew]

/-- **The grading automorphism.** If `L` is the internal direct sum of the integer eigenspaces
`L(j)` of `ad h`, then for a unit `s` of `R` this is the Lie automorphism of `L` acting on `L(j)` by
`s ^ j`. It is characterized by `TauCeti.gradingAut_apply_of_mem`.

When `h` is the differential of a cocharacter `λ` of an algebraic group with Lie algebra `L`, this
is the adjoint action `Ad (λ s)`. -/
noncomputable def gradingAut (s : Rˣ) : L ≃ₗ⁅R⁆ L where
  __ := gradingMap hh s
  map_lie' {x y} := gradingMap_lie hh s x y
  invFun := gradingMap hh s⁻¹
  left_inv x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [gradingMap_gradingMap, inv_mul_cancel, gradingMap_one]
  right_inv x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [gradingMap_gradingMap, mul_inv_cancel, gradingMap_one]

/-- **The grading automorphism at `s` acts on the `j`-eigenspace of `ad h` by `s ^ j`.** -/
theorem gradingAut_apply_of_mem (s : Rˣ) {j : ℤ} {x : L}
    (hx : x ∈ (ad R L h).eigenspace (j : R)) :
    gradingAut hh s x = ((s ^ j : Rˣ) : R) • x :=
  gradingMap_apply_of_mem hh s hx

/-- A linear map out of `L` acting on each integer eigenspace `L(j)` of `ad h` by `s ^ j` is the
grading automorphism at `s`. -/
theorem eq_gradingAut {s : Rˣ} {φ : L →ₗ[R] L}
    (hφ : ∀ (j : ℤ) (x : L), x ∈ (ad R L h).eigenspace (j : R) → φ x = ((s ^ j : Rˣ) : R) • x) :
    φ = ((gradingAut hh s : L ≃ₗ[R] L) : L →ₗ[R] L) :=
  LinearMap.ext_of_iSup_eq_top hh.submodule_iSup_eq_top fun j x hx ↦ by
    rw [hφ j x hx, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
      gradingAut_apply_of_mem hh s hx]

/-- The grading automorphisms compose like the units: `gradingAut (s * r) = gradingAut s ∘
gradingAut r`. -/
theorem gradingAut_mul_apply (s r : Rˣ) (x : L) :
    gradingAut hh (s * r) x = gradingAut hh s (gradingAut hh r x) :=
  (gradingMap_gradingMap hh s r x).symm

/-- The grading automorphism at `1` is the identity. -/
@[simp]
theorem gradingAut_one_apply (x : L) : gradingAut hh 1 x = x :=
  gradingMap_one hh x

/-- The inverse of the grading automorphism at `s` is the grading automorphism at `s⁻¹`. -/
@[simp]
theorem gradingAut_symm (s : Rˣ) : (gradingAut hh s).symm = gradingAut hh s⁻¹ :=
  LieEquiv.ext fun x ↦ by
    rw [LieEquiv.symm_apply_eq, ← gradingAut_mul_apply, mul_inv_cancel, gradingAut_one_apply]

/-- The grading automorphisms fix `h`, which lies in the `0`-eigenspace of `ad h`. -/
@[simp]
theorem gradingAut_apply_self (s : Rˣ) : gradingAut hh s h = h := by
  have hh0 : h ∈ (ad R L h).eigenspace ((0 : ℤ) : R) := by
    simp
  rw [gradingAut_apply_of_mem hh s hh0, zpow_zero, Units.val_one, one_smul]

end Grading

end TauCeti
