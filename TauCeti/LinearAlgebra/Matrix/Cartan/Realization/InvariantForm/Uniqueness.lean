/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.InvariantForm.Basic

import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.CentralSplitting
import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Uniqueness

/-!
# Isometric classification and central extensions of standard invariant forms

This module classifies standard invariant bilinear forms on minimal Cartan realizations up to
realization-preserving isometric equivalence and analyzes their behavior on non-minimal central
enlargements.

## Minimal realizations

On a minimal realization `R` (`R.IsMinimal`) with chosen complement `W` to `R.corootSpan`, any
standard invariant form `B` pairs `R.cartanCenter ⊓ R.corootSpan` nondegenerately against `W`,
inducing a linear equivalence `B.centerComplEquivDual hR hW` from
`↥(R.cartanCenter ⊓ R.corootSpan)` onto `Dual K W`. Using this equivalence, the nilpotent shear
`x ↦ x + δ(x)` that fixes `R.corootSpan` pointwise and shifts `w ∈ W` by the unique central coroot
`c` with `B(c, w') = -(1/2) B(w, w')` makes `W` isotropic while preserving every simple coroot `hᵢ`
and every simple root `αᵢ`. This gives an explicit realization-preserving isometric equivalence
`(ofCompl A R hW).form.IsometryEquiv B.form` (`InvariantForm.ofComplIsometryEquiv`), proving that
all standard invariant forms on minimal realizations are isometric via realization isomorphisms
(`exists_isometryEquiv_map_eq_self`, `exists_isometryEquiv_map_eq`).

## Non-minimal central enlargements

Any finite-dimensional realization splits as `H = M ⊕ Z` with `M` minimal and `Z ≤ R.cartanCenter`
(`CartanRealization.exists_isMinimal_restrict_isCompl`). Extending a minimal form on `M`
orthogonally by a nondegenerate symmetric form `Φ` on `Z` (`InvariantForm.extendOfIsCompl`) proves
that every finite-dimensional realization admits a nondegenerate standard invariant form
(`InvariantForm.exists_nondegenerate`), even when `2 |I| < finrank K H` forces Kac's `ofCompl` to be
degenerate for every complement. Over a strict ordered field (`ℚ` or `ℝ`), choosing `+I` vs. `-I`
on a nontrivial central complement `Z` yields two nondegenerate standard invariant forms linked by
no realization-preserving isometry
(`InvariantForm.exists_nondegenerate_not_isometryEquiv_of_not_isMinimal`), in contrast to
algebraically closed fields where all nondegenerate symmetric forms on `Z` are `GL(Z)`-equivalent.

## Main definitions

* `TauCeti.CartanRealization.InvariantForm.centerComplPairing`,
  `TauCeti.CartanRealization.InvariantForm.centerComplEquivDual`: the pairing between
  `R.cartanCenter ⊓ R.corootSpan` and a complement `W` to `R.corootSpan`, and the resulting linear
  equivalence with `Dual K W` on a minimal realization.
* `TauCeti.CartanRealization.InvariantForm.ofComplIsometryEquiv`: explicit realization-preserving
  isometric equivalence `(ofCompl A R hW).form.IsometryEquiv B.form` on a minimal realization.
* `TauCeti.CartanRealization.InvariantForm.extendOfIsCompl`: orthogonal extension of a form on a
  sub-realization across a central splitting `H = M ⊕ Z`, `Z ≤ R.cartanCenter`.

## Main results

* `TauCeti.CartanRealization.InvariantForm.exists_isometryEquiv_map_eq_self`,
  `TauCeti.CartanRealization.InvariantForm.exists_isometryEquiv_map_eq`: uniqueness of standard
  invariant forms on minimal realizations up to realization-compatible isometric equivalence.
* `TauCeti.CartanRealization.InvariantForm.exists_nondegenerate`: existence of a nondegenerate
  standard invariant form on any finite-dimensional realization of a finite symmetrizable datum.
* `TauCeti.CartanRealization.InvariantForm.exists_nondegenerate_not_isometryEquiv_of_not_isMinimal`:
  non-uniqueness up to realization-preserving isometry on non-minimal realizations over strict
  ordered fields.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §2.1 (Lemma 2.1 and eq. (2.1.4)) and §3.9.
-/

public section

open Module
open scoped Matrix

namespace TauCeti.CartanRealization.InvariantForm

/-! ### Uniqueness up to realization-fixing isometry on minimal realizations -/

section MinimalUniqueness

section CenterComplPairing

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : SymmetrizableDatum I} {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}

/-- The restricted pairing `↥(R.cartanCenter ⊓ R.corootSpan) →ₗ[K] Dual K W` given by `c ↦ B(c, ·)`
on any subspace `W`. -/
def centerComplPairing (B : InvariantForm A R) (W : Submodule K H) :
    ↥(R.cartanCenter ⊓ R.corootSpan) →ₗ[K] Dual K W :=
  B.form.compl₁₂ (R.cartanCenter ⊓ R.corootSpan).subtype W.subtype

@[simp]
theorem centerComplPairing_apply (B : InvariantForm A R) (W : Submodule K H)
    (c : ↥(R.cartanCenter ⊓ R.corootSpan)) (w : W) :
    B.centerComplPairing W c w = B.form c w :=
  (rfl)

/-- For any complement `W` to `R.corootSpan`, the pairing `B.centerComplPairing W` is injective
(without assuming minimality of `R` or finiteness of `I`). -/
theorem centerComplPairing_injective (B : InvariantForm A R) {W : Submodule K H}
    (hW : IsCompl R.corootSpan W) : Function.Injective (B.centerComplPairing W) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ Subtype.ext ?_
  have hker : (c : H) ∈ LinearMap.ker B.form := by
    rw [LinearMap.mem_ker]
    ext y
    have hy : y = R.corootSpan.projection W hW y + (y - R.corootSpan.projection W hW y) :=
      (add_sub_cancel _ y).symm
    rw [hy, map_add,
      B.form_eq_zero_of_mem_cartanCenter_of_mem_corootSpan c.property.1
        (Submodule.projection_apply_mem hW y),
      zero_add]
    exact LinearMap.congr_fun hc ⟨_, Submodule.sub_projection_mem hW y⟩
  exact B.disjoint_ker_form_corootSpan.le_bot ⟨hker, c.property.2⟩

end CenterComplPairing

section Fintype

variable {I K H : Type*} [Fintype I] [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : SymmetrizableDatum I} {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}

/-- On a minimal realization, `B.centerComplPairing W` is a linear equivalence
`↥(R.cartanCenter ⊓ R.corootSpan) ≃ₗ[K] Dual K W`. -/
noncomputable def centerComplEquivDual (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) :
    ↥(R.cartanCenter ⊓ R.corootSpan) ≃ₗ[K] Dual K W :=
  have := hR.finiteDimensional
  (B.centerComplPairing W).linearEquivOfInjective (B.centerComplPairing_injective hW) <| by
    have hmin := R.isMinimal_iff.mp hR
    have hcompl := Submodule.finrank_add_eq_of_isCompl hW
    rw [R.finrank_corootSpan] at hcompl
    have hcent := R.finrank_cartanCenter_inf_corootSpan_add_rank
    rw [Subspace.dual_finrank_eq]
    omega

@[simp]
theorem centerComplEquivDual_apply (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W)
    (c : ↥(R.cartanCenter ⊓ R.corootSpan)) (w : W) :
    B.centerComplEquivDual hR hW c w = B.form c w := by
  have := hR.finiteDimensional
  rw [centerComplEquivDual, LinearMap.linearEquivOfInjective_apply, centerComplPairing_apply]

@[simp]
theorem form_centerComplEquivDual_symm_left (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (φ : Dual K W) (w : W) :
    B.form ((B.centerComplEquivDual hR hW).symm φ : H) w = φ w := by
  rw [← B.centerComplEquivDual_apply hR hW, LinearEquiv.apply_symm_apply]

@[simp]
theorem form_centerComplEquivDual_symm_right (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (w : W) (φ : Dual K W) :
    B.form w ((B.centerComplEquivDual hR hW).symm φ : H) = φ w := by
  rw [B.isSymm.eq, B.form_centerComplEquivDual_symm_left hR hW]

/-- Nilpotent endomorphism shifting `W` into `R.cartanCenter ⊓ R.corootSpan` so as to make `W`
isotropic under `B.form`. -/
private noncomputable def complShiftMap (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) : H →ₗ[K] H :=
  (R.cartanCenter ⊓ R.corootSpan).subtype ∘ₗ
    (B.centerComplEquivDual hR hW).symm.toLinearMap ∘ₗ
    (-(2 : K)⁻¹ • B.form.restrict W) ∘ₗ
    W.projectionOnto R.corootSpan hW.symm

private theorem complShiftMap_mem (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x : H) :
    B.complShiftMap hR hW x ∈ R.cartanCenter ⊓ R.corootSpan :=
  SetLike.coe_mem _

private theorem complShiftMap_of_mem_corootSpan (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) {x : H} (hx : x ∈ R.corootSpan) :
    B.complShiftMap hR hW x = 0 := by
  rw [complShiftMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_right hW.symm hx, map_zero, map_zero, map_zero]

private theorem complShiftMap_comp_self (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x : H) :
    B.complShiftMap hR hW (B.complShiftMap hR hW x) = 0 :=
  B.complShiftMap_of_mem_corootSpan hR hW (B.complShiftMap_mem hR hW x).2

private theorem form_complShiftMap_compl (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (z : H) (w : W) :
    B.form (B.complShiftMap hR hW z) w =
      -(2 : K)⁻¹ * B.form (z - R.corootSpan.projection W hW z) w := by
  have hproj : W.projectionOnto R.corootSpan hW.symm z =
      ⟨z - R.corootSpan.projection W hW z, Submodule.sub_projection_mem hW z⟩ := by
    apply Subtype.ext
    simp [Submodule.coe_projectionOnto_apply, Submodule.projection_eq_self_sub_projection hW.symm]
  simp [complShiftMap, hproj, LinearMap.BilinForm.restrict_apply]

private theorem form_add_complShiftMap (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x y : H) :
    B.form (x + B.complShiftMap hR hW x) (y + B.complShiftMap hR hW y) =
      (ofCompl A R hW).form x y := by
  set δx := B.complShiftMap hR hW x
  set δy := B.complShiftMap hR hW y
  set hx := R.corootSpan.projection W hW x
  set hy := R.corootSpan.projection W hW y
  have hhx : hx ∈ R.corootSpan := Submodule.projection_apply_mem hW x
  have hhy : hy ∈ R.corootSpan := Submodule.projection_apply_mem hW y
  set wx : W := ⟨x - hx, Submodule.sub_projection_mem hW x⟩
  set wy : W := ⟨y - hy, Submodule.sub_projection_mem hW y⟩
  have hcx : δx ∈ R.cartanCenter ⊓ R.corootSpan := B.complShiftMap_mem hR hW x
  have hcy : δy ∈ R.cartanCenter ⊓ R.corootSpan := B.complShiftMap_mem hR hW y
  have hpair_xy : B.form δx wy = -(2 : K)⁻¹ * B.form wx wy :=
    B.form_complShiftMap_compl hR hW x wy
  have hpair_yx : B.form wx δy = -(2 : K)⁻¹ * B.form wx wy := by
    rw [B.isSymm.eq, B.form_complShiftMap_compl hR hW y wx, B.isSymm.eq (wy : H) (wx : H)]
  obtain ⟨ux, hux⟩ : ∃ u : H, u = (wx : H) + δx := ⟨_, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ u : H, u = (wy : H) + δy := ⟨_, rfl⟩
  have hw_orth : B.form ux uy = 0 := by
    simp only [hux, huy, map_add, LinearMap.add_apply]
    rw [hpair_xy, hpair_yx, B.form_eq_zero_of_mem_cartanCenter_inf_corootSpan hcx hcy]
    linear_combination -B.form wx wy * mul_inv_cancel₀ (two_ne_zero (α := K))
  have h_hx_uy : B.form hx uy = (ofCompl A R hW).form hx wy := by
    rw [huy, map_add, B.form_eq_zero_of_mem_corootSpan_of_mem_cartanCenter hhx hcy.1, add_zero,
      form_eq_of_mem_corootSpan_left B (ofCompl A R hW) hhx]
  have h_ux_hy : B.form ux hy = (ofCompl A R hW).form wx hy := by
    rw [hux, map_add, LinearMap.add_apply,
      B.form_eq_zero_of_mem_cartanCenter_of_mem_corootSpan hcx.1 hhy, add_zero,
      form_eq_of_mem_corootSpan_right B (ofCompl A R hW) _ hhy]
  have hx1 : x = hx + wx := (add_sub_cancel hx x).symm
  have hy1 : y = hy + wy := (add_sub_cancel hy y).symm
  have hx2 : x + δx = hx + ux := by rw [hux, ← add_assoc, ← hx1]
  have hy2 : y + δy = hy + uy := by rw [huy, ← add_assoc, ← hy1]
  conv_lhs => rw [hx2, hy2]
  conv_rhs => rw [hx1, hy1]
  simp only [map_add, LinearMap.add_apply]
  rw [hw_orth, h_hx_uy, h_ux_hy, form_eq_of_mem_corootSpan_left B (ofCompl A R hW) hhx,
    ofCompl_form_eq_zero hW wx.property wy.property]

/-- On a minimal realization, any standard invariant form `B` is isometric to `ofCompl A R hW`
via an explicit nilpotent shear `x ↦ x + δ(x)` fixing `R.corootSpan` pointwise and shifting `W` by
values in `R.cartanCenter ⊓ R.corootSpan`. -/
noncomputable def ofComplIsometryEquiv (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) :
    (ofCompl A R hW).form.IsometryEquiv B.form where
  toFun x := x + B.complShiftMap hR hW x
  map_add' x y := by rw [map_add]; abel
  map_smul' c x := by simp [smul_add]
  invFun x := x - B.complShiftMap hR hW x
  left_inv x := by
    dsimp only
    rw [map_add, B.complShiftMap_comp_self hR hW, add_zero, add_sub_cancel_right]
  right_inv x := by
    dsimp only
    rw [map_sub, B.complShiftMap_comp_self hR hW, sub_zero, sub_add_cancel]
  map_app' := B.form_add_complShiftMap hR hW

private theorem ofComplIsometryEquiv_apply_eq (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x : H) :
    B.ofComplIsometryEquiv hR hW x = x + B.complShiftMap hR hW x := (rfl)

private theorem ofComplIsometryEquiv_symm_apply_eq (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x : H) :
    (B.ofComplIsometryEquiv hR hW).symm x = x - B.complShiftMap hR hW x := (rfl)

/-- `ofComplIsometryEquiv` fixes `R.corootSpan` pointwise. -/
theorem ofComplIsometryEquiv_apply_of_mem_corootSpan (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) {x : H} (hx : x ∈ R.corootSpan) :
    B.ofComplIsometryEquiv hR hW x = x := by
  rw [ofComplIsometryEquiv_apply_eq, B.complShiftMap_of_mem_corootSpan hR hW hx, add_zero]

/-- `(ofComplIsometryEquiv).symm` fixes `R.corootSpan` pointwise. -/
theorem ofComplIsometryEquiv_symm_apply_of_mem_corootSpan (B : InvariantForm A R)
    (hR : R.IsMinimal) {W : Submodule K H} (hW : IsCompl R.corootSpan W) {x : H}
    (hx : x ∈ R.corootSpan) :
    (B.ofComplIsometryEquiv hR hW).symm x = x := by
  rw [ofComplIsometryEquiv_symm_apply_eq, B.complShiftMap_of_mem_corootSpan hR hW hx, sub_zero]

/-- On `w : W`, `ofComplIsometryEquiv` adds the unique element `c ∈ R.cartanCenter ⊓ R.corootSpan`
satisfying `B(c, w') = -(1/2) B(w, w')` for all `w' ∈ W`. -/
theorem ofComplIsometryEquiv_apply_compl (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (w : W) :
    B.ofComplIsometryEquiv hR hW w =
      (w : H) + ((B.centerComplEquivDual hR hW).symm (-(2 : K)⁻¹ • B.form.restrict W w) : H) := by
  rw [ofComplIsometryEquiv_apply_eq]
  simp [complShiftMap, Submodule.projectionOnto_apply_left hW.symm w]

/-- On `w : W`, `(ofComplIsometryEquiv).symm` subtracts the unique element
`c ∈ R.cartanCenter ⊓ R.corootSpan` satisfying `B(c, w') = -(1/2) B(w, w')` for all `w' ∈ W`. -/
theorem ofComplIsometryEquiv_symm_apply_compl (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (w : W) :
    (B.ofComplIsometryEquiv hR hW).symm w =
      (w : H) - ((B.centerComplEquivDual hR hW).symm (-(2 : K)⁻¹ • B.form.restrict W w) : H) := by
  rw [ofComplIsometryEquiv_symm_apply_eq]
  simp [complShiftMap, Submodule.projectionOnto_apply_left hW.symm w]

/-- Every vector is shifted by `ofComplIsometryEquiv` only along `R.cartanCenter ⊓ R.corootSpan`. -/
theorem ofComplIsometryEquiv_sub_mem (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) (x : H) :
    B.ofComplIsometryEquiv hR hW x - x ∈ R.cartanCenter ⊓ R.corootSpan := by
  rw [ofComplIsometryEquiv_apply_eq, add_sub_cancel_left]
  exact B.complShiftMap_mem hR hW x

/-- `ofComplIsometryEquiv` preserves every simple coroot and every simple root of `R`. -/
@[simp]
theorem map_ofComplIsometryEquiv (B : InvariantForm A R) (hR : R.IsMinimal)
    {W : Submodule K H} (hW : IsCompl R.corootSpan W) :
    R.map (B.ofComplIsometryEquiv hR hW).toLinearEquiv = R := by
  apply CartanRealization.ext
  · intro i
    rw [map_coroot]
    exact B.ofComplIsometryEquiv_apply_of_mem_corootSpan hR hW (R.coroot_mem_corootSpan i)
  · intro i
    ext h
    rw [map_root_apply, LinearMap.BilinForm.IsometryEquiv.coe_symm_toLinearEquiv,
      ofComplIsometryEquiv_symm_apply_eq, map_sub,
      (R.mem_cartanCenter_iff _).mp (B.complShiftMap_mem hR hW h).1 i, sub_zero]

/-- **Uniqueness of the standard invariant form on a minimal realization**: any two standard
invariant forms `B₁, B₂` on a minimal realization `R` are linked by an isometric equivalence
fixing every simple coroot and every simple root. -/
theorem exists_isometryEquiv_map_eq_self (hR : R.IsMinimal) (B₁ B₂ : InvariantForm A R) :
    ∃ e : B₁.form.IsometryEquiv B₂.form, R.map e.toLinearEquiv = R := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl R.corootSpan
  let e₁ := B₁.ofComplIsometryEquiv hR hW
  let e₂ := B₂.ofComplIsometryEquiv hR hW
  refine ⟨e₁.symm.trans e₂, ?_⟩
  rw [LinearMap.BilinForm.IsometryEquiv.toLinearEquiv_trans,
    LinearMap.BilinForm.IsometryEquiv.toLinearEquiv_symm,
    ← CartanRealization.map_trans,
    (R.map_symm_eq_iff _).mpr (B₁.map_ofComplIsometryEquiv hR hW),
    B₂.map_ofComplIsometryEquiv hR hW]

/-- Between any two minimal realizations `R` and `S` of the same symmetrizable datum `A`, any
standard invariant form on `R` and any standard invariant form on `S` are linked by a compatible
isometric equivalence. -/
theorem exists_isometryEquiv_map_eq {H' : Type*} [AddCommGroup H'] [Module K H']
    {S : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H'} (hR : R.IsMinimal)
    (hS : S.IsMinimal) (B₁ : InvariantForm A R) (B₂ : InvariantForm A S) :
    ∃ e : B₁.form.IsometryEquiv B₂.form, R.map e.toLinearEquiv = S := by
  obtain ⟨f, rfl⟩ := hR.exists_map_eq hS
  obtain ⟨g, hg⟩ := exists_isometryEquiv_map_eq_self hS (B₁.map f) B₂
  refine ⟨(B₁.isometryEquivMap f).trans g, ?_⟩
  rw [LinearMap.BilinForm.IsometryEquiv.toLinearEquiv_trans, B₁.isometryEquivMap_toLinearEquiv,
    ← CartanRealization.map_trans, hg]

end Fintype

end MinimalUniqueness

/-! ### Central enlargements: existence and non-uniqueness -/

section CentralEnlargement

section

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : SymmetrizableDatum I} {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}

/-- Extend a standard invariant form `BM` on a sub-realization `R.restrict M hc hs` across a
central direct-sum decomposition `H = M ⊕ Z` (`Z ≤ R.cartanCenter`) by an orthogonal symmetric
bilinear form `Φ` on `Z`. -/
noncomputable def extendOfIsCompl {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) : InvariantForm A R where
  form := (LinearMap.BilinForm.prod BM.form Φ).congr (Submodule.prodEquivOfIsCompl M Z hMZ)
  isSymm := ⟨fun x y ↦ (LinearMap.BilinForm.isSymm_prod_iff.mpr ⟨BM.isSymm, hΦ⟩).eq _ _⟩
  form_coroot i h := by
    set e := Submodule.prodEquivOfIsCompl M Z hMZ
    have hcor_sub : (⟨R.coroot i, hc (R.coroot_mem_corootSpan i)⟩ : M) =
        (R.restrict M hc hs).coroot i :=
      Subtype.ext (R.coe_restrict_coroot M hc hs i).symm
    have hcor : e.symm (R.coroot i) = ((R.restrict M hc hs).coroot i, 0) := by
      rw [← hcor_sub]
      exact Submodule.prodEquivOfIsCompl_symm_apply_left M Z hMZ
        ⟨R.coroot i, hc (R.coroot_mem_corootSpan i)⟩
    have hh : h = ((e.symm h).1 : H) + ((e.symm h).2 : H) := by
      simpa [e] using (e.apply_symm_apply h).symm
    have hz : R.root i ((e.symm h).2 : H) = 0 :=
      (R.mem_cartanCenter_iff _).mp (hZ (e.symm h).2.property) i
    simp only [LinearMap.BilinForm.congr_apply, hcor, LinearMap.BilinForm.prod_apply,
      map_zero, LinearMap.zero_apply, add_zero, BM.form_coroot, restrict_root_apply]
    conv_rhs => rw [hh, map_add, hz, add_zero]

theorem extendOfIsCompl_form {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) :
    (BM.extendOfIsCompl hMZ hZ hΦ).form =
      (LinearMap.BilinForm.prod BM.form Φ).congr (Submodule.prodEquivOfIsCompl M Z hMZ) :=
  (rfl)

@[simp]
theorem extendOfIsCompl_form_apply_left {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) (m₁ m₂ : M) :
    (BM.extendOfIsCompl hMZ hZ hΦ).form m₁ m₂ = BM.form m₁ m₂ := by
  simp [extendOfIsCompl_form, Submodule.prodEquivOfIsCompl_symm_apply_left M Z hMZ]

@[simp]
theorem extendOfIsCompl_form_apply_right {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) (z₁ z₂ : Z) :
    (BM.extendOfIsCompl hMZ hZ hΦ).form z₁ z₂ = Φ z₁ z₂ := by
  simp [extendOfIsCompl_form, Submodule.prodEquivOfIsCompl_symm_apply_right M Z hMZ]

@[simp]
theorem extendOfIsCompl_form_apply_mixed {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) (m : M) (z : Z) :
    (BM.extendOfIsCompl hMZ hZ hΦ).form m z = 0 := by
  simp [extendOfIsCompl_form, Submodule.prodEquivOfIsCompl_symm_apply_left M Z hMZ,
    Submodule.prodEquivOfIsCompl_symm_apply_right M Z hMZ]

@[simp]
theorem extendOfIsCompl_form_apply_mixed' {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) (z : Z) (m : M) :
    (BM.extendOfIsCompl hMZ hZ hΦ).form z m = 0 := by
  rw [(BM.extendOfIsCompl hMZ hZ hΦ).isSymm.eq, BM.extendOfIsCompl_form_apply_mixed hMZ hZ hΦ]

@[simp]
theorem restrict_extendOfIsCompl {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) :
    (BM.extendOfIsCompl hMZ hZ hΦ).restrict M hc hs = BM := by
  ext m₁ m₂
  simp

@[simp]
theorem nondegenerate_extendOfIsCompl_iff {M Z : Submodule K H} {hc : R.corootSpan ≤ M}
    {hs : M ⊔ R.cartanCenter = ⊤} (BM : InvariantForm A (R.restrict M hc hs))
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Φ : LinearMap.BilinForm K Z}
    (hΦ : Φ.IsSymm) :
    (BM.extendOfIsCompl hMZ hZ hΦ).form.Nondegenerate ↔
      BM.form.Nondegenerate ∧ Φ.Nondegenerate := by
  simp [extendOfIsCompl_form]

/-- Every finite-dimensional realization of a finite symmetrizable datum over a characteristic-zero
field admits a **nondegenerate** standard invariant form. -/
theorem exists_nondegenerate [Finite I] [FiniteDimensional K H] (A : SymmetrizableDatum I)
    (R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H) :
    ∃ B : InvariantForm A R, B.form.Nondegenerate := by
  let := Fintype.ofFinite I
  obtain ⟨M, Z, hc, hs, hMmin, hMZ, hZ⟩ := R.exists_isMinimal_restrict_isCompl
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (R.restrict M hc hs).corootSpan
  let BM := ofCompl A (R.restrict M hc hs) hW
  let b := Module.finBasis K Z
  have hΦ : (Matrix.toBilin b (1 : Matrix _ _ K)).IsSymm :=
    (Matrix.isSymm_toBilin_iff_isSymm b).mpr Matrix.isSymm_one
  exact ⟨BM.extendOfIsCompl hMZ hZ hΦ,
    (BM.nondegenerate_extendOfIsCompl_iff hMZ hZ hΦ).mpr
      ⟨BM.nondegenerate_of_isMinimal hMmin, Matrix.nondegenerate_toBilin_one b⟩⟩

end

/-- When `M` is a minimal sub-realization and `Ψ` is nonpositive on a central complement `Z`, the
orthogonal extension `BM.extendOfIsCompl hMZ hZ hΨ` is nonpositive on the **entire** Cartan center
`R.cartanCenter` (because the `M`-component of any central vector lies in the isotropic subspace
`R.cartanCenter ⊓ R.corootSpan`). -/
theorem extendOfIsCompl_form_self_nonpos_of_mem_cartanCenter
    {I K H : Type*} [Fintype I] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] {A : SymmetrizableDatum I}
    {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}
    {M Z : Submodule K H} {hc : R.corootSpan ≤ M} {hs : M ⊔ R.cartanCenter = ⊤}
    (BM : InvariantForm A (R.restrict M hc hs)) (hMmin : (R.restrict M hc hs).IsMinimal)
    (hMZ : IsCompl M Z) (hZ : Z ≤ R.cartanCenter) {Ψ : LinearMap.BilinForm K Z}
    (hΨ : Ψ.IsSymm) (hΨ_nonpos : ∀ z : Z, Ψ z z ≤ 0) {x : H} (hx : x ∈ R.cartanCenter) :
    (BM.extendOfIsCompl hMZ hZ hΨ).form x x ≤ 0 := by
  set p := (Submodule.prodEquivOfIsCompl M Z hMZ).symm x
  have hp_eq : x = (p.1 : H) + (p.2 : H) := by
    simpa [p] using ((Submodule.prodEquivOfIsCompl M Z hMZ).apply_symm_apply x).symm
  have hp1_cent : (p.1 : H) ∈ R.cartanCenter := by
    have hsub : (p.1 : H) = x - (p.2 : H) := eq_sub_of_add_eq hp_eq.symm
    rw [hsub]
    exact R.cartanCenter.sub_mem hx (hZ p.2.property)
  have hp1_cor : (p.1 : H) ∈ R.corootSpan :=
    (R.isMinimal_restrict_iff M hc hs).mp hMmin ⟨hp1_cent, p.1.property⟩
  have hp1_iso : (BM.extendOfIsCompl hMZ hZ hΨ).form (p.1 : H) (p.1 : H) = 0 :=
    (BM.extendOfIsCompl hMZ hZ hΨ).form_eq_zero_of_mem_cartanCenter_inf_corootSpan
      ⟨hp1_cent, hp1_cor⟩ ⟨hp1_cent, hp1_cor⟩
  rw [hp_eq, (BM.extendOfIsCompl hMZ hZ hΨ).isSymm.apply_add_self, hp1_iso,
    BM.extendOfIsCompl_form_apply_mixed hMZ hZ hΨ, BM.extendOfIsCompl_form_apply_right hMZ hZ hΨ]
  linarith [hΨ_nonpos p.2]

/-- **Non-uniqueness on non-minimal realizations**: over a strict ordered field (such as `ℚ` or
`ℝ`), every non-minimal finite-dimensional realization of a finite symmetrizable datum admits two
nondegenerate standard invariant forms that are **not** linked by any realization-preserving
isometric equivalence. (Over an algebraically closed field such as `ℂ`, by contrast, all
nondegenerate symmetric forms on the central complement `Z` are `GL(Z)`-equivalent.) -/
theorem exists_nondegenerate_not_isometryEquiv_of_not_isMinimal
    {I K H : Type*} [Fintype I] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (A : SymmetrizableDatum I) {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}
    (hR : ¬ R.IsMinimal) :
    ∃ B₁ B₂ : InvariantForm A R, B₁.form.Nondegenerate ∧ B₂.form.Nondegenerate ∧
      ¬ ∃ e : B₁.form.IsometryEquiv B₂.form, R.map e.toLinearEquiv = R := by
  obtain ⟨M, Z, hc, hs, hMmin, hMZ, hZ⟩ := R.exists_isMinimal_restrict_isCompl
  -- Non-minimality forces the central complement `Z` to have positive dimension.
  have hZpos : 0 < finrank K Z := by
    have h1 := R.finrank_complement_of_isMinimal_restrict hc hs hMmin hMZ
    have h2 := R.two_mul_card_le_rank_add_finrank
    have h3 : finrank K H + (A.cartan.map (Int.cast : ℤ → K)).rank ≠ 2 * Fintype.card I :=
      mt R.isMinimal_iff.mpr hR
    have h4 := (A.cartan.map (Int.cast : ℤ → K)).rank_le_card_width
    omega
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (R.restrict M hc hs).corootSpan
  let BM := ofCompl A (R.restrict M hc hs) hW
  let b := Module.finBasis K Z
  have hΦ : (Matrix.toBilin b (1 : Matrix _ _ K)).IsSymm :=
    (Matrix.isSymm_toBilin_iff_isSymm b).mpr Matrix.isSymm_one
  let B₁ := BM.extendOfIsCompl hMZ hZ hΦ
  let B₂ := BM.extendOfIsCompl hMZ hZ hΦ.neg
  refine ⟨B₁, B₂,
    (BM.nondegenerate_extendOfIsCompl_iff hMZ hZ hΦ).mpr
      ⟨BM.nondegenerate_of_isMinimal hMmin, Matrix.nondegenerate_toBilin_one b⟩,
    (BM.nondegenerate_extendOfIsCompl_iff hMZ hZ hΦ.neg).mpr
      ⟨BM.nondegenerate_of_isMinimal hMmin,
        TauCeti.BilinForm.nondegenerate_neg_iff.mpr (Matrix.nondegenerate_toBilin_one b)⟩,
    fun ⟨e, he⟩ ↦ ?_⟩
  let z₀ : Z := b ⟨0, hZpos⟩
  have hz₀_val : B₁.form (z₀ : H) (z₀ : H) = 1 := by
    rw [BM.extendOfIsCompl_form_apply_right hMZ hZ, Matrix.toBilin_apply_basis,
      Matrix.one_apply_eq]
  have hez₀ : e (z₀ : H) ∈ R.cartanCenter := by
    have hmem : e (z₀ : H) ∈ R.cartanCenter.map e.toLinearEquiv.toLinearMap :=
      Submodule.mem_map_of_mem (hZ z₀.property)
    rwa [← R.cartanCenter_map e.toLinearEquiv, he] at hmem
  have hΨ_nonpos (z : Z) : (-Matrix.toBilin b (1 : Matrix _ _ K)) z z ≤ 0 := by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, Left.neg_nonpos_iff]
    exact Matrix.toBilin_one_apply_self_nonneg b z
  have hB₂_nonpos : B₂.form (e (z₀ : H)) (e (z₀ : H)) ≤ 0 :=
    BM.extendOfIsCompl_form_self_nonpos_of_mem_cartanCenter hMmin hMZ hZ _ hΨ_nonpos hez₀
  linarith [(e.map_app z₀ z₀).trans hz₀_val]

end CentralEnlargement

end TauCeti.CartanRealization.InvariantForm

end

/-! ### Worked examples and negative controls -/

section Examples

open Module Matrix TauCeti TauCeti.CartanRealization

private def affineA1Datum : SymmetrizableDatum (Fin 2) where
  cartan := !![2, -2; -2, 2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_two]
      zero_comm := by simp [Fin.forall_fin_two] }
  symmetrizer := 1
  symmetrizer_pos := by decide
  symmetrizes := by decide

/-- Minimal realization of affine `A₁⁽¹⁾` on `ℚ³` with `h₀ = e₀`, `h₁ = e₁`, and scaling element
`d = e₂` (`α₀(d) = 1`, `α₁(d) = 0`). -/
private noncomputable def affineA1Realization :
    CartanRealization (affineA1Datum.cartan.map (Int.cast : ℤ → ℚ)) (Fin 3 → ℚ) where
  coroot := ![Pi.single 0 1, Pi.single 1 1]
  root := ![(2 : ℚ) • LinearMap.proj 0 - (2 : ℚ) • LinearMap.proj 1 + LinearMap.proj 2,
    -(2 : ℚ) • LinearMap.proj 0 + (2 : ℚ) • LinearMap.proj 1]
  coroot_linearIndependent := Fintype.linearIndependent_iff.mpr fun c hc i ↦ by
    have h0 := congrFun hc 0; have h1 := congrFun hc 1
    simp [Fin.sum_univ_two] at h0 h1
    fin_cases i <;> simp [h0, h1]
  root_linearIndependent := Fintype.linearIndependent_iff.mpr fun c hc i ↦ by
    have h2 := LinearMap.congr_fun hc (Pi.single 2 1)
    have h0 := LinearMap.congr_fun hc (Pi.single 0 1)
    simp [Fin.sum_univ_two] at h2 h0
    have h1 : c 1 = 0 := by linarith
    fin_cases i <;> simp [h2, h1]
  root_coroot i j := by fin_cases i <;> fin_cases j <;> simp [affineA1Datum]

private theorem isMinimal_affineA1Realization : affineA1Realization.IsMinimal := by
  rw [affineA1Realization.isMinimal_iff_cartanCenter_le_corootSpan]
  intro x hx
  have hx2 : x 2 = 0 := by
    have h0 := (affineA1Realization.mem_cartanCenter_iff x).mp hx 0
    have h1 := (affineA1Realization.mem_cartanCenter_iff x).mp hx 1
    simp [affineA1Realization] at h0 h1; linarith
  have hx_eq : x = x 0 • affineA1Realization.coroot 0 + x 1 • affineA1Realization.coroot 1 := by
    ext k; fin_cases k <;> simp [affineA1Realization, hx2]
  exact hx_eq ▸ add_mem (Submodule.smul_mem _ _ (affineA1Realization.coroot_mem_corootSpan 0))
    (Submodule.smul_mem _ _ (affineA1Realization.coroot_mem_corootSpan 1))

private theorem isCompl_affineA1_span (a : ℚ) :
    IsCompl affineA1Realization.corootSpan
      (Submodule.span ℚ {Pi.single 2 (1 : ℚ) + a • affineA1Realization.coroot 0}) := by
  refine IsCompl.of_eq (eq_bot_iff.mpr ?_) (eq_top_iff.mpr fun x _ ↦ ?_)
  · rintro x ⟨hxc, hxw⟩
    obtain ⟨u, rfl⟩ := (affineA1Realization.mem_corootSpan_iff x).mp hxc
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hxw
    have ht0 : t = 0 := by
      simpa [corootMap_apply, Fin.sum_univ_two, affineA1Realization] using congrFun ht 2
    simpa [ht0] using ht.symm
  · set w := Pi.single 2 (1 : ℚ) + a • affineA1Realization.coroot 0
    have hx : x = ((x 0 - a * x 2) • affineA1Realization.coroot 0 +
        x 1 • affineA1Realization.coroot 1) + x 2 • w :=
      calc
        x = x 0 • affineA1Realization.coroot 0 + x 1 • affineA1Realization.coroot 1 +
            x 2 • Pi.single 2 (1 : ℚ) := by
          ext k; fin_cases k <;> simp [affineA1Realization]
        _ = ((x 0 - a * x 2) • affineA1Realization.coroot 0 +
            x 1 • affineA1Realization.coroot 1) + x 2 • w := by
          dsimp only [w]; module
    exact hx ▸ Submodule.add_mem_sup
      (add_mem (Submodule.smul_mem _ _ (affineA1Realization.coroot_mem_corootSpan 0))
        (Submodule.smul_mem _ _ (affineA1Realization.coroot_mem_corootSpan 1)))
      (Submodule.smul_mem _ _ (Submodule.subset_span rfl))

/-- Affine `A₁⁽¹⁾` on `ℚ³`: Kac's complement form `B` for `W = span {d}` has Gram matrix
`[[2, -2, 1], [-2, 2, 0], [1, 0, 0]]` of determinant `-2`, pairs `c = h₀ + h₁` to `0` with coroots
and to `1` with `d` (whereas the naive zero-extension has `c` in its radical), and for the shifted
complement `W' = span {d + h₀}` the nilpotent shear `B.ofComplIsometryEquiv` sends `d + h₀` to the
`B`-isotropic vector `d - h₀ - 2 h₁`. -/
example :
    let b := Pi.basisFun ℚ (Fin 3)
    let hW : IsCompl affineA1Realization.corootSpan (Submodule.span ℚ {b 2}) := by
      simpa [b] using isCompl_affineA1_span 0
    let hW' : IsCompl affineA1Realization.corootSpan
        (Submodule.span ℚ {b 2 + affineA1Realization.coroot 0}) := by
      simpa [b] using isCompl_affineA1_span 1
    let B := InvariantForm.ofCompl affineA1Datum affineA1Realization hW
    let c := affineA1Realization.coroot 0 + affineA1Realization.coroot 1
    LinearMap.BilinForm.toMatrix b B.form = !![(2 : ℚ), -2, 1; -2, 2, 0; 1, 0, 0] ∧
      (LinearMap.BilinForm.toMatrix b B.form).det = -2 ∧
      B.form c (affineA1Realization.coroot 0) = 0 ∧ B.form c (b 2) = 1 ∧
      c ∈ LinearMap.ker (Matrix.toBilin b !![(2 : ℚ), -2, 0; -2, 2, 0; 0, 0, 0]) ∧
      B.ofComplIsometryEquiv isMinimal_affineA1Realization hW'
          (b 2 + affineA1Realization.coroot 0) =
        b 2 - affineA1Realization.coroot 0 - (2 : ℚ) • affineA1Realization.coroot 1 := by
  intro b hW hW' B c
  have hb0 : b 0 = affineA1Realization.coroot 0 := by
    ext i; fin_cases i <;> simp [b, affineA1Realization]
  have hb1 : b 1 = affineA1Realization.coroot 1 := by
    ext i; fin_cases i <;> simp [b, affineA1Realization]
  have hB0 (y) : B.form (b 0) y = 2 * y 0 - 2 * y 1 + y 2 := by
    rw [hb0]; simpa [affineA1Realization, affineA1Datum] using B.form_coroot 0 y
  have hB1 (y) : B.form (b 1) y = -2 * y 0 + 2 * y 1 := by
    rw [hb1]; simpa [affineA1Realization, affineA1Datum] using B.form_coroot 1 y
  have hB (i j : Fin 3) : B.form (b i) (b j) = !![(2 : ℚ), -2, 1; -2, 2, 0; 1, 0, 0] i j := by
    fin_cases i
    · exact (hB0 (b j)).trans (by fin_cases j <;> simp [b])
    · exact (hB1 (b j)).trans (by fin_cases j <;> simp [b])
    · fin_cases j
      · exact (B.isSymm.eq (b 2) (b 0)).trans ((hB0 (b 2)).trans (by simp [b]))
      · exact (B.isSymm.eq (b 2) (b 1)).trans ((hB1 (b 2)).trans (by simp [b]))
      · exact (InvariantForm.ofCompl_form_eq_zero hW (Submodule.subset_span rfl)
          (Submodule.subset_span rfl)).trans (by simp)
  have hmat : LinearMap.BilinForm.toMatrix b B.form = !![(2 : ℚ), -2, 1; -2, 2, 0; 1, 0, 0] := by
    ext i j; rw [LinearMap.BilinForm.toMatrix_apply, hB]
  refine ⟨hmat, by rw [hmat, Matrix.det_fin_three]; norm_num, by simp [c, affineA1Datum],
    by simp [c, ← hb0, ← hb1, hB], ?_, ?_⟩
  · rw [LinearMap.mem_ker]; apply b.ext; intro j
    fin_cases j <;> simp [c, ← hb0, ← hb1, Matrix.toBilin_apply, Fin.sum_univ_three]
  · set w' : Submodule.span ℚ {b 2 + affineA1Realization.coroot 0} :=
      ⟨b 2 + affineA1Realization.coroot 0, Submodule.subset_span rfl⟩
    have hc_mem : (-2 : ℚ) • c ∈ affineA1Realization.cartanCenter ⊓
        affineA1Realization.corootSpan :=
      ⟨(affineA1Realization.mem_cartanCenter_iff _).mpr fun i ↦ by
          fin_cases i <;> simp [c, affineA1Realization],
        Submodule.smul_mem _ _ (add_mem (affineA1Realization.coroot_mem_corootSpan 0)
          (affineA1Realization.coroot_mem_corootSpan 1))⟩
    have hsym : (B.centerComplEquivDual isMinimal_affineA1Realization hW').symm
        (-(2 : ℚ)⁻¹ • B.form.restrict _ w') = ⟨(-2 : ℚ) • c, hc_mem⟩ := by
      have hww : B.form (b 2 + b 0) (b 2 + b 0) = 4 := by norm_num [hB]
      have hcw : B.form (b 0 + b 1) (b 2 + b 0) = 1 := by norm_num [hB]
      rw [LinearEquiv.symm_apply_eq]; ext ⟨u, hu⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [LinearMap.smul_apply, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        B.centerComplEquivDual_apply]
      simp only [w', c, ← hb0, ← hb1, map_smul, LinearMap.smul_apply, smul_eq_mul, hww, hcw]
      ring
    have heq := B.ofComplIsometryEquiv_apply_compl isMinimal_affineA1Realization hW' w'
    rw [hsym] at heq
    have hlin : b 2 + affineA1Realization.coroot 0 + (-2 : ℚ) • c =
        b 2 - affineA1Realization.coroot 0 - (2 : ℚ) • affineA1Realization.coroot 1 := by
      dsimp only [c]; module
    exact heq.trans hlin

private def a1Datum : SymmetrizableDatum (Fin 1) where
  cartan := !![2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_one]
      zero_comm := by simp }
  symmetrizer := 1
  symmetrizer_pos := by decide
  symmetrizes := by decide

/-- Central enlargement of `A₁` inside `Fin (n + 1) → ℚ` with `h₀ = e₀` and `α₀ = 2 e₀*`. -/
private noncomputable def a1Enlarged (n : ℕ) :
    CartanRealization (a1Datum.cartan.map (Int.cast : ℤ → ℚ)) (Fin (n + 1) → ℚ) where
  coroot _ := Pi.single 0 1
  root _ := (2 : ℚ) • LinearMap.proj 0
  coroot_linearIndependent := Fintype.linearIndependent_iff.mpr fun c hc i ↦ by
    fin_cases i; simpa using congrFun hc 0
  root_linearIndependent := Fintype.linearIndependent_iff.mpr fun c hc i ↦ by
    fin_cases i; simpa using LinearMap.congr_fun hc (Pi.single 0 1)
  root_coroot i j := by fin_cases i; fin_cases j; simp [a1Datum]

/-- Non-minimal central enlargements of `A₁` to `ℚ²` and `ℚ³`:
1. On `ℚ²`, `¬ (a1Enlarged 1).IsMinimal`, so
   `exists_nondegenerate_not_isometryEquiv_of_not_isMinimal` produces two nondegenerate standard
   invariant forms with no realization-preserving isometry;
2. On `ℚ³`, **every** complement `W` to `(a1Enlarged 2).corootSpan` produces a degenerate
   `ofCompl`. -/
example :
    (∃ B₁ B₂ : InvariantForm a1Datum (a1Enlarged 1),
      B₁.form.Nondegenerate ∧ B₂.form.Nondegenerate ∧
        ¬ ∃ e : B₁.form.IsometryEquiv B₂.form,
          (a1Enlarged 1).map e.toLinearEquiv = a1Enlarged 1) ∧
    ∀ (W : Submodule ℚ (Fin 3 → ℚ)) (hW : IsCompl (a1Enlarged 2).corootSpan W),
      ¬ (InvariantForm.ofCompl a1Datum (a1Enlarged 2) hW).form.Nondegenerate := by
  refine ⟨InvariantForm.exists_nondegenerate_not_isometryEquiv_of_not_isMinimal a1Datum ?_,
    fun W hW ↦ InvariantForm.not_nondegenerate_ofCompl_of_two_mul_card_lt_finrank hW (by simp)⟩
  intro hmin
  have hcent : (Pi.single 1 (1 : ℚ) : Fin 2 → ℚ) ∈ (a1Enlarged 1).corootSpan :=
    ((a1Enlarged 1).isMinimal_iff_cartanCenter_le_corootSpan.mp hmin) <|
      ((a1Enlarged 1).mem_cartanCenter_iff _).mpr fun i ↦ by fin_cases i; simp [a1Enlarged]
  obtain ⟨c, hc⟩ := ((a1Enlarged 1).mem_corootSpan_iff _).mp hcent
  have h1 := congrFun hc 1; simp [corootMap_apply, a1Enlarged] at h1

end Examples
