/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import TauCeti.LinearAlgebra.BilinearForm.Squares
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.Ring

/-!
# The submodule of symmetric bilinear forms and its rank

On any module `M` over a commutative ring `R`, the symmetric bilinear forms `B : BilinForm R M`
form an `R`-submodule `LinearMap.BilinForm.symmSubmodule R M`.

When `2` is invertible in `R`, every bilinear form splits uniquely into its symmetric part
`⅟2 • (B + B.flip)` and its alternating part `⅟2 • (B - B.flip)`. Combined with the universal
property of the second exterior power (`TauCeti.BilinForm.ofExteriorSquareDual`), this identifies
`symmSubmodule R M × Module.Dual R (⋀[R]^2 M)` with `BilinForm R M` without choosing a basis.

On a finite free `R`-module `M` of rank `n` over a commutative ring satisfying
`StrongRankCondition`, identifying symmetric bilinear forms with symmetric `n × n` matrices and
reading off their upper-triangular entries shows that `symmSubmodule R M` is free of rank
`n * (n + 1) / 2` in arbitrary characteristic (including characteristic `2`).

## Main definitions

* `LinearMap.BilinForm.symmSubmodule`: the submodule of symmetric bilinear forms.
* `LinearMap.BilinForm.symmProdExteriorDualEquiv`: the canonical linear equivalence
  `(symmSubmodule R M × Module.Dual R (⋀[R]^2 M)) ≃ₗ[R] BilinForm R M` when `2` is invertible.

## Main results

* `LinearMap.BilinForm.finrank_symmSubmodule`: on a finite free module `M`, the submodule of
  symmetric bilinear forms has `finrank` equal to
  `Module.finrank R M * (Module.finrank R M + 1) / 2`.
-/

public section

open LinearMap (BilinForm)

namespace LinearMap.BilinForm

section CommRing

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The submodule of symmetric bilinear forms on `M`. -/
def symmSubmodule : Submodule R (BilinForm R M) where
  carrier := {B | B.IsSymm}
  zero_mem' := isSymm_zero
  add_mem' h₁ h₂ := h₁.add h₂
  smul_mem' c _ h := h.smul c

variable {R M}

/-- Membership in `symmSubmodule R M` is `LinearMap.BilinForm.IsSymm`. -/
@[simp]
theorem mem_symmSubmodule {B : BilinForm R M} : B ∈ symmSubmodule R M ↔ B.IsSymm :=
  (Iff.rfl)

end CommRing

section InvertibleTwo

variable (R M : Type*) [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

private theorem isSymm_half_add_flip (B : BilinForm R M) :
    (⅟(2 : R) • (B + B.flip)).IsSymm :=
  ⟨fun x y ↦ by
    simp only [LinearMap.smul_apply, LinearMap.add_apply, flip_apply, smul_eq_mul]
    rw [add_comm]⟩

private theorem isAlt_half_sub_flip (B : BilinForm R M) :
    LinearMap.IsAlt (⅟(2 : R) • (B - B.flip)) := fun x ↦ by
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, flip_apply, sub_self, smul_zero]

private theorem symm_part_add_exterior_eq {B : BilinForm R M} (hB : B.IsSymm)
    (ψ : Module.Dual R (⋀[R]^2 M)) :
    ⅟(2 : R) • ((B + TauCeti.BilinForm.ofExteriorSquareDual ψ) +
      (B + TauCeti.BilinForm.ofExteriorSquareDual ψ).flip) = B := by
  ext x y
  simp only [LinearMap.smul_apply, LinearMap.add_apply, flip_apply,
    TauCeti.BilinForm.ofExteriorSquareDual_apply, smul_eq_mul]
  have hswap : exteriorPower.ιMulti R 2 ![y, x] = -exteriorPower.ιMulti R 2 ![x, y] := by
    simpa [Equiv.swap_apply_def] using
      (exteriorPower.ιMulti R 2).map_swap ![x, y] (by decide : (0 : Fin 2) ≠ 1)
  rw [hB.eq y x, hswap, map_neg]
  have hsum : B x y + ψ (exteriorPower.ιMulti R 2 ![x, y]) +
      (B x y + -ψ (exteriorPower.ιMulti R 2 ![x, y])) = 2 * B x y := by ring
  rw [hsum, ← mul_assoc, invOf_mul_self, one_mul]

private theorem alt_part_add_exterior_eq {B : BilinForm R M} (hB : B.IsSymm)
    (ψ : Module.Dual R (⋀[R]^2 M)) :
    exteriorPower.alternatingMapLinearEquiv
      (LinearMap.IsAlt.toAlternatingMap
        (isAlt_half_sub_flip R M (B + TauCeti.BilinForm.ofExteriorSquareDual ψ))) = ψ := by
  refine TauCeti.BilinForm.ofExteriorSquareDual_injective ?_
  ext x y
  simp only [TauCeti.BilinForm.ofExteriorSquareDual_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    LinearMap.IsAlt.toAlternatingMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, flip_apply, smul_eq_mul]
  have hneg := (TauCeti.BilinForm.isAlt_ofExteriorSquareDual ψ).neg_eq x y
  simp only [TauCeti.BilinForm.ofExteriorSquareDual_apply] at hneg
  rw [hB.eq y x, ← hneg]
  have hsum : B x y + ψ (exteriorPower.ιMulti R 2 ![x, y]) -
      (B x y + -ψ (exteriorPower.ιMulti R 2 ![x, y])) =
      2 * ψ (exteriorPower.ιMulti R 2 ![x, y]) := by ring
  rw [hsum, ← mul_assoc, invOf_mul_self, one_mul]

/-- When `2` is invertible in `R`, decomposing a bilinear form into its symmetric and alternating
parts identifies `symmSubmodule R M × Module.Dual R (⋀[R]^2 M)` with `BilinForm R M`. -/
noncomputable def symmProdExteriorDualEquiv :
    (symmSubmodule R M × Module.Dual R (⋀[R]^2 M)) ≃ₗ[R] BilinForm R M where
  toFun p := p.1.1 + TauCeti.BilinForm.ofExteriorSquareDual p.2
  invFun B :=
    (⟨⅟(2 : R) • (B + B.flip), isSymm_half_add_flip R M B⟩,
      exteriorPower.alternatingMapLinearEquiv
        (LinearMap.IsAlt.toAlternatingMap (isAlt_half_sub_flip R M B)))
  map_add' p q := by
    ext x y
    simp only [Prod.fst_add, Submodule.coe_add, Prod.snd_add, map_add, LinearMap.add_apply]
    ring
  map_smul' c p := by
    ext x y
    simp only [Prod.smul_fst, SetLike.val_smul, Prod.smul_snd, map_smul, RingHom.id_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_add]
  left_inv p := Prod.ext (Subtype.ext (symm_part_add_exterior_eq R M p.1.2 p.2))
    (alt_part_add_exterior_eq R M p.1.2 p.2)
  right_inv B := by
    ext x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, flip_apply,
      TauCeti.BilinForm.ofExteriorSquareDual_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.IsAlt.toAlternatingMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      LinearMap.sub_apply, smul_eq_mul]
    calc
      ⅟(2 : R) * (B x y + B y x) + ⅟(2 : R) * (B x y - B y x) =
          (⅟(2 : R) * 2) * B x y := by ring
      _ = B x y := by rw [invOf_mul_self, one_mul]

variable {R M}

/-- Evaluation of `symmProdExteriorDualEquiv` as the sum of the symmetric form and the alternating
form attached to the exterior-square functional. -/
@[simp]
theorem symmProdExteriorDualEquiv_apply
    (p : symmSubmodule R M × Module.Dual R (⋀[R]^2 M)) :
    symmProdExteriorDualEquiv R M p = p.1.1 + TauCeti.BilinForm.ofExteriorSquareDual p.2 :=
  (rfl)

/-- The symmetric component of `symmProdExteriorDualEquiv.symm B` is `⅟2 • (B + B.flip)`. -/
@[simp]
theorem symmProdExteriorDualEquiv_symm_fst (B : BilinForm R M) :
    ((symmProdExteriorDualEquiv R M).symm B).1.1 = ⅟(2 : R) • (B + B.flip) :=
  (rfl)

/-- The exterior-square component of `symmProdExteriorDualEquiv.symm B` evaluates on `x ∧ y` to
`⅟2 * (B x y - B y x)`. -/
@[simp]
theorem symmProdExteriorDualEquiv_symm_snd_apply_ιMulti (B : BilinForm R M) (x y : M) :
    ((symmProdExteriorDualEquiv R M).symm B).2 (exteriorPower.ιMulti R 2 ![x, y]) =
      ⅟(2 : R) * (B x y - B y x) := by
  simp [symmProdExteriorDualEquiv, LinearMap.sub_apply]

end InvertibleTwo

section FiniteFree

private theorem card_upperTriangle (n : ℕ) :
    Fintype.card {ij : Fin n × Fin n // ij.1 ≤ ij.2} = n * (n + 1) / 2 := by
  classical
  have hpart := Fintype.card_congr (Equiv.sumCompl (fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2))
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hpart
  let e : {ij : Fin n × Fin n // ¬ij.1 ≤ ij.2} ⊕ Fin n ≃ {ij : Fin n × Fin n // ij.1 ≤ ij.2} :=
    { toFun := Sum.elim (fun ij ↦ ⟨(ij.1.2, ij.1.1), le_of_not_ge ij.2⟩)
        (fun i ↦ ⟨(i, i), le_rfl⟩)
      invFun := fun ij ↦
        if h : ij.1.1 = ij.1.2 then Sum.inr ij.1.1
        else Sum.inl ⟨(ij.1.2, ij.1.1), not_le.mpr (lt_of_le_of_ne ij.2 h)⟩
      left_inv := by
        rintro (⟨⟨i, j⟩, h⟩ | i)
        · have hne : j ≠ i := fun hij ↦ h (hij ▸ le_rfl)
          simp [hne]
        · simp
      right_inv := fun ⟨⟨i, j⟩, h⟩ ↦ by
        by_cases hij : i = j <;> simp [hij] }
  have he := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at he
  have hmul : n * (n + 1) = n * n + n := by ring
  omega

/-- On a finite free module `M`, the submodule of symmetric bilinear forms has `finrank` equal to
`finrank R M * (finrank R M + 1) / 2` (in arbitrary characteristic). -/
theorem finrank_symmSubmodule {R M : Type*} [CommRing R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (symmSubmodule R M) =
      Module.finrank R M * (Module.finrank R M + 1) / 2 := by
  classical
  set n := Module.finrank R M
  let b : Module.Basis (Fin n) R M :=
    (Module.Free.chooseBasis R M).reindex
      (Fintype.equivFinOfCardEq (Module.finrank_eq_card_chooseBasisIndex R M).symm)
  let e : symmSubmodule R M ≃ₗ[R] ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → R) :=
    { toFun := fun B ij ↦ toMatrix b B.1 ij.1.1 ij.1.2
      invFun := fun f ↦
        ⟨(toMatrix b).symm (Matrix.of fun i j ↦
          if h : i ≤ j then f ⟨(i, j), h⟩ else f ⟨(j, i), le_of_not_ge h⟩), by
          rw [mem_symmSubmodule, ← isSymm_toMatrix_iff_isSymm b, LinearEquiv.apply_symm_apply]
          refine Matrix.IsSymm.ext fun i j ↦ ?_
          dsimp
          by_cases hij : i ≤ j <;> by_cases hji : j ≤ i <;> simp [hij, hji]
          · cases le_antisymm hij hji; rfl
          · omega⟩
      map_add' := fun B₁ B₂ ↦ by funext ij; simp
      map_smul' := fun c B ↦ by funext ij; simp
      left_inv := fun B ↦ Subtype.ext <| (toMatrix b).injective <| Matrix.ext fun i j ↦ by
        rw [LinearEquiv.apply_symm_apply]
        dsimp
        split_ifs with h
        · rfl
        · exact ((B.1.isSymm_toMatrix_iff_isSymm b).mpr B.2).apply i j
      right_inv := fun f ↦ by
        funext ⟨⟨i, j⟩, h⟩
        dsimp only
        rw [LinearEquiv.apply_symm_apply]
        simp [h] }
  rw [e.finrank_eq, Module.finrank_pi, card_upperTriangle]

end FiniteFree

end LinearMap.BilinForm
