/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Squares
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Tactic.Ring

/-!
# The submodule of symmetric bilinear forms and its rank

On any module `M` over a commutative semiring `R`, symmetric bilinear forms form an `R`-submodule
`LinearMap.BilinForm.symmSubmodule R M`, and alternating ones an `R`-submodule
`LinearMap.BilinForm.altSubmodule R M`. When `R` is a commutative ring with `Invertible (2 : R)`,
splitting a bilinear form into symmetric and alternating parts identifies
`symmSubmodule R M × Module.Dual R (⋀[R]^2 M)` with `BilinForm R M` without choosing a basis. On a
finite free module `M` over a commutative semiring `R`, `Module.finrank R (symmSubmodule R M) =
Module.finrank R M * (Module.finrank R M + 1) / 2` in arbitrary characteristic.

## Main definitions

* `LinearMap.BilinForm.symmSubmodule`: the submodule of symmetric bilinear forms.
* `LinearMap.BilinForm.altSubmodule`: the submodule of alternating bilinear forms.
* `LinearMap.BilinForm.symmProdExteriorDualEquiv`: the canonical linear equivalence
  `(symmSubmodule R M × Module.Dual R (⋀[R]^2 M)) ≃ₗ[R] BilinForm R M` when `2` is invertible.

## Main results

* `LinearMap.BilinForm.isSymm_add_flip` and `LinearMap.BilinForm.isAlt_sub_flip`: adding or
  subtracting the flip of a bilinear form yields a symmetric or alternating bilinear form.
* `LinearMap.BilinForm.disjoint_symmSubmodule_altSubmodule`: when `2` is invertible, only the zero
  form is both symmetric and alternating.
* `LinearMap.BilinForm.finrank_symmSubmodule`: `Module.finrank R (symmSubmodule R M) =
  Module.finrank R M * (Module.finrank R M + 1) / 2` on a finite free module.
-/

public section

open LinearMap (BilinForm)

namespace LinearMap.BilinForm

section CommSemiring

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The submodule of symmetric bilinear forms on `M`. -/
def symmSubmodule : Submodule R (BilinForm R M) where
  carrier := {B | B.IsSymm}
  zero_mem' := isSymm_zero
  add_mem' h₁ h₂ := h₁.add h₂
  smul_mem' c _ h := h.smul c

/-- The submodule of alternating bilinear forms on `M`. -/
def altSubmodule : Submodule R (BilinForm R M) where
  carrier := {B | B.IsAlt}
  zero_mem' := isAlt_zero
  add_mem' h₁ h₂ := h₁.add h₂
  smul_mem' c _ h := h.smul c

variable {R M}

/-- Membership in `symmSubmodule R M` is `LinearMap.BilinForm.IsSymm`. -/
@[simp] theorem mem_symmSubmodule {B : BilinForm R M} : B ∈ symmSubmodule R M ↔ B.IsSymm := Iff.rfl

/-- Membership in `altSubmodule R M` is `LinearMap.BilinForm.IsAlt`. -/
@[simp] theorem mem_altSubmodule {B : BilinForm R M} : B ∈ altSubmodule R M ↔ B.IsAlt := Iff.rfl

/-- Adding a bilinear form to its flip produces a symmetric bilinear form. -/
theorem isSymm_add_flip (B : BilinForm R M) : (B + B.flip).IsSymm :=
  ⟨fun _ _ ↦ by simp only [LinearMap.add_apply, flip_apply, add_comm]⟩

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/-- Subtracting the flip of a bilinear form produces an alternating bilinear form. -/
theorem isAlt_sub_flip (B : BilinForm R M) : (B - B.flip).IsAlt := fun _ ↦ by
  simp only [LinearMap.sub_apply, flip_apply, sub_self]

end CommRing

section InvertibleTwo

variable (R M : Type*) [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

private theorem symm_part_add_exterior_eq {B : BilinForm R M} (hB : B.IsSymm)
    (ψ : Module.Dual R (⋀[R]^2 M)) :
    ⅟(2 : R) • ((B + TauCeti.BilinForm.ofExteriorSquareDual ψ) +
      (B + TauCeti.BilinForm.ofExteriorSquareDual ψ).flip) = B := by
  ext x y
  simp only [LinearMap.smul_apply, LinearMap.add_apply, flip_apply, smul_eq_mul, hB.eq y x,
    ← (TauCeti.BilinForm.isAlt_ofExteriorSquareDual ψ).neg_eq x y]
  grind [invOf_mul_self]

private theorem alt_part_add_exterior_eq {B : BilinForm R M} (hB : B.IsSymm)
    (ψ : Module.Dual R (⋀[R]^2 M)) :
    exteriorPower.alternatingMapLinearEquiv (LinearMap.IsAlt.toAlternatingMap
      ((isAlt_sub_flip (B + TauCeti.BilinForm.ofExteriorSquareDual ψ)).smul (⅟(2 : R)))) = ψ := by
  refine TauCeti.BilinForm.ofExteriorSquareDual_injective (LinearMap.ext₂ fun x y ↦ ?_)
  simp only [TauCeti.BilinForm.ofExteriorSquareDual_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [LinearMap.IsAlt.toAlternatingMap_apply
    ((isAlt_sub_flip (B + TauCeti.BilinForm.ofExteriorSquareDual ψ)).smul (⅟(2 : R))) ![x, y]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, flip_apply, smul_eq_mul]
  rw [hB.eq y x, ← (TauCeti.BilinForm.isAlt_ofExteriorSquareDual ψ).neg_eq x y,
    TauCeti.BilinForm.ofExteriorSquareDual_apply]
  grind [invOf_mul_self]

/-- When `2` is invertible in `R`, decomposing a bilinear form into its symmetric and alternating
parts identifies `symmSubmodule R M × Module.Dual R (⋀[R]^2 M)` with `BilinForm R M`. -/
noncomputable def symmProdExteriorDualEquiv :
    (symmSubmodule R M × Module.Dual R (⋀[R]^2 M)) ≃ₗ[R] BilinForm R M where
  toFun p := p.1.val + TauCeti.BilinForm.ofExteriorSquareDual p.2
  invFun B := (⟨⅟(2 : R) • (B + B.flip), (isSymm_add_flip B).smul _⟩,
    exteriorPower.alternatingMapLinearEquiv
      (LinearMap.IsAlt.toAlternatingMap ((isAlt_sub_flip B).smul _)))
  map_add' _ _ := LinearMap.ext₂ fun _ _ ↦ by
    simp only [Prod.fst_add, Submodule.coe_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring
  map_smul' _ _ := LinearMap.ext₂ fun _ _ ↦ by
    simp only [Prod.smul_fst, SetLike.val_smul, Prod.smul_snd, map_smul, RingHom.id_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_add]
  left_inv p := Prod.ext (Subtype.ext (symm_part_add_exterior_eq R M p.1.property p.2))
    (alt_part_add_exterior_eq R M p.1.property p.2)
  right_inv B := LinearMap.ext₂ fun x y ↦ by
    simp only [LinearMap.add_apply, TauCeti.BilinForm.ofExteriorSquareDual_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [LinearMap.IsAlt.toAlternatingMap_apply ((isAlt_sub_flip B).smul (⅟(2 : R))) ![x, y]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.sub_apply, flip_apply, smul_eq_mul]
    grind [invOf_mul_self]

variable {R M}

/-- Evaluation of `symmProdExteriorDualEquiv` as the sum of symmetric and alternating parts. -/
@[simp] theorem symmProdExteriorDualEquiv_apply
    (p : symmSubmodule R M × Module.Dual R (⋀[R]^2 M)) :
    symmProdExteriorDualEquiv R M p = p.1.val + TauCeti.BilinForm.ofExteriorSquareDual p.2 := (rfl)

/-- The symmetric component of `symmProdExteriorDualEquiv.symm B` is `⅟2 • (B + B.flip)`. -/
@[simp] theorem symmProdExteriorDualEquiv_symm_fst (B : BilinForm R M) :
    ((symmProdExteriorDualEquiv R M).symm B).1.val = ⅟(2 : R) • (B + B.flip) := (rfl)

/-- Exterior-square component of `symmProdExteriorDualEquiv.symm B` evaluated on `x ∧ y`. -/
@[simp] theorem symmProdExteriorDualEquiv_symm_snd_apply_ιMulti (B : BilinForm R M) (x y : M) :
    ((symmProdExteriorDualEquiv R M).symm B).2 (exteriorPower.ιMulti R 2 ![x, y]) =
      ⅟(2 : R) * (B x y - B y x) := by
  simp only [symmProdExteriorDualEquiv, LinearEquiv.coe_symm_mk,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [LinearMap.IsAlt.toAlternatingMap_apply ((isAlt_sub_flip B).smul (⅟(2 : R))) ![x, y]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.smul_apply, LinearMap.sub_apply,
    flip_apply, smul_eq_mul]

/-- When `2` is invertible, a bilinear form that is both symmetric and alternating is zero. -/
theorem disjoint_symmSubmodule_altSubmodule :
    Disjoint (symmSubmodule R M) (altSubmodule R M) := by
  refine Submodule.disjoint_def.2 fun B hs ha ↦ LinearMap.ext₂ fun x y ↦ ?_
  have h₁ := (mem_symmSubmodule.1 hs).eq x y
  have h₂ := (mem_altSubmodule.1 ha).neg_eq x y
  have h : (2 : R) * B x y = 0 := by
    rw [two_mul, ← sub_neg_eq_add, h₂, ← h₁, sub_self]
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  simpa using congrArg (⅟(2 : R) * ·) h

end InvertibleTwo

section FiniteFree

/-- On a finite free module `M`, the submodule of symmetric bilinear forms has `finrank` equal to
`finrank R M * (finrank R M + 1) / 2` (in arbitrary characteristic). -/
theorem finrank_symmSubmodule {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (symmSubmodule R M) =
      Module.finrank R M * (Module.finrank R M + 1) / 2 := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    have : Subsingleton (symmSubmodule R M) := Module.subsingleton R _
    simp [Module.finrank_subsingleton]
  set n := Module.finrank R M
  let b : Module.Basis (Fin n) R M := (Module.Free.chooseBasis R M).reindex
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_chooseBasisIndex R M).symm)
  let e : symmSubmodule R M ≃ₗ[R] (Sym2 (Fin n) → R) :=
    { toFun := fun B ↦ Sym2.lift ⟨fun i j ↦ toMatrix b B.val i j,
        fun i j ↦ ((B.val.isSymm_toMatrix_iff_isSymm b).mpr B.property).apply j i⟩
      invFun := fun f ↦ ⟨(toMatrix b).symm (Matrix.of fun i j ↦ f s(i, j)), by
        rw [mem_symmSubmodule, ← isSymm_toMatrix_iff_isSymm b, LinearEquiv.apply_symm_apply]
        exact Matrix.IsSymm.ext fun i j ↦ by simp [Sym2.eq_swap]⟩
      map_add' := fun _ _ ↦ funext fun p ↦ p.ind fun _ _ ↦ by simp
      map_smul' := fun _ _ ↦ funext fun p ↦ p.ind fun _ _ ↦ by simp
      left_inv := fun B ↦ Subtype.ext <| (toMatrix b).injective <| Matrix.ext fun _ _ ↦ by
        dsimp only; rw [LinearEquiv.apply_symm_apply]; simp
      right_inv := fun f ↦ funext fun p ↦ p.ind fun _ _ ↦ by
        dsimp only; simp only [Sym2.lift_mk]; rw [LinearEquiv.apply_symm_apply]; simp }
  simp [e.finrank_eq, Sym2.card, Nat.choose_two_right, Nat.mul_comm]

end FiniteFree

end LinearMap.BilinForm
