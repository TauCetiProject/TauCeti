/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projection

/-!
# Weights of the contragredient representation

For a representation `ρ` of `GL n k` on `W`, the contragredient `ρ.dual` acts on
`Module.Dual k W` by `g • f = f ∘ ρ(g⁻¹)`. A functional of weight `l` pairs with a vector of
weight `l'` through the character `t ↦ ∏ tᵢ ^ (lᵢ + l'ᵢ)`, so it vanishes on that vector unless
`l + l' = 0`, once weights are separated by their characters
(`TauCeti.apply_eq_zero_of_mem_weightSpace_dual`).

When moreover the weight spaces of `ρ` span `W`, a functional of weight `l` is determined by its
restriction to the weight space of `-l`, and every functional there extends, by zero on the
other weight spaces, to a functional of weight `l`. So the weight space of `ρ.dual` of weight `l`
is the dual of the weight space of `ρ` of weight `-l` (`TauCeti.weightSpaceDualEquiv`): the
weights of the contragredient are the negatives of the weights, with the same multiplicities
(`TauCeti.finrank_weightSpace_dual`).

## Main definitions

* `TauCeti.weightSpaceDualEquiv`: the weight space of `ρ.dual` of weight `l` is
  `Module.Dual k (weightSpace ρ (-l))`, by restriction.

## Main results

* `TauCeti.apply_eq_zero_of_mem_weightSpace_dual`: a functional of weight `l` vanishes on the
  vectors of weight `l'` for `l + l' ≠ 0`.
* `TauCeti.finrank_weightSpace_dual`: `dim (W^*)_l = dim W_{-l}`.
* `TauCeti.weightSpace_dual_ne_bot_iff`: `l` is a weight of `ρ.dual` iff `-l` is a weight of `ρ`.
-/

public section

open Matrix Module

universe u v

namespace TauCeti

variable {W : Type v} [AddCommGroup W]

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ} [Module k W]

/-- The contragredient action of a torus element on a functional of weight `l`, evaluated at a
vector `w`: `f (ρ(t⁻¹) w) = χ_l(t) f(w)`. -/
theorem apply_inv_of_mem_weightSpace_dual {ρ : Representation k (GL (Fin n) k) W}
    {l : Fin n → ℤ} {f : Dual k W} (hf : f ∈ weightSpace ρ.dual l) (t : Fin n → kˣ) (w : W) :
    f (ρ (diagGL t)⁻¹ w) = ((weightChar k l t : kˣ) : k) * f w := by
  have h := congrArg (fun g : Dual k W ↦ g w) (apply_of_mem_weightSpace hf t)
  simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h

end CommRing

section IsCancelMulZero

variable {k : Type u} [CommRing k] [IsCancelMulZero k] {n : ℕ} [Module k W]

/-- **A functional of weight `l` vanishes on the vectors of weight `l'` unless `l + l' = 0`**,
when distinct weights give distinct characters: `χ_l(t) f(w) = f(ρ(t⁻¹) w) = χ_{l'}(t)⁻¹ f(w)`
for every torus element `t`. -/
theorem apply_eq_zero_of_mem_weightSpace_dual
    (hchar : Function.Injective (weightChar k (κ := Fin n)))
    {ρ : Representation k (GL (Fin n) k) W} {l l' : Fin n → ℤ} (hll' : l + l' ≠ 0)
    {f : Dual k W} (hf : f ∈ weightSpace ρ.dual l) {w : W} (hw : w ∈ weightSpace ρ l') :
    f w = 0 := by
  by_contra hfw
  have hl : weightChar k l = weightChar k (-l') := MonoidHom.ext fun t ↦ Units.ext <| by
    have h := apply_inv_of_mem_weightSpace_dual hf t w
    rw [← map_inv diagGL, apply_of_mem_weightSpace hw, map_smul, smul_eq_mul] at h
    rw [weightChar_neg, MonoidHom.inv_apply, ← map_inv]
    exact (mul_right_cancel₀ hfw h).symm
  exact hll' (by rw [hchar hl, neg_add_cancel])

/-- A functional of weight `l` vanishes on the weight spaces other than `-l`, when distinct
weights give distinct characters. -/
theorem iSup_weightSpace_ne_le_ker (hchar : Function.Injective (weightChar k (κ := Fin n)))
    {ρ : Representation k (GL (Fin n) k) W} {l : Fin n → ℤ} {f : Dual k W}
    (hf : f ∈ weightSpace ρ.dual l) :
    (⨆ (l' : Fin n → ℤ) (_ : l' ≠ -l), weightSpace ρ l') ≤ LinearMap.ker f :=
  iSup₂_le fun _ hl' _ hw ↦ apply_eq_zero_of_mem_weightSpace_dual hchar
    (fun h ↦ hl' (eq_neg_of_add_eq_zero_right h)) hf hw

end IsCancelMulZero

section Spanning

variable {k : Type u} [Field k] {n : ℕ} [Module k W]
variable (hchar : Function.Injective (weightChar k (κ := Fin n)))
  {ρ : Representation k (GL (Fin n) k) W} (hρ : ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤)
include hchar hρ

/-- The functional of weight `l` extending a functional `φ` on the weight space of `-l` by zero
on the other weight spaces. -/
noncomputable def extendWeightSpaceDual (l : Fin n → ℤ) (φ : Dual k (weightSpace ρ (-l))) :
    Dual k W :=
  LinearMap.ofIsCompl (isCompl_weightSpace_iSup_ne hchar hρ (-l)) φ 0

/-- The extension by zero restricts to `φ` on the weight space of `-l`. -/
theorem extendWeightSpaceDual_apply_of_mem (l : Fin n → ℤ) (φ : Dual k (weightSpace ρ (-l)))
    {w : W} (hw : w ∈ weightSpace ρ (-l)) : extendWeightSpaceDual hchar hρ l φ w = φ ⟨w, hw⟩ :=
  LinearMap.ofIsCompl_apply_left _ ⟨w, hw⟩

/-- The extension by zero vanishes on the weight spaces other than `-l`. -/
theorem extendWeightSpaceDual_apply_of_mem_iSup (l : Fin n → ℤ)
    (φ : Dual k (weightSpace ρ (-l))) {w : W}
    (hw : w ∈ ⨆ (l' : Fin n → ℤ) (_ : l' ≠ -l), weightSpace ρ l') :
    extendWeightSpaceDual hchar hρ l φ w = 0 :=
  LinearMap.ofIsCompl_apply_right _ ⟨w, hw⟩

/-- The extension by zero of a functional on the weight space of `-l` has weight `l`. -/
theorem extendWeightSpaceDual_mem (l : Fin n → ℤ) (φ : Dual k (weightSpace ρ (-l))) :
    extendWeightSpaceDual hchar hρ l φ ∈ weightSpace ρ.dual l := by
  rw [mem_weightSpace_iff]
  intro t
  ext w
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    ((isCompl_weightSpace_iSup_ne hchar hρ (-l)).sup_eq_top ▸ Submodule.mem_top (x := w))
  have ha' : ρ (diagGL t)⁻¹ a = ((weightChar k l t : kˣ) : k) • a := by
    rw [← map_inv diagGL, apply_of_mem_weightSpace ha, weightChar_neg, MonoidHom.inv_apply,
      map_inv, inv_inv]
  have hb' : ρ (diagGL t)⁻¹ b ∈ ⨆ (l' : Fin n → ℤ) (_ : l' ≠ -l), weightSpace ρ l' := by
    rw [← map_inv diagGL]
    exact iSup_weightSpace_ne_le_comap (-l) t⁻¹ hb
  simp [ha', extendWeightSpaceDual_apply_of_mem_iSup hchar hρ l φ hb,
    extendWeightSpaceDual_apply_of_mem_iSup hchar hρ l φ hb',
    extendWeightSpaceDual_apply_of_mem hchar hρ l φ ha]

/-- **The weight space of the contragredient of weight `l` is the dual of the weight space of
weight `-l`**, by restriction, when the weight spaces span and distinct weights give distinct
characters. The inverse extends a functional by zero on the other weight spaces. -/
noncomputable def weightSpaceDualEquiv (l : Fin n → ℤ) :
    weightSpace ρ.dual l ≃ₗ[k] Dual k (weightSpace ρ (-l)) where
  toFun f := (f : Dual k W) ∘ₗ (weightSpace ρ (-l)).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := ⟨extendWeightSpaceDual hchar hρ l φ, extendWeightSpaceDual_mem hchar hρ l φ⟩
  left_inv f := Subtype.ext <| LinearMap.ofIsCompl_eq _ (fun _ ↦ rfl) fun u ↦
    (iSup_weightSpace_ne_le_ker hchar f.property u.property).symm
  right_inv φ := LinearMap.ext fun w ↦ extendWeightSpaceDual_apply_of_mem hchar hρ l φ w.property

/-- `weightSpaceDualEquiv` is restriction to the weight space of `-l`. -/
@[simp]
theorem weightSpaceDualEquiv_apply (l : Fin n → ℤ) (f : weightSpace ρ.dual l)
    (w : weightSpace ρ (-l)) : weightSpaceDualEquiv hchar hρ l f w = (f : Dual k W) w :=
  (rfl)

/-- The inverse of `weightSpaceDualEquiv` is extension by zero on the other weight spaces. -/
@[simp]
theorem coe_weightSpaceDualEquiv_symm_apply (l : Fin n → ℤ) (φ : Dual k (weightSpace ρ (-l))) :
    (((weightSpaceDualEquiv hchar hρ l).symm φ : weightSpace ρ.dual l) : Dual k W) =
      extendWeightSpaceDual hchar hρ l φ :=
  (rfl)

/-- **The weights of the contragredient are the negatives of the weights, with the same
multiplicities**: `dim (W^*)_l = dim W_{-l}`, for a representation whose weight spaces span it,
when distinct weights give distinct characters. -/
theorem finrank_weightSpace_dual (l : Fin n → ℤ) :
    finrank k (weightSpace ρ.dual l) = finrank k (weightSpace ρ (-l)) :=
  (weightSpaceDualEquiv hchar hρ l).finrank_eq.trans Subspace.dual_finrank_eq

/-- **`l` is a weight of the contragredient iff `-l` is a weight**, for a representation whose
weight spaces span it, when distinct weights give distinct characters. -/
theorem weightSpace_dual_ne_bot_iff (l : Fin n → ℤ) :
    weightSpace ρ.dual l ≠ ⊥ ↔ weightSpace ρ (-l) ≠ ⊥ := by
  rw [← Submodule.nontrivial_iff_ne_bot, ← Submodule.nontrivial_iff_ne_bot,
    (weightSpaceDualEquiv hchar hρ l).nontrivial_congr, nontrivial_dual_iff]

end Spanning

end TauCeti
