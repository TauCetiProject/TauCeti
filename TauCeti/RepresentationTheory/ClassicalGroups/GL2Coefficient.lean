/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Tensor
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Combinatorics

/-!
# The algebraic coefficients `V_(a,b)` of `GL₂`

For integers `a ≥ b`, the algebraic representation `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂`
(`TauCeti.gl2CoefficientRep k a b`) is the coefficient system of weight `(a, b)`. This file gives
its coordinate description over a field `k` whose weight characters separate weights (for instance
an infinite field, `TauCeti.weightChar_injective`):

* it has dimension `a - b + 1`;
* its weights are the `(a - i, b + i)` for `0 ≤ i ≤ a - b`, each of multiplicity one, and in
  particular `(a, b)` is a weight;
* a scalar matrix `z` acts by `z ^ (a + b)`.

The weights are read off from those of the symmetric power (`TauCeti.Weight.SymmetricPower`) and
the translation of weights by the determinant twist (`TauCeti.weightSpace_tprod_detPowerRep`).

## Main definitions

* `TauCeti.GL2CoefficientSpace k a b`: its carrier `Sym^{a-b}(k²) ⊗ k`.
* `TauCeti.gl2CoefficientRep k a b`: the representation `Sym^{a-b}(Std) ⊗ det^b` of `GL₂(k)`.

## Main results

* `TauCeti.finrank_gl2CoefficientRep`: `dim V_(a,b) = a - b + 1`.
* `TauCeti.weightSpace_gl2CoefficientRep_ne_bot_iff`: the weights of `V_(a,b)` are the `l` with
  `b ≤ l 0`, `b ≤ l 1` and `l 0 + l 1 = a + b`.
* `TauCeti.finrank_weightSpace_gl2CoefficientRep`: each weight has multiplicity one.
* `TauCeti.gl2CoefficientRep_scalar`: a scalar matrix `z` acts by `z ^ (a + b)`.
-/

public section

noncomputable section

open Matrix Module
open scoped TensorProduct

namespace TauCeti

variable (k : Type) [Field k] (a b : ℤ)

/-- The carrier `Sym^{a-b}(k²) ⊗ k` of the coefficient `V_(a,b)`. -/
abbrev GL2CoefficientSpace : Type := Sym[k]^(a - b).toNat (Fin 2 → k) ⊗[k] k

/-- The **algebraic coefficient** `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂`, for integers
`a ≥ b` (for `a < b` the symmetric power has exponent `0`). -/
abbrev gl2CoefficientRep : Representation k (GL (Fin 2) k) (GL2CoefficientSpace k a b) :=
  (symPowerRep k 2 (a - b).toNat).tprod (detPowerRep k 2 b)

variable {k a b}

/-- **`dim V_(a,b) = a - b + 1`.** -/
theorem finrank_gl2CoefficientRep (hab : b ≤ a) :
    (finrank k (GL2CoefficientSpace k a b) : ℤ) = a - b + 1 := by
  rw [finrank_tensorProduct, finrank_self, mul_one, SymmetricPower.finrank_eq, finrank_fin_fun,
    Nat.multichoose_two, Nat.cast_add, Int.toNat_of_nonneg (sub_nonneg.mpr hab), Nat.cast_one]

/-- The weight-`l` space of `V_(a,b)` is, through `W ⊗ k ≃ W`, the weight-`(l - b)` space of
`Sym^{a-b}(Std)`. -/
theorem weightSpace_gl2CoefficientRep (l : Fin 2 → ℤ) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l =
      Submodule.comap (TensorProduct.rid k _).toLinearMap
        (weightSpace (symPowerRep k 2 (a - b).toNat) (l - fun _ ↦ b)) :=
  weightSpace_tprod_detPowerRep _ b l

/-- **The weights of `V_(a,b)`** are the `l` with `b ≤ l 0`, `b ≤ l 1` and `l 0 + l 1 = a + b`,
that is, the `(a - i, b + i)` for `0 ≤ i ≤ a - b`. -/
theorem weightSpace_gl2CoefficientRep_ne_bot_iff
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) (l : Fin 2 → ℤ) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l ≠ ⊥ ↔
      b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b := by
  rw [weightSpace_gl2CoefficientRep, Submodule.comap_equiv_eq_map_symm, Ne,
    Submodule.map_eq_bot_iff, ← Ne, weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq hchar]
  simp only [Fin.forall_fin_two, Fin.sum_univ_two, Pi.sub_apply,
    Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  omega

/-- **The highest weight `(a, b)` is a weight** of `V_(a,b)`. -/
theorem weightSpace_gl2CoefficientRep_highest_ne_bot
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) ![a, b] ≠ ⊥ :=
  (weightSpace_gl2CoefficientRep_ne_bot_iff hchar hab _).2 ⟨by simpa using hab, by simp, by simp⟩

/-- **Every weight of `V_(a,b)` has multiplicity one.** -/
theorem finrank_weightSpace_gl2CoefficientRep
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a) {l : Fin 2 → ℤ}
    (hl : b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b) :
    finrank k (weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l) = 1 := by
  obtain ⟨s, hs⟩ := (exists_sym_weightOfMultiset_eq_iff (d := (a - b).toNat)
    (l - fun _ ↦ b)).2 ⟨by simp only [Fin.forall_fin_two, Pi.sub_apply]; omega, by
      simp only [Fin.sum_univ_two, Pi.sub_apply, Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
      omega⟩
  rw [weightSpace_gl2CoefficientRep, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.finrank_map_eq, ← hs, finrank_weightSpace_symPowerRep hchar s]

/-- **A scalar matrix `z` acts on `V_(a,b)` by `z ^ (a + b)`**: every weight of `V_(a,b)` has
coordinate sum `a + b`, and the weight spaces span. -/
theorem gl2CoefficientRep_scalar (hchar : Function.Injective (weightChar k (κ := Fin 2)))
    (hab : b ≤ a) (z : kˣ) (x : GL2CoefficientSpace k a b) :
    gl2CoefficientRep k a b (GeneralLinearGroup.scalar (Fin 2) z) x =
      ((z ^ (a + b) : kˣ) : k) • x := by
  have hdet : ⨆ l : Fin 2 → ℤ, weightSpace (detPowerRep k 2 b) l = ⊤ :=
    top_unique ((weightSpace_detPowerRep b).symm.le.trans (le_iSup _ _))
  have hx : x ∈ ⨆ l : Fin 2 → ℤ,
      weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) l := by
    rw [iSup_weightSpace_tprod_eq_top iSup_weightSpace_symPowerRep_eq_top hdet]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun x ↦ gl2CoefficientRep k a b
      (GeneralLinearGroup.scalar (Fin 2) z) x = ((z ^ (a + b) : kˣ) : k) • x) hx
    (fun l y hy ↦ ?_) (by simp) (fun y y' hy hy' ↦ by rw [map_add, hy, hy', smul_add])
  by_cases hy0 : y = 0
  · simp [hy0]
  have hl := (weightSpace_gl2CoefficientRep_ne_bot_iff hchar hab l).1
    ((Submodule.ne_bot_iff _).2 ⟨y, hy, hy0⟩)
  rw [apply_scalar_of_mem_weightSpace hy z, Fin.sum_univ_two, hl.2.2]

end TauCeti
