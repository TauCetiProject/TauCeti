/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
import TauCeti.Logic.Equiv.Fin.Basic

/-!
# Basic reindexing lemmas for multilinear maps

General reindexing lemmas for `MultilinearMap.domDomCongr` complementing
`Mathlib.LinearAlgebra.Multilinear.Basic`.

## Main results

* `MultilinearMap.domDomCongrLinearEquiv'_eq_domDomCongr`: on a constant domain family,
  `domDomCongrLinearEquiv'` agrees with `domDomCongr`.
* `MultilinearMap.domDomCongr_finCongr_domDomCongr_finCongr`: successive `finCongr` reindexings
  collapse to a single `finCongr` reindexing.
* `MultilinearMap.domDomCongr_compLinearMap`: reindexing commutes with `compLinearMap`.
-/

public section

namespace MultilinearMap

variable {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ : R₁ →+* R₂}
  {N₁ N₂ : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R₁ N₁] [Module R₂ N₂]

/-- On a constant domain family, `domDomCongrLinearEquiv'` agrees with `domDomCongr`. -/
theorem domDomCongrLinearEquiv'_eq_domDomCongr {S : Type*} [Semiring S] [Module S N₂]
    [SMulCommClass R₂ S N₂] {ι₁ ι₂ : Type*} (f : (ι₁ → N₁) →ₘₛₗ[σ] N₂) (e : ι₁ ≃ ι₂) :
    domDomCongrLinearEquiv' S σ (fun _ : ι₁ ↦ N₁) N₂ e f = f.domDomCongr e := by
  ext x
  simp only [domDomCongrLinearEquiv'_apply, coe_mk, Function.comp_apply, domDomCongr_apply,
    Equiv.piCongrLeft'_symm]
  exact congrArg f (funext fun i ↦ by simp only [Equiv.piCongrLeft'_apply, Equiv.symm_symm])

/-- Successive `finCongr` reindexings collapse to the composite `finCongr` reindexing. -/
@[simp]
theorem domDomCongr_finCongr_domDomCongr_finCongr {a b c : ℕ} (f : (Fin a → N₁) →ₘₛₗ[σ] N₂)
    (h₁ : a = b) (h₂ : b = c) :
    (f.domDomCongr (finCongr h₁)).domDomCongr (finCongr h₂) =
      f.domDomCongr (finCongr (h₁.trans h₂)) := by
  rw [← domDomCongr_trans, TauCeti.finCongr_trans]

/-- Reindexing after `compLinearMap` equals reindexing first and precomposing by the reindexed
family. -/
theorem domDomCongr_compLinearMap {R₃ : Type*} [Semiring R₃] {σ₁₂ : R₁ →+* R₂}
    {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    {ι₁ ι₂ N₃ : Type*} [AddCommMonoid N₃] [Module R₃ N₃]
    (f : (ι₁ → N₂) →ₘₛₗ[σ₂₃] N₃) (e : ι₁ ≃ ι₂) (g : ι₁ → N₁ →ₛₗ[σ₁₂] N₂) :
    (f.compLinearMap g).domDomCongr e = (f.domDomCongr e).compLinearMap fun i ↦ g (e.symm i) := by
  ext x; simp only [domDomCongr_apply, compLinearMap_apply, Equiv.symm_apply_apply]

end MultilinearMap
