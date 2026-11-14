/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp

/-!
# Coproducts of copies of a module

The categorical coproduct `∐_ι M` of copies of a module `M` in `ModuleCat R` is the module
`ι →₀ M` of finitely supported families: Mathlib identifies the coproduct with the direct sum
(`ModuleCat.coprodIsoDirectSum`), and the direct sum of copies of `M` with `ι →₀ M`
(`finsuppLEquivDirectSum`). The resulting linear equivalence sends the summand inclusion of index
`i` to `Finsupp.single i`.

## Main declarations

* `ModuleCat.coprodLinearEquivFinsupp`: the linear equivalence `∐_ι M ≃ₗ[R] (ι →₀ M)`.
* `ModuleCat.coprodLinearEquivFinsupp_ι_apply`, `ModuleCat.coprodLinearEquivFinsupp_symm_single`: it
  sends the summand inclusion of index `i` to `Finsupp.single i`.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{max v w} R) (ι : Type v) [DecidableEq ι]

/-- The coproduct `∐_ι M` of copies of a module `M` is the module `ι →₀ M` of finitely supported
families, the summand of index `i` going to the families supported at `i`. -/
def coprodLinearEquivFinsupp : (∐ fun _ : ι ↦ M : ModuleCat.{max v w} R) ≃ₗ[R] (ι →₀ M) :=
  (coprodIsoDirectSum fun _ : ι ↦ M).toLinearEquiv.trans
    (finsuppLEquivDirectSum R M ι).symm

variable {M ι}

/-- `ModuleCat.coprodLinearEquivFinsupp` sends `x` in the summand of index `i` to the family
supported at `i` with value `x`. -/
@[simp]
theorem coprodLinearEquivFinsupp_ι_apply (i : ι) (x : M) :
    coprodLinearEquivFinsupp M ι (Sigma.ι (fun _ : ι ↦ M) i x) = Finsupp.single i x := by
  rw [coprodLinearEquivFinsupp, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    ι_coprodIsoDirectSum_hom_apply, finsuppLEquivDirectSum_symm_lof]

/-- The inverse of `ModuleCat.coprodLinearEquivFinsupp` sends the family supported at `i` with
value `x` to `x` in the summand of index `i`. -/
@[simp]
theorem coprodLinearEquivFinsupp_symm_single (i : ι) (x : M) :
    (coprodLinearEquivFinsupp M ι).symm (Finsupp.single i x) = Sigma.ι (fun _ : ι ↦ M) i x := by
  rw [LinearEquiv.symm_apply_eq, coprodLinearEquivFinsupp_ι_apply]

end ModuleCat
