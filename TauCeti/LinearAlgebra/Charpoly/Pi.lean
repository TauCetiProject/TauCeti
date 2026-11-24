/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Pi

/-!
# Characteristic polynomials on finite products

The characteristic polynomial of a coordinatewise endomorphism `LinearMap.piMap f` of a finite
product of finite free modules is the product of the characteristic polynomials of its
components (`LinearMap.charpoly_piMap`). This extends Mathlib's `LinearMap.charpoly_prodMap` from
two factors to finitely many; the proof splits off one factor at a time.

## Main results

* `LinearMap.charpoly_piMap`: the characteristic polynomial of `piMap f` is `∏ i, (f i).charpoly`.
-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R]

/-- The characteristic polynomial of a coordinatewise endomorphism of a product indexed by
`Fin n` is the product of the component characteristic polynomials. -/
private theorem charpoly_piMap_fin :
    ∀ (n : ℕ) (M : Fin n → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] (f : ∀ i, Module.End R (M i)),
      (piMap f).charpoly = ∏ i, (f i).charpoly
  | 0, M, _, _, _, _, f => by
    rw [← charpoly_toMatrix _ (Pi.basis fun i => Module.Free.chooseBasis R (M i))]
    simp [Matrix.charpoly, Matrix.det_isEmpty]
  | n + 1, M, _, _, _, _, f => by
    let e := Fin.consLinearEquiv R M
    rw [← e.symm.charpoly_conj, Fin.prod_univ_succ,
      ← charpoly_piMap_fin n (fun i => M i.succ) fun i => f i.succ, ← charpoly_prodMap]
    -- The conjugate of `piMap f` under `Fin.consLinearEquiv` is
    -- `prodMap (f 0) (piMap fun i => f i.succ)` by definition.
    congr 1

variable {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- **The characteristic polynomial is multiplicative on finite products.** The characteristic
polynomial of a coordinatewise endomorphism `piMap f` of a finite product of finite free modules
is the product of the characteristic polynomials of its components. -/
theorem charpoly_piMap (f : ∀ i, Module.End R (M i)) :
    (piMap f).charpoly = ∏ i, (f i).charpoly := by
  let σ := Fintype.equivFin ι
  let e := LinearEquiv.piCongrLeft' R M σ
  rw [← e.charpoly_conj, ← σ.symm.prod_comp,
    ← charpoly_piMap_fin _ (fun j => M (σ.symm j)) fun j => f (σ.symm j)]
  congr 1
  refine LinearMap.ext fun x => funext fun j => ?_
  simp [e, LinearEquiv.conj_apply]

end LinearMap
