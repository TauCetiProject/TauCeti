/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Linear maps out of a product basis

Let `b` and `c` be bases of `M` and `M'`, and let `v` and `w` be families of vectors of `P` and
`Q` indexed like them. The product of the linear maps sending `b` to `v` and `c` to `w` sends the
product basis `b.prod c` of `M × M'` to the family listing the vectors `(vᵢ, 0)` and then
`(0, wⱼ)` (`Module.Basis.prodMap_constr_comp_prod`). So every such family of `P × Q` is the image
of a product basis under a product of linear maps, which is how a function of tuples that
transforms under linear maps is evaluated on it.

## Main results

* `Module.Basis.prodMap_constr_comp_prod`: the image of a product basis under a product of
  linear maps given by `Module.Basis.constr`.
-/

public section

namespace Module.Basis

variable {ι κ R M M' P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- The product of the linear maps sending the basis `b` to `v` and the basis `c` to `w` sends the
product basis `b.prod c` to the family listing the vectors `(vᵢ, 0)` and then `(0, wⱼ)`. -/
theorem prodMap_constr_comp_prod (b : Basis ι R M) (c : Basis κ R M') (v : ι → P) (w : κ → Q) :
    ((b.constr R v).prodMap (c.constr R w) : M × M' → P × Q) ∘ b.prod c =
      Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) := by
  funext k
  cases k <;> simp

end Module.Basis
