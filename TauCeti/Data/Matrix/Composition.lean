/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Composition

/-!
# Flattening block matrices: products and elementary perturbations of the identity

Mathlib's `Matrix.comp` flattens an `m × m` matrix whose entries are `ι × ι` matrices to an
`(m × ι) × (m × ι)` matrix. This file records that flattening is multiplicative also for
rectangular outer matrices, where Mathlib's `Matrix.compRingEquiv` covers only square ones, and how
it acts on the identity plus a single block entry that is itself a single entry:
`1 + (r Eₐᵦ) Eᵢⱼ` flattens to `1 + r E₍ᵢ,ₐ₎₍ⱼ,ᵦ₎`.

## Main results

* `Matrix.comp_mul`: `Matrix.comp` of a product of rectangular block matrices.
* `TauCeti.Matrix.comp_one_add_single_single`: `Matrix.comp` of `1 + (r Eₐᵦ) Eᵢⱼ`.
-/

public section

open Matrix

namespace Matrix

variable {R : Type*} {I J L M : Type*} [Fintype J] [Fintype L]

/-- Flattening `M_{I×J}(M_L(R)) → M_{(I×L)×(J×L)}(R)` is multiplicative, also for rectangular
outer matrices. -/
theorem comp_mul [NonUnitalNonAssocSemiring R] (A : Matrix I J (Matrix L L R))
    (B : Matrix J M (Matrix L L R)) :
    comp I M L L R (A * B) = comp I J L L R A * comp J M L L R B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [comp_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

end Matrix

namespace TauCeti.Matrix

variable {m ι R : Type*} [DecidableEq m] [DecidableEq ι] [Semiring R]

/-- `Matrix.comp` flattens `1 + (r Eₐᵦ) Eᵢⱼ` to `1 + r E₍ᵢ,ₐ₎₍ⱼ,ᵦ₎`. -/
theorem comp_one_add_single_single (i j : m) (a b : ι) (r : R) :
    comp m m ι ι R (1 + single i j (single a b r)) = 1 + single (i, a) (j, b) r := by
  rw [← compAddEquiv_apply, map_add, compAddEquiv_apply, compAddEquiv_apply, comp_one,
    comp_single_single]

end TauCeti.Matrix
