/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.BlockSucc
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# The upper-left block embedding of a general linear group in the next one

An invertible matrix of size `n` becomes one of size `n + 1` by placing it in the upper-left block
and filling the last row and column with those of the identity matrix.  That map on matrices is
`Matrix.blockSucc`, from `TauCeti/LinearAlgebra/Matrix/BlockSucc.lean`; being multiplicative and
unital, it induces the **block inclusion**
`TauCeti.glBlockSucc : GL (Fin n) k →* GL (Fin (n + 1)) k`, the embedding that fixes the last
basis vector, which this file builds.

This is the step of the chain `GL 1 ⊂ GL 2 ⊂ ⋯ ⊂ GL n` along which the general linear groups are
restricted.  `TauCeti.glBlockSucc_diagGL` records that it matches the corresponding chain of
diagonal tori, and `TauCeti.det_glBlockSucc` that it carries special linear matrices to special
linear matrices.

## Main definitions

* `TauCeti.glBlockSucc`: the induced group homomorphism `GL (Fin n) k →* GL (Fin (n + 1)) k`.

## Main results

* `TauCeti.glBlockSucc_injective`: the block inclusion is injective.
* `TauCeti.glBlockSucc_diagGL`: it matches the chains of diagonal tori, appending a `1`.
* `TauCeti.det_glBlockSucc`: it preserves determinants.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section Semiring

variable [Semiring k]

/-- **The block inclusion** `GL (Fin n) k →* GL (Fin (n + 1)) k`: an invertible matrix is placed in
the upper-left block and the last basis vector is fixed.  This is the step of the chain
`GL 1 ⊂ GL 2 ⊂ ⋯` along which representations of the general linear groups are restricted. -/
def glBlockSucc : GL (Fin n) k →* GL (Fin (n + 1)) k :=
  Units.map (blockSuccMonoidHom k n)

@[simp]
theorem coe_glBlockSucc (g : GL (Fin n) k) :
    (glBlockSucc k n g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      blockSucc (g : Matrix (Fin n) (Fin n) k) :=
  blockSuccMonoidHom_apply _

/-- The block inclusion is injective, so it really embeds `GL (Fin n) k` in `GL (Fin (n + 1)) k`
and the chain `GL 1 ⊂ GL 2 ⊂ ⋯` is a chain of subgroups.  Use it to identify two invertible
matrices from the equality of their extensions. -/
theorem glBlockSucc_injective : Function.Injective (glBlockSucc k n) := by
  intro g h hgh
  refine Units.ext (blockSucc_injective ?_)
  rw [← coe_glBlockSucc, ← coe_glBlockSucc]
  exact congrArg (fun u : GL (Fin (n + 1)) k => (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) hgh

/-- The block inclusion matches the chains of diagonal tori: it sends the diagonal matrix with
entries `t` to the one whose entries are `t` followed by `1`. -/
@[simp]
theorem glBlockSucc_diagGL (t : Fin n → kˣ) :
    glBlockSucc k n (diagGL t) = diagGL (Fin.snoc t 1) := by
  refine Units.ext ?_
  ext i j
  rw [coe_glBlockSucc]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [diagGL_apply, (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [diagGL_apply, (Fin.castSucc_lt_last i).ne]
    | cast j => simp [Matrix.diagonal_apply, Fin.castSucc_inj]

end Semiring

section CommRing

variable [CommRing k]

/-- The block inclusion preserves determinants, so it carries special linear matrices to special
linear matrices. -/
@[simp]
theorem det_glBlockSucc (g : GL (Fin n) k) : (glBlockSucc k n g).det = g.det :=
  Units.ext <| by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      coe_glBlockSucc, det_blockSucc]

end CommRing

end TauCeti
