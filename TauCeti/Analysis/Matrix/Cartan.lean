/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Cartan

/-!
# The Cartan decomposition of `GL(n, ℝ)` and `GL(n, ℂ)`

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix `g` factors uniquely as `g = k * exp X` with `k`
unitary (orthogonal when `𝕜 = ℝ`) and `X` Hermitian (symmetric when `𝕜 = ℝ`), and both factors
depend continuously on `g`. In Lie-theoretic terms, `𝔤𝔩(n, 𝕜) = 𝔨 ⊕ 𝔭` is the eigenspace
decomposition of the Cartan involution `X ↦ -Xᴴ`, with `𝔨` the skew-Hermitian and `𝔭` the Hermitian
matrices, and the map `K × 𝔭 → G`, `(k, X) ↦ k * exp X`, is a homeomorphism from the product of the
maximal compact subgroup `K = U(n, 𝕜)` and the vector space `𝔭` onto `G = GL(n, 𝕜)`.

This file specializes `TauCeti.cartanHomeomorph`, stated for complete normed real algebras with an
isometric continuous functional calculus, to matrices. Those structures exist on `Matrix n n 𝕜` only
for the scoped `ℓ²` operator norm, so the specialization is stated here for the default (entrywise)
topology, which that norm induces.

## Main declarations

* `Matrix.GeneralLinearGroup.cartanHomeomorph`: the homeomorphism
  `unitaryGroup n 𝕜 × selfAdjoint (Matrix n n 𝕜) ≃ₜ GL n 𝕜`, `(k, X) ↦ k * exp X`.
* `Matrix.GeneralLinearGroup.val_cartanHomeomorph_apply`,
  `Matrix.GeneralLinearGroup.cartanHomeomorph_symm_apply_fst`,
  `Matrix.GeneralLinearGroup.coe_cartanHomeomorph_symm_apply_snd`: the map and its inverse, whose
  factors are the unitary polar factor `g.polarUnitary` and the logarithm `log √(gᴴ g)` of the
  positive polar factor, written `cfc Real.log`.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1.
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open scoped MatrixOrder

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

variable (n 𝕜) in
/-- **The Cartan decomposition of `GL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`: the map `(k, X) ↦ k * exp X` is
a homeomorphism from the product of the unitary group (the orthogonal group when `𝕜 = ℝ`) and the
Hermitian (symmetric) matrices onto the general linear group. -/
def cartanHomeomorph : unitaryGroup n 𝕜 × selfAdjoint (Matrix n n 𝕜) ≃ₜ GL n 𝕜 := by
  -- The general statement needs a complete normed `ℝ`-algebra with an isometric functional
  -- calculus, which `Matrix n n 𝕜` is for the scoped `ℓ²` operator norm.
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact TauCeti.cartanHomeomorph (Matrix n n 𝕜)

/-- The Cartan decomposition map of `GL(n, 𝕜)` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanHomeomorph_apply (p : unitaryGroup n 𝕜 × selfAdjoint (Matrix n n 𝕜)) :
    (cartanHomeomorph n 𝕜 p : Matrix n n 𝕜) = p.1 * NormedSpace.exp (p.2 : Matrix n n 𝕜) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact TauCeti.val_cartanHomeomorph_apply p

/-- The unitary factor of the Cartan decomposition of `g` is its polar unitary factor. -/
@[simp]
theorem cartanHomeomorph_symm_apply_fst (g : GL n 𝕜) :
    ((cartanHomeomorph n 𝕜).symm g).1 = g.polarUnitary := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact TauCeti.cartanHomeomorph_symm_apply_fst g

/-- The Hermitian factor of the Cartan decomposition of `g` is the logarithm of `√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_snd (g : GL n 𝕜) :
    (((cartanHomeomorph n 𝕜).symm g).2 : Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star (g : Matrix n n 𝕜) * g)) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  -- `CFC.log` is `cfc Real.log`; it is only defined for normed algebras, and matrices carry a
  -- norm only in the `ℓ²` operator norm scope, so the statement uses `cfc Real.log` directly.
  exact TauCeti.coe_cartanHomeomorph_symm_apply_snd g

end Matrix.GeneralLinearGroup
