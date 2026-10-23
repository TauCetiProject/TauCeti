/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
-- Non-public: Mathlib's `Matrix.card_GL_field` and the factored order of `GL₂` are read off in the
-- proofs only.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- Non-public: `Matrix.GeneralLinearGroup.scalar_injective` identifies the centre with `Rˣ`, in the
-- proofs only.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation

/-!
# The order of the projective general linear group

The projective general linear group `PGL(n, R)` is the quotient of `GL n R` by its centre, and for
`n` nonempty that centre is a copy of the unit group `Rˣ`, embedded as the scalar matrices. So
`|PGL(n, R)| · |Rˣ| = |GL n R|`, the projective counterpart of Mathlib's
`Matrix.card_SL_mul_card_units`. Over a finite field `𝔽_q` this gives
`|PGL(n, 𝔽_q)| = ∏ i, (qⁿ - qⁱ) / (q - 1)`, and in size two `|PGL(2, 𝔽_q)| = q³ - q`.

## Main results

* `Matrix.ProjGenLinGroup.instFinite`: `PGL(n, R)` is finite when `R` is.
* `Matrix.GeneralLinearGroup.card_center`: for nonempty `n` the centre of `GL n R` has order
  `|Rˣ|`.
* `Matrix.card_PGL_mul_card_units`: `|PGL(n, R)| · |Rˣ| = |GL n R|` for nonempty `n`.
* `Matrix.card_PGL`: `|PGL(n, R)| = |GL n R| / |Rˣ|` when `R` has finitely many units.
* `Matrix.card_PGL_field`: `|PGL(n, 𝔽_q)| = ∏ i, (qⁿ - qⁱ) / (q - 1)`.
* `TauCeti.natCard_PGL_fin_two`: `|PGL(2, 𝔽_q)| = q³ - q`.
-/

public section

open scoped MatrixGroups

namespace Matrix

section CommRing

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The projective general linear group over a finite ring is finite. -/
instance ProjGenLinGroup.instFinite [Finite R] : Finite PGL(n, R) :=
  inferInstanceAs (Finite (GL n R ⧸ Subgroup.center (GL n R)))

variable [Nonempty n]

/-- For nonempty `n`, the centre of `GL n R` has as many elements as `Rˣ`: it is the image of the
injective scalar embedding. -/
theorem GeneralLinearGroup.card_center :
    Nat.card (Subgroup.center (GL n R)) = Nat.card Rˣ := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact (Nat.card_congr (MonoidHom.ofInjective GeneralLinearGroup.scalar_injective).toEquiv).symm

/-- **The order of `PGL(n, R)` times the number of units is the order of `GL n R`**, for nonempty
`n`. -/
theorem card_PGL_mul_card_units :
    Nat.card PGL(n, R) * Nat.card Rˣ = Nat.card (GL n R) := by
  rw [← GeneralLinearGroup.card_center (n := n)]
  exact (Subgroup.center (GL n R)).index_mul_card

/-- **The order of the projective general linear group** over a commutative ring with finitely
many units. -/
theorem card_PGL [Finite Rˣ] : Nat.card PGL(n, R) = Nat.card (GL n R) / Nat.card Rˣ :=
  Nat.eq_div_of_mul_eq_left Nat.card_pos.ne' card_PGL_mul_card_units

end CommRing

/-- **The order of the projective general linear group over a finite field**:
`|PGL(n, 𝔽_q)| = ∏ i, (qⁿ - qⁱ) / (q - 1)`. -/
theorem card_PGL_field {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] (n : ℕ) [NeZero n] :
    Nat.card PGL(n, 𝔽) =
      (∏ i : Fin n, (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ))) / (Fintype.card 𝔽 - 1) := by
  rw [card_PGL, card_GL_field, Nat.card_units, Nat.card_eq_fintype_card (α := 𝔽)]

end Matrix

namespace TauCeti

/-- **The order of `PGL(2, 𝔽_q)` is `q³ - q`.** -/
theorem natCard_PGL_fin_two (F : Type*) [Field F] [Fintype F] :
    Nat.card PGL(2, F) = Fintype.card F ^ 3 - Fintype.card F := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 2 :=
    ⟨Fintype.card F - 2, by have := Fintype.one_lt_card (α := F); omega⟩
  have h := Matrix.card_PGL_mul_card_units (n := Fin 2) (R := F)
  rw [natCard_GL_fin_two, Nat.card_units, Nat.card_eq_fintype_card (α := F), hm] at h
  have hcube : (m + 2) ^ 3 - (m + 2) = (m + 1) * ((m + 2) * (m + 3)) := by
    have : (m + 2) ^ 3 = (m + 1) * ((m + 2) * (m + 3)) + (m + 2) := by ring
    omega
  have hmpos : 0 < m + 1 := by omega
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hm, hcube]
  refine Nat.eq_of_mul_eq_mul_right hmpos ?_
  rw [hsub] at h
  rw [h]
  ring

end TauCeti
