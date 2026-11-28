/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UnimodularFrame.Card

/-!
# The finite block mass in the norm of a theta lift

At a chosen place the local level fixes a standard frame pointwise, while at a twist place
it fixes an `r`-plane setwise. The normalized block mass combines these two level indices with
counts of rectangular matrices. It separates into a factor for the fixed chosen places and a
factor for the moving twist places. This is the finite scalar needed to compare the norm of a
chain with the norms of its single lifts.

The normalization is that of `New.DescentPair.gramFactor_div_card` in
`grh/src/New/Determinant/Norms/AdjointThetaLift.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open Finset Matrix
open scoped Pointwise

namespace TauCeti.ThetaLift

/-- The normalized finite Gram factor separates into the contribution of the chosen places
`M` and the twist contribution `c_Q`. Here `r` is the source rank, `t` the rank difference,
`q_v` the residue field size, and `W` the family of `r`-planes at the twist places. The latter
contribution is `(∏_{v ∈ Q} q_v)^(tr) · ∏_{v ∈ Q} ∏_{t < i ≤ t+r} (1 - q_v⁻ⁱ)`.

The denominator on the left is the product of the number of rectangular matrices and the
orders of the source general linear groups at the chosen places. The source group orders at
the twist places instead occur in the numerator, where they turn a count of subspaces into a
count of ordered frames. -/
theorem gramFactor_div_card {M Q : Type*} [Fintype M] [Fintype Q]
    (F : M → Type*) (K : Q → Type*) [∀ v, Field (F v)] [∀ v, Field (K v)]
    [∀ v, Fintype (F v)] [∀ v, Fintype (K v)] {t r : ℕ}
    (W : ∀ v, Submodule (K v) (Fin (t + r) → K v))
    (hW : ∀ v, Module.finrank (K v) (W v) = r) :
    let qM (v : M) : ℝ := Fintype.card (F v)
    let qQ (v : Q) : ℝ := Fintype.card (K v)
    let gM (v : M) : ℝ := Nat.card (GL (Fin r) (F v))
    let gQ (v : Q) : ℝ := Nat.card (GL (Fin r) (K v))
    ((∏ v, ((affineGroup (F v) (Fin t) (Fin r)).index : ℝ)) *
        (∏ v, (MulAction.stabilizer (GL (Fin (t + r)) (K v)) (W v)).index * gQ v *
          qQ v ^ (t * r))) /
        ((∏ v, qM v ^ ((t + r) * r) * gM v) * (∏ v, qQ v ^ ((t + r) * r))) =
      (∏ v, (∏ i ∈ range r, (1 - (qM v)⁻¹ ^ (t + i + 1))) / gM v) *
        ((∏ v, qQ v) ^ (t * r) * ∏ v, ∏ i ∈ range r, (1 - (qQ v)⁻¹ ^ (t + i + 1))) := by
  intro qM qQ gM gQ
  rw [← div_mul_div_comm, ← prod_div_distrib, ← prod_div_distrib, ← prod_pow,
    ← prod_mul_distrib]
  congr 1
  · refine prod_congr rfl fun v _ ↦ ?_
    rw [div_mul_eq_div_div, index_affineGroup_div]
  · refine prod_congr rfl fun v _ ↦ ?_
    have hnat := (W v).index_stabilizer_mul_natCard_GL_eq_prod
    rw [hW v, Fintype.card_fin, ← index_affineGroup_fin] at hnat
    have h : ((MulAction.stabilizer (GL (Fin (t + r)) (K v)) (W v)).index : ℝ) * gQ v =
        ((affineGroup (K v) (Fin t) (Fin r)).index : ℝ) := by
      dsimp only [gQ]
      exact_mod_cast hnat
    rw [h, mul_comm, mul_div_assoc, index_affineGroup_div]

end TauCeti.ThetaLift
