/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.DegreeSlab
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard

/-!
# The volume budget for bounded-defect forms

The Pieri share formula and the volume of a unit-width degree slab give a bound in
terms of the actual cardinality of the cycle's exponent type. The product of geometric
sums on the volume side is the number of complete flags over the corresponding finite
field. This supplies the analytic comparison in
`New.FrobeniusCycle.index_mul_finrank_defectConditions_le` in
`grh/src/New/UpperBound/ElementaryDivisors/DefectCount.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open MeasureTheory Set

namespace TauCeti.FrobeniusCycle

/-- The exponents of block degree `n` are independently counted by stars and bars in
each letter. -/
theorem card_exponent {N : ℕ} [NeZero N] (k n : ℕ) :
    Fintype.card (Exponent N (k + 1) n) = (n + k).choose k ^ N := by
  classical
  rw [← Nat.card_eq_fintype_card]
  let e : Exponent N (k + 1) n ≃ (ZMod N → Sym (Fin (k + 1)) n) :=
    { toFun := fun β s ↦ (Sym.equivNatSumOfFintype _ _).symm
        ⟨fun b ↦ β.val (b, s), β.property s⟩
      invFun := fun β ↦ ⟨Finsupp.equivFunOnFinite.symm fun p ↦
          (Sym.equivNatSumOfFintype _ _ (β p.2)).val p.1,
        fun s ↦ by simp⟩
      left_inv := fun β ↦ Exponent.ext fun ⟨b, s⟩ ↦ by simp
      right_inv := fun β ↦ funext fun s ↦ (Sym.equivNatSumOfFintype _ _).injective (by
        apply Subtype.ext
        funext b
        simp) }
  rw [Nat.card_congr e, Nat.card_fun, Sym.natCard_sym_eq_choose, Nat.card_fin,
    Nat.card_eq_fintype_card, ZMod.card]
  have h : k + 1 + n - 1 = n + k := by omega
  rw [h, Nat.choose_symm_add]

/-- The Pieri region in a degree slab, multiplied by the flag-count factor, has volume
at most `1 + θ` times the number of monomials of degree `n` in each letter. The bound
allows each upper degree to exceed `n` by at most `A`, with a budget proportional to
`n` and inversely proportional to the number of letters and `k` (one less than the block rank). -/
theorem prod_mul_volume_real_inter_degreeSlab_le_card_exponent {N : ℕ} [NeZero N]
    {k n : ℕ} {v : ZMod N → Bool} {P A θ : ℝ} {D : ZMod N → ℝ}
    {Ω : Set (Fin (k + 1) × ZMod N → ℝ)} (hP : 1 < P)
    (hΩ : pieriStepMap v P 1 ⁻¹' Ω = pieriCone v P)
    (hn : 0 < n) (hA : 0 ≤ A) (hθ : θ ≤ 1) (hD : ∀ j, D j ≤ n + A)
    (hsmall : 2 * (N : ℝ) * k * A ≤ θ * n) :
    (∏ l : Fin (k + 1), ((P ^ N) ^ (l.val + 1) - 1) / (P ^ N - 1)) *
      volume.real (Ω ∩ degreeSlab (k + 1) D) ≤
        (1 + θ) * (Fintype.card (Exponent N (k + 1) n) : ℝ) := by
  rw [prod_mul_volume_real_inter_degreeSlab hP D hΩ, card_exponent, Nat.cast_pow]
  simpa only [ZMod.card] using volume_real_degreeSlab_le_choose_pow hn hA hθ hD
    (by simpa only [ZMod.card] using hsmall)

end TauCeti.FrobeniusCycle
