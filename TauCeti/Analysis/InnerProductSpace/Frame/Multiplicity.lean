/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Frame.Basic
import TauCeti.NumberTheory.NumericalSemigroup.CoefficientBounds

/-!
# Repetition and prescribed tight frame bounds

Repeating all the vectors of a finite family multiplies its frame operator by the number of
copies. If two families have coprime integral tight frame bounds, concatenating suitable
repetitions realizes every sufficiently large integral bound, without scaling any vector.
This preserves arithmetic conditions on the individual vectors, such as membership in a lattice.

The application to integral tight frames is `New.Parameters.exists_isTightFrame_of_coprime`
and `New.Parameters.exists_coprime_isTightFrame_sq` in lsernau/grh-lean (`72fead1`,
`grh/src/New/Derivatives/Vacuum/ShortVectors.lean` and `StandardDataProducts.lean`).
-/

public section

namespace TauCeti

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [Fintype κ]

/-- The frame operator of the concatenation is the sum of the two frame operators. -/
@[simp] theorem frameOperator_sum_elim (u : ι → E) (v : κ → E) :
    frameOperator 𝕜 (Sum.elim u v) = frameOperator 𝕜 u + frameOperator 𝕜 v := by
  ext x
  simp [Fintype.sum_sum_type]

/-- Indexing each vector by a second, independent index repeats its contribution to the
frame operator once per element of that index type. -/
@[simp] theorem frameOperator_comp_snd (u : ι → E) (κ : Type*) [Fintype κ] :
    frameOperator 𝕜 (u ∘ (Prod.snd : κ × ι → ι)) = Fintype.card κ • frameOperator 𝕜 u := by
  ext x
  simp [Fintype.sum_prod_type, Finset.smul_sum, smul_comm (Fintype.card κ)]

/-- Given finite families with coprime integral tight frame bounds `q` and `h`, obtain a family
with bound `m` by repeating each vector of the first family `a` times and each vector of the
second `b` times. The copies meet the prescribed minima `r` and `s`. -/
theorem exists_tight_frame_multiplicities_of_coprime {u : ι → E} {v : κ → E} {q h m r s : ℕ}
    (hu : frameOperator 𝕜 u = q • LinearMap.id) (hv : frameOperator 𝕜 v = h • LinearMap.id)
    (hqh : q.Coprime h) (hm : (q - 1) * (h - 1) + (r * q + s * h) ≤ m) :
    ∃ a b : ℕ, r ≤ a ∧ s ≤ b ∧
      frameOperator 𝕜 (Sum.elim (u ∘ (Prod.snd : Fin a × ι → ι))
        (v ∘ (Prod.snd : Fin b × κ → κ))) = m • LinearMap.id := by
  obtain ⟨a, b, ha, hb, hm'⟩ := hqh.exists_le_and_eq_add_mul hm
  refine ⟨a, b, ha, hb, ?_⟩
  simp only [frameOperator_sum_elim, frameOperator_comp_snd, Fintype.card_fin, hu, hv,
    smul_smul, ← add_nsmul, ← hm']

/-- The repetitions of two tight frames of coprime integral bounds can realize a square bound
whose square root exceeds any prescribed threshold and is coprime to `p`. Each original vector
can be required to occur with any prescribed minimum multiplicity. -/
theorem exists_tight_frame_square_multiplicities_of_coprime {u : ι → E} {v : κ → E}
    {q h p : ℕ} (hu : frameOperator 𝕜 u = q • LinearMap.id)
    (hv : frameOperator 𝕜 v = h • LinearMap.id) (hqh : q.Coprime h) (hp : 0 < p)
    (N r s : ℕ) :
    ∃ d > N, p.Coprime d ∧ ∃ a b : ℕ, r ≤ a ∧ s ≤ b ∧
      frameOperator 𝕜 (Sum.elim (u ∘ (Prod.snd : Fin a × ι → ι))
        (v ∘ (Prod.snd : Fin b × κ → κ))) = d ^ 2 • LinearMap.id := by
  let k := max N ((q - 1) * (h - 1) + (r * q + s * h))
  let d := p * k + 1
  have hkd : k < d := Nat.lt_succ_of_le (Nat.le_mul_of_pos_left _ hp)
  refine ⟨d, (le_max_left _ _).trans_lt hkd, ?_, ?_⟩
  · simp [d]
  · apply exists_tight_frame_multiplicities_of_coprime hu hv hqh
    exact (le_max_right _ _).trans (hkd.le.trans (Nat.le_self_pow (by decide) d))

end TauCeti
