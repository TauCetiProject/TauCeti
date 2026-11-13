/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IntegerLattice

/-!
# An integral basis of bounded house

For a number field `K` of degree `d = [K : ℚ]`, each successive minimum of
`mixedEmbedding.integerLattice K` with respect to the closed unit ball of `mixedSpace K` is bounded
between `1` and `√|discr K|`
(`TauCeti.NumberField.mixedEmbedding.one_le_successiveMin_integerLattice` and
`TauCeti.NumberField.mixedEmbedding.successiveMin_integerLattice_le`). Applying
`ZLattice.exists_basis_mem_smul_successiveMin` on `ConvexBody.closedBall 0 1 zero_le_one` and
pulling back along `TauCeti.NumberField.mixedEmbedding.integerLatticeEquiv K` turns those minima
into a `ℤ`-basis `TauCeti.NumberField.reducedIntegralBasis K` of `𝓞 K` whose `i`-th element has
house at most `max 1 ((i + 1) / 2) * √|discr K|`.

Its largest house `TauCeti.NumberField.integralBasisHouse K` satisfies `1 ≤ integralBasisHouse K`
and `integralBasisHouse K ≤ max 1 (d / 2) * √|discr K|`, with `integralBasisHouse ℚ = 1`; it bounds
the local norm at every infinite place of all members of `reducedIntegralBasis K`.

## Main definitions

* `TauCeti.NumberField.reducedIntegralBasis K`: a `ℤ`-basis of `𝓞 K` indexed by
  `Fin (finrank ℚ K)` with house bounded via successive minima in terms of `[K : ℚ]` and
  `|discr K|`.
* `TauCeti.NumberField.integralBasisHouse K`: the largest house among the members of
  `reducedIntegralBasis K`.

## Main results

* `TauCeti.NumberField.house_reducedIntegralBasis_le_mul_sqrt_discr`:
  `house (reducedIntegralBasis K i : K) ≤ max 1 ((i + 1) / 2) * √|(discr K : ℝ)|`.
* `TauCeti.NumberField.integralBasisHouse_le_iff`:
  `integralBasisHouse K ≤ c ↔ ∀ i, house (reducedIntegralBasis K i : K) ≤ c`.
* `TauCeti.NumberField.one_le_integralBasisHouse` and `TauCeti.NumberField.integralBasisHouse_le`:
  `1 ≤ integralBasisHouse K ≤ max 1 ([K : ℚ] / 2) * √|(discr K : ℝ)|`.
* `TauCeti.NumberField.integralBasisHouse_rat`: `integralBasisHouse ℚ = 1`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Appendix C.2.
* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter V,
  Lemma 8, and Chapter VIII.
-/

public section

noncomputable section

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

section Construction

variable (K)

/-- **Existence of an integral basis of bounded house.** Every number field `K` has a `ℤ`-basis
`b` of `𝓞 K` indexed by `Fin (finrank ℚ K)` such that `b i` has house at most
`max 1 ((i + 1) / 2) * √|discr K|` and the embedded images `mixedEmbedding K (b i)` are linearly
independent over `ℝ`. -/
theorem exists_basis_ringOfIntegers_house_le :
    ∃ b : Basis (Fin (finrank ℚ K)) ℤ (𝓞 K),
      LinearIndependent ℝ (fun i ↦ mixedEmbedding K (b i : K)) ∧
      ∀ i : Fin (finrank ℚ K),
        house (b i : K) ≤ max 1 ((((i : ℕ) : ℝ) + 1) / 2) * √|(discr K : ℝ)| := by
  classical
  let U : ConvexBody (mixedSpace K) := ConvexBody.closedBall 0 1 zero_le_one
  obtain ⟨bL, hbL⟩ := ZLattice.exists_basis_mem_smul_successiveMin (K := U)
    (mixedEmbedding.integerLattice K)
    (ConvexBody.mem_interior_closedBall_self (0 : mixedSpace K) zero_lt_one)
    (fun _ hz ↦ by simpa [U] using hz)
  let eIdx : Fin (finrank ℝ (mixedSpace K)) ≃ Fin (finrank ℚ K) :=
    finCongr (mixedEmbedding.finrank K)
  let b : Basis (Fin (finrank ℚ K)) ℤ (𝓞 K) :=
    (bL.map (integerLatticeEquiv K).symm).reindex eIdx
  have hb_img (i : Fin (finrank ℚ K)) :
      mixedEmbedding K (b i : K) = (bL (eIdx.symm i) : mixedSpace K) := by
    simp [b]
  refine ⟨b, ?_, fun i ↦ ?_⟩
  · have hR := (bL.ofZLatticeBasis ℝ (mixedEmbedding.integerLattice K)).linearIndependent.comp
      eIdx.symm eIdx.symm.injective
    convert hR with i
    rw [Function.comp_apply, Basis.ofZLatticeBasis_apply, hb_img]
  · set j := eIdx.symm i
    have hj_val : (j : ℕ) = (i : ℕ) := by simp [j, eIdx]
    have hc : 0 ≤ max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
        ZLattice.successiveMin (mixedEmbedding.integerLattice K) U j :=
      mul_nonneg (le_trans zero_le_one (le_max_left _ _))
        (ZLattice.successiveMin_nonneg _ _ j)
    have hnorm : house (b i : K) ≤ max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
        ZLattice.successiveMin (mixedEmbedding.integerLattice K) U j := by
      have hz := hbL j
      rw [ConvexBody.coe_closedBall, smul_unitClosedBall_of_nonneg hc,
        mem_closedBall_zero_iff] at hz
      rwa [← norm_mixedEmbedding, hb_img]
    rw [← hj_val]
    exact hnorm.trans (mul_le_mul_of_nonneg_left (successiveMin_integerLattice_le K j)
      (le_trans zero_le_one (le_max_left _ _)))

/-- **An integral basis of bounded house** of `𝓞 K`, indexed by `Fin (finrank ℚ K)`, constructed
from successive minima so that its `i`-th element has house at most
`max 1 ((i + 1) / 2) * √|discr K|`. -/
def reducedIntegralBasis : Basis (Fin (finrank ℚ K)) ℤ (𝓞 K) :=
  (exists_basis_ringOfIntegers_house_le K).choose

/-- The images of `reducedIntegralBasis K` under `mixedEmbedding K` are linearly independent over
`ℝ`. -/
theorem linearIndependent_real_mixedEmbedding_reducedIntegralBasis :
    LinearIndependent ℝ fun i ↦ mixedEmbedding K (reducedIntegralBasis K i : K) :=
  (exists_basis_ringOfIntegers_house_le K).choose_spec.1

/-- The `i`-th member of `reducedIntegralBasis K` has house at most
`max 1 ((i + 1) / 2) * √|discr K|`. -/
theorem house_reducedIntegralBasis_le_mul_sqrt_discr (i : Fin (finrank ℚ K)) :
    house (reducedIntegralBasis K i : K) ≤
      max 1 ((((i : ℕ) : ℝ) + 1) / 2) * √|(discr K : ℝ)| :=
  (exists_basis_ringOfIntegers_house_le K).choose_spec.2 i

/-- **The house of `reducedIntegralBasis K`**: the largest house among the members of
`reducedIntegralBasis K`. -/
def integralBasisHouse : ℝ :=
  have : Nonempty (Fin (finrank ℚ K)) := Fin.pos_iff_nonempty.1 Module.finrank_pos
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ house (reducedIntegralBasis K i : K)

/-- Unfolds `integralBasisHouse K` as the supremum of the houses of `reducedIntegralBasis K`. -/
theorem integralBasisHouse_def :
    integralBasisHouse K =
      have : Nonempty (Fin (finrank ℚ K)) := Fin.pos_iff_nonempty.1 Module.finrank_pos
      Finset.univ.sup' Finset.univ_nonempty fun i ↦ house (reducedIntegralBasis K i : K) :=
  (rfl)

end Construction

/-- `integralBasisHouse K` is bounded above by `c` if and only if every member of
`reducedIntegralBasis K` has house at most `c`. -/
@[simp]
theorem integralBasisHouse_le_iff {c : ℝ} :
    integralBasisHouse K ≤ c ↔ ∀ i, house (reducedIntegralBasis K i : K) ≤ c := by
  simp [integralBasisHouse_def]

/-- Every member of `reducedIntegralBasis K` has house at most `integralBasisHouse K`. -/
theorem house_reducedIntegralBasis_le (i : Fin (finrank ℚ K)) :
    house (reducedIntegralBasis K i : K) ≤ integralBasisHouse K :=
  integralBasisHouse_le_iff.1 le_rfl i

/-- At every infinite place `w`, the embedded basis element `reducedIntegralBasis K i` has local
norm at most `integralBasisHouse K`. -/
theorem normAtPlace_mixedEmbedding_reducedIntegralBasis_le (w : InfinitePlace K)
    (i : Fin (finrank ℚ K)) :
    normAtPlace w (mixedEmbedding K (reducedIntegralBasis K i : K)) ≤ integralBasisHouse K := by
  classical
  exact (normAtPlace_le_norm w _).trans
    ((norm_mixedEmbedding _).trans_le (house_reducedIntegralBasis_le i))

/-- `integralBasisHouse K` is at least `1`. -/
theorem one_le_integralBasisHouse : 1 ≤ integralBasisHouse K := by
  let i₀ : Fin (finrank ℚ K) := ⟨0, Module.finrank_pos⟩
  have hi₀ : (reducedIntegralBasis K i₀ : K) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.2 ((reducedIntegralBasis K).ne_zero i₀)
  exact (one_le_house_of_isIntegral (reducedIntegralBasis K i₀).2 hi₀).trans
    (house_reducedIntegralBasis_le i₀)

/-- `integralBasisHouse K` is positive. -/
theorem integralBasisHouse_pos : 0 < integralBasisHouse K :=
  zero_lt_one.trans_le one_le_integralBasisHouse

/-- **Upper bound on `integralBasisHouse K` in terms of the degree and discriminant**:
`integralBasisHouse K ≤ max 1 ([K : ℚ] / 2) * √|discr K|`. -/
theorem integralBasisHouse_le :
    integralBasisHouse K ≤ max 1 ((finrank ℚ K : ℝ) / 2) * √|(discr K : ℝ)| := by
  rw [integralBasisHouse_le_iff]
  intro i
  refine (house_reducedIntegralBasis_le_mul_sqrt_discr K i).trans ?_
  gcongr
  have hi : (i : ℕ) + 1 ≤ finrank ℚ K := i.isLt
  exact_mod_cast hi

/-- `integralBasisHouse K` is at most `[K : ℚ] * √|discr K|`. -/
theorem integralBasisHouse_le_finrank_mul_sqrt_discr :
    integralBasisHouse K ≤ finrank ℚ K * √|(discr K : ℝ)| := by
  refine integralBasisHouse_le.trans ?_
  gcongr
  have hd : (1 : ℝ) ≤ finrank ℚ K := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  exact max_le hd (by linarith)

/-- Over `ℚ`, `integralBasisHouse ℚ` equals `1`. -/
@[simp]
theorem integralBasisHouse_rat : integralBasisHouse ℚ = 1 := by
  refine le_antisymm (integralBasisHouse_le.trans ?_) one_le_integralBasisHouse
  rw [Module.finrank_self, NumberField.discr_rat]
  norm_num

end TauCeti.NumberField
end
