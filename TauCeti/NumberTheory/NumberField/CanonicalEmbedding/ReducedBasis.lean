/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

/-!
# An integral basis of bounded house

For a number field `K` of degree `d = [K : ℚ]`, the norm on `mixedSpace K` at `mixedEmbedding K x`
is the house of `x` (`TauCeti.NumberField.norm_mixedEmbedding`), so the closed unit ball of
`mixedSpace K` (`ConvexBody.closedBall 0 1 zero_le_one`) cuts out the elements of `K` whose
conjugates all have modulus at most `1`. Every nonzero algebraic integer has house at least `1`, so
every successive minimum of `mixedEmbedding.integerLattice K` with respect to the unit ball is at
least `1`. Minkowski's second theorem
(`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume`) bounds the product of those
minima by `√|discr K|`, and `ZLattice.exists_basis_mem_smul_successiveMin` turns the minima into a
`ℤ`-basis `TauCeti.NumberField.reducedIntegralBasis K` of `𝓞 K` whose `i`-th element has house at
most `max 1 ((i + 1) / 2) * √|discr K|`.

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

open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

section Construction

variable (K)

open scoped Classical in
/-- Every successive minimum of `mixedEmbedding.integerLattice K` with respect to the unit ball is
at least `1`, because every nonzero algebraic integer has house at least `1`. -/
private theorem one_le_successiveMin_integerLattice
    (i : Fin (finrank ℝ (mixedSpace K))) :
    1 ≤ ZLattice.successiveMin (mixedEmbedding.integerLattice K)
      (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i := by
  obtain ⟨⟨ht, v, hv, hvL⟩, -⟩ := ZLattice.successiveMin_isLeast
    (mixedEmbedding.integerLattice K)
    (ConvexBody.mem_interior_closedBall_self (0 : mixedSpace K) zero_lt_one) i
  obtain ⟨α, hα⟩ := (hvL 0).1
  replace hα : mixedEmbedding K (α : K) = v 0 := by simpa using hα
  have hα0 : (α : K) ≠ 0 := by
    intro h0
    exact hv.ne_zero 0 (by simpa [h0] using hα.symm)
  have hv0 : ‖v 0‖ ≤ ZLattice.successiveMin (mixedEmbedding.integerLattice K)
      (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i := by
    have hz := (hvL 0).2
    rwa [ConvexBody.coe_closedBall, smul_unitClosedBall_of_nonneg ht,
      mem_closedBall_zero_iff] at hz
  calc (1 : ℝ) ≤ house (α : K) := one_le_house_of_isIntegral α.2 hα0
    _ = ‖v 0‖ := by rw [← hα, norm_mixedEmbedding]
    _ ≤ ZLattice.successiveMin (mixedEmbedding.integerLattice K)
          (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i := hv0

open scoped Classical in
/-- The product of the successive minima of `mixedEmbedding.integerLattice K` with respect to the
unit ball of `mixedSpace K` is at most `√|discr K|`. -/
private theorem prod_successiveMin_integerLattice_le :
    ∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
      (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i ≤
      √|(discr K : ℝ)| := by
  have hmink := ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
    (K := ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one)
    (mixedEmbedding.integerLattice K) volume (fun _ hz ↦ by simpa using hz)
  have hdim : finrank ℝ (mixedSpace K) = nrRealPlaces K + 2 * nrComplexPlaces K := by
    rw [mixedEmbedding.finrank, ← card_add_two_mul_card_eq_rank]
  have hprod_nn : 0 ≤
      ∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
        (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i :=
    Finset.prod_nonneg fun i _ ↦ ZLattice.successiveMin_nonneg _ _ i
  set C : ℝ := 2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K
  have hC : 0 < C := by positivity
  rw [← mul_le_mul_iff_left₀ hC]
  calc (∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
          (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i) * C
      ≤ (∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
          (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i) *
          volume.real (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one :
            Set (mixedSpace K)) := by
        rw [ConvexBody.coe_closedBall]
        exact mul_le_mul_of_nonneg_left (two_pow_mul_two_pow_le_volume_real_closedBall K) hprod_nn
    _ ≤ 2 ^ finrank ℝ (mixedSpace K) * ZLattice.covolume (mixedEmbedding.integerLattice K) := hmink
    _ = √|(discr K : ℝ)| * C := by
        rw [hdim, covolume_integerLattice, two_mul, pow_add, pow_add, inv_pow]
        dsimp [C]
        field_simp

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
    rw [← coe_integerLatticeEquiv]
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
    have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase j,
        ZLattice.successiveMin (mixedEmbedding.integerLattice K) U k :=
      Finset.prod_induction _ (1 ≤ ·) (fun _ _ ha hb ↦ one_le_mul_of_one_le_of_one_le ha hb)
        le_rfl (fun k _ ↦ one_le_successiveMin_integerLattice K k)
    have hlam : ZLattice.successiveMin (mixedEmbedding.integerLattice K) U j ≤
        √|(discr K : ℝ)| := by
      refine (le_mul_of_one_le_right (ZLattice.successiveMin_nonneg _ _ j) hrest).trans ?_
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      exact prod_successiveMin_integerLattice_le K
    rw [← hj_val]
    exact hnorm.trans (mul_le_mul_of_nonneg_left hlam (le_trans zero_le_one (le_max_left _ _)))

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
