/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
import Mathlib.Analysis.Normed.Group.Tannery
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Dual
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# The dual of a periodic Besov space

Let `φ` be a smooth bump function on `EuclideanSpace ℝ d`, with periodic Littlewood–Paley blocks
`Δₖ` on the torus `𝕋ᵈ = UnitAddTorus d`, and let `p, p'` and `q, q'` be pairs of Hölder conjugate
exponents in `[1, ∞]`. This file identifies the continuous dual of the periodic Besov space
`B^s_{p,q}(𝕋ᵈ)` with `B^{-s}_{p',q'}(𝕋ᵈ)`:

`(B^s_{p,q}(𝕋ᵈ))^* ≃ B^{-s}_{p',q'}(𝕋ᵈ)` for `1 ≤ p ≤ ∞` and `1 ≤ q < ∞`,

through the bilinear pairing `⟨u, w⟩ = ∑ₙ u(n) w(-n)` of Fourier coefficients, which for functions
is the integral `∫ u w` over the torus
(`TauCeti.UnitAddTorus.BesovSpace.pairing_eq_integral_of_coeff_eq`).

The series `∑ₙ u(n) w(-n)` need not converge absolutely, so the pairing is defined blockwise: with
`Δ⁺ₖ = ∑_{k - L ≤ j < k + L} Δⱼ`, where `L = φ.littlewoodPaleyOverlap φ` is the overlap width of
the partition,

`⟨u, w⟩ = ∑ₖ ∫ (Δₖ u) (Δ⁺ₖ w) = ∑ₖ ∑ₙ ψₖ(n) u(n) w(-n)`,

since the pieces `ψⱼ` are even and `Δ⁺ₖ` is the identity on the frequencies of `Δₖ`. Each term is
bounded by Hölder's inequality in `Lᵖ × L^{p'}`, and after weighting the `k`-th term by
`2^{ks} 2^{-ks} = 1` the series is bounded by Hölder's inequality in `ℓ^q × ℓ^{q'}` (Mathlib's
`lp.dualPairing`). For trigonometric polynomials the pairing is the finite sum `∑ₙ u(n) w(-n)`.

For `q < ∞` the trigonometric polynomials are dense in `B^s_{p,q}(𝕋ᵈ)`, for every `1 ≤ p ≤ ∞`: the
smooth truncations `∑_{i < N} ψᵢ u` converge to `u`, because the blocks of the remainder are
controlled by the blocks `Δᵢ u` with `i ≥ N`, a tail of an `ℓ^q` sequence. The case `p = ∞` is
included, since every block is a trigonometric polynomial, and so are `p = 1` and `p = ∞` in the
duality (on `ℝᵈ`, `TauCeti.BesovSpace.strongDualEquiv` needs `1 ≤ p < ∞`, so excludes `p = ∞`).
Consequently a continuous linear functional `Λ` on `B^s_{p,q}(𝕋ᵈ)` is determined by its values on
the monomials `eₙ`, and it is the pairing with the formal Fourier series `w(n) = Λ(e₋ₙ)`. That `w`
lies in `B^{-s}_{p',q'}(𝕋ᵈ)`, with norm at most a constant times `‖Λ‖`, is the norming argument of
Bahouri–Chemin–Danchin, Proposition 2.76: testing `Λ` on the trigonometric polynomials `ψₖ ĝ` with
`g ∈ Lᵖ(𝕋ᵈ)` gives `∫ (Δₖ w) g = Λ(ψₖ ĝ)`, and the dual norm of `L^{p'}(𝕋ᵈ)`
(`MeasureTheory.Lp.toDual`, an isometry for all Hölder conjugate exponents, including `p = 1` and
`p = ∞`) and of `ℓ^{q'}` turns these values into the bound.

The construction of the pairing through the enlarged blocks and the norming argument adapt the
Euclidean formalization in `TauCeti/Analysis/FunctionalSpaces/BesovSpace/Duality.lean` and
`TauCeti/Analysis/FunctionalSpaces/BesovSpace/Norming.lean` from tempered distributions on `ℝᵈ` to
Fourier coefficients on the torus.

## Main declarations

* `TauCeti.UnitAddTorus.BesovSpace.monomial`: the trigonometric monomial `eₙ` as an element of
  `B^s_{p,q}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.BesovSpace.span_monomial_closure_eq_top`: for `q < ∞` the trigonometric
  polynomials are dense in `B^s_{p,q}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.BesovSpace.pairing`: the pairing `B^s_{p,q}(𝕋ᵈ) × B^{-s}_{p',q'}(𝕋ᵈ) → ℂ`,
  a continuous bilinear map, with the series `TauCeti.UnitAddTorus.BesovSpace.hasSum_pairing`, the
  finite sums `TauCeti.UnitAddTorus.BesovSpace.pairing_eq_sum_of_support_subset` on trigonometric
  polynomials, the sum `TauCeti.UnitAddTorus.BesovSpace.pairing_eq_tsum_of_summable` of
  `∑ₙ u(n) w(-n)` whenever that series is summable, the integral
  `TauCeti.UnitAddTorus.BesovSpace.pairing_eq_integral_of_coeff_eq` for the coefficients of
  `f, g ∈ L²(𝕋ᵈ)`, and the bound `TauCeti.UnitAddTorus.BesovSpace.exists_norm_pairing_le`, uniform
  in the exponents.
* `TauCeti.UnitAddTorus.BesovSpace.strongDualEquiv`: **the duality
  `B^{-s}_{p',q'}(𝕋ᵈ) ≃ (B^s_{p,q}(𝕋ᵈ))^*`** for `1 ≤ p ≤ ∞` and `1 ≤ q < ∞`. Its inverse sends
  `Λ` to the coefficients `n ↦ Λ(e₋ₙ)`
  (`TauCeti.UnitAddTorus.BesovSpace.coeff_strongDualEquiv_symm_apply`) and is bounded uniformly in
  the exponents (`TauCeti.UnitAddTorus.BesovSpace.exists_norm_strongDualEquiv_symm_apply_le`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Proposition 2.76.
* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (periodic distributions and the periodic Besov spaces).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.11.2.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Besov spaces are built on `Lᵖ` for the product of the Haar probability measures on
-- the circle factors, given by this instance; use it here so that the blocks below live on the
-- same spaces.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable {φ : ContDiffBump (0 : EuclideanSpace ℝ d)}

attribute [local instance] isProbabilityMeasure_volume

/-! ### The enlarged blocks -/

/-- The sum `Δ⁺ₖ c = ∑_{k - L ≤ j < k + L} Δⱼ c` of the blocks of `c` near `k`, where
`L = φ.littlewoodPaleyOverlap φ`. -/
private def enlargedBlockLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) (c : (d → ℤ) → ℂ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  ∑ j ∈ Finset.Ico (k - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
    littlewoodPaleyBlockLp φ p j c

/-- **The terms of the pairing.** `∫ (Δₖ a) (Δ⁺ₖ b) = ∑ₙ ψₖ(n) a(n) b(-n)`: the cutoff
`∑_{k - L ≤ j < k + L} ψⱼ` of `Δ⁺ₖ` is `1` on the support of `ψₖ`, and the pieces are even. -/
private theorem integral_littlewoodPaleyBlockLp_mul_enlargedBlockLp {p p' : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ p')] (k : ℕ) (a b : (d → ℤ) → ℂ) :
    ∫ x, littlewoodPaleyBlockLp φ p k a x * enlargedBlockLp (φ := φ) p' k b x =
      ∑' n, (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * a n * b (-n) := by
  rw [integral_littlewoodPaleyBlockLp_mul]
  refine tsum_congr fun n ↦ ?_
  have h := congrArg (fun x : ℝ ↦ (x : ℂ) * a n * b (-n))
    (φ.sum_Ico_inhomogeneousLittlewoodPaley_mul k (latticePoint n))
  push_cast at h
  rw [← mFourierCoeffCLM_apply, enlargedBlockLp, map_sum, ← h, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mFourierCoeffCLM_apply, mFourierCoeff_littlewoodPaleyBlockLp,
    inhomogeneousLittlewoodPaley_latticePoint_neg]
  ring

/-- The pieces `ψₖ(n)` sum to `1`, so `∑ₖ ψₖ(n) a = a`. -/
private theorem hasSum_inhomogeneousLittlewoodPaley_latticePoint_mul (n : d → ℤ) (a : ℂ) :
    HasSum (fun k ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * a) a := by
  simpa using (Complex.hasSum_ofReal.2
    (φ.hasSum_inhomogeneousLittlewoodPaley (latticePoint n))).mul_right a

namespace BesovSpace

section EnlargedBlocks

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted enlarged block `2^{ks} Δ⁺ₖ w` is controlled by the weighted blocks of `w` of index
within `L` of `k`. -/
private theorem norm_smul_enlargedBlockLp_le (w : BesovSpace φ s p q) (k : ℕ) :
    ‖(((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlockLp (φ := φ) p k w.coeff‖ ≤
      2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ∑ j ∈ Finset.Ico (k - φ.littlewoodPaleyOverlap φ)
        (k + φ.littlewoodPaleyOverlap φ), 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j w.coeff‖ := by
  rw [norm_smul, Complex.norm_of_nonneg (by positivity), enlargedBlockLp]
  simpa using TauCeti.two_rpow_mul_norm_sum_Ico_le s (C := 1)
    (g := fun j ↦ littlewoodPaleyBlockLp φ p j w.coeff)
    (x := fun j ↦ littlewoodPaleyBlockLp φ p j w.coeff) (fun j ↦ (one_mul _).ge) k
    (φ.littlewoodPaleyOverlap φ)

/-- The weighted enlarged blocks `(2^{ks} Δ⁺ₖ w)ₖ` of `w ∈ B^s_{p,q}(𝕋ᵈ)`, an `ℓ^q` sequence of
`Lᵖ` functions. -/
private def enlargedWeightedBlocks (w : BesovSpace φ s p q) :
    lp (fun _ : ℕ ↦ Lp ℂ p (volume : Measure (UnitAddTorus d))) q :=
  ⟨fun k ↦ (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlockLp (φ := φ) p k w.coeff,
    ((Memℓp.sum_Ico_sub_add (memBesov_def.1 w.memBesov_coeff)
      (φ.littlewoodPaleyOverlap φ)).const_mul (2 ^ (|s| * φ.littlewoodPaleyOverlap φ))).mono
      fun k ↦ norm_smul_enlargedBlockLp_le w k⟩

private theorem enlargedWeightedBlocks_apply (w : BesovSpace φ s p q) (k : ℕ) :
    enlargedWeightedBlocks w k =
      (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlockLp (φ := φ) p k w.coeff :=
  (rfl)

private theorem norm_enlargedWeightedBlocks_le [Fact (1 ≤ q)] (w : BesovSpace φ s p q) :
    ‖enlargedWeightedBlocks w‖ ≤
      2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ‖w‖ := by
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  -- The window sums of the weighted block norms of `w`, as an element of `ℓ^q`.
  obtain ⟨b, hb, hbn⟩ :=
    lp.exists_eq_sum_Ico_sub_add_and_norm_le (lp.normSeq w.weightedBlocks)
      (φ.littlewoodPaleyOverlap φ)
  calc ‖enlargedWeightedBlocks w‖ ≤ ‖(2 ^ (|s| * φ.littlewoodPaleyOverlap φ) : ℝ) • b‖ :=
        lp.norm_mono hq fun k ↦ by
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, enlargedWeightedBlocks_apply, hb,
            Real.norm_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ ↦ by
              rw [lp.normSeq_apply]; positivity))]
          simp only [lp.normSeq_apply, norm_weightedBlocks_apply]
          exact norm_smul_enlargedBlockLp_le w k
    _ = 2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ‖b‖ := by
        rw [lp.norm_const_smul hq, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * (2 * φ.littlewoodPaleyOverlap φ * ‖w‖) := by
        rw [← norm_weightedBlocks w, ← lp.norm_normSeq w.weightedBlocks]
        gcongr
    _ = _ := by ring

variable (φ s p q) in
/-- `w ↦ (2^{ks} Δ⁺ₖ w)ₖ` as a bounded operator from `B^s_{p,q}(𝕋ᵈ)` to `ℓ^q(Lᵖ)`. -/
private def enlargedWeightedBlocksL [Fact (1 ≤ q)] :
    BesovSpace φ s p q →L[ℂ] lp (fun _ : ℕ ↦ Lp ℂ p (volume : Measure (UnitAddTorus d))) q :=
  LinearMap.mkContinuous
    { toFun := enlargedWeightedBlocks
      map_add' v w := lp.ext <| funext fun k ↦ by
        simp only [enlargedWeightedBlocks_apply, enlargedBlockLp, coeff_add, map_add,
          Finset.sum_add_distrib, smul_add, lp.coeFn_add, Pi.add_apply]
      map_smul' c w := lp.ext <| funext fun k ↦ by
        simp only [enlargedWeightedBlocks_apply, enlargedBlockLp, coeff_smul, map_smul,
          ← Finset.smul_sum, smul_comm _ c, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply] }
    (2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|s| * φ.littlewoodPaleyOverlap φ))
    norm_enlargedWeightedBlocks_le

private theorem enlargedWeightedBlocksL_apply [Fact (1 ≤ q)] (w : BesovSpace φ s p q) :
    enlargedWeightedBlocksL φ s p q w = enlargedWeightedBlocks w :=
  (rfl)

end EnlargedBlocks

/-! ### The pairing -/

section Pairing

variable {s : ℝ} {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
  [p.HolderConjugate p'] [q.HolderConjugate q']

variable (φ s p p' q q') in
/-- The **duality pairing** `⟨u, w⟩ = ∑ₖ ∫ (Δₖ u) (Δ⁺ₖ w)` of `u ∈ B^s_{p,q}(𝕋ᵈ)` and
`w ∈ B^{-s}_{p',q'}(𝕋ᵈ)`, for Hölder conjugate pairs `p, p'` and `q, q'`. Here
`Δ⁺ₖ = ∑_{k - L ≤ j < k + L} Δⱼ`, with `L = φ.littlewoodPaleyOverlap φ`, is the identity on the
frequencies of `Δₖ`. The pairing is the sum of the series `∑ₖ ∑ₙ ψₖ(n) u(n) w(-n)`
(`TauCeti.UnitAddTorus.BesovSpace.hasSum_pairing`), which is `∑ₙ u(n) w(-n)` when `u` is a
trigonometric polynomial (`TauCeti.UnitAddTorus.BesovSpace.pairing_eq_sum_of_support_subset`) and
whenever that series is summable (`TauCeti.UnitAddTorus.BesovSpace.pairing_eq_tsum_of_summable`).
-/
def pairing : BesovSpace φ s p q →L[ℂ] BesovSpace φ (-s) p' q' →L[ℂ] ℂ :=
  (lp.dualPairing q q'
    (fun _ : ℕ ↦ (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure (UnitAddTorus d)) p p')
    (K := ‖(ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure (UnitAddTorus d)) p p'‖₊)
    fun _ ↦ le_rfl).bilinearComp
    (weightedBlocksₗᵢ φ s p q).toContinuousLinearMap (enlargedWeightedBlocksL φ (-s) p' q')

/-- The pairing is the `ℓ^q × ℓ^{q'}` pairing of the weighted blocks `(2^{ks} Δₖ u)ₖ` and the
weighted enlarged blocks `(2^{-ks} Δ⁺ₖ w)ₖ`. -/
private theorem pairing_apply_eq_dualPairing (u : BesovSpace φ s p q)
    (w : BesovSpace φ (-s) p' q') :
    pairing φ s p p' q q' u w =
      lp.dualPairing q q' (fun _ : ℕ ↦ (ContinuousLinearMap.mul ℂ ℂ).lpPairing
          (volume : Measure (UnitAddTorus d)) p p')
        (K := ‖(ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure (UnitAddTorus d)) p p'‖₊)
        (fun _ ↦ le_rfl) u.weightedBlocks (enlargedWeightedBlocks w) := by
  rw [pairing, ContinuousLinearMap.bilinearComp_apply, LinearIsometry.coe_toContinuousLinearMap,
    weightedBlocksₗᵢ_apply, enlargedWeightedBlocksL_apply]

/-- The pairing is the sum over `k` of the integrals of the weighted blocks `2^{ks} Δₖ u` against
the weighted enlarged blocks `2^{-ks} Δ⁺ₖ w`. -/
private theorem pairing_apply_eq_tsum_lpPairing (u : BesovSpace φ s p q)
    (w : BesovSpace φ (-s) p' q') :
    pairing φ s p p' q q' u w = ∑' k, (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume p p'
      (u.weightedBlocks k) (enlargedWeightedBlocks w k) := by
  rw [pairing_apply_eq_dualPairing]
  exact lp.dualPairing_apply ..

omit [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q.HolderConjugate q'] in
/-- The `k`-th term of the pairing is `∑ₙ ψₖ(n) u(n) w(-n)`: the weights `2^{ks}` and `2^{-ks}`
cancel. -/
private theorem lpPairing_weightedBlocks_enlargedWeightedBlocks (u : BesovSpace φ s p q)
    (w : BesovSpace φ (-s) p' q') (k : ℕ) :
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume p p' (u.weightedBlocks k)
        (enlargedWeightedBlocks w k) =
      ∑' n, (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * u.coeff n *
        w.coeff (-n) := by
  have hweight : (((2 : ℝ) ^ (-s * k) : ℝ) : ℂ) * (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.rpow_neg_mul_mul_rpow_mul two_pos, Complex.ofReal_one]
  rw [weightedBlocks_apply, enlargedWeightedBlocks_apply, map_smul, map_smul,
    smul_apply, smul_smul, hweight, one_smul,
    ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_littlewoodPaleyBlockLp_mul_enlargedBlockLp k u.coeff w.coeff

/-- **The pairing as a series.** The pairing of `u ∈ B^s_{p,q}(𝕋ᵈ)` and `w ∈ B^{-s}_{p',q'}(𝕋ᵈ)` is
the sum of the convergent series `∑ₖ ∑ₙ ψₖ(n) u(n) w(-n)`, each inner sum having finitely many
nonzero terms. -/
theorem hasSum_pairing (u : BesovSpace φ s p q) (w : BesovSpace φ (-s) p' q') :
    HasSum (fun k ↦ ∑' n, (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * u.coeff n *
      w.coeff (-n)) (pairing φ s p p' q q' u w) := by
  rw [pairing_apply_eq_tsum_lpPairing]
  simp only [← lpPairing_weightedBlocks_enlargedWeightedBlocks u w]
  exact ((lp.memℓp u.weightedBlocks).holder 1 (lp.memℓp (enlargedWeightedBlocks w))
    (fun _ : ℕ ↦ (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume p p')
    (K := ‖(ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure (UnitAddTorus d)) p p'‖)
    fun _ ↦ le_rfl).summable_of_one.hasSum

/-- The pairing of `u` and `w` is `∑ₖ ∑ₙ ψₖ(n) u(n) w(-n)`. -/
theorem pairing_apply (u : BesovSpace φ s p q) (w : BesovSpace φ (-s) p' q') :
    pairing φ s p p' q q' u w =
      ∑' k, ∑' n, (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * u.coeff n *
        w.coeff (-n) :=
  (hasSum_pairing u w).tsum_eq.symm

/-- **The pairing of a trigonometric polynomial.** If the coefficients of `u` vanish outside a
finite set `t`, then `⟨u, w⟩ = ∑_{n ∈ t} u(n) w(-n)`. -/
theorem pairing_eq_sum_of_support_subset {t : Finset (d → ℤ)} {u : BesovSpace φ s p q}
    (hu : Function.support u.coeff ⊆ t) (w : BesovSpace φ (-s) p' q') :
    pairing φ s p p' q q' u w = ∑ n ∈ t, u.coeff n * w.coeff (-n) := by
  refine (hasSum_pairing u w).unique ?_
  have hu0 (n : d → ℤ) (hn : n ∉ t) : u.coeff n = 0 := Function.notMem_support.1 fun h ↦ hn (hu h)
  have ht (k : ℕ) : ∑' n, (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * u.coeff n *
      w.coeff (-n) = ∑ n ∈ t, (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) *
        u.coeff n * w.coeff (-n) :=
    tsum_eq_sum fun n hn ↦ by rw [hu0 n hn, mul_zero, zero_mul]
  simp_rw [ht]
  refine hasSum_sum fun n _ ↦ ?_
  simpa only [mul_assoc] using
    hasSum_inhomogeneousLittlewoodPaley_latticePoint_mul n (u.coeff n * w.coeff (-n))

/-- **The pairing as a series of coefficients.** If the series `∑ₙ u(n) w(-n)` is summable, then
`⟨u, w⟩` is its sum. The partial sums `∑_{k ≤ N} ψₖ(n) = φ(2^{-N} n)` lie in `[0, 1]`, so the
blockwise series converges to `∑ₙ u(n) w(-n)` by dominated convergence. -/
theorem pairing_eq_tsum_of_summable {u : BesovSpace φ s p q} {w : BesovSpace φ (-s) p' q'}
    (h : Summable fun n ↦ u.coeff n * w.coeff (-n)) :
    pairing φ s p p' q q' u w = ∑' n, u.coeff n * w.coeff (-n) := by
  set a : (d → ℤ) → ℂ := fun n ↦ u.coeff n * w.coeff (-n)
  have hbound (N : ℕ) (n : d → ℤ) : ‖∑ k ∈ Finset.range (N + 1),
      (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * a n‖ ≤ ‖a n‖ := by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg φ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) φ.le_one
  have hlim := tendsto_tsum_of_dominated_convergence h.norm
    (fun n ↦ (hasSum_inhomogeneousLittlewoodPaley_latticePoint_mul n (a n)).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)) (Eventually.of_forall hbound)
  refine tendsto_nhds_unique ((hasSum_pairing u w).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)) (hlim.congr fun N ↦ ?_)
  simp only [Function.comp_apply]
  rw [Summable.tsum_finsetSum fun k _ ↦ summable_of_ne_finset_zero fun n hn ↦ by
    rw [inhomogeneousLittlewoodPaley_eq_zero_of_notMem (φ := φ) k hn, Complex.ofReal_zero,
      zero_mul]]
  simp only [a, mul_assoc]

/-- **The pairing of square-integrable functions.** If `u` and `w` have the Fourier coefficients
of `f, g ∈ L²(𝕋ᵈ)`, then `⟨u, w⟩ = ∫ f g`: by Parseval's identity for `star f` and `g`, the
series `∑ₙ f̂(n) ĝ(-n)` converges to `∫ f g`. -/
theorem pairing_eq_integral_of_coeff_eq {u : BesovSpace φ s p q} {w : BesovSpace φ (-s) p' q'}
    {f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))} (hu : u.coeff = mFourierCoeff f)
    (hw : w.coeff = mFourierCoeff g) :
    pairing φ s p p' q q' u w = ∫ x, f x * g x := by
  have hstar (n : d → ℤ) :
      starRingEnd ℂ (mFourierCoeff (star f : Lp ℂ 2 volume) n) = mFourierCoeff f (-n) := by
    rw [mFourierCoeff_congr_ae (Lp.coeFn_star f), mFourierCoeff, mFourierCoeff, ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp [mFourier_neg]
  have hint : ∫ x, starRingEnd ℂ ((star f : Lp ℂ 2 volume) x) * g x = ∫ x, f x * g x :=
    integral_congr_ae (by filter_upwards [Lp.coeFn_star f] with x hx; simp [hx])
  have hP := hasSum_prod_mFourierCoeff (star f) g
  simp only [hstar, hint] at hP
  have hP' : HasSum (fun n ↦ u.coeff n * w.coeff (-n)) (∫ x, f x * g x) := by
    simpa [hu, hw, Function.comp_def] using (Equiv.neg (d → ℤ)).hasSum_iff.2 hP
  rw [pairing_eq_tsum_of_summable hP'.summable, hP'.tsum_eq]

variable (φ s) in
/-- **Hölder's inequality for the pairing.** There is `C`, depending only on `φ` and `s`, such that
`‖⟨u, w⟩‖ ≤ C ‖u‖_{B^s_{p,q}} ‖w‖_{B^{-s}_{p',q'}}` for all Hölder conjugate pairs `p, p'` and
`q, q'` and all `u` and `w`. -/
theorem exists_norm_pairing_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']
      (u : BesovSpace φ s p q) (w : BesovSpace φ (-s) p' q'),
      ‖pairing φ s p p' q q' u w‖ ≤ C * ‖u‖ * ‖w‖ := by
  refine ⟨2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|-s| * φ.littlewoodPaleyOverlap φ), by positivity,
    fun {p p' q q'} _ _ _ _ _ _ u w ↦ ?_⟩
  set D := lp.dualPairing q q'
    (fun _ : ℕ ↦ (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure (UnitAddTorus d)) p p')
    (K := ‖(ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure (UnitAddTorus d)) p p'‖₊)
    fun _ ↦ le_rfl
  have hD : ‖D‖ ≤ 1 := (lp.norm_dualPairing _ _).trans ((ContinuousLinearMap.norm_lpPairing_le
    _).trans (ContinuousLinearMap.opNorm_mul_le ℂ ℂ))
  calc ‖pairing φ s p p' q q' u w‖ = ‖D u.weightedBlocks (enlargedWeightedBlocks w)‖ := by
        rw [pairing_apply_eq_dualPairing]
    _ ≤ ‖D‖ * ‖u.weightedBlocks‖ * ‖enlargedWeightedBlocks w‖ := D.le_opNorm₂ _ _
    _ ≤ 1 * ‖u‖ *
          (2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|-s| * φ.littlewoodPaleyOverlap φ) * ‖w‖) := by
        rw [norm_weightedBlocks]
        gcongr
        exact norm_enlargedWeightedBlocks_le w
    _ = _ := by ring

end Pairing

/-! ### Trigonometric polynomials and their density -/

section Density

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

variable (φ s p q) in
/-- The **trigonometric monomial** `eₙ`, the formal Fourier series with coefficients
`Pi.single n 1`, as an element of `B^s_{p,q}(𝕋ᵈ)`. -/
def monomial (n : d → ℤ) : BesovSpace φ s p q :=
  ⟨Pi.single n 1, memBesov_of_finite_support ((Set.finite_singleton n).subset
    Pi.support_single_subset)⟩

@[simp]
theorem coeff_monomial (n : d → ℤ) : (monomial φ s p q n).coeff = Pi.single n 1 :=
  (rfl)

/-- **Trigonometric polynomials are combinations of monomials.** If the coefficients of `u` vanish
outside a finite set `t`, then `u = ∑_{n ∈ t} u(n) eₙ`. -/
theorem eq_sum_monomial_of_support_subset {t : Finset (d → ℤ)} {u : BesovSpace φ s p q}
    (hu : Function.support u.coeff ⊆ t) : u = ∑ n ∈ t, u.coeff n • monomial φ s p q n := by
  refine ext (funext fun m ↦ ?_)
  rw [coeff_sum, Finset.sum_apply]
  simp only [coeff_smul, coeff_monomial, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · exact Function.notMem_support.1 fun h ↦ hm (hu h)

/-- The block `Δⱼ (ψₖ c)` vanishes unless `k` lies in the window `j - L ≤ k < j + L`, for the
overlap width `L = φ.littlewoodPaleyOverlap φ`. -/
private theorem littlewoodPaleyBlockLp_mul_eq_zero {j k : ℕ}
    (hk : k ∉ Finset.Ico (j - φ.littlewoodPaleyOverlap φ) (j + φ.littlewoodPaleyOverlap φ))
    (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ p j
      (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * c n) = 0 := by
  rw [← map_zero (littlewoodPaleyBlockLp φ p j)]
  refine littlewoodPaleyBlockLp_congr fun n ↦ ?_
  rw [Pi.zero_apply, mul_zero, ← mul_assoc, ← Complex.ofReal_mul,
    φ.inhomogeneousLittlewoodPaley_mul_eq_zero_of_notMem_Ico hk, Complex.ofReal_zero, zero_mul]

variable (φ) in
/-- The coefficients `(∑_{i < N} ψᵢ(n)) c(n)` of the smooth truncation `S_N c = ∑_{i < N} ψᵢ c`. -/
private def truncationCoeff (N : ℕ) (c : (d → ℤ) → ℂ) : (d → ℤ) → ℂ :=
  fun n ↦ (∑ i ∈ Finset.range N, (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ)) * c n

/-- The smooth truncation is a trigonometric polynomial. -/
private theorem finite_support_truncationCoeff (N : ℕ) (c : (d → ℤ) → ℂ) :
    (Function.support (truncationCoeff φ N c)).Finite :=
  (finite_setOf_norm_latticePoint_le (2 ^ N * φ.rOut)).subset fun n hn ↦ by
    by_contra hlt
    simp only [Set.mem_ofPred_eq, not_le] at hlt
    refine hn ?_
    rw [truncationCoeff, Finset.sum_eq_zero fun i hi ↦ by
      rw [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm ((mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ one_le_two (Finset.mem_range.1 hi).le) φ.rOut_pos.le).trans hlt.le),
        Complex.ofReal_zero],
      zero_mul]

variable (φ) in
/-- The **smooth truncation** `S_N u = ∑_{i < N} ψᵢ u` of `u ∈ B^s_{p,q}(𝕋ᵈ)`. -/
private def truncation (N : ℕ) (u : BesovSpace φ s p q) : BesovSpace φ s p q :=
  ⟨truncationCoeff φ N u.coeff, memBesov_of_finite_support (finite_support_truncationCoeff N _)⟩

private theorem coeff_truncation (N : ℕ) (u : BesovSpace φ s p q) :
    (truncation φ N u).coeff = truncationCoeff φ N u.coeff :=
  (rfl)

/-- The blocks of the remainder `u - S_N u` are the finite sums
`Δₖ (u - S_N u) = ∑_{k - L ≤ i < k + L, N ≤ i} Δₖ (ψᵢ u)`. -/
private theorem littlewoodPaleyBlockLp_sub_truncation (k N : ℕ) (u : BesovSpace φ s p q) :
    littlewoodPaleyBlockLp φ p k (u - truncation φ N u).coeff =
      ∑ i ∈ Finset.Ico (k - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
        if N ≤ i then littlewoodPaleyBlockLp φ p k
          (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * u.coeff n) else 0 := by
  have hite (i : ℕ) : (if N ≤ i then littlewoodPaleyBlockLp φ p k
      (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * u.coeff n) else 0) =
      littlewoodPaleyBlockLp φ p k (if N ≤ i then
        (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * u.coeff n) else 0) := by
    split_ifs <;> simp
  simp_rw [hite, ← map_sum]
  refine littlewoodPaleyBlockLp_congr fun n ↦ ?_
  have h := congrArg (fun x : ℝ ↦ (x : ℂ) * u.coeff n)
    (φ.mul_one_sub_sum_range_eq_sum_Ico k N (latticePoint n))
  push_cast [apply_ite (fun x : ℝ ↦ (x : ℂ))] at h
  rw [Finset.sum_mul] at h
  simp only [ite_mul, zero_mul, mul_assoc] at h
  simp only [coeff_sub, coeff_truncation, truncationCoeff, Pi.sub_apply, Finset.sum_apply,
    apply_ite (fun c : (d → ℤ) → ℂ ↦ c n), Pi.zero_apply]
  rw [Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  linear_combination h

variable (φ s p) in
/-- The remainder `u - S_N u` of the smooth truncation is controlled by the weighted blocks of `u`
of index at least `N`: there is `K`, depending only on `φ`, `s` and `p`, with
`‖u - S_N u‖ ≤ K ‖b‖_{ℓ^q}`, where `bᵢ = 2^{is} ‖Δᵢ u‖_p` for `i ≥ N` and `bᵢ = 0` for `i < N`. -/
private theorem exists_norm_sub_truncation_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : BesovSpace φ s p q) (N : ℕ),
      ‖u - truncation φ N u‖ ≤ K * ‖lp.normSeq u.weightedBlocks -
        ∑ i ∈ Finset.range N, lp.single q i (lp.normSeq u.weightedBlocks i)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_littlewoodPaleyBlockLp_mul_le φ
  set L := φ.littlewoodPaleyOverlap φ
  refine ⟨C * 2 ^ (|s| * L) * (2 * L), by positivity, fun {q} _ u N ↦ ?_⟩
  set b := lp.normSeq u.weightedBlocks -
    ∑ i ∈ Finset.range N, lp.single q i (lp.normSeq u.weightedBlocks i)
  have hb (i : ℕ) : b i =
      if N ≤ i then 2 ^ (s * i) * ‖littlewoodPaleyBlockLp φ p i u.coeff‖ else 0 := by
    simp only [b, lp.coeFn_sub, lp.coeFn_sum, Pi.sub_apply, Finset.sum_apply, lp.single_apply,
      Pi.single_apply, Finset.sum_ite_eq, Finset.mem_range, lp.normSeq_apply,
      norm_weightedBlocks_apply]
    split_ifs <;> first | omega | ring
  refine norm_le_of_forall_rpow_mul_norm_le_sum_Ico (by positivity) _ b fun k ↦ ?_
  rw [littlewoodPaleyBlockLp_sub_truncation]
  refine (TauCeti.two_rpow_mul_norm_sum_Ico_le s (C := C)
    (x := fun i ↦ if N ≤ i then littlewoodPaleyBlockLp φ p i u.coeff else 0) (fun i ↦ ?_)
    k L).trans ?_
  · split_ifs
    exacts [hC φ p k i u.coeff, by rw [norm_zero, mul_zero]]
  · rw [max_eq_left hC0]
    gcongr with i
    refine le_trans (le_of_eq ?_) (Real.le_norm_self _)
    rw [hb]
    split_ifs <;> simp

/-- **Density of the trigonometric polynomials.** For `q < ∞` and every `1 ≤ p ≤ ∞`, the
trigonometric monomials span a dense subspace of `B^s_{p,q}(𝕋ᵈ)`: the smooth truncations
`∑_{i < N} ψᵢ u` converge to `u`. -/
theorem span_monomial_closure_eq_top [Fact (1 ≤ q)] (hq : q ≠ ∞) :
    (Submodule.span ℂ (Set.range (monomial φ s p q))).topologicalClosure = ⊤ := by
  obtain ⟨K, -, hK⟩ := exists_norm_sub_truncation_le φ s p
  refine Submodule.eq_top_iff'.2 fun u ↦ ?_
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto (f := fun N ↦ truncation φ N u) (b := atTop) ?_
    (Eventually.of_forall fun N ↦ ?_)
  · -- `‖u - S_N u‖ ≤ K ‖f - ∑_{i < N} fᵢ eᵢ‖ → 0`, as `f = ∑ᵢ fᵢ eᵢ` in `ℓ^q` for `q < ∞`.
    have h := ((lp.hasSum_single hq (lp.normSeq u.weightedBlocks)).tendsto_sum_nat.const_sub
      (lp.normSeq u.weightedBlocks)).norm.const_mul K
    rw [sub_self, norm_zero, mul_zero] at h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) h
    rw [norm_sub_rev]
    exact hK u N
  · have h := eq_sum_monomial_of_support_subset (u := truncation φ N u)
      (t := (finite_support_truncationCoeff N u.coeff).toFinset)
      (by rw [coeff_truncation, Set.Finite.coe_toFinset])
    rw [SetLike.mem_coe, h]
    exact Submodule.sum_mem _ fun n _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

variable (φ s q) in
/-- The trigonometric polynomial `ψₖ ĝ`, with coefficients `ψₖ(n) ĝ(n)`, of `g ∈ Lᵖ(𝕋ᵈ)`. -/
private def blockOf (k : ℕ) (g : Lp ℂ p (volume : Measure (UnitAddTorus d))) : BesovSpace φ s p q :=
  ⟨fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * mFourierCoeff g n,
    memBesov_of_finite_support <| (finite_setOf_norm_latticePoint_le (ι := d)
      (2 ^ k * φ.rOut)).toFinset.finite_toSet.subset
      (support_inhomogeneousLittlewoodPaley_mul_subset k _)⟩

private theorem coeff_blockOf (k : ℕ)
    (g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (blockOf φ s q k g).coeff =
      fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * mFourierCoeff g n :=
  (rfl)

private theorem support_coeff_blockOf_subset (k : ℕ)
    (g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Function.support (blockOf φ s q k g).coeff ⊆
      (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ k * φ.rOut)).toFinset :=
  support_inhomogeneousLittlewoodPaley_mul_subset k _

private theorem blockOf_smul (k : ℕ) (a : ℂ)
    (g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    blockOf φ s q k (a • g) = a • blockOf φ s q k g := by
  refine ext (funext fun n ↦ ?_)
  simp only [coeff_smul, coeff_blockOf, Pi.smul_apply, smul_eq_mul, ← mFourierCoeffCLM_apply,
    map_smul]
  ring

end Density

/-! ### The duality -/

section Dual

variable {s : ℝ} {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
  [p.HolderConjugate p'] [q.HolderConjugate q']

/-- The pairing of the monomial `eₙ` with `w` is the coefficient `w(-n)`. -/
@[simp]
theorem pairing_monomial_left (n : d → ℤ) (w : BesovSpace φ (-s) p' q') :
    pairing φ s p p' q q' (monomial φ s p q n) w = w.coeff (-n) := by
  rw [pairing_eq_sum_of_support_subset (t := {n}) (by simp)]
  simp

/-- The pairing of `u` with the monomial `eₙ` is the coefficient `u(-n)`. -/
@[simp]
theorem pairing_monomial_right (u : BesovSpace φ s p q) (n : d → ℤ) :
    pairing φ s p p' q q' u (monomial φ (-s) p' q' n) = u.coeff (-n) := by
  refine (hasSum_pairing u _).unique ?_
  have h (k : ℕ) : ∑' m, (φ.inhomogeneousLittlewoodPaley k (latticePoint m) : ℂ) * u.coeff m *
      (monomial φ (-s) p' q' n).coeff (-m) =
      (φ.inhomogeneousLittlewoodPaley k (latticePoint (-n)) : ℂ) * u.coeff (-n) := by
    rw [tsum_eq_single (-n) fun m hm ↦ by
      rw [coeff_monomial, Pi.single_eq_of_ne (fun h ↦ hm (by rw [← h, neg_neg])), mul_zero]]
    simp
  simp_rw [h]
  exact hasSum_inhomogeneousLittlewoodPaley_latticePoint_mul (-n) (u.coeff (-n))

/-- On a trigonometric polynomial, a continuous linear functional is determined by its values on
the monomials: `Λ u = ∑_{n ∈ t} u(n) Λ(eₙ)` when the coefficients of `u` vanish outside `t`. -/
private theorem apply_eq_sum_of_support_subset
    (Λ : StrongDual ℂ (BesovSpace φ s p q)) {t : Finset (d → ℤ)} {u : BesovSpace φ s p q}
    (hu : Function.support u.coeff ⊆ t) :
    Λ u = ∑ n ∈ t, u.coeff n * Λ (monomial φ s p q n) := by
  conv_lhs => rw [eq_sum_monomial_of_support_subset hu]
  simp only [map_sum, map_smul, smul_eq_mul]

variable (φ s) in
/-- **Sums of the trigonometric polynomials `ψₖ ĝₖ`.** There is `K ≥ 0`, depending only on `φ` and
`s`, such that `‖∑_{k ∈ t} ψₖ ĝₖ‖_{B^s_{p,q}} ≤ K ‖w‖_{ℓ^q}` whenever `2^{ks} ‖gₖ‖_p ≤ wₖ` for
`k ∈ t`. -/
private theorem exists_norm_sum_blockOf_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (t : Finset ℕ)
      (g : ℕ → Lp ℂ p (volume : Measure (UnitAddTorus d))) (w : lp (fun _ : ℕ ↦ ℝ) q),
      (∀ k ∈ t, 2 ^ (s * k) * ‖g k‖ ≤ w k) → ‖∑ k ∈ t, blockOf φ s q k (g k)‖ ≤ K * ‖w‖ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_littlewoodPaleyBlockLp_mul_le φ
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_littlewoodPaleyBlockLp_mFourierCoeff_le φ
  set L := φ.littlewoodPaleyOverlap φ
  refine ⟨C₁ * C₂ * 2 ^ (|s| * L) * (2 * L), by positivity, fun {p q} _ _ t g w hw ↦ ?_⟩
  refine norm_le_of_forall_rpow_mul_norm_le_sum_Ico (by positivity) _ w fun j ↦ ?_
  -- The block `Δⱼ` of the sum only meets the pieces `ψₖ ĝₖ` with `k` within `L` of `j`.
  have hj : littlewoodPaleyBlockLp φ p j (∑ k ∈ t, blockOf φ s q k (g k)).coeff =
      ∑ k ∈ Finset.Ico (j - L) (j + L), if k ∈ t then littlewoodPaleyBlockLp φ p j
        (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) *
          mFourierCoeff (g k) n) else 0 := by
    rw [coeff_sum, map_sum, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun k hk ↦ (Finset.mem_filter.1 hk).2) fun k hkt hk ↦ ?_).symm
    rw [coeff_blockOf]
    exact littlewoodPaleyBlockLp_mul_eq_zero (fun h ↦ hk (Finset.mem_filter.2 ⟨h, hkt⟩)) _
  rw [hj]
  refine (TauCeti.two_rpow_mul_norm_sum_Ico_le s (C := C₁ * C₂)
    (x := fun k ↦ if k ∈ t then g k else 0) (fun k ↦ ?_) j L).trans ?_
  · split_ifs
    · calc _ ≤ C₁ * ‖littlewoodPaleyBlockLp φ p k (mFourierCoeff (g k))‖ := hC₁ φ p j k _
        _ ≤ C₁ * (C₂ * ‖g k‖) := by gcongr; exact hC₂ p k (g k)
        _ = _ := by ring
    · simp
  · rw [max_eq_left (by positivity)]
    gcongr with k
    split_ifs with hkt
    · exact (hw k hkt).trans (Real.le_norm_self _)
    · simp

/-- **Testing a functional on the blocks.** For the coefficients `e(n) = Λ(e₋ₙ)` of a functional
`Λ` on `B^s_{p,q}(𝕋ᵈ)` and `g ∈ Lᵖ(𝕋ᵈ)`, `∫ (Δₖ e) g = Λ(ψₖ ĝ)`. -/
private theorem toDual_littlewoodPaleyBlockLp_apply (Λ : StrongDual ℂ (BesovSpace φ s p q))
    (k : ℕ) (g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Lp.toDual ℂ volume p' p
        (littlewoodPaleyBlockLp φ p' k fun n ↦ Λ (monomial φ s p q (-n))) g =
      Λ (blockOf φ s q k g) := by
  have hfin : ∑ n ∈ (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ k * φ.rOut)).toFinset,
      (blockOf φ s q k g).coeff n * Λ (monomial φ s p q n) =
      ∑' n, (blockOf φ s q k g).coeff n * Λ (monomial φ s p q n) :=
    (tsum_eq_sum fun n hn ↦ by
      rw [Function.notMem_support.1 fun h ↦ hn (support_coeff_blockOf_subset k g h),
        zero_mul]).symm
  rw [Lp.toDual_apply, integral_littlewoodPaleyBlockLp_mul,
    apply_eq_sum_of_support_subset Λ (support_coeff_blockOf_subset k g), hfin,
    ← (Equiv.neg (d → ℤ)).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [Equiv.neg_apply, coeff_blockOf, inhomogeneousLittlewoodPaley_latticePoint_neg,
    neg_neg]
  ring

/-- **Assembling the blocks.** If there are `zₖ` with `2^{-ks} ‖Δₖ e‖_{p'} ≤ 2 ‖zₖ‖` whose finite
pairings with `ℓ^q` satisfy `‖∑_{k ∈ t} cₖ zₖ‖ ≤ B ‖c‖_q`, then `e ∈ B^{-s}_{p',q'}(𝕋ᵈ)` with norm
at most `2 B`. -/
private theorem exists_memBesov_and_norm_le_of_forall {e : (d → ℤ) → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (z : ℕ → ℂ)
    (hz : ∀ k : ℕ, (2 : ℝ) ^ (-s * k) * ‖littlewoodPaleyBlockLp φ p' k e‖ ≤ 2 * ‖z k‖)
    (hzc : ∀ (t : Finset ℕ) (c : lp (fun _ : ℕ ↦ ℂ) q), ‖∑ k ∈ t, c k * z k‖ ≤ B * ‖c‖) :
    ∃ h : MemBesov φ (-s) p' q' e, ‖(⟨e, h⟩ : BesovSpace φ (-s) p' q')‖ ≤ 2 * B := by
  obtain ⟨hx, hxn⟩ := lp.exists_memℓp_and_norm_le_of_forall_norm_sum_mul_le (p := q')
    (x := fun k : ℕ ↦ (2 : ℝ) ^ (-s * k) * ‖littlewoodPaleyBlockLp φ p' k e‖) z zero_le_two hB
    (fun k ↦ (Real.norm_of_nonneg (by positivity)).trans_le (hz k)) hzc
  refine ⟨memBesov_def.2 hx, (le_of_eq ?_).trans hxn⟩
  rw [← norm_weightedBlocks, ← lp.norm_normSeq]
  exact congrArg norm (lp.ext (funext fun k ↦
    (lp.normSeq_apply _ k).trans (norm_weightedBlocks_apply _ k)))

/-- **Pairing the tested values with `ℓ^q`.** Under the bound of `exists_norm_sum_blockOf_le` with
constant `K`, for functions `gₖ` with `‖gₖ‖_p ≤ 1` the values `zₖ = 2^{-ks} ∫ (Δₖ e) gₖ` satisfy
`‖∑_{k ∈ t} cₖ zₖ‖ ≤ ‖Λ‖ K ‖c‖_q`: the sum is `Λ` applied to `∑_{k ∈ t} ψₖ (cₖ 2^{-ks} gₖ)^`. -/
private theorem norm_sum_mul_toDual_apply_le {K : ℝ}
    (hKt : ∀ (t : Finset ℕ) (g : ℕ → Lp ℂ p (volume : Measure (UnitAddTorus d)))
      (w : lp (fun _ : ℕ ↦ ℝ) q), (∀ k ∈ t, 2 ^ (s * k) * ‖g k‖ ≤ w k) →
      ‖∑ k ∈ t, blockOf φ s q k (g k)‖ ≤ K * ‖w‖)
    (Λ : StrongDual ℂ (BesovSpace φ s p q)) (g : ℕ → Lp ℂ p (volume : Measure (UnitAddTorus d)))
    (hg1 : ∀ k, ‖g k‖ ≤ 1) (t : Finset ℕ) (c : lp (fun _ : ℕ ↦ ℂ) q) :
    ‖∑ k ∈ t, c k * (((2 ^ (-s * k) : ℝ) : ℂ) * Lp.toDual ℂ volume p' p
      (littlewoodPaleyBlockLp φ p' k fun n ↦ Λ (monomial φ s p q (-n))) (g k))‖ ≤
      ‖Λ‖ * K * ‖c‖ := by
  have heq : ∑ k ∈ t, c k * (((2 ^ (-s * k) : ℝ) : ℂ) * Lp.toDual ℂ volume p' p
      (littlewoodPaleyBlockLp φ p' k fun n ↦ Λ (monomial φ s p q (-n))) (g k)) =
      Λ (∑ k ∈ t, blockOf φ s q k ((c k * ((2 ^ (-s * k) : ℝ) : ℂ)) • g k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [blockOf_smul, map_smul, ← toDual_littlewoodPaleyBlockLp_apply (p' := p'), smul_eq_mul,
      mul_assoc]
  rw [heq]
  calc _ ≤ ‖Λ‖ * ‖∑ k ∈ t, blockOf φ s q k ((c k * ((2 ^ (-s * k) : ℝ) : ℂ)) • g k)‖ :=
        Λ.le_opNorm _
    _ ≤ ‖Λ‖ * (K * ‖lp.normSeq c‖) := by
        gcongr
        refine hKt t _ _ fun k _ ↦ ?_
        rw [lp.normSeq_apply, norm_smul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity), ← mul_assoc, mul_left_comm,
          Real.rpow_mul_mul_rpow_neg_mul two_pos, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (hg1 k)
    _ = ‖Λ‖ * K * ‖c‖ := by rw [lp.norm_normSeq, mul_assoc]

variable (φ s) in
/-- **Functionals are given by coefficients in `B^{-s}_{p',q'}(𝕋ᵈ)`.** There is `C`, depending only
on `φ` and `s`, such that for all Hölder conjugate pairs `p, p'` and `q, q'` and every continuous
linear functional `Λ` on `B^s_{p,q}(𝕋ᵈ)`, the coefficients `n ↦ Λ(e₋ₙ)` lie in
`B^{-s}_{p',q'}(𝕋ᵈ)` with norm at most `C ‖Λ‖`. -/
private theorem exists_memBesov_apply_monomial_neg_and_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']
      (Λ : StrongDual ℂ (BesovSpace φ s p q)),
      ∃ h : MemBesov φ (-s) p' q' (fun n ↦ Λ (monomial φ s p q (-n))),
        ‖(⟨_, h⟩ : BesovSpace φ (-s) p' q')‖ ≤ C * ‖Λ‖ := by
  obtain ⟨K, hK, hKt⟩ := exists_norm_sum_blockOf_le φ s
  refine ⟨2 * K, by positivity, fun {p p' q q'} _ _ _ _ _ _ Λ ↦ ?_⟩
  set e : (d → ℤ) → ℂ := fun n ↦ Λ (monomial φ s p q (-n))
  set T := Lp.toDual ℂ (volume : Measure (UnitAddTorus d)) p' p
  -- Functions `gₖ` with `‖gₖ‖_p ≤ 1` nearly norming `Δₖ e`.
  have hnear (k : ℕ) : ∃ g : Lp ℂ p (volume : Measure (UnitAddTorus d)), ‖g‖ ≤ 1 ∧
      ‖littlewoodPaleyBlockLp φ p' k e‖ ≤ 2 * ‖T (littlewoodPaleyBlockLp φ p' k e) g‖ := by
    rcases (norm_nonneg (littlewoodPaleyBlockLp φ p' k e)).eq_or_lt with h0 | h0
    · exact ⟨0, by simp, by rw [← h0]; positivity⟩
    obtain ⟨g, hg1, hg⟩ := (T (littlewoodPaleyBlockLp φ p' k e)).exists_lt_apply_of_lt_opNorm
      ((half_lt_self h0).trans_eq (T.norm_map _).symm)
    exact ⟨g, hg1.le, by linarith⟩
  choose g hg1 hg using hnear
  obtain ⟨h, hn⟩ := exists_memBesov_and_norm_le_of_forall (φ := φ) (s := s) (p' := p')
    (q := q) (q' := q') (by positivity)
    (fun k ↦ ((2 ^ (-s * k) : ℝ) : ℂ) * T (littlewoodPaleyBlockLp φ p' k e) (g k))
    (fun k ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc (2 : ℝ) ^ (-s * k) * ‖littlewoodPaleyBlockLp φ p' k e‖
          ≤ 2 ^ (-s * k) * (2 * ‖T (littlewoodPaleyBlockLp φ p' k e) (g k)‖) := by
            gcongr; exact hg k
        _ = _ := by ring)
    (norm_sum_mul_toDual_apply_le (fun t g w ↦ hKt t g w) Λ g hg1)
  exact ⟨h, hn.trans_eq (by ring)⟩

/-- The coefficients `n ↦ Λ(e₋ₙ)` of a functional `Λ` on `B^s_{p,q}(𝕋ᵈ)` lie in
`B^{-s}_{p',q'}(𝕋ᵈ)`. -/
private theorem memBesov_apply_monomial_neg (Λ : StrongDual ℂ (BesovSpace φ s p q)) :
    MemBesov φ (-s) p' q' (fun n ↦ Λ (monomial φ s p q (-n))) :=
  ((exists_memBesov_apply_monomial_neg_and_norm_le φ s).choose_spec.2 Λ).fst

variable (φ s p p' q q') in
/-- `Λ ↦ (n ↦ Λ(e₋ₙ))`, the inverse of the duality, as a linear map. -/
private def ofStrongDual : StrongDual ℂ (BesovSpace φ s p q) →ₗ[ℂ] BesovSpace φ (-s) p' q' where
  toFun Λ := ⟨fun n ↦ Λ (monomial φ s p q (-n)), memBesov_apply_monomial_neg Λ⟩
  map_add' _ _ := ext (funext fun _ ↦ by simp)
  map_smul' _ _ := ext (funext fun _ ↦ by simp)

private theorem coeff_ofStrongDual (Λ : StrongDual ℂ (BesovSpace φ s p q)) (n : d → ℤ) :
    (ofStrongDual φ s p p' q q' Λ).coeff n = Λ (monomial φ s p q (-n)) :=
  (rfl)

private theorem norm_ofStrongDual_le (Λ : StrongDual ℂ (BesovSpace φ s p q)) :
    ‖ofStrongDual φ s p p' q q' Λ‖ ≤
      (exists_memBesov_apply_monomial_neg_and_norm_le φ s).choose * ‖Λ‖ :=
  ((exists_memBesov_apply_monomial_neg_and_norm_le φ s).choose_spec.2 Λ).snd

private theorem norm_pairing_flip_apply_le (w : BesovSpace φ (-s) p' q') :
    ‖(pairing φ s p p' q q').flip w‖ ≤ (exists_norm_pairing_le φ s).choose * ‖w‖ := by
  obtain ⟨hC0, hC⟩ := (exists_norm_pairing_le φ s).choose_spec
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  rw [ContinuousLinearMap.flip_apply]
  exact (hC u w).trans_eq (by ring)

variable (φ s p p' q q') in
/-- **The duality `(B^s_{p,q}(𝕋ᵈ))^* ≃ B^{-s}_{p',q'}(𝕋ᵈ)`**, for Hölder conjugate pairs `p, p'`
and `q, q'` with `1 ≤ p ≤ ∞` and `1 ≤ q < ∞`: `w ∈ B^{-s}_{p',q'}(𝕋ᵈ)` acts on `B^s_{p,q}(𝕋ᵈ)` by
the pairing `u ↦ ⟨u, w⟩` (`TauCeti.UnitAddTorus.BesovSpace.strongDualEquiv_apply`), and the inverse
sends a functional `Λ` to the coefficients `n ↦ Λ(e₋ₙ)`
(`TauCeti.UnitAddTorus.BesovSpace.coeff_strongDualEquiv_symm_apply`). -/
def strongDualEquiv (hq : q ≠ ∞) :
    BesovSpace φ (-s) p' q' ≃L[ℂ] StrongDual ℂ (BesovSpace φ s p q) :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun w := (pairing φ s p p' q q').flip w
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := ofStrongDual φ s p p' q q'
      left_inv w := ext (funext fun n ↦ by
        rw [coeff_ofStrongDual, ContinuousLinearMap.flip_apply, pairing_monomial_left, neg_neg])
      right_inv Λ := ContinuousLinearMap.ext_on
        (Submodule.dense_iff_topologicalClosure_eq_top.2 (span_monomial_closure_eq_top hq))
        (by
          rintro _ ⟨m, rfl⟩
          rw [ContinuousLinearMap.flip_apply, pairing_monomial_left, coeff_ofStrongDual,
            neg_neg]) }
    _ _ norm_pairing_flip_apply_le norm_ofStrongDual_le

@[simp]
theorem strongDualEquiv_apply (hq : q ≠ ∞) (w : BesovSpace φ (-s) p' q')
    (u : BesovSpace φ s p q) :
    strongDualEquiv φ s p p' q q' hq w u = pairing φ s p p' q q' u w :=
  (rfl)

@[simp]
theorem coeff_strongDualEquiv_symm_apply (hq : q ≠ ∞) (Λ : StrongDual ℂ (BesovSpace φ s p q))
    (n : d → ℤ) :
    ((strongDualEquiv φ s p p' q q' hq).symm Λ).coeff n = Λ (monomial φ s p q (-n)) :=
  (rfl)

variable (φ s) in
/-- **The inverse of the duality is bounded uniformly in the exponents.** There is `C`, depending
only on `φ` and `s`, such that the element of `B^{-s}_{p',q'}(𝕋ᵈ)` representing a functional `Λ`
on `B^s_{p,q}(𝕋ᵈ)` has norm at most `C ‖Λ‖`, for all Hölder conjugate pairs `p, p'` and `q, q'`
with `q < ∞`. -/
theorem exists_norm_strongDualEquiv_symm_apply_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q'] (hq : q ≠ ∞)
      (Λ : StrongDual ℂ (BesovSpace φ s p q)),
      ‖(strongDualEquiv φ s p p' q q' hq).symm Λ‖ ≤ C * ‖Λ‖ :=
  ⟨_, (exists_memBesov_apply_monomial_neg_and_norm_le φ s).choose_spec.1,
    fun _ Λ ↦ norm_ofStrongDual_le Λ⟩

end Dual

end BesovSpace

end TauCeti.UnitAddTorus
