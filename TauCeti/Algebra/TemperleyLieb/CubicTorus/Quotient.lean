/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.RingTheory.TraceFunctional.Positive
-- Private: `interval_cases` and `module` are used only inside proofs.
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module

/-!
# The Jones quotient at `δ = √3` as the inversion-fixed cubic quantum torus

Building on the cubic quantum torus `CubicTorus N`, its inversion-fixed star-subalgebra
`cubicFixed N`, and the star-algebra homomorphism
`F_m = cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` from
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`, this file establishes:

* **Surjectivity of `cubicFixedHom m`**: commutator separation on the symmetrized Weyl elements
  `W(a) + W(a⁻¹)` shows that the Temperley–Lieb projections `p_j` generate the entire
  inversion-fixed subalgebra `cubicFixed (m - 1)`.
* **Tower inclusions and conditional expectation**: extending `Fin N → ZMod 3` by `0` in the last
  coordinate induces injective star-algebra inclusions `cubicTorusIncl N` and `cubicFixedIncl N`
  intertwining `strandIncl` and preserving `cubicScalarCoefficient`. Projecting onto Weyl basis
  elements with vanishing last coordinate defines a `CubicTorus N`-bimodule conditional expectation
  `cubicExpectation N : CubicTorus (N + 1) →ₗ[ℂ] CubicTorus N` satisfying
  `E_N (I_N x * y) = x * E_N y`, `s_N (E_N y) = s_{N + 1} y`, and `E_N (p_{last}) = 3⁻¹ • 1`.
* **Markov trace identity and positivity**: pulling back `(√3) ^ m * s_{m - 1}` along
  `cubicFixedHom m` defines a Markov trace `cubicFixedTrace` at `δ = √3`. By Markov uniqueness,
  every Markov trace `tr` at `√3` satisfies `tr m x = (√3) ^ m * s_{m - 1} (F_m x)`. Parseval
  positivity and faithfulness of `cubicScalarFunctional` imply `0 ≤ tr m (star x * x)` (the `ℓ = 6`
  discrete-series point `2 cos (π / 6)` of Jones's positivity theorem) and identify
  `(tr m).traceRadical` with `RingHom.ker (cubicFixedHom m)`.
* **Jones quotient equivalence and five-strand Jones–Wenzl vanishing**: passing to the quotient
  yields `IsMarkovTrace.quotientCubicFixedEquiv` (and star-algebra equivalence
  `IsMarkovTrace.quotientCubicFixedStarEquiv`) of complex dimension `(3 ^ (m - 1) + 1) / 2`
  intertwining `quotientStrandIncl` and `quotientTrace`. At five strands, `[6]_{√3} = 0`, so
  `cubicFixedHom 5` annihilates the negligible Jones–Wenzl projection `jonesWenzl (√3 : ℂ) 5`.

## Main definitions

* `TauCeti.TemperleyLieb.cubicTorusIncl` and `TauCeti.TemperleyLieb.cubicFixedIncl`:
  the coordinate star-algebra inclusions `CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1)` and
  `cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1)`.
* `TauCeti.TemperleyLieb.cubicExpectation`: the conditional expectation
  `E_N : CubicTorus (N + 1) →ₗ[ℂ] CubicTorus N` projecting onto `a_{last} = 0`.
* `TauCeti.TemperleyLieb.cubicFixedTrace`: the unnormalized Markov trace at `δ = √3` induced by
  `cubicScalarCoefficient`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedStarEquiv`: the algebra and star-algebra
  isomorphisms identifying the `m`-strand Jones quotient at `δ = √3` with `cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.cubicFixedHom_surjective`: `cubicFixedHom m` is surjective.
* `TauCeti.TemperleyLieb.cubicTorusIncl_injective`,
  `TauCeti.TemperleyLieb.cubicFixedIncl_injective`, and
  `TauCeti.TemperleyLieb.cubicFixedHom_strandIncl`: injectivity and tower compatibility of the
  coordinate inclusions.
* `TauCeti.TemperleyLieb.cubicExpectation_cubicTorusIncl_mul`,
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicExpectation`, and
  `TauCeti.TemperleyLieb.cubicExpectation_cubicProjection_last`: conditional expectation identities
  underlying the Markov trace relation.
* `TauCeti.TemperleyLieb.isMarkovTrace_cubicFixedTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom`, and
  `TauCeti.TemperleyLieb.markovTrace_eq_mul_cubicScalarCoefficient_cubicFixedHom`: the Markov-trace
  formula `tr m x = (√3) ^ m * s_{m - 1} (F_m x)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicFixedHom`: positivity of the Markov
  Hermitian form at `δ = √3` and identification of the trace radical with
  `RingHom.ker (cubicFixedHom m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`,
  `TauCeti.TemperleyLieb.exists_cubicFixedModel`, and
  `TauCeti.TemperleyLieb.cubicFixedHom_jonesWenzl_five`: dimension `(3 ^ (m - 1) + 1) / 2`,
  packaged existence theorem for the inversion-fixed cubic torus model, and vanishing of the
  five-strand Jones–Wenzl projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702, Proposition 3.6.
* E. C. Rowell and H. Wenzl, `SO(N)_2` *braid group representations are Gaussian*, Quantum Topol.
  8 (2017), no. 1, 1–33.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Surjectivity of `cubicFixedHom` via commutator separation -/

private theorem eq_zero_of_two_mul_eq_zero_zmod3 {x : ZMod 3} (h : (2 : ZMod 3) * x = 0) :
    x = 0 := by
  revert x h
  decide

/-- The symmetrized Weyl element `S(a) = W(a) + W(a⁻¹)` in `CubicTorus N`. -/
private noncomputable def weylSymm (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  weyl N a + weyl N a⁻¹

private theorem weylSymm_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weylSymm N a⁻¹ = weylSymm N a := by
  simp [weylSymm, add_comm]

private theorem weylSymm_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weylSymm N a * weylSymm N b =
      (cubicFactor N a b : ℂ) • weylSymm N (a * b) +
        (((cubicFactor N a b)⁻¹ : ℂˣ) : ℂ) • weylSymm N (a * b⁻¹) := by
  simp only [weylSymm, add_mul, mul_add, weyl_mul, smul_add]
  rw [cubicFactor_inv_inv, cubicFactor_inv_fst, cubicFactor_inv_snd]
  have h1 : a⁻¹ * b⁻¹ = (a * b)⁻¹ := (mul_inv a b).symm
  have h2 : a⁻¹ * b = (a * b⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
  rw [h1, h2]
  abel

private theorem weylSymm_single_mem_range {N : ℕ} {R : Subalgebra ℂ (CubicTorus N)}
    (hproj : ∀ j : Fin N, cubicProjection N j ∈ R) (j : Fin N) :
    weylSymm N (Multiplicative.ofAdd (Pi.single j 1)) ∈ R := by
  have heq :
      weylSymm N (Multiplicative.ofAdd (Pi.single j 1)) =
        (3 : ℂ) • cubicProjection N j - 1 := by
    rw [cubicProjection_def, smul_smul, mul_inv_cancel₀ (by norm_num), one_smul,
      cubicSite_def, weyl_sq, weylSymm]
    abel
  rw [heq]
  exact R.sub_mem (R.smul_mem (hproj j) 3) R.one_mem

private theorem weylSymm_mul_mem_of_chainForm_ne_zero {N : ℕ} {R : Subalgebra ℂ (CubicTorus N)}
    {a b : Multiplicative (Fin N → ZMod 3)}
    (ha : weylSymm N a ∈ R) (hb : weylSymm N b ∈ R)
    (hB : chainForm N a.toAdd b.toAdd ≠ 0) :
    weylSymm N (a * b) ∈ R ∧ weylSymm N (a * b⁻¹) ∈ R := by
  set c : ℂˣ := cubicFactor N a b
  set d : ℂ := (c : ℂ) ^ 2 - ((c⁻¹ : ℂˣ) : ℂ) ^ 2
  have hba : cubicFactor N b a = c⁻¹ := cubicFactor_swap N a b
  have hmul1 : weylSymm N a * weylSymm N b =
      (c : ℂ) • weylSymm N (a * b) + ((c⁻¹ : ℂˣ) : ℂ) • weylSymm N (a * b⁻¹) :=
    weylSymm_mul N a b
  have hmul2 : weylSymm N b * weylSymm N a =
      ((c⁻¹ : ℂˣ) : ℂ) • weylSymm N (a * b) + (c : ℂ) • weylSymm N (a * b⁻¹) := by
    have hswap := weylSymm_mul N b a
    rw [hba, inv_inv, mul_comm b a] at hswap
    have hinv : b * a⁻¹ = (a * b⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
    rw [hinv, weylSymm_inv] at hswap
    exact hswap
  have hdet : d ≠ 0 := by
    intro hzero
    have heq : (c ^ 2 : ℂˣ) = (c⁻¹) ^ 2 := Units.ext (sub_eq_zero.mp (by simpa [d] using hzero))
    have h4 : c ^ 4 = 1 := by
      calc
        c ^ 4 = c ^ 2 * c ^ 2 := by rw [← pow_add]
        _ = c ^ 2 * (c⁻¹) ^ 2 := by rw [heq]
        _ = (c * c⁻¹) ^ 2 := by rw [mul_pow]
        _ = 1 := by simp
    have h1 : c = 1 := by
      have h3 : c ^ 3 = 1 := by
        rw [show c = cubicFactor N a b from rfl, cubicFactor_def]
        exact cubeRootPow_pow_three _
      rw [pow_succ, h3, one_mul] at h4
      exact h4
    rw [show c = cubicFactor N a b from rfl, cubicFactor_def] at h1
    exact hB (eq_zero_of_two_mul_eq_zero_zmod3 (cubeRootPow_eq_one_iff.mp h1))
  have hlin1 :
      (c : ℂ) • (weylSymm N a * weylSymm N b) - ((c⁻¹ : ℂˣ) : ℂ) • (weylSymm N b * weylSymm N a) =
        d • weylSymm N (a * b) := by
    rw [hmul1, hmul2, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    have hcc : (c : ℂ) * ((c⁻¹ : ℂˣ) : ℂ) = 1 := c.mul_inv
    have hc'c : ((c⁻¹ : ℂˣ) : ℂ) * (c : ℂ) = 1 := c.inv_mul
    rw [hcc, hc'c, ← sq, ← sq]
    dsimp only [d]
    module
  have hlin2 :
      (c : ℂ) • (weylSymm N b * weylSymm N a) - ((c⁻¹ : ℂˣ) : ℂ) • (weylSymm N a * weylSymm N b) =
        d • weylSymm N (a * b⁻¹) := by
    rw [hmul1, hmul2, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    have hcc : (c : ℂ) * ((c⁻¹ : ℂˣ) : ℂ) = 1 := c.mul_inv
    have hc'c : ((c⁻¹ : ℂˣ) : ℂ) * (c : ℂ) = 1 := c.inv_mul
    rw [hcc, hc'c, ← sq, ← sq]
    dsimp only [d]
    module
  constructor
  · have hmem : d • weylSymm N (a * b) ∈ R := by
      rw [← hlin1]
      exact R.sub_mem (R.smul_mem (R.mul_mem ha hb) _) (R.smul_mem (R.mul_mem hb ha) _)
    have hsmul := R.smul_mem hmem d⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at hsmul
  · have hmem : d • weylSymm N (a * b⁻¹) ∈ R := by
      rw [← hlin2]
      exact R.sub_mem (R.smul_mem (R.mul_mem hb ha) _) (R.smul_mem (R.mul_mem ha hb) _)
    have hsmul := R.smul_mem hmem d⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at hsmul

private theorem weylSymm_mem_of_projections {N : ℕ} {R : Subalgebra ℂ (CubicTorus N)}
    (hproj : ∀ j : Fin N, cubicProjection N j ∈ R)
    (a : Multiplicative (Fin N → ZMod 3)) :
    weylSymm N a ∈ R := by
  have hsingle : ∀ j : Fin N, weylSymm N (Multiplicative.ofAdd (Pi.single j 1)) ∈ R :=
    weylSymm_single_mem_range hproj
  suffices h : ∀ k : ℕ, k ≤ N →
      ∀ v : Fin N → ZMod 3, (∀ j : Fin N, k ≤ j.val → v j = 0) →
        weylSymm N (Multiplicative.ofAdd v) ∈ R by
    exact h N le_rfl a.toAdd fun j hj ↦ absurd hj (not_le.mpr j.isLt)
  intro k hk
  induction k with
  | zero =>
    intro v hv
    have hv0 : v = 0 := funext fun j ↦ hv j (Nat.zero_le _)
    subst hv0
    have h0 : weylSymm N (Multiplicative.ofAdd (0 : Fin N → ZMod 3)) = (2 : ℂ) • 1 := by
      simp only [weylSymm, ofAdd_zero, inv_one, weyl_one]
      module
    rw [h0]
    exact R.smul_mem R.one_mem 2
  | succ k ih =>
    have hkN : k < N := hk
    let j₀ : Fin N := ⟨k, hkN⟩
    have ihk := ih (Nat.le_of_succ_le hk)
    -- First handle the case where `v` has `j₀`-coordinate equal to `1`.
    have hstep1 : ∀ w : Fin N → ZMod 3, (∀ j : Fin N, k ≤ j.val → w j = 0) →
        weylSymm N (Multiplicative.ofAdd (w + Pi.single j₀ 1)) ∈ R := by
      cases k with
      | zero =>
        intro w hw
        have hw0 : w = 0 := funext fun j ↦ hw j (Nat.zero_le _)
        rw [hw0, zero_add]
        exact hsingle j₀
      | succ k' =>
        let j₁ : Fin N := ⟨k', by omega⟩
        have hform : ∀ w : Fin N → ZMod 3, (∀ j : Fin N, k' + 1 ≤ j.val → w j = 0) →
            chainForm N w (Pi.single j₀ 1) = w j₁ := by
          intro w hw
          rw [chainForm_single_right]
          have hpos : 0 < (j₀ : ℕ) := by simp [j₀]
          have hprev : (⟨(j₀ : ℕ) - 1, by omega⟩ : Fin N) = j₁ := Fin.ext (by simp [j₀, j₁])
          simp only [hpos, ↓reduceDIte, hprev]
          split_ifs with hnext
          · rw [hw ⟨(j₀ : ℕ) + 1, hnext⟩ (by simp [j₀]), sub_zero]
          · rw [sub_zero]
        have hnz : ∀ w : Fin N → ZMod 3, (∀ j : Fin N, k' + 1 ≤ j.val → w j = 0) →
            w j₁ ≠ 0 → weylSymm N (Multiplicative.ofAdd (w + Pi.single j₀ 1)) ∈ R := by
          intro w hw hw1
          have hB : chainForm N (Multiplicative.ofAdd w).toAdd
              (Multiplicative.ofAdd (Pi.single j₀ 1)).toAdd ≠ 0 := by
            simpa [hform w hw] using hw1
          simpa [ofAdd_add] using
            (weylSymm_mul_mem_of_chainForm_ne_zero (ihk w hw) (hsingle j₀) hB).1
        have hne1 : ∀ w : Fin N → ZMod 3, (∀ j : Fin N, k' + 1 ≤ j.val → w j = 0) →
            w j₁ = 0 → chainForm N w (Pi.single j₁ 1) ≠ 1 →
            weylSymm N (Multiplicative.ofAdd (w + Pi.single j₀ 1)) ∈ R := by
          intro w hw hw1 hBw
          let w' : Fin N → ZMod 3 := w + Pi.single j₁ 1
          have hw' : ∀ j : Fin N, k' + 1 ≤ j.val → w' j = 0 := by
            intro j hj
            have hjne : j ≠ j₁ := fun h ↦ by subst h; simp [j₁] at hj
            simp [w', hw j hj, Pi.single_eq_of_ne hjne]
          have hw'1 : w' j₁ ≠ 0 := by simp [w', hw1]
          have hmem' : weylSymm N (Multiplicative.ofAdd (w' + Pi.single j₀ 1)) ∈ R :=
            hnz w' hw' hw'1
          have hB' : chainForm N (Multiplicative.ofAdd (w' + Pi.single j₀ 1)).toAdd
              (Multiplicative.ofAdd (Pi.single j₁ 1)).toAdd ≠ 0 := by
            rw [toAdd_ofAdd, toAdd_ofAdd, chainForm_add_left, chainForm_add_left, chainForm_self,
              add_zero, chainForm_swap N (Pi.single j₁ 1) (Pi.single j₀ 1),
              chainForm_single_single_succ (show (j₁ : ℕ) + 1 = j₀ by simp [j₁, j₀]),
              ← sub_eq_add_neg]
            exact sub_ne_zero.mpr hBw
          have hres := (weylSymm_mul_mem_of_chainForm_ne_zero hmem' (hsingle j₁) hB').2
          have hidx : Multiplicative.ofAdd (w' + Pi.single j₀ 1) *
              (Multiplicative.ofAdd (Pi.single j₁ 1))⁻¹ =
              Multiplicative.ofAdd (w + Pi.single j₀ 1) := by
            apply Multiplicative.toAdd.injective
            simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, w']
            abel
          rwa [hidx] at hres
        intro w hw
        by_cases hw1 : w j₁ = 0
        · by_cases hBw : chainForm N w (Pi.single j₁ 1) = 1
          · -- Switch to `-w`, where `B(-w, e_{j₁}) = 2 ≠ 1`, to recover `S(w - e_{j₀})`,
            -- then subtract from `S(w) * S(e_{j₀}) = S(w + e_{j₀}) + S(w - e_{j₀})`.
            have hneg_supp : ∀ j : Fin N, k' + 1 ≤ j.val → (-w) j = 0 := fun j hj ↦ by
              simp [hw j hj]
            have hneg1 : (-w) j₁ = 0 := by simp [hw1]
            have hnegB : chainForm N (-w) (Pi.single j₁ 1) ≠ 1 := by
              rw [chainForm_neg_left, hBw]
              decide
            have hsub_mem :
                weylSymm N (Multiplicative.ofAdd (w - Pi.single j₀ 1)) ∈ R := by
              have hneg_mem := hne1 (-w) hneg_supp hneg1 hnegB
              have heq : Multiplicative.ofAdd (-w + Pi.single j₀ 1) =
                  (Multiplicative.ofAdd (w - Pi.single j₀ 1))⁻¹ := by
                apply Multiplicative.toAdd.injective
                simp only [toAdd_inv, toAdd_ofAdd]
                abel
              rw [heq, weylSymm_inv] at hneg_mem
              exact hneg_mem
            have hfac : cubicFactor N (Multiplicative.ofAdd w)
                (Multiplicative.ofAdd (Pi.single j₀ 1)) = 1 := by
              rw [cubicFactor_def, toAdd_ofAdd, toAdd_ofAdd, hform w hw, hw1, mul_zero,
                cubeRootPow_zero]
            have hprod := weylSymm_mul N (Multiplicative.ofAdd w)
              (Multiplicative.ofAdd (Pi.single j₀ 1))
            rw [hfac, inv_one, Units.val_one, one_smul, one_smul] at hprod
            have heq :
                weylSymm N (Multiplicative.ofAdd (w + Pi.single j₀ 1)) =
                  weylSymm N (Multiplicative.ofAdd w) *
                    weylSymm N (Multiplicative.ofAdd (Pi.single j₀ 1)) -
                  weylSymm N (Multiplicative.ofAdd (w - Pi.single j₀ 1)) := by
              have h1 : Multiplicative.ofAdd w * Multiplicative.ofAdd (Pi.single j₀ 1) =
                  Multiplicative.ofAdd (w + Pi.single j₀ 1) := by simp
              have h2 : Multiplicative.ofAdd w * (Multiplicative.ofAdd (Pi.single j₀ 1))⁻¹ =
                  Multiplicative.ofAdd (w - Pi.single j₀ 1) := by
                apply Multiplicative.toAdd.injective
                simp [sub_eq_add_neg]
              rw [h1, h2] at hprod
              exact eq_sub_of_add_eq hprod.symm
            rw [heq]
            exact R.sub_mem (R.mul_mem (ihk w hw) (hsingle j₀)) hsub_mem
          · exact hne1 w hw hw1 hBw
        · exact hnz w hw hw1
    -- Split any `v` supported on `< k + 1` according to `v j₀ ∈ {0, 1, 2}`.
    intro v hv
    let w : Fin N → ZMod 3 := Function.update v j₀ 0
    have hw : ∀ j : Fin N, k ≤ j.val → w j = 0 := by
      intro j hj
      by_cases hj0 : j = j₀
      · subst hj0; simp [w]
      · have hgt : k + 1 ≤ j.val := by
          have : j.val ≠ k := fun h ↦ hj0 (Fin.ext h)
          omega
        simp [w, hj0, hv j hgt]
    have hval : v j₀ = 0 ∨ v j₀ = 1 ∨ v j₀ = 2 := by
      have : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
      exact this (v j₀)
    rcases hval with hc | hc | hc
    · have hvw : v = w := by
        ext j
        by_cases hj0 : j = j₀
        · subst hj0; simp [w, hc]
        · simp [w, hj0]
      rw [hvw]
      exact ihk w hw
    · have hvw : v = w + Pi.single j₀ 1 := by
        ext j
        by_cases hj0 : j = j₀
        · subst hj0; simp [w, hc]
        · simp [w, hj0]
      rw [hvw]
      exact hstep1 w hw
    · have hvw : -v = -w + Pi.single j₀ 1 := by
        ext j
        by_cases hj0 : j = j₀
        · subst hj0
          simp only [Pi.neg_apply, Pi.add_apply, Pi.single_eq_same, w, Function.update_self,
            neg_zero, zero_add, hc]
          decide
        · simp [w, hj0]
      have hneg_w : ∀ j : Fin N, k ≤ j.val → (-w) j = 0 := fun j hj ↦ by simp [hw j hj]
      have hmem := hstep1 (-w) hneg_w
      rw [← hvw, ofAdd_neg, weylSymm_inv] at hmem
      exact hmem

/-- **Surjectivity of `cubicFixedHom m`**: the Temperley–Lieb algebra at `δ = √3` surjects onto
the inversion-fixed subalgebra `cubicFixed (m - 1)`. -/
theorem cubicFixedHom_surjective (m : ℕ) : Function.Surjective (cubicFixedHom m) := by
  let F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
    (cubicFixed (m - 1)).toSubalgebra.val.comp (cubicFixedHom m).toAlgHom
  have hproj : ∀ j : Fin (m - 1), cubicProjection (m - 1) j ∈ F.range := by
    intro j
    rw [AlgHom.mem_range]
    refine ⟨(Real.sqrt 3 : ℂ)⁻¹ • e (Real.sqrt 3 : ℂ) j, ?_⟩
    have hsqrt_ne : (Real.sqrt 3 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    simp only [F, AlgHom.comp_apply, Subalgebra.coe_val, StarAlgHom.coe_toAlgHom, map_smul,
      coe_cubicFixedHom_e, smul_smul, inv_mul_cancel₀ hsqrt_ne, one_smul]
  intro ⟨y, hy⟩
  have hy_eq :
      y = ∑ a : Multiplicative (Fin (m - 1) → ZMod 3),
        ((2 : ℂ)⁻¹ * (cubicBasis (m - 1)).repr y a) • weylSymm (m - 1) a := by
    have havg : y = (2 : ℂ)⁻¹ • (y + cubicInversion (m - 1) y) := by
      rw [(mem_cubicFixed (m - 1)).mp hy]
      module
    conv_lhs => rw [havg]
    conv_lhs => rw [← (cubicBasis (m - 1)).sum_repr y]
    simp only [map_sum, map_smul, ← Finset.sum_add_distrib, Finset.smul_sum, smul_add, smul_smul,
      cubicBasis_apply, cubicInversion_weyl, weylSymm]
  have hy_mem : y ∈ F.range := by
    rw [hy_eq]
    exact F.range.sum_mem fun a _ ↦
      F.range.smul_mem (weylSymm_mem_of_projections hproj a) _
  rw [AlgHom.mem_range] at hy_mem
  obtain ⟨x, hx⟩ := hy_mem
  exact ⟨x, Subtype.ext hx⟩

/-! ### Tower inclusions and conditional expectation -/

private def snocZero (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    Multiplicative (Fin (N + 1) → ZMod 3) :=
  Multiplicative.ofAdd (Fin.snoc a.toAdd 0)

private theorem snocZero_def (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    snocZero N a = Multiplicative.ofAdd (Fin.snoc a.toAdd 0) :=
  (rfl)

private theorem snocZero_one (N : ℕ) : snocZero N 1 = 1 := by
  apply Multiplicative.toAdd.injective
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp [snocZero]

private theorem snocZero_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    snocZero N (a * b) = snocZero N a * snocZero N b := by
  apply Multiplicative.toAdd.injective
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp [snocZero]

private theorem snocZero_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    snocZero N a⁻¹ = (snocZero N a)⁻¹ := by
  apply Multiplicative.toAdd.injective
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp [snocZero]

private theorem snocZero_eq_one_iff (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    snocZero N a = 1 ↔ a = 1 := by
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    ext i
    have hi := congrFun (congrArg Multiplicative.toAdd h) i.castSucc
    simpa [snocZero] using hi
  · rintro rfl
    exact snocZero_one N

private theorem chainForm_snoc_zero (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm N a b := by
  let a' : Fin (N + 1) → ZMod 3 := Fin.snoc a 0
  let b' : Fin (N + 1) → ZMod 3 := Fin.snoc b 0
  change chainForm (N + 1) a' b' = chainForm N a b
  rw [chainForm_def, chainForm_def, Fin.sum_univ_castSucc]
  have hlast :
      (∑ j : Fin (N + 1),
          if (Fin.last N : ℕ) + 1 = j then a' (Fin.last N) * b' j - b' (Fin.last N) * a' j
          else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [a', b']
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fin.sum_univ_castSucc]
  simp only [a', b', Fin.snoc_last, mul_zero, sub_self, ite_self, add_zero]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [Fin.snoc_castSucc]

private theorem cubicFactor_snocZero (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor (N + 1) (snocZero N a) (snocZero N b) = cubicFactor N a b := by
  simp [cubicFactor_def, snocZero, chainForm_snoc_zero]

private noncomputable def cubicTorusInclAlgHom (N : ℕ) :
    CubicTorus N →ₐ[ℂ] CubicTorus (N + 1) :=
  cubicTorusLift (fun a ↦ weyl (N + 1) (snocZero N a)) (by rw [snocZero_one, weyl_one])
    fun a b ↦ by rw [weyl_mul, cubicFactor_snocZero, ← snocZero_mul]

/-- The coordinate star-algebra inclusion `I_N : CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1)` extending
Weyl indices by `0` in the last coordinate. -/
noncomputable def cubicTorusIncl (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1) :=
  { cubicTorusInclAlgHom N with
    map_star' := fun x ↦ by
      change cubicTorusInclAlgHom N (star x) = star (cubicTorusInclAlgHom N x)
      rw [← (cubicBasis N).sum_repr x]
      simp only [star_sum, map_sum, star_smul, map_smul, cubicBasis_apply, star_weyl,
        cubicTorusInclAlgHom, cubicTorusLift_weyl, snocZero_inv] }

/-- `cubicTorusIncl N` acts on Weyl basis elements by extending the index by `0` at `Fin.last N`.
-/
@[simp]
theorem cubicTorusIncl_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicTorusIncl N (weyl N a) = weyl (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)) := by
  simp [cubicTorusIncl, cubicTorusInclAlgHom, snocZero]

/-- `cubicTorusIncl N` maps the `j`-th site unitary to `cubicSite (N + 1) j.castSucc`. -/
@[simp]
theorem cubicTorusIncl_cubicSite (N : ℕ) (j : Fin N) :
    cubicTorusIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  have hsnoc :
      Fin.snoc (Pi.single j (1 : ZMod 3)) 0 = (Pi.single j.castSucc 1 : Fin (N + 1) → ZMod 3) := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply]
  simp [cubicSite_def, hsnoc]

/-- `cubicTorusIncl N` maps the `j`-th Temperley–Lieb projection to
`cubicProjection (N + 1) j.castSucc`. -/
@[simp]
theorem cubicTorusIncl_cubicProjection (N : ℕ) (j : Fin N) :
    cubicTorusIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  simp [cubicProjection_def]

/-- `cubicTorusIncl N` intertwines the inversion involutions `θ_N` and `θ_{N + 1}`. -/
@[simp]
theorem cubicTorusIncl_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicTorusIncl N (cubicInversion N x) = cubicInversion (N + 1) (cubicTorusIncl N x) := by
  have hhom :
      (cubicTorusIncl N).toAlgHom.comp (cubicInversion N).toAlgHom =
        (cubicInversion (N + 1)).toAlgHom.comp (cubicTorusIncl N).toAlgHom :=
    cubicTorus_algHom_ext fun a ↦ by
      simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom, cubicInversion_weyl,
        cubicTorusIncl_weyl]
      rw [← snocZero_def, ← snocZero_def, snocZero_inv]
  exact AlgHom.congr_fun hhom x

/-- `cubicTorusIncl N` preserves the scalar trace `cubicScalarCoefficient`. -/
@[simp]
theorem cubicScalarCoefficient_cubicTorusIncl (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient (N + 1) (cubicTorusIncl N x) = cubicScalarCoefficient N x := by
  have hlin :
      (cubicScalarCoefficient (N + 1)).comp (cubicTorusIncl N).toAlgHom.toLinearMap =
        cubicScalarCoefficient N :=
    (cubicBasis N).ext fun a ↦ by
      simp [← snocZero_def, snocZero_eq_one_iff]
  exact LinearMap.congr_fun hlin x

/-- The coordinate inclusion `cubicTorusIncl N` is injective. -/
theorem cubicTorusIncl_injective (N : ℕ) : Function.Injective (cubicTorusIncl N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply (cubicScalarCoefficient_star_mul_self_eq_zero_iff N).mp
  rw [← cubicScalarCoefficient_cubicTorusIncl N, map_mul, map_star, hx, mul_zero, map_zero]

/-- `cubicTorusIncl N x` lies in `cubicFixed (N + 1)` if and only if `x` lies in `cubicFixed N`.
-/
theorem cubicTorusIncl_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicTorusIncl N x ∈ cubicFixed (N + 1) ↔ x ∈ cubicFixed N := by
  rw [mem_cubicFixed, mem_cubicFixed, ← cubicTorusIncl_cubicInversion]
  exact (cubicTorusIncl_injective N).eq_iff

/-- The coordinate star-algebra inclusion `cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1) where
  toFun x := ⟨cubicTorusIncl N x, (cubicTorusIncl_mem_cubicFixed_iff N).mpr x.2⟩
  map_one' := Subtype.ext (map_one (cubicTorusIncl N))
  map_mul' x y := Subtype.ext (map_mul (cubicTorusIncl N) (x : CubicTorus N) (y : CubicTorus N))
  map_zero' := Subtype.ext (map_zero (cubicTorusIncl N))
  map_add' x y := Subtype.ext (map_add (cubicTorusIncl N) (x : CubicTorus N) (y : CubicTorus N))
  commutes' z := Subtype.ext ((cubicTorusIncl N).commutes z)
  map_star' x := Subtype.ext (map_star (cubicTorusIncl N) (x : CubicTorus N))

/-- Coercing `cubicFixedIncl N x` to `CubicTorus (N + 1)` recovers `cubicTorusIncl N x`. -/
@[simp]
theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicTorusIncl N x :=
  (rfl)

/-- The fixed-subalgebra inclusion `cubicFixedIncl N` is injective. -/
theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) := by
  intro x y hxy
  exact Subtype.ext (cubicTorusIncl_injective N (congrArg Subtype.val hxy))

/-- `cubicFixedHom` intertwines Temperley–Lieb `strandIncl` with `cubicFixedIncl`. -/
theorem cubicFixedHom_strandIncl (n : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    cubicFixedHom (n + 2) (strandIncl x) =
      cubicFixedIncl n (cubicFixedHom (n + 1) x) := by
  have hhom :
      (cubicFixedHom (n + 2)).toAlgHom.comp strandIncl =
        (cubicFixedIncl n).toAlgHom.comp (cubicFixedHom (n + 1)).toAlgHom := by
    apply TemperleyLieb.hom_ext
    intro i
    apply Subtype.ext
    simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom, strandIncl_e, coe_cubicFixedIncl]
    rw [coe_cubicFixedHom_e (n + 2) i.castSucc, coe_cubicFixedHom_e (n + 1) i, map_smul]
    change (Real.sqrt 3 : ℂ) • cubicProjection (n + 1) i.castSucc =
      (Real.sqrt 3 : ℂ) • cubicTorusIncl n (cubicProjection n i)
    rw [cubicTorusIncl_cubicProjection]
  exact AlgHom.congr_fun hhom x

/-- The conditional expectation `E_N : CubicTorus (N + 1) →ₗ[ℂ] CubicTorus N` sending `W(a)` to
`W(Fin.init a)` when `a (Fin.last N) = 0` and to `0` otherwise. -/
noncomputable def cubicExpectation (N : ℕ) : CubicTorus (N + 1) →ₗ[ℂ] CubicTorus N :=
  (cubicBasis (N + 1)).constr ℂ fun a ↦
    if a.toAdd (Fin.last N) = 0 then weyl N (Multiplicative.ofAdd (Fin.init a.toAdd)) else 0

/-- Evaluation of `cubicExpectation N` on a Weyl basis element `W(a)`. -/
@[simp]
theorem cubicExpectation_weyl (N : ℕ) (a : Multiplicative (Fin (N + 1) → ZMod 3)) :
    cubicExpectation N (weyl (N + 1) a) =
      if a.toAdd (Fin.last N) = 0 then weyl N (Multiplicative.ofAdd (Fin.init a.toAdd)) else 0 := by
  rw [← cubicBasis_apply, cubicExpectation, Module.Basis.constr_basis]

private theorem snoc_init_of_last_eq_zero {N : ℕ} {v : Fin (N + 1) → ZMod 3}
    (hv : v (Fin.last N) = 0) : Fin.snoc (Fin.init v) 0 = v := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp [hv]
  · simp [Fin.init]

/-- `cubicExpectation N` is a left inverse to `cubicTorusIncl N`: `E_N (I_N x) = x`. -/
@[simp]
theorem cubicExpectation_cubicTorusIncl (N : ℕ) (x : CubicTorus N) :
    cubicExpectation N (cubicTorusIncl N x) = x := by
  have hlin :
      (cubicExpectation N).comp (cubicTorusIncl N).toAlgHom.toLinearMap = LinearMap.id :=
    (cubicBasis N).ext fun a ↦ by
      simp [Fin.init_snoc]
  exact LinearMap.congr_fun hlin x

/-- Left `CubicTorus N`-bimodule property of `cubicExpectation N`:
`E_N (I_N x * y) = x * E_N y`. -/
theorem cubicExpectation_cubicTorusIncl_mul (N : ℕ) (x : CubicTorus N) (y : CubicTorus (N + 1)) :
    cubicExpectation N (cubicTorusIncl N x * y) = x * cubicExpectation N y := by
  have hbilin :
      (((LinearMap.mul ℂ (CubicTorus (N + 1))).comp (cubicTorusIncl N).toAlgHom.toLinearMap).compr₂
          (cubicExpectation N)) =
        (LinearMap.mul ℂ (CubicTorus N)).compl₂ (cubicExpectation N) := by
    refine (cubicBasis N).ext fun a ↦ (cubicBasis (N + 1)).ext fun b ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearMap.mul_apply', AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, cubicBasis_apply,
      cubicTorusIncl_weyl, weyl_mul, map_smul, cubicExpectation_weyl, toAdd_mul, toAdd_ofAdd,
      Pi.add_apply, Fin.snoc_last, zero_add]
    split_ifs with hb
    · have hb_snoc : b = snocZero N (Multiplicative.ofAdd (Fin.init b.toAdd)) := by
        apply Multiplicative.toAdd.injective
        simpa [snocZero] using (snoc_init_of_last_eq_zero hb).symm
      have hfac :
          cubicFactor (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)) b =
            cubicFactor N a (Multiplicative.ofAdd (Fin.init b.toAdd)) := by
        conv_lhs => rw [hb_snoc]
        exact cubicFactor_snocZero N a (Multiplicative.ofAdd (Fin.init b.toAdd))
      have hinit :
          Fin.init (Fin.snoc a.toAdd 0 + b.toAdd) = a.toAdd + Fin.init b.toAdd := by
        ext i
        simp [Fin.init]
      rw [hfac, hinit, ofAdd_add, ofAdd_toAdd, ← weyl_mul]
    · rw [smul_zero, mul_zero]
  exact LinearMap.congr_fun₂ hbilin x y

/-- Right `CubicTorus N`-bimodule property of `cubicExpectation N`:
`E_N (y * I_N x) = E_N y * x`. -/
theorem cubicExpectation_mul_cubicTorusIncl (N : ℕ) (y : CubicTorus (N + 1)) (x : CubicTorus N) :
    cubicExpectation N (y * cubicTorusIncl N x) = cubicExpectation N y * x := by
  have hbilin :
      (((LinearMap.mul ℂ (CubicTorus (N + 1))).compl₂
          (cubicTorusIncl N).toAlgHom.toLinearMap).compr₂ (cubicExpectation N)) =
        (LinearMap.mul ℂ (CubicTorus N)).comp (cubicExpectation N) := by
    refine (cubicBasis (N + 1)).ext fun b ↦ (cubicBasis N).ext fun a ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearMap.mul_apply', AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, cubicBasis_apply,
      cubicTorusIncl_weyl, weyl_mul, map_smul, cubicExpectation_weyl, toAdd_mul, toAdd_ofAdd,
      Pi.add_apply, Fin.snoc_last, add_zero]
    split_ifs with hb
    · have hb_snoc : b = snocZero N (Multiplicative.ofAdd (Fin.init b.toAdd)) := by
        apply Multiplicative.toAdd.injective
        simpa [snocZero] using (snoc_init_of_last_eq_zero hb).symm
      have hfac :
          cubicFactor (N + 1) b (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)) =
            cubicFactor N (Multiplicative.ofAdd (Fin.init b.toAdd)) a := by
        conv_lhs => rw [hb_snoc]
        exact cubicFactor_snocZero N (Multiplicative.ofAdd (Fin.init b.toAdd)) a
      have hinit :
          Fin.init (b.toAdd + Fin.snoc a.toAdd 0) = Fin.init b.toAdd + a.toAdd := by
        ext i
        simp [Fin.init]
      rw [hfac, hinit, ofAdd_add, ofAdd_toAdd, ← weyl_mul]
    · rw [smul_zero, zero_mul]
  exact LinearMap.congr_fun₂ hbilin y x

/-- `cubicExpectation N` commutes with `star`. -/
@[simp]
theorem cubicExpectation_star (N : ℕ) (y : CubicTorus (N + 1)) :
    cubicExpectation N (star y) = star (cubicExpectation N y) := by
  rw [← (cubicBasis (N + 1)).sum_repr y]
  simp only [star_sum, map_sum, star_smul, map_smul, cubicBasis_apply, star_weyl,
    cubicExpectation_weyl, toAdd_inv, Pi.neg_apply, neg_eq_zero]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  split_ifs with ha
  · have hinit : Fin.init (-a.toAdd) = -Fin.init a.toAdd := by
      ext i
      simp [Fin.init]
    rw [hinit, ofAdd_neg, star_weyl]
  · simp

/-- `cubicExpectation N` commutes with `cubicInversion`. -/
@[simp]
theorem cubicExpectation_cubicInversion (N : ℕ) (y : CubicTorus (N + 1)) :
    cubicExpectation N (cubicInversion (N + 1) y) = cubicInversion N (cubicExpectation N y) := by
  have hlin :
      (cubicExpectation N).comp (cubicInversion (N + 1)).toAlgHom.toLinearMap =
        (cubicInversion N).toAlgHom.toLinearMap.comp (cubicExpectation N) := by
    refine (cubicBasis (N + 1)).ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
      cubicBasis_apply, cubicInversion_weyl, cubicExpectation_weyl, toAdd_inv, Pi.neg_apply,
      neg_eq_zero]
    split_ifs with ha
    · have hinit : Fin.init (-a.toAdd) = -Fin.init a.toAdd := by
        ext i
        simp [Fin.init]
      rw [hinit, ofAdd_neg, cubicInversion_weyl]
    · simp
  exact LinearMap.congr_fun hlin y

/-- `cubicExpectation N` maps `cubicFixed (N + 1)` into `cubicFixed N`. -/
theorem cubicExpectation_mem_cubicFixed (N : ℕ) {y : CubicTorus (N + 1)}
    (hy : y ∈ cubicFixed (N + 1)) :
    cubicExpectation N y ∈ cubicFixed N := by
  rw [mem_cubicFixed, ← cubicExpectation_cubicInversion, (mem_cubicFixed (N + 1)).mp hy]

/-- `cubicExpectation N` preserves the scalar trace: `s_N (E_N y) = s_{N + 1} y`. -/
@[simp]
theorem cubicScalarCoefficient_cubicExpectation (N : ℕ) (y : CubicTorus (N + 1)) :
    cubicScalarCoefficient N (cubicExpectation N y) = cubicScalarCoefficient (N + 1) y := by
  have hlin :
      (cubicScalarCoefficient N).comp (cubicExpectation N) = cubicScalarCoefficient (N + 1) := by
    refine (cubicBasis (N + 1)).ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, cubicBasis_apply, cubicExpectation_weyl]
    by_cases ha : a.toAdd (Fin.last N) = 0
    · simp only [ha, ↓reduceIte, cubicScalarCoefficient_weyl]
      have hiff : Multiplicative.ofAdd (Fin.init a.toAdd) = 1 ↔ a = 1 := by
        constructor
        · intro h1
          apply Multiplicative.toAdd.injective
          have hinit : Fin.init a.toAdd = 0 := by simpa using congrArg Multiplicative.toAdd h1
          rw [← snoc_init_of_last_eq_zero ha, hinit]
          ext i
          refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
        · rintro rfl
          apply Multiplicative.toAdd.injective
          ext _
          simp [Fin.init]
      simp [hiff]
    · have ha1 : a ≠ 1 := fun h ↦ ha (by simp [h])
      simp [ha, ha1]
  exact LinearMap.congr_fun hlin y

/-- The conditional expectation of the last Temperley–Lieb projection `p_{last}` is `3⁻¹ • 1`. -/
@[simp]
theorem cubicExpectation_cubicProjection_last (N : ℕ) :
    cubicExpectation N (cubicProjection (N + 1) (Fin.last N)) = (3 : ℂ)⁻¹ • 1 := by
  have h1 : (Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3) (Fin.last N) ≠ 0 := by
    simp
  have h2 : (-(Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3)) (Fin.last N) ≠ 0 := by
    simp
  rw [cubicProjection_def, cubicSite_def, weyl_sq, ← ofAdd_neg, ← weyl_one]
  simp only [map_smul, map_add, cubicExpectation_weyl, toAdd_one, toAdd_ofAdd, Pi.zero_apply,
    ↓reduceIte, h1, h2, add_zero]
  have hinit0 : Fin.init (0 : Fin (N + 1) → ZMod 3) = 0 := by
    ext _
    simp [Fin.init]
  rw [hinit0, ofAdd_zero, weyl_one]

/-- Multiplying an included torus element on the right by the last projection scales its scalar
trace by `3⁻¹`. -/
theorem cubicScalarCoefficient_cubicTorusIncl_mul_cubicProjection_last (N : ℕ)
    (x : CubicTorus N) :
    cubicScalarCoefficient (N + 1)
        (cubicTorusIncl N x * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * cubicScalarCoefficient N x := by
  rw [← cubicScalarCoefficient_cubicExpectation, cubicExpectation_cubicTorusIncl_mul,
    cubicExpectation_cubicProjection_last, mul_smul_comm, mul_one, map_smul, smul_eq_mul]

/-! ### The Markov trace at `δ = √3`, positivity, and the trace radical -/

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ) m` obtained by pulling back
`(√3 : ℂ) ^ m` times `cubicScalarCoefficient (m - 1)` along `cubicFixedHom m`. -/
noncomputable def cubicFixedTrace (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) •
    (cubicScalarCoefficient (m - 1) ∘ₗ
      (cubicFixed (m - 1)).toSubalgebra.val.toLinearMap ∘ₗ (cubicFixedHom m).toAlgHom.toLinearMap)

/-- Evaluation formula for `cubicFixedTrace`. -/
theorem cubicFixedTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedTrace m x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) :=
  (rfl)

/-- **The cubic torus scalar trace defines a Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicFixedTrace :
    IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicFixedTrace where
  map_one m := by simp [cubicFixedTrace_apply]
  map_mul_comm m x y := by
    simp only [cubicFixedTrace_apply, map_mul, MulMemClass.coe_mul,
      cubicScalarCoefficient_mul_comm]
  map_strandIncl n x := by
    rw [cubicFixedTrace_apply, cubicFixedTrace_apply, cubicFixedHom_strandIncl, coe_cubicFixedIncl]
    change (Real.sqrt 3 : ℂ) ^ (n + 2) *
        cubicScalarCoefficient (n + 1) (cubicTorusIncl n (cubicFixedHom (n + 1) x).val) =
      (Real.sqrt 3 : ℂ) *
        ((Real.sqrt 3 : ℂ) ^ (n + 1) * cubicScalarCoefficient n (cubicFixedHom (n + 1) x).val)
    rw [cubicScalarCoefficient_cubicTorusIncl, pow_succ']
    ring
  map_strandIncl_mul_e_last n x := by
    have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rw [cubicFixedTrace_apply, cubicFixedTrace_apply, map_mul, MulMemClass.coe_mul,
      cubicFixedHom_strandIncl, coe_cubicFixedIncl, coe_cubicFixedHom_e (n + 2) (Fin.last n),
      mul_smul_comm, map_smul]
    change (Real.sqrt 3 : ℂ) ^ (n + 2) *
        ((Real.sqrt 3 : ℂ) •
          cubicScalarCoefficient (n + 1)
            (cubicTorusIncl n (cubicFixedHom (n + 1) x).val *
              cubicProjection (n + 1) (Fin.last n))) =
      (Real.sqrt 3 : ℂ) ^ (n + 1) * cubicScalarCoefficient n (cubicFixedHom (n + 1) x).val
    rw [cubicScalarCoefficient_cubicTorusIncl_mul_cubicProjection_last, smul_eq_mul, pow_succ]
    set s : ℂ := cubicScalarCoefficient n (cubicFixedHom (n + 1) x).val
    calc
      (Real.sqrt 3 : ℂ) ^ (n + 1) * (Real.sqrt 3 : ℂ) * ((Real.sqrt 3 : ℂ) * ((3 : ℂ)⁻¹ * s)) =
          (Real.sqrt 3 : ℂ) ^ (n + 1) * (((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹) *
            s := by
            ring
      _ = (Real.sqrt 3 : ℂ) ^ (n + 1) * s := by
          rw [hsqrt]
          norm_num

/-- Positive functional on `cubicFixed (m - 1)` given by `(√3 : ℂ) ^ m * s_{m - 1}`, used to
identify the trace radical with `RingHom.ker (cubicFixedHom m)`. -/
private noncomputable def scaledCubicFixedFunctional (m : ℕ) :
    StarPositiveFunctional (cubicFixed (m - 1)) where
  toLinearMap :=
    ((Real.sqrt 3 : ℂ) ^ m) •
      (cubicScalarCoefficient (m - 1) ∘ₗ (cubicFixed (m - 1)).toSubalgebra.val.toLinearMap)
  square_nonneg x := by
    have hx := cubicScalarCoefficient_star_mul_self_nonneg (m - 1) (x : CubicTorus (m - 1))
    have hx0 : ((0 : ℝ) : ℂ) ≤
        cubicScalarCoefficient (m - 1) (star (x : CubicTorus (m - 1)) * x) := by
      simpa using hx
    change 0 ≤ (Real.sqrt 3 : ℂ) ^ m *
      cubicScalarCoefficient (m - 1) (star (x : CubicTorus (m - 1)) * x)
    rw [Complex.eq_re_of_ofReal_le hx0, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.zero_le_real]
    exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hx).1

private theorem nullSubmodule_scaledCubicFixedFunctional (m : ℕ) :
    (scaledCubicFixedFunctional m).nullSubmodule = ⊥ := by
  have hsqrt_ne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  ext x
  simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    scaledCubicFixedFunctional, pow_ne_zero m hsqrt_ne]

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` coincides with `cubicFixedTrace`. -/
theorem eq_cubicFixedTrace (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) :
    tr = cubicFixedTrace :=
  htr.unique isMarkovTrace_cubicFixedTrace

/-- **The Markov trace at `δ = √3` as the cubic torus scalar trace**: for every Markov trace `tr`,
`tr m x = (√3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x)`. -/
theorem apply_eq_mul_cubicScalarCoefficient_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) := by
  rw [htr.eq_cubicFixedTrace, cubicFixedTrace_apply]

/-- **Positivity of the Markov trace at `δ = √3`** (the `ℓ = 6` discrete-series point
`2 cos (π / 6)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have h := (scaledCubicFixedFunctional m).square_nonneg (cubicFixedHom m x)
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul, map_star]
  exact h

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicFixedHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicFixedHom m x = 0 := by
  have hsqrt_ne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul, map_star,
    MulMemClass.coe_mul, StarMemClass.coe_star, mul_eq_zero,
    or_iff_right (pow_ne_zero m hsqrt_ne),
    cubicScalarCoefficient_star_mul_self_eq_zero_iff, Subtype.ext_iff, ZeroMemClass.coe_zero]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √3` is the kernel of `cubicFixedHom`.** -/
theorem traceRadical_eq_ker_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m) :=
  LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot (tr m) (htr.map_mul_comm m)
    (scaledCubicFixedFunctional m) (nullSubmodule_scaledCubicFixedFunctional m)
    (cubicFixedHom m) fun a ↦ by
      rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom]
      rfl

/-- At `δ = √3`, the null vectors of `x ↦ tr m (star x * x)` are precisely the trace radical. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ x ∈ (tr m).traceRadical (htr.map_mul_comm m) := by
  rw [htr.map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero,
    htr.traceRadical_eq_ker_cubicFixedHom, RingHom.mem_ker]

/-- The trace radical at `δ = √3` is star-stable. -/
theorem isStar_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ((tr m).traceRadical (htr.map_mul_comm m)).IsStar where
  star_mem {a} ha := by
    rw [htr.traceRadical_eq_ker_cubicFixedHom, RingHom.mem_ker] at ha ⊢
    rw [map_star, ha, star_zero]

/-- **The Jones quotient at `δ = √3` is isomorphic to the inversion-fixed cubic torus**
`cubicFixed (m - 1)`. -/
noncomputable def quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      cubicFixed (m - 1) :=
  (Ideal.quotientEquivAlgOfEq ℂ
    (show (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m).toAlgHom from
      htr.traceRadical_eq_ker_cubicFixedHom m)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := (cubicFixedHom m).toAlgHom)
      (cubicFixedHom_surjective m))

/-- `quotientCubicFixedEquiv` evaluates on a quotient representative via `cubicFixedHom`. -/
@[simp]
theorem quotientCubicFixedEquiv_mk
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    htr.quotientCubicFixedEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      cubicFixedHom m x := by
  simp only [quotientCubicFixedEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- `quotientCubicFixedEquiv` preserves `star` when the trace-radical quotient carries its
quotient star structure. -/
@[simp]
theorem quotientCubicFixedEquiv_star
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [((tr m).traceRadical (htr.map_mul_comm m)).IsStar]
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    htr.quotientCubicFixedEquiv m (star q) = star (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [Ideal.Quotient.star_mk, quotientCubicFixedEquiv_mk, map_star]

/-- `quotientCubicFixedEquiv` upgraded to a `ℂ`-star-algebra equivalence when the trace radical
carries `Ideal.IsStar`. -/
noncomputable def quotientCubicFixedStarEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [((tr m).traceRadical (htr.map_mul_comm m)).IsStar] :
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃⋆ₐ[ℂ]
      cubicFixed (m - 1) :=
  { htr.quotientCubicFixedEquiv m with
    map_smul' := fun r x ↦ map_smul (htr.quotientCubicFixedEquiv m) r x
    map_star' := htr.quotientCubicFixedEquiv_star m }

/-- `quotientCubicFixedEquiv` intertwines `quotientStrandIncl` with `cubicFixedIncl`. -/
theorem quotientCubicFixedEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk, htr.quotientCubicFixedEquiv_mk,
    cubicFixedHom_strandIncl]

/-- `(quotientCubicFixedEquiv m).symm` maps `cubicFixedHom m x` back to the quotient class of `x`.
-/
@[simp]
theorem quotientCubicFixedEquiv_symm_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (htr.quotientCubicFixedEquiv m).symm (cubicFixedHom m x) =
      Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x :=
  (htr.quotientCubicFixedEquiv m).injective (by simp)

/-- `(quotientCubicFixedEquiv _).symm` intertwines `cubicFixedIncl` with `quotientStrandIncl`. -/
theorem quotientCubicFixedEquiv_symm_cubicFixedIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (y : cubicFixed n) :
    (htr.quotientCubicFixedEquiv (n + 2)).symm (cubicFixedIncl n y) =
      htr.quotientStrandIncl n ((htr.quotientCubicFixedEquiv (n + 1)).symm y) :=
  (htr.quotientCubicFixedEquiv (n + 2)).injective <| by
    rw [AlgEquiv.apply_symm_apply, htr.quotientCubicFixedEquiv_quotientStrandIncl,
      AlgEquiv.apply_symm_apply]

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √3` is `(√3 : ℂ) ^ m` times
`cubicScalarCoefficient (m - 1)` under `quotientCubicFixedEquiv`. -/
theorem quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 3 : ℂ) ^ m *
        cubicScalarCoefficient (m - 1) (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom]

/-- Transporting `quotientTrace` across `(quotientCubicFixedEquiv m).symm` gives `(√3 : ℂ) ^ m`
times `cubicScalarCoefficient (m - 1)`. -/
@[simp]
theorem quotientTrace_quotientCubicFixedEquiv_symm
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) (y : cubicFixed (m - 1)) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientCubicFixedEquiv m).symm y) =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) y := by
  simp [htr.quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv]

/-- The `m`-strand Temperley–Lieb trace quotient at `δ = √3` has complex dimension
`(3 ^ (m - 1) + 1) / 2`. -/
@[simp]
theorem finrank_quotient_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    Module.finrank ℂ
        (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) =
      (3 ^ (m - 1) + 1) / 2 := by
  rw [(htr.quotientCubicFixedEquiv m).toLinearEquiv.finrank_eq, finrank_cubicFixed]

end IsMarkovTrace

/-- Specialization of `IsMarkovTrace.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom` to the
spin-model `markovTrace` at any unit `q : ℂˣ` satisfying `(√3 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_cubicScalarCoefficient_cubicFixedHom (q : ℂˣ)
    (hq : (Real.sqrt 3 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_cubicScalarCoefficient_cubicFixedHom m x

/-! ### Packaged cubic-torus model and vanishing of the five-strand Jones–Wenzl projection -/

/-- **The inversion-fixed cubic torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every Markov
trace `tr` at loop value `√3` and every `m : ℕ`, there is a surjective `ℂ`-star-algebra
homomorphism `F : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` sending each generator
`e j` to `(√3 : ℂ) • cubicProjection (m - 1) j`, expressing `tr m` as `(√3 : ℂ) ^ m` times
`cubicScalarCoefficient (m - 1)`, and having kernel equal to the trace radical
`(tr m).traceRadical`. -/
theorem exists_cubicFixedModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1),
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
          (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        tr m x = (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicFixedHom m,
    cubicFixedHom_surjective m,
    coe_cubicFixedHom_e m,
    htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom m,
    (htr.traceRadical_eq_ker_cubicFixedHom m).symm⟩

/-- At `δ = √3`, `cubicFixedHom 5` maps the five-strand Jones–Wenzl projection
`jonesWenzl (√3 : ℂ) 5` to `0`. -/
@[simp]
theorem cubicFixedHom_jonesWenzl_five :
    cubicFixedHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt_ne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hq3 : qInt ℂ (Real.sqrt 3 : ℂ) 3 = 2 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 1, qInt_two, qInt_one, hsqrt]
    norm_num
  have hq4 : qInt ℂ (Real.sqrt 3 : ℂ) 4 = (Real.sqrt 3 : ℂ) := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 2, hq3, qInt_two]
    ring
  have hq5 : qInt ℂ (Real.sqrt 3 : ℂ) 5 = 1 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 3, hq4, hq3, hsqrt]
    norm_num
  have hq6 : qInt ℂ (Real.sqrt 3 : ℂ) 6 = 0 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 4, hq5, hq4]
    ring
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp
    · simp [qInt_two, hsqrt_ne]
    · simp [hq3]
    · simp [hq4, hsqrt_ne]
    · simp [hq5]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicFixedTrace.traceRadical_eq_ker_cubicFixedHom 5,
    isMarkovTrace_cubicFixedTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq6

end TauCeti.TemperleyLieb
