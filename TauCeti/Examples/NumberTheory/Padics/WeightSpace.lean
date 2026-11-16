/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.DualNumber
public import TauCeti.NumberTheory.Padics.WeightSpace.Specialization
public import TauCeti.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Polynomial.Monic

/-!
# Examples of `p`-adic weight specialisation

Sanity checks for `TauCeti.WeightSpace` and `ℤ_p[[ℤ_pˣ]]`: non-invertibility of `1 + X` in
polynomials, first-order jets in `MaxDualNumber ℚ_[p]`, intertwining of adic and normed
specialisation at `p`, and dyadic sign separation at `p = 2`.
-/

public section

open Filter Topology TauCeti TauCeti.WeightSpace

namespace TauCeti.Examples

-- `1 + X` has no polynomial inverse over any nontrivial semiring.
example {R : Type*} [Semiring R] [Nontrivial R] :
    ¬∃ P : Polynomial R, (1 + PowerSeries.X : PowerSeries R) * (P : PowerSeries R) = 1 := by
  rintro ⟨P, hP⟩
  have hmul : (Polynomial.X + Polynomial.C (1 : R)) * P = 1 :=
    Polynomial.coe_injective R <| by simpa [add_comm] using hP
  have hcomm : Commute (Polynomial.X + Polynomial.C (1 : R)) P :=
    (Polynomial.commute_X P).add_left (by rw [map_one]; exact Commute.one_left P)
  exact Polynomial.not_isUnit_X_add_C 1 (isUnit_iff_exists.mpr ⟨P, hmul, hcomm.symm.eq.trans hmul⟩)

-- Normed specialisation at `ε ∈ MaxDualNumber ℚ_[p]` (`‖ε‖ = 1`, `ε ^ 2 = 0`) is the 1-jet.
example {p : ℕ} [Fact p.Prime] (φ : PowerSeries ℤ_[p]) :
    let hε : Tendsto ((MaxDualNumber.eps : MaxDualNumber ℚ_[p]) ^ ·) atTop (𝓝 0) :=
      tendsto_atTop_of_eventually_const (i₀ := 2) fun n hn ↦ by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [pow_add, sq, MaxDualNumber.eps_mul_eps, zero_mul]
    (ofCoord (p := p) 1 MaxDualNumber.eps hε).normedSpecialize
        (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      algebraMap ℤ_[p] (MaxDualNumber ℚ_[p]) (φ.coeff 0) +
        φ.coeff 1 • (MaxDualNumber.eps : MaxDualNumber ℚ_[p]) := by
  intro hε
  rw [normedSpecialize_padicUnitsCoordinate_map_singleOneRingHom, padicPowerSeriesEval_apply,
    PowerSeries.evalAt_def, tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, coord_ofCoord, pow_zero, pow_one,
      Algebra.algebraMap_eq_smul_one]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp (Finset.mem_range.not.mp hn))
    rw [coord_ofCoord, pow_add, sq, MaxDualNumber.eps_mul_eps, zero_mul, smul_zero]

-- `algebraMap ℤ_[p] ℚ_[p]` intertwines adic and normed specialisation at `p`.
example {p : ℕ} [Fact p.Prime] (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :
    let hpZ : PowerSeries.HasEval (p : ℤ_[p]) :=
      Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr dvd_rfl
    let hpQ : Tendsto (((p : ℚ_[p]) ^ ·)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    algebraMap ℤ_[p] ℚ_[p] ((ofHasEval (p := p) 1 hpZ).adicSpecialize x) =
      (ofCoord (p := p) 1 (p : ℚ_[p]) hpQ).normedSpecialize x := by
  intro hpZ hpQ
  let φ := (Algebra.ofId ℤ_[p] ℚ_[p]).comp (ofHasEval (p := p) 1 hpZ).adicSpecialize
  have hφ : Continuous φ := (PadicInt.isEmbedding_coe_ringHom.continuous.comp
    (ofHasEval (p := p) 1 hpZ).continuous_adicSpecialize).congr fun z ↦ by
      simp [φ, PadicInt.algebraMap_eq_coe_ringHom]
  have hκ : ofContinuousRingHom φ.toRingHom hφ = ofCoord (p := p) 1 (p : ℚ_[p]) hpQ :=
    ext_finiteChar_coord
      (by ext δ; simp [φ, coe_finiteChar_ofContinuousRingHom_apply, ← finiteChar_apply])
      (by simp [φ])
  exact AlgHom.congr_fun (eq_normedSpecialize_of_continuous hφ _ fun _ ↦ by
    rw [← hκ, coe_ofContinuousRingHom_apply]; rfl) x

-- For `p = 2`, the two dyadic sign weights separate `[ω(-1)]`.
example :
    let g := completedGroupAlgebra.of ℤ_[2] ℤ_[2]ˣ
      (padicUnitsSection 2 (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ))
    (ofHasEval (p := 2) 1 (PowerSeries.HasEval.zero (S := ℤ_[2]))).adicSpecialize g = 1 ∧
      (ofHasEval (p := 2) (padicUnitsSection 2)
        (PowerSeries.HasEval.zero (S := ℤ_[2]))).adicSpecialize g = -1 := by
  intro g
  refine ⟨by rw [adicSpecialize_of, ← finiteChar_apply, finiteChar_ofHasEval]; simp, ?_⟩
  rw [adicSpecialize_of, ← finiteChar_apply, finiteChar_ofHasEval]
  have hsq : (padicUnitsSection 2 (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ) : ℤ_[2]) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow,
      show (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ) ^ 2 = 1 by rw [padicUnitsDepth_two]; decide,
      map_one, Units.val_one]
  exact (sq_eq_one_iff.mp hsq).resolve_left fun h1 ↦
    (padicUnitsSection_injective 2).ne (a₁ := (-1 : (ZMod (2 ^ padicUnitsDepth 2))ˣ)) (a₂ := 1)
      (by rw [padicUnitsDepth_two]; decide) ((Units.ext h1).trans (map_one _).symm)

end TauCeti.Examples
