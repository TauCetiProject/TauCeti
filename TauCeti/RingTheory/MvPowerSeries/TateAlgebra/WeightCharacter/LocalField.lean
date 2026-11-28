/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.Analysis.Normed.Ring.Ultra
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeightCharacter.Basic

import Mathlib.Algebra.Order.Field.Pi
import TauCeti.Analysis.Normed.Ring.UnitBall
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.EmbeddingEval
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius.Eval

/-!
# Uniqueness of local analytic weights

Over a finite extension of `ℚ_p`, the character on the units determines its restricted
expansion near `1` in the coordinates of the full family of embeddings when bounded
`ℚ_p`-linear maps into normed fields jointly separate the points of the coefficient
algebra. At fixed polyradii this also determines the associated automorphy factor and
slash action.
-/

public section

namespace TauCeti.MvPowerSeries.AnalyticWeight

open _root_.MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {F K R : Type*}
  [NormedField F] [NormedAlgebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [NormedField K] [NormedAlgebra ℚ_[p] K]
  [NormedCommRing R] [NormedAlgebra K R] [IsUltrametricDist R] [CompleteSpace R]
  [NormedSpace ℚ_[p] R] [IsScalarTower ℚ_[p] K R]
  {k : ℕ} {r s : Fin k → ℝ}

private theorem exists_common_radius [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)] :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (∀ i, ε ≤ r i) ∧ (∀ i, ε ≤ s i) := by
  obtain ⟨δ, hδ, hδrs⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ ↦ (0 : ℝ)) (y := fun i ↦ min (r i) (s i))
    (fun i ↦ lt_min (Fact.out : 0 < r i) (Fact.out : 0 < s i))
  simp only [zero_add, lt_min_iff] at hδrs
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_, ?_⟩
  · exact fun i ↦ (min_le_left _ _).trans (hδrs i).1.le
  · exact fun i ↦ (min_le_left _ _).trans (hδrs i).2.le

/-- Expansions of the same local unit character have the same formal coefficients, even when
the polyradii at which the two series are restricted differ. The coordinates come from the full
family of embeddings. The bounded `ℚ_p`-linear maps `φ j : R → L j` must jointly separate the
points of `R`. -/
theorem coe_expansion_eq_of_char_eq [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]
    (σ : Fin k → F →ₐ[ℚ_[p]] K) (hσ : Function.Injective σ) (hk : Module.finrank ℚ_[p] F = k)
    {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)] [∀ j, NormedAlgebra ℚ_[p] (L j)]
    (φ : ∀ j, R →L[ℚ_[p]] L j) (hφ : ∀ a, (∀ j, φ j a = 0) → a = 0) :
    letI : IsUltrametricDist F := .of_normedAlgebra ℚ_[p]
    ∀ {κ : AnalyticWeight R (fun i ↦
        (algebraMap K R).comp ((σ i).toRingHom.comp (Subring.unitClosedBall F).subtype)) r}
      {κ' : AnalyticWeight R (fun i ↦
        (algebraMap K R).comp ((σ i).toRingHom.comp (Subring.unitClosedBall F).subtype)) s},
      κ.char = κ'.char → (κ.expansion : MvPowerSeries (Fin k) R) = κ'.expansion := by
  intro κ κ' hchar
  obtain ⟨ε, hε, hε1, hεr, hεs⟩ := exists_common_radius (r := r) (s := s)
  let C : ℝ := max 1 ‖(1 : R)‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ : ℝ := ε / C
  have hδ : 0 < δ := div_pos hε hC
  have hδε : δ ≤ ε := div_le_self hε.le (le_max_left _ _)
  let c : Fin k → ℝ := fun _ ↦ ε
  have hcr : c ≤ r := hεr
  have hcs : c ≤ s := hεs
  let f := restrictedRadiusHom (fun _ ↦ hε.le) hcr κ.expansion
  let g := restrictedRadiusHom (fun _ ↦ hε.le) hcs κ'.expansion
  have hbound (y : F) (hy : ‖y‖ ≤ δ) (i : Fin k) : ‖algebraMap K R (σ i y)‖ ≤ c i := by
    rw [norm_algebraMap, (σ i).isometry.norm_map_of_map_zero (map_zero (σ i))]
    exact (mul_le_mul hy (le_max_right _ _) (norm_nonneg _) hδ.le).trans_eq
      (div_mul_cancel₀ ε hC.ne')
  suffices hfg : f = g by
    simpa [f, g] using congrArg (fun w : IsRestricted.subring (R := R) c ↦ w.val) hfg
  apply sub_eq_zero.mp
  refine eq_zero_of_restrictedEval₂_algHom_arg_eq_zero
    σ hσ hk hδ φ hφ (f - g) hbound ?_
  intro y hy
  have : IsUltrametricDist F := .of_normedAlgebra ℚ_[p]
  let : CompleteSpace F := FiniteDimensional.completeSpace ℚ_[p] F
  let z : Subring.unitClosedBall F :=
    ⟨y, Subring.mem_unitClosedBall.mpr (hy.trans (hδε.trans hε1.le))⟩
  have hu : IsUnit (1 + z) := by
    apply isUnit_unitClosedBall_of_norm_sub_one_lt
    simpa [z] using hy.trans_lt (hδε.trans_lt hε1)
  obtain ⟨u, hu⟩ := hu
  rw [map_sub, sub_eq_zero]
  calc
    _ = κ.char u :=
      (restrictedEval₂_restrictedRadiusHom _ hcr _ _ _ (hbound y hy) κ.expansion).trans
        (κ.char_eq_restrictedEval₂ u z (fun i ↦ (hbound y hy i).trans (hcr i)) hu).symm
    _ = κ'.char u := DFunLike.congr_fun hchar u
    _ = _ := (κ'.char_eq_restrictedEval₂ u z (fun i ↦ (hbound y hy i).trans (hcs i)) hu).trans
      (restrictedEval₂_restrictedRadiusHom _ hcs _ _ _ (hbound y hy) κ'.expansion).symm

/-- At fixed polyradii the local unit character determines the analytic weight, hence its
automorphy factor and slash action. -/
theorem eq_of_char_eq [∀ i, Fact (0 < r i)] (σ : Fin k → F →ₐ[ℚ_[p]] K)
    (hσ : Function.Injective σ) (hk : Module.finrank ℚ_[p] F = k)
    {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)] [∀ j, NormedAlgebra ℚ_[p] (L j)]
    (φ : ∀ j, R →L[ℚ_[p]] L j) (hφ : ∀ a, (∀ j, φ j a = 0) → a = 0) :
    letI : IsUltrametricDist F := .of_normedAlgebra ℚ_[p]
    ∀ {κ κ' : AnalyticWeight R (fun i ↦
        (algebraMap K R).comp ((σ i).toRingHom.comp (Subring.unitClosedBall F).subtype)) r},
      κ.char = κ'.char → κ = κ' := by
  intro κ κ' hchar
  exact AnalyticWeight.ext hchar (Subtype.ext (coe_expansion_eq_of_char_eq σ hσ hk φ hφ hchar))

end TauCeti.MvPowerSeries.AnalyticWeight
