/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.EmbeddingEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeightCharacter

import TauCeti.Analysis.Normed.Ring.UnitBall
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic

/-!
# Uniqueness of local analytic weights

Over a finite extension of `ℚ_p`, the character on the units determines its restricted
expansion near `1` in the coordinates of the full family of embeddings. Consequently
the automorphy factor and slash action associated to an analytic weight are independent of
the choice of expansion. The coefficients can be separated by bounded linear functionals,
so the uniqueness statement applies to suitable nonreduced Banach algebras as well.
-/

public section

namespace TauCeti.MvPowerSeries.AnalyticWeight

open _root_.MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {F K R : Type*}
  [NormedField F] [IsUltrametricDist F] [NormedAlgebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [NormedField K] [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K]
  [NormedCommRing R] [NormedAlgebra K R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  {k : ℕ} {r s : Fin k → ℝ}

/-- Expansions of the same local unit character have the same formal coefficients, even when
the polyradii at which the two series are restricted differ. The coordinates come from the full
family of embeddings, and bounded linear functionals separate the coefficients over `K`. -/
theorem coe_expansion_eq_of_char_eq [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]
    (σ : Fin k → F →ₐ[ℚ_[p]] K) (hσ : Function.Injective σ) (hk : Module.finrank ℚ_[p] F = k)
    {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)] [∀ j, NormedAlgebra K (L j)]
    (φ : ∀ j, R →L[K] L j) (hφ : ∀ a, (∀ j, φ j a = 0) → a = 0)
    {κ : AnalyticWeight R (fun i ↦
      (algebraMap K R).comp ((σ i).toRingHom.comp (Subring.unitClosedBall F).subtype)) r}
    {κ' : AnalyticWeight R (fun i ↦
      (algebraMap K R).comp ((σ i).toRingHom.comp (Subring.unitClosedBall F).subtype)) s}
    (hchar : κ.char = κ'.char) :
    (κ.expansion : MvPowerSeries (Fin k) R) = κ'.expansion := by
  let t := fun i ↦ min (r i) (s i)
  let radii := insert (1 / 2 : ℝ) (Finset.univ.image t)
  let ε := radii.inf' (Finset.insert_nonempty _ _) id
  have hε : 0 < ε := by
    dsimp only [ε]
    rw [Finset.lt_inf'_iff]
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · norm_num
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
      exact lt_min (Fact.out : 0 < r i) (Fact.out : 0 < s i)
  have hεt i : ε ≤ t i :=
    Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_image_of_mem t (Finset.mem_univ i)))
  have hε1 : ε < 1 :=
    (Finset.inf'_le id (Finset.mem_insert_self _ _)).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  let c : Fin k → ℝ := fun _ ↦ ε
  have hcr : c ≤ r := fun i ↦ (hεt i).trans (min_le_left _ _)
  have hcs : c ≤ s := fun i ↦ (hεt i).trans (min_le_right _ _)
  let f := restrictedRadiusHom (fun _ ↦ hε.le) hcr κ.expansion
  let g := restrictedRadiusHom (fun _ ↦ hε.le) hcs κ'.expansion
  have hbound (y : F) (hy : ‖y‖ ≤ ε) (i : Fin k) : ‖algebraMap K R (σ i y)‖ ≤ c i := by
    rw [norm_algebraMap', (σ i).isometry.norm_map_of_map_zero (map_zero (σ i))]
    exact hy
  suffices hfg : f = g by
    simpa [f, g] using congrArg (fun w : IsRestricted.subring (R := R) c ↦ w.val) hfg
  apply sub_eq_zero.mp
  refine eq_zero_of_restrictedEval₂_padicEmbeddings_eq_zero (r := c) (hr := fun _ ↦ ⟨hε⟩)
    σ hσ hk hε φ hφ (f - g) hbound ?_
  intro y hy
  let : CompleteSpace F := FiniteDimensional.completeSpace ℚ_[p] F
  let z : Subring.unitClosedBall F := ⟨y, Subring.mem_unitClosedBall.mpr (hy.trans hε1.le)⟩
  have hu : IsUnit (1 + z) := by
    apply isUnit_unitClosedBall_of_norm_sub_one_lt
    simpa [z] using hy.trans_lt hε1
  obtain ⟨u, hu⟩ := hu
  rw [map_sub, sub_eq_zero]
  have ev {a : Fin k → ℝ} (hca : c ≤ a) (w : IsRestricted.subring (R := R) a) :
      restrictedEval₂ (RingHom.id R) (fun i ↦ algebraMap K R (σ i y)) (fun _ ↦ le_rfl)
          (hbound y hy) (restrictedRadiusHom (fun _ ↦ hε.le) hca w) =
        restrictedEval₂ (RingHom.id R) (fun i ↦ algebraMap K R (σ i y)) (fun _ ↦ le_rfl)
          (fun i ↦ (hbound y hy i).trans (hca i)) w := by
    rw [restrictedEval₂_apply, restrictedEval₂_apply, coe_restrictedRadiusHom]
  calc
    _ = κ.char u := (ev hcr _).trans
      (κ.char_eq_restrictedEval₂ u z (fun i ↦ (hbound y hy i).trans (hcr i)) hu).symm
    _ = κ'.char u := DFunLike.congr_fun hchar u
    _ = _ := (κ'.char_eq_restrictedEval₂ u z (fun i ↦ (hbound y hy i).trans (hcs i)) hu).trans
      (ev hcs _).symm

/-- At fixed polyradii the local unit character determines the analytic weight, hence its
automorphy factor and slash action. -/
theorem eq_of_char_eq [∀ i, Fact (0 < r i)] (σ : Fin k → F →ₐ[ℚ_[p]] K)
    (hσ : Function.Injective σ) (hk : Module.finrank ℚ_[p] F = k)
    {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)] [∀ j, NormedAlgebra K (L j)]
    (φ : ∀ j, R →L[K] L j) (hφ : ∀ a, (∀ j, φ j a = 0) → a = 0)
    {κ κ' : AnalyticWeight R (fun i ↦
      (algebraMap K R).comp ((σ i).toRingHom.comp (Subring.unitClosedBall F).subtype)) r}
    (hchar : κ.char = κ'.char) : κ = κ' :=
  AnalyticWeight.ext hchar (Subtype.ext (coe_expansion_eq_of_char_eq σ hσ hk φ hφ hchar))

end TauCeti.MvPowerSeries.AnalyticWeight
