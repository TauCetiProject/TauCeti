/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
import Mathlib.GroupTheory.Index

/-!
# Elliptic ramification of maps between Fuchsian quotients

For an inclusion `Δ ≤ Γ` of discrete subgroups of `PSL(2, ℝ)`, the ramification exponent at
the orbit of `z` is the relative index of the two point stabilizers. In the elliptic quotient
charts centred at the same `z`, the induced map is a power map with that exponent. The
calculation also applies to free points, where the exponent is one.

The local model is the cyclic disc quotient of Farkas--Kra, *Riemann Surfaces*, Chapter I,
§§4--5. The stabilizer-index interpretation follows the usual orbit-stabilizer principle.
-/

public noncomputable section

open Filter Metric MulAction TauCeti Topology UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- The point stabilizer of a subgroup, regarded as a subgroup of `PSL(2, ℝ)`. -/
private def ambientStabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) : Subgroup PSL(2, ℝ) :=
  (stabilizer Γ z).map Γ.subtype

private theorem ambientStabilizer_mono (h : Δ ≤ Γ) (z : ℍ) :
    ambientStabilizer Δ z ≤ ambientStabilizer Γ z := by
  rintro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨⟨g, h g.property⟩, ?_, rfl⟩
  simpa only [mem_stabilizer_iff, Subgroup.smul_def] using hg

private theorem card_ambientStabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    Nat.card (ambientStabilizer Γ z) = Nat.card (stabilizer Γ z) :=
  Subgroup.card_map_of_injective Γ.subtype_injective

/-- The index of the smaller point stabilizer in the larger one. This is the exponent of the
local power map at the orbit of `z`. -/
def ellipticRamificationIndex (_h : Δ ≤ Γ) (z : ℍ) : ℕ :=
  (ambientStabilizer Δ z).relIndex (ambientStabilizer Γ z)

/-- The order of the larger point stabilizer is the order of the smaller stabilizer times the
elliptic ramification index. -/
theorem card_stabilizer_mul_ellipticRamificationIndex (h : Δ ≤ Γ) (z : ℍ) :
    Nat.card (stabilizer Δ z) * ellipticRamificationIndex h z =
      Nat.card (stabilizer Γ z) := by
  have hm := (ambientStabilizer Δ z).relIndex_mul_card (ambientStabilizer Γ z)
  rw [inf_eq_left.mpr (ambientStabilizer_mono h z)] at hm
  rw [card_ambientStabilizer, card_ambientStabilizer, mul_comm] at hm
  exact hm

/-- The elliptic ramification index is positive. -/
theorem ellipticRamificationIndex_pos (h : Δ ≤ Γ) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    0 < ellipticRamificationIndex h z := by
  have hm := card_stabilizer_mul_ellipticRamificationIndex h z
  by_contra hn
  have hz : ellipticRamificationIndex h z = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz, mul_zero] at hm
  exact Nat.card_pos.ne' hm.symm

/-- An identity inclusion has elliptic ramification index one. -/
@[simp]
theorem ellipticRamificationIndex_self (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    ellipticRamificationIndex (le_refl Γ) z = 1 := by
  exact Subgroup.relIndex_self _

/-- Elliptic ramification indices multiply in a tower of subgroup inclusions. -/
theorem ellipticRamificationIndex_mul {Θ : Subgroup PSL(2, ℝ)}
    (h : Δ ≤ Γ) (k : Γ ≤ Θ) (z : ℍ) :
    ellipticRamificationIndex h z * ellipticRamificationIndex k z =
      ellipticRamificationIndex (h.trans k) z :=
  Subgroup.relIndex_mul_relIndex (ambientStabilizer Δ z) (ambientStabilizer Γ z)
    (ambientStabilizer Θ z) (ambientStabilizer_mono h z)
    (ambientStabilizer_mono k z)

/-- In elliptic charts centred at `z`, the map of orbit quotients is the power map whose
exponent is the index of the two stabilizers. -/
theorem stabilizerBallQuotientChart_map_of_le (h : Δ ≤ Γ) (z τ : ℍ) {ε : ℝ}
    [Finite (stabilizer Δ z)] [Finite (stabilizer Γ z)]
    (hε : 0 < ε) (hΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    (hτ : dist τ z < ε) :
    stabilizerBallQuotientChart hε hΓ
        (Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h)
          (Quotient.mk _ τ)) =
      (stabilizerBallQuotientChart hε hΔ (Quotient.mk _ τ)) ^
        ellipticRamificationIndex h z := by
  rw [TauCeti.Setoid.map_of_le_mk, stabilizerBallQuotientChart_mk hε hΓ hτ,
    stabilizerBallQuotientChart_mk hε hΔ hτ, ← pow_mul]
  congr 1
  exact (card_stabilizer_mul_ellipticRamificationIndex h z).symm

/-- On the entire target of the smaller elliptic chart, the coordinate expression of the
quotient map is `u ↦ u ^ ellipticRamificationIndex h z`. -/
theorem stabilizerBallQuotientChart_map_of_le_symm (h : Δ ≤ Γ) (z : ℍ) {ε : ℝ}
    [Finite (stabilizer Δ z)] [Finite (stabilizer Γ z)]
    (hε : 0 < ε) (hΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    {u : ℂ} (hu : u ∈ (stabilizerBallQuotientChart hε hΔ).target) :
    stabilizerBallQuotientChart hε hΓ
        (Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h)
          ((stabilizerBallQuotientChart hε hΔ).symm u)) =
      u ^ ellipticRamificationIndex h z := by
  have hr : 0 ≤ Real.tanh (ε / 2) := by
    rw [← Real.tanh_zero]
    exact Real.tanh_strictMono.monotone (by linarith)
  rw [stabilizerBallQuotientChart_target, ← image_pow_ball hr] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  have hw' : ‖w‖ < Real.tanh (ε / 2) := mem_ball_zero_iff.mp hw
  let τ : ℍ := (discCoordinateHomeomorph z).symm
    (.mk w (hw'.trans (Real.tanh_lt_one _)))
  have hτ : dist τ z < ε := by
    rw [← mem_ball, mem_ball_iff_norm_discCoordinate_lt]
    simpa [τ] using hw'
  rw [stabilizerBallQuotientChart_symm_pow hε hΔ hw']
  simpa [stabilizerBallQuotientChart_mk hε hΔ hτ, τ] using
    stabilizerBallQuotientChart_map_of_le h z τ hε hΔ hΓ hτ

/-- A common positive radius gives elliptic quotient charts for both groups in an inclusion. -/
theorem exists_pos_isOpenEmbedding_stabilizerBallQuotientToQuotient_pair
    (h : Δ ≤ Γ) (z : ℍ) [DiscreteTopology Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ∃ ε : ℝ, 0 < ε ∧
      IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε) ∧
      IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε) := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  exact (eventually_mem_nhdsWithin.and
    ((eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Δ z).and
      (eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z))).exists

/-- The compactified quotient map has the same power expression at an elliptic orbit, using
the charts of the coarse quotient transported into the compactification. -/
theorem compactifiedQuotientMap_ellipticChart (h : Δ ≤ Γ) (z : ℍ)
    [DiscreteTopology Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ∀ {ε : ℝ} (hε : 0 < ε)
      (hΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
      (hΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
      {u : ℂ} (_hu : u ∈ (stabilizerBallQuotientChart hε hΔ).target),
      CompactifiedQuotient.ofQuotientChart (stabilizerBallQuotientChart hε hΓ)
          (compactifiedQuotientMap h
            ((CompactifiedQuotient.ofQuotientChart
              (stabilizerBallQuotientChart hε hΔ)).symm u)) =
        u ^ ellipticRamificationIndex h z := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro ε hε hΔ hΓ u hu
  rw [CompactifiedQuotient.ofQuotientChart_symm_apply,
    compactifiedQuotientMap_ofQuotient,
    CompactifiedQuotient.ofQuotientChart_ofQuotient]
  exact stabilizerBallQuotientChart_map_of_le_symm h z hε hΔ hΓ hu

end Subgroup
