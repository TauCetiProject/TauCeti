/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Basic
public import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# Ramification in elliptic charts of Fuchsian quotients

For an inclusion `Δ ≤ Γ` of subgroups of `PSL(2, ℝ)`, the relative index of their point
stabilizers is the local power-map exponent when the stabilizers are finite. This file computes
the induced map in the elliptic charts of the coarse quotients.

The local cyclic-disc model follows Farkas--Kra, *Riemann Surfaces*, Chapter I, §§4--5.
-/

public noncomputable section

open Filter Metric MulAction TauCeti Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

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

private theorem ambientStabilizer_smul (Γ : Subgroup PSL(2, ℝ)) (g : Γ) (z : ℍ) :
    ambientStabilizer Γ (g • z) =
      MulAut.conj (g : PSL(2, ℝ)) • ambientStabilizer Γ z := by
  unfold ambientStabilizer
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.pointwise_smul_def, Subgroup.map_map]
  let f : PSL(2, ℝ) →* PSL(2, ℝ) :=
    (MulDistribMulAction.toMonoidEnd (MulAut PSL(2, ℝ)) PSL(2, ℝ))
      (MulAut.conj (g : PSL(2, ℝ)))
  calc
    _ = (stabilizer Γ z).map (f.comp Γ.subtype) := by
      apply congrArg (fun k : Γ →* PSL(2, ℝ) => (stabilizer Γ z).map k)
      ext x
      simp [f, MulAut.conj_apply]
    _ = _ := (Subgroup.map_map (stabilizer Γ z) f Γ.subtype).symm

/-- The relative index of the smaller point stabilizer in the larger one. For finite stabilizers,
this is the exponent of the local power map at the orbit of `z`. -/
def ellipticRamificationIndex (_h : Δ ≤ Γ) (z : ℍ) : ℕ :=
  ((stabilizer Δ z).map Δ.subtype).relIndex ((stabilizer Γ z).map Γ.subtype)

/-- The elliptic ramification index is the relative index of the ambient point stabilizers. -/
theorem ellipticRamificationIndex_def (h : Δ ≤ Γ) (z : ℍ) :
    ellipticRamificationIndex h z =
      ((stabilizer Δ z).map Δ.subtype).relIndex ((stabilizer Γ z).map Γ.subtype) := by
  rw [ellipticRamificationIndex]

/-- The relative stabilizer index depends only on the source orbit. -/
theorem ellipticRamificationIndex_smul (h : Δ ≤ Γ) (g : Δ) (z : ℍ) :
    ellipticRamificationIndex h (g • z) = ellipticRamificationIndex h z := by
  let gΓ : Γ := ⟨g.1, h g.2⟩
  have hgΓ : gΓ • z = g • z := by
    simp only [Subgroup.smul_def, gΓ]
  calc
    ellipticRamificationIndex h (g • z) =
        (ambientStabilizer Δ (g • z)).relIndex
          (ambientStabilizer Γ (gΓ • z)) := by
            simp only [ellipticRamificationIndex_def, ambientStabilizer, hgΓ]
    _ = (ambientStabilizer Δ z).relIndex (ambientStabilizer Γ z) := by
      rw [ambientStabilizer_smul Δ g z, ambientStabilizer_smul Γ gΓ z]
      exact Subgroup.relIndex_pointwise_smul (MulAut.conj (g : PSL(2, ℝ))) _ _
    _ = ellipticRamificationIndex h z := by
      simp only [ellipticRamificationIndex_def, ambientStabilizer]

/-- Ramification is trivial exactly when the two ambient point stabilizers agree. -/
@[simp]
theorem ellipticRamificationIndex_eq_one_iff (h : Δ ≤ Γ) (z : ℍ) :
    ellipticRamificationIndex h z = 1 ↔
      (stabilizer Δ z).map Δ.subtype = (stabilizer Γ z).map Γ.subtype := by
  unfold ellipticRamificationIndex
  rw [Subgroup.relIndex_eq_one]
  exact ⟨fun hk => le_antisymm (ambientStabilizer_mono h z) hk,
    fun he => he ▸ le_refl _⟩

/-- The induced map is unramified at a free point of the larger group. -/
@[simp]
theorem ellipticRamificationIndex_eq_one_of_stabilizer_eq_bot (h : Δ ≤ Γ) (z : ℍ)
    (hz : stabilizer Γ z = ⊥) : ellipticRamificationIndex h z = 1 := by
  apply (ellipticRamificationIndex_eq_one_iff h z).2
  apply le_antisymm (ambientStabilizer_mono h z)
  simp only [ambientStabilizer] at *
  simp [hz]

/-- The `Nat.card` of the larger point stabilizer equals that of the smaller stabilizer times
the relative index. For finite stabilizers, this is an identity of group orders. -/
theorem card_stabilizer_mul_ellipticRamificationIndex (h : Δ ≤ Γ) (z : ℍ) :
    Nat.card (stabilizer Δ z) * ellipticRamificationIndex h z =
      Nat.card (stabilizer Γ z) := by
  have hm := (ambientStabilizer Δ z).relIndex_mul_card (ambientStabilizer Γ z)
  rw [inf_eq_left.mpr (ambientStabilizer_mono h z)] at hm
  rw [card_ambientStabilizer, card_ambientStabilizer, mul_comm] at hm
  exact hm

/-- For a finite point stabilizer, the relative index is the quotient of stabilizer orders. -/
theorem ellipticRamificationIndex_eq_card_div (h : Δ ≤ Γ) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    ellipticRamificationIndex h z =
      Nat.card (stabilizer Γ z) / Nat.card (stabilizer Δ z) := by
  let : Finite (stabilizer Δ z) := finite_stabilizer_of_le h z
  rw [← card_stabilizer_mul_ellipticRamificationIndex h z,
    Nat.mul_div_cancel_left _ Nat.card_pos]

/-- For finite stabilizers, the relative index is the group index of the inclusion map. -/
theorem ellipticRamificationIndex_eq_index (h : Δ ≤ Γ) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    ellipticRamificationIndex h z = (stabilizerInclusion h z).range.index := by
  let : Finite (stabilizer Δ z) := finite_stabilizer_of_le h z
  have hcard : Nat.card (stabilizerInclusion h z).range =
      Nat.card (stabilizer Δ z) := by
    simpa only [Subgroup.map_top, Subgroup.card_top] using
      (Subgroup.card_map_of_injective
        (K := (⊤ : Subgroup (stabilizer Δ z))) (stabilizerInclusion_injective h z))
  rw [ellipticRamificationIndex_eq_card_div h z, Subgroup.index_eq_card_div, hcard]

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
theorem ellipticRamificationIndex_tower {Θ : Subgroup PSL(2, ℝ)}
    (h : Δ ≤ Γ) (k : Γ ≤ Θ) (z : ℍ) :
    ellipticRamificationIndex h z * ellipticRamificationIndex k z =
      ellipticRamificationIndex (h.trans k) z :=
  Subgroup.relIndex_mul_relIndex (ambientStabilizer Δ z) (ambientStabilizer Γ z)
    (ambientStabilizer Θ z) (ambientStabilizer_mono h z)
    (ambientStabilizer_mono k z)

/-- In elliptic charts centred at `z`, the map of orbit quotients is the power map whose
exponent is the index of the two stabilizers. -/
theorem stabilizerBallQuotientChart_map_of_le (h : Δ ≤ Γ) (z τ : ℍ)
    [Finite (stabilizer Γ z)] :
    letI : Finite (stabilizer Δ z) := finite_stabilizer_of_le h z
    ∀ {ε : ℝ} (hε : 0 < ε) (hΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    (_hτ : dist τ z < ε),
    stabilizerBallQuotientChart hε hΓ
        (Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h)
          (Quotient.mk _ τ)) =
      (stabilizerBallQuotientChart hε hΔ (Quotient.mk _ τ)) ^
        ellipticRamificationIndex h z := by
  intro ε hε hΔ hΓ hτ
  have : Finite (stabilizer Δ z) := finite_stabilizer_of_le h z
  rw [TauCeti.Setoid.map_of_le_mk, stabilizerBallQuotientChart_mk hε hΓ hτ,
    stabilizerBallQuotientChart_mk hε hΔ hτ, ← pow_mul]
  congr 1
  exact (card_stabilizer_mul_ellipticRamificationIndex h z).symm

/-- On the entire target of the smaller elliptic chart, the coordinate expression of the
quotient map is `u ↦ u ^ ellipticRamificationIndex h z`. -/
theorem stabilizerBallQuotientChart_map_of_le_symm (h : Δ ≤ Γ) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    letI : Finite (stabilizer Δ z) := finite_stabilizer_of_le h z
    ∀ {ε : ℝ} (hε : 0 < ε) (hΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    {u : ℂ} (_hu : u ∈ (stabilizerBallQuotientChart hε hΔ).target),
    stabilizerBallQuotientChart hε hΓ
        (Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h)
          ((stabilizerBallQuotientChart hε hΔ).symm u)) =
      u ^ ellipticRamificationIndex h z := by
  intro ε hε hΔ hΓ u hu
  have : Finite (stabilizer Δ z) := finite_stabilizer_of_le h z
  have hr : 0 ≤ Real.tanh (ε / 2) := by
    rw [← Real.tanh_zero]; exact (Real.tanh_strictMono (by linarith)).le
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

variable {Δ Γ : Subgroup PSL(2, ℝ)} (h : Δ ≤ Γ) (z : ℍ)

/-- Two properly discontinuous actions admit a common positive chart radius at `z`. -/
theorem exists_common_elliptic_chart_radius
    [ProperlyDiscontinuousSMul Δ ℍ] [ProperlyDiscontinuousSMul Γ ℍ] :
    ∃ ε : ℝ, 0 < ε ∧
      IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε) ∧
      IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε) :=
  (eventually_mem_nhdsWithin.and
    ((eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Δ z).and
      (eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z))).exists

/-- For a representative lying in both chart balls centered at the same point, the map induced
by `Δ ≤ Γ` has chart expression `u ↦ u ^ e`. The two chart radii may differ. -/
theorem stabilizerBallQuotientChart_map_mk_eq_pow_ellipticRamificationIndex
    [Finite (stabilizer Γ z)]
    {εΔ εΓ : ℝ} (hεΔ : 0 < εΔ) (hεΓ : 0 < εΓ)
    (hopenΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z εΔ))
    (hopenΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z εΓ))
    {τ : ℍ} (hτΔ : dist τ z < εΔ) (hτΓ : dist τ z < εΓ) :
    let : Finite (stabilizer Δ z) :=
      Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
    stabilizerBallQuotientChart hεΓ hopenΓ
      (Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h)
        (Quotient.mk _ τ)) =
      (stabilizerBallQuotientChart hεΔ hopenΔ (Quotient.mk _ τ)) ^
        ellipticRamificationIndex h z := by
  dsimp only
  let : Finite (stabilizer Δ z) :=
    Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
  rw [TauCeti.Setoid.map_of_le_mk,
    stabilizerBallQuotientChart_mk hεΓ hopenΓ hτΓ,
    stabilizerBallQuotientChart_mk hεΔ hopenΔ hτΔ,
    ← pow_mul, card_stabilizer_mul_ellipticRamificationIndex h z]

/-- The map of orbit quotients sends the source of a chart centered at `z` into the
corresponding chart source for the larger group, when both use the same radius. -/
theorem map_mem_stabilizerBallQuotientChart_source
    [Finite (stabilizer Γ z)]
    {ε : ℝ} (hε : 0 < ε)
    (hopenΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hopenΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    {q : orbitRel.Quotient Δ ℍ} :
    let : Finite (stabilizer Δ z) :=
      Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
    q ∈ (stabilizerBallQuotientChart hε hopenΔ).source →
    Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) q ∈
      (stabilizerBallQuotientChart hε hopenΓ).source := by
  dsimp only
  let : Finite (stabilizer Δ z) :=
    Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
  intro hq
  induction q using Quotient.inductionOn' with
  | h τ =>
      obtain ⟨g, hg⟩ := (mem_stabilizerBallQuotientChart_source_iff hε hopenΔ).1 hq
      rw [TauCeti.Setoid.map_of_le_mk]
      exact (mem_stabilizerBallQuotientChart_source_iff hε hopenΓ).2
        ⟨⟨g.1, h g.2⟩, hg⟩

/-- On the entire source of a common elliptic chart, the quotient map is the power map
of degree equal to the elliptic ramification index. -/
theorem stabilizerBallQuotientChart_map_eq_pow_ellipticRamificationIndex
    [Finite (stabilizer Γ z)]
    {ε : ℝ} (hε : 0 < ε)
    (hopenΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hopenΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    {q : orbitRel.Quotient Δ ℍ} :
    let : Finite (stabilizer Δ z) :=
      Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
    q ∈ (stabilizerBallQuotientChart hε hopenΔ).source →
    stabilizerBallQuotientChart hε hopenΓ
      (Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) q) =
      (stabilizerBallQuotientChart hε hopenΔ q) ^ ellipticRamificationIndex h z := by
  dsimp only
  let : Finite (stabilizer Δ z) :=
    Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
  intro hq
  induction q using Quotient.inductionOn' with
  | h τ =>
      obtain ⟨g, hg⟩ := (mem_stabilizerBallQuotientChart_source_iff hε hopenΔ).1 hq
      have heq : (Quotient.mk _ (g • τ) : orbitRel.Quotient Δ ℍ) = Quotient.mk _ τ :=
        Quotient.sound (orbitRel_apply.mpr (mem_orbit τ g))
      simpa only [heq] using
        (stabilizerBallQuotientChart_map_mk_eq_pow_ellipticRamificationIndex
          h z hε hε hopenΔ hopenΓ hg hg)

end Subgroup
