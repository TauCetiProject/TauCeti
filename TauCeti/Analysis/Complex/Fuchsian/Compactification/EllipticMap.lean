/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
public import TauCeti.Analysis.Complex.Fuchsian.Stabilizer

/-!
# Elliptic ramification of maps between Fuchsian quotients

For an inclusion `Δ ≤ Γ` of discrete projective subgroups, the stabilizer of a point for `Δ`
embeds in its stabilizer for `Γ`. Thus the smaller stabilizer order divides the larger one.
In the canonical disc coordinates, the map of orbit quotients is the power map whose exponent
is the ratio of those orders. This gives the elliptic local ramification index of the
compactified quotient map in charts with a common admissible radius.

The local cyclic quotient model is described in Farkas–Kra, *Riemann Surfaces*, Chapter I,
§§4–5, and Katok, *Fuchsian Groups*, §2.4.
-/

public noncomputable section

open MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)} (h : Δ ≤ Γ) (z : ℍ)

/-- The elliptic ramification index at `z` is the ratio of the finite stabilizer orders. -/
def ellipticRamificationIndex (_h : Δ ≤ Γ) (z : ℍ)
    [Finite (stabilizer Γ z)] : ℕ := by
  letI : Finite (stabilizer Δ z) :=
    Finite.of_injective (stabilizerInclusion _h z) (stabilizerInclusion_injective _h z)
  letI := Fintype.ofFinite (stabilizer Δ z)
  letI := Fintype.ofFinite (stabilizer Γ z)
  exact Fintype.card (stabilizer Γ z) / Fintype.card (stabilizer Δ z)

/-- The stabilizer order upstairs times the elliptic ramification index is the stabilizer
order downstairs. -/
theorem card_stabilizer_mul_ellipticRamificationIndex (h : Δ ≤ Γ) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    Nat.card (stabilizer Δ z) * ellipticRamificationIndex h z =
      Nat.card (stabilizer Γ z) := by
  let : Finite (stabilizer Δ z) :=
    Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
  simpa only [ellipticRamificationIndex, Fintype.card_eq_nat_card] using
    Nat.mul_div_cancel' (card_stabilizer_dvd_card_stabilizer h z)

/-- Elliptic ramification indices are positive. -/
theorem ellipticRamificationIndex_pos [Finite (stabilizer Γ z)] :
    0 < ellipticRamificationIndex h z := by
    let : Finite (stabilizer Δ z) :=
      Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
    simpa only [ellipticRamificationIndex, Fintype.card_eq_nat_card] using
      Nat.div_pos (Nat.le_of_dvd Nat.card_pos
        (card_stabilizer_dvd_card_stabilizer h z)) Nat.card_pos

/-- The ratio of stabilizer orders is the group-theoretic index of the smaller stabilizer
inside the larger one. -/
theorem ellipticRamificationIndex_eq_index
    [Finite (stabilizer Γ z)] :
    ellipticRamificationIndex h z = (stabilizerInclusion h z).range.index := by
  let : Finite (stabilizer Δ z) :=
    Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
  rw [ellipticRamificationIndex, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Subgroup.index_eq_card_div]
  rw [Nat.card_congr (Equiv.ofInjective (stabilizerInclusion h z)
    (stabilizerInclusion_injective h z))]
  rfl

/-- The identity inclusion has elliptic ramification index one. -/
@[simp]
theorem ellipticRamificationIndex_self (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    ellipticRamificationIndex (le_refl Γ) z = 1 := by
  simpa only [ellipticRamificationIndex, Fintype.card_eq_nat_card] using
    Nat.div_self (Nat.card_pos (α := stabilizer Γ z))

/-- Elliptic ramification indices multiply in a tower of subgroup inclusions. -/
theorem ellipticRamificationIndex_mul {Θ : Subgroup PSL(2, ℝ)}
    (h : Δ ≤ Γ) (k : Γ ≤ Θ) (z : ℍ)
    [Finite (stabilizer Θ z)] :
    let : Finite (stabilizer Γ z) :=
      Finite.of_injective (stabilizerInclusion k z) (stabilizerInclusion_injective k z)
    ellipticRamificationIndex h z * ellipticRamificationIndex k z =
      ellipticRamificationIndex (h.trans k) z := by
  let : Finite (stabilizer Γ z) :=
    Finite.of_injective (stabilizerInclusion k z) (stabilizerInclusion_injective k z)
  let : Finite (stabilizer Δ z) :=
    Finite.of_injective (stabilizerInclusion h z) (stabilizerInclusion_injective h z)
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := stabilizer Δ z))
  calc
    Nat.card (stabilizer Δ z) *
        (ellipticRamificationIndex h z * ellipticRamificationIndex k z) =
        (Nat.card (stabilizer Δ z) * ellipticRamificationIndex h z) *
          ellipticRamificationIndex k z := (mul_assoc ..).symm
    _ = Nat.card (stabilizer Γ z) * ellipticRamificationIndex k z := by
      rw [card_stabilizer_mul_ellipticRamificationIndex h z]
    _ = Nat.card (stabilizer Θ z) := card_stabilizer_mul_ellipticRamificationIndex k z
    _ = Nat.card (stabilizer Δ z) * ellipticRamificationIndex (h.trans k) z :=
      (card_stabilizer_mul_ellipticRamificationIndex (h.trans k) z).symm

/-- Two properly discontinuous actions admit a common positive chart radius at `z`. -/
theorem exists_common_elliptic_chart_radius
    [ProperlyDiscontinuousSMul Δ ℍ] [ProperlyDiscontinuousSMul Γ ℍ] :
    ∃ ε : ℝ, 0 < ε ∧
      IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε) ∧
      IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε) :=
  (eventually_mem_nhdsWithin.and
    ((eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Δ z).and
      (eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z))).exists

/-- In elliptic charts centered at the same upper-half-plane point, the quotient map induced
by `Δ ≤ Γ` is locally `u ↦ u ^ e`, where `e` is the ratio of stabilizer orders. -/
private theorem stabilizerBallQuotientChart_compactifiedQuotientMap_ofQuotient
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
        (stabilizerBallQuotientChart_compactifiedQuotientMap_ofQuotient
          h z hε hε hopenΔ hopenΓ hg hg)

/-- The compactified quotient map has elliptic local expression `u ↦ u ^ e` in the
transported charts at points of the uncompactified quotient. -/
theorem ofQuotientChart_compactifiedQuotientMap_eq_pow_ellipticRamificationIndex
    [DiscreteTopology Γ]
    {ε : ℝ} (hε : 0 < ε)
    (hopenΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hopenΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    {q : orbitRel.Quotient Δ ℍ} :
    let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    q ∈ (stabilizerBallQuotientChart hε hopenΔ).source →
    CompactifiedQuotient.ofQuotientChart (stabilizerBallQuotientChart hε hopenΓ)
      (compactifiedQuotientMap h (.ofQuotient q)) =
      (CompactifiedQuotient.ofQuotientChart (stabilizerBallQuotientChart hε hopenΔ)
        (.ofQuotient q)) ^ ellipticRamificationIndex h z := by
  dsimp only
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro hq
  simpa only [compactifiedQuotientMap_ofQuotient,
    CompactifiedQuotient.ofQuotientChart_ofQuotient] using
    (stabilizerBallQuotientChart_map_eq_pow_ellipticRamificationIndex
      h z hε hopenΔ hopenΓ hq)

end Subgroup
