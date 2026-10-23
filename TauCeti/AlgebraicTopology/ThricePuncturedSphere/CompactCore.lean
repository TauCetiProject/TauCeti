/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
public import TauCeti.Topology.Covering.Finite
public import TauCeti.Topology.Covering.Proper

/-!
# The compact cores of the thrice-punctured sphere

For `ρ > 0`, the *compact core* `compactCore ρ` of `ℂ ∖ {0, 1}` is the set of points at distance
at least `ρ` from each of the three punctures, measured in the standard local coordinate `z`,
`1 - z` or `1 / z` at `0`, `1` or `∞`:

  `compactCore ρ = {z | ρ ≤ ‖z‖ ∧ ρ ≤ ‖z - 1‖ ∧ ‖z‖ ≤ ρ⁻¹}`.

It is compact, and every compact subset of `ℂ ∖ {0, 1}` lies in one of them, so the complements
of the compact cores form a basis of the cocompact filter: going to infinity in `ℂ ∖ {0, 1}`
means approaching one of the three punctures. The core of radius `1 / 2` is the complement of
the three standard punctured neighbourhoods.

A finite cover of `ℂ ∖ {0, 1}` is a proper map, so the preimage of every compact core is compact.
This is the compactness input for filling in the punctures of a finite cover: for small `ρ > 0`,
the cover is the union of the compact preimage of `compactCore ρ` and of its parts over the closed
punctured discs `0 < ‖w‖ ≤ ρ` in the coordinates `w` at `0`, `1` and `∞`. In the filling charts,
each of these parts becomes a finite union of closed discs, hence compact, once its centres are
added.

## Main definitions

* `TauCeti.ThricePuncturedSphere.compactCore`: the points at distance at least `ρ` from the
  three punctures.

## Main results

* `TauCeti.ThricePuncturedSphere.isCompact_compactCore`: the compact cores are compact.
* `TauCeti.ThricePuncturedSphere.exists_subset_compactCore`: every compact set lies in a compact
  core.
* `TauCeti.ThricePuncturedSphere.hasBasis_cocompact`: the complements of the compact cores form a
  basis of the cocompact filter.
* `TauCeti.ThricePuncturedSphere.compactCore_one_half`: the compact core of radius `1 / 2` is the
  complement of the three standard punctured neighbourhoods.
* `TauCeti.ThricePuncturedSphere.Puncture.mem_compactCore_iff`: on the standard punctured
  neighbourhood of a puncture, the compact core of radius `ρ > 0` is cut out by the standard
  coordinate having norm at least `2 * ρ`.
* `IsCoveringMap.isCompact_preimage_compactCore`: a covering map of `ℂ ∖ {0, 1}` with one finite
  fibre has compact preimage over every compact core.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7.
-/

public section

open Set Filter

namespace TauCeti

namespace ThricePuncturedSphere

/-- The **compact core** of radius `ρ` of the thrice-punctured sphere: the points at distance at
least `ρ` from `0` and from `1`, and at distance at most `ρ⁻¹` from `0`. In the standard local
coordinates `z`, `1 - z` and `1 / z` at the three punctures, for `ρ > 0` these are the points whose
coordinate has norm at least `ρ`. For `ρ ≤ 0`, the compact core is empty. -/
def compactCore (ρ : ℝ) : Set ThricePuncturedSphere :=
  {z | ρ ≤ ‖(z : ℂ)‖ ∧ ρ ≤ ‖(z : ℂ) - 1‖ ∧ ‖(z : ℂ)‖ ≤ ρ⁻¹}

@[simp]
theorem mem_compactCore {ρ : ℝ} {z : ThricePuncturedSphere} :
    z ∈ compactCore ρ ↔ ρ ≤ ‖(z : ℂ)‖ ∧ ρ ≤ ‖(z : ℂ) - 1‖ ∧ ‖(z : ℂ)‖ ≤ ρ⁻¹ :=
  Iff.rfl

/-- The compact core is compact: for `ρ > 0` its image in `ℂ` is closed and bounded and avoids the
two finite punctures, and for `ρ ≤ 0` it is empty. -/
theorem isCompact_compactCore (ρ : ℝ) : IsCompact (compactCore ρ) := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · have hempty : compactCore ρ = ∅ := eq_empty_of_forall_notMem fun z hz ↦
      (norm_pos_iff.mpr z.ne_zero).not_ge (hz.2.2.trans (inv_nonpos.mpr hρ))
    exact hempty ▸ isCompact_empty
  let K : Set ℂ := {z | ρ ≤ ‖z‖ ∧ ρ ≤ ‖z - 1‖ ∧ ‖z‖ ≤ ρ⁻¹}
  have hK : IsCompact K := by
    refine (isCompact_closedBall (0 : ℂ) ρ⁻¹).of_isClosed_subset ?_ fun z hz ↦ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
          (isClosed_le continuous_norm continuous_const))
    · simpa using hz.2.2
  have hrange : K ⊆ range ((↑) : ThricePuncturedSphere → ℂ) := by
    rintro z ⟨h0, h1, -⟩
    exact ⟨⟨z, norm_pos_iff.mp (hρ.trans_le h0),
      sub_ne_zero.mp (norm_pos_iff.mp (hρ.trans_le h1))⟩, rfl⟩
  exact isOpenEmbedding_coe.isInducing.isCompact_preimage' hK hrange

/-- **Every compact subset of the thrice-punctured sphere lies in a compact core**: on a compact
set, the distances to the three punctures in their local coordinates are bounded below by a
positive constant. -/
theorem exists_subset_compactCore {K : Set ThricePuncturedSphere} (hK : IsCompact K) :
    ∃ ρ, 0 < ρ ∧ K ⊆ compactCore ρ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, empty_subset _⟩
  -- The smallest of the three local coordinate norms `‖z‖`, `‖z - 1‖` and `‖1 / z‖`.
  let g : ThricePuncturedSphere → ℝ := fun z ↦ min (min ‖(z : ℂ)‖ ‖(z : ℂ) - 1‖) ‖(z : ℂ)‖⁻¹
  have hg : Continuous g := by
    have h0 : Continuous fun z : ThricePuncturedSphere ↦ ‖(z : ℂ)‖ :=
      continuous_subtype_val.norm
    exact (h0.min (continuous_subtype_val.sub continuous_const).norm).min
      (h0.inv₀ fun z ↦ norm_ne_zero_iff.mpr z.ne_zero)
  have hpos (z : ThricePuncturedSphere) : 0 < g z := by
    have h0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
    have h1 : 0 < ‖(z : ℂ) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr z.ne_one)
    exact lt_min (lt_min h0 h1) (inv_pos.mpr h0)
  obtain ⟨z₀, -, hz₀⟩ := hK.exists_isMinOn hne hg.continuousOn
  refine ⟨g z₀, hpos z₀, fun z hz ↦ ?_⟩
  have hle : g z₀ ≤ g z := hz₀ hz
  refine ⟨hle.trans ((min_le_left _ _).trans (min_le_left _ _)),
    hle.trans ((min_le_left _ _).trans (min_le_right _ _)), ?_⟩
  rw [le_inv_comm₀ (norm_pos_iff.mpr z.ne_zero) (hpos z₀)]
  exact hle.trans (min_le_right _ _)

/-- The complements of the compact cores of positive radius form a basis of the cocompact filter
on the thrice-punctured sphere. -/
theorem hasBasis_cocompact :
    (cocompact ThricePuncturedSphere).HasBasis (fun ρ : ℝ ↦ 0 < ρ) fun ρ ↦ (compactCore ρ)ᶜ :=
  Filter.hasBasis_cocompact.to_hasBasis
    (fun _ hK ↦ (exists_subset_compactCore hK).imp fun _ h ↦ ⟨h.1, compl_subset_compl.mpr h.2⟩)
    fun ρ _ ↦ ⟨_, isCompact_compactCore ρ, subset_rfl⟩

/-- On the standard punctured neighbourhood of a puncture, the compact core of radius `ρ > 0`
consists of the points whose standard coordinate has norm at least `2 * ρ`: the cores are the
complements of the punctured discs of radius `2 * ρ` about the three punctures in these
coordinates. -/
theorem Puncture.mem_compactCore_iff (q : Puncture) {ρ : ℝ} (hρ : 0 < ρ)
    {z : ThricePuncturedSphere} (hz : z ∈ q.neighborhood) :
    z ∈ compactCore ρ ↔ 2 * ρ ≤ ‖(q.coord ⟨z, hz⟩ : ℂ)‖ := by
  have hinv : ρ ≤ 1 / 2 ↔ 2 ≤ ρ⁻¹ := by
    rw [le_inv_comm₀ two_pos hρ, one_div]
  have h0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
  have h1 := norm_sub_norm_le (z : ℂ) 1
  have h1' := norm_sub_norm_le 1 (z : ℂ)
  rw [norm_sub_rev, norm_one] at h1'
  rw [norm_one] at h1
  have hz' := hz
  cases q with
  | zero =>
    rw [Puncture.neighborhood_zero, mem_puncturedNeighborhoodZero] at hz'
    rw [mem_compactCore, Puncture.coe_coord_zero, norm_mul, Complex.norm_two]
    refine ⟨fun h ↦ by linarith [h.1], fun h ↦ ?_⟩
    have := hinv.1 (by linarith)
    exact ⟨by linarith, by linarith, by linarith⟩
  | one =>
    rw [Puncture.neighborhood_one, mem_puncturedNeighborhoodOne] at hz'
    rw [mem_compactCore, Puncture.coe_coord_one, norm_mul, Complex.norm_two, norm_sub_rev]
    refine ⟨fun h ↦ by linarith [h.2.1], fun h ↦ ?_⟩
    have : ρ ≤ ‖(z : ℂ) - 1‖ := by rw [norm_sub_rev]; linarith
    have := hinv.1 (by linarith)
    exact ⟨by linarith, by linarith, by linarith⟩
  | inf =>
    rw [Puncture.neighborhood_inf, mem_puncturedNeighborhoodInf] at hz'
    have key : 2 * ρ ≤ 2 / ‖(z : ℂ)‖ ↔ ‖(z : ℂ)‖ ≤ ρ⁻¹ := by
      rw [le_div_iff₀ h0, ← one_div, le_div_iff₀' hρ]
      constructor <;> intro <;> linarith
    rw [mem_compactCore, Puncture.coe_coord_inf, norm_div, Complex.norm_two, key]
    refine ⟨fun h ↦ h.2.2, fun h ↦ ?_⟩
    have := hinv.2 (by linarith)
    exact ⟨by linarith, by linarith, h⟩

/-- The compact core of radius `1 / 2` is the complement of the three standard punctured
neighbourhoods of `0`, `1` and `∞`. -/
theorem compactCore_one_half : compactCore (1 / 2) =
    (puncturedNeighborhoodZero ∪ puncturedNeighborhoodOne ∪ puncturedNeighborhoodInf)ᶜ := by
  ext z
  simp [not_lt, and_assoc]

end ThricePuncturedSphere

open ThricePuncturedSphere

/-- **The compact core of a finite cover.** A covering map of the thrice-punctured sphere with one
finite fibre has finite fibres everywhere, so it is proper and the preimage of every compact core
is compact. -/
theorem _root_.IsCoveringMap.isCompact_preimage_compactCore {E : Type*} [TopologicalSpace E]
    {p : E → ThricePuncturedSphere} (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere}
    (hfin : Finite (p ⁻¹' {z₀})) (ρ : ℝ) : IsCompact (p ⁻¹' compactCore ρ) :=
  (hp.isProperMap (finite_fiber_of_finite_fiber hp hfin)).isCompact_preimage
    (isCompact_compactCore ρ)

end TauCeti
