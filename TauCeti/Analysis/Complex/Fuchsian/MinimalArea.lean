/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Field.OrbifoldDeficit
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.EulerCharacteristic
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Finite
import TauCeti.Analysis.Complex.Fuchsian.Cusp.VertexCycle
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Cofinite
import TauCeti.Analysis.Complex.Fuchsian.Polygon.Area
import TauCeti.Analysis.Complex.Fuchsian.Polygon.LocallyFinite

/-!
# The minimal areas of cofinite Fuchsian groups

A cofinite Fuchsian group `Γ` of signature `(g; m₁, …, m_r; c)` has covolume `2π δ` for the
deficit `δ = 2g - 2 + ∑ᵢ (1 - 1 / mᵢ) + c`. Positivity of the covolume forces `δ > 0`, and the
smallest positive values of such deficits are `1 / 42`, attained only at `(0; 2, 3, 7)`, and, when
there is a cusp, `1 / 6`, attained only at `(0; 2, 3; 1)`
(`TauCeti.one_div_forty_two_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast`,
`TauCeti.one_div_six_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast`). This gives Siegel's
theorem: every cofinite Fuchsian group has covolume at least `π / 21`, with equality exactly for
signature `(0; 2, 3, 7)`, and every cofinite group with a cusp has covolume at least `π / 3`, the
covolume of `PSL(2, ℤ)`.

The lower bounds need only `2 - 2g ≤ 2`. They are read off a Dirichlet polygon of `Γ` with a side
pairing by elements of `Γ`: its area formula `covolume Γ = 2π (-χ + ∑ₑ (1 - 1 / mₑ) + c)` holds
with the cell count `χ` of the polygon in place of `2 - 2g`
(`TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.covolume_eq_two_pi_mul_neg_cellEulerChar_add`),
the ideal vertex cycles of the polygon are the cusps of `Γ`, and the cell count is at most `2`
(`TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.cellEulerChar_le_two`). At equality in the
`π / 21` bound there is no cusp, so `Γ` is cocompact and its covolume is
`2π (2g - 2 + ∑ₑ (1 - 1 / mₑ))` for the topological genus `g` of `X(Γ)`
(`Subgroup.covolume_eq_two_pi_mul_two_mul_genus_sub_two_add`). The equality case of the `π / 3`
bound, signature `(0; 2, 3; 1)`, needs the identification of the cell count of a polygon with
cusps with `χ(X(Γ))`, and is not proved here.

## Main results

* `Subgroup.pi_div_twentyOne_le_covolume`: Siegel's bound `π / 21 ≤ covolume Γ`.
* `Subgroup.IsCofinite.covolume_eq_pi_div_twentyOne_iff`: for a cofinite group whose compactified
  quotient has finite CW type, equality holds exactly for signature `(0; 2, 3, 7)`: topological
  genus zero, no cusp, and one elliptic orbit of each order `2`, `3` and `7`.
* `Subgroup.pi_div_three_le_covolume`: a discrete group with a cusp has covolume at least
  `π / 3`.

## References

* Carl Ludwig Siegel, *Some remarks on discontinuous groups*, Annals of Mathematics 46 (1945),
  708–718.
* Gaven J. Martin, *The geometry and arithmetic of Kleinian groups*, arXiv:1311.2636 (2013),
  Theorems 2.1 and 2.2.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.3.
-/

public section

open MeasureTheory MulAction Set UpperHalfPlane TauCeti TauCeti.UpperHalfPlane
  TauCeti.RiemannSurface
open scoped MatrixGroups Real

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The area formula of a cofinite group read off a Dirichlet polygon: the covolume is
`2π (-χ + ∑ₑ (1 - 1 / mₑ) + c)` for the cell count `χ ≤ 2` of the polygon and the number `c` of
cusp orbits. -/
private theorem IsCofinite.exists_le_two_covolume_eq (hΓ : Γ.IsCofinite) :
    ∃ χ : ℤ, χ ≤ 2 ∧ covolume Γ ℍ = ENNReal.ofReal (2 * π * (-(χ : ℝ) +
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) + Nat.card Γ.CuspOrbit)) := by
  have := hΓ.discreteTopology
  obtain ⟨p, hp⟩ := freeLocus_nonempty Γ
  obtain ⟨n, _, P, σ, hmap, hP, hcusp⟩ := hΓ.exists_sidePairing_of_mem_freeLocus hp
  have hlf := P.locallyFinite_smul_carrier_of_isCuspPoint hcusp
  have hdisj := ConvexPolygon.disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain hP hp
  refine ⟨σ.cellEulerChar, σ.cellEulerChar_le_two, ?_⟩
  rw [σ.covolume_eq_two_pi_mul_neg_cellEulerChar_add hmap hlf hdisj,
    σ.natCard_cuspOrbit hmap hlf hdisj]

/-- The covolume of a discrete group is positive, so a formula `covolume Γ = 2π δ` forces
`δ > 0`. -/
private theorem pos_of_covolume_eq [DiscreteTopology Γ] {δ : ℝ}
    (h : covolume Γ ℍ = ENNReal.ofReal (2 * π * δ)) : 0 < δ := by
  have hpos := Γ.covolume_pos
  rw [h, ENNReal.ofReal_pos] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

/-- `ENNReal.ofReal (2π δ) = ENNReal.ofReal (2π a)` exactly when `δ = a`, for `δ, a ≥ 0`. -/
private theorem ofReal_two_pi_mul_eq_ofReal_two_pi_mul_iff {δ a : ℝ} (hδ : 0 ≤ δ) (ha : 0 ≤ a) :
    ENNReal.ofReal (2 * π * δ) = ENNReal.ofReal (2 * π * a) ↔ δ = a := by
  rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity),
    mul_right_inj' (by positivity)]

/-- **Siegel's bound.** Every discrete subgroup of `PSL(2, ℝ)` has covolume at least `π / 21`.
The content is for cofinite groups; the covolume of any other discrete group is infinite. -/
theorem pi_div_twentyOne_le_covolume [DiscreteTopology Γ] :
    ENNReal.ofReal (π / 21) ≤ covolume Γ ℍ := by
  by_cases hΓ : Γ.IsCofinite
  · obtain ⟨χ, hχ, h⟩ := hΓ.exists_le_two_covolume_eq
    have hδ := one_div_forty_two_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast hχ
      (pos_of_covolume_eq h)
    rw [h]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])
  · rw [isCofinite_iff_covolume_ne_top, not_not] at hΓ
    exact hΓ ▸ le_top

/-- **The minimal area with a cusp.** A discrete subgroup of `PSL(2, ℝ)` with at least one cusp
has covolume at least `π / 3`, the covolume of `PSL(2, ℤ)`. The content is for cofinite groups;
the covolume of any other discrete group is infinite. -/
theorem pi_div_three_le_covolume [DiscreteTopology Γ] [Nonempty Γ.CuspOrbit] :
    ENNReal.ofReal (π / 3) ≤ covolume Γ ℍ := by
  by_cases hΓ : Γ.IsCofinite
  · have := hΓ.finite_cuspOrbit
    obtain ⟨χ, hχ, h⟩ := hΓ.exists_le_two_covolume_eq
    have hδ := one_div_six_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast hχ Nat.card_pos
      (pos_of_covolume_eq h)
    rw [h]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])
  · rw [isCofinite_iff_covolume_ne_top, not_not] at hΓ
    exact hΓ ▸ le_top

/-- **The equality case of Siegel's bound.** A cofinite Fuchsian group whose compactified quotient
has finite CW type has covolume `π / 21` exactly when its signature is `(0; 2, 3, 7)`: the
compactified quotient has topological genus zero, there is no cusp, and there is one elliptic
orbit of each order `2`, `3` and `7`. -/
theorem IsCofinite.covolume_eq_pi_div_twentyOne_iff [DiscreteTopology Γ] (hΓ : Γ.IsCofinite)
    [FiniteCWType Γ.CompactifiedQuotient] :
    covolume Γ ℍ = ENNReal.ofReal (π / 21) ↔
      genus Γ.CompactifiedQuotient = 0 ∧ IsEmpty Γ.CuspOrbit ∧
        ∀ m : ℕ, Nat.card {e // e ∈ Γ.ellipticOrbits ∧ cardStabilizerOnOrbit e = m} =
          Multiset.count m {2, 3, 7} := by
  have := hΓ.finite_cuspOrbit
  have hE := hΓ.finite_ellipticOrbits
  have hf : ∀ e ∈ Γ.ellipticOrbits, cardStabilizerOnOrbit e ≠ 1 :=
    fun e ↦ (Γ.mem_ellipticOrbits_iff_cardStabilizerOnOrbit_ne_one e).mp
  rw [show π / 21 = 2 * π * (1 / 42) by ring]
  -- without cusps, `Γ` is cocompact and the signature area formula decides the equality
  have hcocompact (hC : IsEmpty Γ.CuspOrbit) : covolume Γ ℍ = ENNReal.ofReal (2 * π * (1 / 42)) ↔
      genus Γ.CompactifiedQuotient = 0 ∧ ∀ m : ℕ,
        Nat.card {e // e ∈ Γ.ellipticOrbits ∧ cardStabilizerOnOrbit e = m} =
          Multiset.count m {2, 3, 7} := by
    have := compactSpace_quotient_iff_isCofinite_and_isEmpty_cuspOrbit.mpr ⟨hΓ, hC⟩
    have h := covolume_eq_two_pi_mul_two_mul_genus_sub_two_add (Γ := Γ)
    rw [h, ofReal_two_pi_mul_eq_ofReal_two_pi_mul_iff (pos_of_covolume_eq h).le (by norm_num)]
    have key := orbifold_deficit_finsum_eq_one_div_forty_two_iff (K := ℝ) hE
      (g := genus Γ.CompactifiedQuotient) (c := 0) hf
    simpa only [Nat.cast_zero, add_zero, true_and] using key
  refine ⟨fun h ↦ ?_, fun ⟨hg, hC, hfib⟩ ↦ (hcocompact hC).mpr ⟨hg, hfib⟩⟩
  -- at equality the polygon form of the area formula leaves no cusp
  obtain ⟨χ, hχ, hcov⟩ := hΓ.exists_le_two_covolume_eq
  have hδ := h
  rw [hcov, ofReal_two_pi_mul_eq_ofReal_two_pi_mul_iff (pos_of_covolume_eq hcov).le
    (by norm_num), neg_intCast_add_finsum_mem_one_sub_inv_add_natCast_eq_one_div_forty_two_iff hE
    hχ hf] at hδ
  have hC : IsEmpty Γ.CuspOrbit := Finite.card_eq_zero_iff.mp hδ.2.1
  exact ⟨((hcocompact hC).mp h).1, hC, hδ.2.2⟩

end Subgroup
