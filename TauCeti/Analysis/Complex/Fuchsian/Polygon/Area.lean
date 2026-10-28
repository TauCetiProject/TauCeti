/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Polygon
public import TauCeti.Analysis.Complex.Fuchsian.FundamentalPolygon
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Ideal

/-!
# The area of a fundamental polygon through its elliptic orbits

Let `σ` pair the sides of a convex hyperbolic `n`-gon `P`, with vertices in `ℍ ∪ ∂ℍ`, and let
`Γ ≤ PSL(2, ℝ)` contain the side-pairing maps, with translates of `P` covering `ℍ` and distinct
translates of its interior disjoint. Group the interior angles of `P` by vertex cycles. An ideal
cycle has angle sum `0`, while a finite cycle has angle sum `2π / m`, where `m` is the order of
the stabilizer in `Γ` of its vertices. By the classification of the elliptic orbits of `Γ` through
`P`, the elliptic orbits are the finite cycles with `m ≥ 2` together with one orbit of order two
for each of the `k` self-paired sides. Writing `V` for the number of finite vertex cycles, the
angle sum of `P` is therefore

`∑ αᵢ = 2π (V + k / 2 - ∑ₑ (1 - 1 / mₑ))`,

the sum running over the elliptic orbits `e` of `Γ` with stabilizer orders `mₑ`. Combined with
the Gauss–Bonnet formula for the covolume, this gives, for a locally finite fundamental polygon,

`covolume Γ = 2π ((n - k) / 2 - 1 - V + ∑ₑ (1 - 1 / mₑ))`.

This is the orbifold area formula read off from the polygon, with the effective `PSL(2, ℝ)`
stabilizer orders. In the cell decomposition of the compactified quotient given by `P`, with the
`V` finite cycles, the cusp cycles, and the midpoints of the `k` self-paired sides as vertices,
`(n + k) / 2` edges and one face, the polygon count `(n - k) / 2 - 1 - V` is `2g - 2 + s` for a
surface of genus `g` with `s` cusps. The formula then reads `2π (2g - 2 + ∑ₑ (1 - 1 / mₑ) + s)`.
That identification of the polygon count is not proved here.

## Main results

* `ConvexPolygon.SidePairing.finsum_mem_ellipticOrbits_one_sub_inv_eq`: the sum of `1 - 1 / mₑ`
  over the elliptic orbits as a sum over the vertices plus a term for the self-paired sides.
* `ConvexPolygon.SidePairing.sum_interiorAngle_eq_two_pi_mul`: the angle sum of a fundamental
  polygon in terms of its finite vertex cycles, self-paired sides, and the elliptic orbits.
* `ConvexPolygon.SidePairing.covolume_eq_two_pi_mul`: the covolume of `Γ` in the same terms.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§9.3 and 10.4 (the angle sum of a cycle and the signature area formula).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.5 and 4.3 (elliptic cycles, and the area of a fundamental region in terms of
  the signature).
-/

public section

open MeasureTheory MulAction Set UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

open scoped Classical in
/-- **The elliptic orbits read off a fundamental polygon.** If the translates of `P` by a group
`Γ` containing the side-pairing maps cover `ℍ` and have disjoint interiors, the sum of
`1 - 1 / mₑ` over the elliptic orbits `e` of `Γ`, with stabilizer orders `mₑ`, is `k / 2` for the
`k` self-paired sides plus the sum over the finite vertices `i` with nonidentity cycle
transformation of `(1 - 1 / mᵢ) / Lᵢ`. Here `mᵢ` is the order of the cycle transformation at `i`
and `Lᵢ` the length of the cycle through `i`. -/
theorem finsum_mem_ellipticOrbits_one_sub_inv_eq (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) =
      (∑ i, if (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1 then
        (1 - (orderOf (σ.cycleMap i) : ℝ)⁻¹) / σ.cycleLength i else 0) +
        Nat.card {i : Fin n // σ.pair i = i} / 2 := by
  classical
  rw [← finsum_set_coe_eq_finsum_mem,
    ← finsum_comp_equiv (σ.ellipticOrbitEquiv hmap hcover hdisj), finsum_eq_sum_of_fintype,
    Fintype.sum_sum_type]
  congr 1
  · rw [← finsum_eq_sum_of_fintype,
      σ.finsum_eq_sum_ite_div_cycleLength
        (fun hi ↦ by
          rw [σ.isLeft_vertex_eq_of_mem_cycle hi, ne_eq, σ.cycleMap_eq_one_iff_of_mem_cycle hi])
        _ (fun i ↦ 1 - (orderOf (σ.cycleMap i) : ℝ)⁻¹) fun i ↦ by
        rw [σ.cardStabilizerOnOrbit_ellipticOrbitEquiv_inl_mk]]
  · simp_rw [σ.cardStabilizerOnOrbit_ellipticOrbitEquiv_inr]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    norm_num [div_eq_mul_inv]

/-- **The angle sum of a fundamental polygon.** If the translates of `P` by a group `Γ` containing
the side-pairing maps cover `ℍ` and have disjoint interiors, the interior angles of `P` add up to
`2π (V + k / 2 - ∑ₑ (1 - 1 / mₑ))`. Here `V` is the number of finite vertex cycles, `k` the number
of self-paired sides, and `e` runs over the elliptic orbits of `Γ`, with stabilizer orders `mₑ`;
there are finitely many of these. -/
theorem sum_interiorAngle_eq_two_pi_mul (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    ∑ i, P.interiorAngle i = 2 * π * (Nat.card σ.FiniteVertexCycle +
      Nat.card {i : Fin n // σ.pair i = i} / 2 -
        ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹)) := by
  rw [σ.natCard_finiteVertexCycle_eq_sum,
    σ.finsum_mem_ellipticOrbits_one_sub_inv_eq hmap hcover hdisj,
    ← σ.sum_cycleAngleSum_div_cycleLength, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  -- compare the sums vertex by vertex
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hl : (P.vertex i).isLeft
  · have hz := (Sum.inl_getLeft _ hl).symm
    have hm := Nat.cast_ne_zero (R := ℝ) |>.2 (σ.orderOf_cycleMap_ne_zero hz hmap hdisj)
    have hL : (σ.cycleLength i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (σ.cycleLength_pos i).ne'
    rw [σ.cycleAngleSum_eq_two_pi_div hz hmap hdisj]
    by_cases hc : σ.cycleMap i = 1
    · simp [hl, hc, div_eq_mul_inv]
    · simp only [hl, hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      field_simp
      ring
  · simp [hl, σ.cycleAngleSum_eq_zero_of_isRight_vertex (Sum.not_isLeft.1 hl)]

/-- **The orbifold area formula for a fundamental polygon.** Let the translates of a side-paired
convex `n`-gon `P` by a group `Γ` containing the side-pairing maps be locally finite, with disjoint
interiors. Then the covolume of `Γ` is `2π ((n - k) / 2 - 1 - V + ∑ₑ (1 - 1 / mₑ))`, where `k` is
the number of self-paired sides, `V` the number of finite vertex cycles, and `e` runs over the
elliptic orbits of `Γ`, with stabilizer orders `mₑ`. -/
theorem covolume_eq_two_pi_mul (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    covolume Γ ℍ = ENNReal.ofReal (2 * π * ((n - Nat.card {i : Fin n // σ.pair i = i}) / 2 - 1 -
      Nat.card σ.FiniteVertexCycle +
        ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹))) := by
  rw [σ.covolume_eq hmap hlf hdisj,
    σ.sum_interiorAngle_eq_two_pi_mul hmap (σ.iUnion_smul_carrier_eq_univ hmap hlf) hdisj]
  congr 1
  ring

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
