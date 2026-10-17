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

/-- At a finite vertex of a polygon with disjoint translated interiors, the cycle angle sum is
`2π` divided by the order of the cycle transformation, which is not zero. -/
private theorem cycleAngleSum_eq_two_pi_div_of_isLeft {j : Fin n} (hj : (P.vertex j).isLeft)
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    (orderOf (σ.cycleMap j) : ℝ) ≠ 0 ∧
      σ.cycleAngleSum j = 2 * π / orderOf (σ.cycleMap j) := by
  have h := σ.orderOf_cycleMap_mul_cycleAngleSum (Sum.inl_getLeft _ hj).symm hmap hdisj
  have hm : (orderOf (σ.cycleMap j) : ℝ) ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at h
    exact Real.two_pi_pos.ne h
  exact ⟨hm, by rw [eq_div_iff hm, mul_comm, h]⟩

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
  classical
  let m : Fin n → ℝ := fun i ↦ orderOf (σ.cycleMap i)
  let L : Fin n → ℝ := fun i ↦ σ.cycleLength i
  have hleft {j i : Fin n} (hi : i ∈ σ.cycle j) :
      (P.vertex i).isLeft = true ↔ (P.vertex j).isLeft = true := by
    rw [← Sum.not_isRight, ← Sum.not_isRight, σ.isRight_vertex_of_mem_cycle hi]
  -- the angle sum, grouped by cycles
  have hA : ∑ i, P.interiorAngle i =
      ∑ i, if (P.vertex i).isLeft then 2 * π / (m i * L i) else 0 := by
    rw [← σ.sum_cycleAngleSum_div_cycleLength]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with hi
    · rw [(σ.cycleAngleSum_eq_two_pi_div_of_isLeft hi hmap hdisj).2, div_div]
    · rw [σ.cycleAngleSum_eq_zero_of_isRight_vertex (Sum.not_isLeft.1 hi), zero_div]
  -- the number of finite vertex cycles
  have hV : (Nat.card σ.FiniteVertexCycle : ℝ) =
      ∑ i, if (P.vertex i).isLeft then 1 / L i else 0 := by
    have h := σ.finsum_eq_sum_div_cycleLength hleft fun _ ↦ (1 : ℝ)
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_one,
      ← Nat.card_eq_fintype_card] at h
    rw [h, ← Finset.sum_subtype (Finset.univ.filter fun i ↦ (P.vertex i).isLeft)
      (fun _ ↦ by simp) fun i ↦ 1 / L i, Finset.sum_filter]
  -- the elliptic orbits: nontrivial finite vertex cycles and self-paired sides
  have hE : ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) =
      (∑ i, if (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1 then (1 - (m i)⁻¹) / L i else 0) +
        Nat.card {i : Fin n // σ.pair i = i} / 2 := by
    have hp {j i : Fin n} (hi : i ∈ σ.cycle j) :
        ((P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1) ↔ ((P.vertex j).isLeft ∧ σ.cycleMap j ≠ 1) := by
      rw [hleft hi, ne_eq, ne_eq, ← orderOf_eq_one_iff, ← orderOf_eq_one_iff (x := σ.cycleMap j),
        σ.orderOf_cycleMap_of_mem_cycle hi]
    rw [← finsum_set_coe_eq_finsum_mem,
      ← finsum_comp_equiv (σ.ellipticOrbitEquiv hmap hcover hdisj), finsum_eq_sum_of_fintype,
      Fintype.sum_sum_type]
    congr 1
    · rw [← finsum_eq_sum_of_fintype, σ.finsum_eq_sum_div_cycleLength hp,
        Fintype.sum_congr _ (fun i ↦ (1 - (m i.1)⁻¹) / L i.1) fun i ↦ by
          rw [σ.cardStabilizerOnOrbit_ellipticOrbitEquiv_inl_mk],
        ← Finset.sum_subtype (Finset.univ.filter fun i ↦ (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1)
          (fun _ ↦ by simp) fun i ↦ (1 - (m i)⁻¹) / L i, Finset.sum_filter]
    · simp_rw [σ.cardStabilizerOnOrbit_ellipticOrbitEquiv_inr]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
      norm_num
      ring
  -- compare the three sums vertex by vertex
  have hpt (i : Fin n) : (if (P.vertex i).isLeft then 2 * π / (m i * L i) else 0) =
      2 * π * ((if (P.vertex i).isLeft then 1 / L i else 0) -
        if (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1 then (1 - (m i)⁻¹) / L i else 0) := by
    by_cases hl : (P.vertex i).isLeft
    · have hm := (σ.cycleAngleSum_eq_two_pi_div_of_isLeft hl hmap hdisj).1
      have hL : L i ≠ 0 := Nat.cast_ne_zero.2 (σ.cycleLength_pos i).ne'
      by_cases hc : σ.cycleMap i = 1
      · have hm1 : m i = 1 := by simp [m, hc]
        simp only [hl, hc, hm1, ne_eq, not_true_eq_false, and_false, ↓reduceIte, sub_zero, one_mul,
          mul_one_div]
      · simp only [hl, hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        field_simp
        ring
    · simp [hl]
  rw [hA, hV, hE, Finset.sum_congr rfl fun i _ ↦ hpt i, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

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
