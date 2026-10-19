/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Disc.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.JordanPolygon
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Power

/-!
# Disc Schwarz--Christoffel maps with a vertex at infinity

An unbounded polygonal Jordan domain that agrees at infinity with a sector of opening `β * π`
has a disc Schwarz--Christoffel representation with one additional prevertex at `1`. Its exponent
is `-β - 1`, whereas the finite vertices retain the exponents given by their interior angles.
Thus the sum of all disc exponents is `-2`, even though the finite half-plane exponents sum to
`β - 1`.

The representation below includes the limits at every finite vertex and divergence at `1`.
In particular, its added exponent is allowed to be less than `-1`: that prevertex maps to
infinity, rather than to a finite corner. The finite prevertices are the Cayley images of distinct
real prevertices, so none equals `1`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

/-- **The disc Schwarz--Christoffel theorem for an unbounded polygonal Jordan domain.**
Suppose a connected open set has Jordan frontier on the Riemann sphere, finitely many distinct
corners of angles `(e i + 1) * π`, straight sides away from those corners, and a sector of opening
`β * π` at infinity. Then it is the bijective image of the unit disc under an affine image of a
disc Schwarz--Christoffel primitive. The finite prevertices have exponents `e i` and tend to the
prescribed vertices; the additional prevertex `1` has exponent `-β - 1` and tends to infinity. -/
theorem exists_bijOn_const_mul_schwarzChristoffelDiscPrimitive_add_of_isJordanCurve_insert_infty
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2) {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) {v : ι → ℂ}
    (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    ∃ a : ι → ℝ, Injective a ∧ ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun ζ => A * schwarzChristoffelDiscPrimitive
        (Option.elim' 1 (fun i => boundaryCayley (a i))) (Option.elim' (-β - 1) e) ζ + B)
        (ball 0 1) U ∧
      (∀ i, Tendsto (fun ζ => A * schwarzChristoffelDiscPrimitive
        (Option.elim' 1 (fun j => boundaryCayley (a j))) (Option.elim' (-β - 1) e) ζ + B)
        (𝓝[ball 0 1] (boundaryCayley (a i) : ℂ)) (𝓝 (v i))) ∧
      Tendsto (fun ζ => A * schwarzChristoffelDiscPrimitive
        (Option.elim' 1 (fun i => boundaryCayley (a i))) (Option.elim' (-β - 1) e) ζ + B)
        (𝓝[ball 0 1] 1) (cobounded ℂ) := by
  let z₀ : UpperHalfPlane := UpperHalfPlane.I
  obtain ⟨a, ha, A, hA, B, hbij, hvertices⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_insert_infty
      e he z₀ hβ hUo hUc hUJ hv hside hcorner hinfty
  have hsum := exponent_sum_eq_sub_one_of_isJordanCurve_insert_infty
    e he hβ hUo hUc hUJ hv hside hcorner hinfty
  have hexp : -∑ i, e i - 2 = -β - 1 := by rw [hsum]; ring
  obtain ⟨A', hA', B', hbij', hfinite, hdiv⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelDiscPrimitive_add_with_infty_of_bijOn a e z₀ hbij
  simp only [hexp] at hbij' hfinite hdiv
  refine ⟨a, ha, A', hA', B', hbij', fun i => ?_, hdiv ?_⟩
  · have hsum_i : -1 < ∑ j with a j = a i, e j := by
      rw [Finset.sum_eq_single_of_mem i (by simp) fun j hj hji =>
        absurd (ha (Finset.mem_filter.mp hj).2) hji]
      exact (he i).1
    apply hfinite (a i) (v i)
    simpa only [hvertices i] using
      ((tendsto_schwarzChristoffelPrimitive a e z₀ i hsum_i).const_mul A).add_const B
  · exact (tendsto_add_const_cobounded B).comp
      ((tendsto_mul_left_cobounded hA).comp
        (tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_neg_one_lt_sum
          a e z₀ (by rw [hsum]; linarith [hβ.1])))

end TauCeti
