/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Disc
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.JordanPolygon

/-!
# The disc Schwarz--Christoffel representation of polygonal Jordan domains

Every bounded polygonal Jordan domain is an affine image of a normalized disc
Schwarz--Christoffel primitive. Its prevertices are the Cayley images of the distinct real
prevertices of the corresponding upper-half-plane map, and the map tends to each prescribed
polygon vertex at its prevertex. This puts the existence theorem in the disc coordinates used
for conformal maps of the unit disc.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- **The disc Schwarz--Christoffel representation.** For a bounded polygonal Jordan domain
`U` with distinct vertices `v i` and interior angles `(e i + 1) * π`, there are distinct real
prevertices `a i` and an affine image of the disc Schwarz--Christoffel primitive with disc
prevertices `boundaryCayley (a i)` that maps the unit disc bijectively onto `U`. At each disc
prevertex, its limit from within the disc is the prescribed vertex. -/
theorem exists_bijOn_const_mul_schwarzChristoffelDiscPrimitive_add_of_isJordanCurve_frontier
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUb : IsBounded U) (hUJ : IsJordanCurve (frontier U)) {v : ι → ℂ}
    (hv : Function.Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2)) :
    ∃ a : ι → ℝ, Function.Injective a ∧ ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun ζ => A * schwarzChristoffelDiscPrimitive
        (fun i => boundaryCayley (a i)) e ζ + B) (ball 0 1) U ∧
      ∀ i, Tendsto (fun ζ => A * schwarzChristoffelDiscPrimitive
        (fun j => boundaryCayley (a j)) e ζ + B)
        (𝓝[ball 0 1] (boundaryCayley (a i) : ℂ)) (𝓝 (v i)) := by
  obtain ⟨a, ha, A, hA, B, hmap, hvertex⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier
      e he UpperHalfPlane.I hUo hUc hUb hUJ hv hside hcorner
  have hsum := exponent_sum_eq_neg_two_of_isJordanCurve_frontier
    e he hUo hUc hUb hUJ hv hside hcorner
  obtain ⟨A', hA', B', hdisc, hboundary⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelDiscPrimitive_add_of_bijOn
      a e UpperHalfPlane.I hsum hmap
  refine ⟨a, ha, A', hA', B', hdisc, fun i => ?_⟩
  apply hboundary (a i) (v i)
  have hfilter : (Finset.univ.filter (fun j => a j = a i)) = {i} := by
    ext j
    simp [ha.eq_iff]
  have hfinite : -1 < ∑ j with a j = a i, e j := by
    simpa only [hfilter, Finset.sum_singleton] using (he i).1
  simpa only [hvertex i] using
    ((tendsto_schwarzChristoffelPrimitive a e UpperHalfPlane.I i hfinite).const_mul A).add_const B

end TauCeti
