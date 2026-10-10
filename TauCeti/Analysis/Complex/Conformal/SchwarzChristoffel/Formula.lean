/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Prevertex

-- Non-public: the boundary-arc continuation of the pre-Schwarzian derivative and the passage from
-- decay along the upper half-plane to decay at infinity are used only in the proof.
import TauCeti.Analysis.Complex.Conformal.Reflection.LogDeriv
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Analysis.Contour.PolarPart.PartialFraction

/-!
# The Schwarz--Christoffel formula from local polygonal boundary data

A locally conformal map `f` of the upper half-plane satisfying the prescribed straight-side,
corner and end boundary conditions, and an asymptotic condition at infinity, is completely
determined, up to an affine map of the target, by the real **prevertices** `a i` and the
**turning exponents** `e i`: it is `A * F + B`, where `F` is the normalized Schwarz--Christoffel
primitive for `a` and `e`.

Away from the prevertices, `f` extends continuously and injectively to the real axis with boundary
values on an affine line, the nearby upper half-plane lying strictly to one side of it; that is,
the boundary interval is carried into a side.  At a prevertex `a i` the polygon has either a finite
vertex or a vertex at infinity.

* At a finite vertex, the image `f - f (a i)`, rotated and scaled by some `b ≠ 0`, lies inside the
  sector of opening `(e i + 1) * π` and has boundary values on its two rays; that is, the two
  sides meeting at the vertex `f (a i)` make the interior angle `(e i + 1) * π`.  The exponent
  condition `e i ∈ Ioo (-1) 1` says that angle lies strictly between `0` and `2 * π`, so both
  convex and reentrant vertices are allowed.
* At a vertex at infinity of opening `β * π`, with `0 < β < 2`, the inverted map `b / (f - c)`
  extends continuously and injectively across `a i` with value `0` there, fills the sector of
  opening `β * π` above the axis, and has its other boundary values on the two bounding rays.
  The two unbounded sides then lie on lines through `c`, and the turning exponent is
  `e i = -β - 1 ∈ Ioo (-3) (-1)`.
* At a vertex at infinity of opening `0`, between two parallel sides, the exponential
  `exp ((f - c) / b)` extends continuously and injectively across `a i` with value `0` there,
  with real boundary values and the nearby upper half-plane carried into the upper half-plane.
  The turning exponent is then `e i = -1`.

With several prevertices of the last two kinds, this describes polygons with several vertices at
infinity, such as strips.

At infinity the condition is that `z * f''(z) / f'(z)` has a finite limit `L` as `z` tends to
infinity in the upper half-plane.  The geometric conditions at infinity supply it, by
`TauCeti.Analysis.Complex.Conformal.Reflection.Infinity`: if the point at infinity is carried into
a side of the polygon then `L = -2`, and if it is carried to a vertex at infinity, between two
unbounded sides spanning a sector of opening `β * π`, then `L = β - 1`.  In either case `L` is the
sum of the turning exponents.

These are local conditions; they do not assert global injectivity or surjectivity onto a
polygon.  Under these conditions, the proof runs the classical argument: the pre-Schwarzian
derivative `f'' / f'` continues by Schwarz reflection across every boundary side to a
conjugation-symmetric function holomorphic off the prevertices, a straightened corner, a power
coordinate at a vertex at infinity, or the logarithm at a parallel-sided end gives it the residue
`e i` at `a i`, the condition at infinity makes it decay there, so partial fractions identify it
with `∑ i, e i / (z - a i)`, and integrating that differential equation recovers `f`.

## Main results

* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` -- a locally
  conformal map of the upper half-plane satisfying the prescribed local side, corner and end
  conditions, with `z * f''(z) / f'(z)` convergent at infinity, is an affine image of the
  Schwarz--Christoffel primitive for `a` and `e`.
* `TauCeti.exponent_sum_eq_of_logDeriv_deriv_eqOn` -- if the pre-Schwarzian derivative of such a
  map is `∑ i, e i / (z - a i)`, then `∑ i, e i` is the limit of `z * f''(z) / f'(z)` at infinity.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

/-- **The exponent sum is the limit at infinity.**  Let `f` have pre-Schwarzian derivative
`f'' / f' = ∑ i, e i / (z - a i)` on the upper half-plane, where the poles `a i` and coefficients
`e i` may be complex, and suppose that `z * f''(z) / f'(z) → L` as `z` tends to infinity in the
upper half-plane.  Then `∑ i, e i = L`.

When the point at infinity is carried into a side of a polygon, `L = -2`
(`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_neg_inv`); for the turning
exponents `e i = α i / π - 1` of a polygon with interior angles `α i`, this is the angle sum
`∑ i, α i = (n - 2) * π`. -/
theorem exponent_sum_eq_of_logDeriv_deriv_eqOn
    {ι : Type*} [Fintype ι] (a e : ι → ℂ) {f : ℂ → ℂ} {L : ℂ}
    (hpre : EqOn (logDeriv (deriv f))
      (fun z => ∑ i, e i / (z - a i)) upperHalfPlaneSet)
    (hinfty : Tendsto (fun z => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 L)) :
    ∑ i, e i = L := by
  have hsum := tendsto_mul_sum_div_sub_cobounded (S := Finset.univ) a e
  exact tendsto_nhds_unique (hsum.mono_left inf_le_left) (hinfty.congr' <| by
    rw [eventuallyEq_inf_principal_iff]
    exact Eventually.of_forall fun z hz => by rw [hpre hz])

/-- **The Schwarz--Christoffel formula.**  Let `f` be holomorphic with nonvanishing derivative on
the upper half-plane.  Assume that away from the distinct real prevertices `a i` its boundary
values run along affine lines with the upper half-plane on one side, and that each `a i` is
carried to a vertex of one of three kinds:
* a finite vertex: `f` opens the sector of angle `(e i + 1) * π` at `f (a i)`, with boundary values
  on the two bounding rays, where `-1 < e i < 1`;
* a vertex at infinity of opening `β * π` with `0 < β < 2`, where `e i = -β - 1`: the inverted map
  `b / (f - c)` extends across `a i` with value `0`, opens the sector of angle `β * π` there, and
  has its other boundary values on the two bounding rays;
* a vertex at infinity between two parallel sides, where `e i = -1`: the exponential
  `exp ((f - c) / b)` extends across `a i` with value `0`, injectively, with real boundary values
  and upper half-plane values above the axis.

Assume finally that `z * f''(z) / f'(z)` has a finite limit as `z` tends to infinity in the upper
half-plane.  Then throughout the upper half-plane

`f z = (f'(z₀) / integrand(z₀)) * F z + f z₀`,

where `F` is the normalized Schwarz--Christoffel primitive for the data `a` and `e`.  So `f` is an
affine image of `F`, and the two constants are read off from the value and derivative of `f` at
the normalization point `z₀`. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (z₀ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hside : ∀ x : ℝ, (∀ i, a i ≠ x) → ∃ r > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Metric.ball (x : ℂ) r, z.im = 0 → ((f z - q) / b).im = 0) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → 0 < ((f z - q) / b).im)
    (hvertex : ∀ i, (e i ∈ Ioo (-1 : ℝ) 1 ∧ ∃ r > 0, ∃ b : ℂ, b ≠ 0 ∧
      ContinuousOn f (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn f (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Metric.ball ((a i : ℝ) : ℂ) r, 0 < z.im →
        |((f z - f (a i : ℂ)) / b).arg| < (e i + 1) * Real.pi / 2) ∧
      ∀ z ∈ Metric.ball ((a i : ℝ) : ℂ) r, z.im = 0 → f z ≠ f (a i : ℂ) →
        |((f z - f (a i : ℂ)) / b).arg| = (e i + 1) * Real.pi / 2) ∨
      (e i ∈ Ioo (-3 : ℝ) (-1) ∧ ∃ r > 0, ∃ c b : ℂ, b ≠ 0 ∧ ∃ g : ℂ → ℂ,
        EqOn g (fun z => b / (f z - c))
          (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
        g (a i : ℂ) = 0 ∧
        ContinuousOn g (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
        InjOn g (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
        (∀ z ∈ Metric.ball ((a i : ℝ) : ℂ) r, 0 < z.im →
          |(g z).arg| < (-e i - 1) * Real.pi / 2) ∧
        ∀ z ∈ Metric.ball ((a i : ℝ) : ℂ) r, z.im = 0 → g z ≠ 0 →
          |(g z).arg| = (-e i - 1) * Real.pi / 2) ∨
      (e i = -1 ∧ ∃ r > 0, ∃ c b : ℂ, b ≠ 0 ∧ ∃ g : ℂ → ℂ,
        EqOn g (fun z => exp ((f z - c) / b))
          (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
        g (a i : ℂ) = 0 ∧
        ContinuousOn g (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
        (∀ z ∈ Metric.ball ((a i : ℝ) : ℂ) r, z.im = 0 → (g z).im = 0) ∧
        MapsTo g (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} ∧
        InjOn g (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im})))
    {L : ℂ} (hinfty : Tendsto (fun z => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 L)) :
    EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand a e z₀ *
      schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet := by
  have hfin : (range fun i => ((a i : ℝ) : ℂ)).Finite := finite_range _
  have hre : (range fun i => ((a i : ℝ) : ℂ)) ⊆ {z : ℂ | z.im = 0} := by
    rintro _ ⟨i, rfl⟩
    simp
  -- Reflection across the boundary sides continues the pre-Schwarzian derivative off the
  -- prevertices.
  obtain ⟨φ, hφd, hφf, hφconj⟩ :=
    exists_differentiableOn_eqOn_logDeriv_deriv (f := f)
      (S := range fun i => ((a i : ℝ) : ℂ)) hf hfn fun x hx =>
        hside x fun i hi => hx ⟨i, by simp [hi]⟩
  rw [inter_eq_left.mpr hre] at hφd
  -- A straightened corner, or a logarithm at a parallel-sided end, gives it the residue `e i`
  -- at the prevertex `a i`.
  have hpole : ∀ i, Tendsto (fun z => (z - ((a i : ℝ) : ℂ)) * φ z)
      (𝓝[≠] ((a i : ℝ) : ℂ)) (𝓝 ((e i : ℝ) : ℂ)) := by
    intro i
    have hdiff : ((range fun j => ((a j : ℝ) : ℂ)) \ {((a i : ℝ) : ℂ)}).Finite := hfin.sdiff
    obtain ⟨ρ, hρ, hsub⟩ :=
      Metric.isOpen_iff.mp hdiff.isClosed.isOpen_compl ((a i : ℝ) : ℂ) (by simp)
    have hφρ : DifferentiableOn ℂ φ (Metric.ball ((a i : ℝ) : ℂ) ρ \ {((a i : ℝ) : ℂ)}) :=
      hφd.mono fun z hz hzS => hsub hz.1 ⟨hzS, hz.2⟩
    have hball (r : ℝ) : MapsTo (starRingEnd ℂ) (Metric.ball ((a i : ℝ) : ℂ) r)
        (Metric.ball ((a i : ℝ) : ℂ) r) := fun z hz => by
      rw [Metric.mem_ball, ← Complex.conj_ofReal, Complex.dist_conj_conj]
      exact hz
    rcases hvertex i with ⟨hei, r, hr, b, hb, hcont, hinj, hsector, hrays⟩ |
      ⟨hei, r, hr, c, b, hb, g, hgf, hg0, hgc, hgi, hsector, hrays⟩ |
      ⟨hei, r, hr, c, b, hb, g, hgf, hg0, hgc, hgr, hgu, hgi⟩
    · have hcast : ((e i : ℝ) : ℂ) = ((e i + 1 : ℝ) : ℂ) - 1 := by push_cast; ring
      rw [hcast]
      exact tendsto_sub_mul_nhdsNE_of_sector (φ := φ) (f := f) (x := a i) (r := ρ)
        (β := e i + 1) (Ω := Metric.ball ((a i : ℝ) : ℂ) r) (b := b) hρ hφρ
        (fun z _ => hφconj z) (hφf.mono inter_subset_left)
        ⟨by linarith [hei.1], by linarith [hei.2]⟩ hb Metric.isOpen_ball (hball r)
        (Metric.mem_ball_self hr) hcont (hf.mono inter_subset_right) hinj hsector hrays
    · have hcast : ((e i : ℝ) : ℂ) = -((-e i - 1 : ℝ) : ℂ) - 1 := by push_cast; ring
      rw [hcast]
      exact tendsto_sub_mul_nhdsNE_of_eqOn_div (x := a i) (β := -e i - 1) hρ hφρ
        (fun z _ => hφconj z) (hφf.mono inter_subset_left)
        ⟨by linarith [hei.2], by linarith [hei.1]⟩ hb Metric.isOpen_ball (hball r)
        (Metric.mem_ball_self hr) (hf.mono inter_subset_right) hgf hg0 hgc hgi hsector hrays
    · rw [hei, ofReal_neg, ofReal_one]
      exact tendsto_sub_mul_nhdsNE_of_eqOn_exp (x := a i) hρ hφρ (fun z _ => hφconj z)
        (hφf.mono inter_subset_left) hb Metric.isOpen_ball (hball r) (Metric.mem_ball_self hr)
        (hf.mono inter_subset_right) hgf hg0 hgc hgr hgu hgi
  -- The finite limit of `z * f'' / f'` at infinity makes it decay there.
  have hdecay : Tendsto φ (cobounded ℂ) (𝓝 0) := by
    refine tendsto_zero_cobounded_of_tendsto_mul_upperHalfPlaneSet hinfty ?_
      (Eventually.of_forall hφconj) hφf
    filter_upwards [isBounded_def.mp hfin.isBounded] with z hz _
    exact ((hφd z hz).differentiableAt (hfin.isClosed.isOpen_compl.mem_nhds hz)).continuousAt
  -- Partial fractions and integration then recover `f` itself.
  exact eqOn_const_mul_schwarzChristoffelPrimitive_add_of_tendsto a e ha z₀ hf hfn hφd hφf hpole
    hdecay

end TauCeti

end
