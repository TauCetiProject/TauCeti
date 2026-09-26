/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Prevertex

-- Non-public: the boundary-arc continuation of the pre-Schwarzian derivative and its decay in the
-- coordinate at infinity are used only in the proof.
import TauCeti.Analysis.Complex.Conformal.Reflection.Infinity
import TauCeti.Analysis.Complex.Conformal.Reflection.LogDeriv

/-!
# The Schwarz--Christoffel formula from local polygonal boundary data

A locally conformal map `f` of the upper half-plane satisfying the prescribed straight-side,
corner-sector, and infinity boundary conditions is completely determined, up to an affine map of
the target, by the real **prevertices** `a i` and the **turning exponents** `e i`: it is
`A * F + B`, where `F` is the normalized Schwarz--Christoffel primitive for `a` and `e`.

The three pieces of boundary data are the three ways a real point can sit against the polygon.

* Away from the prevertices, `f` extends continuously and injectively to the real axis with
  boundary values on an affine line, the nearby upper half-plane lying strictly to one side of it;
  that is, the boundary interval is carried into a side.
* At the prevertex `a i` the image `f - f (a i)`, rotated and scaled by some `b ≠ 0`, lies inside
  the sector of opening `(e i + 1) * π` and has boundary values on its two rays; that is, the two
  sides meeting at the vertex `f (a i)` make the interior angle `(e i + 1) * π`.  The exponent
  condition `e i ∈ Ioo (-1) 1` says that angle lies strictly between `0` and `2 * π`, so both
  convex and reentrant vertices are allowed.
* The point at infinity lies inside a side: in the coordinate `w ↦ -1 / w` at infinity, and after
  normalizing the target so that the side is the real axis with the polygon above it, `f` extends
  continuously and injectively across `0`.

These are local polygonal boundary conditions; they do not assert global injectivity or
surjectivity onto a polygon.  Under these conditions, the proof runs the classical argument: the
pre-Schwarzian derivative `f'' / f'` continues by Schwarz reflection across every boundary side to
a conjugation-symmetric function holomorphic off the prevertices, a straightened corner gives it
the residue `e i` at `a i`, the side through infinity makes it decay there, so partial fractions
identify it with `∑ i, e i / (z - a i)`, and integrating that differential equation recovers `f`.

## Main result

* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` -- a locally
  conformal map of the upper half-plane satisfying the prescribed local side, corner, and infinity
  conditions is an affine image of the Schwarz--Christoffel primitive for `a` and `e`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

/-- **The Schwarz--Christoffel formula.**  Let `f` be holomorphic with nonvanishing derivative on
the upper half-plane.  Assume that away from the distinct real prevertices `a i` its boundary
values run along affine lines with the upper half-plane on one side, that at `a i` it opens the
sector of angle `(e i + 1) * π` with boundary values on the two bounding rays, and that in the
coordinate at infinity it likewise extends across a straight side.  Then throughout the upper
half-plane

`f z = (f'(z₀) / integrand(z₀)) * F z + f z₀`,

where `F` is the normalized Schwarz--Christoffel primitive for the data `a` and `e`.  So `f` is an
affine image of `F`, and the two constants are read off from the value and derivative of `f` at
the normalization point `z₀`. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hside : ∀ x : ℝ, (∀ i, a i ≠ x) → ∃ r > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Metric.ball (x : ℂ) r, z.im = 0 → ((f z - q) / b).im = 0) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → 0 < ((f z - q) / b).im)
    (hcorner : ∀ i, ∃ r > 0, ∃ b : ℂ, b ≠ 0 ∧
      ContinuousOn f (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn f (Metric.ball ((a i : ℝ) : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Metric.ball ((a i : ℝ) : ℂ) r, 0 < z.im →
        |((f z - f (a i : ℂ)) / b).arg| < (e i + 1) * Real.pi / 2) ∧
      ∀ z ∈ Metric.ball ((a i : ℝ) : ℂ) r, z.im = 0 → f z ≠ f (a i : ℂ) →
        |((f z - f (a i : ℂ)) / b).arg| = (e i + 1) * Real.pi / 2)
    (hinfty : ∃ r > 0, ∃ g : ℂ → ℂ, ∃ q b : ℂ, b ≠ 0 ∧
      EqOn g (fun w => (f (-w⁻¹) - q) / b) (Metric.ball 0 r ∩ upperHalfPlaneSet) ∧
      ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0) ∧
      MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet ∧
      InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im})) :
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
  -- A straightened corner gives it the residue `e i` at the prevertex `a i`.
  have hpole : ∀ i, Tendsto (fun z => (z - ((a i : ℝ) : ℂ)) * φ z)
      (𝓝[≠] ((a i : ℝ) : ℂ)) (𝓝 ((e i : ℝ) : ℂ)) := by
    intro i
    obtain ⟨r, hr, b, hb, hcont, hinj, hsector, hrays⟩ := hcorner i
    have hdiff : ((range fun j => ((a j : ℝ) : ℂ)) \ {((a i : ℝ) : ℂ)}).Finite := hfin.sdiff
    obtain ⟨ρ, hρ, hsub⟩ :=
      Metric.isOpen_iff.mp hdiff.isClosed.isOpen_compl ((a i : ℝ) : ℂ) (by simp)
    have hball : MapsTo (starRingEnd ℂ) (Metric.ball ((a i : ℝ) : ℂ) r)
        (Metric.ball ((a i : ℝ) : ℂ) r) := fun z hz => by
      rw [Metric.mem_ball, ← Complex.conj_ofReal, Complex.dist_conj_conj]
      exact hz
    have hcast : ((e i : ℝ) : ℂ) = ((e i + 1 : ℝ) : ℂ) - 1 := by push_cast; ring
    rw [hcast]
    exact tendsto_sub_mul_nhdsNE_of_sector (φ := φ) (f := f) (x := a i) (r := ρ)
      (β := e i + 1) (Ω := Metric.ball ((a i : ℝ) : ℂ) r) (b := b) hρ
      (hφd.mono fun z hz hzS => hsub hz.1 ⟨hzS, hz.2⟩) (fun z _ => hφconj z)
      (hφf.mono inter_subset_left) ⟨by linarith [(he i).1], by linarith [(he i).2]⟩ hb
      Metric.isOpen_ball hball (Metric.mem_ball_self hr) hcont (hf.mono inter_subset_right) hinj
      hsector hrays
  -- The side through infinity makes it decay there.
  have hdecay : Tendsto φ (cobounded ℂ) (𝓝 0) := by
    obtain ⟨r, hr, g, q, b, hb, hgf, hgcont, hgreal, hgupper, hginj⟩ := hinfty
    have hgholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet) := by
      refine DifferentiableOn.congr ?_ fun w hw => hgf hw
      · intro w hw
        have hw0 : w ≠ 0 := fun h => by simp [h] at hw
        have hnegInv : -w⁻¹ ∈ upperHalfPlaneSet := by
          simp only [upperHalfPlaneSet, mem_ofPred_eq]
          simp only [neg_im, inv_im, neg_div, neg_neg]
          exact div_pos hw.2 (Complex.normSq_pos.mpr hw0)
        exact (((hf (-w⁻¹) hnegInv).differentiableAt
          (isOpen_upperHalfPlaneSet.mem_nhds hnegInv)).comp w
            (differentiableAt_inv hw0).neg).sub_const q |>.div_const b |>.differentiableWithinAt
    refine tendsto_zero_cobounded_of_eqOn_logDeriv_deriv hr hb hgf hgcont hgholo hgreal hgupper
      hginj ?_ (Eventually.of_forall hφconj) hφf
    filter_upwards [isBounded_def.mp hfin.isBounded] with z hz _
    exact ((hφd z hz).differentiableAt (hfin.isClosed.isOpen_compl.mem_nhds hz)).continuousAt
  -- Partial fractions and integration then recover `f` itself.
  exact eqOn_const_mul_schwarzChristoffelPrimitive_add_of_tendsto a e ha z₀ hf hfn hφd hφf hpole
    hdecay

end TauCeti

end
