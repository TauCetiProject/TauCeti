/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The energy identity on the truncated pair of pants

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` built from
period-one Hamiltonians `H_q` on the three ends of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`,
with values in a manifold `M` with a nondegenerate two-form `ω`, such as a closed symplectic
manifold, and let `u : S → M` be a `C¹` map. This file integrates the energy identity
`ω(du - X_K) = u^*ω + d(K(u)) - R_K(u)` over the truncation `S_R` of `S`
(`TauCeti.ThricePuncturedSphere.truncation`), where every `±s ≤ R`, and then over all of `S`.

The truncation is the disjoint union of its core, where every `±s < 1` and `K` vanishes, and of
the three end pieces `1 ≤ ±s ≤ R`. On each end piece the rectangle identity
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` applies in cylinder
coordinates, where `K = β(±s - 1) H_q(t) dt`; the change of variables
`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image` moves it to `S`. The `ds` component
vanishes, so only the circles `±s = 1` and `±s = R` contribute boundary terms, and the cutoff `β`
vanishes on the first. For `R ≥ 1`, if the energy density and the curvature are integrable over
`S_R`, this gives

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`).
With the curvature bound
`TauCeti.SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le`, the
energy over `S_R` differs from the area plus the Hamiltonian boundary terms by at most
`B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`, uniformly in `R`.

Letting `R → ∞` gives the energy identity on the whole pair of pants. Suppose that the end loops
`t ↦ u(φ_q(±R + i t))` converge pointwise to loops `x_q` as `R → ∞`, that the Hamiltonians are
bounded, and that the energy density and the area density of `u` are integrable over `S`. Then the
curvature is integrable over `S`
(`SmoothTwoForm.IsNondegenerate.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`): it
is the difference of the area density plus the continuous exterior derivative `d(K(u))` and the
energy density, hence measurable, and its absolute integral is at most `B₀ + B₁ + B_∞`. The
truncations exhaust `S`, and dominated convergence on the boundary circles gives

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`). The
middle term is the boundary integral `∫_∂ K(u)` at the asymptotic orbits. For a solution of the
Floer equation with tamed almost complex structures the energy is nonnegative, so the topological
part `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` is at least `-(B₀ + B₁ + B_∞)`
(`SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap`). Once the area
is expressed through the actions of capped orbits and the product class, this is the lower bound
on the valuation of the output monomials of the pair-of-pants product.

Neither closedness of `ω` nor caps are used: the identities are stated with the area `∫ u^*ω`
of the map itself. For a symplectic vector space target the energy and curvature densities are
continuous, so their integrability over the truncations is automatic
(`TauCeti.SymplecticForm.integrableOn_truncation_pairOfPantsPerturbation`); the vector-space
statements, the constant-form case of those here, are in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action`.

## Main results

* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`:
  the energy identity on the truncated pair of pants, for a manifold target.
* `IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le`:
  the resulting energy bound, uniform in the truncation, in the namespace `SmoothTwoForm`.
* `SmoothTwoForm.IsNondegenerate.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the
  curvature is integrable over `S`.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`: the energy
  identity on the whole pair of pants, for a map with asymptotic loops at the ends.
* `SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le`:
  the resulting energy bound.
* `SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap`: the lower
  bound on the topological energy of a Floer solution.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations on punctured surfaces.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends and their energy.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace Floer

/-! ### The decomposition of the truncation -/

/-- The piece `1 ≤ ±s ≤ R` of the end `q` in its cylinder coordinates, with the angular coordinate
in one period `[-1/2, 1/2)`. -/
private noncomputable def endPiece (q : Puncture) (R : ℝ) : Set (ℝ × ℝ) :=
  {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico (-1 / 2) (1 / 2)

/-- The end pieces lie in the truncation. -/
private theorem image_endPiece_subset (q : Puncture) {R : ℝ} (hR : 1 ≤ R) :
    endChart q '' endPiece q R ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (1 ≤ q.endSign * z.1 ∧ q.endSign * z.1 ≤ R) ∧ z.2 ∈ Ico (-1 / 2 : ℝ) (1 / 2) := hz
  have hz₀ : 0 < q.endSign * z.1 := by linarith [hz'.1.1]
  have hS := mem_thricePuncturedSphereReal_iff.1 (endChart_mem_thricePuncturedSphereReal hz₀)
  refine mem_truncation.2 ⟨hS.1, hS.2, fun r => ?_⟩
  by_cases hr : q = r
  · subst hr
    rw [re_endCoord_endChart]
    exact hz'.1.2
  · have h := endSign_mul_re_endCoord_nonpos hr (w := Complex.equivRealProdCLM.symm (endChart q z))
      (by rwa [re_endCoord_endChart])
    linarith

/-- A point of the truncation on the part `±s ≥ 1` of the end `q` lies in its end piece. -/
private theorem mem_image_endPiece {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R) {q : Puncture}
    (hq : 1 ≤ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ endChart q '' endPiece q R := by
  obtain ⟨hz₀, hz₁, hzR⟩ := mem_truncation.1 hz
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    (⟨⟨by simpa using hq, by simpa using hzR q⟩, by simpa using q.im_endCoord_mem_Ico _⟩ :
      _ ∧ _), ?_⟩
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter ⟨hz₀, hz₁⟩ q),
    ContinuousLinearEquiv.apply_symm_apply]

/-- The end pieces of distinct ends are disjoint. -/
private theorem disjoint_image_endPiece {R : ℝ} {q r : Puncture} (hqr : q ≠ r) :
    Disjoint (endChart q '' endPiece q R) (endChart r '' endPiece r R) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have ha' : 1 ≤ q.endSign * a.1 := ha.1.1
  have hb' : 1 ≤ r.endSign * b.1 := hb.1.1
  have h := congrArg Complex.equivRealProdCLM.symm hab
  rw [equivRealProdCLM_symm_endChart, equivRealProdCLM_symm_endChart] at h
  exact cylindricalEndLift_ne_cylindricalEndLift hqr (z := Complex.equivRealProdCLM.symm a)
    (z' := Complex.equivRealProdCLM.symm b) (by simp; linarith) (by simp; linarith) h.symm

/-- The image of an end piece in `S` is measurable. -/
private theorem measurableSet_image_endPiece (q : Puncture) (R : ℝ) :
    MeasurableSet (endChart q '' endPiece q R) :=
  measurable_image_of_fderivWithin
    ((measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
      (measurableSet_le (measurable_const.mul measurable_id) measurable_const) |>.prod
      measurableSet_Ico)
    (fun w _ => (hasFDerivAt_endChart q w).hasFDerivWithinAt)
    ((injOn_endChart q).mono fun z hz => by
      have h : 1 ≤ q.endSign * z.1 := hz.1.1
      exact mem_endStrip_iff.2 ⟨by linarith, hz.2⟩)

/-- **The boundary circle of an end piece.** By periodicity, the integral of the end Hamiltonian
over the circle `±s = R` may be taken over `[0, 1]` instead of `[-1/2, 1/2]`. -/
private theorem intervalIntegral_endChart_boundary_eq {X : Type*} {H : Puncture → ℝ → X → ℝ}
    (hH : ∀ q, Periodic (H q) 1) {u : ℝ × ℝ → X} {R : ℝ} (q : Puncture) :
    ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t))) =
      ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
  have hper : Periodic (fun t : ℝ => H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) 1 := fun t => by
    simp only [q.periodic_cylindricalEndLift (q.endSign * R) t, hH q t]
  have h := Function.Periodic.intervalIntegral_add_eq hper (-1 / 2) 0
  norm_num at h
  simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
  convert h using 1 <;> norm_num

/-- The truncations of `S`, in real coordinates, increase with the cutoff. -/
private theorem monotone_preimage_truncation :
    Monotone fun R : ℝ => Complex.equivRealProdCLM.symm ⁻¹' truncation R :=
  fun _ _ h => preimage_mono (truncation_mono h)

/-- The truncations of `S`, in real coordinates, exhaust `S`. -/
private theorem iUnion_preimage_truncation :
    ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' truncation R = thricePuncturedSphereReal := by
  rw [← preimage_iUnion, iUnion_truncation]
  rfl

/-- The truncations of `S`, in real coordinates, are measurable. -/
private theorem measurableSet_preimage_truncation (R : ℝ) :
    MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
  (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_truncation R)).isClosed.measurableSet

/-- The truncations of `S`, in real coordinates, lie in `S`. -/
private theorem preimage_truncation_subset (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ thricePuncturedSphereReal := fun _ hz =>
  mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩

/-- Integrals over `S` are the limits of the integrals over its truncations. -/
private theorem tendsto_setIntegral_truncation {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f thricePuncturedSphereReal) :
    Tendsto (fun R : ℝ => ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z) atTop
      (𝓝 (∫ z in thricePuncturedSphereReal, f z)) := by
  rw [← iUnion_preimage_truncation] at hf ⊢
  exact tendsto_setIntegral_of_monotone measurableSet_preimage_truncation
    monotone_preimage_truncation hf

/-- If the loops of `u` along the circles `±s = R` of the end `q` converge pointwise to a loop `x`
as `R → ∞`, then the integrals of a bounded continuous Hamiltonian along them converge to its
integral along `x`. -/
private theorem tendsto_intervalIntegral_endLoop {X : Type*} [TopologicalSpace X]
    {H : Puncture → ℝ → X → ℝ} (hHc : ∀ q, Continuous (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → X}
    (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture} {x : ℝ → X}
    (hx : ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x t))) :
    Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H q t (x t))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B q) ?_
    (Eventually.of_forall fun R ↦ ae_of_all _ fun t _ ↦ (Real.norm_eq_abs _).trans_le (hB q _ _))
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ ((hHc q).tendsto (t, x t)).comp
      (tendsto_const_nhds.prodMk_nhds (hx t)))
  -- For `R > 0` the circle `±s = R` lies in `S`, where `u` is continuous.
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hmem (t : ℝ) : Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)) ∈ thricePuncturedSphereReal := by
    rw [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_apply]
    refine cylindricalEndLift_ne_zero_and_ne_one q ?_
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> simp [h, hR]
  have hloop : Continuous fun t : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))) :=
    hu.comp_continuous (Complex.equivRealProdCLM.continuous.comp
      ((q.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))) hmem
  exact ((hHc q).comp (continuous_id.prodMk hloop)).aestronglyMeasurable

/-- The cutoff `β(R - 1)` of the boundary terms tends to `1`. -/
private theorem tendsto_smoothTransition_sub_one :
    Tendsto (fun R : ℝ ↦ smoothTransition (R - 1)) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_ge_atTop 2] with R hR
    exact (smoothTransition.one_of_one_le (by linarith)).symm

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ}

/-- The components of the perturbation are differentiable in the domain point, at points of `S`. -/
private theorem differentiableAt_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z :=
  (((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).comp (f := fun z' ↦ (z', x)) z
    (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt one_ne_zero).differentiableAt

/-- The components of the perturbation are differentiable in the point of the manifold, at points
of `S`. -/
private theorem mdifferentiableAt_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).comp (f := fun y ↦ (z, y)) x
    (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero

/-- If a density `f` is integrable over the image under the end chart of a rectangle
`[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`, then its pullback `g`, the density
at the image point times the Jacobian of the end chart, is integrable over the closed rectangle. -/
private theorem integrableOn_endChart_rect {q : Puncture} {a₁ b₁ : ℝ}
    (hpos : ∀ s ∈ Icc a₁ b₁, 1 / 2 < q.endSign * s) {f g : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2))))
    (hg : ∀ w ∈ Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
      g w = (fderiv ℝ (endChart q) w).det * f (endChart q w)) :
    IntegrableOn g (Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2)) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hinj : InjOn (endChart q) s :=
    (injOn_endChart q).mono fun z hz => mem_endStrip_iff.2 ⟨hpos _ hz.1, hz.2⟩
  have hae : s =ᵐ[volume] Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  refine IntegrableOn.congr_set_ae ?_ hae.symm
  refine ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas
    (fun w _ => (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt) hinj
    f).1 hf).congr_fun (fun w hw => ?_) hmeas
  dsimp only
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q w), smul_eq_mul, hg w hw]

/-- The exterior derivative `d(K(u))` of the pulled-back perturbation is continuous on `S`. -/
private theorem continuousOn_exteriorDerivative (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) :
    ContinuousOn (fun z ↦
      fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w)
          Complex.I) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) 1)
          z stdComplexLineImag) thricePuncturedSphereReal := by
  have hc (v : ℂ) : ContinuousOn (fderiv ℝ (fun w ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v))
      thricePuncturedSphereReal := by
    have hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
        (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
        (thricePuncturedSphereReal ×ˢ univ) := fun p hp ↦
      (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hp.1 p.2 v).contMDiffWithinAt
    exact (contMDiffOn_iff_contDiffOn.mp (hK.comp (contMDiffOn_id.prodMk hu)
      fun _ hz ↦ ⟨hz, mem_univ _⟩)).continuousOn_fderiv_of_isOpen
        isOpen_thricePuncturedSphereReal le_rfl
  exact ((hc Complex.I).clm_apply continuousOn_const).sub ((hc 1).clm_apply continuousOn_const)

end Floer

/-! ### The energy identity for a manifold target -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {H : Puncture → ℝ → M → ℝ} {ω : SmoothTwoForm I M} {u : ℝ × ℝ → M}

/-- The cylinder-coordinate half of the energy identity over a rectangle of an end, for a manifold
target: over the rectangle `[a₁, b₁] × [-1/2, 1/2]` of the part `±s > 1/2` of the end `q`, the
energy of `u ∘ φ_q` for the end components `β(±s - 1) H_q(t) dt` of the perturbation is its
symplectic area, plus the Hamiltonian boundary terms, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_endChart_rect (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (hpos' : ∀ s ∈ Icc a₁ b₁, 1 / 2 < q.endSign * s)
    (hE : IntegrableOn (ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q))
      (Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2)))
    (hR : IntegrableOn (fun w ↦ ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) w (u (endChart q w)))
      (Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2))) :
    ∫ w in Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2), ω.floerEnergyDensity
        (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q) w =
      (∫ w in Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2),
          (SmoothBundleForm.eval₂ ω ((u ∘ endChart q) w)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineImag) : ℝ)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ w in Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2), ω.hamiltonianCurvature
          (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I) w
          (u (endChart q w)) := by
  set U : Set (ℝ × ℝ) := {z | 1 / 2 < q.endSign * z.1}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz => hpos' _ (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  have hpos {z : ℝ × ℝ} (hz : z ∈ U) : 0 < q.endSign * z.1 := by
    have h : 1 / 2 < q.endSign * z.1 := hz
    linarith
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn fun w hw =>
      endChart_mem_thricePuncturedSphereReal (hpos hw)
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`, a `C¹` datum on `U`.
  have hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry (pairOfPantsEndComponent H q 1)) (U ×ˢ univ) :=
    (contMDiffOn_const (c := (0 : ℝ))).congr fun p hp =>
      pairOfPantsEndComponent_one_of_pos (hH q) (hpos hp.1) p.2
  have hβH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 fun p : (ℝ × ℝ) × M =>
      smoothTransition (q.endSign * p.1.1 - 1) • H q p.1.2 p.2 :=
    ((smoothTransition.contDiff.comp (f := fun s : ℝ × ℝ => q.endSign * s.1 - 1)
      (by fun_prop)).contMDiff.comp contMDiff_fst).smul
      ((hHs q).comp (((contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contMDiff.comp
        contMDiff_fst).prodMk contMDiff_snd))
  have hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry (pairOfPantsEndComponent H q Complex.I)) (U ×ˢ univ) :=
    hβH.contMDiffOn.congr fun p hp => by
      rw [smul_eq_mul]
      exact pairOfPantsEndComponent_I_of_pos (hH q) (hpos hp.1) p.2
  rw [hω.integral_floerEnergyDensity hUo hu' hKs hKt (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩) hIccU
    hE hR]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c) ((u ∘ endChart q) (s, c)) =
      0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hH q) (hpos (z := (s, c)) (hpos' s hs)) _
  have ht {c : ℝ} (hc : c ∈ Icc a₁ b₁) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2,
          pairOfPantsEndComponent H q Complex.I (c, t) ((u ∘ endChart q) (c, t)) =
        ∫ t in (-1 / 2 : ℝ)..1 / 2,
          smoothTransition (q.endSign * c - 1) * H q t (u (endChart q (c, t))) :=
    intervalIntegral.integral_congr fun t _ =>
      pairOfPantsEndComponent_I_of_pos (hH q) (hpos (z := (c, t)) (hpos' c hc)) _
  rw [hs₀, hs₀, ht (c := a₁) ⟨le_rfl, hab⟩, ht (c := b₁) ⟨hab, le_rfl⟩]
  simp only [Function.comp_apply]
  ring

/-- **The energy identity over a rectangle of an end, for a manifold target.** Over the image in
`S` of a rectangle `[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`, the Floer energy
is the symplectic area, plus the integrals of the Hamiltonian term `β(±s - 1) H_q(t)` over the
outgoing boundary circle minus the incoming one, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endChart (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (ha : 1 / 2 < q.endSign * a₁)
    (hb : 1 / 2 < q.endSign * b₁)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2))))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)))) :
    ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  set U : Set (ℝ × ℝ) := {z | 1 / 2 < q.endSign * z.1}
  -- The rectangle lies in the part `±s > 1/2` of the end.
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : 1 / 2 < q.endSign * z.1 := by
    obtain ⟨h₁, h₂⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz => hU₁ (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  have hsU : s ⊆ U := fun z hz => hIccU (by
    rw [Icc_prod_eq]
    exact ⟨hz.1, Ico_subset_Icc_self hz.2⟩)
  have hpos {z : ℝ × ℝ} (hz : z ∈ U) : 0 < q.endSign * z.1 := by
    have h : 1 / 2 < q.endSign * z.1 := hz
    linarith
  have hpos' (s' : ℝ) (hs' : s' ∈ Icc a₁ b₁) : 1 / 2 < q.endSign * s' := hU₁ (z := (s', 0)) hs'
  have hS {z : ℝ × ℝ} (hz : z ∈ U) := endChart_mem_thricePuncturedSphereReal (hpos hz)
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hinj : InjOn (endChart q) s :=
    (injOn_endChart q).mono fun z hz => mem_endStrip_iff.2 ⟨hsU hz, hz.2⟩
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (endChart q) w :=
    (hasFDerivAt_endChart q w).differentiableAt
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q w) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))).mdifferentiableAt
      one_ne_zero
  have htgt {w : ℝ × ℝ} (hw : w ∈ U) (v : ℂ) :=
    mdifferentiableAt_target hH hHs (hS hw) (u (endChart q w)) v
  -- In the cylinder coordinates of the end the datum is `β(±s - 1) H_q(t) dt`.
  have hpull (v : ℝ × ℝ) := perturbationPullback_endChart (H := H) q v
  have hE' := integrableOn_endChart_rect hpos' hE (g := ω.floerEnergyDensity
      (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q))
    fun w hw => by
      have h := ω.floerEnergyDensity_perturbationPullback
        (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (hφ w) (hud (hsU hw))
        (htgt (hsU hw) 1) (htgt (hsU hw) Complex.I)
      rwa [hpull, hpull, equivRealProdCLM_symm_stdComplexLineReal,
        equivRealProdCLM_symm_stdComplexLineImag] at h
  have hR' := integrableOn_endChart_rect hpos' hR (g := fun w ↦ ω.hamiltonianCurvature
      (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I) w
      (u (endChart q w)))
    fun w hw => by
      have h := ω.hamiltonianCurvature_perturbationPullback (x := u (endChart q w))
        (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        ((contDiff_endChart q 2).contDiffAt)
        (differentiableAt_domain hH hHs (hS (hsU hw)) _ 1)
        (differentiableAt_domain hH hHs (hS (hsU hw)) _ Complex.I)
        (htgt (hsU hw) 1) (htgt (hsU hw) Complex.I)
      rwa [hpull, hpull, equivRealProdCLM_symm_stdComplexLineReal,
        equivRealProdCLM_symm_stdComplexLineImag] at h
  -- Change variables to the cylinder coordinates of the end, in each of the three integrals.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ => hφ w) (fun w _ => det_fderiv_endChart_nonneg q w)
    (fun w hw => hud (hsU hw)) (fun _ _ => mdifferentiableAt_const)
    (fun _ _ => mdifferentiableAt_const)
  have h₀ (v : ℝ × ℝ) : perturbationPullback (endChart q) (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ))
      (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simp only [h₀, floerEnergyDensity_zero] at harea
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ => hφ w)
      (fun w _ => det_fderiv_endChart_nonneg q w) (fun w hw => hud (hsU hw))
      (fun w hw => htgt (hsU hw) 1) (fun w hw => htgt (hsU hw) Complex.I),
    ω.integral_hamiltonianCurvature_image hmeas hinj
      (fun w _ => (contDiff_endChart q 2).contDiffAt)
      (fun w _ => det_fderiv_endChart_nonneg q w)
      (fun w hw => differentiableAt_domain hH hHs (hS (hsU hw)) _ 1)
      (fun w hw => differentiableAt_domain hH hHs (hS (hsU hw)) _ Complex.I)
      (fun w hw => htgt (hsU hw) 1) (fun w hw => htgt (hsU hw) Complex.I),
    hpull, hpull, equivRealProdCLM_symm_stdComplexLineReal,
    equivRealProdCLM_symm_stdComplexLineImag]
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : s =ᵐ[volume] Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  exact integral_floerEnergyDensity_endChart_rect hω hH hHs hu hab hpos' hE' hR'

/-- **The energy identity on an end piece, for a manifold target.** Over the end piece
`1 ≤ ±s ≤ R` of the end `q`, the Floer energy is the symplectic area, plus `±β(R - 1)` times the
integral of `H_q(t)` over the boundary circle `±s = R`, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endPiece (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R)
    (q : Puncture)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (endChart q '' endPiece q R))
    (hcurv : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (endChart q '' endPiece q R)) :
    ∫ z in endChart q '' endPiece q R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' endPiece q R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) *
          (q.endSign * ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t)))) -
        ∫ z in endChart q '' endPiece q R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · have hpiece : endPiece q R = Icc 1 R ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp [endPiece, h]
    rw [hpiece] at hE hcurv ⊢
    rw [integral_floerEnergyDensity_image_endChart hω hH hHs hu hR
      (by rw [h]; norm_num) (by rw [h]; linarith) hE hcurv]
    simp only [h, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  · have hpiece : endPiece q R = Icc (-R) (-1) ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp only [endPiece, h, mem_prod, mem_ofPred_eq, mem_Icc]
      constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
    rw [hpiece] at hE hcurv ⊢
    rw [integral_floerEnergyDensity_image_endChart hω hH hHs hu (by linarith)
      (by rw [h]; linarith) (by rw [h]; norm_num) hE hcurv]
    simp only [h, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul]
    ring

/-- The pointwise energy identity `E = u^*ω + d(K(u)) - R_K(u)` for the pair-of-pants
perturbation holds at every point of `S`. -/
private theorem floerEnergyDensity_eq_of_mem (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w)
            Complex.I) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) 1)
            z stdComplexLineImag) -
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) :=
  hω.floerEnergyDensity_eq
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt
      one_ne_zero)
    ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) 1).mdifferentiableAt
      one_ne_zero)
    ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) Complex.I).mdifferentiableAt
      one_ne_zero)

/-- On a compact part `T` of `S` over which the energy density and the curvature are integrable,
the symplectic area density is integrable too. -/
private theorem integrableOn_area (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {T : Set (ℝ × ℝ)}
    (hT : IsCompact T) (hTS : T ⊆ thricePuncturedSphereReal)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) T)
    (hcurv : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) T) :
    IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) T := by
  refine ((hE.sub (((continuousOn_exteriorDerivative hH hHs hu).mono hTS).integrableOn_compact
    hT)).add hcurv).congr_fun (fun z hz ↦ ?_) hT.measurableSet
  simp only [Pi.add_apply, Pi.sub_apply, floerEnergyDensity_eq_of_mem hω hH hHs hu (hTS hz)]
  ring

/-- **The energy identity on the truncated pair of pants, for a manifold target.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on a manifold `M` with a
nondegenerate two-form `ω`, attached to the three ends of `S = ℂ ∖ {0, 1}`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u`
be a map which is `C¹` on `S`. For `R ≥ 1`, if the energy density and the curvature `R_K(u)` are
integrable over the truncation `S_R` of `S`, then the Floer energy of `u` over `S_R` is its
symplectic area, plus `β(R - 1)` times the signed sum over the three ends of the integrals of
`H_q(t)` along the boundary circles `±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. Closedness of the two-form is not used. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R))
    (hcurv : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set A : Puncture → Set (ℝ × ℝ) := fun q => endChart q '' endPiece q R
  set C := T \ ⋃ q, A q
  have harea := integrableOn_area hω hH hHs hu
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R))
    (preimage_truncation_subset R) hE hcurv
  -- The truncation is the disjoint union of its core `C`, where every `±s < 1`, and the three
  -- end pieces.
  have hTm : MeasurableSet T := measurableSet_preimage_truncation R
  have hAm (q : Puncture) : MeasurableSet (A q) := measurableSet_image_endPiece q R
  have hAT (q : Puncture) : A q ⊆ T := image_endPiece_subset q hR
  have hAd : Pairwise (Disjoint on A) := fun q r hqr => disjoint_image_endPiece hqr
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ q, ∫ z in A q, f z := by
    have hTC : T = C ∪ ⋃ q, A q := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun q => hf.mono_set (hAT q)]
  -- On the core the perturbation vanishes nearby, so the energy is the area and the curvature
  -- vanishes.
  have hcore {z : ℝ × ℝ} (hz : z ∈ C) :
      ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
    intro q
    by_contra! h
    exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endPiece hz.1 h⟩)
  have hCm : MeasurableSet C := hTm.diff (MeasurableSet.iUnion hAm)
  have hCE : ∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in C, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by
    refine setIntegral_congr_fun hCm fun z hz => ?_
    have hK : pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) = fun _ => 0 :=
      funext (pairOfPantsPerturbation_eq_zero_of_forall_le fun q ↦ (hcore hz q).le)
    simp [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
      perturbedMFDeriv_apply_stdComplexLineImag, hK, hamiltonianVectorField_const]
  have hCR : ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz =>
      ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt (K := pairOfPantsPerturbation H)
        (fun w hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y)
        (preimage_truncation_subset R hz.1) (hcore hz) (u z)
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE, hCR,
    Finset.sum_congr rfl fun q _ => integral_floerEnergyDensity_image_endPiece hω hH hHs hu hR q
      (hE.mono_set (hAT q)) (hcurv.mono_set (hAT q)),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [intervalIntegral_endChart_boundary_eq hH]
  ring

/-- **The energy bound on the truncated pair of pants, for a manifold target.** Under the
hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`,
if the end Hamiltonians are bounded, `|H_q| ≤ B_q`, then the Floer energy over the truncation
`S_R` differs from the symplectic area plus the Hamiltonian boundary terms by at most
`B₀ + B₁ + B_∞`, uniformly in `R`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R))
    (hcurv : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs hu hR hE hcurv, hsub,
    abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-- **The curvature is integrable over the pair of pants, for a manifold target.** Let `u` be `C¹`
on `S`, with Floer energy density and symplectic area density integrable over `S`, for the
pair-of-pants perturbation of bounded period-one `C¹` Hamiltonians. Then the curvature `R_K(u)` is
integrable over `S`: it is the area density plus the continuous exterior derivative `d(K(u))`
minus the energy density, hence measurable, and its absolute integral is at most `B₀ + B₁ + B_∞`.
-/
theorem IsNondegenerate.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      thricePuncturedSphereReal := by
  have hSm := isOpen_thricePuncturedSphereReal.measurableSet
  refine ⟨?_, ?_⟩
  · refine ((hA.aestronglyMeasurable.add ((continuousOn_exteriorDerivative hH hHs hu
      ).aestronglyMeasurable hSm)).sub hE.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem hSm] with z hz
    simp only [Pi.add_apply, Pi.sub_apply, floerEnergyDensity_eq_of_mem hω hH hHs hu hz]
    ring
  · have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
    refine ((setLIntegral_le_lintegral _ _).trans
      (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u)).trans_lt ?_
    exact ENNReal.sum_lt_top.2 fun q _ ↦ ENNReal.ofReal_lt_top

/-- **The energy identity on the pair of pants, for a manifold target.** Let `K` be the
pair-of-pants perturbation of bounded period-one `C¹` Hamiltonians `H_q` on a manifold `M` with a
nondegenerate two-form `ω`, attached to the three ends of `S = ℂ ∖ {0, 1}`. Let `u` be a map which
is `C¹` on `S`, whose loops `t ↦ u(φ_q(±R + i t))` along the circles of the end `q` converge
pointwise to loops `x_q` as `R → ∞`, and whose Floer energy density and symplectic area density
are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. The middle term is the
boundary integral `∫_∂ K(u)` at the asymptotic orbits, and the curvature term is integrable
(`SmoothTwoForm.IsNondegenerate.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`).
Closedness of the two-form is not used. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hcurv := hω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation hH hHs hB hu hE hA
  -- Both sides are the limits as `R → ∞` of the two sides of the identity on the truncation
  -- `S_R`, where the cutoff `β(R - 1)` of the boundary terms equals `1` once `R ≥ 2`.
  have hrhs := ((tendsto_setIntegral_truncation hA).add (by
      simpa only [one_mul] using tendsto_smoothTransition_sub_one.mul
        (tendsto_finsetSum Finset.univ fun q _ ↦ (tendsto_intervalIntegral_endLoop
          (fun q ↦ (hHs q).continuous) hB hu.continuousOn (hx q)).const_mul q.endSign))).sub
    (tendsto_setIntegral_truncation hcurv)
  refine tendsto_nhds_unique (tendsto_setIntegral_truncation hE) (hrhs.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact (hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs hu hR
    (hE.mono_set (preimage_truncation_subset R))
    (hcurv.mono_set (preimage_truncation_subset R))).symm

/-- **The energy bound on the pair of pants, for a manifold target.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, the Floer
energy over `S` differs from its topological part, the symplectic area plus the Hamiltonian terms
at the asymptotic orbits, by at most `B₀ + B₁ + B_∞`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    |(∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation hH hHs hB hu hx hE hA, hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-- **The topological energy of a pair-of-pants solution is bounded below, for a manifold
target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` for almost complex
structures `J z` on the tangent spaces `T_(u z) M` tamed by `ω`, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`. Since its
energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic orbits is
at least `-(B₀ + B₁ + B_∞)`. -/
theorem IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    {J : (z : ℝ × ℝ) → AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -∑ q, B q ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1
    (hω.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le hH hHs hB hu hx hE hA)
  linarith [h.2]

end SmoothTwoForm

end TauCeti
