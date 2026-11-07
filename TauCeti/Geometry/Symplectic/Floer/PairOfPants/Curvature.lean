/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Curvature
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The integrated curvature and the energy identity of the pair-of-pants perturbation

The energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants turns a bound
`∫_S sup_X |R_K| ≤ C` on the curvature of the perturbation datum `K` into the lower bound on the
valuation of product coefficients and the upper bound on the energy of the curves they count.
This file computes such a constant `C` for the perturbation
`TauCeti.Floer.pairOfPantsPerturbation` built from period-one Hamiltonians `H_q` on the three ends
of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, and integrates the energy identity over the
truncations of `S`. The target is a manifold `M` with a nondegenerate two-form `ω`
(`TauCeti.SmoothTwoForm`), as for the closed symplectic manifolds of Hamiltonian Floer theory; the
Hamiltonian vector fields, the curvature and the energy density are the intrinsic ones of
`TauCeti.Geometry.Symplectic.Floer.Manifold`. The results for a symplectic vector space `V`, on
which the energy identity on the whole of `S` is then proved, are the special case of the constant
form `TauCeti.SymplecticForm.constSmooth`.

In the coordinates `(s, t)` of the end `q` the perturbation is `β(±s) H_q(t) dt` with the cutoff
`β(±s) = smoothTransition (±s - 1)`
(`TauCeti.Floer.pairOfPantsPerturbation_cylindricalEndLift_of_pos`), so its curvature there is the
continuation curvature `±β'(±s - 1) H_q(t)`
(`SmoothTwoForm.hamiltonianCurvature_pairOfPantsEndComponent`), and the perturbation vanishes
off the parts `±s > 1` of the ends. Since the curvature is a two-form
(`SmoothTwoForm.hamiltonianCurvature_perturbationPullback`), its absolute integral over
`S` is the sum over the three ends of the integrals of `β'(±s - 1) |H_q(t)|` over half-cylinders,
and the cutoff has total increase `∫ β' = 1`. Hence, if `|H_q| ≤ B_q`, then

`∫_S |R_K(z, u(z))| dz ≤ B₀ + B₁ + B_∞`

for every map `u : S → M`, measurable or not
(`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`). The curvature
is computed in the global coordinate `z = s + i t` of `S ⊆ ℂ`, in which the `ds` and `dt`
components of `K` are its values on the tangent vectors `1` and `i`.

The same decomposition of `S` into its core, where `K` vanishes, and the three ends integrates
the energy identity over the truncation `S_R` of `S`
(`TauCeti.ThricePuncturedSphere.truncation`), where every `±s ≤ R`. On each end the rectangle
identity `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` applies in cylinder
coordinates; the boundary terms along the angular sides cancel by periodicity, and those on the
circles `±s = 1` vanish with the cutoff. For a map `u` which is `C¹` on `S` and `R ≥ 1` this
gives

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`, and `u^*ω` the
symplectic area density `ω(∂_s u, ∂_t u)`. With the curvature bound, the energy over `S_R`
therefore differs from the area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`,
uniformly in `R`. The integrands are integrable over the compact set `S_R`: the area density is
continuous on `S`, the curvature is the continuous function `±β'(±s - 1) H_q(t, u)` in the
coordinates of each end and vanishes on the core, and the energy density is the sum of these and
the exterior derivative of `K(u)`.

For a vector space target, letting `R → ∞` gives the energy identity on the whole pair of pants.
Suppose that the loops
`t ↦ u(φ_q(±R + i t))` converge pointwise to loops `x_q` as `R → ∞`, and that the energy density
and the area density of `u` are integrable over `S`. The curvature is then integrable over `S`,
the truncations exhaust `S`, and dominated convergence on the boundary circles gives

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

the identity `E = ∫ u^*ω + ∫_∂ K(u) - ∫ R_K(u)` with the boundary term evaluated at the asymptotic
orbits. Hence the energy differs from this topological part by at most `B₀ + B₁ + B_∞`. For a
solution of the Floer equation with tamed almost complex structures the energy is nonnegative, so
the topological part is at least `-(B₀ + B₁ + B_∞)`. Once the area is expressed through the
actions of capped orbits and the product class, this becomes the lower bound on the valuation of
the output monomials of the pair-of-pants product.

## Main results

For a manifold target, and for a vector space target in the namespace `SymplecticForm`:

* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`: the
  integrated curvature of the pair-of-pants perturbation along any map is at most the sum of
  bounds for the three end Hamiltonians.
* `SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le`: hence the
  integral of the curvature over any set has absolute value at most the same sum.
* `SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt`: the curvature
  vanishes where the perturbation is cylindrical, beyond the collars `1 ≤ ±s ≤ 2` of the ends.
* `SmoothTwoForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`: the energy
  identity on the truncated pair of pants.
* `SmoothTwoForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le`: the
  resulting energy bound, uniform in the truncation.

For a vector space target only:

* `SymplecticForm.integrableOn_truncation_pairOfPantsPerturbation`: the energy density, the area
  density and the curvature term along a map `C¹` on `S` are integrable over every truncation.
* `SymplecticForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the curvature along a
  map continuous on `S` is integrable over `S`.
* `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`: the energy identity on the
  whole pair of pants, for a map with asymptotic loops at the ends.
* `SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le`: the resulting
  energy bound.
* `SymplecticForm.neg_sum_le_integral_add_sum_of_isComplexLinearMap`: the lower bound on the
  topological energy of a Floer solution.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends and their energy.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

/-! ### Decomposing the truncated pair of pants -/

namespace Floer

/-- The part `1 ≤ ±s ≤ R`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates: the
collar and the cylindrical part of the end inside the truncation `S_R`, over one period. -/
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
    (hH : ∀ q, Periodic (H q) 1) (u : ℝ × ℝ → X) (R : ℝ) (q : Puncture) :
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

/-- The truncation is the disjoint union of its core, where every `±s < 1`, and the three end
pieces, so integrals over it split accordingly. -/
private theorem setIntegral_truncation_eq_add_sum {R : ℝ} (hR : 1 ≤ R) {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R \
          ⋃ q, endChart q '' endPiece q R, f z) +
        ∑ q, ∫ z in endChart q '' endPiece q R, f z := by
  have hAT (q : Puncture) := image_endPiece_subset q hR
  conv_lhs => rw [(sdiff_union_of_subset (iUnion_subset hAT)).symm]
  rw [setIntegral_union disjoint_sdiff_left
    (MeasurableSet.iUnion fun q => measurableSet_image_endPiece q R)
    (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
    integral_iUnion_fintype (fun q => measurableSet_image_endPiece q R)
      (fun q r hqr => disjoint_image_endPiece hqr) fun q => hf.mono_set (hAT q)]

/-- On the core of the truncation, off the end pieces, every signed longitudinal coordinate is
less than `1`. -/
private theorem endSign_mul_re_endCoord_lt_one_of_mem_core {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R \
      ⋃ q, endChart q '' endPiece q R) (q : Puncture) :
    q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
  by_contra! h
  exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endPiece hz.1 h⟩)

/-- The truncation is compact, hence measurable. -/
private theorem isCompact_preimage_truncation (R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)

/-- The truncation lies in `S`. -/
private theorem preimage_truncation_subset (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ thricePuncturedSphereReal := fun _ hz =>
  mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩

end Floer

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ}

/-- The components of the perturbation in real coordinates are differentiable in the domain
point, at points of `S`, for `C¹` Hamiltonians on a manifold. -/
private theorem differentiableAt_pairOfPantsPerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ pairOfPantsPerturbation H w x)
      (Complex.equivRealProdCLM.symm z) :=
    (contMDiffAt_pairOfPantsPerturbation hH hHs
      ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (f := fun w : ℂ ↦ (w, x)) _
      (contMDiffAt_id.prodMk contMDiffAt_const)
  exact ((hK.contDiffAt.differentiableAt one_ne_zero).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

/-- The components of the perturbation are differentiable in the target point, at points
of `S`, for `C¹` Hamiltonians on a manifold. -/
private theorem mdifferentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  (((contMDiffAt_pairOfPantsPerturbation hH hHs
    ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp
      (f := fun y : M ↦ (Complex.equivRealProdCLM.symm z, y)) x
      (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply contMDiffAt_const).mdifferentiableAt
    one_ne_zero

/-- The components of the perturbation are `C¹` on `S × M`. -/
private theorem contMDiffOn_pairOfPantsPerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contMDiffWithinAt

variable [IsManifold I ⊤ M]

/-- **The curvature in the coordinates of an end.** On the end `q`, where `±s > 0`, the curvature
of the pulled-back perturbation `β(±s) H_q(t) dt` is `±β'(±s - 1) H_q(t)`. -/
private theorem hamiltonianCurvature_perturbationPullback_endChart (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {q : Puncture}
    {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) (x : M) :
    ω.hamiltonianCurvature
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) z x =
      q.endSign * deriv smoothTransition (q.endSign * z.1 - 1) * H q z.2 x := by
  have hHt : DifferentiableAt ℝ (fun t ↦ H q t x) z.2 :=
    (((hHs q).contMDiffAt.comp (f := fun t : ℝ ↦ (t, x)) z.2
      (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt).differentiableAt one_ne_zero
  rw [perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hz hHt]

/-- The curvature of the perturbation over the image of the strip of the end `q` is at most a
bound `B_q` for the Hamiltonian of that end: the cutoff `β(±s - 1)` has total increase one. -/
private theorem setLIntegral_image_endChart_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) (q : Puncture) :
    ∫⁻ z in endChart q '' endStrip q, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (B q) := by
  have hβ : ∫⁻ s, ‖deriv (fun σ ↦ smoothTransition (σ - 1)) (q.endSign * s)‖ₑ = 1 := by
    simp_rw [deriv_comp_sub_const, Real.enorm_eq_ofReal smoothTransition.monotone.deriv_nonneg]
    rw [smoothTransition.lintegral_ofReal_deriv_mul_sub _ q.endSign_ne_zero, abs_endSign, inv_one,
      ENNReal.ofReal_one]
  -- The datum is differentiable jointly, hence separately, in the domain and target points.
  have hK {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : M) :=
    (contMDiffAt_pairOfPantsPerturbation (n := 1) hH hHs ⟨w, hw⟩ x).mdifferentiableAt
      one_ne_zero
  have hdom {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : M) (v : ℂ) :
      DifferentiableAt ℝ (fun w' ↦ pairOfPantsPerturbation H w' x v) w :=
    ((hK hw x).comp (f := fun w' : ℂ ↦ (w', x)) w
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt.clm_apply
        (differentiableAt_const v)
  have htgt {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : M) (v : ℂ) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ pairOfPantsPerturbation H w y v) x :=
    ((hK hw x).comp (f := fun y : M ↦ (w, y)) x
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)).clm_apply mdifferentiableAt_const
  have hHt (x : M) : Differentiable ℝ fun t ↦ H q t x :=
    (((hHs q).comp (f := fun t : ℝ ↦ (t, x)) (contMDiff_id.prodMk contMDiff_const)).contDiff
      ).differentiable one_ne_zero
  refine (ω.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le
    (P := fun σ ↦ smoothTransition (σ - 1)) (fun w hw x v ↦ hdom hw x v)
    (fun w hw x v ↦ htgt hw x v)
    (fun z hz x v ↦ pairOfPantsPerturbation_cylindricalEndLift_of_pos (hH q) hz x v)
    (fun σ ↦ (smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.comp σ
      (differentiableAt_id.sub_const 1)) hHt (hB q) u).trans_eq ?_
  rw [hβ, one_mul]

/-- **The integrated curvature of the pair-of-pants perturbation, for a manifold target.** Let `K`
be the pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on a manifold `M` with a
two-form `ω`, attached to the three ends of `S = ℂ ∖ {0, 1}`, with `|H_q| ≤ B_q`, and write its
components in the global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)`. Then for every map `u` into `M`, the integral of `|R_K(z, u(z))|` over the
plane is at most `B₀ + B₁ + B_∞`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) :=
  (ω.lintegral_enorm_hamiltonianCurvature_le_sum_endStrip
    (fun _ hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y) u).trans
    (Finset.sum_le_sum fun q _ ↦ setLIntegral_image_endChart_le ω hH hHs hB u q)

/-- The integral of the curvature of the pair-of-pants perturbation along any map into a manifold,
over any set, has absolute value at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`. -/
theorem abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ q, B q := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun q _ => hB₀ q),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_sum_of_nonneg fun q _ => hB₀ q]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u))

/-- **The curvature vanishes on the cylindrical parts of the ends, for a manifold target.** At a
point of `S` where the signed longitudinal coordinate of some end is greater than `2`, the
perturbation is `H_q(t) dt` in the coordinates of that end, and its curvature vanishes. Together
with the vanishing of the perturbation on the core, this confines the curvature to the collars
`1 ≤ ±s ≤ 2` of the three ends, a compact part of `S`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    {q : Puncture} (hq : 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re)
    (x : M) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  obtain ⟨w, hw, rfl⟩ := mem_image_endChart hz (q := q) (by linarith)
  have hw₂ : 2 < q.endSign * w.1 := by rwa [re_endCoord_endChart] at hq
  -- In the coordinates of the end the curvature is `±β'(±s - 1) H_q(t)`, and `β' = 0` there.
  have key := ω.hamiltonianCurvature_perturbationPullback (φ := endChart q) (w := w)
    (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (x := x) ((contDiff_endChart q 2).contDiffAt)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz _ 1)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz _ Complex.I)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hz _ 1)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hz _ Complex.I)
  have hβ : deriv smoothTransition (q.endSign * w.1 - 1) = 0 :=
    smoothTransition.deriv_of_one_lt (by linarith)
  rw [hamiltonianCurvature_perturbationPullback_endChart ω hH hHs (by linarith) x, hβ, mul_zero,
    zero_mul] at key
  exact (mul_eq_zero.1 key.symm).resolve_left (det_fderiv_endChart_pos q w).ne'


/-- The symplectic area density of a map which is `C¹` on `S` is continuous on `S`: it is the
pullback `u^*ω` within the open set `S`, evaluated on the coordinate vectors. -/
private theorem continuousOn_symplecticArea (ω : SmoothTwoForm I M) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) :
    ContinuousOn (fun z ↦ SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) thricePuncturedSphereReal := by
  have hS := isOpen_thricePuncturedSphereReal
  have hpb := (ω.contMDiff.of_le (by simp)).contMDiffOn.mpullbackWithin_form (m := 0) hu
    (by simp) (mapsTo_univ _ _) hS.uniqueMDiffOn
  have hc : ContinuousOn _ thricePuncturedSphereReal := fun z hz ↦
    (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace (hpb z hz)).continuousWithinAt
  refine ((ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ
    ![stdComplexLineReal, stdComplexLineImag]).continuous.comp_continuousOn hc).congr
      fun z hz ↦ ?_
  have h := mpullback_apply_pair (I := 𝓘(ℝ, ℝ × ℝ)) (I' := I) u ω.1 z stdComplexLineReal
    stdComplexLineImag
  rw [← mpullbackWithin_eq_mpullback (hS.uniqueMDiffOn z hz)
    ((hu.contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt one_ne_zero)] at h
  rw [SmoothBundleForm.eval₂_apply]
  exact h.symm

/-- The curvature term along a map continuous on `S` is integrable over every truncation `S_R`
with `R ≥ 1`: it vanishes on the core, and in the coordinates of each end it is the continuous
function `±β'(±s - 1) H_q(t, u)`. -/
private theorem integrableOn_truncation_hamiltonianCurvature (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hAT (q : Puncture) := image_endPiece_subset q hR
  rw [← sdiff_union_of_subset (iUnion_subset hAT)]
  refine integrableOn_union.2 ⟨?_, integrableOn_finite_iUnion.2 fun q ↦ ?_⟩
  · -- On the core the perturbation vanishes, and so does its curvature.
    refine integrableOn_zero.congr_fun (fun z hz ↦ ?_)
      ((isCompact_preimage_truncation R).isClosed.measurableSet.diff
        (MeasurableSet.iUnion fun q ↦ measurableSet_image_endPiece q R))
    exact (ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt
      (fun w hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y)
      (preimage_truncation_subset R hz.1) (endSign_mul_re_endCoord_lt_one_of_mem_core hz) _).symm
  · -- Change variables to the coordinates of the end, where the curvature is continuous on the
    -- compact closure of the end piece.
    set K : Set (ℝ × ℝ) :=
      {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)
    have hpos {w : ℝ × ℝ} (hw : w ∈ K) : 0 < q.endSign * w.1 := by linarith [hw.1.1]
    have hK : IsCompact K := by
      refine IsCompact.prod ?_ isCompact_Icc
      exact (Homeomorph.mulLeft₀ q.endSign q.endSign_ne_zero).isCompact_preimage.2
        (isCompact_Icc (a := 1) (b := R))
    have hpK : endPiece q R ⊆ K := prod_mono subset_rfl Ico_subset_Icc_self
    have hmeas : MeasurableSet (endPiece q R) :=
      ((measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
        (measurableSet_le (measurable_const.mul measurable_id) measurable_const)).prod
        measurableSet_Ico
    have hinj : InjOn (endChart q) (endPiece q R) :=
      (injOn_endChart q).mono fun z hz ↦ by
        have h : 1 ≤ q.endSign * z.1 := hz.1.1
        exact mem_endStrip_iff.2 ⟨by linarith, hz.2⟩
    refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume) hmeas
      (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      hinj _).2 ?_
    have hcont : ContinuousOn (fun w : ℝ × ℝ ↦
        q.endSign * deriv smoothTransition (q.endSign * w.1 - 1) * H q w.2 (u (endChart q w)))
        K := by
      have hβ : Continuous (deriv smoothTransition) :=
        (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
      have hu' : ContinuousOn (fun w ↦ u (endChart q w)) K :=
        hu.comp (contDiff_endChart q 0).continuous.continuousOn fun w hw ↦
          endChart_mem_thricePuncturedSphereReal (hpos hw)
      exact (continuous_const.mul (hβ.comp (by fun_prop))).continuousOn.mul
        ((hHs q).continuous.comp_continuousOn (continuous_snd.continuousOn.prodMk hu'))
    refine ((hcont.integrableOn_compact hK).mono_set hpK).congr_fun (fun w hw ↦ ?_) hmeas
    have hS := endChart_mem_thricePuncturedSphereReal (hpos (hpK hw))
    rw [abs_of_nonneg (det_fderiv_endChart_nonneg q w), smul_eq_mul,
      ← ω.hamiltonianCurvature_perturbationPullback (contDiff_endChart q 2).contDiffAt
        (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS _ 1)
        (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS _ Complex.I)
        (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ 1)
        (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ Complex.I),
      hamiltonianCurvature_perturbationPullback_endChart ω hH hHs (hpos (hpK hw))]

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- The cylinder-coordinate half of the energy identity over a rectangle of an end: over the strip
`[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end coordinates, the pulled-back Floer
energy is the symplectic area, plus the Hamiltonian boundary terms, minus the integrated
curvature. -/
private theorem integral_floerEnergyDensity_endChart_rect (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (ha : 1 / 2 < q.endSign * a₁)
    (hb : 1 / 2 < q.endSign * b₁)
    (hE : IntegrableOn (ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q))
      (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)))
    (hR : IntegrableOn (fun w ↦ ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) w (u (endChart q w)))
      (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2))) :
    ∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
        ω.floerEnergyDensity (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I)
          (u ∘ endChart q) w =
      (∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
          SmoothBundleForm.eval₂ ω (u (endChart q w))
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineImag)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
          ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
            (pairOfPantsEndComponent H q Complex.I) w (u (endChart q w)) := by
  set U : Set (ℝ × ℝ) := {z | 1 / 2 < q.endSign * z.1}
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : z ∈ U := by
    obtain ⟨h₁, h₂⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;>
      simp only [U, mem_ofPred_eq, h] at ha hb ⊢ <;> linarith
  have hpos {z : ℝ × ℝ} (hz : z ∈ U) : 0 < q.endSign * z.1 := by
    have h : 1 / 2 < q.endSign * z.1 := hz
    linarith
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) =ᵐ[volume]
      Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`: apply the energy identity on
  -- the rectangle.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn fun w hw =>
      endChart_mem_thricePuncturedSphereReal (hpos hw)
  have hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry (pairOfPantsEndComponent H q 1)) (U ×ˢ univ) :=
    contMDiffOn_const.congr fun p hp => pairOfPantsEndComponent_one_of_pos (hH q) (hpos hp.1) p.2
  have hβH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 fun p : (ℝ × ℝ) × M =>
      smoothTransition (q.endSign * p.1.1 - 1) * H q p.1.2 p.2 :=
    ((smoothTransition.contDiff.comp (f := fun w : ℝ × ℝ => q.endSign * w.1 - 1)
      (by fun_prop)).contMDiff.comp contMDiff_fst).smul
      ((hHs q).comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))
  have hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry (pairOfPantsEndComponent H q Complex.I)) (U ×ˢ univ) :=
    hβH.contMDiffOn.congr fun p hp => pairOfPantsEndComponent_I_of_pos (hH q) (hpos hp.1) p.2
  have hrect := hω.integral_floerEnergyDensity
    (isOpen_lt continuous_const (continuous_const.mul continuous_fst)) hu' hKs hKt
    (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩)
    (fun z hz => hU₁ (by rw [Icc_prod_eq] at hz; exact hz.1))
    (hE.congr_set_ae hae.symm) (hR.congr_set_ae hae.symm)
  simp only [Function.comp_apply] at hrect
  rw [hrect]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c) (u (endChart q (s, c))) =
      0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hH q) (hpos (hU₁ (z := (s, c)) hs)) _
  have ht {c : ℝ} (hc : c ∈ Icc a₁ b₁) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2,
          pairOfPantsEndComponent H q Complex.I (c, t) (u (endChart q (c, t))) =
        ∫ t in (-1 / 2 : ℝ)..1 / 2,
          smoothTransition (q.endSign * c - 1) * H q t (u (endChart q (c, t))) :=
    intervalIntegral.integral_congr fun t _ =>
      pairOfPantsEndComponent_I_of_pos (hH q) (hpos (hU₁ (z := (c, t)) hc)) _
  rw [hs₀, hs₀, ht (c := a₁) ⟨le_rfl, hab⟩, ht (c := b₁) ⟨hab, le_rfl⟩]
  ring

/-- **The energy identity over a rectangle of an end.** Over the image in `S` of a rectangle
`[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`, the Floer energy is the
symplectic area, plus the integrals of the Hamiltonian term `β(±s - 1) H_q(t)` over the outgoing
boundary circle minus the incoming one, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endChart (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
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
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- The rectangle lies in the part `±s > 1/2` of the end, where the end chart is an injective
  -- orientation-preserving change of coordinates into `S`.
  have hsU {z : ℝ × ℝ} (hz : z ∈ s) : 1 / 2 < q.endSign * z.1 := by
    obtain ⟨⟨h₁, h₂⟩, -⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hS {z : ℝ × ℝ} (hz : z ∈ s) : endChart q z ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by linarith [hsU hz])
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hinj : InjOn (endChart q) s :=
    (injOn_endChart q).mono fun z hz => mem_endStrip_iff.2 ⟨hsU hz, hz.2⟩
  have hφ (w : ℝ × ℝ) : HasFDerivAt (endChart q) (fderiv ℝ (endChart q) w) w :=
    (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt
  have hud {w : ℝ × ℝ} (hw : w ∈ s) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q w) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))).mdifferentiableAt
      one_ne_zero
  have hKd (v : ℂ) {w : ℝ × ℝ} (hw : w ∈ s) :=
    differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS hw) (u (endChart q w)) v
  have hKm (v : ℂ) {w : ℝ × ℝ} (hw : w ∈ s) :=
    mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) (u (endChart q w)) v
  -- Change variables to the cylinder coordinates of the end, in each of the three integrals and
  -- in the two integrability hypotheses.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ => (hφ w).differentiableAt) (fun w _ => det_fderiv_endChart_nonneg q w)
    (fun w hw => hud hw) (fun _ _ => mdifferentiableAt_const) (fun _ _ => mdifferentiableAt_const)
  simp only [perturbationPullback_zero, floerEnergyDensity_zero, Function.comp_apply] at harea
  have hE' := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume) hmeas
    (fun w _ => (hφ w).hasFDerivWithinAt) hinj _).1 hE
  have hR' := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume) hmeas
    (fun w _ => (hφ w).hasFDerivWithinAt) hinj _).1 hR
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ => (hφ w).differentiableAt)
      (fun w _ => det_fderiv_endChart_nonneg q w) (fun w hw => hud hw) (fun w hw => hKm 1 hw)
      (fun w hw => hKm Complex.I hw),
    ω.integral_hamiltonianCurvature_image hmeas hinj
      (fun w _ => (contDiff_endChart q 2).contDiffAt) (fun w _ => det_fderiv_endChart_nonneg q w)
      (fun w hw => hKd 1 hw) (fun w hw => hKd Complex.I hw) (fun w hw => hKm 1 hw)
      (fun w hw => hKm Complex.I hw),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  refine integral_floerEnergyDensity_endChart_rect hω hH hHs hu hab ha hb
    (hE'.congr_fun (fun w hw => ?_) hmeas) (hR'.congr_fun (fun w hw => ?_) hmeas)
  · dsimp only
    rw [abs_of_nonneg (det_fderiv_endChart_nonneg q w), smul_eq_mul,
      ← ω.floerEnergyDensity_perturbationPullback (hφ w).differentiableAt (hud hw) (hKm 1 hw)
        (hKm Complex.I hw), perturbationPullback_endChart, perturbationPullback_endChart,
      equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  · dsimp only
    rw [abs_of_nonneg (det_fderiv_endChart_nonneg q w), smul_eq_mul,
      ← ω.hamiltonianCurvature_perturbationPullback (contDiff_endChart q 2).contDiffAt (hKd 1 hw)
        (hKd Complex.I hw) (hKm 1 hw) (hKm Complex.I hw), perturbationPullback_endChart,
      perturbationPullback_endChart, equivRealProdCLM_symm_stdComplexLineReal,
      equivRealProdCLM_symm_stdComplexLineImag]

/-- **The energy identity on an end piece.** Over the end piece `1 ≤ ±s ≤ R` of the end `q`, the
Floer energy is the symplectic area, plus `±β(R - 1)` times the integral of `H_q(t)` over the
boundary circle `±s = R`, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endPiece (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
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
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
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

/-- The Floer energy density of a map which is `C¹` on `S` is integrable over every truncation
`S_R` with `R ≥ 1`: by the pointwise energy identity it is the area density plus the exterior
derivative of `K(u)` minus the curvature term. -/
private theorem integrableOn_truncation_floerEnergyDensity (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  have hT := isCompact_preimage_truncation R
  have hTS := preimage_truncation_subset R
  -- The pulled-back components `K(u)` are `C¹` on `S`, so their derivatives are integrable over
  -- the compact truncation.
  have hd (v : ℂ) : ContDiffOn ℝ 1
      (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v)
      thricePuncturedSphereReal :=
    contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_pairOfPantsPerturbation hH hHs v).comp
      (contMDiffOn_id.prodMk hu) fun _ hz ↦ ⟨hz, mem_univ _⟩)
  have hcont (v : ℂ) (e : ℝ × ℝ) : ContinuousOn (fun z ↦ fderiv ℝ
      (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v) z e)
      thricePuncturedSphereReal :=
    ((hd v).continuousOn_fderiv_of_isOpen isOpen_thricePuncturedSphereReal le_rfl).clm_apply
      continuousOn_const
  have hderiv := (((hcont Complex.I stdComplexLineReal).sub
    (hcont 1 stdComplexLineImag)).mono hTS).integrableOn_compact (μ := volume) hT
  have harea := ((continuousOn_symplecticArea ω hu).mono hTS).integrableOn_compact (μ := volume) hT
  -- By the pointwise energy identity the energy density is `u^*ω + d(K(u)) - R_K(u)`.
  refine ((harea.add hderiv).sub (integrableOn_truncation_hamiltonianCurvature ω hH hHs
    hu.continuousOn hR)).congr_fun (fun z hz ↦ ?_) hT.isClosed.measurableSet
  have hzS := hTS hz
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [hω.floerEnergyDensity_eq
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hzS)).mdifferentiableAt
      one_ne_zero)
    ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hzS (u z) 1).mdifferentiableAt
      one_ne_zero)
    ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hzS (u z) Complex.I).mdifferentiableAt
      one_ne_zero)]

/-- **The energy identity on the truncated pair of pants.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
values in a manifold `M` carrying a nondegenerate two-form `ω`, and with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Let `u` be
a map into `M` which is `C¹` on `S`, and let `R ≥ 1`. Then over the truncation `S_R` of `S` the
Floer energy of `u` is its symplectic area, plus `β(R - 1)` times the signed sum over the three
ends of the integrals of `H_q(t)` along the boundary circles `±s = R`, minus the integrated
curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. Closedness of `ω` is not used. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hE := integrableOn_truncation_floerEnergyDensity hω hH hHs hu hR
  have hcurv := integrableOn_truncation_hamiltonianCurvature ω hH hHs hu.continuousOn hR
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set C := T \ ⋃ q, endChart q '' endPiece q R
  have hAT (q : Puncture) := image_endPiece_subset q hR
  have hCm : MeasurableSet C := (isCompact_preimage_truncation R).isClosed.measurableSet.diff
    (MeasurableSet.iUnion fun q => measurableSet_image_endPiece q R)
  -- On the core the perturbation vanishes, so the energy is the area and the curvature vanishes.
  have hK {z : ℝ × ℝ} (hz : z ∈ C) :
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) = fun _ => 0 :=
    funext (pairOfPantsPerturbation_eq_zero_of_forall_le fun q ↦
      (endSign_mul_re_endCoord_lt_one_of_mem_core hz q).le)
  have hCE : ∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in C, SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) :=
    setIntegral_congr_fun hCm fun z hz => by
      simp [floerEnergyDensity_def, hK hz, hamiltonianVectorField_const]
  have hCR : ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz =>
      ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt
        (fun w hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y)
        (preimage_truncation_subset R hz.1) (endSign_mul_re_endCoord_lt_one_of_mem_core hz) _
  rw [setIntegral_truncation_eq_add_sum hR hE,
    setIntegral_truncation_eq_add_sum hR
      (((continuousOn_symplecticArea ω hu).mono (preimage_truncation_subset R)).integrableOn_compact
        (μ := volume) (isCompact_preimage_truncation R)),
    setIntegral_truncation_eq_add_sum hR hcurv, hCE, hCR,
    Finset.sum_congr rfl fun q _ => integral_floerEnergyDensity_image_endPiece hω hH hHs hu hR q
      (hE.mono_set (hAT q)) (hcurv.mono_set (hAT q)),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [intervalIntegral_endChart_boundary_eq hH u R]
  ring

/-- **The energy bound on the truncated pair of pants.** If the end Hamiltonians are bounded,
`|H_q| ≤ B_q`, then for every `R ≥ 1` the Floer energy over the truncation `S_R` differs from the
symplectic area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R`.
-/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hω hH hHs hu hR, hsub,
    abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

end SmoothTwoForm

/-! ### Symplectic vector space targets -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}

/-- `C¹` Hamiltonians on a vector space are `C¹` maps of manifolds. -/
private theorem contMDiff_uncurry_of_contDiff
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (q : Puncture) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
  contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff

/-- The points of `S`, in real coordinates, form an open set. -/
private theorem isOpen_puncturedSphere :
    IsOpen {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} :=
  isOpen_thricePuncturedSphereReal

/-- The components of the perturbation in real coordinates are `C¹` jointly in the domain point
of `S` and the target point. -/
private theorem contDiffOn_pairOfPantsPerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (v : ℂ) :
    ContDiffOn ℝ 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contDiffWithinAt

variable [FiniteDimensional ℝ V]

/-- **The integrated curvature of the pair-of-pants perturbation.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
`|H_q| ≤ B_q`, and write its components in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map `u` into the target, the integral
of `|R_K(z, u(z))|` over the plane is at most `B₀ + B₁ + B_∞`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le hH
    (contMDiff_uncurry_of_contDiff hHs) hB u

/-- The integral of the curvature of the pair-of-pants perturbation along any map, over any set,
has absolute value at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`. -/
theorem abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → V) (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ q, B q := by
  simpa using ω.constSmooth.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le hH
    (contMDiff_uncurry_of_contDiff hHs) hB u s

/-- **The curvature vanishes on the cylindrical parts of the ends.** At a point of `S` where the
signed longitudinal coordinate of some end is greater than `2`, the perturbation is `H_q(t) dt` in
the coordinates of that end, and its curvature vanishes. This confines the curvature to the
collars `1 ≤ ±s ≤ 2` of the three ends, a compact part of `S`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    {q : Puncture} (hq : 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re)
    (x : V) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  simpa using ω.constSmooth.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH
    (contMDiff_uncurry_of_contDiff hHs) hz hq x
/-- The Floer energy density, the symplectic area density and the curvature of the pair-of-pants
perturbation, along a map that is `C¹` on `S`, are integrable over every truncation. -/
theorem integrableOn_truncation_pairOfPantsPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal) (R : ℝ) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  have hT := isCompact_preimage_truncation R
  have hTS := preimage_truncation_subset R
  have hKs := contDiffOn_pairOfPantsPerturbation hH hHs 1
  have hKt := contDiffOn_pairOfPantsPerturbation hH hHs Complex.I
  have hdu := hu.continuousOn_fderiv_of_isOpen isOpen_thricePuncturedSphereReal le_rfl
  refine ⟨?_, ?_, ?_⟩
  · exact ((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal hu hKs hKt).mono
      hTS).integrableOn_compact hT
  · exact ((ω.continuousOn_apply_comp (hdu.clm_apply continuousOn_const)
      (hdu.clm_apply continuousOn_const)).mono hTS).integrableOn_compact hT
  · exact ((ω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal
      hu.continuousOn hKs hKt).mono hTS).integrableOn_compact hT

/-- **The energy identity on the truncated pair of pants.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`,
and let `u` be a map which is `C¹` on `S`. For `R ≥ 1`, over the truncation `S_R` of `S` the Floer
energy of `u` is its symplectic area, plus `β(R - 1)` times the signed sum over the three ends of
the integrals of `H_q(t)` along the boundary circles `±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have h := ω.constSmooth.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (isNondegenerate_constSmooth ω) hH (contMDiff_uncurry_of_contDiff hHs)
    (contMDiffOn_iff_contDiffOn.2 hu) hR
  have harea (z : ℝ × ℝ) : SmoothBundleForm.eval₂ ω.constSmooth (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineImag) =
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
    rw [mfderiv_eq_fderiv]
    exact constSmooth_apply ω _ _ _
  simp only [harea, floerEnergyDensity_constSmooth, hamiltonianCurvature_constSmooth] at h
  exact h

/-- **The energy bound on the truncated pair of pants.** If the end Hamiltonians are bounded,
`|H_q| ≤ B_q`, then for every `R ≥ 1` the Floer energy over the truncation `S_R` differs from the
symplectic area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R`.
-/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation_truncation ω hH hHs hu hR, hsub,
    abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-! ### The energy identity on the whole pair of pants -/

/-- The truncations of `S`, in real coordinates, increase with the cutoff. -/
private theorem monotone_preimage_truncation :
    Monotone fun R : ℝ => Complex.equivRealProdCLM.symm ⁻¹' truncation R :=
  fun _ _ h => preimage_mono (truncation_mono h)

/-- The truncations of `S`, in real coordinates, exhaust `S`. -/
private theorem iUnion_preimage_truncation :
    ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' truncation R =
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1} := by
  rw [← preimage_iUnion, iUnion_truncation]
  rfl

/-- Integrals over `S` are the limits of the integrals over its truncations. -/
private theorem tendsto_setIntegral_truncation {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) :
    Tendsto (fun R : ℝ => ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z) atTop
      (𝓝 (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, f z)) := by
  rw [← iUnion_preimage_truncation] at hf ⊢
  exact tendsto_setIntegral_of_monotone (fun R =>
    (isCompact_preimage_truncation R).isClosed.measurableSet) monotone_preimage_truncation hf

/-- **The curvature is integrable over the pair of pants.** Along a map `u` which is continuous
on `S`, the curvature of the pair-of-pants perturbation of bounded period-one `C¹` Hamiltonians is
integrable over `S`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContinuousOn u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1} :=
  ⟨(ω.continuousOn_hamiltonianCurvature_comp isOpen_puncturedSphere hu
      (contDiffOn_pairOfPantsPerturbation hH hHs 1)
      (contDiffOn_pairOfPantsPerturbation hH hHs Complex.I)).aestronglyMeasurable
      isOpen_puncturedSphere.measurableSet,
    (setLIntegral_le_lintegral _ _).trans_lt
      ((lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u).trans_lt
        (ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top))⟩

omit [FiniteDimensional ℝ V] in
/-- If the loops of `u` along the circles `±s = R` of the end `q` converge pointwise to a loop `x`
as `R → ∞`, then the integrals of a bounded continuous Hamiltonian along them converge to its
integral along `x`. -/
private theorem tendsto_intervalIntegral_endLoop (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContinuousOn u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) {q : Puncture} {x : ℝ → V}
    (hx : ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x t))) :
    Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H q t (x t))) := by
  have hHc : Continuous (uncurry (H q)) := (hHs q).continuous
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B q) ?_
    (Eventually.of_forall fun R ↦ ae_of_all _ fun t _ ↦ (Real.norm_eq_abs _).trans_le (hB q _ _))
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ (hHc.tendsto (t, x t)).comp (tendsto_const_nhds.prodMk_nhds (hx t)))
  -- For `R > 0` the circle `±s = R` lies in `S`, where `u` is continuous.
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hmem (t : ℝ) : Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))) ≠ 0 ∧
      Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))) ≠ 1 := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    refine cylindricalEndLift_ne_zero_and_ne_one q ?_
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> simp [h, hR]
  have hloop : Continuous fun t : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))) :=
    hu.comp_continuous (Complex.equivRealProdCLM.continuous.comp
      ((q.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))) hmem
  exact (hHc.comp (continuous_id.prodMk hloop)).aestronglyMeasurable

/-- **The energy identity on the pair of pants.** Let `K` be the pair-of-pants perturbation of
bounded period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Let `u`
be a map which is `C¹` on `S`, whose loops `t ↦ u(φ_q(±R + i t))` along the circles of the end
`q` converge pointwise to loops `x_q` as `R → ∞`, and whose Floer energy density and symplectic
area density are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. The middle term is the
boundary integral `∫_∂ K(u)` at the asymptotic orbits, and the curvature term is integrable
(`integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`). -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    (hA : IntegrableOn
      (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1}) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1},
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- Both sides are the limits as `R → ∞` of the two sides of the identity on the truncation
  -- `S_R`, where the cutoff `β(R - 1)` of the boundary terms equals `1` once `R ≥ 2`.
  have hβ : Tendsto (fun R : ℝ ↦ smoothTransition (R - 1)) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [eventually_ge_atTop 2] with R hR
      exact (smoothTransition.one_of_one_le (by linarith)).symm
  have hrhs := ((tendsto_setIntegral_truncation hA).add (by
      simpa only [one_mul] using hβ.mul (tendsto_finsetSum Finset.univ fun q _ ↦
        (tendsto_intervalIntegral_endLoop hHs hB hu.continuousOn (hx q)).const_mul q.endSign))).sub
    (tendsto_setIntegral_truncation
      (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hB hu.continuousOn))
  refine tendsto_nhds_unique (tendsto_setIntegral_truncation hE) (hrhs.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact (integral_floerEnergyDensity_pairOfPantsPerturbation_truncation ω hH hHs hu hR).symm

/-- **The energy bound on the pair of pants.** Under the hypotheses of
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`, the Floer energy over `S`
differs from its topological part, the symplectic area plus the Hamiltonian terms at the
asymptotic orbits, by at most `B₀ + B₁ + B_∞`. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    (hA : IntegrableOn
      (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1}) :
    |(∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1},
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation ω hH hHs hB hu hx hE hA, hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-- **The topological energy of a pair-of-pants solution is bounded below.** Let `u` solve the
Floer equation `(du - X_K)^{0,1} = 0` on `S` for almost complex structures `J z` tamed by `ω`,
under the hypotheses of `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`.
Since its energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic
orbits is at least `-(B₀ + B₁ + B_∞)`. -/
theorem neg_sum_le_integral_add_sum_of_isComplexLinearMap (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    (hA : IntegrableOn
      (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    -∑ q, B q ≤
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1},
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) isOpen_puncturedSphere.measurableSet
    fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := abs_le.1
    (abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le ω hH hHs hB hu hx hE hA)
  linarith [h.2]

end SymplecticForm

end TauCeti
