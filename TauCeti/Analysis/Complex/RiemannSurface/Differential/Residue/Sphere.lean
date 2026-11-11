/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Pullback
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sphere
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Divisor
public import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# The residue theorem on the Riemann sphere

A `1`-form `ω` meromorphic everywhere on the Riemann sphere `OnePoint ℂ` has residues adding up to
zero (`TauCeti.RiemannSurface.OneForm.sum_residue_sphere`):

`∑_{x ∈ supp (div ω)} Res_x ω = 0`.

Write `ω = g(z) dz` in the affine chart and `ω = h(w) dw` in the inverted chart `w = 1/z`, so that
`h(w) = -g(1/w) / w²` for `w ≠ 0`. For `R` large, every finite pole lies in the disc `|z| < R`
and `h` has no pole other than `0` in the disc `|w| ≤ 1/R`. The classical residue theorem gives
`∮_{|z| = R} g = 2πi ∑_{z ∈ ℂ} Res_z ω` and `∮_{|w| = 1/R} h = 2πi Res_∞ ω`, and the substitution
`w = 1/z`, which reverses the orientation of the circle, gives `∮_{|w| = 1/R} h = -∮_{|z| = R} g`
(`TauCeti.Contour.circleIntegral_neg_inv_sq_smul_comp_inv`).

Two consequences on a compact Riemann surface `X` follow.

* For a finite holomorphic map `F : X → ℙ¹` and a `1`-form `η` meromorphic on `ℙ¹`, the residues
  of the pullback `F^* η` add up to zero over the preimage of the poles of `η`
  (`TauCeti.RiemannSurface.OneForm.sum_residue_pullback_sphere`) and over the divisor of `F^* η`
  (`TauCeti.RiemannSurface.OneForm.sum_residue_divisor_pullback_sphere`): over a fibre the
  residues add up to `deg F` times the residue downstairs.
* For a nonzero meromorphic function `f` on a compact connected Riemann surface, the residues of
  the logarithmic differential `df / f` add up to zero
  (`TauCeti.RiemannSurface.OneForm.sum_residue_logDeriv`). The residue of `df / f` at `x` is the
  order of `f` at `x`, so this is the statement that a principal divisor has degree zero.

The general residue theorem on a compact Riemann surface is not proved here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §10 (the residue theorem).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter IV §1 (the residue theorem, and its proof on the
  Riemann sphere).
-/

public noncomputable section

open Complex Filter Function IsManifold Metric OnePoint Set Topology

open scoped Manifold Real

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Inversion of a circle integral.** Substituting `w = 1/z` turns the circle `|w| = r` into the
circle `|z| = 1/r` traversed in the opposite direction, and `dw = -dz / z²`. So if
`h(w) = -g(1/w) / w²`, then `∮_{|w| = r} h(w) dw = -∮_{|z| = 1/r} g(z) dz`. -/
theorem circleIntegral_neg_inv_sq_smul_comp_inv (g : ℂ → E) (r : ℝ) :
    (∮ w in C(0, r), (-(w ^ 2)⁻¹) • g w⁻¹) = -∮ z in C(0, r⁻¹), g z := by
  set F : ℝ → E := fun θ ↦ (circleMap 0 r⁻¹ θ * I) • g (circleMap 0 r⁻¹ θ) with hF
  have hpt : ∀ θ : ℝ, (circleMap 0 r θ * I) • ((-(circleMap 0 r θ ^ 2)⁻¹) •
      g (circleMap 0 r θ)⁻¹) = -F (-θ) := by
    intro θ
    simp only [hF]
    rw [← circleMap_zero_inv, smul_smul, ← neg_smul]
    congr 1
    rcases eq_or_ne (circleMap 0 r θ) 0 with h | h
    · simp [h]
    · field_simp
  have hper : Periodic F (2 * π) := fun θ ↦ by
    simp only [hF, periodic_circleMap 0 r⁻¹ θ]
  simp only [circleIntegral, deriv_circleMap, hpt, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg, neg_zero]
  congr 1
  simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0

end TauCeti.Contour

namespace TauCeti.RiemannSurface.OneForm

open AlgebraicGeometry WeilDivisor

/-! ### The two charts of the sphere -/

private theorem affineChart_mem_maximalAtlas_sphere :
    (affineChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∈ maximalAtlas 𝓘(ℂ) 1 (OnePoint ℂ) := by
  simpa only [chartAt_coe] using chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) ((0 : ℂ) : OnePoint ℂ)

private theorem invChart_mem_maximalAtlas_sphere :
    (invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∈ maximalAtlas 𝓘(ℂ) 1 (OnePoint ℂ) :=
  chartAt_infty (𝕜 := ℂ) ▸ chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) ∞

/-- The transformation law between the two charts of the sphere: if `ω = g(z) dz` in the affine
chart, then `ω = -g(1/w) / w² dw` in the inverted chart, at every `w ≠ 0`. -/
private theorem coeff_invChart_eq_neg_inv_sq_mul (ω : OneForm (OnePoint ℂ)) {w : ℂ} (hw : w ≠ 0) :
    ω.coeff invChart w = -(w ^ 2)⁻¹ * ω.coeff affineChart w⁻¹ := by
  have hw' : w⁻¹ ≠ 0 := inv_ne_zero hw
  have h := ω.coeff_eq_coeff_mul_deriv affineChart_mem_maximalAtlas_sphere
    invChart_mem_maximalAtlas_sphere
    (y := ((w⁻¹ : ℂ) : OnePoint ℂ)) (by simp)
    (by simpa using fun h ↦ hw' (coe_injective h))
  rw [invChart_coe, inv_inv, affineChart_coe, affineChart_comp_invChart_symm, deriv_inv] at h
  rw [h, mul_comm]

variable {ω : OneForm (OnePoint ℂ)}

/-- Off the support of its divisor, an everywhere meromorphic `1`-form has nonnegative order. -/
private theorem order_nonneg_of_notMem_support (hω : ∀ x, ω.MeromorphicAt x) {x : OnePoint ℂ}
    (hx : x ∉ ω.divisor.support) : 0 ≤ ω.order x := by
  rw [mem_support_iff, not_not, coeff_divisor hω, WithTop.untop₀_eq_zero] at hx
  rcases hx with h | h <;> simp [h]

/-! ### The residue theorem on the sphere -/

/-- **The residue theorem on the Riemann sphere.** The residues of a `1`-form meromorphic
everywhere on `OnePoint ℂ` add up to zero; the residue at `∞` is read in the inverted chart. -/
theorem sum_residue_sphere (hω : ∀ x, ω.MeromorphicAt x) :
    ∑ x ∈ ω.divisor.support, ω.residue x = 0 := by
  classical
  set S := ω.divisor.support
  set g := ω.coeff affineChart
  set h := ω.coeff invChart
  -- The finite part of the support, and a radius `R` beyond all of it.
  set T : Finset ℂ := S.preimage (↑) coe_injective.injOn
  obtain ⟨r, hr⟩ := (T : Set ℂ).toFinite.isBounded.subset_ball 0
  set R := max r 1
  have hR : 0 < R := lt_max_of_lt_right one_pos
  have hTR : (T : Set ℂ) ⊆ ball 0 R := hr.trans (ball_subset_ball (le_max_left _ _))
  have hres0 : ∀ x ∉ S, ω.residue x = 0 := fun x hx ↦
    residue_eq_zero_of_order_nonneg (order_nonneg_of_notMem_support hω hx)
  -- Split the sum into the finite points and `∞`.
  have hsplit : ∑ x ∈ S, ω.residue x =
      ω.residue ∞ + ∑ z ∈ T, ω.residue (z : OnePoint ℂ) := by
    have hsub : S ⊆ insert ∞ (T.map ⟨(↑), coe_injective⟩) := by
      intro x hx
      induction x using OnePoint.rec with
      | infty => exact Finset.mem_insert_self _ _
      | coe z => exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ (by simpa [T] using hx))
    rw [Finset.sum_subset hsub fun x _ hx ↦ hres0 x hx, Finset.sum_insert (by simp),
      Finset.sum_map]
    rfl
  have hfin : ∀ z : ℂ, ω.residue (z : OnePoint ℂ) = Contour.residue g z := fun z ↦ by
    rw [residue_def, chartAt_coe, affineChart_coe]
  have hinf : ω.residue ∞ = Contour.residue h 0 := by
    rw [residue_def, chartAt_infty, invChart_infty]
  -- The residue theorem on the large circle `|z| = R` in the affine chart.
  have hg : MeromorphicOn g (closedBall 0 R) := fun z _ ↦ by
    simpa only [meromorphicAt_def, chartAt_coe, affineChart_coe] using hω z
  have hgsupp : ∀ z ∈ closedBall (0 : ℂ) R, _root_.meromorphicOrderAt g z < 0 → z ∈ T := by
    intro z _ hz
    by_contra hzT
    have hzS : (z : OnePoint ℂ) ∉ S := by simpa [T] using hzT
    have := order_nonneg_of_notMem_support hω hzS
    rw [order_def, chartAt_coe, affineChart_coe] at this
    exact (not_lt.2 this) hz
  have hG := Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hR T hg hTR hgsupp
  -- The residue theorem on the small circle `|w| = 1/R` in the inverted chart.
  have hRinv : 0 < R⁻¹ := inv_pos.2 hR
  have hh : MeromorphicOn h (closedBall 0 R⁻¹) := by
    intro w _
    rcases eq_or_ne w 0 with rfl | hw
    · simpa only [meromorphicAt_def, chartAt_infty, invChart_infty] using hω ∞
    · have hsrc : ((w⁻¹ : ℂ) : OnePoint ℂ) ∈ invChart.source := by
        simpa using fun h ↦ inv_ne_zero hw (coe_injective h)
      simpa only [invChart_coe, inv_inv] using
        (meromorphicAt_iff_of_mem_maximalAtlas invChart_mem_maximalAtlas_sphere hsrc).1 (hω _)
  have hhsupp : ∀ w ∈ closedBall (0 : ℂ) R⁻¹, _root_.meromorphicOrderAt h w < 0 →
      w ∈ ({0} : Finset ℂ) := by
    intro w hwR hw
    rw [Finset.mem_singleton]
    by_contra hw0
    have hsrc : ((w⁻¹ : ℂ) : OnePoint ℂ) ∈ invChart.source := by
      simpa using fun h ↦ inv_ne_zero hw0 (coe_injective h)
    have hwT : w⁻¹ ∉ T := fun hT ↦ by
      have h1 := hTR hT
      rw [mem_ball_zero_iff, norm_inv] at h1
      rw [mem_closedBall_zero_iff] at hwR
      have h2 : R ≤ ‖w‖⁻¹ := by
        rw [le_inv_comm₀ hR (norm_pos_iff.2 hw0)]
        exact hwR
      exact (not_lt.2 h2) h1
    have hwS : ((w⁻¹ : ℂ) : OnePoint ℂ) ∉ S := by simpa [T] using hwT
    have := order_nonneg_of_notMem_support hω hwS
    rw [order_eq_of_mem_maximalAtlas invChart_mem_maximalAtlas_sphere hsrc, invChart_coe,
      inv_inv] at this
    exact (not_lt.2 this) hw
  have hH := Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hRinv {0} hh
    (by simpa using hRinv) hhsupp
  -- The circle inversion relates the two contour integrals.
  have hinv : (∮ w in C(0, R⁻¹), h w) = -∮ z in C(0, R), g z := by
    rw [show (∮ z in C(0, R), g z) = ∮ z in C(0, R⁻¹⁻¹), g z by rw [inv_inv],
      ← Contour.circleIntegral_neg_inv_sq_smul_comp_inv g R⁻¹]
    refine circleIntegral.integral_congr hRinv.le fun w hw ↦ ?_
    rw [smul_eq_mul]
    exact coeff_invChart_eq_neg_inv_sq_mul ω (ne_of_mem_sphere hw hRinv.ne')
  rw [Finset.sum_singleton, hinv, hG] at hH
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [hsplit, hinf, Finset.sum_congr rfl fun z _ ↦ hfin z]
  have := hH.symm
  rw [← mul_neg, mul_right_inj' hpi] at this
  linear_combination this

/-! ### Pullbacks along finite maps to the sphere -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {η : OneForm (OnePoint ℂ)}

/-- The preimage under a map with finite fibres of the support of the divisor of `η` is finite. -/
theorem finite_preimage_support_divisor (F : FiniteHolomorphicMap X (OnePoint ℂ))
    (η : OneForm (OnePoint ℂ)) : (F ⁻¹' (η.divisor.support : Set (OnePoint ℂ))).Finite :=
  η.divisor.support.finite_toSet.preimage' fun y _ ↦ F.finite_fiber y

variable [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X]

/-- **The residue theorem for a pullback from the sphere.** Let `F : X → ℙ¹` be a finite
holomorphic map from a compact Riemann surface and `η` a `1`-form meromorphic everywhere on the
sphere. Then the residues of `F^* η` over the preimage of the support of the divisor of `η` add
up to zero: over each fibre they add up to `deg F` times the residue of `η`
(`TauCeti.RiemannSurface.OneForm.sum_residue_pullback_eq_degree_mul`), and the residues of `η`
add up to zero (`TauCeti.RiemannSurface.OneForm.sum_residue_sphere`). -/
theorem sum_residue_pullback_sphere (F : FiniteHolomorphicMap X (OnePoint ℂ))
    (hη : ∀ y, η.MeromorphicAt y) :
    ∑ x ∈ (finite_preimage_support_divisor F η).toFinset, (η.pullback F).residue x = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := F) (t := η.divisor.support)
    fun x hx ↦ by simpa using hx]
  have hfib : ∀ y ∈ η.divisor.support,
      {x ∈ (finite_preimage_support_divisor F η).toFinset | F x = y} =
        (F.finite_fiber y).toFinset := fun y hy ↦ by
    ext x
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_preimage, Finset.mem_coe,
      mem_singleton_iff]
    exact ⟨And.right, fun hx ↦ ⟨hx ▸ hy, hx⟩⟩
  rw [Finset.sum_congr rfl fun y hy ↦ by
    rw [hfib y hy, sum_residue_pullback_eq_degree_mul F (hη y)], ← Finset.mul_sum,
    sum_residue_sphere hη, mul_zero]

/-- **The residue theorem for a pullback from the sphere**, summed over the divisor of the
pullback. Let `F : X → ℙ¹` be a finite holomorphic map from a compact Riemann surface and `η` a
`1`-form meromorphic everywhere on the sphere. Then the residues of `F^* η` add up to zero. -/
theorem sum_residue_divisor_pullback_sphere (F : FiniteHolomorphicMap X (OnePoint ℂ))
    (hη : ∀ y, η.MeromorphicAt y) :
    ∑ x ∈ (η.pullback F).divisor.support, (η.pullback F).residue x = 0 := by
  classical
  by_cases hm : ∀ x, (η.pullback F).MeromorphicAt x
  · set P := (finite_preimage_support_divisor F η).toFinset
    have hpull : ∀ x, (η.pullback F).residue x = localMultiplicity F x * η.residue (F x) :=
      fun x ↦ residue_pullback (hη (F x)) (.of_forall fun z ↦ F.holomorphic z)
    have h1 : ∑ x ∈ (η.pullback F).divisor.support, (η.pullback F).residue x =
        ∑ x ∈ (η.pullback F).divisor.support ∪ P, (η.pullback F).residue x := by
      refine Finset.sum_subset Finset.subset_union_left fun x _ hx ↦ ?_
      rw [mem_support_iff, not_not, coeff_divisor hm, WithTop.untop₀_eq_zero] at hx
      exact residue_eq_zero_of_order_nonneg (by rcases hx with h | h <;> simp [h])
    have h2 : ∑ x ∈ P, (η.pullback F).residue x =
        ∑ x ∈ (η.pullback F).divisor.support ∪ P, (η.pullback F).residue x := by
      refine Finset.sum_subset Finset.subset_union_right fun x _ hx ↦ ?_
      have hFx : F x ∉ η.divisor.support := by simpa [P] using hx
      rw [hpull, residue_eq_zero_of_order_nonneg (order_nonneg_of_notMem_support hη hFx),
        mul_zero]
    rw [h1, ← h2, sum_residue_pullback_sphere F hη]
  · simp [divisor_of_not_forall_meromorphicAt hm]

/-! ### The logarithmic differential -/

/-- **The residue theorem for `df / f`.** On a compact connected Riemann surface, the residues of
the logarithmic differential `f⁻¹ df` of a nonzero meromorphic function `f` add up to zero over
the zeros and poles of `f`. The residue at `x` is the order of `f` at `x`
(`TauCeti.RiemannSurface.OneForm.residue_inv_smul_mvfderiv`), so the sum is the degree of the
principal divisor of `f`, which vanishes
(`TauCeti.RiemannSurface.MeromorphicFunction.degree_principalDivisor`). -/
theorem sum_residue_logDeriv [ConnectedSpace X] {f : MeromorphicFunction X} (hf : f ≠ 0) :
    ∑ x ∈ ((MeromorphicFunction.orderSystem X).principalDivisor
        (Additive.ofMul (Units.mk0 f hf))).support,
      residue (f.finitePart⁻¹ • mvfderiv 𝓘(ℂ) f.finitePart) x = 0 := by
  set D := (MeromorphicFunction.orderSystem X).principalDivisor (Additive.ofMul (Units.mk0 f hf))
  have hres : ∀ x, residue (f.finitePart⁻¹ • mvfderiv 𝓘(ℂ) f.finitePart) x =
      (WeilDivisor.coeff D x : ℂ) :=
    fun x ↦ residue_inv_smul_mvfderiv (f.meromorphicAt_finitePart x) (by
      rw [← MeromorphicFunction.order_apply]
      exact (MeromorphicFunction.coe_coeff_principalDivisor_orderSystem
        (Additive.ofMul (Units.mk0 f hf)) x).symm)
  rw [Finset.sum_congr rfl fun x _ ↦ hres x]
  have hdeg := MeromorphicFunction.degree_principalDivisor (Additive.ofMul (Units.mk0 f hf))
  rw [degree_apply] at hdeg
  exact_mod_cast hdeg

/-! ### Check: the form `dz / z` on the sphere -/

/-- The `1`-form `dz / z` on the sphere, in the affine and inverted charts. -/
private theorem coeff_inv_smul_sphereCoordinateDifferential_invChart {w : ℂ} (hw : w ≠ 0) :
    (((affineChart : OnePoint ℂ → ℂ))⁻¹ • sphereCoordinateDifferential).coeff invChart w =
      -w⁻¹ := by
  rw [coeff_smul, Pi.mul_apply, coeff_invChart_eq_neg_inv_sq_mul _ hw,
    coeff_sphereCoordinateDifferential_affineChart, comp_apply, Pi.inv_apply,
    invChart_symm_of_ne_zero hw, affineChart_coe, inv_inv]
  field_simp

/-- The form `dz / z` has residue `1` at `0`. -/
theorem residue_inv_smul_sphereCoordinateDifferential_zero :
    (((affineChart : OnePoint ℂ → ℂ))⁻¹ • sphereCoordinateDifferential).residue
      ((0 : ℂ) : OnePoint ℂ) = 1 := by
  rw [residue_def, chartAt_coe, affineChart_coe, coeff_smul,
    coeff_sphereCoordinateDifferential_affineChart]
  have : (((affineChart : OnePoint ℂ → ℂ))⁻¹ ∘ affineChart.symm) * (fun _ ↦ (1 : ℂ)) =
      fun z ↦ (z - 0)⁻¹ := by
    funext z
    simp
  rw [this, Contour.residue_sub_inv]

/-- The form `dz / z` has residue `-1` at `∞`. -/
theorem residue_inv_smul_sphereCoordinateDifferential_infty :
    (((affineChart : OnePoint ℂ → ℂ))⁻¹ • sphereCoordinateDifferential).residue ∞ = -1 := by
  rw [residue_def, chartAt_infty, invChart_infty,
    Contour.residue_congr_nhdsNE (g := (-1 : ℂ) • fun w ↦ (w - 0)⁻¹)
      (eventually_nhdsWithin_of_forall fun w hw ↦ by
        rw [coeff_inv_smul_sphereCoordinateDifferential_invChart hw]
        simp),
    Contour.residue_const_smul, Contour.residue_sub_inv, smul_eq_mul, mul_one]

end TauCeti.RiemannSurface.OneForm
