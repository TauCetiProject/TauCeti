/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Pullback
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sphere
public import TauCeti.Analysis.Contour.Curve.Circle.Basic
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

For a finite holomorphic map `F : X → ℙ¹` from a compact Riemann surface `X` and a `1`-form `η`
meromorphic on `ℙ¹`, the residues of the pullback `F^* η` add up to zero over the preimage of the
poles of `η` (`TauCeti.RiemannSurface.OneForm.sum_residue_preimage_support_pullback_sphere`) and
over the divisor of `F^* η` (`TauCeti.RiemannSurface.OneForm.sum_residue_pullback_sphere`): over a
fibre the residues add up to `deg F` times the residue downstairs.

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

namespace TauCeti.RiemannSurface.OneForm

open AlgebraicGeometry WeilDivisor

variable {ω : OneForm (OnePoint ℂ)}

/-- The sum of the residues over the support of the divisor splits into the residue at `∞` and the
sum over the finite points of the support. -/
private theorem sum_residue_support_eq_residue_infty_add (hω : ∀ x, ω.MeromorphicAt x) :
    ∑ x ∈ ω.divisor.support, ω.residue x =
      ω.residue ∞ + ∑ z ∈ ω.divisor.support.preimage ((↑) : ℂ → OnePoint ℂ) coe_injective.injOn,
        ω.residue (z : OnePoint ℂ) := by
  classical
  set T : Finset ℂ := ω.divisor.support.preimage (↑) coe_injective.injOn
  have hsub : ω.divisor.support ⊆ insert ∞ (T.map ⟨(↑), coe_injective⟩) := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Finset.mem_insert_self _ _
    | coe z => exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ (by simpa [T] using hx))
  rw [sum_residue_divisor_support_eq_of_subset hω hsub, Finset.sum_insert (by simp),
    Finset.sum_map]
  rfl

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
    exact (not_lt.2 (meromorphicOrderAt_coeff_affineChart_nonneg hω hzS)) hz
  have hG := Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hR T hg hTR hgsupp
  -- The residue theorem on the small circle `|w| = 1/R` in the inverted chart: a point `w ≠ 0`
  -- of that disc has `|1/w| ≥ R`, so `1/w` is not in the support.
  have hRinv : 0 < R⁻¹ := inv_pos.2 hR
  have hhsupp : ∀ w ∈ closedBall (0 : ℂ) R⁻¹, _root_.meromorphicOrderAt h w < 0 →
      w ∈ ({0} : Finset ℂ) := by
    intro w hwR hw
    rw [Finset.mem_singleton]
    by_contra hw0
    have hwT : w⁻¹ ∉ T := fun hT ↦ by
      have h1 := hTR hT
      rw [mem_ball_zero_iff, norm_inv] at h1
      rw [mem_closedBall_zero_iff, ← le_inv_comm₀ hR (norm_pos_iff.2 hw0)] at hwR
      exact (not_lt.2 hwR) h1
    have hwS : ((w⁻¹ : ℂ) : OnePoint ℂ) ∉ S := by simpa [T] using hwT
    exact (not_lt.2 (meromorphicOrderAt_coeff_invChart_nonneg hω hw0 hwS)) hw
  have hH := Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hRinv {0}
    (fun w _ ↦ meromorphicAt_coeff_invChart hω w) (by simpa using hRinv) hhsupp
  -- The circle inversion relates the two contour integrals.
  have hinv : (∮ w in C(0, R⁻¹), h w) = -∮ z in C(0, R), g z := by
    have hsub := Contour.circleIntegral_neg_inv_sq_smul_comp_inv g R⁻¹
    rw [inv_inv] at hsub
    rw [← hsub]
    refine circleIntegral.integral_congr hRinv.le fun w hw ↦ ?_
    rw [smul_eq_mul]
    exact coeff_invChart_eq_neg_inv_sq_mul ω (ne_of_mem_sphere hw hRinv.ne')
  rw [Finset.sum_singleton, hinv, hG] at hH
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [sum_residue_support_eq_residue_infty_add hω, hinf, Finset.sum_congr rfl fun z _ ↦ hfin z]
  have := hH.symm
  rw [← mul_neg, mul_right_inj' hpi] at this
  linear_combination this

/-! ### Pullbacks along finite maps to the sphere -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [T2Space X] {η : OneForm (OnePoint ℂ)}

/-- **The residue theorem for a pullback from the sphere.** Let `F : X → ℙ¹` be a finite
holomorphic map from a compact Riemann surface and `η` a `1`-form meromorphic everywhere on the
sphere. Then the residues of `F^* η` over the preimage of the support of the divisor of `η` add
up to zero: over each fibre they add up to `deg F` times the residue of `η`
(`TauCeti.RiemannSurface.OneForm.sum_residue_pullback_eq_degree_mul`), and the residues of `η`
add up to zero (`TauCeti.RiemannSurface.OneForm.sum_residue_sphere`). -/
theorem sum_residue_preimage_support_pullback_sphere (F : FiniteHolomorphicMap X (OnePoint ℂ))
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
theorem sum_residue_pullback_sphere (F : FiniteHolomorphicMap X (OnePoint ℂ))
    (hη : ∀ y, η.MeromorphicAt y) :
    ∑ x ∈ (η.pullback F).divisor.support, (η.pullback F).residue x = 0 := by
  classical
  by_cases hm : ∀ x, (η.pullback F).MeromorphicAt x
  · set P := (finite_preimage_support_divisor F η).toFinset
    have hpull : ∀ x, (η.pullback F).residue x = localMultiplicity F x * η.residue (F x) :=
      fun x ↦ residue_pullback (hη (F x)) (.of_forall fun z ↦ F.holomorphic z)
    have hP : ∑ x ∈ P, (η.pullback F).residue x =
        ∑ x ∈ (η.pullback F).divisor.support ∪ P, (η.pullback F).residue x := by
      refine Finset.sum_subset Finset.subset_union_right fun x _ hx ↦ ?_
      have hFx : F x ∉ η.divisor.support := by simpa [P] using hx
      rw [hpull, residue_eq_zero_of_notMem_support hη hFx, mul_zero]
    rw [sum_residue_divisor_support_eq_of_subset hm Finset.subset_union_left, ← hP,
      sum_residue_preimage_support_pullback_sphere F hη]
  · simp [divisor_of_not_forall_meromorphicAt hm]

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
