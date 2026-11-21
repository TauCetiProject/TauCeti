/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# The Hopf projection is a smooth submersion

Complex projective space `CPⁿ` is the orbit space of the unit sphere `S²ⁿ⁺¹` of `ℂⁿ⁺¹` under
scalar multiplication by unit complex numbers (`TauCeti.ComplexProjectiveSpace`), and its
projection `TauCeti.ComplexProjectiveSpace.mk` is the Hopf fibration. This file shows that `mk` is
a smooth submersion for the real smooth structure underlying the homogeneous-ratio atlas of `CPⁿ`
(`TauCeti.ComplexProjectiveSpace.instIsManifoldReal`) and the stereographic structure of the
sphere.

On the part of the sphere where the coordinate `w_k` is nonzero, `mk` read in the chart `X_k ≠ 0`
is the smooth map `w ↦ (w_j / w_k)_{j ≠ k}`. Its derivative is onto because `mk` has smooth local
sections through every point: the unit representative `w / ‖w‖` of the homogeneous coordinate
vector `w = (z₀, …, 1, …, z_{n-1})` (`TauCeti.ComplexProjectiveSpace.affineUnitVector`), rotated
by a unit complex number so that it passes through the given point, composes with `mk` to the
inverse of the chart.

The circle `Circle` acts smoothly, freely and properly on the sphere with the fibres of `mk` as
its orbits, so the quotient manifold theorem gives the orbit space
`MulAction.orbitRel.Quotient Circle S²ⁿ⁺¹` a smooth structure of its own
(`ProperSMul.orbitRelQuotientChartedSpace`). As `mk` is a smooth submersion with these fibres, the
identity on orbits is a diffeomorphism between the quotient structure and the homogeneous-ratio
structure (`TauCeti.ComplexProjectiveSpace.orbitRelQuotientDiffeomorph`): the two smooth
structures on `CPⁿ` agree.

## Main results

* `TauCeti.ComplexProjectiveSpace.contMDiff_affineUnitVector`: the unit representative of an
  affine point is a smooth map into the sphere.
* `TauCeti.ComplexProjectiveSpace.contMDiff_mk`: the Hopf projection is smooth, of every order.
* `TauCeti.ComplexProjectiveSpace.surjective_mfderiv_mk`: its derivative is onto at every point.
* `TauCeti.ComplexProjectiveSpace.isSubmersion_mk`: it is a submersion.
* `TauCeti.ComplexProjectiveSpace.orbitRelQuotientDiffeomorph`: the diffeomorphism from the
  quotient manifold of the circle action onto `CPⁿ`, sending the orbit of `x` to `mk n x`
  (`TauCeti.ComplexProjectiveSpace.orbitRelQuotientDiffeomorph_mk`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.31
  (uniqueness of smooth quotients) and Theorem 21.10 (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto (2003),
  Theorem 1.21.
-/

public section

noncomputable section

open Function Metric Set
open scoped ContDiff Manifold

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-! ### Smooth local sections over the affine charts -/

/-- The homogeneous coordinate vector `(z₀, …, 1, …, z_{n-1})` of an affine point is a smooth
function of the affine coordinates. -/
theorem contDiff_affineVector (k : Fin (n + 1)) {r : ℕ∞ω} :
    ContDiff ℝ r (affineVector (n := n) k) := by
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  induction i using k.succAboveCases with
  | x => simpa only [affineVector_apply_self] using contDiff_const
  | p j => simpa only [affineVector_apply_succAbove] using contDiff_apply ℝ (fun _ ↦ ℂ) j

/-- The unit representative `w / ‖w‖` of the point with affine coordinates `z` in the chart
`X_k ≠ 0` is a smooth map into the unit sphere `S²ⁿ⁺¹`. -/
theorem contMDiff_affineUnitVector (k : Fin (n + 1)) {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) r (affineUnitVector (n := n) k) := by
  have hv := contDiff_affineVector (n := n) k (r := r)
  have h : ContDiff ℝ r fun z ↦ ‖affineVector k z‖⁻¹ • affineVector k z :=
    ((hv.norm ℂ fun z ↦ affineVector_ne_zero k z).inv
      fun z ↦ norm_ne_zero_iff.2 (affineVector_ne_zero k z)).smul hv
  exact (h.contMDiff.codRestrict_sphere fun z ↦ coe_affineUnitVector_apply k z ▸
    (affineUnitVector k z).property).congr fun z ↦
      Subtype.ext (coe_affineUnitVector_apply k z)

/-! ### The Hopf projection -/

/-- **The Hopf projection is smooth**, of every order, from the unit sphere `S²ⁿ⁺¹` to complex
projective space with the real structure of its homogeneous-ratio atlas. In the chart `X_k ≠ 0`
it reads `w ↦ (w_j / w_k)_{j ≠ k}`. -/
theorem contMDiff_mk (r : ℕ∞ω) :
    ContMDiff (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) r (mk n) := by
  intro w
  obtain ⟨k, hk⟩ := exists_mem_affineOpen (mk n w)
  have hwk : (w : EuclideanSpace ℂ (Fin (n + 1))) k ≠ 0 := (mk_mem_affineOpen_iff k w).1 hk
  -- The homogeneous ratios are holomorphic, hence real smooth, where `w_k ≠ 0`.
  have hG : ContDiffAt ℂ r (fun v : EuclideanSpace ℂ (Fin (n + 1)) ↦
      fun j : Fin n ↦ v (k.succAbove j) / v k) (w : EuclideanSpace ℂ (Fin (n + 1))) :=
    contDiffAt_pi.2 fun j ↦ (contDiffAt_piLp_apply (𝕜 := ℂ) 2).div
      (contDiffAt_piLp_apply (𝕜 := ℂ) 2) hwk
  refine ((contMDiff_affineParam_real k r).contMDiffAt.comp w
    ((hG.restrict_scalars ℝ).comp_contMDiffAt contMDiff_coe_sphere.contMDiffAt))
    |>.congr_of_eventuallyEq ?_
  filter_upwards [((isOpen_affineOpen k).preimage (continuous_mk n)).mem_nhds hk] with v hv
  rw [comp_apply, ← affineParam_ratio k hv]
  simp only [comp_apply, ratio_mk]

/-- **The derivative of the Hopf projection is onto** at every point of `S²ⁿ⁺¹`. -/
theorem surjective_mfderiv_mk (w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    Surjective (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (mk n) w) := by
  obtain ⟨k, hk⟩ := exists_mem_affineOpen (mk n w)
  set z₀ := affineChart k (mk n w)
  have hw : mk n w = mk n (affineUnitVector k z₀) := by
    rw [← affineParam_def, ← affineChart_symm_apply,
      (affineChart k).left_inv (by rwa [affineChart_source])]
  obtain ⟨c, hc⟩ := (mk_eq_mk_iff_exists_circle_smul n w (affineUnitVector k z₀)).1 hw
  -- A smooth section `z ↦ c • w(z) / ‖w(z)‖` of `mk n` over the chart `X_k ≠ 0`, passing
  -- through `w` at `z₀`, for a suitable unit complex number `c`. Its composite with `mk n` is
  -- the inverse of that chart.
  set s : (Fin n → ℂ) → sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
    fun z ↦ c • affineUnitVector k z
  have hs : ContMDiff 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) 1 s :=
    (contMDiff_smul (I := 𝓡 1)).comp (contMDiff_const.prodMk (contMDiff_affineUnitVector k))
  have hsz : s z₀ = w := hc
  have hcomp : mk n ∘ s = (affineChart k).symm := by
    funext z
    rw [comp_apply, affineChart_symm_apply, affineParam_def]
    exact (mk_eq_mk_iff_exists_circle_smul n _ _).2 ⟨c, rfl⟩
  -- The derivative of the inverse of a chart of the maximal atlas is invertible.
  have hchart := (isInvertible_mfderivWithin_extend_symm
    (affineChart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℂ)) (r := 1) k) (y := z₀)
    (by simp)).surjective
  simp only [OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, comp_id,
    modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hchart
  have key : Surjective (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (mk n ∘ s) z₀) := by
    rwa [hcomp]
  rw [mfderiv_comp_of_eq ((contMDiff_mk 1 w).mdifferentiableAt one_ne_zero)
    ((hs z₀).mdifferentiableAt one_ne_zero) hsz, ContinuousLinearMap.coe_comp] at key
  have h := key.of_comp
  rwa [hsz] at h

/-- **The Hopf projection is a submersion**, of every order, from `S²ⁿ⁺¹` onto complex projective
space with the real structure of its homogeneous-ratio atlas. -/
theorem isSubmersion_mk (r : ℕ∞ω) :
    Manifold.IsSubmersion (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) r (mk n) :=
  ((contMDiff_mk (n := n) ω).isSubmersionOfComplement_of_surjective_mfderiv le_top
    surjective_mfderiv_mk).isSubmersion.of_le le_top

/-! ### Comparison with the quotient manifold of the circle action -/

variable (n) in
/-- **The quotient smooth structure on `CPⁿ` is the homogeneous-ratio structure.** The circle acts
smoothly, freely and properly on `S²ⁿ⁺¹`, so its orbit space carries the smooth structure of the
quotient manifold theorem (`ProperSMul.orbitRelQuotientChartedSpace`). The identity on orbits is a
`C^m` diffeomorphism from it onto complex projective space with the real structure of its
homogeneous-ratio atlas, sending the orbit of `x` to `mk n x`. -/
def orbitRelQuotientDiffeomorph {m : ℕ∞ω} (hm : m ≤ ∞) :
    letI := ProperSMul.orbitRelQuotientChartedSpace (𝓡 1) Circle (𝓡 (2 * n + 1))
      (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    MulAction.orbitRel.Quotient Circle (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) ≃ₘ^m⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace (EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace ℝ (Fin (2 * n + 1)))), 𝓘(ℝ, Fin n → ℂ)⟯ ComplexProjectiveSpace n :=
  ProperSMul.diffeomorphOfOrbitSubmersion (𝓡 1) hm (mk n) (isSubmersion_mk m) (mk_surjective n)
    (mk_eq_mk_iff_exists_circle_smul n)

/-- `orbitRelQuotientDiffeomorph` sends the orbit of `x` to the point `mk n x`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_mk {m : ℕ∞ω} (hm : m ≤ ∞)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    letI := ProperSMul.orbitRelQuotientChartedSpace (𝓡 1) Circle (𝓡 (2 * n + 1))
      (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    orbitRelQuotientDiffeomorph n hm (Quotient.mk _ x) = mk n x :=
  ProperSMul.diffeomorphOfOrbitSubmersion_mk (𝓡 1) hm _ _ _ _ x

/-- The inverse of `orbitRelQuotientDiffeomorph` sends `mk n x` to the orbit of `x`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_symm_mk {m : ℕ∞ω} (hm : m ≤ ∞)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    letI := ProperSMul.orbitRelQuotientChartedSpace (𝓡 1) Circle (𝓡 (2 * n + 1))
      (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (orbitRelQuotientDiffeomorph n hm).symm (mk n x) = Quotient.mk _ x :=
  ProperSMul.diffeomorphOfOrbitSubmersion_symm_apply (𝓡 1) hm _ _ _ _ x

end TauCeti.ComplexProjectiveSpace
