/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Radial contractions of a finite-dimensional real normed space

The radial contraction of `E` about `c` with parameter `κ ≥ 0` is
`y ↦ c + (1 + κ d(y, c)²)^(-1/2) • (y - c)`, where `d = Euclidean.dist` is the distance of the
inner product structure that `toEuclidean` transports to `E`. It is jointly smooth in `κ` and `y`,
it is the identity for `κ = 0`, it moves no point away from `c` for `d`, and for `κ = r⁻²` it is
Mathlib's `OpenPartialHomeomorph.univBall` after an affine normalization, so it maps `E`
homeomorphically, with a smooth inverse, onto the Euclidean ball `Euclidean.ball c r`. Its
derivative at the centre is the identity.

The Euclidean distance replaces the norm of `E` because its square is smooth, which the square of
an arbitrary norm need not be.

These maps shrink an embedding of `E` into a prescribed neighbourhood of its centre without
changing its derivative there; they are used to reduce the disc theorem in a manifold to the
Euclidean disc theorem.

## Main definitions

* `TauCeti.radialContraction`: the radial contraction about a point with a given parameter.

## Main results

* `TauCeti.euclideanDist_radialContraction_le`: a radial contraction moves no point away from
  its centre.
* `TauCeti.radialContraction_mem_ball`: for `κ = r⁻²` it takes values in the Euclidean ball of
  radius `r`.
* `TauCeti.contDiffOn_radialContraction`: joint smoothness in the parameter and the point.
* `TauCeti.exists_radialContraction_eq_openPartialHomeomorph`: for a positive parameter it is an
  open partial homeomorphism defined on all of `E`, smooth in both directions.
* `TauCeti.hasFDerivAt_radialContraction_self`: its derivative at the centre is the identity, so
  precomposing with it does not change derivatives at the centre
  (`TauCeti.fderiv_comp_radialContraction_self`).

The construction transports Mathlib's `OpenPartialHomeomorph.univBall` and its smoothness
(`contDiffOn_univBall_symm`).
-/

public section

noncomputable section

open Set Metric OpenPartialHomeomorph
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The radial contraction of `E` about `c` with parameter `κ`: the point `y` moves towards `c`
by the factor `(1 + κ d(y, c)²)^(-1/2)`, for the Euclidean distance
`d(y, c) = ‖toEuclidean (y - c)‖`. For `κ = 0` it is the identity, and for `κ = r⁻²` it is a
diffeomorphism of `E` onto `Euclidean.ball c r`. -/
def radialContraction (c : E) (κ : ℝ) (y : E) : E :=
  c + (√(1 + κ * ‖toEuclidean (y - c)‖ ^ 2))⁻¹ • (y - c)

@[simp] theorem radialContraction_zero (c y : E) : radialContraction c 0 y = y := by
  simp [radialContraction]

@[simp] theorem radialContraction_self (c : E) (κ : ℝ) : radialContraction c κ c = c := by
  simp [radialContraction]

/-- The radial contraction read in `toEuclidean`: the image of `y - c` is rescaled by the
contraction factor. -/
theorem toEuclidean_radialContraction (c : E) (κ : ℝ) (y : E) :
    toEuclidean (radialContraction c κ y) =
      toEuclidean c + (√(1 + κ * ‖toEuclidean (y - c)‖ ^ 2))⁻¹ • toEuclidean (y - c) := by
  rw [radialContraction, map_add, map_smul]

/-- A radial contraction moves no point away from the centre, for the Euclidean distance. -/
theorem euclideanDist_radialContraction_le (c y : E) {κ : ℝ} (hκ : 0 ≤ κ) :
    Euclidean.dist (radialContraction c κ y) c ≤ Euclidean.dist y c := by
  have h1 : 1 ≤ √(1 + κ * ‖toEuclidean (y - c)‖ ^ 2) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_right (by positivity))
  simp only [Euclidean.dist, dist_eq_norm, ← map_sub]
  rw [map_sub, toEuclidean_radialContraction, add_sub_cancel_left, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le h1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)

/-- For a positive parameter, the radial contraction read in `toEuclidean` is `univBall` read
after the affine normalization `y ↦ r⁻¹ • toEuclidean (y - c)`, where `κ = r⁻²`. -/
theorem toEuclidean_radialContraction_eq_univBall (c y : E) {r : ℝ} (hr : 0 < r) :
    toEuclidean (radialContraction c (r⁻¹ ^ 2) y) =
      univBall (toEuclidean c) r (r⁻¹ • toEuclidean (y - c)) := by
  -- For `r > 0`, `univBall c r` is `univUnitBall` followed by `x ↦ r • x + c`, by definition.
  have hball (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      univBall (toEuclidean c) r x = r • univUnitBall x + toEuclidean c := by
    simp only [univBall, hr, ↓reduceDIte]
    rfl
  rw [hball, univUnitBall_apply, toEuclidean_radialContraction, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr, smul_smul, smul_smul, mul_pow, add_comm (toEuclidean c)]
  congr 2
  field_simp

/-- For `κ = r⁻²` the radial contraction lands in the Euclidean ball of radius `r` about the
centre. -/
theorem radialContraction_mem_ball (c y : E) {r : ℝ} (hr : 0 < r) :
    radialContraction c (r⁻¹ ^ 2) y ∈ Euclidean.ball c r := by
  rw [Euclidean.ball_eq_preimage, mem_preimage, toEuclidean_radialContraction_eq_univBall c y hr,
    ← univBall_target (toEuclidean c) hr]
  exact (univBall (toEuclidean c) r).map_source (by simp)

/-- For `κ = r⁻²`, the range of the radial contraction is the whole Euclidean ball. -/
theorem range_radialContraction (c : E) {r : ℝ} (hr : 0 < r) :
    range (radialContraction c (r⁻¹ ^ 2)) = Euclidean.ball c r := by
  apply Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    exact radialContraction_mem_ball c y hr
  · intro z hz
    have hz' : toEuclidean z ∈ (univBall (toEuclidean c) r).target := by
      simpa only [univBall_target _ hr, Euclidean.ball_eq_preimage, mem_preimage] using hz
    let w := (univBall (toEuclidean c) r).symm (toEuclidean z)
    refine ⟨c + toEuclidean.symm (r • w), ?_⟩
    apply toEuclidean.injective
    rw [toEuclidean_radialContraction_eq_univBall c _ hr]
    simpa only [add_sub_cancel_left, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul] using
      (univBall (toEuclidean c) r).right_inv hz'

/-- Membership in the range of a positive radial contraction is membership in its ball. -/
@[simp] theorem exists_radialContraction_eq_iff (c y : E) {r : ℝ} (hr : 0 < r) :
    (∃ x, radialContraction c (r ^ 2)⁻¹ x = y) ↔ y ∈ Euclidean.ball c r := by
  -- Use the normal form of range membership and inverse powers used by `simp`.
  simpa only [mem_range, inv_pow] using Set.ext_iff.mp (range_radialContraction c hr) y

/-- The radial contraction is jointly smooth in the parameter and the point, wherever
`1 + κ d(y, c)²` is positive. -/
theorem contDiffOn_radialContraction (c : E) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => radialContraction c q.1 q.2)
      {q | 0 < 1 + q.1 * ‖toEuclidean (q.2 - c)‖ ^ 2} := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  have hsub : ContDiff ℝ ∞ fun q : ℝ × E => q.2 - c := contDiff_snd.sub contDiff_const
  have hden : ContDiffAt ℝ ∞ (fun q : ℝ × E => √(1 + q.1 * ‖toEuclidean (q.2 - c)‖ ^ 2)) q :=
    (contDiffAt_const.add (contDiffAt_fst.mul
      ((contDiff_norm_sq ℝ).comp (toEuclidean.contDiff.comp hsub)).contDiffAt)).sqrt hq.ne'
  exact contDiffAt_const.add ((hden.inv (Real.sqrt_ne_zero'.mpr hq)).smul hsub.contDiffAt)

/-- A radial contraction with nonnegative parameter is smooth. -/
theorem contDiff_radialContraction (c : E) {κ : ℝ} (hκ : 0 ≤ κ) :
    ContDiff ℝ ∞ (radialContraction c κ) := by
  rw [← contDiffOn_univ]
  exact (contDiffOn_radialContraction c).comp (contDiffOn_const.prodMk contDiffOn_id)
    fun y _ => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hκ (sq_nonneg _))

/-- For a positive parameter, the radial contraction is the restriction to all of `E` of an open
partial homeomorphism onto a Euclidean ball, which is smooth in both directions. -/
theorem exists_radialContraction_eq_openPartialHomeomorph (c : E) {κ : ℝ} (hκ : 0 < κ) :
    ∃ Θ : OpenPartialHomeomorph E E, Θ.source = univ ∧
      ContDiffOn ℝ ∞ Θ Θ.source ∧ ContDiffOn ℝ ∞ Θ.symm Θ.target ∧
      ⇑Θ = radialContraction c κ := by
  set r := (√κ)⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hκ)
  set e := toEuclidean (E := E)
  -- The affine normalization `y ↦ r⁻¹ • e (y - c)` and its inverse `z ↦ e.symm (r • z) + c`.
  let A : E ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ((Homeomorph.subRight c).trans e.toHomeomorph).trans
      (Homeomorph.smulOfNeZero r⁻¹ (by positivity))
  have hA (y : E) : A y = r⁻¹ • e (y - c) := rfl
  have hAsymm (z) : A.symm z = e.symm (r⁻¹⁻¹ • z) + c := rfl
  let Θ := (A.transOpenPartialHomeomorph (univBall (e c) r)).transHomeomorph e.symm.toHomeomorph
  have hΘ : ⇑Θ = radialContraction c κ := by
    ext y
    simp only [Θ, transHomeomorph_apply, Homeomorph.transOpenPartialHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply]
    rw [hA, ← toEuclidean_radialContraction_eq_univBall c y hr, inv_inv, Real.sq_sqrt hκ.le]
    exact e.symm_apply_apply _
  have hΘsymm : ⇑Θ.symm = fun z => A.symm ((univBall (e c) r).symm (e z)) := rfl
  have hΘtarget : Θ.target = e ⁻¹' ball (e c) r := by
    rw [transHomeomorph_target, Homeomorph.transOpenPartialHomeomorph_target,
      univBall_target (e c) hr]
    rfl
  refine ⟨Θ, by simp [Θ], ?_, ?_, hΘ⟩
  · rw [hΘ]
    exact (contDiff_radialContraction c hκ.le).contDiffOn
  · rw [hΘsymm, hΘtarget]
    have hAsymm' : ⇑A.symm = fun z => e.symm (r⁻¹⁻¹ • z) + c := funext hAsymm
    rw [hAsymm']
    exact ((e.symm.contDiff.comp (contDiff_id.const_smul _)).add contDiff_const).comp_contDiffOn
      (contDiffOn_univBall_symm.comp e.contDiff.contDiffOn fun z hz => hz)

/-- A radial contraction with nonnegative parameter is a topological embedding. -/
theorem isEmbedding_radialContraction (c : E) {κ : ℝ} (hκ : 0 ≤ κ) :
    Topology.IsEmbedding (radialContraction c κ) := by
  rcases hκ.eq_or_lt with rfl | hκ
  · have : radialContraction c 0 = id := funext (radialContraction_zero c)
    rw [this]
    exact Topology.IsEmbedding.id
  obtain ⟨Θ, hsource, -, -, hΘeq⟩ := exists_radialContraction_eq_openPartialHomeomorph c hκ
  exact hΘeq ▸ (Θ.isOpenEmbedding hsource).isEmbedding

/-- A radial contraction has derivative the identity at its centre. -/
theorem hasFDerivAt_radialContraction_self (c : E) (κ : ℝ) :
    HasFDerivAt (radialContraction c κ) (ContinuousLinearMap.id ℝ E) c := by
  have hq : (0 : ℝ) < 1 + κ * ‖toEuclidean (c - c)‖ ^ 2 := by simp
  have ha : DifferentiableAt ℝ (fun y : E => (√(1 + κ * ‖toEuclidean (y - c)‖ ^ 2))⁻¹) c :=
    (((contDiffAt_const.add (contDiffAt_const.mul ((contDiff_norm_sq ℝ).comp
      (toEuclidean.contDiff.comp (contDiff_id.sub contDiff_const))).contDiffAt)).sqrt hq.ne').inv
        (Real.sqrt_ne_zero'.mpr hq)).differentiableAt (n := 1) (by simp)
  convert (ha.hasFDerivAt.smul ((hasFDerivAt_id c).sub_const c)).const_add c using 1
  · ext v
    rw [radialContraction, Pi.smul_apply', id]
  · simp

/-- Precomposing with a radial contraction does not change the derivative at its centre. -/
theorem fderiv_comp_radialContraction_self {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : E → F} (c : E) (κ : ℝ) (hh : DifferentiableAt ℝ h c) :
    fderiv ℝ (h ∘ radialContraction c κ) c = fderiv ℝ h c := by
  have hh' : HasFDerivAt h (fderiv ℝ h c) (radialContraction c κ c) := by
    rw [radialContraction_self]
    exact hh.hasFDerivAt
  simpa using (hh'.comp c (hasFDerivAt_radialContraction_self c κ)).fderiv

end TauCeti
