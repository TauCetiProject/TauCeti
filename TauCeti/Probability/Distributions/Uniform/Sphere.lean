/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.MeasureTheory.Constructions.HaarToSphere
public import TauCeti.Probability.Distributions.Chi.Gaussian
public import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# The uniform law on the unit sphere

On a finite-dimensional real inner product space `E` of dimension `d ≥ 1`, the uniform law
`uniformSphereMeasure E` on the unit sphere is Mathlib's polar-coordinate surface measure
`volume.toSphere` normalized to total mass one. The surface measure has total mass
`2 π ^ (d / 2) / Γ (d / 2)` (`TauCeti.toSphere_volume_apply_univ`). In dimension zero the sphere
is empty and there is no probability law on it.

The uniform law is invariant under linear isometries, so its embedded mean vanishes. It is also
the law of the direction of a standard Gaussian vector, and that direction is independent of the
Gaussian radius, which has the chi law with `d` degrees of freedom. More generally, the direction
of any finite measure with a radial density against Lebesgue measure is uniform and independent
of the radius. The direction is read through `sphereDirection e`, which sends a nonzero vector `x`
to `‖x‖⁻¹ • x` and the origin to an assigned point `e` of the sphere; the origin is a null set
for these laws, so the results hold for every choice of `e`.

The radial factorization comes from the polar-coordinate formula
`TauCeti.lintegral_eq_lintegral_toSphere_lintegral_Ioi`, which is Mathlib's
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` read on integrals.

## Main definitions

* `TauCeti.Probability.uniformSphereMeasure`: the uniform law on the unit sphere.
* `TauCeti.Probability.sphereDirection`: the direction of a vector, with an assigned value at
  the origin.

## Main results

* `TauCeti.Probability.map_uniformSphereMeasure`: invariance under linear isometric
  equivalences.
* `TauCeti.Probability.integral_coe_uniformSphereMeasure`: the embedded mean is zero.
* `TauCeti.Probability.map_sphereDirection_prod_norm_withDensity`: the direction of a radial
  density is uniform and independent of the radius.
* `TauCeti.Probability.stdGaussian_map_sphereDirection_prod_norm`: the direction and radius of a
  standard Gaussian vector are independent, uniform on the sphere and chi distributed.
* `TauCeti.Probability.hasLaw_sphereDirection_of_hasLaw_stdGaussian`,
  `TauCeti.Probability.indepFun_sphereDirection_norm_of_hasLaw_stdGaussian`: the same statements
  for a random vector with standard Gaussian law.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, section 1.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace TauCeti.Probability

section UniformSphere

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

variable (E) in
/-- The uniform law on the unit sphere of a finite-dimensional real inner product space: the
surface measure `volume.toSphere` divided by its total mass. It is a probability measure in every
positive dimension; in dimension zero the sphere is empty. -/
def uniformSphereMeasure : Measure (sphere (0 : E) 1) :=
  ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere

variable (E) in
/-- The uniform law on the sphere is the normalized surface measure. -/
theorem uniformSphereMeasure_def :
    uniformSphereMeasure E =
      ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere := by
  rw [uniformSphereMeasure]

/-- The uniform law of a set of the sphere is its surface measure divided by the surface area
`2 π ^ (d / 2) / Γ (d / 2)` of the sphere. -/
theorem uniformSphereMeasure_apply (s : Set (sphere (0 : E) 1)) :
    uniformSphereMeasure E s = (volume : Measure E).toSphere s /
      ENNReal.ofReal (2 * Real.pi ^ ((Module.finrank ℝ E : ℝ) / 2) /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2)) := by
  rw [uniformSphereMeasure_def, Measure.smul_apply, smul_eq_mul, toSphere_volume_apply_univ,
    ENNReal.div_eq_inv_mul]

/-- In every positive dimension the uniform law on the sphere is a probability measure. -/
instance isProbabilityMeasure_uniformSphereMeasure [Nontrivial E] :
    IsProbabilityMeasure (uniformSphereMeasure E) where
  measure_univ := by
    rw [uniformSphereMeasure_def, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.2 (Measure.toSphere_ne_zero _))
      (measure_ne_top _ _)

/-- **Isometry invariance of the uniform sphere law.** A linear isometric equivalence, restricted
to the unit spheres, carries the uniform law on the sphere of `E` to the uniform law on the
sphere of `F`. With `F = E` this is invariance under orthogonal transformations. -/
theorem map_uniformSphereMeasure (f : E ≃ₗᵢ[ℝ] F) :
    (uniformSphereMeasure E).map (Subtype.map f fun x hx ↦ by simpa using hx) =
      uniformSphereMeasure F := by
  rw [uniformSphereMeasure_def, uniformSphereMeasure_def, Measure.map_smul, map_toSphere,
    f.measurePreserving.map_eq, toSphere_volume_apply_univ, toSphere_volume_apply_univ,
    f.toLinearEquiv.finrank_eq]
  exact (f.continuous.measurable.subtype_map _).aemeasurable

/-- The uniform law on the sphere has embedded mean zero. -/
theorem integral_coe_uniformSphereMeasure :
    ∫ x, (x : E) ∂uniformSphereMeasure E = 0 := by
  let f : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  set g : sphere (0 : E) 1 → sphere (0 : E) 1 := Subtype.map f fun x hx ↦ by simpa using hx
  have hg : Measurable g := f.continuous.measurable.subtype_map _
  have h := integral_map (μ := uniformSphereMeasure E) hg.aemeasurable
    (continuous_subtype_val.aestronglyMeasurable (f := ((↑) : sphere (0 : E) 1 → E)))
  rw [map_uniformSphereMeasure f] at h
  have hg' : ∀ x : sphere (0 : E) 1, (g x : E) = -(x : E) := fun x ↦ by
    simp only [g]
    rw [Subtype.map_coe]
    simp [f]
  simp_rw [hg', integral_neg] at h
  have h2 : (2 : ℝ) • ∫ x, (x : E) ∂uniformSphereMeasure E = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

end UniformSphere

section Direction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- The direction of a vector on the unit sphere: `‖x‖⁻¹ • x` for a nonzero vector `x`, and the
assigned point `e` of the sphere at the origin. -/
def sphereDirection (e : sphere (0 : E) 1) (x : E) : sphere (0 : E) 1 :=
  ⟨if x = 0 then e else NormedSpace.normalize x, by
    split_ifs with hx
    exacts [e.2, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)]⟩

variable (e : sphere (0 : E) 1) {x : E}

/-- The direction of the origin is the assigned point. -/
@[simp]
theorem sphereDirection_zero : sphereDirection e 0 = e := by
  simp [sphereDirection]

/-- The direction of a nonzero vector is its normalization. -/
theorem coe_sphereDirection_of_ne_zero (hx : x ≠ 0) :
    (sphereDirection e x : E) = NormedSpace.normalize x := by
  simp [sphereDirection, hx]

/-- A vector is its norm times its direction. -/
@[simp]
theorem norm_smul_sphereDirection (x : E) : ‖x‖ • (sphereDirection e x : E) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [coe_sphereDirection_of_ne_zero e hx, NormedSpace.norm_smul_normalize]

/-- A positive multiple of a point of the sphere has that point as its direction. -/
@[simp]
theorem sphereDirection_smul_of_pos {r : ℝ} (hr : 0 < r) (u : sphere (0 : E) 1) :
    sphereDirection e (r • (u : E)) = u := by
  have hu : (u : E) ≠ 0 := ne_zero_of_mem_sphere one_ne_zero u
  ext1
  rw [coe_sphereDirection_of_ne_zero e (smul_ne_zero hr.ne' hu),
    NormedSpace.normalize_smul_of_pos hr,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere u)]

/-- A point of the sphere is its own direction. -/
@[simp]
theorem sphereDirection_coe (u : sphere (0 : E) 1) : sphereDirection e (u : E) = u := by
  simpa using sphereDirection_smul_of_pos e one_pos u

/-- The direction map is measurable. -/
@[fun_prop]
theorem measurable_sphereDirection [MeasurableSpace E] [BorelSpace E] :
    Measurable (sphereDirection e) := by
  unfold sphereDirection NormedSpace.normalize
  refine Measurable.subtype_mk (Measurable.ite (measurableSet_singleton 0) measurable_const ?_)
  fun_prop

end Direction

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The direction of a radial law is uniform and independent of the radius.** If a finite
measure has a density against Lebesgue measure depending only on the norm, then its direction
and its radius are independent, and the direction is uniform on the sphere. The assigned
direction `e` of the origin is irrelevant since the origin is a null set. -/
theorem map_sphereDirection_prod_norm_withDensity (e : sphere (0 : E) 1) {φ : ℝ → ℝ≥0∞}
    (hφ : Measurable φ) [IsFiniteMeasure ((volume : Measure E).withDensity fun x ↦ φ ‖x‖)] :
    ((volume : Measure E).withDensity fun x ↦ φ ‖x‖).map (fun x ↦ (sphereDirection e x, ‖x‖)) =
      (uniformSphereMeasure E).prod
        (((volume : Measure E).withDensity fun x ↦ φ ‖x‖).map (‖·‖)) := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  set ν := (volume : Measure E).withDensity fun x ↦ φ ‖x‖
  set Φ : E → sphere (0 : E) 1 × ℝ := fun x ↦ (sphereDirection e x, ‖x‖)
  have hΦ : Measurable Φ := (measurable_sphereDirection e).prodMk measurable_norm
  -- In polar coordinates, the mass of a product set factors into a sphere part and a radial part.
  set K : Set ℝ → ℝ≥0∞ := fun t ↦
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * t.indicator φ r
  have key : ∀ s t, MeasurableSet s → MeasurableSet t →
      ν (Φ ⁻¹' (s ×ˢ t)) = (volume : Measure E).toSphere s * K t := by
    intro s t hs ht
    have hst : MeasurableSet (Φ ⁻¹' (s ×ˢ t)) := hΦ (hs.prod ht)
    rw [withDensity_apply _ hst, ← lintegral_indicator hst,
      lintegral_eq_lintegral_toSphere_lintegral_Ioi
        (f := (Φ ⁻¹' (s ×ˢ t)).indicator fun x ↦ φ ‖x‖)
        ((hφ.comp measurable_norm).indicator hst), mul_comm ((volume : Measure E).toSphere s),
      ← lintegral_indicator_const hs]
    refine lintegral_congr fun u ↦ ?_
    rw [← setLIntegral_congr_fun measurableSet_Ioi (f := fun r ↦
      s.indicator (fun _ ↦ ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * t.indicator φ r) u)]
    · by_cases hu : u ∈ s <;> simp [hu, K]
    · intro r hr
      have hr : 0 < r := hr
      have hnr : ‖r • (u : E)‖ = r := by simp [norm_smul, Real.norm_of_nonneg hr.le]
      have hΦr : Φ (r • (u : E)) = (u, r) := by simp [Φ, sphereDirection_smul_of_pos e hr, hnr]
      by_cases hu : u ∈ s <;> by_cases ht : r ∈ t <;> simp [hΦr, hnr, hu, ht]
  have hnorm : ∀ t, (‖·‖) ⁻¹' t = Φ ⁻¹' (univ ×ˢ t) := fun t ↦ by ext; simp [Φ]
  have hσ₀ : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.2 (Measure.toSphere_ne_zero _)
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  rw [Measure.map_apply hΦ (hs.prod ht), key s t hs ht, Measure.map_apply measurable_norm ht,
    hnorm, key univ t .univ ht, uniformSphereMeasure_def, Measure.smul_apply, smul_eq_mul,
    mul_comm _ ((volume : Measure E).toSphere s), mul_assoc, ← mul_assoc _ _ (K t),
    ENNReal.inv_mul_cancel hσ₀ (measure_ne_top _ _), one_mul]

/-- **The direction of a standard Gaussian vector is uniform and independent of its radius.**
The pair of the direction and the norm of a standard Gaussian vector has the product of the
uniform law on the sphere and the chi law with `d` degrees of freedom. -/
theorem stdGaussian_map_sphereDirection_prod_norm (e : sphere (0 : E) 1) :
    (stdGaussian E).map (fun x ↦ (sphereDirection e x, ‖x‖)) =
      (uniformSphereMeasure E).prod (chiMeasure (Module.finrank ℝ E) 1) := by
  set d := Module.finrank ℝ E
  set φ : ℝ → ℝ≥0∞ := fun r ↦
    ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / 2))
  have hφ : Measurable φ := by fun_prop
  -- Transport the isotropic density of the Euclidean standard Gaussian along an orthonormal basis.
  have hG : stdGaussian E = (volume : Measure E).withDensity fun x ↦ φ ‖x‖ := by
    let b := (stdOrthonormalBasis ℝ E).repr
    rw [← stdGaussian_map b.symm, stdGaussian_eq_withDensity, ← b.symm.coe_toHomeomorph,
      ← Homeomorph.toMeasurableEquiv_coe, MeasurableEquiv.map_withDensity,
      Homeomorph.toMeasurableEquiv_coe, b.symm.coe_toHomeomorph, b.symm.measurePreserving.map_eq]
    congr 1
    funext x
    simp [φ, d]
  have : IsFiniteMeasure ((volume : Measure E).withDensity fun x ↦ φ ‖x‖) := hG ▸ inferInstance
  rw [← stdGaussian_map_norm E, hG]
  exact map_sphereDirection_prod_norm_withDensity e hφ

/-- **The direction of a standard Gaussian vector is uniform on the sphere.** -/
theorem stdGaussian_map_sphereDirection (e : sphere (0 : E) 1) :
    (stdGaussian E).map (sphereDirection e) = uniformSphereMeasure E := by
  have := isProbabilityMeasure_chiMeasure (Nat.cast_nonneg (Module.finrank ℝ E)) one_pos
  have h := congrArg (Measure.map Prod.fst) (stdGaussian_map_sphereDirection_prod_norm e)
  rwa [Measure.map_map measurable_fst
    ((measurable_sphereDirection e).prodMk measurable_norm), Measure.map_fst_prod,
    measure_univ, one_smul] at h

end Radial

section RandomVariable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E}

/-- The direction of a random vector with standard Gaussian law is uniform on the sphere. -/
theorem hasLaw_sphereDirection_of_hasLaw_stdGaussian (hX : HasLaw X (stdGaussian E) P)
    (e : sphere (0 : E) 1) :
    HasLaw (fun ω ↦ sphereDirection e (X ω)) (uniformSphereMeasure E) P :=
  HasLaw.comp ⟨(measurable_sphereDirection e).aemeasurable, stdGaussian_map_sphereDirection e⟩ hX

/-- The direction of a random vector with standard Gaussian law is independent of its norm. -/
theorem indepFun_sphereDirection_norm_of_hasLaw_stdGaussian (hX : HasLaw X (stdGaussian E) P)
    (e : sphere (0 : E) 1) :
    IndepFun (fun ω ↦ sphereDirection e (X ω)) (fun ω ↦ ‖X ω‖) P := by
  have := hX.isProbabilityMeasure
  have hnorm : HasLaw (fun ω ↦ ‖X ω‖) (chiMeasure (Module.finrank ℝ E) 1) P :=
    HasLaw.comp ⟨measurable_norm.aemeasurable, stdGaussian_map_norm E⟩ hX
  refine (indepFun_iff_hasLaw_prodMk_prod
    (hasLaw_sphereDirection_of_hasLaw_stdGaussian hX e) hnorm).2 ?_
  exact HasLaw.comp ⟨((measurable_sphereDirection e).prodMk measurable_norm).aemeasurable,
    stdGaussian_map_sphereDirection_prod_norm e⟩ hX

end RandomVariable

end TauCeti.Probability
