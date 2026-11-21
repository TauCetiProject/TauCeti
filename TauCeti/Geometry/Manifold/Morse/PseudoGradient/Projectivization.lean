/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.EuclideanMetric
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Gradient
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Geometry.Manifold.Riemannian.Invariant
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Radial.Chart
import TauCeti.Data.Set.Card
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.InformationTheory.Coding.Equivalence
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Pseudo-gradients on real projective space invariant under the sign changes

The group `Fin (n + 1) → ℤˣ` of sign changes of the homogeneous coordinates acts on the real
projective space `ℝℙⁿ = ℙ ℝ (Fin (n + 1) → ℝ)` by diffeomorphisms, and preserves the moment function
`[v] ↦ (∑ i, w i * v i ^ 2) / ∑ i, v i ^ 2` (`TauCeti.projectiveMomentFunction_smul`). For pairwise
distinct weights this file constructs an adapted pseudo-gradient of the moment function which is
invariant under all sign changes
(`TauCeti.exists_isAdaptedPseudoGradient_projectiveMomentFunction_mfderiv_smul`). A sign change
fixing two critical points and exchanging two trajectories between them then compares the signs of
these trajectories in the integral Morse complex; on `ℝℙ²` with weights `w 0 < w 1 < w 2`, the
reflection `[x : y : z] ↦ [x : y : -z]` fixes the three critical points and exchanges the two
trajectories from the maximum `[e₂]` to the saddle `[e₁]`.

An adapted pseudo-gradient must be the linear field of a Morse chart near each critical point, so
averaging an arbitrary one over the group does not work: the averaged field is linear in no chart
unless the sign changes act linearly in the Morse charts. This file therefore writes down explicit
Morse charts of the moment function in which they do.

* **Morse charts.** At the coordinate point `[eₖ]`, with affine coordinates
  `z j = v (k.succAbove j) / v k`, the moment function is
  `w k + ∑ j, (w (k.succAbove j) - w k) z j ^ 2 / (1 + |z|²)`. So the affine chart followed by the
  radial chart `z ↦ z / √(1 + |z|²)` (`TauCeti.radialChart`, the Euclidean
  `OpenPartialHomeomorph.univUnitBall`), with the linear coordinates scaled by
  `√(2 |w (k.succAbove j) - w k|)`, is a Morse chart (`TauCeti.projectiveMomentMorseChart`). A sign
  change `ε` acts on the affine coordinates at `k` by the signs `ε (k.succAbove j) * ε k`
  (`TauCeti.affineChart_signs_smul`), and the radial chart commutes with such sign changes, so `ε`
  acts linearly in this Morse chart (`TauCeti.projectiveMomentMorseChart_toChart_smul`), by an
  isometry of its Euclidean metric (`TauCeti.projectiveMomentMorseChart_euclideanForm_smul`).
* **An invariant metric.** The points whose affine coordinates at `k` are at most `1 / 2` in
  absolute value form pairwise disjoint closed neighbourhoods of the critical points, invariant
  under the sign changes. A metric equal to the Euclidean metrics of the Morse charts there,
  averaged over the finite group of sign changes (`TauCeti.averageRiemannianMetric`), is invariant
  and still Euclidean in the Morse charts
  (`TauCeti.exists_signs_invariant_contMDiffRiemannianMetric_projectiveMomentFunction`).
* **An invariant pseudo-gradient.** The negative gradient of this metric is an adapted
  pseudo-gradient (`TauCeti.isAdaptedPseudoGradient_neg_mgradient`), and, as the gradient of an
  invariant function for an invariant metric, it commutes with the sign changes.

## Main declarations

* `TauCeti.projectiveMomentMorseChart`: an explicit Morse chart of the moment function at `[eₖ]`.
* `TauCeti.projectiveMomentMorseChart_toChart_smul`: the sign changes act linearly in it.
* `TauCeti.exists_signs_invariant_contMDiffRiemannianMetric_projectiveMomentFunction`: a metric
  invariant under the sign changes and Euclidean in Morse charts at the critical points.
* `TauCeti.exists_isAdaptedPseudoGradient_projectiveMomentFunction_mfderiv_smul`: an adapted
  pseudo-gradient invariant under the sign changes.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.2 (adapted pseudo-gradients) and Chapter 4 (the Morse complex of `ℝℙ²`).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the integral Morse complex of `ℝℙ²`, by symmetry).
-/

public section

open Bundle Function Set Projectivization TauCeti.Manifold
open scoped LinearAlgebra.Projectivization Manifold ContDiff

namespace TauCeti

variable {n : ℕ}

/-! ### Explicit Morse charts of the moment function -/

variable {w : Fin (n + 1) → ℝ} {k : Fin (n + 1)}

/-- The scaling factor `√(2 |w (k.succAbove j) - w k|)` of the `j`-th Morse coordinate of the moment
function at `[eₖ]`. -/
noncomputable def projectiveMomentScale (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)) (j : Fin n) : ℝ :=
  √(2 * |w (k.succAbove j) - w k|)

/-- The square of the scaling factor of the `j`-th Morse coordinate is
`2 |w (k.succAbove j) - w k|`. -/
theorem sq_projectiveMomentScale (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)) (j : Fin n) :
    projectiveMomentScale w k j ^ 2 = 2 * |w (k.succAbove j) - w k| :=
  Real.sq_sqrt (by positivity)

/-- The Morse coordinates are scaled by positive factors when `w k` differs from the other
weights. -/
theorem projectiveMomentScale_pos (hk : ∀ i, i ≠ k → w i ≠ w k) (j : Fin n) :
    0 < projectiveMomentScale w k j :=
  Real.sqrt_pos.2 (mul_pos two_pos
    (abs_pos.2 (sub_ne_zero.2 (hk _ (Fin.succAbove_ne k j)))))

/-- The linear coordinates of the Morse chart of the moment function at `[eₖ]`: the `j`-th
coordinate is scaled by `projectiveMomentScale w k j`. -/
noncomputable def projectiveMomentCoord (hk : ∀ i, i ≠ k → w i ≠ w k) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Fin n → ℝ)) → ℝ) :=
  (LinearEquiv.piCongrRight fun j ↦ LinearEquiv.smulOfNeZero ℝ ℝ _
    (projectiveMomentScale_pos hk j).ne').trans
      (LinearEquiv.funCongrLeft ℝ ℝ (finCongr (Module.finrank_fin_fun ℝ)))

/-- The `i`-th Morse coordinate at `[eₖ]` is the scaled affine coordinate of the same index. -/
theorem projectiveMomentCoord_apply (hk : ∀ i, i ≠ k → w i ≠ w k) (z : Fin n → ℝ)
    (i : Fin (Module.finrank ℝ (Fin n → ℝ))) :
    projectiveMomentCoord hk z i =
      projectiveMomentScale w k (finCongr (Module.finrank_fin_fun ℝ) i) *
        z (finCongr (Module.finrank_fin_fun ℝ) i) :=
  (rfl)

/-- **An explicit Morse chart of the moment function on real projective space.** At the coordinate
point `[eₖ]`, where the weight `w k` differs from all others, the affine chart at `k` followed by
the radial chart `z ↦ z / √(1 + |z|²)` is a Morse chart: with the coordinates
`ζ j = √(2 |w (k.succAbove j) - w k|) z j / √(1 + |z|²)` the moment function is
`w k + (1/2) ∑ j, sign (w (k.succAbove j) - w k) ζ j ^ 2`. -/
noncomputable def projectiveMomentMorseChart (hk : ∀ i, i ≠ k → w i ≠ w k) :
    MorseChart (Fin n → ℝ) (projectiveMomentFunction ℝ w) (mk ℝ (Pi.single k 1) (by simp)) where
  toChart := (affineOpenPartialHomeomorph k).trans radialChart
  mem_maximalAtlas := by
    have hA := affineOpenPartialHomeomorph_mem_maximalAtlas (𝕜 := ℝ) (n := n)
      (I := 𝓘(ℝ, Fin n → ℝ)) (r := ∞) k
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · exact contDiff_radialChart.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas hA).mono inter_subset_left)
    · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      exact (contMDiffOn_symm_of_mem_maximalAtlas hA).comp
        (contDiffOn_radialChart_symm.contMDiffOn.mono inter_subset_left) fun z hz ↦ hz.2
  mem_source := by simp
  apply_self := by
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply, coe_affineOpenPartialHomeomorph,
      affineChart_mk_single, radialChart_apply, smul_zero]
  coord := projectiveMomentCoord hk
  weight i := if w k < w (k.succAbove (finCongr (Module.finrank_fin_fun ℝ) i)) then 1 else -1
  weight_eq_neg_one_or_eq_one i := by split_ifs <;> simp
  ncard_weight_neg := by
    rw [manifoldMorseIndex_projectiveMomentFunction, Module.finrank_self, one_mul]
    -- A weight is negative exactly when the corresponding weight of `w` lies below `w k`.
    have hpre : {i | (if w k < w (k.succAbove (finCongr (Module.finrank_fin_fun ℝ) i)) then (1 : ℝ)
        else -1) < 0} =
          finCongr (Module.finrank_fin_fun ℝ) ⁻¹' (k.succAbove ⁻¹' {i | w i < w k}) := by
      ext i
      simp only [mem_ofPred_eq, mem_preimage]
      split_ifs with h
      · exact iff_of_false (by norm_num) (not_lt.2 h.le)
      · exact iff_of_true (by norm_num) (lt_of_le_of_ne (not_lt.1 h) (hk _ (Fin.succAbove_ne k _)))
    rw [hpre, ncard_preimage_of_injective_subset_range (finCongr _).injective
      fun i _ ↦ (finCongr _).surjective i, ncard_preimage_succAbove,
      sdiff_singleton_eq_self (lt_irrefl (w k))]
  eq_quadratic y hy := by
    have hy' : y ∈ affineOpen k := by simpa using hy.1
    set z := affineChart k y with hz
    have hfy : projectiveMomentFunction ℝ w y = ProjectiveMomentChart.model ℝ (w k)
        (w ∘ k.succAbove) z := by
      rw [← projectiveMomentFunction_comp_affineChart_symm, comp_apply,
        (affineChart (K := ℝ) k).left_inv (by simpa using hy')]
    rw [hfy, projectiveMomentFunction_mk_single, ProjectiveMomentChart.model_apply]
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply, coe_affineOpenPartialHomeomorph,
      ← hz, radialChart_apply, projectiveMomentCoord_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Equiv.sum_comp (finCongr (Module.finrank_fin_fun ℝ)).symm]
    simp only [Equiv.apply_symm_apply, Real.norm_eq_abs, sq_abs]
    have hS : 0 < 1 + ∑ j, z j ^ 2 := by positivity
    have hterm (j : Fin n) : (if w k < w (k.succAbove j) then (1 : ℝ) else -1) *
        (projectiveMomentScale w k j * ((√(1 + ∑ j, z j ^ 2))⁻¹ * z j)) ^ 2 =
          2 * (w (k.succAbove j) - w k) * z j ^ 2 / (1 + ∑ j, z j ^ 2) := by
      rw [mul_pow, mul_pow, sq_projectiveMomentScale, inv_pow, Real.sq_sqrt hS.le]
      split_ifs with h
      · rw [abs_of_pos (sub_pos.2 h)]
        field_simp
      · rw [abs_of_neg (sub_neg.2 (lt_of_le_of_ne (not_lt.1 h) (hk _ (Fin.succAbove_ne k j))))]
        field_simp
    have hsum : ∑ i, 2 * (w (k.succAbove i) - w k) * z i ^ 2 / (1 + ∑ j, z j ^ 2) =
        2 * ((∑ i, w (k.succAbove i) * z i ^ 2) - w k * ∑ i, z i ^ 2) / (1 + ∑ j, z j ^ 2) := by
      rw [← Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact congrArg (· / _) (Finset.sum_congr rfl fun i _ ↦ by ring)
    simp only [hterm, hsum]
    field_simp
    ring

/-- The chart map of `projectiveMomentMorseChart` is the affine chart at `k` followed by the
radial chart. -/
theorem projectiveMomentMorseChart_toChart (hk : ∀ i, i ≠ k → w i ≠ w k) :
    (projectiveMomentMorseChart hk).toChart = (affineOpenPartialHomeomorph k).trans radialChart :=
  (rfl)

/-- The Morse chart at `[eₖ]` is defined on the affine open set of the chart at `k`. -/
@[simp]
theorem projectiveMomentMorseChart_source (hk : ∀ i, i ≠ k → w i ≠ w k) :
    (projectiveMomentMorseChart hk).toChart.source = affineOpen k := by
  simp [projectiveMomentMorseChart_toChart]

/-- The linear coordinates of `projectiveMomentMorseChart` are `projectiveMomentCoord`. -/
theorem projectiveMomentMorseChart_coord (hk : ∀ i, i ≠ k → w i ≠ w k) :
    (projectiveMomentMorseChart hk).coord = projectiveMomentCoord hk :=
  (rfl)

/-- The `i`-th Morse coordinate at `[eₖ]` has weight `1` when `w (k.succAbove i)` exceeds `w k`,
and `-1` otherwise. -/
theorem projectiveMomentMorseChart_weight (hk : ∀ i, i ≠ k → w i ≠ w k)
    (i : Fin (Module.finrank ℝ (Fin n → ℝ))) :
    (projectiveMomentMorseChart hk).weight i =
      if w k < w (k.succAbove (finCongr (Module.finrank_fin_fun ℝ) i)) then 1 else -1 :=
  (rfl)

/-! ### The sign changes in the Morse charts -/

/-- The Morse chart of the moment function at `[eₖ]` turns the sign change `ε` into the change of
signs `chartSigns ε k` of its coordinates. -/
theorem projectiveMomentMorseChart_toChart_smul (hk : ∀ i, i ≠ k → w i ≠ w k)
    (ε : Fin (n + 1) → ℤˣ) (y : ℙ ℝ (Fin (n + 1) → ℝ)) :
    (projectiveMomentMorseChart hk).toChart (ε • y) =
      chartSigns ε k • (projectiveMomentMorseChart hk).toChart y := by
  simp only [projectiveMomentMorseChart_toChart, OpenPartialHomeomorph.coe_trans, comp_apply,
    coe_affineOpenPartialHomeomorph, affineChart_signs_smul, radialChart_smul]

/-- The scaled coordinates commute with changes of sign of the coordinates. -/
theorem projectiveMomentCoord_smul (hk : ∀ i, i ≠ k → w i ≠ w k) (δ : Fin n → ℤˣ)
    (z : Fin n → ℝ) :
    projectiveMomentCoord hk (δ • z) =
      (δ ∘ finCongr (Module.finrank_fin_fun ℝ)) • projectiveMomentCoord hk z := by
  ext i
  simp only [projectiveMomentCoord_apply, Pi.smul_apply', comp_apply, Units.smul_def,
    zsmul_eq_mul]
  ring

/-- **The sign changes are isometries of the Euclidean metric of the Morse chart** of the moment
function at `[eₖ]`. -/
theorem projectiveMomentMorseChart_euclideanForm_smul (hk : ∀ i, i ≠ k → w i ≠ w k)
    (ε : Fin (n + 1) → ℤˣ) {y : ℙ ℝ (Fin (n + 1) → ℝ)}
    (hy : y ∈ (projectiveMomentMorseChart hk).toChart.source)
    (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
    (projectiveMomentMorseChart hk).euclideanForm (ε • y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) y u)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) y v) =
      (projectiveMomentMorseChart hk).euclideanForm y u v := by
  set φ := projectiveMomentMorseChart hk
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (DistribSMul.toLinearMap ℝ (Fin n → ℝ) (chartSigns ε k))
  have hsrc : ε • y ∈ φ.toChart.source := by simpa [φ] using hy
  have hcomp : (φ.toChart : _ → _) ∘ (ε • ·) = L ∘ φ.toChart :=
    funext fun y ↦ projectiveMomentMorseChart_toChart_smul hk ε y
  have hε : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (fun x : ℙ ℝ (Fin (n + 1) → ℝ) ↦ ε • x) y :=
    (contMDiff_const_smul ε : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) 1 _).mdifferentiableAt
      (by simp)
  have hd (a : TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) φ.toChart (ε • y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) y a) =
          L (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) φ.toChart y a : Fin n → ℝ) := by
    have h1 := mfderiv_comp (f := fun x : ℙ ℝ (Fin (n + 1) → ℝ) ↦ ε • x) (x := y)
      (φ.mdifferentiableAt_toChart hsrc) hε
    have h2 := mfderiv_comp (g := L) (f := φ.toChart) (x := y) L.mdifferentiableAt
      (φ.mdifferentiableAt_toChart hy)
    rw [hcomp, h2, L.mfderiv_eq] at h1
    exact (congrArg (· a) h1).symm
  have hdot (a b : Fin n → ℝ) : projectiveMomentCoord hk (L a) ⬝ᵥ projectiveMomentCoord hk (L b) =
      projectiveMomentCoord hk a ⬝ᵥ projectiveMomentCoord hk b := by
    simp only [L, LinearMap.coe_toContinuousLinearMap', DistribSMul.toLinearMap_apply]
    have hδ (c : Fin (Module.finrank ℝ (Fin n → ℝ)) → ℝ) :
        (chartSigns ε k ∘ finCongr (Module.finrank_fin_fun ℝ)) • c =
          signedEquiv (chartSigns ε k ∘ finCongr (Module.finrank_fin_fun ℝ)) (Equiv.refl _) c := by
      ext i
      simp only [Pi.smul_apply', Units.smul_def, zsmul_eq_mul, signedEquiv_apply,
        Equiv.refl_symm, Equiv.refl_apply]
    rw [projectiveMomentCoord_smul, projectiveMomentCoord_smul, hδ, hδ, dotProduct_signedEquiv]
  simp only [MorseChart.euclideanForm_apply, hd, φ, projectiveMomentMorseChart_coord]
  -- Tangent vectors of `Fin n → ℝ` are its elements.
  exact hdot _ _

/-! ### An invariant metric and an invariant pseudo-gradient -/

/-- The closed set of points whose affine coordinates at `k` are at most `1 / 2` in absolute
value. -/
private noncomputable def nearCoordinatePoint (k : Fin (n + 1)) : Set (ℙ ℝ (Fin (n + 1) → ℝ)) :=
  (affineChart k).symm '' Metric.closedBall 0 (1 / 2)

private theorem isClosed_nearCoordinatePoint (k : Fin (n + 1)) :
    IsClosed (nearCoordinatePoint k) :=
  ((isCompact_closedBall _ _).image (continuous_affineChart_symm k)).isClosed

private theorem nearCoordinatePoint_subset_affineOpen (k : Fin (n + 1)) :
    nearCoordinatePoint k ⊆ affineOpen (K := ℝ) k := by
  rintro _ ⟨z, -, rfl⟩
  simp

private theorem abs_affineChart_le_of_mem_nearCoordinatePoint {k : Fin (n + 1)}
    {x : ℙ ℝ (Fin (n + 1) → ℝ)} (hx : x ∈ nearCoordinatePoint k) (j : Fin n) :
    |affineChart k x j| ≤ 1 / 2 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [(affineChart (K := ℝ) k).right_inv (by simp), ← Real.norm_eq_abs]
  exact (norm_le_pi_norm z j).trans (mem_closedBall_zero_iff.1 hz)

private theorem pairwise_disjoint_nearCoordinatePoint :
    Pairwise (Disjoint on nearCoordinatePoint (n := n)) := by
  intro k l hkl
  refine Set.disjoint_left.2 fun x hk hl ↦ ?_
  have hk0 := nearCoordinatePoint_subset_affineOpen k hk
  have hl0 := nearCoordinatePoint_subset_affineOpen l hl
  obtain ⟨j₁, hj₁⟩ := Fin.exists_succAbove_eq hkl
  obtain ⟨j₂, hj₂⟩ := Fin.exists_succAbove_eq (Ne.symm hkl)
  have h₁ := abs_affineChart_le_of_mem_nearCoordinatePoint hl j₁
  have h₂ := abs_affineChart_le_of_mem_nearCoordinatePoint hk j₂
  induction x using ind with | h v hv =>
  rw [mk_mem_affineOpen_iff] at hk0 hl0
  simp only [affineChart_mk, hj₁, hj₂] at h₁ h₂
  have h1 : |v k / v l| * |v l / v k| = 1 := by
    rw [← abs_mul, div_mul_div_comm, mul_comm (v k), div_self (mul_ne_zero hl0 hk0), abs_one]
  nlinarith [abs_nonneg (v k / v l), abs_nonneg (v l / v k)]

private theorem smul_mem_nearCoordinatePoint {k : Fin (n + 1)} (ε : Fin (n + 1) → ℤˣ)
    {x : ℙ ℝ (Fin (n + 1) → ℝ)} (hx : x ∈ nearCoordinatePoint k) :
    ε • x ∈ nearCoordinatePoint k := by
  have hx0 := nearCoordinatePoint_subset_affineOpen k hx
  have hεx : ε • x ∈ (affineChart (K := ℝ) k).source := by
    simpa using hx0
  refine ⟨affineChart k (ε • x), ?_, (affineChart (K := ℝ) k).left_inv hεx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j
  rw [affineChart_signs_smul, Pi.smul_apply']
  rw [norm_units_zsmul, Real.norm_eq_abs]
  exact abs_affineChart_le_of_mem_nearCoordinatePoint hx j

/-- **A metric on real projective space invariant under the sign changes, Euclidean in Morse
charts.** For pairwise distinct weights `w`, there is a smooth Riemannian metric on `ℝℙⁿ` for which
every sign change of the homogeneous coordinates is an isometry, and which near each critical point
`[eₖ]` of the moment function is the Euclidean metric of a Morse chart. -/
theorem exists_signs_invariant_contMDiffRiemannianMetric_projectiveMomentFunction
    {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ)
        (fun x : ℙ ℝ (Fin (n + 1) → ℝ) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ (ε : Fin (n + 1) → ℤˣ) x (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
        g.inner (ε • x) (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) x u)
          (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) x v) = g.inner x u v) ∧
      ∀ k, ∃ φ : MorseChart (Fin n → ℝ) (projectiveMomentFunction ℝ w)
          (mk ℝ (Pi.single k 1) (by simp)),
        ∀ y ∈ φ.toChart.source, g.inner y = φ.euclideanForm y := by
  have hk (k : Fin (n + 1)) : ∀ i, i ≠ k → w i ≠ w k := fun i hi ↦ hw.ne hi
  let φ (k : Fin (n + 1)) := projectiveMomentMorseChart (hk k)
  have hAsub (k : Fin (n + 1)) : nearCoordinatePoint k ⊆ (φ k).toChart.source := fun x hx ↦ by
    simpa [φ] using nearCoordinatePoint_subset_affineOpen k hx
  -- Extend the Euclidean metrics of the Morse charts from the sets `nearCoordinatePoint k`.
  obtain ⟨g₀, hg₀⟩ := exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite
    (U := fun k ↦ (φ k).toChart.source) (β := fun k ↦ (φ k).euclideanForm)
    isClosed_nearCoordinatePoint (locallyFinite_of_finite _) pairwise_disjoint_nearCoordinatePoint
    (fun k ↦ (φ k).toChart.open_source) hAsub (fun k ↦ (φ k).contMDiffOn_euclideanForm)
    (fun k _ _ ↦ (φ k).euclideanForm_comm _) fun k _ hy _ hv ↦ (φ k).euclideanForm_self_pos hy hv
  -- Average it over the sign changes.
  let g := averageRiemannianMetric (Fin (n + 1) → ℤˣ) g₀
  have hgA (k : Fin (n + 1)) : ∀ y ∈ nearCoordinatePoint k, g.inner y = (φ k).euclideanForm y := by
    intro y hy
    ext u v
    rw [averageRiemannianMetric_inner]
    have hterm (ε : Fin (n + 1) → ℤˣ) : g₀.inner (ε • y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) y u)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) y v) = (φ k).euclideanForm y u v := by
      rw [hg₀ k _ (smul_mem_nearCoordinatePoint ε hy)]
      exact projectiveMomentMorseChart_euclideanForm_smul (hk k) ε (hAsub k hy) u v
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  refine ⟨g, averageRiemannianMetric_inner_mfderiv _ g₀, fun k ↦ ?_⟩
  -- Restrict the Morse chart at `[eₖ]` to the open set of points with coordinates below `1 / 2`.
  have hopen : IsOpen ((affineChart (K := ℝ) k).symm '' Metric.ball 0 (1 / 2)) :=
    (isOpenEmbedding_affineChart_symm k).isOpenMap _ Metric.isOpen_ball
  have hmem : mk ℝ (Pi.single k 1) (by simp) ∈
      (affineChart (K := ℝ) k).symm '' Metric.ball 0 (1 / 2) :=
    ⟨0, by simp, affineChart_symm_zero k⟩
  refine ⟨(φ k).restr hopen hmem, fun y hy ↦ ?_⟩
  rw [MorseChart.restr_euclideanForm]
  rw [MorseChart.restr_source] at hy
  exact hgA k y (image_mono Metric.ball_subset_closedBall hy.2)

/-- **An adapted pseudo-gradient on real projective space invariant under the sign changes.** For
pairwise distinct weights `w`, the moment function on `ℝℙⁿ` has an adapted pseudo-gradient `X`
which commutes with every sign change `ε` of the homogeneous coordinates: `dε (X x) = X (ε • x)`.
It is the negative gradient of the metric of
`TauCeti.exists_signs_invariant_contMDiffRiemannianMetric_projectiveMomentFunction`. -/
theorem exists_isAdaptedPseudoGradient_projectiveMomentFunction_mfderiv_smul
    {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    ∃ X : (x : ℙ ℝ (Fin (n + 1) → ℝ)) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X ∧
        ∀ (ε : Fin (n + 1) → ℤˣ) x,
          mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ε • ·) x (X x) = X (ε • x) := by
  obtain ⟨g, hiso, hφ⟩ :=
    exists_signs_invariant_contMDiffRiemannianMetric_projectiveMomentFunction hw
  let : RiemannianBundle (fun x : ℙ ℝ (Fin (n + 1) → ℝ) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :=
    ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ)
      (fun x : ℙ ℝ (Fin (n + 1) → ℝ) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :=
    ⟨⟨g.inner, g.contMDiff, g.inner_eq⟩⟩
  have hf := isMorse_projectiveMomentFunction (𝕜 := ℝ) hw
  refine ⟨fun y ↦ -mgradient 𝓘(ℝ, Fin n → ℝ) (projectiveMomentFunction ℝ w) y,
    isAdaptedPseudoGradient_neg_mgradient hf.contMDiff fun x hx ↦ ?_, fun ε x ↦ ?_⟩
  · have hx' := mem_criticalPoints_iff_mfderiv_eq_zero.2 hx
    rw [criticalPoints_projectiveMomentFunction hw] at hx'
    obtain ⟨k, rfl⟩ := hx'
    obtain ⟨φ, hφk⟩ := hφ k
    exact ⟨φ, φ.isEuclidean_iff_euclideanForm.2 fun y hy u v ↦ by rw [g.inner_eq, hφk y hy]⟩
  -- The gradient of an invariant function for an invariant metric is equivariant.
  have hloc : IsLocalRiemannianIsometry 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (fun x : ℙ ℝ (Fin (n + 1) → ℝ) ↦ ε • x) :=
    { contMDiff := contMDiff_const_smul ε
      isInvertible_mfderiv := fun x ↦ by
        have h := (Diffeomorph.constSmul 𝓘(ℝ, Fin n → ℝ) 1 ε :
          ℙ ℝ (Fin (n + 1) → ℝ) ≃ₘ^1⟮_, _⟯ _).isInvertible_mfderiv (x := x) one_ne_zero
        rwa [Diffeomorph.coe_constSmul] at h
      inner_mfderiv := fun x u v ↦ by rw [g.inner_eq, g.inner_eq, hiso] }
  have h := hloc.mfderiv_mgradient_comp (hf.contMDiff.mdifferentiableAt (by simp) (x := ε • x))
  rw [show projectiveMomentFunction ℝ w ∘ (ε • ·) = projectiveMomentFunction ℝ w from
    funext (projectiveMomentFunction_smul w ε)] at h
  rw [map_neg, h]

end TauCeti
