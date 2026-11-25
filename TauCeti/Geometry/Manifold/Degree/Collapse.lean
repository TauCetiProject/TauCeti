/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Degree.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Basic
import TauCeti.Analysis.InnerProductSpace.OrthogonalSpanSingleton
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# Maps to a sphere with a regular value of one preimage

Let `M` be a Hausdorff boundaryless smooth manifold modelled on a real normed space `W` of
dimension `n`, and let `Sⁿ` be the unit sphere of a real inner product space `E` of dimension
`n + 1`. For every point `x₀ ∈ M` this file constructs a smooth map `f : M → Sⁿ` and a point
`y ∈ Sⁿ` such that `y` is a regular value of `f` whose fibre is the single point `x₀`
(`TauCeti.exists_contMDiff_sphere_isRegularValue_preimage_eq_singleton`). For orientations of `M`
and of `Sⁿ` the signed count of this fibre is therefore `1` or `-1`
(`TauCeti.exists_contMDiff_sphere_degreeAtRegularValue_eq_one_or_eq_neg_one`), so when `M` is
compact and `1 ≤ n`, so that `Sⁿ` is connected, the map has degree `±1`: it is a smooth model of
the map collapsing the complement of a coordinate ball to a point.

The map is built in a chart at `x₀`. Fix a unit vector `e` of `E` and a linear isomorphism `L` of
`W` onto the hyperplane `e^⊥`, and a smooth bump function `β` on `W` equal to `1` near the image
`c` of `x₀` and vanishing outside a ball `B` around `c` inside the chart. The vector
`v z = β z • L (z - c) + (1 - 2 β z) • e` never vanishes, so `z ↦ v z / ‖v z‖` is a smooth map
`W → Sⁿ`. It equals the north pole `e` outside `B`, so read in the chart it extends by `e` to a
smooth map on `M` (`TauCeti.Manifold.exists_contMDiff_eq_comp_extChartAt`). It takes the value
`-e` only at `c`, and its projection to `e^⊥ ≅ W` is `(β z / ‖v z‖) • (z - c)`, whose derivative at
`c` is the identity, so its derivative at `c` is injective.

## Main results

* `TauCeti.exists_contMDiff_sphere_isRegularValue_preimage_eq_singleton`: a smooth map
  `M → Sⁿ` with a regular value whose fibre is one given point.
* `TauCeti.exists_contMDiff_sphere_degreeAtRegularValue_eq_one_or_eq_neg_one`: for orientations
  of `M` and `Sⁿ`, the signed count of that fibre is `±1`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §§5–7 (the degree and the collapse maps of the Pontryagin construction).
-/

public section

noncomputable section

open Function Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace TauCeti

/-! ### The bubble map of a vector space -/

section Bubble

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {c : W} (β : ContDiffBump c) (L : W →L[ℝ] E) (P : E →L[ℝ] W) (e : E)

/-- The vector `β z • L (z - c) + (1 - 2 β z) • e`, which never vanishes when `L` is injective
onto a complement of `e` (`TauCeti.bubbleVec_ne_zero`). -/
private def bubbleVec (z : W) : E :=
  β z • L (z - c) + (1 - 2 * β z) • e

/-- The normalized bubble vector, a map from `W` to the unit sphere when the bubble vector does
not vanish. -/
private def bubbleNormalized (z : W) : E :=
  ‖bubbleVec β L e z‖⁻¹ • bubbleVec β L e z

variable {L P e}

/-- At the centre the bubble vector is `-e`. -/
private theorem bubbleVec_center : bubbleVec β L e c = -e := by
  rw [bubbleVec, β.apply_center, sub_self, map_zero, smul_zero, zero_add]
  norm_num

/-- The bubble vector never vanishes: its component along `e` is `1 - 2 β z`, and its component
`β z • (z - c)` in `W` vanishes only where `β z = 0` or `z = c`, where `β = 1`. -/
private theorem bubbleVec_ne_zero (hPL : ∀ w, P (L w) = w) (hPe : P e = 0)
    (hLe : ∀ w, ⟪L w, e⟫ = 0) (he : ‖e‖ = 1) (z : W) : bubbleVec β L e z ≠ 0 := by
  intro h
  have h₁ := congrArg (fun v ↦ ⟪v, e⟫) h
  have h₂ := congrArg P h
  simp only [bubbleVec, inner_add_left, inner_smul_left, hLe, real_inner_self_eq_norm_sq, he,
    inner_zero_left, map_add, map_smul, hPL, hPe, smul_zero, add_zero, map_zero] at h₁ h₂
  have hβ : β z = 1 / 2 := by simp at h₁; linarith
  rcases smul_eq_zero.1 h₂ with h₃ | h₃
  · rw [hβ] at h₃; norm_num at h₃
  · rw [sub_eq_zero.1 h₃, β.apply_center] at hβ
    norm_num at hβ

/-- The projection of the normalized bubble vector to `W` is `(β z / ‖v z‖) • (z - c)`. -/
private theorem apply_bubbleNormalized (hPL : ∀ w, P (L w) = w) (hPe : P e = 0) (z : W) :
    P (bubbleNormalized β L e z) = (‖bubbleVec β L e z‖⁻¹ * β z) • (z - c) := by
  simp [bubbleNormalized, bubbleVec, hPL, hPe, smul_smul]

/-- Outside the outer ball of the bump, the normalized bubble vector is `e`. -/
private theorem bubbleNormalized_of_le_dist (he : ‖e‖ = 1) {z : W} (hz : β.rOut ≤ dist z c) :
    bubbleNormalized β L e z = e := by
  simp only [bubbleNormalized, bubbleVec, β.zero_of_le_dist hz, map_sub, zero_smul, mul_zero,
    sub_zero, one_smul, zero_add, he, inv_one]

/-- At the centre the normalized bubble vector is `-e`. -/
private theorem bubbleNormalized_self (he : ‖e‖ = 1) : bubbleNormalized β L e c = -e := by
  rw [bubbleNormalized, bubbleVec_center, norm_neg, he, inv_one, one_smul]

/-- The normalized bubble vector is `-e` only at the centre. -/
private theorem eq_of_bubbleNormalized_eq_neg (hPL : ∀ w, P (L w) = w) (hPe : P e = 0)
    (hLe : ∀ w, ⟪L w, e⟫ = 0) (he : ‖e‖ = 1) {z : W} (hz : bubbleNormalized β L e z = -e) :
    z = c := by
  have h := congrArg P hz
  rw [apply_bubbleNormalized β hPL hPe, map_neg, hPe, neg_zero] at h
  rcases smul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (inv_eq_zero.1 h) (norm_ne_zero_iff.2 (bubbleVec_ne_zero β hPL hPe hLe he z))
    · -- Where the bump vanishes, the bubble vector is `e`, not `-e`.
      have h' : bubbleNormalized β L e z = e := by simp [bubbleNormalized, bubbleVec, h, he]
      rw [h'] at hz
      exact (ne_neg_of_mem_unit_sphere ℝ ⟨e, by simp [he]⟩ (Subtype.ext hz)).elim
  · exact sub_eq_zero.1 h

/-- The bubble vector is smooth. -/
private theorem contDiff_bubbleVec : ContDiff ℝ ∞ (bubbleVec β L e) :=
  (β.contDiff.smul (L.contDiff.comp (contDiff_id.sub contDiff_const))).add
    ((contDiff_const.sub (contDiff_const.mul β.contDiff)).smul contDiff_const)

/-- The normalized bubble vector is smooth. -/
private theorem contDiff_bubbleNormalized (hPL : ∀ w, P (L w) = w) (hPe : P e = 0)
    (hLe : ∀ w, ⟪L w, e⟫ = 0) (he : ‖e‖ = 1) : ContDiff ℝ ∞ (bubbleNormalized β L e) :=
  ((contDiff_bubbleVec β).norm ℝ (bubbleVec_ne_zero β hPL hPe hLe he)).inv
      (fun z ↦ norm_ne_zero_iff.2 (bubbleVec_ne_zero β hPL hPe hLe he z)) |>.smul
    (contDiff_bubbleVec β)

/-- The derivative of the normalized bubble vector at the centre is injective: its projection
to `W` has derivative the identity there. -/
private theorem injective_fderiv_bubbleNormalized (hPL : ∀ w, P (L w) = w) (hPe : P e = 0)
    (hLe : ∀ w, ⟪L w, e⟫ = 0) (he : ‖e‖ = 1) :
    Injective (fderiv ℝ (bubbleNormalized β L e) c) := by
  have hne := bubbleVec_ne_zero β hPL hPe hLe he
  have hd : Differentiable ℝ (bubbleNormalized β L e) :=
    (contDiff_bubbleNormalized β hPL hPe hLe he).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  -- The scalar `‖v z‖⁻¹ * β z` is differentiable and equals `1` at the centre.
  have hn : DifferentiableAt ℝ (fun z ↦ ‖bubbleVec β L e z‖) c :=
    (((contDiff_bubbleVec β).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)) c).norm ℝ (hne c)
  have hs : DifferentiableAt ℝ (fun z ↦ ‖bubbleVec β L e z‖⁻¹ * β z) c :=
    (hn.inv (norm_ne_zero_iff.2 (hne c))).mul
      (β.contDiff.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) c)
  have hs1 : ‖bubbleVec β L e c‖⁻¹ * β c = 1 := by
    rw [bubbleVec_center, β.apply_center, norm_neg, he, inv_one, one_mul]
  have hP : HasFDerivAt (fun z ↦ P (bubbleNormalized β L e z)) (ContinuousLinearMap.id ℝ W) c := by
    have h := hs.hasFDerivAt.smul ((hasFDerivAt_id c).sub_const c)
    simp only [id_eq, sub_self, ContinuousLinearMap.smulRight_zero, add_zero, hs1, one_smul] at h
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall
      fun z ↦ apply_bubbleNormalized β hPL hPe z)
  have hcomp := (P.hasFDerivAt.comp c (hd c).hasFDerivAt).unique hP
  have hleft (w : W) : P (fderiv ℝ (bubbleNormalized β L e) c w) = w := by
    simpa using DFunLike.congr_fun hcomp w
  exact LeftInverse.injective hleft

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The normalized bubble vector, read as a map to the unit sphere, has injective derivative at
the centre. -/
private theorem injective_mfderiv_codRestrict_bubbleNormalized (hPL : ∀ w, P (L w) = w)
    (hPe : P e = 0) (hLe : ∀ w, ⟪L w, e⟫ = 0) (he : ‖e‖ = 1)
    (hS : ∀ z, bubbleNormalized β L e z ∈ sphere (0 : E) 1) :
    Injective (mfderiv 𝓘(ℝ, W) (𝓡 n) (Set.codRestrict (bubbleNormalized β L e) _ hS) c) := by
  set g := Set.codRestrict (bubbleNormalized β L e) _ hS
  have hg : ContMDiff 𝓘(ℝ, W) (𝓡 n) ∞ g :=
    (contDiff_bubbleNormalized β hPL hPe hLe he).contMDiff.codRestrict_sphere hS
  -- The inclusion of the sphere composed with `g` is the normalized bubble vector.
  have hval := mfderiv_comp c ((contMDiff_coe_sphere (m := ∞)).mdifferentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)) ((hg c).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  have hcoe : ((↑) : sphere (0 : E) 1 → E) ∘ g = bubbleNormalized β L e :=
    funext fun _ ↦ Set.val_codRestrict_apply ..
  rw [hcoe, mfderiv_eq_fderiv] at hval
  have hinj : Injective ⇑((mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (g c)).comp
      (mfderiv 𝓘(ℝ, W) (𝓡 n) g c)) := by
    rw [← hval]
    exact fun a b hab ↦ (NormedSpace.fromTangentSpace _).injective
      (injective_fderiv_bubbleNormalized β hPL hPe hLe he
        ((NormedSpace.fromTangentSpace _).symm.injective hab))
  rw [ContinuousLinearMap.coe_comp] at hinj
  exact hinj.of_comp

end Bubble

/-! ### The collapse map of a manifold -/

section Collapse

variable {W H M : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace H] {I : ModelWithCorners ℝ W H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The collapse map: a smooth map `f : M → Sⁿ` and a point `y` whose fibre is the single point
`x₀`, at which the derivative of `f` is injective. -/
private theorem exists_collapse (hW : finrank ℝ W = n) (x₀ : M) :
    ∃ (f : M → sphere (0 : E) 1) (y : sphere (0 : E) 1), ContMDiff I (𝓡 n) ∞ f ∧
      f ⁻¹' {y} = {x₀} ∧ Injective (mfderiv I (𝓡 n) f x₀) := by
  -- A unit vector `e`, an isomorphism `L` of `W` onto `e^⊥` and a left inverse `P` killing `e`.
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  obtain ⟨L, P, hPL, hPe, hLe⟩ := exists_leftInverse_inner_eq_zero_of_finrank_eq hW
    (norm_ne_zero_iff.1 (he.symm ▸ one_ne_zero))
  set φ := extChartAt I x₀
  have hsrc : φ.source = (chartAt H x₀).source := extChartAt_source I x₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := I) x₀) (φ x₀)
    (mem_extChartAt_target x₀)
  -- The bump is `1` on the ball of radius `r / 4` and vanishes outside the ball of radius `r / 2`,
  -- where the bubble map `g` is the north pole `e`.
  let β : ContDiffBump (φ x₀) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hS (z : W) : bubbleNormalized β L e z ∈ sphere (0 : E) 1 := by
    simp [bubbleNormalized, norm_smul, bubbleVec_ne_zero β hPL hPe hLe he z]
  let g : W → sphere (0 : E) 1 := Set.codRestrict (bubbleNormalized β L e) _ hS
  have hg : ContMDiff 𝓘(ℝ, W) (𝓡 n) ∞ g :=
    (contDiff_bubbleNormalized β hPL hPe hLe he).contMDiff.codRestrict_sphere hS
  let north : sphere (0 : E) 1 := ⟨e, by simp [he]⟩
  obtain ⟨f, hf, hfg, hfc⟩ := Manifold.exists_contMDiff_eq_comp_extChartAt (c := north)
    (r := r / 2) x₀ ((closedBall_subset_ball (by linarith)).trans hball) hg
    fun z hz ↦ Subtype.ext (bubbleNormalized_of_le_dist β he hz.le)
  have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  refine ⟨f, ⟨-e, by simp [he]⟩, hf, Set.ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩, ?_⟩
  · -- Only the centre `x₀` of the chart goes to the south pole `-e`.
    by_cases hxs : x ∈ (chartAt H x₀).source
    · rw [mem_preimage, mem_singleton_iff, hfg x hxs] at hx
      exact φ.injOn (by rwa [hsrc]) (by rwa [hsrc])
        (eq_of_bubbleNormalized_eq_neg β hPL hPe hLe he (congrArg Subtype.val hx))
    · rw [mem_preimage, mem_singleton_iff, hfc x hxs] at hx
      exact (ne_neg_of_mem_unit_sphere ℝ north (Subtype.ext (congrArg Subtype.val hx))).elim
  · rw [mem_singleton_iff.1 hx]
    exact (hfg x₀ hx₀).trans (Subtype.ext (bubbleNormalized_self β he))
  · -- Near `x₀`, `f` is `g ∘ φ`.
    exact injective_mfderiv_of_eventuallyEq_comp_extChartAt
      ((hg (φ x₀)).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
      (injective_mfderiv_codRestrict_bubbleNormalized β hPL hPe hLe he hS)
      (Filter.eventually_of_mem ((chartAt H x₀).open_source.mem_nhds hx₀) hfg)

/-- **A map to the sphere with a regular value of one preimage.** On a Hausdorff boundaryless
smooth manifold `M` of dimension `n`, for every point `x₀` there is a smooth map `f : M → Sⁿ` to
the unit sphere of a real inner product space of dimension `n + 1`, and a regular value `y` of
`f` whose fibre is `{x₀}`. -/
theorem exists_contMDiff_sphere_isRegularValue_preimage_eq_singleton (hW : finrank ℝ W = n)
    (x₀ : M) : ∃ (f : M → sphere (0 : E) 1) (y : sphere (0 : E) 1),
      ContMDiff I (𝓡 n) ∞ f ∧ IsRegularValue I (𝓡 n) f y ∧ f ⁻¹' {y} = {x₀} := by
  obtain ⟨f, y, hf, hy, hinj⟩ := exists_collapse (E := E) (I := I) hW x₀
  refine ⟨f, y, hf, isRegularValue_iff.2 fun x hx ↦ ?_, hy⟩
  obtain rfl : x = x₀ := by
    rw [← mem_singleton_iff, ← hy, mem_preimage, mem_singleton_iff]
    exact hx
  have hdim : finrank ℝ (TangentSpace I x) = finrank ℝ (TangentSpace (𝓡 n) (f x)) :=
    hW.trans finrank_euclideanSpace_fin.symm
  exact isRegularPoint_iff.2 ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (mfderiv I (𝓡 n) f x : TangentSpace I x →ₗ[ℝ] TangentSpace (𝓡 n) (f x)))).1 hinj)

/-- **A map to the sphere of degree `±1` at a regular value.** For orientations `o` of a
Hausdorff boundaryless smooth manifold `M` of dimension `n` and `o'` of the unit sphere `Sⁿ` of a
real inner product space of dimension `n + 1`, there are a smooth map `f : M → Sⁿ` and a regular
value `y` of `f` at which the signed count of the fibre is `1` or `-1`. When `M` is compact and
`1 ≤ n`, so that `Sⁿ` is connected, `f` therefore has degree `±1`. -/
theorem exists_contMDiff_sphere_degreeAtRegularValue_eq_one_or_eq_neg_one [Nonempty M]
    (hW : finrank ℝ W = n) (o : Manifold.Orientation I M (Fin n))
    (o' : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) :
    ∃ (f : M → sphere (0 : E) 1) (y : sphere (0 : E) 1), ContMDiff I (𝓡 n) ∞ f ∧
      IsRegularValue I (𝓡 n) f y ∧
        (degreeAtRegularValue o o' f y = 1 ∨ degreeAtRegularValue o o' f y = -1) := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨f, y, hf, hy, hfy⟩ :=
    exists_contMDiff_sphere_isRegularValue_preimage_eq_singleton (E := E) (I := I) hW x₀
  have hx₀ : f x₀ = y := by
    rw [← mem_singleton_iff, ← mem_preimage, hfy]
    exact mem_singleton x₀
  refine ⟨f, y, hf, hy, ?_⟩
  rw [degreeAtRegularValue_eq_sum (s := {x₀}) fun x ↦ by
    rw [Finset.mem_singleton, ← mem_singleton_iff, ← hfy, mem_preimage, mem_singleton_iff],
    Finset.sum_singleton]
  exact Manifold.Orientation.orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint
    (hy.isRegularPoint hx₀)

end Collapse

end TauCeti
