/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Euclidean
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Trans

/-!
# The disc theorem in a manifold

Let `M` be a boundaryless smooth manifold modelled on a finite-dimensional real inner product
space `E`. Two smooth embeddings `f g : E → M` with the same centre `f 0 = g 0`, whose derivatives
at `0` have the same orientation, are smoothly isotopic through embeddings, relative to the centre
(`TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_chartAt_mul_pos`). The orientations are
compared in the chart at the centre, by asking that the product of the two derivative
determinants be positive.

This is the disc theorem in the form of Hirsch, Chapter 4, Theorem 6.6, for open discs `E ≅ ℝⁿ`: the
condition there, `Det (D(g⁻¹ ∘ f)(0)) > 0`, is the positivity of the product of determinants
above. The ambient form of Palais's disc theorem, used to show that connected sums are well
defined, follows from it by the isotopy extension theorem, and on a connected manifold the
centres can first be made to agree by a compactly supported diffeotopy
(`TauCeti.exists_diffeotopy_final_apply_eq`). Neither of these steps is taken here.

The Euclidean case is `TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_mul_pos`. To reduce to
it, both embeddings are first shrunk by precomposing with a radial contraction of `E` onto a small
ball about `0`, so that they land in a ball `B` inside the chart at the centre. Read in the chart,
they are embeddings `E → E` with values in `B`, and the Euclidean disc theorem connects them. Its
motion may leave `B`, so it is followed by a radial contraction of `E` onto `B`, and the two ends
are connected to this contracted motion by radial contractions that keep `B` in place. The
resulting motion stays in `B`, so the inverse chart carries it back to `M`.

The radial contraction of `E` about `c` with parameter `κ ≥ 0` is
`y ↦ c + (1 + κ ‖y - c‖²)^(-1/2) • (y - c)`. It is jointly smooth in `κ` and `y`, it is the
identity for `κ = 0`, it moves no point away from `c`, and for `κ = r⁻²` it is Mathlib's
`OpenPartialHomeomorph.univBall c r` after an affine normalization, a diffeomorphism of `E` onto
the ball of radius `r` about `c`. Its smoothness is why `E` is an inner product space, such as
`EuclideanSpace ℝ (Fin n)`: the square of the norm has to be smooth.

## Main results

* `TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_chartAt_mul_pos`: the disc theorem in a
  manifold, for embeddings with a common centre.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6, p. 117.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
-/

public section

noncomputable section

open Set Metric Topology Manifold OpenPartialHomeomorph
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Radial contractions -/

/-- The radial contraction of `E` about `c` with parameter `κ`: the point `y` moves towards `c`
by the factor `(1 + κ ‖y - c‖²)^(-1/2)`. For `κ = 0` it is the identity, and for `κ = r⁻²` it is
a diffeomorphism of `E` onto the ball of radius `r` about `c`. -/
private def radialContraction (c : E) (κ : ℝ) (y : E) : E :=
  c + (√(1 + κ * ‖y - c‖ ^ 2))⁻¹ • (y - c)

private theorem radialContraction_zero (c y : E) : radialContraction c 0 y = y := by
  simp [radialContraction]

private theorem radialContraction_self (c : E) (κ : ℝ) : radialContraction c κ c = c := by
  simp [radialContraction]

/-- A radial contraction moves no point away from the centre. -/
private theorem norm_radialContraction_sub_le (c y : E) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖radialContraction c κ y - c‖ ≤ ‖y - c‖ := by
  have h1 : 1 ≤ √(1 + κ * ‖y - c‖ ^ 2) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_right (by positivity))
  rw [radialContraction, add_sub_cancel_left, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans_le h1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)

/-- For a positive parameter, the radial contraction is `univBall c r` read after the affine
normalization `y ↦ r⁻¹ • (y - c)`, where `κ = r⁻²`. -/
private theorem radialContraction_eq_univBall (c y : E) {r : ℝ} (hr : 0 < r) :
    radialContraction c (r⁻¹ ^ 2) y = univBall c r (r⁻¹ • (y - c)) := by
  -- For `r > 0`, `univBall c r` is `univUnitBall` followed by `x ↦ r • x + c`, by definition.
  have hball (x : E) : univBall c r x = r • univUnitBall x + c := by
    simp only [univBall, hr, ↓reduceDIte]
    rfl
  rw [hball, univUnitBall_apply, radialContraction, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hr, smul_smul, smul_smul, mul_pow, add_comm c]
  congr 2
  field_simp

/-- For `κ = r⁻²` the radial contraction lands in the ball of radius `r` about the centre. -/
private theorem radialContraction_mem_ball (c y : E) {r : ℝ} (hr : 0 < r) :
    radialContraction c (r⁻¹ ^ 2) y ∈ ball c r := by
  rw [radialContraction_eq_univBall c y hr, ← univBall_target c hr]
  exact (univBall c r).map_source (by simp)

/-- The radial contraction is jointly smooth in the parameter and the point, wherever
`1 + κ ‖y - c‖²` is positive. -/
private theorem contDiffOn_radialContraction (c : E) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => radialContraction c q.1 q.2)
      {q | 0 < 1 + q.1 * ‖q.2 - c‖ ^ 2} := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  have hsub : ContDiff ℝ ∞ fun q : ℝ × E => q.2 - c := contDiff_snd.sub contDiff_const
  have hden : ContDiffAt ℝ ∞ (fun q : ℝ × E => √(1 + q.1 * ‖q.2 - c‖ ^ 2)) q :=
    (contDiffAt_const.add (contDiffAt_fst.mul ((contDiff_norm_sq ℝ).comp hsub).contDiffAt)).sqrt
      hq.ne'
  exact contDiffAt_const.add ((hden.inv (Real.sqrt_ne_zero'.mpr hq)).smul hsub.contDiffAt)

/-- A smooth family of radial contractions with nonnegative parameters, applied to a smooth
family of points, is smooth. -/
private theorem contMDiff_radialContraction {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] (c : E) {κ : X → ℝ} {y : X → E} (hκ : ContMDiff J 𝓘(ℝ) ∞ κ)
    (hκ₀ : ∀ x, 0 ≤ κ x) (hy : ContMDiff J 𝓘(ℝ, E) ∞ y) :
    ContMDiff J 𝓘(ℝ, E) ∞ fun x => radialContraction c (κ x) (y x) :=
  (contDiffOn_radialContraction c).contMDiffOn.comp_contMDiff (hκ.prodMk_space hy)
    fun x => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (hκ₀ x) (sq_nonneg _))

/-- A radial contraction with nonnegative parameter is smooth. -/
private theorem contDiff_radialContraction (c : E) {κ : ℝ} (hκ : 0 ≤ κ) :
    ContDiff ℝ ∞ (radialContraction c κ) := by
  rw [← contDiffOn_univ]
  exact (contDiffOn_radialContraction c).comp (contDiffOn_const.prodMk contDiffOn_id)
    fun y _ => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hκ (sq_nonneg _))

/-- For a positive parameter, the radial contraction is the restriction to all of `E` of an open
partial homeomorphism onto a ball, which is smooth in both directions. -/
private theorem exists_radialContraction_eq_openPartialHomeomorph (c : E) {κ : ℝ}
    (hκ : 0 < κ) : ∃ Θ : OpenPartialHomeomorph E E, Θ.source = univ ∧
      ContDiffOn ℝ ∞ Θ Θ.source ∧ ContDiffOn ℝ ∞ Θ.symm Θ.target ∧
      ⇑Θ = radialContraction c κ := by
  set r := (√κ)⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hκ)
  -- The affine normalization `y ↦ r⁻¹ • (y - c)` and its inverse `z ↦ r • z + c`.
  let A : E ≃ₜ E := (Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero r⁻¹ (by positivity))
  have hA (y : E) : A y = r⁻¹ • (y - c) := rfl
  have hAsymm (z : E) : A.symm z = r⁻¹⁻¹ • z + c := rfl
  have hΘ : ⇑(A.transOpenPartialHomeomorph (univBall c r)) = radialContraction c κ := by
    ext y
    rw [Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply, hA,
      ← radialContraction_eq_univBall c y hr, inv_inv, Real.sq_sqrt hκ.le]
  refine ⟨A.transOpenPartialHomeomorph (univBall c r), by simp, ?_, ?_, hΘ⟩
  · rw [hΘ]
    exact (contDiff_radialContraction c hκ.le).contDiffOn
  · have : ⇑A.symm = fun z => r⁻¹⁻¹ • z + c := funext hAsymm
    simp only [Homeomorph.transOpenPartialHomeomorph_symm_apply,
      Homeomorph.transOpenPartialHomeomorph_target, univBall_target c hr, this]
    exact ((contDiff_id.const_smul _).add contDiff_const).comp_contDiffOn contDiffOn_univBall_symm

/-- A radial contraction with nonnegative parameter is a local diffeomorphism and a topological
embedding. -/
private theorem isLocalDiffeomorph_and_isEmbedding_radialContraction (c : E) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (radialContraction c κ) ∧
      IsEmbedding (radialContraction c κ) := by
  rcases hκ.eq_or_lt with rfl | hκ
  · have : radialContraction c 0 = id := funext (radialContraction_zero c)
    rw [this]
    exact ⟨(Diffeomorph.refl 𝓘(ℝ, E) E ∞).isLocalDiffeomorph, IsEmbedding.id⟩
  obtain ⟨Θ, hsource, hΘ, hΘsymm, hΘeq⟩ := exists_radialContraction_eq_openPartialHomeomorph c hκ
  refine ⟨fun y => ?_, hΘeq ▸ (Θ.isOpenEmbedding hsource).isEmbedding⟩
  exact isLocalDiffeomorphAt_of_eqOn (Φ := PartialDiffeomorph.ofOpenPartialHomeomorph Θ hΘ hΘsymm)
    (by simp [hsource]) fun z _ => by simp [← hΘeq]

/-- A radial contraction has derivative the identity at its centre. -/
private theorem hasFDerivAt_radialContraction_self (c : E) (κ : ℝ) :
    HasFDerivAt (radialContraction c κ) (ContinuousLinearMap.id ℝ E) c := by
  have hq : (0 : ℝ) < 1 + κ * ‖c - c‖ ^ 2 := by simp
  have ha : DifferentiableAt ℝ (fun y : E => (√(1 + κ * ‖y - c‖ ^ 2))⁻¹) c :=
    (((contDiffAt_const.add (contDiffAt_const.mul ((contDiff_norm_sq ℝ).comp
      (contDiff_id.sub contDiff_const)).contDiffAt)).sqrt hq.ne').inv
        (Real.sqrt_ne_zero'.mpr hq)).differentiableAt (n := 1) (by simp)
  convert (ha.hasFDerivAt.smul ((hasFDerivAt_id c).sub_const c)).const_add c using 1
  · ext v
    rw [radialContraction, Pi.smul_apply', id]
  · simp

/-! ### Isotopies built from radial contractions and local diffeomorphisms -/

section Isotopies

variable {E' H' N P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ P]

/-- A smooth embedding of `E` precomposed with a radial contraction about `0`. -/
private def contractEmbedding (f : SmoothEmbedding 𝓘(ℝ, E) J ∞ E N) {κ : ℝ} (hκ : 0 ≤ κ) :
    SmoothEmbedding 𝓘(ℝ, E) J ∞ E N :=
  SmoothEmbedding.ofIsSmoothEmbedding (f ∘ radialContraction 0 κ)
    (isSmoothEmbedding_comp_isLocalDiffeomorph
      (isLocalDiffeomorph_and_isEmbedding_radialContraction 0 hκ).1
      (isLocalDiffeomorph_and_isEmbedding_radialContraction 0 hκ).2 f.isSmoothEmbedding)

private theorem coe_contractEmbedding (f : SmoothEmbedding 𝓘(ℝ, E) J ∞ E N) {κ : ℝ}
    (hκ : 0 ≤ κ) : ⇑(contractEmbedding f hκ) = f ∘ radialContraction 0 κ := by
  rw [contractEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding]

private theorem contractEmbedding_apply (f : SmoothEmbedding 𝓘(ℝ, E) J ∞ E N) {κ : ℝ}
    (hκ : 0 ≤ κ) (x : E) : contractEmbedding f hκ x = f (radialContraction 0 κ x) := by
  rw [coe_contractEmbedding, Function.comp_apply]

/-- The source contraction `t ↦ f ∘ radialContraction 0 (t κ)` is a smooth isotopy from `f`. -/
private def contractIsotopy (f : SmoothEmbedding 𝓘(ℝ, E) J ∞ E N) {κ : ℝ} (hκ : 0 ≤ κ) :
    SmoothIsotopy f.toContMDiffMap (contractEmbedding f hκ).toContMDiffMap where
  toContMDiffMap := ⟨fun p => f (radialContraction 0 ((p.1 : ℝ) * κ) p.2),
    f.contMDiff.comp (contMDiff_radialContraction 0
      ((contDiff_id.mul contDiff_const).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp contMDiff_fst))
      (fun p => mul_nonneg p.1.2.1 hκ) contMDiff_snd)⟩
  map_zero_left x := by simp [radialContraction_zero]
  map_one_left x := by simp [contractEmbedding_apply]
  isSmoothEmbedding t := by
    have h := (contractEmbedding f (mul_nonneg t.2.1 hκ)).isSmoothEmbedding
    rwa [coe_contractEmbedding] at h

private theorem contractIsotopy_apply (f : SmoothEmbedding 𝓘(ℝ, E) J ∞ E N) {κ : ℝ}
    (hκ : 0 ≤ κ) (p : unitInterval × E) :
    contractIsotopy f hκ p = f (radialContraction 0 ((p.1 : ℝ) * κ) p.2) := (rfl)

/-- Postcompose a smooth isotopy with a map which is a local diffeomorphism at every point of a
set containing the motion, and a topological embedding on that set. -/
private def postcompIsotopy {f₀ f₁ : C^∞⟮𝓘(ℝ, E), E; J, N⟯} (K : SmoothIsotopy f₀ f₁)
    (k : N → P) {s : Set N} (hKs : ∀ p, K p ∈ s) (hk : ∀ y ∈ s, IsLocalDiffeomorphAt J J ∞ k y)
    (hks : IsEmbedding (s.domRestrict k)) (g₀ g₁ : C^∞⟮𝓘(ℝ, E), E; J, P⟯)
    (hg₀ : ∀ x, g₀ x = k (f₀ x)) (hg₁ : ∀ x, g₁ x = k (f₁ x)) : SmoothIsotopy g₀ g₁ where
  toContMDiffMap := ⟨fun p => k (K p), show ContMDiff _ _ ∞ (fun p => k (K p)) from
    fun p => (hk _ (hKs p)).contMDiffAt.comp p K.contMDiff.contMDiffAt⟩
  map_zero_left x := by
    rw [ContMDiffMap.coeFn_mk, SmoothIsotopy.apply_zero, hg₀]
  map_one_left x := by
    rw [ContMDiffMap.coeFn_mk, SmoothIsotopy.apply_one, hg₁]
  isSmoothEmbedding t :=
    isSmoothEmbedding_isLocalDiffeomorphAt_comp (f := fun x => K (t, x)) (k := k)
      (fun x => hk _ (hKs (t, x))) (range_subset_iff.2 fun x => hKs (t, x)) hks
      (K.isSmoothEmbedding t)

end Isotopies

/-- A smooth embedding into `E` followed by a radial contraction. -/
private def radialEmbedding (c : E) {κ : ℝ} (hκ : 0 ≤ κ)
    (F : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E) : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E :=
  SmoothEmbedding.ofIsSmoothEmbedding (radialContraction c κ ∘ F)
    (isSmoothEmbedding_isLocalDiffeomorphAt_comp
      (fun _ => (isLocalDiffeomorph_and_isEmbedding_radialContraction c hκ).1 _) (subset_univ _)
      ((isLocalDiffeomorph_and_isEmbedding_radialContraction c hκ).2.comp IsEmbedding.subtypeVal)
      F.isSmoothEmbedding)

private theorem coe_radialEmbedding (c : E) {κ : ℝ} (hκ : 0 ≤ κ)
    (F : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E) :
    ⇑(radialEmbedding c hκ F) = radialContraction c κ ∘ F := by
  rw [radialEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding]

/-- The target contraction `t ↦ radialContraction c (t κ) ∘ F` is a smooth isotopy from `F`. -/
private def radialIsotopy (c : E) {κ : ℝ} (hκ : 0 ≤ κ)
    (F : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E) :
    SmoothIsotopy F.toContMDiffMap (radialEmbedding c hκ F).toContMDiffMap where
  toContMDiffMap := ⟨fun p => radialContraction c ((p.1 : ℝ) * κ) (F p.2),
    contMDiff_radialContraction c ((contDiff_id.mul contDiff_const).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp contMDiff_fst))
      (fun p => mul_nonneg p.1.2.1 hκ) (F.contMDiff.comp contMDiff_snd)⟩
  map_zero_left x := by simp [radialContraction_zero]
  map_one_left x := by simp [coe_radialEmbedding]
  isSmoothEmbedding t := by
    have h := (radialEmbedding c (mul_nonneg t.2.1 hκ) F).isSmoothEmbedding
    rwa [coe_radialEmbedding] at h

private theorem radialIsotopy_apply (c : E) {κ : ℝ} (hκ : 0 ≤ κ)
    (F : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E) (p : unitInterval × E) :
    radialIsotopy c hκ F p = radialContraction c ((p.1 : ℝ) * κ) (F p.2) := (rfl)

/-- **The disc theorem in a ball.** Two smooth embeddings `E → E` with values in a ball, centred
at its centre, with derivatives of the same orientation there, are smoothly isotopic relative to
the centre through embeddings with values in the ball. -/
private theorem exists_smoothIsotopy_mapsTo_ball [FiniteDimensional ℝ E] {c : E} {r : ℝ}
    (hr : 0 < r) {F G : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E} (hF0 : F 0 = c) (hG0 : G 0 = c)
    (hF : ∀ x, F x ∈ ball c r) (hG : ∀ x, G x ∈ ball c r)
    (hdet : 0 < (fderiv ℝ F 0).det * (fderiv ℝ G 0).det) :
    ∃ L : SmoothIsotopy F.toContMDiffMap G.toContMDiffMap,
      (∀ q, L q ∈ ball c r) ∧ ∀ t : unitInterval, L (t, 0) = c := by
  obtain ⟨K, hK⟩ := F.exists_smoothIsotopy_of_det_mul_pos G (hF0.trans hG0.symm) hdet
  -- Follow `K` by the radial contraction onto `ball c r`, and join its ends to `F` and `G` by
  -- radial contractions, which keep `ball c r` in place.
  have hκ : (0 : ℝ) ≤ r⁻¹ ^ 2 := sq_nonneg _
  have hpush (F : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E) (hF : ∀ x, F x ∈ ball c r)
      (q : unitInterval × E) : radialIsotopy c hκ F q ∈ ball c r := by
    rw [radialIsotopy_apply, mem_ball_iff_norm]
    exact (norm_radialContraction_sub_le c _ (mul_nonneg q.1.2.1 hκ)).trans_lt
      (mem_ball_iff_norm.1 (hF q.2))
  let τK := postcompIsotopy K (radialContraction c (r⁻¹ ^ 2)) (s := univ) (fun _ => trivial)
    (fun y _ => (isLocalDiffeomorph_and_isEmbedding_radialContraction c hκ).1 y)
    ((isLocalDiffeomorph_and_isEmbedding_radialContraction c hκ).2.comp IsEmbedding.subtypeVal)
    (radialEmbedding c hκ F).toContMDiffMap (radialEmbedding c hκ G).toContMDiffMap
    (fun x => by simp [coe_radialEmbedding]) (fun x => by simp [coe_radialEmbedding])
  have hτK (q : unitInterval × E) : τK q = radialContraction c (r⁻¹ ^ 2) (K q) := rfl
  refine ⟨((radialIsotopy c hκ F).trans τK le_rfl).trans (radialIsotopy c hκ G).symm le_rfl,
    fun q => ?_, fun t => ?_⟩
  · refine SmoothIsotopy.trans_apply_mem _ _ _ (fun t => ?_) (fun t => ?_) q.1
    · refine SmoothIsotopy.trans_apply_mem _ _ _ (fun t => hpush F hF _) (fun t => ?_) t
      rw [hτK]
      exact radialContraction_mem_ball c _ hr
    · rw [SmoothIsotopy.symm_apply]
      exact hpush G hG _
  · refine SmoothIsotopy.trans_apply_mem (s := {c}) _ _ _ (fun t => ?_) (fun t => ?_) t
    · refine SmoothIsotopy.trans_apply_mem (s := {c}) _ _ _ (fun t => ?_) (fun t => ?_) t
      · rw [mem_singleton_iff, radialIsotopy_apply, hF0, radialContraction_self]
      · rw [mem_singleton_iff, hτK, hK, hF0, radialContraction_self]
    · rw [mem_singleton_iff, SmoothIsotopy.symm_apply, radialIsotopy_apply, hG0,
        radialContraction_self]

/-! ### The disc theorem -/

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A smooth embedding of `E` into a chart domain, read in that chart. -/
private def chartEmbedding {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (f : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (hf : range f ⊆ φ.source) : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E :=
  SmoothEmbedding.ofIsSmoothEmbedding (φ ∘ f)
    (isSmoothEmbedding_isLocalDiffeomorphAt_comp
      (fun x => φ.isLocalDiffeomorphAt_of_mem_maximalAtlas hφ (hf (mem_range_self x))) hf
      φ.isOpenEmbedding_restrict.isEmbedding f.isSmoothEmbedding)

private theorem coe_chartEmbedding {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (f : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (hf : range f ⊆ φ.source) : ⇑(chartEmbedding hφ f hf) = φ ∘ f := by
  rw [chartEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding]

/-- A smooth embedding of `E`, read in the chart at the image of `0`, is differentiable at `0`. -/
private theorem differentiableAt_chartAt_comp (f : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) :
    DifferentiableAt ℝ (chartAt E (f 0) ∘ f) 0 := by
  have h := (f.contMDiff.mdifferentiableAt (by simp) (x := 0)).hasMFDerivAt.2.differentiableWithinAt
  simpa [writtenInExtChartAt, differentiableWithinAt_univ] using h

/-- Shrinking the source by a radial contraction about `0` does not change the derivative at `0`
of an embedding read in a chart. -/
private theorem fderiv_chartEmbedding_contractEmbedding {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (k : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    {κ : ℝ} (hκ : 0 ≤ κ) (hk : range (contractEmbedding k hκ) ⊆ φ.source)
    (hd : DifferentiableAt ℝ (φ ∘ k) 0) :
    fderiv ℝ (chartEmbedding hφ (contractEmbedding k hκ) hk) 0 = fderiv ℝ (φ ∘ k) 0 := by
  have hd' : HasFDerivAt (φ ∘ k) (fderiv ℝ (φ ∘ k) 0) (radialContraction 0 κ 0) := by
    rw [radialContraction_self]
    exact hd.hasFDerivAt
  rw [coe_chartEmbedding, coe_contractEmbedding, ← Function.comp_assoc]
  simpa using (hd'.comp (0 : E) (hasFDerivAt_radialContraction_self 0 κ)).fderiv

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The disc theorem in a manifold.** Two smooth embeddings of `E` into a boundaryless manifold
modelled on `E`, with the same centre `f 0 = g 0` and derivatives at `0` of the same orientation,
are smoothly isotopic relative to that centre. The orientations are compared in the chart at the
centre: the product of the derivative determinants there is positive. This condition does not
depend on the chart, since a change of chart multiplies both determinants by the same nonzero
number. For `M = E` it is the hypothesis of the Euclidean disc theorem
`TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_mul_pos`. -/
theorem SmoothEmbedding.exists_smoothIsotopy_of_det_chartAt_mul_pos
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hcentre : f 0 = g 0)
    (hdet : 0 < (fderiv ℝ (chartAt E (f 0) ∘ f) 0).det *
      (fderiv ℝ (chartAt E (f 0) ∘ g) 0).det) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap,
      ∀ t : unitInterval, G (t, 0) = f 0 := by
  set p := f 0 with hp
  set φ := chartAt E p
  have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  set c := φ p
  have hpφ : p ∈ φ.source := mem_chart_source E p
  -- A ball about the centre of the chart, and a ball about `0` that `f` and `g` map into it.
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball c r ⊆ φ.target :=
    Metric.isOpen_iff.1 φ.open_target c (φ.map_source hpφ)
  set U := φ.source ∩ φ ⁻¹' ball c r
  have hU : U ∈ 𝓝 p :=
    (φ.isOpen_inter_preimage isOpen_ball).mem_nhds ⟨hpφ, mem_ball_self hr⟩
  obtain ⟨δ, hδ, hδU⟩ : ∃ δ > 0, ball (0 : E) δ ⊆ f ⁻¹' U ∩ g ⁻¹' U :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem
      (f.contMDiff.continuous.continuousAt.preimage_mem_nhds hU)
      (g.contMDiff.continuous.continuousAt.preimage_mem_nhds (hcentre ▸ hU)))
  -- Step 1: shrink the source, so that both embeddings land in `U`.
  have ha : (0 : ℝ) ≤ δ⁻¹ ^ 2 := sq_nonneg _
  set f₁ := contractEmbedding f ha
  set g₁ := contractEmbedding g ha
  have hf₁U (x : E) : f₁ x ∈ U := by
    rw [contractEmbedding_apply]
    exact (hδU (by simpa using radialContraction_mem_ball (0 : E) x hδ)).1
  have hg₁U (x : E) : g₁ x ∈ U := by
    rw [contractEmbedding_apply]
    exact (hδU (by simpa using radialContraction_mem_ball (0 : E) x hδ)).2
  have hf₁φ : range f₁ ⊆ φ.source := range_subset_iff.2 fun x => (hf₁U x).1
  have hg₁φ : range g₁ ⊆ φ.source := range_subset_iff.2 fun x => (hg₁U x).1
  -- Step 2: read the shrunken embeddings in the chart.
  set F₁ := chartEmbedding hφ f₁ hf₁φ
  set G₁ := chartEmbedding hφ g₁ hg₁φ
  have hF₁ (x : E) : F₁ x = φ (f₁ x) := by rw [coe_chartEmbedding, Function.comp_apply]
  have hG₁ (x : E) : G₁ x = φ (g₁ x) := by rw [coe_chartEmbedding, Function.comp_apply]
  have hF₁ball (x : E) : F₁ x ∈ ball c r := hF₁ x ▸ (hf₁U x).2
  have hG₁ball (x : E) : G₁ x ∈ ball c r := hG₁ x ▸ (hg₁U x).2
  have hF₁0 : F₁ 0 = c := by
    rw [hF₁, contractEmbedding_apply, radialContraction_self]
  have hG₁0 : G₁ 0 = c := by
    rw [hG₁, contractEmbedding_apply, radialContraction_self, ← hcentre]
  -- The shrinking has derivative the identity at `0`, so the orientations are unchanged.
  have hdet₁ : 0 < (fderiv ℝ F₁ 0).det * (fderiv ℝ G₁ 0).det := by
    rwa [fderiv_chartEmbedding_contractEmbedding hφ f ha hf₁φ (differentiableAt_chartAt_comp f),
      fderiv_chartEmbedding_contractEmbedding hφ g ha hg₁φ
        (by simpa only [φ, p, hcentre] using differentiableAt_chartAt_comp g)]
  -- Step 3: the Euclidean disc theorem in the chart, confined to `ball c r`.
  obtain ⟨L, hLball, hL0⟩ := exists_smoothIsotopy_mapsTo_ball hr hF₁0 hG₁0 hF₁ball hG₁ball hdet₁
  -- Step 4: carry the confined motion back to `M` through the chart.
  let L' := postcompIsotopy L φ.symm (s := φ.target) (fun q => hball (hLball q))
    (fun y hy => φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas hφ hy)
    φ.symm.isOpenEmbedding_restrict.isEmbedding f₁.toContMDiffMap g₁.toContMDiffMap
    (fun x => by simp [hF₁, φ.left_inv (hf₁U x).1])
    (fun x => by simp [hG₁, φ.left_inv (hg₁U x).1])
  have hL' (q : unitInterval × E) : L' q = φ.symm (L q) := rfl
  -- Step 5: undo the shrinking of the sources.
  refine ⟨((contractIsotopy f ha).trans L' le_rfl).trans (contractIsotopy g ha).symm le_rfl,
    fun t => ?_⟩
  refine SmoothIsotopy.trans_apply_mem (s := {p}) _ _ _ (fun t => ?_) (fun t => ?_) t
  · refine SmoothIsotopy.trans_apply_mem (s := {p}) _ _ _ (fun t => ?_) (fun t => ?_) t
    · rw [mem_singleton_iff, contractIsotopy_apply, radialContraction_self]
    · rw [mem_singleton_iff, hL', hL0, φ.left_inv hpφ]
  · rw [mem_singleton_iff, SmoothIsotopy.symm_apply, contractIsotopy_apply, radialContraction_self,
      hcentre]

end Manifold

end TauCeti
