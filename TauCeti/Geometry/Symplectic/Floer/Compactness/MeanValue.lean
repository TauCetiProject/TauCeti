/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The mean-value inequality for Floer solutions in real coordinates and in charts

Gromov–Floer compactness for Floer solutions in a closed manifold `M` uses an a priori bound on
small discs of small energy, the mean-value inequality. For solutions of the coordinate Floer
equation `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` in a real inner product space, on discs of
`ℂ`, it is `TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy`.
This file states it in the two forms in which Floer solutions in a manifold are read.

* **Real coordinates and finite-dimensional targets.** For a target `F` that is a
  finite-dimensional normed space, without an inner product, and on balls of `ℝ × ℝ`, which are
  squares for its sup norm, there are `δ > 0` and `C` such that a solution on `B_r(z₀)` with
  `r² + ∫_{B_r(z₀)} ‖∂ₛu‖² < δ` satisfies `r² ‖∂ₛu(z₀)‖² ≤ C (r² + ∫_{B_r(z₀)} ‖∂ₛu‖²)`
  (`TauCeti.Floer.exists_pos_forall_sq_mul_norm_fderiv_sq_le_of_small_energy_of_finiteDimensional`).
  The disc of `ℂ` of radius `r` lies in the square of the same radius, through the coordinate
  `equivRealProdCLM`, and `toEuclidean` moves the target to a Euclidean space.
* **Charts of a manifold.** For a solution `u : ℝ × ℝ → M` of `(du - X_K)^{0,1} = 0` with values
  in a chart, the same inequality holds for the intrinsic Floer energy density
  `e(u) = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`: if `r² + ∫_{B_r(z₀)} e(u) < δ`, then
  `r² e(u)(z₀) ≤ C (r² + ∫_{B_r(z₀)} e(u))`
  (in the namespace `TauCeti.SmoothTwoForm`,
  `IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy`). On a compact
  window of the chart, `e(u)` and `‖∂ₛv‖²` for the coordinate expression `v` of `u` bound each
  other up to constants (`IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_sq_le` and
  `exists_forall_floerEnergyDensity_le_norm_fderiv_extChartAt_comp_sq`), and the square `B_r(z₀)`
  has area `4 r²` (`Real.volume_real_ball_prod`).

So a disc of radius `r` and small energy has energy density at most `C (1 + ∫ e(u) / r²)` at its
centre. Contrapositively, a disc on which `r² e(u)` is large at the centre carries at least a fixed
amount of energy: this is the lower bound for the energy concentrating at a point where the energy
densities of a sequence of solutions blow up, once the discs about the centres chosen by
`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv` are known to lie in a
chart. That localization of small discs into charts is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.3
  (the mean-value inequality) and Section 8.1 (inhomogeneous equations).
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter MeasureTheory Metric Real Set Topology

namespace TauCeti.Floer

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- In the complex coordinate `equivRealProdCLM` and after a linear equivalence `L`, the derivative
of `u` in the direction `1` is `L ∂ₛu`. -/
private theorem fderiv_comp_comp_equivRealProdCLM_apply (L : F ≃L[ℝ] G) (u : ℝ × ℝ → F) (y v : ℂ) :
    fderiv ℝ (L ∘ (u ∘ equivRealProdCLM)) y v =
      L (fderiv ℝ u (equivRealProdCLM y) (equivRealProdCLM v)) := by
  rw [L.comp_fderiv, equivRealProdCLM.comp_right_fderiv]
  rfl

/-- In the complex coordinate `equivRealProdCLM` and after a linear equivalence `L`, the energy of
`u` on the disc of `ℂ` of radius `r` is at most `‖L‖²` times its energy on the square `B_r(z₀)`
of `ℝ × ℝ`, which contains the disc. -/
private theorem setIntegral_ball_norm_fderiv_comp_sq_le (L : F ≃L[ℝ] G) {u : ℝ × ℝ → F}
    {z₀ : ℝ × ℝ} {r : ℝ}
    (hu' : ContinuousOn (fun y ↦ fderiv ℝ u y stdComplexLineReal) (closedBall z₀ r)) :
    ∫ y in ball (equivRealProdCLM.symm z₀) r, ‖fderiv ℝ (L ∘ (u ∘ equivRealProdCLM)) y 1‖ ^ 2 ≤
      ‖(L : F →L[ℝ] G)‖ ^ 2 * ∫ y in ball z₀ r, ‖fderiv ℝ u y stdComplexLineReal‖ ^ 2 := by
  set f : ℝ × ℝ → ℝ := fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2
  have hball : ∀ y ∈ ball (equivRealProdCLM.symm z₀) r, equivRealProdCLM y ∈ ball z₀ r :=
    fun y hy ↦ by
      rw [mem_ball, ← equivRealProdCLM.apply_symm_apply z₀]
      exact (lipschitz_equivRealProd.dist_le_mul _ _).trans_lt (by simpa using hy)
  -- `equivRealProdCLM` preserves volume.
  have hint : IntegrableOn (f ∘ equivRealProdCLM) (equivRealProdCLM ⁻¹' ball z₀ r) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      equivRealProdCLM.toHomeomorph.measurableEmbedding).2 <|
      (hu'.norm.pow 2).integrableOn_compact (isCompact_closedBall z₀ r) |>.mono_set
        ball_subset_closedBall
  rw [← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    equivRealProdCLM.toHomeomorph.measurableEmbedding f, ← integral_const_mul]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity)
    ((hint.mono_set fun y hy ↦ hball y hy).const_mul _)
    ((ae_restrict_mem measurableSet_ball).mono fun y _ ↦ ?_)).trans <|
    setIntegral_mono_set (hint.const_mul _)
      (Eventually.of_forall fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Eventually.of_forall fun y hy ↦ hball y hy)
  rw [fderiv_comp_comp_equivRealProdCLM_apply, equivRealProdCLM_one]
  calc _ ≤ (‖(L : F →L[ℝ] G)‖ * ‖fderiv ℝ u (equivRealProdCLM y) stdComplexLineReal‖) ^ 2 := by
        gcongr
        exact L.toContinuousLinearMap.le_opNorm _
    _ = _ := by rw [mul_pow]; rfl

/-- The arithmetic closing the mean-value inequality in real coordinates: the centre value `a` is
at most `N'² b` for the value `b` in the coordinates of the inner product space, where the
mean-value inequality bounds `π r² b` by the energy `I_w ≤ N² I`. -/
private theorem sq_mul_le_of_pi_mul_sq_mul_le {a b r N N' I Iw : ℝ} (ha : a ≤ N' ^ 2 * b)
    (hmv : π * r ^ 2 * b ≤ 7 * π * r ^ 2 + 8 * Iw) (hIw : Iw ≤ N ^ 2 * I) (hI : 0 ≤ I) :
    r ^ 2 * a ≤ N' ^ 2 * (7 + 8 * N ^ 2 / π) * (r ^ 2 + I) := by
  have hπ0 : 0 < π := pi_pos
  refine le_of_mul_le_mul_left ?_ hπ0
  have h7 : π * (7 + 8 * N ^ 2 / π) = 7 * π + 8 * N ^ 2 := by
    rw [mul_add, mul_div_cancel₀ _ hπ0.ne']
    ring
  calc π * (r ^ 2 * a) ≤ N' ^ 2 * (π * r ^ 2 * b) := by
        nlinarith [mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ π * r ^ 2)]
    _ ≤ N' ^ 2 * (7 * π * r ^ 2 + 8 * (N ^ 2 * I)) := by
        gcongr
        exact hmv.trans (by gcongr)
    _ ≤ N' ^ 2 * ((7 * π + 8 * N ^ 2) * (r ^ 2 + I)) := by
        gcongr N' ^ 2 * ?_
        nlinarith [mul_nonneg hπ0.le hI, mul_nonneg (sq_nonneg N) (sq_nonneg r)]
    _ = π * (N' ^ 2 * (7 + 8 * N ^ 2 / π) * (r ^ 2 + I)) := by
        rw [← h7]
        ring

variable [FiniteDimensional ℝ F]

/-- The mean-value inequality for an inner product space, applied to a solution in `F` on a square
of `ℝ × ℝ` read in the complex coordinate `equivRealProdCLM` on the disc of the same radius and in
the Euclidean coordinate `toEuclidean`. -/
private theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_toEuclidean_comp_sq_le
    {J : (ℝ × ℝ) × F → F →L[ℝ] F} {X : (ℝ × ℝ) × F → ℝ × ℝ →L[ℝ] F}
    {W : Set ((ℝ × ℝ) × F)} {D : Set (ℝ × ℝ)} {K : Set F}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃u : ℝ × ℝ → F⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 ≤ r → ball z₀ r ⊆ D →
      ContDiffOn ℝ 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ u y stdComplexLineReal) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y stdComplexLineImag - X (y, u y) stdComplexLineImag =
        J (y, u y) (fderiv ℝ u y stdComplexLineReal - X (y, u y) stdComplexLineReal)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      π * r ^ 2 + ∫ y in ball (equivRealProdCLM.symm z₀) r,
        ‖fderiv ℝ (toEuclidean ∘ (u ∘ equivRealProdCLM)) y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ (toEuclidean ∘ (u ∘ equivRealProdCLM)) (equivRealProdCLM.symm z₀) 1‖ ^ 2
        ≤ 7 * π * r ^ 2 + 8 * ∫ y in ball (equivRealProdCLM.symm z₀) r,
          ‖fderiv ℝ (toEuclidean ∘ (u ∘ equivRealProdCLM)) y 1‖ ^ 2 := by
  let L : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) := toEuclidean
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  -- The data conjugated by `e` on the domain and by `L` on the target.
  let g : ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) → (ℝ × ℝ) × F :=
    fun q ↦ (e q.1, L.symm q.2)
  have hgc : ContDiff ℝ 2 g :=
    (e.contDiff.comp contDiff_fst).prodMk (L.symm.contDiff.comp contDiff_snd)
  have hDKW' : (e ⁻¹' D) ×ˢ (L '' K) ⊆ g ⁻¹' W := by
    rintro ⟨y, _⟩ ⟨hy, x, hx, rfl⟩
    have h : (e y, x) ∈ D ×ˢ K := ⟨hy, hx⟩
    simpa [g] using hDKW h
  obtain ⟨δ, hδ, hmean⟩ := exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy
    (J := fun q ↦ L.toContinuousLinearMap ∘L J (g q) ∘L L.symm.toContinuousLinearMap)
    (X := fun q ↦ L.toContinuousLinearMap ∘L X (g q) ∘L (e : ℂ →L[ℝ] ℝ × ℝ))
    (hW.preimage hgc.continuous)
    (contDiffOn_const.clm_comp ((hJ.comp hgc.contDiffOn (mapsTo_preimage g W)).clm_comp
      contDiffOn_const))
    (contDiffOn_const.clm_comp ((hX.comp hgc.contDiffOn (mapsTo_preimage g W)).clm_comp
      contDiffOn_const))
    (e.toHomeomorph.isCompact_preimage.2 hD) (hK.image L.continuous) hDKW'
    (by rintro y hy _ ⟨x, hx, rfl⟩ v; simp [g, hJsq (e y) hy x hx])
  refine ⟨δ, hδ, fun u z₀ r hr hrD hu hu' hfl huK hE ↦ ?_⟩
  -- The disc of `ℂ` lies in the square of the same radius.
  have hdist (y : ℂ) : dist (e y) z₀ ≤ dist y (e.symm z₀) := by
    conv_lhs => rw [← e.apply_symm_apply z₀]
    exact (lipschitz_equivRealProd.dist_le_mul y (e.symm z₀)).trans (by simp)
  have hball : ∀ y ∈ ball (e.symm z₀) r, e y ∈ ball z₀ r := fun y hy ↦ (hdist y).trans_lt hy
  have hcball : ∀ y ∈ closedBall (e.symm z₀) r, e y ∈ closedBall z₀ r := fun y hy ↦
    (hdist y).trans hy
  have hw1 (y : ℂ) := fderiv_comp_comp_equivRealProdCLM_apply L u y 1
  have hwI (y : ℂ) := fderiv_comp_comp_equivRealProdCLM_apply L u y I
  rw [← he, equivRealProdCLM_one] at hw1
  rw [← he, equivRealProdCLM_I] at hwI
  exact hmean (u := L ∘ (u ∘ e)) (z₀ := e.symm z₀) hr
    (fun y hy ↦ by simpa [he] using hrD (hball y hy))
    (L.contDiff.comp_contDiffOn (hu.comp e.contDiff.contDiffOn hball))
    ((L.continuous.comp_continuousOn (hu'.comp e.continuous.continuousOn hcball)).congr
      fun y _ ↦ hw1 y)
    (fun y hy ↦ by
      rw [hw1, hwI]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, g,
        Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, he, equivRealProdCLM_one,
        equivRealProdCLM_I]
      rw [← map_sub, ← map_sub, L.symm_apply_apply, hfl _ (hball y hy)])
    (fun y hy ↦ ⟨u (e y), huK _ (hball y hy), rfl⟩) hE

/-- **The mean-value inequality for solutions in a finite-dimensional normed space, in real
coordinates.** Let `J(z, x)` and `X(z, x)` be `C²` on an open set `W ⊆ (ℝ × ℝ) × F` containing
`D × K` for compact `D ⊆ ℝ × ℝ` and `K ⊆ F`, with `J(z, x)² = -1` on `D × K`. There are a threshold
`δ > 0` and a constant `C` such that every solution `u` of the coordinate Floer equation
`∂ₜu - X(z, u)(0, 1) = J(z, u)(∂ₛu - X(z, u)(1, 0))` on a ball `B_r(z₀) ⊆ D` of `ℝ × ℝ`, with
values in `K`, `C³` on the ball and with `∂ₛu` continuous on its closure, satisfies

`r² ‖∂ₛu(z₀)‖² ≤ C (r² + ∫_{B_r(z₀)} ‖∂ₛu‖²)`

as soon as `r² + ∫_{B_r(z₀)} ‖∂ₛu‖² < δ`. Balls of `ℝ × ℝ` are squares for its sup norm. -/
theorem exists_pos_forall_sq_mul_norm_fderiv_sq_le_of_small_energy_of_finiteDimensional
    {J : (ℝ × ℝ) × F → F →L[ℝ] F} {X : (ℝ × ℝ) × F → ℝ × ℝ →L[ℝ] F}
    {W : Set ((ℝ × ℝ) × F)} {D : Set (ℝ × ℝ)} {K : Set F}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ ⦃u : ℝ × ℝ → F⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 ≤ r → ball z₀ r ⊆ D →
      ContDiffOn ℝ 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ u y stdComplexLineReal) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y stdComplexLineImag - X (y, u y) stdComplexLineImag =
        J (y, u y) (fderiv ℝ u y stdComplexLineReal - X (y, u y) stdComplexLineReal)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      r ^ 2 + ∫ y in ball z₀ r, ‖fderiv ℝ u y stdComplexLineReal‖ ^ 2 < δ →
      r ^ 2 * ‖fderiv ℝ u z₀ stdComplexLineReal‖ ^ 2 ≤
        C * (r ^ 2 + ∫ y in ball z₀ r, ‖fderiv ℝ u y stdComplexLineReal‖ ^ 2) := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_toEuclidean_comp_sq_le hW hJ hX hD hK hDKW hJsq
  let L : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) := toEuclidean
  set N := ‖(L : F →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))‖
  set N' := ‖(L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) →L[ℝ] F)‖
  have hπ : 0 < π + N ^ 2 := by positivity
  refine ⟨δ / (π + N ^ 2), div_pos hδ hπ, N' ^ 2 * (7 + 8 * N ^ 2 / π), by positivity,
    fun u z₀ r hr hrD hu hu' hfl huK hE ↦ ?_⟩
  -- The energy in the coordinates of the inner product space is at most `N²` times that of `u`.
  have hIw := setIntegral_ball_norm_fderiv_comp_sq_le L hu'
  have hI0 : 0 ≤ ∫ y in ball z₀ r, ‖fderiv ℝ u y stdComplexLineReal‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hmv := hmean hr hrD hu hu' hfl huK <| by
    have h := (lt_div_iff₀ hπ).1 hE
    nlinarith [mul_nonneg pi_pos.le hI0, mul_nonneg (sq_nonneg N) (sq_nonneg r)]
  -- Return to `u` along `L.symm`.
  refine sq_mul_le_of_pi_mul_sq_mul_le ?_ hmv hIw hI0
  rw [fderiv_comp_comp_equivRealProdCLM_apply, equivRealProdCLM_one,
    equivRealProdCLM.apply_symm_apply, ← mul_pow]
  gcongr
  simpa using L.symm.toContinuousLinearMap.le_opNorm (L (fderiv ℝ u z₀ stdComplexLineReal))

end TauCeti.Floer

open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- On a ball of `ℝ × ℝ`, a square of area `(2 r)²`, a pointwise bound `g ≤ A f + B` integrates to
`∫ g ≤ A ∫ f + B (2 r)²`. -/
private theorem setIntegral_ball_le_mul_setIntegral_add {f g : ℝ × ℝ → ℝ} {z₀ : ℝ × ℝ}
    {r A B : ℝ} (hr : 0 ≤ r) (hg : IntegrableOn g (ball z₀ r)) (hf : IntegrableOn f (ball z₀ r))
    (h : ∀ y ∈ ball z₀ r, g y ≤ A * f y + B) :
    ∫ y in ball z₀ r, g y ≤ A * (∫ y in ball z₀ r, f y) + B * (2 * r) ^ 2 := by
  have hBi : IntegrableOn (fun _ ↦ B) (ball z₀ r) := integrableOn_const measure_ball_lt_top.ne
  calc ∫ y in ball z₀ r, g y ≤ ∫ y in ball z₀ r, (A * f y + B) :=
        setIntegral_mono_on hg ((hf.const_mul A).add hBi) measurableSet_ball h
    _ = A * (∫ y in ball z₀ r, f y) + B * (2 * r) ^ 2 := by
        rw [integral_add (hf.const_mul A) hBi, integral_const_mul, setIntegral_const,
          Real.volume_real_ball_prod z₀ hr, smul_eq_mul, mul_comm ((2 * r) ^ 2)]

/-- The arithmetic closing the mean-value inequality in a chart: the energy density `f₀` at the
centre is at most `A' g₀ + B'` for the coordinate density `g₀`, which the coordinate mean-value
inequality bounds by the coordinate energy `G`, in turn at most `κ` times the Floer energy `I`. -/
private theorem sq_mul_le_of_le_mul_add {f₀ g₀ r A' B' C κ G I : ℝ} (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (hC : 0 ≤ C) (hI : 0 ≤ I) (hf₀ : f₀ ≤ A' * g₀ + B') (hmv : r ^ 2 * g₀ ≤ C * (r ^ 2 + G))
    (hG : r ^ 2 + G ≤ κ * (r ^ 2 + I)) :
    r ^ 2 * f₀ ≤ (A' * C * κ + B') * (r ^ 2 + I) := by
  calc r ^ 2 * f₀ ≤ A' * (r ^ 2 * g₀) + B' * r ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hf₀ (sq_nonneg r)]
    _ ≤ A' * (C * (κ * (r ^ 2 + I))) + B' * (r ^ 2 + I) :=
        add_le_add (mul_le_mul_of_nonneg_left (hmv.trans (by gcongr)) hA')
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hI) hB')
    _ = (A' * C * κ + B') * (r ^ 2 + I) := by ring

/-- **The mean-value inequality for Floer solutions in a chart of a manifold.** Let `ω` be a
nondegenerate two-form on `M` and `α` a point of `M`. Let the structures `J(z, x)` and the
Hamiltonian vector fields of `K_s` and `K_t`, read in the chart at `α`, be `C²` on an open set
`W ⊆ (ℝ × ℝ) × E` containing `D × K`, for compact `D ⊆ ℝ × ℝ` and a compact set `K` of chart
coordinates, and let `J(z, x)` be tamed by `ω` on `D × K`. There are a threshold `δ > 0` and a
constant `C` with the following property. Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0`
for `J(z, u)` on a ball `B_r(z₀) ⊆ D` of `ℝ × ℝ`, with values in the chart source and chart
coordinates in `K`, let `u` be `C³` on the ball, and let `∂ₛ` of its coordinate expression
`extChartAt I α ∘ u` be continuous on the closed ball. If the Floer energy density
`e(u) = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` is integrable on the ball and
`r² + ∫_{B_r(z₀)} e(u) < δ`, then

`r² e(u)(z₀) ≤ C (r² + ∫_{B_r(z₀)} e(u))`.

So a small disc of small energy has energy density at its centre at most `C / r²` times the
energy plus `C`. Balls of `ℝ × ℝ` are squares for its sup norm. -/
theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy
    (hω : ω.IsNondegenerate) (α : M) {W : Set ((ℝ × ℝ) × E)} {D : Set (ℝ × ℝ)} {K : Set E}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J) W)
    (hXs : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks) W)
    (hXt : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt) W)
    (hD : IsCompact D) (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J z ((extChartAt I α).symm y))) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 ≤ r → ball z₀ r ⊆ D →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ (extChartAt I α ∘ u) y stdComplexLineReal)
        (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
        (ω.perturbedMFDeriv Ks Kt u y).toLinearMap) →
      MapsTo u (ball z₀ r) ((extChartAt I α).source ∩ extChartAt I α ⁻¹' K) →
      IntegrableOn (ω.floerEnergyDensity Ks Kt u) (ball z₀ r) →
      r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y < δ →
      r ^ 2 * ω.floerEnergyDensity Ks Kt u z₀ ≤
        C * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y) := by
  set e := extChartAt I α with he
  -- The energy density and `‖∂ₛv‖²` control each other on `D × K`, for `v = e ∘ u`.
  obtain ⟨A, hA0, B, hB0, hpt⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le (Kt := Kt) α
    hD hK hKα (hJ.continuousOn.mono hDKW) (hXs.continuousOn.mono hDKW) hJt
  obtain ⟨A', hA'0, B', hB'0, hrev⟩ :=
    ω.exists_forall_floerEnergyDensity_le_norm_fderiv_extChartAt_comp_sq (Kt := Kt) α hD hK hKα
      (hJ.continuousOn.mono hDKW) (hXs.continuousOn.mono hDKW)
  -- The mean-value inequality for the coordinate expressions.
  obtain ⟨δ, hδ, C, hC0, hmean⟩ :=
    Floer.exists_pos_forall_sq_mul_norm_fderiv_sq_le_of_small_energy_of_finiteDimensional hW hJ
      (contDiffOn_hamiltonianOneFormInChartAt hXs hXt) hD hK hDKW
      (fun z _ _ hy ↦ Floer.almostComplexInChartAt_apply_apply (hKα hy) z)
  set κ := 1 + A + 4 * B with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨δ / κ, div_pos hδ hκ0, A' * C * κ + B', by positivity,
    fun u z₀ r hr hrD hu hu' hfl huK hint hE ↦ ?_⟩
  set f := ω.floerEnergyDensity Ks Kt u
  set g : ℝ × ℝ → ℝ := fun y ↦ ‖fderiv ℝ (e ∘ u) y stdComplexLineReal‖ ^ 2
  have hus {y : ℝ × ℝ} (hy : y ∈ ball z₀ r) : u y ∈ e.source := (huK hy).1
  have hdiff {y : ℝ × ℝ} (hy : y ∈ ball z₀ r) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u y :=
    (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (isOpen_ball.mem_nhds hy)
  have hcd : ContDiffOn ℝ 3 (e ∘ u) (ball z₀ r) := contMDiffOn_iff_contDiffOn.1 <|
    (contMDiffOn_extChartAt (n := 3)).comp hu fun y hy ↦ by
      rw [mem_preimage, ← extChartAt_source I]; exact hus hy
  have hf0 : ∀ y ∈ ball z₀ r, 0 ≤ f y := fun y hy ↦ floerEnergyDensity_nonneg hω (by
    have h := hJt y (hrD hy) _ (huK hy).2
    rwa [e.left_inv (hus hy)] at h) (hfl y hy)
  have hgf : ∀ y ∈ ball z₀ r, g y ≤ A * f y + B := fun y hy ↦
    hpt (hrD hy) (hus hy) (huK hy).2 (hdiff hy) (hfl y hy)
  have hIf0 : 0 ≤ ∫ y in ball z₀ r, f y := setIntegral_nonneg measurableSet_ball hf0
  -- The coordinate energy is controlled by the Floer energy and the area `4 r²` of the square.
  have hIg := setIntegral_ball_le_mul_setIntegral_add hr
    ((hu'.norm.pow 2).integrableOn_compact (isCompact_closedBall z₀ r) |>.mono_set
      ball_subset_closedBall) hint hgf
  have hIgκ : r ^ 2 + ∫ y in ball z₀ r, g y ≤ κ * (r ^ 2 + ∫ y in ball z₀ r, f y) := by
    rw [hκ]
    linear_combination hIg + mul_nonneg hA0 (sq_nonneg r) + 4 * mul_nonneg hB0 hIf0 + hIf0
  have hmv := hmean hr hrD hcd hu' (fun y hy ↦ by
      simpa only [hamiltonianOneFormInChartAt_stdComplexLineReal,
        hamiltonianOneFormInChartAt_stdComplexLineImag, ← he, Function.comp_apply] using
        ω.fderiv_extChartAt_comp_stdComplexLineImag_sub (hdiff hy) (hus hy) (hfl y hy))
    (fun y hy ↦ (huK hy).2) (hIgκ.trans_lt <| by
      calc κ * (r ^ 2 + ∫ y in ball z₀ r, f y) < κ * (δ / κ) := by gcongr
        _ = δ := mul_div_cancel₀ _ hκ0.ne')
  -- At the centre, the energy density is controlled by `‖∂ₛv‖²`.
  rcases hr.eq_or_lt with rfl | hr0
  · simp
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr0
  exact sq_mul_le_of_le_mul_add hA'0 hB'0 hC0 hIf0 (hrev (hrD hz₀) (hus hz₀) (huK hz₀).2
    (hdiff hz₀) (hfl z₀ hz₀)) hmv hIgκ

end TauCeti.SmoothTwoForm
