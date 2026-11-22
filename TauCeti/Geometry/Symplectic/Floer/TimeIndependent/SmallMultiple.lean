/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.SmallHamiltonian
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.ODE.Yorke
import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.Geometry.Symplectic.Floer.Manifold.Translation
import TauCeti.Geometry.Symplectic.Floer.Trajectory
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# Floer cylinders of small multiples of an autonomous Hamiltonian

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `ω(·, J ·)` of a
constant compatible almost complex structure `J`, let `H : V → ℝ` be a `C³` Hamiltonian whose
Hamiltonian vector field has bounded first and second derivatives, and let `K ⊆ V` be compact.
This file shows that there is `ε₀ > 0` such that for `|ε| < ε₀` every finite-energy Floer cylinder
of `εH` with image in `K`, that is every solution `u` of period one in `t` of

`∂s u + J (∂t u - ε X_H(u)) = 0`,

is independent of `t`
(`TauCeti.SymplecticForm.exists_pos_forall_eq_comp_fst_of_isComplexLinearMap`) and so is an
upward gradient line of `εH`
(`TauCeti.SymplecticForm.exists_pos_forall_hasDerivAt_gradient_of_isComplexLinearMap`). The
threshold `ε₀` depends on `ω`, `J`, `H` and `K` only, not on the cylinder. This is one half of
Floer's identification, on a flat target, of the Floer cylinders of a small autonomous Hamiltonian
with its gradient lines: for a fixed `H`, the cylinders of `εH` in `K` are gradient lines. It
gives no threshold in terms of a `C²` norm, and it does not show that every gradient line is a
cylinder.

The analytic core is `TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`:
a cylinder of `εH` whose derivative is bounded by `M` is independent of `t` as soon as
`|ε| ‖d²X_H‖ M` is small compared with `(2π - |ε| ‖dX_H‖)²`. This file supplies the bound `M`,
uniformly in `ε` and in the cylinder.

* **The ends are critical points.** By Yorke's theorem
  (`Function.Periodic.eq_const_of_hasDerivAt_of_lipschitzOnWith`) the one-periodic orbits of the
  vector field `ε X_H`, which is `|ε| ‖dX_H‖`-Lipschitz, are constant once `|ε| ‖dX_H‖ < 2π`. The
  ends of a finite-energy cylinder are such orbits
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq`), so its
  energy is the difference `εH(p₁) - εH(p₀)` of the values of `εH` at two points of `K`, which is
  at most `2 |ε| sup_K |H|`.
* **Small energy bounds the derivative.** By Gromov–Floer compactness over the compact window
  `ε ∈ [-1, 1]`
  (`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`),
  there are `δ > 0` and `M` such that every solution on the square `|s|, |t| < 1/2` with image
  in `K` and energy at most `δ` there has derivative at most `M` at the centre: otherwise a
  sequence of solutions with unbounded derivative at the centre would have to bubble, at the cost
  of energy at least `2δ`. Translating a cylinder, every such square lies in a horizontal strip
  of width one, over which the energy of the cylinder is its total energy
  (`TauCeti.setLIntegral_univ_prod_Icc_add_eq_of_periodic`).

So for `|ε|` small the energy of every cylinder of `εH` in `K` is below `δ`, its derivative is
bounded by `M` everywhere, and the slice-energy argument applies.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the Floer cylinders of
  `C²`-small Hamiltonians.
* J. A. Yorke, *Periods of periodic solutions and the Lipschitz constant*, Proc. Amer. Math. Soc.
  **22** (1969), 509–512.
-/

public section

open Real Set Filter Topology MeasureTheory Function Metric
open scoped Gradient RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {K : Set V} {a c : ℝ}

/-! ### The Hamiltonian vector field of `εH` -/

section Scaling

omit [FiniteDimensional ℝ V] in
/-- The perturbation `εH dt`, as a function of the domain point and the target point, is `C¹`. -/
private theorem contDiff_const_mul_comp_snd {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hH : ContDiff ℝ 3 H) (ε : ℝ) : ContDiff ℝ 1 (uncurry fun (_ : W) (y : V) ↦ ε * H y) :=
  contDiff_const.mul ((hH.of_le (by norm_num)).comp contDiff_snd)

/-- A bound `a` on `dX_H` gives the bound `|ε| a` on `dX_{εH}`. -/
private theorem norm_fderiv_hamiltonianVectorField_const_mul_le (hH : ContDiff ℝ 3 H)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a) (ε : ℝ) (x : V) :
    ‖fderiv ℝ (ω.hamiltonianVectorField fun y ↦ ε * H y) x‖ ≤ |ε| * a := by
  have hX := (ω.contDiff_hamiltonianVectorField (n := 2) hH).differentiable (by norm_num)
  rw [hamiltonianVectorField_const_mul', fderiv_const_smul (hX x), norm_smul, norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (ha x) (abs_nonneg ε)

/-- A bound `c` on `d²X_H` gives the bound `|ε| c` on `d²X_{εH}`. -/
private theorem norm_fderiv_fderiv_hamiltonianVectorField_const_mul_le (hH : ContDiff ℝ 3 H)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c) (ε : ℝ) (x : V) :
    ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField fun y ↦ ε * H y)) x‖ ≤ |ε| * c := by
  have hX := ω.contDiff_hamiltonianVectorField (n := 2) hH
  have hdX : fderiv ℝ (ω.hamiltonianVectorField fun y ↦ ε * H y) =
      ε • fderiv ℝ (ω.hamiltonianVectorField H) := funext fun y ↦ by
    rw [hamiltonianVectorField_const_mul', fderiv_const_smul (hX.differentiable (by norm_num) y),
      Pi.smul_apply]
  have hddX := (hX.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  rw [hdX, fderiv_const_smul hddX]
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hc x) (abs_nonneg ε)

end Scaling

/-! ### The energy of a cylinder of `εH` -/

section Energy

/-- **The energy of a cylinder of `εH`.** If `|ε| a < 2π`, where `a` bounds `dX_H`, the one-periodic
orbits of `εH` are constant, so a finite-energy Floer cylinder of `εH` with image in `K` has energy
`εH(p₁) - εH(p₀)` for two points `p₀, p₁ ∈ K`, which is at most `2 |ε| B` for a bound `B` of `|H|`
on `K`. -/
private theorem lintegral_floerEnergyDensity_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hK : IsCompact K) {B : ℝ} (hB : ∀ x ∈ K, |H x| ≤ B) {ε : ℝ} (hε : |ε| * a < 2 * π)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 3 u) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (huK : ∀ z, u z ∈ K)
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) ≠ ⊤) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) ≤
      ENNReal.ofReal (2 * |ε| * B) := by
  have hHε : ContDiff ℝ 1 (uncurry fun (_ : ℝ) (y : V) ↦ ε * H y) :=
    contDiff_const_mul_comp_snd hH ε
  obtain ⟨x₀, x₁, ⟨hx₀per, hx₀, hx₀K⟩, ⟨hx₁per, hx₁, hx₁K⟩, -, -, hEq⟩ :=
    exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq (ω := ω)
      (H := fun _ y ↦ ε * H y) (J := fun _ ↦ J) (c := 1)
      (M := ‖J.toLinearMap.toContinuousLinearMap‖) hHε (fun _ ↦ rfl)
      (hu.of_le (by norm_num)) (fun s t ↦ hper s t) hK (fun s t ↦ huK (s, t)) one_pos
      (fun _ _ v ↦ by rw [one_mul, hg, real_inner_self_eq_norm_sq])
      (fun _ _ v ↦ J.toLinearMap.toContinuousLinearMap.le_opNorm v) (fun z _ ↦ hfl z) hE
  -- The vector field `ε X_H` is `|ε| a`-Lipschitz, so by Yorke's theorem the orbits are constant.
  have hlip : LipschitzWith (Real.toNNReal (|ε| * a)) (ω.hamiltonianVectorField fun y ↦ ε * H y) :=
    lipschitzWith_of_nnNorm_fderiv_le
      ((ω.contDiff_hamiltonianVectorField (n := 2)
        (contDiff_const.mul hH)).differentiable (by norm_num))
      fun x ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal']
        exact (norm_fderiv_hamiltonianVectorField_const_mul_le hH ha ε x).trans (le_max_left _ _)
  have hyorke : (Real.toNNReal (|ε| * a) : ℝ) * 1 < 2 * π := by
    rw [mul_one, Real.coe_toNNReal']
    exact max_lt hε (by positivity)
  have hconst {x : ℝ → V} (hxper : Periodic x 1)
      (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (fun y ↦ ε * H y) (x t)) t) :
      x = fun _ ↦ x 0 :=
    hxper.eq_const_of_hasDerivAt_of_lipschitzOnWith one_pos hx hlip.lipschitzOnWith
      (by exact_mod_cast hyorke)
  rw [hEq, hconst hx₀per hx₀, hconst hx₁per hx₁]
  simp only [hamiltonianAction_const, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    one_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  have h₀ := hB _ (hx₀K 0)
  have h₁ := hB _ (hx₁K 0)
  rw [← mul_sub]
  calc ε * (H (x₁ 0) - H (x₀ 0)) ≤ |ε| * |H (x₁ 0) - H (x₀ 0)| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |ε| * (B + B) := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add h₁ h₀)
    _ = 2 * |ε| * B := by ring

end Energy

/-! ### Small energy bounds the derivative -/

section Derivative

/-- **Small energy bounds the derivative at the centre.** There are `δ > 0` and `M` such that for
every `ε ∈ [-1, 1]`, every `C³` solution `u` of the Floer equation of `εH` with image in `K` and
energy at most `δ` over the open square `|s|, |t| < 1/2` has `‖du(0)‖ ≤ M`. -/
private theorem exists_pos_forall_norm_fderiv_zero_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (hK : IsCompact K) :
    ∃ δ > 0, ∃ M, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, ε ∈ Icc (-1) 1 → ContDiff ℝ 3 u →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in ball (0 : ℝ × ℝ) (1 / 2),
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) ≤
        ENNReal.ofReal δ →
      ‖fderiv ℝ u 0‖ ≤ M := by
  have hJt : ω.Tames J := fun v hv ↦ by
    rw [hg, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 hv) 2
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (P := ℝ) (Ks := fun _ _ _ ↦ 0) (Kt := fun p _ y ↦ p * H y) (J := fun _ _ _ ↦ J)
    (W := univ) (C := Icc (-1) 1) (D := closedBall (0 : ℝ × ℝ) (1 / 2)) (K := K) isOpen_univ
    contDiffOn_const (contDiff_fst.mul (hH.comp (contDiff_snd.comp contDiff_snd))).contDiffOn
    contDiffOn_const isCompact_Icc (isCompact_closedBall _ _) hK (subset_univ _)
    fun _ _ _ _ _ _ ↦ hJt
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  by_contra! hM
  -- Otherwise there are solutions `u k` with `‖du_k(0)‖ > k`.
  choose ε u hε hu hfl huK hE hlt using fun k : ℕ ↦ hM k
  have hden (k : ℕ) := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0)
    (Kt := fun _ y ↦ ε k * H y) isOpen_univ ((hu k).of_le (by norm_num)).contDiffOn contDiffOn_const
    (contDiff_const_mul_comp_snd hH (ε k)).contDiffOn
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε k * H y) (u k))
      (ball (0 : ℝ × ℝ) (1 / 2)) :=
    ((hden k).mono (subset_univ _)).integrableOn_compact (isCompact_closedBall _ _)
      |>.mono_set ball_subset_closedBall
  have hEle (k : ℕ) :
      ∫ z in ball (0 : ℝ × ℝ) (1 / 2), ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun _ y ↦ ε k * H y) (u k) z ≤ δ / 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦
      ω.floerEnergyDensity_nonneg hJt (hfl k z)) (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (half_pos hδ).le (hE k)
  obtain ⟨φ, -, Z, -, hφ, -, -, -, hZ, -, hbdd, -⟩ := hconv isOpen_ball ball_subset_closedBall hε
    (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) (fun k _ _ ↦ huK k _) hint hEle
  -- The energy `δ / 2` is too small for a bubble, so there are no bubbling points.
  have hZ0 : Z = ∅ := by
    refine Finset.card_eq_zero.1 (Nat.lt_one_iff.1 ?_)
    by_contra! h1
    have : (1 : ℝ) * δ ≤ δ / 2 := (mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hδ.le).trans hZ
    linarith
  obtain ⟨M, hMb⟩ := hbdd {0} isCompact_singleton (by simp [hZ0])
  obtain ⟨n, hn⟩ := exists_nat_ge M
  have h1 := hMb n 0 rfl
  have h2 := hlt (φ n)
  have h3 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  linarith

end Derivative

/-! ### Floer cylinders of `εH` -/

section Main

/-- The energy of a cylinder over the square of side one centred at any point is at most its energy
over the strip `ℝ × [0, 1]`. -/
private theorem setLIntegral_ball_floerEnergyDensity_le (hH : ContDiff ℝ 3 H) {ε : ℝ}
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 3 u) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (z₀ : ℝ × ℝ) :
    ∫⁻ z in ball (0 : ℝ × ℝ) (1 / 2), ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun _ y ↦ ε * H y) (fun w ↦ u (w + z₀)) z) ≤
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) := by
  have hpre : (· + z₀) ⁻¹' ball z₀ (1 / 2) = ball (0 : ℝ × ℝ) (1 / 2) := by
    ext z
    simp [mem_ball, dist_eq_norm]
  have htr := ω.constSmooth.lintegral_floerEnergyDensity_comp_add_right (fun _ _ ↦ 0)
    (fun _ y ↦ ε * H y) u z₀ (ball z₀ (1 / 2))
  rw [hpre] at htr
  simp only [floerEnergyDensity_constSmooth] at htr
  rw [htr]
  -- The square lies in the horizontal strip `ℝ × [t₀ - 1/2, t₀ + 1/2]` of width one.
  have hsub : ball z₀ (1 / 2) ⊆ (univ : Set ℝ) ×ˢ Icc (z₀.2 - 1 / 2) (z₀.2 - 1 / 2 + 1) := by
    intro z hz
    have h := (mem_ball'.1 hz).le.trans_eq' (dist_comm _ _)
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq] at h
    exact ⟨mem_univ _, by linarith [abs_le.1 h.2], by linarith [abs_le.1 h.2]⟩
  have hden := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0)
    (Kt := fun _ y ↦ ε * H y) isOpen_univ (hu.of_le (by norm_num)).contDiffOn contDiffOn_const
    (contDiff_const_mul_comp_snd hH ε).contDiffOn
  have hmeas : Measurable fun z ↦
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) :=
    ENNReal.measurable_ofReal.comp (continuousOn_univ.1 hden).measurable
  have hdper (s t : ℝ) : ENNReal.ofReal
      (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u (s, t + 1)) =
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u (s, t)) := by
    simp only [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
      perturbedFDeriv_apply_stdComplexLineImag, fderiv_add_snd_of_periodic_snd hper, hper]
  exact (lintegral_mono_set hsub).trans_eq
    (by simpa only [Measure.volume_eq_prod] using
      setLIntegral_univ_prod_Icc_add_eq_of_periodic one_pos hmeas hdper _)

/-- **A uniform bound on the derivative.** There are `ε₀ > 0` and `M` such that for `|ε| < ε₀`
every finite-energy Floer cylinder `u` of `εH` with image in `K` has `‖du‖ ≤ M` everywhere, and
`|ε| a` and `|ε| c M` satisfy the smallness conditions of
`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv` for `εH`. -/
private theorem exists_pos_forall_norm_fderiv_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c) (hK : IsCompact K) :
    ∃ ε₀ > 0, ∃ M, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, |ε| < ε₀ → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) → (∀ z, u z ∈ K) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) ≠ ⊤ →
      |ε| * a < 2 * π ∧ |ε| * c * M < 2 * (2 * π - |ε| * a) ^ 2 ∧ ∀ z, ‖fderiv ℝ u z‖ ≤ M := by
  obtain ⟨δ, hδ, M, hM⟩ := exists_pos_forall_norm_fderiv_zero_le hg hH hK
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hH.continuous.continuousOn
  have ha0 : 0 ≤ a := (ContinuousLinearMap.opNorm_nonneg _).trans (ha 0)
  have hc0 : 0 ≤ c := (ContinuousLinearMap.opNorm_nonneg _).trans (hc 0)
  have hM0 : 0 ≤ |M| := abs_nonneg M
  -- The threshold: `ε ∈ [-1, 1]`, `|ε| a ≤ π`, energy `2 |ε| |B| ≤ δ` and `|ε| c |M| < π²`.
  refine ⟨min 1 (min (π / (a + 1)) (min (δ / (2 * |B| + 1)) (π ^ 2 / (c * |M| + 1)))),
    by positivity, |M|, fun ε u hε hu hper huK hfl hE ↦ ?_⟩
  simp only [lt_min_iff] at hε
  obtain ⟨hε1, hεa, hεδ, hεc⟩ := hε
  have hεa' : |ε| * a ≤ π := by
    rw [lt_div_iff₀ (by positivity)] at hεa
    nlinarith [abs_nonneg ε]
  have hεδ' : 2 * |ε| * |B| ≤ δ := by
    rw [lt_div_iff₀ (by positivity)] at hεδ
    nlinarith [abs_nonneg ε]
  have hεc' : |ε| * c * |M| < π ^ 2 := by
    rw [lt_div_iff₀ (by positivity)] at hεc
    nlinarith [abs_nonneg ε, mul_nonneg hc0 hM0]
  have hEle := lintegral_floerEnergyDensity_le hg hH ha hK (B := |B|)
    (fun x hx ↦ (Real.norm_eq_abs _ ▸ hB x hx).trans (le_abs_self B))
    (hεa'.trans_lt (by linarith [pi_pos])) hu hper huK hfl hE
  refine ⟨hεa'.trans_lt (by linarith [pi_pos]), by nlinarith [pi_pos, abs_nonneg ε], fun z₀ ↦ ?_⟩
  -- The translate of `u` by `z₀` has energy at most `δ` on the square about `0`.
  have h := hM (ε := ε) (u := fun w ↦ u (w + z₀)) (abs_le.1 hε1.le)
    (hu.comp (contDiff_id.add contDiff_const))
    (fun z ↦ by
      have := hfl (z + z₀)
      rwa [← ω.perturbedFDeriv_comp_add_right] at this)
    (fun z ↦ huK _)
    ((setLIntegral_ball_floerEnergyDensity_le hH hu hper z₀).trans
      (hEle.trans (ENNReal.ofReal_le_ofReal hεδ')))
  rw [fderiv_comp_add_right, zero_add] at h
  exact h.trans (le_abs_self M)

/-- **Floer cylinders of small multiples of an autonomous Hamiltonian are time-independent.** Let
the inner product of `V` be the metric `ω(·, J ·)` of a constant compatible structure `J`, let `H`
be a `C³` Hamiltonian with `‖dX_H‖ ≤ a` and `‖d²X_H‖ ≤ c` everywhere, and let `K ⊆ V` be compact.
There is `ε₀ > 0` such that for `|ε| < ε₀` every `C³` solution `u` of
`∂s u + J (∂t u - ε X_H(u)) = 0` of period one in `t`, with image in `K` and finite energy, is
independent of `t`: `u(s, t) = u(s, 0)`. -/
theorem exists_pos_forall_eq_comp_fst_of_isComplexLinearMap (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c) (hK : IsCompact K) :
    ∃ ε₀ > 0, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, |ε| < ε₀ → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) → (∀ z, u z ∈ K) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) ≠ ⊤ →
      u = fun z ↦ u (z.1, 0) := by
  obtain ⟨ε₀, hε₀, M, h⟩ := exists_pos_forall_norm_fderiv_le hg hH ha hc hK
  refine ⟨ε₀, hε₀, fun ε u hε hu hper huK hfl hE ↦ ?_⟩
  obtain ⟨ha', hcM, hM⟩ := h hε hu hper huK hfl hE
  exact eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv hg (contDiff_const.mul hH)
    (norm_fderiv_hamiltonianVectorField_const_mul_le hH ha ε)
    (norm_fderiv_fderiv_hamiltonianVectorField_const_mul_le hH hc ε) ha' hcM hu hper hfl hM

/-- **Floer cylinders of small multiples of an autonomous Hamiltonian are gradient lines.** Under
the hypotheses of `TauCeti.SymplecticForm.exists_pos_forall_eq_comp_fst_of_isComplexLinearMap`,
there is `ε₀ > 0` such that for `|ε| < ε₀` the curve `γ(s) = u(s, 0)` of every such cylinder `u`
of `εH` is an upward gradient line of `εH`, `γ' = ∇(εH)(γ)`, for the metric `ω(·, J ·)`. -/
theorem exists_pos_forall_hasDerivAt_gradient_of_isComplexLinearMap
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 3 H)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c) (hK : IsCompact K) :
    ∃ ε₀ > 0, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, |ε| < ε₀ → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) → (∀ z, u z ∈ K) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ ε * H y) u z) ≠ ⊤ →
      ∀ s, HasDerivAt (fun s ↦ u (s, 0)) (∇ (fun y ↦ ε * H y) (u (s, 0))) s := by
  obtain ⟨ε₀, hε₀, M, h⟩ := exists_pos_forall_norm_fderiv_le hg hH ha hc hK
  refine ⟨ε₀, hε₀, fun ε u hε hu hper huK hfl hE ↦ ?_⟩
  obtain ⟨ha', hcM, hM⟩ := h hε hu hper huK hfl hE
  exact hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv hg (contDiff_const.mul hH)
    (norm_fderiv_hamiltonianVectorField_const_mul_le hH ha ε)
    (norm_fderiv_fderiv_hamiltonianVectorField_const_mul_le hH hc ε) ha' hcM hu hper hfl hM

end Main

end TauCeti.SymplecticForm
