/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.SmallEnergy
public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Bubble
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
import TauCeti.Geometry.Symplectic.JHolomorphic.Regularity

/-!
# No bubbling for Floer solutions in a symplectic vector space

Let `(V, ω)` be a finite-dimensional symplectic vector space. Gromov–Floer compactness for
solutions of the Floer equation `(du - X_{Ks,Kt})^{0,1} = 0` of bounded energy has to deal with
bubbling: where the derivatives of a sequence of solutions blow up, rescaling produces a
nonconstant pseudoholomorphic plane of finite area, the bubble
(`TauCeti.SymplecticForm.exists_tendstoLocallyUniformly_rescale_of_tendsto_norm_fderiv`). In a
symplectic vector space the form is exact and such planes do not exist, so the derivatives of
solutions of bounded energy with values in a compact set stay bounded. This file proves this, for
every energy level and not only below the bubbling threshold of
`TauCeti.Geometry.Symplectic.Floer.Compactness.SmallEnergy`. The results, in the namespace
`TauCeti.SymplecticForm`, are the following.

* **No blow-up at a point**
  (`not_tendsto_norm_fderiv_atTop_of_setLIntegral_floerEnergyDensity_le`).
  For a `C²` perturbation `Ks ds + Kt dt` and a `C²` almost complex structure `J(z, x)` on
  `U × V`, the derivatives of smooth solutions `uₙ` on `U` with values in a compact set `K` and
  energy over `U` bounded by `E` cannot tend to infinity along points `zₙ → z₀ ∈ U`, provided that
  `ω` tames `J(z₀, x)` for `x ∈ K`. The bubble `v` at `z₀` is a `C¹` plane, holomorphic for the
  frozen structure `J(z₀, ·)`, with `‖dv(0)‖ = 1` and with area at most `E`. Tameness on the
  compact set `K` bounds `‖dv‖²` by a multiple of the area density, so `‖dv‖²` is integrable, and
  then `v` is constant
  (`TauCeti.SymplecticForm.exists_eq_const_of_isComplexLinearMap_of_contDiff_one`), which
  contradicts `‖dv(0)‖ = 1`.
* **Bounded derivatives on compact sets**
  (`exists_forall_norm_fderiv_le_of_isCompact_of_setLIntegral_floerEnergyDensity_le`). For a
  compact `D ⊆ U` on which `J` is tamed by `ω` over `K`, there is a bound `M` on `‖du‖` over `D`,
  uniform over all smooth solutions on `U` with values in `K` and energy over `U` at most `E`.
* **Bounded derivatives of Floer cylinders**
  (`exists_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le`,
  and `exists_lipschitzWith_of_setLIntegral_floerEnergyDensity_le` in
  Lipschitz form). For a Hamiltonian `H_t` of period one in `t` and an almost complex structure
  `J_t(x)` tamed by `ω` on `K`, there is a bound on `‖du‖` over the whole cylinder, uniform over all
  smooth Floer cylinders `u` of period one with values in `K` and energy at most `E` over
  `ℝ × [0, 1]`. As in `TauCeti.Geometry.Symplectic.Floer.Compactness.SmallEnergy`, translation in
  `s` and periodicity in `t` move any point into the window `(-1, 1) × (-1/2, 3/2)`, whose energy
  is at most `3 E`.

The uniform Lipschitz bound is the hypothesis under which the levels of sequences of Floer
trajectories are selected and matched in `TauCeti.Geometry.Symplectic.Floer.Trajectory.Breaking`
and `TauCeti.Geometry.Symplectic.Floer.Trajectory.BrokenLimit`. It holds for smooth trajectories
with values in a compact set and bounded energy, for one `C²` structure `J_t(x)` tamed on that set.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.2
  (rescaling where the derivatives blow up), Section 4.6 (bubbling) and Section 8.1 (bubbles of
  inhomogeneous equations are holomorphic for the frozen structure).
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V} {U : Set (ℝ × ℝ)}
  {z₀ : ℝ × ℝ}

/-- **No blow-up of the derivatives in a symplectic vector space.** Let the perturbation
`Ks ds + Kt dt` be `C²` and `J(z, x)` be `C²` on `U × V` for an open set `U ⊆ ℝ × ℝ`, and let
`uₙ` be smooth solutions of the Floer equation `(du - X_{Ks,Kt})^{0,1} = 0` for `J(z, u)` on `U`,
with values in a compact set `K` and Floer energy over `U` at most `E`. If `ω` tames `J(z₀, x)`
for `x ∈ K`, then the derivatives `‖duₙ(zₙ)‖` do not tend to infinity along any sequence of points
`zₙ → z₀ ∈ U`. -/
theorem not_tendsto_norm_fderiv_atTop_of_setLIntegral_floerEnergyDensity_le
    (ω : SymplecticForm V) {K : Set V} {u : ℕ → ℝ × ℝ → V} {z : ℕ → ℝ × ℝ} {E : ℝ}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hK : IsCompact K)
    (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    (htame : ∀ x ∈ K, ω.Tames (J z₀ x))
    (hu : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (u n) U) (huK : ∀ n, MapsTo (u n) U K)
    (hsol : ∀ n, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u n y))
      (ω.perturbedFDeriv Ks Kt (u n) y : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∀ n, ∫⁻ y in U, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u n) y) ≤ ENNReal.ofReal E)
    (hz : Tendsto z atTop (𝓝 z₀)) :
    ¬ Tendsto (fun n ↦ ‖fderiv ℝ (u n) (z n)‖) atTop atTop := by
  intro hblow
  obtain ⟨φ, c, ε, v, -, -, -, -, -, -, hv, hvK, hhol, hv0, -, harea⟩ :=
    ω.exists_tendstoLocallyUniformly_rescale_of_tendsto_norm_fderiv hU hz₀ hK hKs hKt
      (hJ.of_le one_le_two) hu huK hsol hz hblow
  -- The bubble `v` is holomorphic for the structure `J₀ = J(z₀, ·)`, which is `C²`.
  set J₀ : V → AlmostComplexStructure V := J z₀
  have hJ₀ : ContDiff ℝ 2 (fun x ↦ (J₀ x).toLinearMap.toContinuousLinearMap) :=
    contDiffOn_univ.1 (hJ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      fun x _ ↦ ⟨hz₀, mem_univ x⟩)
  have hCR (w : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₀ (v w))
      (fderiv ℝ v w : ℝ × ℝ →ₗ[ℝ] V) :=
    (hhol w).fderiv_isComplexLinear
  -- Its area is at most `E`, the energy over a disc about `z₀` inside `U`.
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hA : ∫⁻ w, ENNReal.ofReal
      (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag)) ≤
        ENNReal.ofReal E :=
    (harea δ hδ).trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n ↦
      (lintegral_mono_set hball).trans (hE _)))
  -- Tameness on `K` bounds `‖dv‖²` by a multiple of the area density, so `‖dv‖²` is integrable.
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le (ω := ω)
    (J := fun _ ↦ J₀) hK
    (hJ₀.continuous.comp continuous_snd).continuousOn (fun _ ↦ rfl) fun _ ↦ htame
  have hpt (w : ℝ × ℝ) : ENNReal.ofReal (‖fderiv ℝ v w‖ ^ 2) ≤ ENNReal.ofReal ((1 + M) ^ 2 / c) *
      ENNReal.ofReal (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm]
    exact ω.mul_opNorm_sq_le_of_isComplexLinearMap hc (fun a ↦ (hcM 0 _ (hvK w) a).1)
      (fun a ↦ (hcM 0 _ (hvK w) a).2) (hCR w)
  have hint : Integrable fun w ↦ ‖fderiv ℝ v w‖ ^ 2 := by
    refine ⟨((hv.continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (.of_forall fun w ↦ by positivity)).2 ?_⟩
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hA.trans_lt ENNReal.ofReal_lt_top)
  -- So the bubble is constant, contradicting `‖dv(0)‖ = 1`.
  obtain ⟨a, rfl⟩ := ω.exists_eq_const_of_isComplexLinearMap_of_contDiff_one isOpen_univ
    hJ₀.contDiffOn hv (fun _ ↦ mem_univ _) (fun w ↦ htame _ (hvK w)) hCR hint
  simp at hv0

/-- **Floer solutions of bounded energy in a symplectic vector space have bounded derivatives on
compact sets.** Let the perturbation `Ks ds + Kt dt` be `C²` and `J(z, x)` be `C²` on `U × V`
for an open set `U ⊆ ℝ × ℝ`, let `D ⊆ U` be compact and `K ⊆ V` compact, with `J(z, x)` tamed by
`ω` for `z ∈ D` and `x ∈ K`. For every `E` there is a bound `M` such that every smooth solution
`u` of the Floer equation `(du - X_{Ks,Kt})^{0,1} = 0` for `J(z, u)` on `U`, with values in `K`
and Floer energy over `U` at most `E`, satisfies `‖du‖ ≤ M` on `D`. -/
theorem exists_forall_norm_fderiv_le_of_isCompact_of_setLIntegral_floerEnergyDensity_le
    (ω : SymplecticForm V)
    {K : Set V} {D : Set (ℝ × ℝ)} (hU : IsOpen U) (hD : IsCompact D) (hDU : D ⊆ U)
    (hK : IsCompact K) (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    (htame : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) (E : ℝ) :
    ∃ M, ∀ ⦃u : ℝ × ℝ → V⦄, ContDiffOn ℝ (⊤ : ℕ∞) u U → MapsTo u U K →
      (∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
        (ω.perturbedFDeriv Ks Kt u y : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ y in U, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u y) ≤ ENNReal.ofReal E →
      ∀ z ∈ D, ‖fderiv ℝ u z‖ ≤ M := by
  by_contra hM
  push Not at hM
  -- Solutions `uₙ` with `‖duₙ(zₙ)‖ > n` at points `zₙ ∈ D`; along a subsequence `zₙ → z₀ ∈ D`.
  choose u hu huK hsol hE z hzD hz using fun n : ℕ ↦ hM n
  obtain ⟨z₀, hz₀, ψ, hψ, hlim⟩ := hD.tendsto_subseq hzD
  refine ω.not_tendsto_norm_fderiv_atTop_of_setLIntegral_floerEnergyDensity_le hU (hDU hz₀) hK hKs
    hKt hJ (htame z₀ hz₀) (fun n ↦ hu (ψ n)) (fun n ↦ huK (ψ n)) (fun n ↦ hsol (ψ n))
    (fun n ↦ hE (ψ n)) hlim ?_
  refine tendsto_atTop_mono (fun n ↦ ?_) tendsto_natCast_atTop_atTop
  exact (Nat.cast_le.2 (hψ.id_le n)).trans (hz (ψ n)).le

/-- **Floer cylinders of bounded energy in a symplectic vector space have bounded derivatives.**
Let `H_t` be a `C²` Hamiltonian of period one in `t` and `J_t(x)` a `C²` almost complex structure,
and let `K ⊆ V` be compact with `J_t(x)` tamed by `ω` for `x ∈ K`. For every `E` there is a
bound `M` such that every smooth solution `u` of the Floer equation
`∂s u + J_t(u) (∂t u - X_{H_t}(u)) = 0` of period one in `t`, with values in `K` and Floer energy at
most `E` over the strip `ℝ × [0, 1]`, satisfies `‖du‖ ≤ M` everywhere. -/
theorem exists_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V} {K : Set V}
    (hH : ContDiff ℝ 2 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hK : IsCompact K) (htame : ∀ t, ∀ x ∈ K, ω.Tames (J t x)) (E : ℝ) :
    ∃ M, ∀ ⦃u : ℝ × ℝ → V⦄, ContDiff ℝ (⊤ : ℕ∞) u → (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in univ ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
        ENNReal.ofReal E →
      ∀ z, ‖fderiv ℝ u z‖ ≤ M := by
  set Ω : Set (ℝ × ℝ) := ball ((0 : ℝ), (1 / 2 : ℝ)) 1
  -- The bound on the closed ball about `(0, 1/2)` for solutions on the window `Ω`.
  obtain ⟨M, hM⟩ :=
    ω.exists_forall_norm_fderiv_le_of_isCompact_of_setLIntegral_floerEnergyDensity_le
    (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) (J := fun w ↦ J w.2) (U := Ω) isOpen_ball
    (isCompact_closedBall _ _) (closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1)) hK
    contDiffOn_const
    (contDiff_uncurry_cylindrical hH).contDiffOn
    ((hJ.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn)
    (fun z _ x hx ↦ htame z.2 x hx) (3 * E)
  refine ⟨M, fun u hu hper hfl huK hE z ↦ ?_⟩
  -- Move `z` to a point `(0, t)` with `t ∈ [0, 1)`, by periodicity in `t` and translation in `s`.
  obtain ⟨t, ht, hvd⟩ := exists_mem_Ico_fderiv_comp_add_right_eq zero_lt_one hper z
  have hE3 : ∫⁻ w in Ω, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
      (fun w ↦ u (w + (z.1, 0))) w) ≤ ENNReal.ofReal (3 * E) := by
    refine (lintegral_ball_floerEnergyDensity_comp_add_le hHper hper z.1).trans ?_
    rcases le_or_gt 0 E with - | hE0
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
    · rw [ENNReal.ofReal_of_nonpos hE0.le] at hE
      rw [nonpos_iff_eq_zero.1 hE, mul_zero]
      exact bot_le
  have h := hM (u := fun w ↦ u (w + (z.1, 0)))
    ((hu.comp (contDiff_id.add contDiff_const)).contDiffOn)
    (fun w _ ↦ huK _) (fun w _ ↦ isComplexLinearMap_perturbedFDeriv_comp_add_right hfl z.1 w) hE3
    ((0 : ℝ), t) (by
      simp only [mem_closedBall, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, max_le_iff,
        abs_le]
      exact ⟨by norm_num, by constructor <;> linarith [ht.1, ht.2]⟩)
  rwa [hvd] at h

/-- **Floer cylinders of bounded energy in a symplectic vector space are uniformly Lipschitz.**
Under the hypotheses of
`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le`, there
is a common Lipschitz constant for all smooth Floer cylinders of period one with values in `K` and
Floer energy at most `E` over the strip `ℝ × [0, 1]`. -/
theorem exists_lipschitzWith_of_setLIntegral_floerEnergyDensity_le (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V} {K : Set V}
    (hH : ContDiff ℝ 2 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hK : IsCompact K) (htame : ∀ t, ∀ x ∈ K, ω.Tames (J t x)) (E : ℝ) :
    ∃ L, ∀ ⦃u : ℝ × ℝ → V⦄, ContDiff ℝ (⊤ : ℕ∞) u → (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in univ ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
        ENNReal.ofReal E →
      LipschitzWith L u := by
  obtain ⟨M, hM⟩ :=
    ω.exists_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le hH hHper hJ hK htame E
  refine ⟨M.toNNReal, fun u hu hper hfl huK hE ↦ ?_⟩
  refine lipschitzWith_of_nnNorm_fderiv_le (hu.differentiable (by simp)) fun z ↦ ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm]
  exact (hM hu hper hfl huK hE z).trans (Real.le_coe_toNNReal M)

end TauCeti.SymplecticForm
