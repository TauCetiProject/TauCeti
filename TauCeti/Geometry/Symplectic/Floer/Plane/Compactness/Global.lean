/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Compactness.Closed
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Geometry.Symplectic.Floer.Compactness.EndWindow
import TauCeti.Data.ENNReal.NatCastDiv
import TauCeti.Geometry.Symplectic.Floer.Tameness
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.MeasureTheory.Measure.BubblingSet
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of PSS planes on the whole plane in a closed manifold

Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed symplectic
manifold, and let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`
with end sign `ε`, given by a period-one `C³` Hamiltonian `H` with `|H| ≤ B`. Let `J(z, x)` be
structures on the tangent spaces of `M`, tamed by `ω` and `C²` read in the chart at every point of
`M`, which far out on the end are structures `J_∞(t, x)` in the end coordinates. The
Piunikhin–Salamon–Schwarz maps, and the unit cycle of the pair-of-pants product, count solutions
`u : ℂ → M` of `(du - X_K)^{0,1} = 0`.

Gromov–Floer compactness off finitely many bubbling points is known for these solutions on one
compact window of the plane at a time, and on the translates of one window of the end, with a
threshold that does not depend on the translation
(`TauCeti.Geometry.Symplectic.Floer.Plane.Compactness.Closed`). This file assembles them into the
statement on the whole plane,
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pssPlanePerturbation_univ` in
the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`: there is a threshold `δ > 0` such that every
sequence of solutions whose capped end actions `aₖ` satisfy `ε aₖ ≤ A` has a subsequence converging
off a finite set `Z` of the plane with `#Z * δ ≤ A + B`, every disc about a point of `Z` eventually
carrying energy at least `δ`. The solutions converge locally uniformly off `Z` after applying an
injective `C¹` map `e : M → F` into a normed space, such as the Whitney embedding, and pointwise in
`M`.

The plane is covered by countably many windows: the disc `‖w‖ < exp (2π (T + 2))`, where
`T = max T₀ 2` and the structures are cylindrical beyond `T₀`, and the images under
`y ↦ φ(y + (m, 0))`, for `m ∈ ℕ`, of the two windows `(T + 1, T + 3) × (-2/5, 2/5)` and
`(T + 1, T + 3) × (1/10, 9/10)` of the end coordinates, where `φ(s, t) = exp (2π (s + i t))` is the
end lift of the positive plane. Since `φ` is an open map, injective on bands of angular width one,
locally uniform convergence of the translated ends on a window is locally uniform convergence of the
solutions on its image, and the energy of a translated end over part of a window is the energy of
the solution over its image
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_add_eq`). On each
end window the threshold is that of one of two fixed windows, so the thresholds are bounded below,
and the diagonal argument of `TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion`
applies with the energy measures of the solutions.

The constants that the window theorems take are derived here. One constant `c > 0` with
`c ‖d e v‖² ≤ ω(v, J v)` serves the closed disc `‖w‖ ≤ exp (2π (T + 2))` and the end, since beyond
`T₀` the structures are those of the circle `t ↦ φ(T, t)`, which lies in that disc
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le`). The
pushforwards through `e` of the Hamiltonian vector fields of the perturbation are bounded on the
closed disc, by compactness, and those of the end Hamiltonian `ε H(ε t)` by compactness of `M` and
periodicity.

The window cover, the diagonal assembly and the derivation of the window constants follow the
whole-domain theorem for pairs of pants in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Global`, with the end charts of the pair
of pants replaced by the end lift of the positive plane.

Energy that escapes along the end is not seen by the limit: this is the breaking of Floer
cylinders off the end, which is not treated here, nor are the regularity of the limit and the
bubbles at the points of `Z`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points on a noncompact domain) and Chapter 12 (the PSS isomorphism).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.Complex (realChart contDiff_realChart)
open scoped Manifold Real

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer Floer.PSSPlane

/-! ### The windows of the plane -/

/-- The windows covering the plane: the disc `‖w‖ < exp (2π (T + 2))`, and the images of the end
windows under `y ↦ φ(y + (m, 0))`, for `m ∈ ℕ`, where `φ` is the end lift of the positive plane. -/
private noncomputable def window (T : ℝ) : Option (ℕ × Bool) → Set (ℝ × ℝ)
  | none => {z | ‖equivRealProdCLM.symm z‖ < Real.exp (2 * π * (T + 2))}
  | some (m, b) =>
    (fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0))) '' endWindow T b

/-- The translated end lift `y ↦ φ(y + (m, 0))` of the positive plane is an open map. -/
private theorem isOpenMap_realChart_positive_add (m : ℝ) :
    IsOpenMap fun y ↦ realChart positive.cylindricalEndLift (y + (m, 0)) :=
  positive.isOpenMap_realChart_cylindricalEndLift.comp
    (Homeomorph.addRight (m, (0 : ℝ))).isOpenMap

/-- A point of the plane with `‖w‖ ≥ exp (2π (T + 2))` lies in the image of an end window under
`y ↦ φ(y + (m, 0))` for some `m ∈ ℕ`. -/
private theorem exists_mem_image_realChart_positive_add {T : ℝ} {z : ℝ × ℝ}
    (hz : Real.exp (2 * π * (T + 2)) ≤ ‖equivRealProdCLM.symm z‖) :
    ∃ (m : ℕ) (b : Bool),
      z ∈ (fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0))) '' endWindow T b := by
  obtain ⟨⟨s, t⟩, hs, -, hz'⟩ := positive.exists_realChart_cylindricalEndLift_eq
    (T := T + 1) ((Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])).trans_le hz)
  rw [endSign_positive, one_mul] at hs
  -- Translate `(s, t)` into an end window, using that `φ` has period one in `t`.
  obtain ⟨m, k, b, hy⟩ := exists_sub_mem_endWindow hs t
  have hper : Periodic (fun t ↦ realChart positive.cylindricalEndLift (s, t)) 1 :=
    realChart_positive_add_one s
  exact ⟨m, b, (s - m, t - k), hy, by simpa [hz'] using hper.sub_int_mul_eq k (x := t)⟩

/-- The windows are open, since the end lift is an open map. -/
private theorem isOpen_window (T : ℝ) (i : Option (ℕ × Bool)) : IsOpen (window T i) := by
  rcases i with _ | ⟨m, b⟩
  · exact isOpen_lt (continuous_norm.comp equivRealProdCLM.symm.continuous) continuous_const
  · exact isOpenMap_realChart_positive_add m _ (isOpen_endWindow T b)

/-- The disc window lies in the closed disc `‖w‖ ≤ exp (2π (T + 2))`. -/
private theorem window_none_subset (T : ℝ) :
    window T none ⊆ {z | ‖equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (T + 2))} := by
  rw [window]
  exact ofPred_subset_ofPred.2 fun _ ↦ le_of_lt

/-- The windows cover the plane. -/
private theorem iUnion_window (T : ℝ) : ⋃ i, window T i = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  by_cases hz : ‖equivRealProdCLM.symm z‖ < Real.exp (2 * π * (T + 2))
  · exact mem_iUnion.2 ⟨none, hz⟩
  · obtain ⟨m, b, hzm⟩ := exists_mem_image_realChart_positive_add (not_lt.1 hz)
    exact mem_iUnion.2 ⟨some (m, b), hzm⟩

/-- **Convergence on a window of the end, read on the plane.** Let `g(y) = φ(y + (m, 0))` be the
translated end lift of the positive plane, and let `Ω` be an open window whose translate by
`(m, 0)` lies in a band of angular width one. If the readings `fₙ ∘ g` converge locally uniformly on
`Ω \ Z`, then the `fₙ` converge locally uniformly on `g(Ω) \ g(Z)`. -/
private theorem exists_tendstoLocallyUniformlyOn_image_realChart_positive_add {α : Type*}
    [UniformSpace α] {m : ℕ} {T t₀ : ℝ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : ∀ z ∈ Ω, z + ((m : ℝ), 0) ∈ Ioi T ×ˢ Ioo t₀ (t₀ + 1)) {Z : Finset (ℝ × ℝ)}
    (hZ : ↑Z ⊆ Ω) {f : ℕ → ℝ × ℝ → α} {v : ℝ × ℝ → α}
    (hv : TendstoLocallyUniformlyOn
      (fun n z ↦ f n (realChart positive.cylindricalEndLift (z + ((m : ℝ), 0)))) v atTop
      (Ω \ ↑Z)) :
    ∃ v' : ℝ × ℝ → α, TendstoLocallyUniformlyOn f v' atTop
      ((fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0))) '' Ω \
        (fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0))) '' ↑Z) := by
  have hinj : InjOn (fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0))) Ω :=
    fun a ha b hb hab ↦ add_right_cancel (positive.injOn_realChart_cylindricalEndLift t₀
      ⟨mem_univ _, Ioo_subset_Ico_self (hΩT a ha).2⟩
      ⟨mem_univ _, Ioo_subset_Ico_self (hΩT b hb).2⟩ hab)
  rw [← hinj.image_sdiff_subset hZ]
  exact ⟨_, hv.image_of_isOpenMap (hΩ.sdiff Z.finite_toSet.isClosed)
    (isOpenMap_realChart_positive_add m) (hinj.mono sdiff_subset)⟩

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {e : M → F}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- **Energy concentration on a window of the end, read on the plane.** Let `g(y) = φ(y + (m, 0))`
be the translated end lift of the positive plane, and let `Ω` be an open window whose translate by
`(m, 0)` lies beyond `T ≥ 2` in a band of angular width one. If the energy `δ` of the translated
ends `uₖ ∘ g`, for the cylindrical datum `ε H(ε t) dt`, concentrates in every disc about a point of
`Z ⊆ Ω`, then every neighbourhood of a point of `g(Z)` eventually carries energy at least `δ` for
the energy measure of `uₖ` on the plane. -/
private theorem eventually_ofReal_le_withDensity_image_realChart_positive_add (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, MDifferentiable 𝓘(ℝ, ℝ × ℝ) I (u k)) {m : ℕ} {T t₀ : ℝ}
    (hT : 2 ≤ T) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : ∀ z ∈ Ω, z + ((m : ℝ), 0) ∈ Ioi T ×ˢ Ioo t₀ (t₀ + 1)) {δ : ℝ} {φ : ℕ → ℕ}
    {Z : Finset (ℝ × ℝ)}
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x)
      (fun z ↦ u (φ n) (realChart positive.cylindricalEndLift (z + ((m : ℝ), 0)))) y) :
    ∀ z ∈ (fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0))) '' ↑Z, ∀ N ∈ 𝓝 z,
      ∀ᶠ n in atTop, ENNReal.ofReal δ ≤ (volume.restrict univ).withDensity
        (fun y ↦ ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y)) N := by
  have hg : Continuous fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0)) :=
    (contDiff_realChart positive.contDiff_cylindricalEndLift (n := 0)).continuous.comp
      (continuous_id.add continuous_const)
  rintro _ ⟨z, hz, rfl⟩ N hN
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 (hg.continuousAt.preimage_mem_nhds hN)
  filter_upwards [hconc z hz ε hε] with n hn
  -- The image of the disc is open, so measurable, and lies in `N`.
  refine TauCeti.MeasureTheory.le_withDensity_of_le_setLIntegral
    (s := (fun y ↦ realChart positive.cylindricalEndLift (y + ((m : ℝ), 0))) '' (ball z ε ∩ Ω))
    ((isOpenMap_realChart_positive_add m _ (isOpen_ball.inter hΩ)).measurableSet) (subset_univ _)
    (image_subset_iff.2 (inter_subset_left.trans hεN)) ?_
  -- Its energy is that of the translated end over the disc.
  rw [perturbation_eq_positive p H, ← setLIntegral_floerEnergyDensity_comp_realChart_positive_add_eq
    ω (p.periodic_endSign_mul hH) (contMDiff_uncurry_const_mul_comp_const_mul p.endSign hHs) hT
    (hu _).mdifferentiableOn _ (measurableSet_ball.inter hΩ.measurableSet)
    fun y hy ↦ ⟨(hΩT y hy.2).1, Ioo_subset_Ico_self (hΩT y hy.2).2⟩]
  exact (ENNReal.ofReal_le_ofReal hn).trans
    TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal

/-! ### The constants and thresholds of the windows -/

omit [I.Boundaryless] [CompactSpace M] in
/-- The energy of a PSS plane whose limiting capped end action `a` satisfies `ε a ≤ A` is at most
`A + B`, which is nonnegative. -/
private theorem nonneg_and_lintegral_floerEnergyDensity_le (hω : ω.IsNondegenerate)
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    {B : ℝ} (hB : ∀ t x, |H t x| ≤ B) (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x))
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    {a A : ℝ} (ha : Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u (equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
        (𝓝 a))
    (hA : p.endSign * a ≤ A) :
    0 ≤ A + B ∧ ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) u z) ≤
        ENNReal.ofReal (A + B) := by
  have h := hω.neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation hH hHs hB hu
    (fun z ↦ hJt z _) hfl ha
  exact ⟨by linarith, (hω.lintegral_floerEnergyDensity_pssPlanePerturbation_le hH hHs hB hu
    (fun z ↦ hJt z _) hfl ha).trans (ENNReal.ofReal_le_ofReal (by linarith))⟩

omit [I.Boundaryless] in
/-- **The data of the windows.** Under the hypotheses of the main theorem below, with
`T = max T₀ 2`, there are constants `c > 0` and `L` such that on the closed disc
`‖w‖ ≤ exp (2π (T + 2))` the structures are uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J v)`, and the pushforwards through `e` of the Hamiltonian vector fields of the
two components of the perturbation are at most `L`, and such that on the end the structures `J_∞`
are `C²` in the charts of `M`, tame, and uniformly tame with the same constant `c`, and the
pushforwards of the Hamiltonian vector fields of the end Hamiltonian `ε H(ε t)` are bounded. -/
private theorem exists_pos_window_data (hω : ω.IsNondegenerate) (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J) (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x)) {T₀ : ℝ}
    {Jend : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    ∃ c > 0, ∃ L,
      (∀ z ∈ {z : ℝ × ℝ | ‖equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (max T₀ 2 + 2))},
        ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v)) ∧
      (∀ z ∈ {z : ℝ × ℝ | ‖equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (max T₀ 2 + 2))},
        ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ p.perturbation H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L ∧
        ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ p.perturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) ∧
      (∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α Jend)
        (univ ×ˢ (extChartAt I α).target)) ∧
      (∀ t x, (hω.symplecticFormAt x).Tames (Jend t x)) ∧
      (∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jend t x v)) ∧
      ∃ L', ∀ t x, ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ p.endSign * H (p.endSign * t) y) x)‖ ≤ L' := by
  set T := max T₀ 2
  set D := {z : ℝ × ℝ | ‖equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (T + 2))}
  have hD : IsCompact D := isCompact_setOf_norm_equivRealProdCLM_symm_le _
  -- Beyond `T₀` the structures are those of the circle `φ(T, t)`, which lies in the disc `D`.
  have hmem (t : ℝ) : realChart positive.cylindricalEndLift (T, t) ∈ D := by
    simp only [D, mem_ofPred_eq, positive.norm_symm_realChart_cylindricalEndLift, endSign_positive,
      one_mul, Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have hJend : Jend = fun t ↦ J (realChart positive.cylindricalEndLift (T, t)) :=
    funext fun t ↦ funext fun x ↦ (hJe T t x (le_max_left _ _)).symm
  have hJends (α : M) : ContDiffOn ℝ 2 (almostComplexInChartAt I α Jend)
      (univ ×ˢ (extChartAt I α).target) := by
    rw [hJend, funext (almostComplexInChartAt_comp (I := I) (α := α) (J := J)
      fun t ↦ realChart positive.cylindricalEndLift (T, t))]
    refine (hJ α).comp (s := univ ×ˢ (extChartAt I α).target)
      (f := fun q : ℝ × E ↦ (realChart positive.cylindricalEndLift (T, q.1), q.2)) ?_
      fun q hq ↦ ⟨mem_univ _, hq.2⟩
    exact (((contDiff_realChart positive.contDiff_cylindricalEndLift).comp
      (contDiff_const.prodMk contDiff_fst)).prodMk contDiff_snd).contDiffOn
  -- One tameness constant serves the disc `D`, and with it the end.
  obtain ⟨c, hc, hJc⟩ := hω.exists_pos_forall_mul_norm_mvfderiv_sq_le hD isCompact_univ
    (fun α _ ↦ (hJ α).continuousOn.mono (prod_mono (subset_univ _) subset_rfl))
    (fun z _ x _ ↦ hJt z x) he
  -- The pushforwards of the Hamiltonian vector fields of the components are continuous jointly
  -- in the point of the plane and the target point, so bounded on `D × M`.
  have hcont (w : ℂ) : Continuous fun q : (ℝ × ℝ) × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField
      (fun y ↦ p.perturbation H (equivRealProdCLM.symm q.1) y w) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using contMDiff_uncurry_perturbation (p := p) hH hHs w)).continuous
  obtain ⟨Ls, hLs⟩ := (hD.prod isCompact_univ).exists_bound_of_continuousOn (hcont 1).continuousOn
  obtain ⟨Lt, hLt⟩ :=
    (hD.prod isCompact_univ).exists_bound_of_continuousOn (hcont Complex.I).continuousOn
  refine ⟨c, hc, max Ls Lt, fun z hz x ↦ hJc z hz x (mem_univ x), fun z hz x ↦
    ⟨(hLs (z, x) ⟨hz, mem_univ x⟩).trans (le_max_left _ _),
      (hLt (z, x) ⟨hz, mem_univ x⟩).trans (le_max_right _ _)⟩, hJends,
    fun t x ↦ by rw [hJend]; exact hJt _ x, fun t x v ↦ by
      rw [hJend]; exact hJc _ (hmem t) x (mem_univ x) v, ?_⟩
  exact hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le
    (contMDiff_uncurry_const_mul_comp_const_mul p.endSign hHs) (p.periodic_endSign_mul hH) he

/-- **The windows of the plane, with one threshold.** Under the hypotheses of the main theorem
below, there is a threshold `δ > 0` such that on every window, every subsequence of a sequence of
solutions has a further subsequence along which the solutions read through `e` converge off a set
at each point of which the energy measure of every neighbourhood is eventually at least `δ`. -/
private theorem exists_pos_forall_window (hω : ω.IsNondegenerate) (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J) (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x)) {T₀ : ℝ}
    {Jend : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃a : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k)
          z).toLinearMap) →
      (∀ k, Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u k (equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u k ∘ p.endDisc R)) atTop
          (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) →
      ∀ i ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set (ℝ × ℝ),
        (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, ENNReal.ofReal δ ≤
          (volume.restrict univ).withDensity (fun y ↦ ENNReal.ofReal (ω.floerEnergyDensity
            (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u (ψ (φ n))) y)) N) ∧
        ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (ψ (φ n))) v atTop
          (window (max T₀ 2) i \ Z) := by
  set T := max T₀ 2
  have hT : 2 ≤ T := le_max_right _ _
  have hHs₁ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H) := hHs.of_le (by norm_num)
  have hed : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x := he.mdifferentiable one_ne_zero
  obtain ⟨c, hc, L, hJc, hL, hJend, hJendt, hJendc, L', hL'⟩ :=
    exists_pos_window_data hω p hH hHs₁ hJ hJt hJe he
  -- The thresholds of the two windows of the end, uniform in the translation, and of the disc.
  choose δe hδe hconve using fun b : Bool ↦
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_realChart_positive_add
      hω p hH hHs (T₀ := T) (fun s t x hs ↦ hJe s t x ((le_max_left _ _).trans hs)) hJend hJendt hed
      he_inj hc hJendc hL'
      (D := Icc (T + 1) (T + 3) ×ˢ Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5)
        ((bif b then 1 / 2 else 0) + 2 / 5)) (isCompact_Icc.prod isCompact_Icc)
      (t₀ := (bif b then 1 / 2 else 0) - 1 / 2)
      (endWindow_closed_subset_Ioi_prod_Ioo (max_le le_rfl hT) b)
  obtain ⟨δc, hδc, hconvc⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pssPlanePerturbation
      p hH hHs hB isOpen_univ (isCompact_setOf_norm_equivRealProdCLM_symm_le _) (subset_univ _)
      hJ hJt hed he_inj hc hJc
      (fun z hz x ↦ (hL z hz x).1) fun z hz x ↦ (hL z hz x).2
  refine ⟨min δc (min (δe false) (δe true)), lt_min hδc (lt_min (hδe false) (hδe true)),
    fun u a A hu hfl ha hA i ψ _ ↦ ?_⟩
  rcases i with _ | ⟨m, b⟩
  · obtain ⟨φ, hφ, Z, -, -, hcz, -, v, -, hv, -⟩ := hconvc (u := u ∘ ψ) (a := a ∘ ψ)
      (isOpen_window T none) (window_none_subset T) (fun k ↦ hu _) (fun k ↦ hfl _)
      (fun k ↦ ha _) (fun k ↦ hA _)
    exact ⟨φ, hφ, ↑Z, fun z hz ↦
      eventually_ofReal_le_withDensity_of_forall_eventually_le_setIntegral_ball
        (isOpen_window T none).measurableSet (subset_univ _)
        fun ε hε ↦ (hcz z hz ε hε).mono fun n hn ↦ (min_le_left _ _).trans hn, e ∘ v, hv⟩
  · have hEb (k : ℕ) := nonneg_and_lintegral_floerEnergyDensity_le hω p hH hHs₁ hB hJt
      ((hu k).of_le (by norm_num)) (hfl k) (ha k) (hA k)
    have hΩT (y : ℝ × ℝ) (hy : y ∈ endWindow T b) :=
      endWindow_add_mem_Ioi_prod_Ioo le_rfl (Nat.cast_nonneg m) hy
    have hδb : min δc (min (δe false) (δe true)) ≤ δe b :=
      (min_le_right _ _).trans (by cases b; exacts [min_le_left _ _, min_le_right _ _])
    obtain ⟨φ, hφ, Z, hZΩ, -, hcz, -, v, -, hv, -⟩ := hconve b (Ω := endWindow T b)
      (u := u ∘ ψ) (R := fun _ ↦ (m : ℝ)) (isOpen_endWindow T b)
      (endWindow_subset_Icc_prod_Icc T b) (fun _ ↦ Nat.cast_nonneg m)
      (fun k ↦ hu _) (fun k ↦ hfl _) (hEb 0).1 fun k ↦ (hEb _).2
    exact ⟨φ, hφ, _, eventually_ofReal_le_withDensity_image_realChart_positive_add p hH hHs₁
      (fun k ↦ (hu (ψ k)).mdifferentiable (by norm_num)) hT (isOpen_endWindow T b) hΩT
      (fun z hz ε hε ↦ (hcz z hz ε hε).mono fun n hn ↦ hδb.trans hn),
      exists_tendstoLocallyUniformlyOn_image_realChart_positive_add (isOpen_endWindow T b)
        hΩT hZΩ (f := fun n ↦ e ∘ u (ψ (φ n))) hv⟩

/-! ### The whole plane -/

/-- **PSS planes in a closed manifold converge off finitely many bubbling points on the whole
plane.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed symplectic
manifold, let `K` be the perturbation of a PSS plane `p` with end sign `ε` given by a period-one
`C³` Hamiltonian `H` with `|H| ≤ B`, and let `J(z, x)` be structures on the tangent spaces of `M`,
tamed by `ω` and `C²` read in the chart at every point of `M`, which far out on the end are
structures `J_∞(t, x)` in the end coordinates: `J(φ(s, t), x) = J_∞(t, x)` for `s ≥ T₀`, where `φ`
is the end lift of the positive plane in real coordinates. Let `e : M → F` be an injective `C¹` map
into a normed space, such as the Whitney embedding. There is a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` solutions of `(du - X_K)^{0,1} = 0` on the plane for `J(z, u)`, whose
end loops along the circles `‖w‖ = exp (2πR)`, each capped by the disc `uₖ ∘ endDisc R` of the
plane that it bounds, have capped actions converging to `aₖ` as `R → ∞`, with `ε aₖ ≤ A`. Then
there are a subsequence `φ`, a finite set `Z` of the plane with `#Z * δ ≤ A + B` and a map `v`,
continuous off `Z`, such that along `φ` every disc about a point of `Z` eventually carries energy at
least `δ`, and the solutions converge to `v` off `Z`, locally uniformly after applying `e` and
pointwise in `M`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pssPlanePerturbation_univ
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J) (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x)) {T₀ : ℝ}
    {Jend : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃a : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k)
          z).toLinearMap) →
      (∀ k, Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u k (equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u k ∘ p.endDisc R)) atTop
          (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono φ ∧
        Z.card * δ ≤ A + B ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y) ∧
        ContinuousOn v (↑Z)ᶜ ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (↑Z)ᶜ ∧
        ∀ z ∈ (↑Z : Set (ℝ × ℝ))ᶜ, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  obtain ⟨δ, hδ, hwin⟩ := exists_pos_forall_window hω p hH hHs hB hJ hJt hJe he he_inj
  refine ⟨δ, hδ, fun u a A hu hfl ha hA ↦ ?_⟩
  have hHs₁ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H) := hHs.of_le (by norm_num)
  have hEb (k : ℕ) := nonneg_and_lintegral_floerEnergyDensity_le hω p hH hHs₁ hB hJt
    ((hu k).of_le (by norm_num)) (hfl k) (ha k) (hA k)
  -- Assemble the windows by the diagonal argument, for the energy measures of the `uₖ`.
  obtain ⟨φ, Z, g, hφ, -, hcard, hconc, hconv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion (isOpen_window (max T₀ 2))
      (F := fun k ↦ e ∘ u k) (μ := fun k ↦ (volume.restrict univ).withDensity fun y ↦
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k) y))
      (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top
      (fun k ↦ (measure_mono (subset_univ _)).trans (by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Measure.restrict_univ]
        exact (hEb k).2))
      (hwin hu hfl ha hA)
  rw [iUnion_window, ← compl_eq_univ_sdiff] at hconv
  -- The limit is continuous, and it is read back in `M` through the embedding `e`.
  have hg : ContinuousOn g (↑Z)ᶜ := hconv.continuousOn (Eventually.of_forall fun n ↦
    (he.continuous.comp (hu (φ n)).continuous).continuousOn).frequently
  obtain ⟨v, hv, -, hev, hpt⟩ := isCompact_univ.exists_tendsto_of_tendsto_comp
    he.continuous.continuousOn he_inj.injOn (fun _ _ ↦ .of_forall fun _ ↦ mem_univ _) hg
    fun z hz ↦ hconv.tendsto_at hz
  refine ⟨φ, Z, v, hφ, (ENNReal.natCast_mul_ofReal_le_ofReal_iff (hEb 0).1).1 hcard,
    fun z hz ε hε ↦ ?_, hv, hconv.congr_right hev.symm, hpt⟩
  -- The energy measure of a disc is the energy over the disc.
  have hX (w : ℂ) : ContinuousOn (fun q : (ℝ × ℝ) × M ↦ (⟨q.2, ω.hamiltonianVectorField
      (fun y ↦ p.perturbation H (equivRealProdCLM.symm q.1) y w) q.2⟩ : TangentBundle I M))
      (univ ×ˢ univ) :=
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
      ((contMDiff_uncurry_perturbation (p := p) hH hHs w).of_le (by norm_num))).continuous
        |>.continuousOn
  filter_upwards [hconc z hz _ (ball_mem_nhds z hε)] with n hn
  have h0 (y : ℝ × ℝ) := floerEnergyDensity_nonneg hω (hJt y _) (hfl (φ n) y)
  have hint := (ω.integrableOn_and_setIntegral_floerEnergyDensity_le isOpen_univ
    ((measurableSet_ball (x := z) (ε := ε)).inter MeasurableSet.univ) (subset_univ _)
    ((hu (φ n)).of_le (by norm_num)).contMDiffOn (hX 1) (hX Complex.I) (fun y _ ↦ h0 y) (hEb 0).1
    ((setLIntegral_univ _).trans_le (hEb _).2)).1
  simpa only [inter_univ] using TauCeti.MeasureTheory.le_setIntegral_of_ofReal_le_withDensity
    measurableSet_ball MeasurableSet.univ hint (fun y _ ↦ h0 y) hn

end TauCeti.SmoothTwoForm.IsNondegenerate
