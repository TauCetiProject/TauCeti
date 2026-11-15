/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Analysis.Calculus.MeanValue.Trapping
import TauCeti.Analysis.Hofer
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The mean-value inequality for Floer solutions in a manifold

Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` for a perturbation `K = K_s ds + K_t dt`
and almost complex structures `J(z, u)` tamed by the symplectic form, and let
`e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` be its energy density. The *mean-value inequality* bounds `e`
at the centre of a small square `B_r(z₀)` of the domain by its integral: if `r² + ∫_{B_r(z₀)} e`
is below a threshold `δ`, then

`r² e(z₀) ≤ B (r² + ∫_{B_r(z₀)} e)`.

The additive `r²` accounts for the Hamiltonian term. Squares of side `2 r` are the balls of the sup
norm of `ℝ × ℝ`, the domain of Floer solutions in Tau Ceti.

* For a symplectic vector space target the inequality holds with `δ` and `B` uniform over a compact
  window of the domain and a compact set of the target
  (`TauCeti.SymplecticForm.exists_pos_forall_sq_mul_floerEnergyDensity_le`). It is the mean-value
  inequality for the coordinate equation,
  `TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy`, on the
  disc inscribed in the square
  (`TauCeti.SymplecticForm.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_stdComplexLineReal_sq_le`),
  combined with the comparison of `e` with `‖du‖²` on compact sets
  (`TauCeti.SymplecticForm.exists_forall_norm_fderiv_sq_le_and_floerEnergyDensity_le`).
* Read in a symplectic chart `φ` of a manifold `M`, the same holds for solutions whose image lies
  in a compact subset `C` of the chart
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le`), and
  the derivative of the chart reading `φ ∘ u` is bounded by `e`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_comp_sq_le`).
* For finitely many such charts and compact sets `A i` in the interiors of the `C i`, the
  inequality holds for every solution with image in `⋃ A i`, whether or not the image of the square
  lies in a single chart
  (`SmoothTwoForm.IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mapsTo_iUnion`).
  On a closed symplectic manifold, finitely many Darboux charts give such sets with `⋃ A i = M`.

The last statement is the a priori estimate that places the images of small-energy squares in
single charts, which a chart-by-chart compactness argument for Floer solutions in a closed manifold
needs. Its proof is the standard one: Hofer's lemma for `e`
(`TauCeti.hofer_sq_of_continuousOn_closedBall`) finds a point `x'` near `z₀` and a radius on which
`e ≤ 4 e(x')`. The derivative of the chart reading at `x'` is then bounded in terms of `e(x')`, so a
square about `x'` of radius comparable to `e(x')^(-1/2)` stays in the chart of `u x'`
(`PartialDiffeomorph.mapsTo_ball_of_norm_fderiv_comp_le`), and the inequality in that chart either
bounds `e(x')` directly or shows that `e(x')` is bounded by a constant.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Lemma 4.3.1
  and Section 4.3 (the mean-value inequality), Section 4.6 (Hofer's lemma) and Section 8.1 (the
  inhomogeneous equation).
-/

public section

open Complex ContinuousLinearMap Filter Function MeasureTheory Metric Real Set Topology
open scoped Manifold

/-- A continuous linear map out of `ℝ × ℝ`, with its sup norm, has operator norm at most the sum of
the norms of its values on the two coordinate vectors. -/
theorem ContinuousLinearMap.opNorm_le_norm_apply_stdComplexLineReal_add {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (L : ℝ × ℝ →L[ℝ] E) :
    ‖L‖ ≤ ‖L TauCeti.stdComplexLineReal‖ + ‖L TauCeti.stdComplexLineImag‖ := by
  refine L.opNorm_le_bound (by positivity) fun v ↦ ?_
  have hv : L v = v.1 • L TauCeti.stdComplexLineReal + v.2 • L TauCeti.stdComplexLineImag := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp [TauCeti.stdComplexLineReal, TauCeti.stdComplexLineImag]
  rw [hv, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, mul_comm]
  · exact mul_le_mul_of_nonneg_left (_root_.norm_fst_le v) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_left (_root_.norm_snd_le v) (norm_nonneg _)

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {z : ℝ × ℝ}

/-- On an open set `W ⊆ (ℝ × ℝ) × V`, the Hamiltonian one-form of a perturbation
`K = K_s ds + K_t dt` with `C³` coefficients is `C²`. -/
theorem contDiffOn_hamiltonianOneForm_uncurry (ω : SymplecticForm V) {W : Set ((ℝ × ℝ) × V)}
    (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (uncurry Ks) W) (hKt : ContDiffOn ℝ 3 (uncurry Kt) W) :
    ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × V ↦ ω.hamiltonianOneForm Ks Kt q.1 q.2) W :=
  (ω.contDiffOn_hamiltonianOneForm (P := ℝ) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt) (n := 2)
    (isOpen_univ.prod hW) (hKs.comp contDiffOn_snd fun _ hq ↦ hq.2)
    (hKt.comp contDiffOn_snd fun _ hq ↦ hq.2)).comp
    (contDiffOn_const (c := (0 : ℝ)).prodMk contDiffOn_id) fun _ hq ↦ ⟨mem_univ _, hq⟩

/-- For a map `u` that is `C¹` on an open set `U` of the domain, and a Hamiltonian one-form
continuous on a set `W` containing the graph of `u` over `U`, the Floer energy density of `u` is
continuous on `U`. -/
theorem continuousOn_floerEnergyDensity_of_continuousOn_hamiltonianOneForm
    (ω : SymplecticForm V) {U : Set (ℝ × ℝ)} {W : Set ((ℝ × ℝ) × V)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U)
    (hX : ContinuousOn (fun q : (ℝ × ℝ) × V ↦ ω.hamiltonianOneForm Ks Kt q.1 q.2) W)
    (hUW : ∀ z ∈ U, (z, u z) ∈ W) :
    ContinuousOn (ω.floerEnergyDensity Ks Kt u) U := by
  have hP : ContinuousOn (fun z ↦ ω.perturbedFDeriv Ks Kt u z) U := by
    simp_rw [perturbedFDeriv_eq_sub]
    exact (hu.continuousOn_fderiv_of_isOpen hU le_rfl).sub
      (hX.comp (continuousOn_id.prodMk hu.continuousOn) hUW)
  exact (ω.continuousOn_apply_comp (hP.clm_apply (continuousOn_const (c := stdComplexLineReal)))
    (hP.clm_apply (continuousOn_const (c := stdComplexLineImag)))).congr fun z _ ↦
      floerEnergyDensity_def ω Ks Kt u z

/-- **The energy density bounds the whole derivative.** Let `u` solve the Floer equation at `z`
for an almost complex structure `J` with `a ‖v‖² ≤ ω(v, J v)` and `‖J v‖ ≤ M ‖v‖`, where `0 < a`,
and let the Hamiltonian one-form `X_K` at `(z, u z)` have norm at most `N`. Then
`‖du(z)‖² ≤ 4 (1 + M²) / a · ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t}) + 2 N²`. -/
theorem norm_fderiv_sq_le_of_isComplexLinearMap (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} {a M N : ℝ} (ha : 0 < a)
    (hJa : ∀ v, a * ‖v‖ ^ 2 ≤ ω v (J v)) (hJM : ∀ v, ‖J v‖ ≤ M * ‖v‖)
    (hN : ‖ω.hamiltonianOneForm Ks Kt z (u z)‖ ≤ N)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ‖fderiv ℝ u z‖ ^ 2 ≤
      4 * (1 + M ^ 2) / a * ω.floerEnergyDensity Ks Kt u z + 2 * N ^ 2 := by
  set P := ω.perturbedFDeriv Ks Kt u z with hPdef
  have hcomp := ω.mul_norm_sq_add_norm_sq_perturbedFDeriv_le_mul_floerEnergyDensity ha.le hJa hJM h
  have hP : ‖P‖ ≤ ‖P stdComplexLineReal‖ + ‖P stdComplexLineImag‖ :=
    P.opNorm_le_norm_apply_stdComplexLineReal_add
  have hd : ‖fderiv ℝ u z‖ ≤ ‖P‖ + N := by
    have : fderiv ℝ u z = P + ω.hamiltonianOneForm Ks Kt z (u z) := by
      rw [hPdef, ω.perturbedFDeriv_eq_sub, sub_add_cancel]
    rw [this]
    exact (norm_add_le _ _).trans (by gcongr)
  have hP2 : ‖P‖ ^ 2 ≤ 2 * (1 + M ^ 2) / a * ω.floerEnergyDensity Ks Kt u z := by
    rw [← hPdef] at hcomp
    have hsq : ‖P‖ ^ 2 ≤ 2 * (‖P stdComplexLineReal‖ ^ 2 + ‖P stdComplexLineImag‖ ^ 2) := by
      nlinarith [norm_nonneg P, norm_nonneg (P stdComplexLineReal),
        norm_nonneg (P stdComplexLineImag), sq_nonneg (‖P stdComplexLineReal‖ -
          ‖P stdComplexLineImag‖)]
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]
  have h0 : 0 ≤ ‖P‖ + N := (norm_nonneg _).trans hd
  have : ‖fderiv ℝ u z‖ ^ 2 ≤ 2 * ‖P‖ ^ 2 + 2 * N ^ 2 := by
    nlinarith [norm_nonneg (fderiv ℝ u z), norm_nonneg P, sq_nonneg (‖P‖ - N)]
  calc ‖fderiv ℝ u z‖ ^ 2 ≤ 2 * ‖P‖ ^ 2 + 2 * N ^ 2 := this
    _ ≤ 2 * (2 * (1 + M ^ 2) / a * ω.floerEnergyDensity Ks Kt u z) + 2 * N ^ 2 := by gcongr
    _ = _ := by ring

/-- For a solution of the Floer equation at `z` for `J` with `ω(v, J v) ≤ b ‖v‖²`, and a
Hamiltonian one-form of norm at most `N` at `(z, u z)`, the energy density is at most
`2 b (‖∂ₛu(z)‖² + N²)`. -/
theorem floerEnergyDensity_le_of_isComplexLinearMap (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} {b N : ℝ} (hb : 0 ≤ b) (hJb : ∀ v, ω v (J v) ≤ b * ‖v‖ ^ 2)
    (hN : ‖ω.hamiltonianOneForm Ks Kt z (u z)‖ ≤ N)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerEnergyDensity Ks Kt u z ≤
      2 * b * (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 + N ^ 2) := by
  rw [ω.floerEnergyDensity_eq_of_isComplexLinearMap h, perturbedFDeriv_apply_stdComplexLineReal]
  set d := fderiv ℝ u z stdComplexLineReal
  set X := ω.hamiltonianVectorField (Ks z) (u z)
  -- `X_{K_s}` is the value of the one-form `X_K` on the unit vector `(1, 0)`.
  have hX : ‖X‖ ≤ N := by
    have h1 : ω.hamiltonianOneForm Ks Kt z (u z) stdComplexLineReal = X := by
      simp [hamiltonianOneForm_apply, X]
    rw [← h1]
    refine ((ω.hamiltonianOneForm Ks Kt z (u z)).le_opNorm _).trans ?_
    simpa [stdComplexLineReal_eq, Prod.norm_def] using hN
  have h0 : 0 ≤ N := (norm_nonneg _).trans hN
  have hdX : ‖d - X‖ ^ 2 ≤ 2 * (‖d‖ ^ 2 + N ^ 2) := by
    have := norm_sub_le d X
    nlinarith [norm_nonneg (d - X), norm_nonneg d, norm_nonneg X, sq_nonneg (‖d‖ - ‖X‖)]
  calc ω (d - X) (J (d - X)) ≤ b * ‖d - X‖ ^ 2 := hJb _
    _ ≤ b * (2 * (‖d‖ ^ 2 + N ^ 2)) := by gcongr
    _ = _ := by ring

/-- **The energy density and the derivative are comparable over a compact window.** Let `J(z, x)`
be continuous and tamed by `ω`, and the Hamiltonian one-form `X_K(z, x)` continuous, for
`(z, x)` in `D × K` with `D ⊆ ℝ × ℝ` and `K ⊆ V` compact. There is a constant `L ≥ 0` such that
every solution `u` of the Floer equation for `J(z, u)` at a point `z ∈ D` with `u z ∈ K` satisfies
`‖du(z)‖² ≤ L (e + 1)` and `e ≤ L (‖∂ₛu(z)‖² + 1)`, where
`e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` is its energy density at `z`. -/
theorem exists_forall_norm_fderiv_sq_le_and_floerEnergyDensity_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {D : Set (ℝ × ℝ)} {K : Set V}
    (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ContinuousOn (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (D ×ˢ K))
    (hX : ContinuousOn (fun p : (ℝ × ℝ) × V ↦ ω.hamiltonianOneForm Ks Kt p.1 p.2) (D ×ˢ K))
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ L ≥ 0, ∀ ⦃u : ℝ × ℝ → V⦄ ⦃z : ℝ × ℝ⦄, z ∈ D → u z ∈ K →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) →
      ‖fderiv ℝ u z‖ ^ 2 ≤ L * (ω.floerEnergyDensity Ks Kt u z + 1) ∧
        ω.floerEnergyDensity Ks Kt u z ≤ L * (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 + 1) := by
  have hDK : IsCompact (D ×ˢ K) := hD.prod hK
  obtain ⟨a, ha, b, hb, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    (J := fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) hDK hJ fun p hp ↦ hJt _ hp.1 _ hp.2
  obtain ⟨M, hM⟩ := hDK.exists_bound_of_continuousOn hJ
  obtain ⟨N, hN⟩ := hDK.exists_bound_of_continuousOn hX
  set M' := max M 0
  set N' := max N 0
  refine ⟨4 * (1 + M' ^ 2) / a + 2 * N' ^ 2 + 2 * b * (1 + N' ^ 2), by positivity,
    fun u z hz hu h ↦ ?_⟩
  have hp : (z, u z) ∈ D ×ˢ K := ⟨hz, hu⟩
  have hJM : ∀ v, ‖J z (u z) v‖ ≤ M' * ‖v‖ := fun v ↦
    ((J z (u z)).toLinearMap.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((hM _ hp).trans (le_max_left _ _)) (norm_nonneg _))
  have hNz : ‖ω.hamiltonianOneForm Ks Kt z (u z)‖ ≤ N' := (hN _ hp).trans (le_max_left _ _)
  have he0 : 0 ≤ ω.floerEnergyDensity Ks Kt u z := ω.floerEnergyDensity_nonneg (hJt z hz _ hu) h
  have h₁ := ω.norm_fderiv_sq_le_of_isComplexLinearMap ha (fun v ↦ (hab _ hp v).1) hJM hNz h
  have h₂ := ω.floerEnergyDensity_le_of_isComplexLinearMap hb (fun v ↦ (hab _ hp v).2) hNz h
  have hc : 0 ≤ 4 * (1 + M' ^ 2) / a := by positivity
  constructor
  · nlinarith [sq_nonneg N', mul_nonneg hb (sq_nonneg N')]
  · set d := ‖fderiv ℝ u z stdComplexLineReal‖
    have hd0 : 0 ≤ d ^ 2 := sq_nonneg d
    calc ω.floerEnergyDensity Ks Kt u z ≤ 2 * b * (d ^ 2 + N' ^ 2) := h₂
      _ ≤ 2 * b * (1 + N' ^ 2) * (d ^ 2 + 1) := by
        nlinarith [mul_nonneg (mul_nonneg hb (sq_nonneg N')) hd0]
      _ ≤ _ := by gcongr; nlinarith [sq_nonneg N']

/-- **The mean-value inequality for Floer solutions on squares.** Let `K = K_s ds + K_t dt` be
`C³` and `J(z, x)` be `C²` on an open set `W ⊆ (ℝ × ℝ) × V` containing `D × K` for compact
`D ⊆ ℝ × ℝ` and `K ⊆ V`. There is a threshold `δ > 0` with the following property. Let `u` be a
`C³` solution of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on the square `B_r(z₀) ⊆ D`
of side `2 r`, with image in `K` and `‖∂ₛu‖²` integrable. If `π r² + ∫_{B_r(z₀)} ‖∂ₛu‖² < δ`, then
`π r² ‖∂ₛu(z₀)‖² ≤ 7 π r² + 32 ∫_{B_r(z₀)} ‖∂ₛu‖²`. This is
`TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy` on the disc
of radius `r / 2` inscribed in the square, read through the complex coordinate `equivRealProdCLM`.
-/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_stdComplexLineReal_sq_le
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)}
    {D : Set (ℝ × ℝ)} {K : Set V} (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W) :
    ∃ δ > 0, ∀ ⦃u : ℝ × ℝ → V⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 < r → ball z₀ r ⊆ D →
      ContDiffOn ℝ 3 u (ball z₀ r) →
      (∀ z ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) →
      MapsTo u (ball z₀ r) K →
      IntegrableOn (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2) (ball z₀ r) →
      π * r ^ 2 + ∫ z in ball z₀ r, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ stdComplexLineReal‖ ^ 2 ≤
        7 * π * r ^ 2 + 32 * ∫ z in ball z₀ r, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  set g : ℂ × V → (ℝ × ℝ) × V := fun q ↦ (e q.1, q.2)
  have hg {n : WithTop ℕ∞} : ContDiff ℝ n g :=
    (e.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hX := ω.contDiffOn_hamiltonianOneForm_uncurry hW hKs hKt
  obtain ⟨δ, hδ, hmean⟩ :=
    Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy
    (J := fun q ↦ (J (e q.1) q.2).toLinearMap.toContinuousLinearMap)
    (X := fun q ↦ ω.hamiltonianOneForm Ks Kt (e q.1) q.2 ∘L (e : ℂ →L[ℝ] ℝ × ℝ))
    (hW.preimage (hg (n := 0)).continuous) (hJ.comp hg.contDiffOn (mapsTo_preimage g W))
    ((hX.comp hg.contDiffOn (mapsTo_preimage g W)).clm_comp
      (contDiffOn_const (c := (e : ℂ →L[ℝ] ℝ × ℝ))))
    (e.toHomeomorph.isCompact_preimage.2 hD) hK (fun q hq ↦ hDKW ⟨hq.1, hq.2⟩)
    (fun _ _ _ _ v ↦ by simp)
  refine ⟨δ, hδ, fun u z₀ r hr hrD hu hfl huK hint hsmall ↦ ?_⟩
  set d : ℝ × ℝ → ℝ := fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 with hd_def
  -- The closed disc of radius `r / 2` about `e⁻¹ z₀` lies, through `e`, in the square.
  set y₀ := e.symm z₀
  have hball : ∀ y, ‖y - y₀‖ ≤ r / 2 → e y ∈ ball z₀ r := fun y hy ↦ by
    have h := lipschitz_equivRealProd.dist_le_mul y y₀
    simp only [NNReal.coe_one, one_mul] at h
    rw [mem_ball, show z₀ = e y₀ by simp [y₀]]
    refine (h.trans ?_).trans_lt (half_lt_self hr)
    simpa [dist_eq_norm] using hy
  have hsub : ball y₀ (r / 2) ⊆ e ⁻¹' ball z₀ r := fun y hy ↦
    hball y (by simpa [dist_eq_norm] using (mem_ball.1 hy).le)
  have hu' : ContDiffOn ℝ 3 (u ∘ e) (e ⁻¹' ball z₀ r) :=
    hu.comp e.contDiff.contDiffOn (mapsTo_preimage _ _)
  -- `e` preserves volume, and `∂ₛ(u ∘ e) = (∂ₛu) ∘ e`.
  have hint' : IntegrableOn (fun y ↦ ‖fderiv ℝ (u ∘ e) y 1‖ ^ 2) (e ⁻¹' ball z₀ r) := by
    simp only [he, fderiv_comp_equivRealProdCLM_one]
    exact (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      equivRealProdCLM.toHomeomorph.measurableEmbedding).2 hint
  have hJle : ∫ y in ball y₀ (r / 2), ‖fderiv ℝ (u ∘ e) y 1‖ ^ 2 ≤ ∫ z in ball z₀ r, d z := by
    refine (setIntegral_mono_set hint' (Eventually.of_forall fun _ ↦ by positivity)
      hsub.eventuallySubset).trans_eq ?_
    simp only [he, hd_def, fderiv_comp_equivRealProdCLM_one]
    exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      equivRealProdCLM.toHomeomorph.measurableEmbedding d _
  have hmv := hmean (u := u ∘ e) (z₀ := y₀) (r := r / 2) (by positivity)
    (fun y hy ↦ hrD (hsub hy)) (hu'.mono hsub)
    (((hu'.continuousOn_fderiv_of_isOpen (isOpen_ball.preimage e.continuous)
      (by norm_num)).clm_apply continuousOn_const).mono fun y hy ↦
        hball y (by simpa [dist_eq_norm] using mem_closedBall.1 hy))
    (fun y hy ↦ by simpa [he] using ω.fderiv_comp_equivRealProdCLM_I_sub (hfl (e y) (hsub hy)))
    (fun y hy ↦ huK (hsub hy))
    (by nlinarith [pi_pos, sq_nonneg r])
  rw [fderiv_comp_equivRealProdCLM_one, show e y₀ = z₀ by simp [y₀]] at hmv
  nlinarith

/-- **The mean-value inequality for the Floer energy density.** Let `K = K_s ds + K_t dt` be `C³`
and `J(z, x)` be `C²` on an open set `W ⊆ (ℝ × ℝ) × V` containing `D × K` for compact
`D ⊆ ℝ × ℝ` and `K ⊆ V`, with `J(z, x)` tamed by `ω` on `D × K`. There are a threshold `δ > 0` and
a constant `A ≥ 0` with the following property. Let `u` be a `C³` solution of the Floer equation
`(du - X_K)^{0,1} = 0` for `J(z, u)` on the square `B_r(z₀) ⊆ D` of side `2 r`, with image in `K`
and integrable energy density `e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`. If `r² + ∫_{B_r(z₀)} e < δ`,
then `r² e(z₀) ≤ A (r² + ∫_{B_r(z₀)} e)`. -/
theorem exists_pos_forall_sq_mul_floerEnergyDensity_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)}
    {K : Set V} (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > 0, ∃ A ≥ 0, ∀ ⦃u : ℝ × ℝ → V⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 < r → ball z₀ r ⊆ D →
      ContDiffOn ℝ 3 u (ball z₀ r) →
      (∀ z ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) →
      MapsTo u (ball z₀ r) K → IntegrableOn (ω.floerEnergyDensity Ks Kt u) (ball z₀ r) →
      r ^ 2 + ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z < δ →
      r ^ 2 * ω.floerEnergyDensity Ks Kt u z₀ ≤
        A * (r ^ 2 + ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z) := by
  obtain ⟨L, hL0, hL⟩ := ω.exists_forall_norm_fderiv_sq_le_and_floerEnergyDensity_le hD hK
    (hJ.continuousOn.mono hDKW)
    ((ω.contDiffOn_hamiltonianOneForm_uncurry hW hKs hKt).continuousOn.mono hDKW) hJt
  obtain ⟨δ₀, hδ₀, hmean⟩ :=
    ω.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_stdComplexLineReal_sq_le hW hKs hKt hJ hD hK
      hDKW
  set C₁ := 2 * L + 1
  have hC₁ : 0 < C₁ := by positivity
  refine ⟨δ₀ / (4 + 4 * C₁), by positivity, L * (8 + 128 * C₁), by positivity,
    fun u z₀ r hr hrD hu hfl huK hint hsmall ↦ ?_⟩
  set f := ω.floerEnergyDensity Ks Kt u
  set I := ∫ z in ball z₀ r, f z
  have hf0 : ∀ z ∈ ball z₀ r, 0 ≤ f z := fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJt z (hrD hz) _ (huK hz)) (hfl z hz)
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball hf0
  -- On the square, `‖∂ₛu‖²` is integrable, with integral at most `C₁ (4 r² + ∫ e)`.
  set d : ℝ × ℝ → ℝ := fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 with hd_def
  have hdle : ∀ z ∈ ball z₀ r, d z ≤ L * f z + L := fun z hz ↦ by
    have h1 : ‖fderiv ℝ u z stdComplexLineReal‖ ≤ ‖fderiv ℝ u z‖ :=
      ((fderiv ℝ u z).le_opNorm _).trans_eq (by simp [stdComplexLineReal_eq, Prod.norm_def])
    have h2 := (hL (hrD hz) (huK hz) (hfl z hz)).1
    simp only [hd_def]
    nlinarith [norm_nonneg (fderiv ℝ u z stdComplexLineReal)]
  have hfin : volume (ball z₀ r) ≠ ⊤ := measure_ball_lt_top.ne
  have hdint : IntegrableOn d (ball z₀ r) := integrableOn_of_le_mul_add measurableSet_ball hfin
    ((((hu.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).clm_apply
      continuousOn_const).norm.pow 2).aestronglyMeasurable measurableSet_ball) hint
    (fun _ _ ↦ by positivity) hdle
  have hdI : ∫ z in ball z₀ r, d z ≤ C₁ * (4 * r ^ 2 + I) := by
    have h := setIntegral_le_mul_measureReal_add_setIntegral_of_le measurableSet_ball hfin hL0 hL0
      hdint hint hf0 hdle
    -- The square `B_r(z₀)` has area `4 r²`.
    have hvol : volume.real (ball z₀ r) = 4 * r ^ 2 := by
      rw [← ball_prod_same z₀.1 z₀.2 r, measureReal_def, Measure.volume_eq_prod,
        Measure.prod_prod, Real.volume_ball, Real.volume_ball, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
      ring
    rwa [hvol, show L + L + 1 = C₁ by ring] at h
  have hd0 : 0 ≤ ∫ z in ball z₀ r, d z := setIntegral_nonneg measurableSet_ball fun _ _ ↦ by
    positivity
  have hmv := hmean hr hrD hu hfl huK hdint (by
    have : (4 + 4 * C₁) * (r ^ 2 + I) < δ₀ := by
      rwa [lt_div_iff₀ (by positivity), mul_comm] at hsmall
    nlinarith [pi_le_four, sq_nonneg r])
  -- From `π r² ‖∂ₛu(z₀)‖² ≤ 7 π r² + 32 ∫ ‖∂ₛu‖²` and `π ≥ 2`, and `e ≤ L (‖∂ₛu‖² + 1)` at `z₀`.
  set s := ‖fderiv ℝ u z₀ stdComplexLineReal‖ ^ 2
  have hs : r ^ 2 * s ≤ 7 * r ^ 2 + 16 * (C₁ * (4 * r ^ 2 + I)) := by
    nlinarith [two_le_pi, sq_nonneg r, mul_nonneg (sq_nonneg r) (sq_nonneg
      ‖fderiv ℝ u z₀ stdComplexLineReal‖)]
  have hez₀ := (hL (hrD (mem_ball_self hr)) (huK (mem_ball_self hr))
    (hfl z₀ (mem_ball_self hr))).2
  calc r ^ 2 * f z₀ ≤ r ^ 2 * (L * (s + 1)) := by gcongr
    _ = L * (r ^ 2 * s + r ^ 2) := by ring
    _ ≤ L * (7 * r ^ 2 + 16 * (C₁ * (4 * r ^ 2 + I)) + r ^ 2) := by gcongr
    _ ≤ L * (8 + 128 * C₁) * (r ^ 2 + I) := by
      nlinarith [mul_nonneg hL0 (mul_nonneg hC₁.le hI0), mul_nonneg hL0 (sq_nonneg r),
        mul_nonneg hL0 (mul_nonneg hC₁.le (sq_nonneg r))]

end TauCeti.SymplecticForm

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

/-- **The energy density bounds the derivative in a symplectic chart.** Under the hypotheses of
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` on a chart `φ`
and compact sets `D` and `C ⊆ φ.source`, there is a constant `L ≥ 0` such that every solution `u`
of the Floer equation for `J(z, u)` at a point `z ∈ D` where it is differentiable, with `u z ∈ C`,
satisfies `‖d(φ ∘ u)(z)‖² ≤ L (e + 1)` for its energy density `e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`
at `z`. -/
theorem exists_forall_norm_fderiv_comp_sq_le (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hC : IsCompact C) (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ L ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄, z ∈ D → u z ∈ C →
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap →
      ‖fderiv ℝ (φ ∘ u) z‖ ^ 2 ≤ L * (ω.floerEnergyDensity Ks Kt u z + 1) := by
  have hφC : IsCompact (φ '' C) := hC.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hCφ)
  have hJ't : ∀ z ∈ D, ∀ y ∈ φ '' C, ω₀.Tames (J' z y) := by
    rintro z hz _ ⟨x, hx, rfl⟩
    exact tames_of_isComplexLinearMap_mvfderiv hω
      (φ.bijective_mvfderiv (by simp) (hCφ hx)).surjective (hφ x hx) (hJJ' z hz x hx)
      (hJt z hz x hx)
  obtain ⟨L, hL0, hL⟩ := ω₀.exists_forall_norm_fderiv_sq_le_and_floerEnergyDensity_le
    (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hD hφC
    (hJ'.continuousOn.mono hDCW)
    ((ω₀.contDiffOn_hamiltonianOneForm_uncurry (Ks := fun z y ↦ Ks z (φ.symm y))
      (Kt := fun z y ↦ Kt z (φ.symm y)) hW hKs hKt).continuousOn.mono hDCW) hJ't
  refine ⟨L, hL0, fun u z hz hu hdu hfl ↦ ?_⟩
  obtain ⟨he, hfl'⟩ := floerEnergyDensity_comp_and_isComplexLinearMap hω φ (hφ _ hu)
    (hJJ' z hz _ hu) hW hKs hKt (hCφ hu) (hDCW ⟨hz, u z, hu, rfl⟩) hdu hfl
  rw [← he]
  exact (hL hz ⟨u z, hu, rfl⟩ hfl').1

/-- **The mean-value inequality for Floer solutions in a symplectic chart.** Under the hypotheses
of `IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` on a chart
`φ` and compact sets `D` and `C ⊆ φ.source`, there are a threshold `δ > 0` and a constant `A ≥ 0`
with the following property. Let `u` be a `C³` solution of the Floer equation
`(du - X_K)^{0,1} = 0` for `J(z, u)` on the square `B_r(z₀) ⊆ D`, with image in `C` and
integrable energy density `e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`. If `r² + ∫_{B_r(z₀)} e < δ`, then
`r² e(z₀) ≤ A (r² + ∫_{B_r(z₀)} e)`. -/
theorem exists_pos_forall_sq_mul_floerEnergyDensity_le (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hC : IsCompact C) (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ δ > 0, ∃ A ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 < r → ball z₀ r ⊆ D →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ r) →
      (∀ z ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) →
      MapsTo u (ball z₀ r) C → IntegrableOn (ω.floerEnergyDensity Ks Kt u) (ball z₀ r) →
      r ^ 2 + ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z < δ →
      r ^ 2 * ω.floerEnergyDensity Ks Kt u z₀ ≤
        A * (r ^ 2 + ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z) := by
  have hφC : IsCompact (φ '' C) := hC.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hCφ)
  have hJ't : ∀ z ∈ D, ∀ y ∈ φ '' C, ω₀.Tames (J' z y) := by
    rintro z hz _ ⟨x, hx, rfl⟩
    exact tames_of_isComplexLinearMap_mvfderiv hω
      (φ.bijective_mvfderiv (by simp) (hCφ hx)).surjective (hφ x hx) (hJJ' z hz x hx)
      (hJt z hz x hx)
  obtain ⟨δ, hδ, A, hA, hmean⟩ := ω₀.exists_pos_forall_sq_mul_floerEnergyDensity_le
    (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hW hKs hKt hJ' hD hφC
    hDCW hJ't
  refine ⟨δ, hδ, A, hA, fun u z₀ r hr hrD hu hfl huC hint hsmall ↦ ?_⟩
  -- At each point of the square, the chart transports the Floer equation and the energy density.
  have hpt {z : ℝ × ℝ} (hz : z ∈ ball z₀ r) :=
    floerEnergyDensity_comp_and_isComplexLinearMap hω φ (hφ _ (huC hz))
      (hJJ' z (hrD hz) _ (huC hz)) hW hKs hKt (hCφ (huC hz))
      (hDCW ⟨hrD hz, u z, huC hz, rfl⟩)
      ((hu.contMDiffAt (isOpen_ball.mem_nhds hz)).mdifferentiableAt (by norm_num)) (hfl z hz)
  have hint_eq : ∫ z in ball z₀ r, ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y))
      (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u) z = ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z :=
    setIntegral_congr_fun measurableSet_ball fun z hz ↦ (hpt hz).1
  have h := hmean (u := φ ∘ u) hr hrD
    (contMDiffOn_iff_contDiffOn.1 <| (φ.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp hu
      (huC.mono_right hCφ))
    (fun z hz ↦ (hpt hz).2) (fun z hz ↦ ⟨u z, huC hz, rfl⟩)
    (hint.congr_fun (fun z hz ↦ ((hpt hz).1).symm) measurableSet_ball) (hint_eq ▸ hsmall)
  rwa [hint_eq, (hpt (mem_ball_self hr)).1] at h

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ V] in
/-- In a chart `φ`, a compact set `A` in the interior of `C ⊆ φ.source` has a margin: there is
`η > 0` such that every point of `C` within `η` of a point of `A`, measured in the chart, lies in
the interior of `C`. -/
private theorem exists_pos_forall_mem_interior (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {A C : Set M} (hA : IsCompact A) (hAC : A ⊆ interior C) (hCφ : C ⊆ φ.source) :
    ∃ η > 0, ∀ a ∈ A, ∀ x ∈ C, ‖φ x - φ a‖ < η → x ∈ interior C := by
  have hAφ : A ⊆ φ.source := hAC.trans (interior_subset.trans hCφ)
  have hT : IsCompact (φ '' A) := hA.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hAφ)
  have hU : IsOpen (φ '' interior C) := by
    simpa using φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
      (by simpa using interior_subset.trans hCφ)
  obtain ⟨η, hη, hsub⟩ := hT.exists_thickening_subset_open hU (image_mono hAC)
  refine ⟨η, hη, fun a ha x hx hxa ↦ ?_⟩
  obtain ⟨c, hc, hcx⟩ := hsub (mem_thickening_iff.2 ⟨φ a, mem_image_of_mem φ ha, by
    rwa [dist_eq_norm]⟩)
  rwa [← φ.toPartialEquiv.injOn (hCφ (interior_subset hc)) (hCφ hx) hcx]

/-- Under the hypotheses of `exists_pos_forall_sq_mul_floerEnergyDensity_le` on a chart `φ`, the
energy density of a `C³` solution on an open set `U ⊆ D` is continuous at every point `z` of `U`
with `u z` in the interior of `C`: near `z` it is the energy density of the coordinate map. -/
private theorem continuousAt_floerEnergyDensity (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W) {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hUD : U ⊆ D) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U)
    (hfl : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) {z : ℝ × ℝ} (hz : z ∈ U)
    (hzC : u z ∈ interior C) :
    ContinuousAt (ω.floerEnergyDensity Ks Kt u) z := by
  set N := U ∩ u ⁻¹' interior C
  have hN : IsOpen N := hu.continuousOn.isOpen_inter_preimage hU isOpen_interior
  have hNC {y : ℝ × ℝ} (hy : y ∈ N) : u y ∈ C := interior_subset hy.2
  have hcont := ω₀.continuousOn_floerEnergyDensity_of_continuousOn_hamiltonianOneForm
    (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hN
    ((contMDiffOn_iff_contDiffOn.1 <| (φ.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp
      (hu.mono inter_subset_left) fun y hy ↦ hCφ (hNC hy)).of_le (by norm_num))
    (ω₀.contDiffOn_hamiltonianOneForm_uncurry (Ks := fun z y ↦ Ks z (φ.symm y))
      (Kt := fun z y ↦ Kt z (φ.symm y)) hW hKs hKt).continuousOn
    fun y hy ↦ hDCW ⟨hUD hy.1, u y, hNC hy, rfl⟩
  refine (hcont.congr fun y hy ↦ ?_).continuousAt (hN.mem_nhds ⟨hz, hzC⟩)
  exact (floerEnergyDensity_comp_and_isComplexLinearMap hω φ (hφ _ (hNC hy))
    (hJJ' y (hUD hy.1) _ (hNC hy)) hW hKs hKt (hCφ (hNC hy))
    (hDCW ⟨hUD hy.1, u y, hNC hy, rfl⟩)
    ((hu.contMDiffAt (hU.mem_nhds hy.1)).mdifferentiableAt (by norm_num)) (hfl y hy.1)).1.symm

/-- The arithmetic of the case of the mean-value inequality in which the trapping radius
`t = η / (√(L (4 a + 1)) + 1)` is the binding constraint: if `t² a ≤ A (t² + Q)` and `Q` is small
compared with `η²`, then `a ≤ 2 A + 1`. -/
private theorem le_two_mul_add_one_of_sq_mul_le {a A L η Q : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hη : 0 < η) (hQ0 : 0 ≤ Q) (hQ : Q ≤ η ^ 2 / (16 * (A + 1) * (L + 1)))
    (h : (η / (√(L * (4 * a + 1)) + 1)) ^ 2 * a ≤
      A * ((η / (√(L * (4 * a + 1)) + 1)) ^ 2 + Q)) :
    a ≤ 2 * A + 1 := by
  set κ := √(L * (4 * a + 1))
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = L * (4 * a + 1) := Real.sq_sqrt (by positivity)
  have hm : 0 < κ + 1 := by positivity
  -- Clear the denominator `(κ + 1)²`.
  have h' : η ^ 2 * a ≤ A * η ^ 2 + A * Q * (κ + 1) ^ 2 := by
    rw [div_pow] at h
    have := mul_le_mul_of_nonneg_right h (sq_nonneg (κ + 1))
    field_simp at this
    nlinarith [this]
  have hm2 : (κ + 1) ^ 2 ≤ 2 * L * (4 * a + 1) + 2 := by nlinarith [sq_nonneg (κ - 1)]
  have hAQ : 16 * (A * Q) * (L + 1) ≤ η ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at hQ
    nlinarith [mul_nonneg hQ0 (mul_nonneg hA hL)]
  have hη2 : 0 < η ^ 2 := by positivity
  have h3 : A * Q * (κ + 1) ^ 2 ≤ η ^ 2 * a / 2 + η ^ 2 / 8 := by
    have hAQ0 : 0 ≤ A * Q := mul_nonneg hA hQ0
    calc A * Q * (κ + 1) ^ 2 ≤ A * Q * (2 * L * (4 * a + 1) + 2) := by gcongr
      _ = 8 * (A * Q) * L * a + 2 * (A * Q) * (L + 1) := by ring
      _ ≤ η ^ 2 * a / 2 + η ^ 2 / 8 := by nlinarith [mul_nonneg hAQ0 ha, mul_nonneg hL ha]
  nlinarith

/-- The arithmetic that ends the mean-value inequality. Let `a ≥ 0` satisfy `s² a ≤ A (s² + Q)`
for the radius `s = min ε' t` with `t = η / (√(L (4 a + 1)) + 1)`, where `0 < ε' ≤ ε` and `Q` is
small compared with `η²`. Then `ε'² a ≤ (3 A + 1)(ε² + Q)`: either `s = ε'`, or the trapping radius
binds and `a ≤ 2 A + 1`. -/
private theorem sq_mul_le_of_min_sq_mul_le {a A L η Q ε ε' : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hη : 0 < η) (hQ0 : 0 ≤ Q) (hQ : Q ≤ η ^ 2 / (16 * (A + 1) * (L + 1)))
    (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (h : min ε' (η / (√(L * (4 * a + 1)) + 1)) ^ 2 * a ≤
      A * (min ε' (η / (√(L * (4 * a + 1)) + 1)) ^ 2 + Q)) :
    ε' ^ 2 * a ≤ (3 * A + 1) * (ε ^ 2 + Q) := by
  have hε'2 : ε' ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hε'.le hε'ε 2
  rcases le_total ε' (η / (√(L * (4 * a + 1)) + 1)) with ht | ht
  · rw [min_eq_left ht] at h
    nlinarith
  · rw [min_eq_right ht] at h
    have hbd := le_two_mul_add_one_of_sq_mul_le ha hA hL hη hQ0 hQ h
    nlinarith [mul_le_mul hε'2 hbd ha (by positivity)]

/-- **The mean-value inequality for Floer solutions in a manifold.** Let finitely many symplectic
charts `φ i` carry the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le` on compact
sets `C i ⊆ (φ i).source`, over a compact window `D` of the domain, and let `A i` be compact sets
with `A i` in the interior of `C i`; for a closed manifold, finitely many Darboux charts give such
sets with `⋃ A i = M`. There are a threshold `δ > 0` and a constant `B ≥ 0` with the following
property. Let `u` be a `C³` solution of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on
the square `B_r(z₀) ⊆ D`, with image in `⋃ A i` and integrable energy density
`e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`. If `r² + ∫_{B_r(z₀)} e < δ`, then
`r² e(z₀) ≤ B (r² + ∫_{B_r(z₀)} e)`.

The image of `B_r(z₀)` need not lie in a single chart: the proof finds, by Hofer's lemma, a point
`x'` and a radius on which `e` is at most `4 e(x')`, shows that a smaller square about `x'` stays
in one set `C i` because the derivative of the chart reading is controlled by `e`, and applies the
mean-value inequality in that chart. -/
theorem exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mapsTo_iUnion
    [T2Space M] (hω : ω.IsNondegenerate) {ι : Type*} [Finite ι]
    (φ : ι → PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {Jc : ι → ℝ × ℝ → V → AlmostComplexStructure V} {W : ι → Set ((ℝ × ℝ) × V)}
    {D : Set (ℝ × ℝ)} {A C : ι → Set M}
    (hφ : ∀ i, ∀ x ∈ C i, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I (φ i) x v) (mvfderiv I (φ i) x w))
    (hJJ' : ∀ i, ∀ z ∈ D, ∀ x ∈ C i,
      IsComplexLinearMap (J z x) (Jc i z (φ i x)) (mvfderiv I (φ i) x).toLinearMap)
    (hW : ∀ i, IsOpen (W i))
    (hKs : ∀ i, ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 ((φ i).symm p.2)) (W i))
    (hKt : ∀ i, ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 ((φ i).symm p.2)) (W i))
    (hJc : ∀ i, ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (Jc i p.1 p.2).toLinearMap.toContinuousLinearMap) (W i))
    (hD : IsCompact D) (hC : ∀ i, IsCompact (C i)) (hCφ : ∀ i, C i ⊆ (φ i).source)
    (hDCW : ∀ i, D ×ˢ ((φ i) '' C i) ⊆ W i)
    (hJt : ∀ i, ∀ z ∈ D, ∀ x ∈ C i, (hω.symplecticFormAt x).Tames (J z x))
    (hA : ∀ i, IsCompact (A i)) (hAC : ∀ i, A i ⊆ interior (C i)) :
    ∃ δ > 0, ∃ B ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, 0 < r → ball z₀ r ⊆ D →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ r) →
      (∀ z ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) →
      MapsTo u (ball z₀ r) (⋃ i, A i) → IntegrableOn (ω.floerEnergyDensity Ks Kt u) (ball z₀ r) →
      r ^ 2 + ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z < δ →
      r ^ 2 * ω.floerEnergyDensity Ks Kt u z₀ ≤
        B * (r ^ 2 + ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z) := by
  -- The proof has four steps: uniform constants over the charts; Hofer's lemma for `e` at `z₀`,
  -- giving `x'` and `ε'`; trapping a square about `x'` in one chart `C i`; and the mean-value
  -- inequality in that chart, combined with the arithmetic of `sq_mul_le_of_min_sq_mul_le`.
  -- Constants for each chart, made uniform over the finitely many charts.
  choose δi hδi Ai _ hmean using fun i ↦ exists_pos_forall_sq_mul_floerEnergyDensity_le hω
    (φ i) (hφ i) (hJJ' i) (hW i) (hKs i) (hKt i) (hJc i) hD (hC i) (hCφ i) (hDCW i) (hJt i)
  choose Li _ hder using fun i ↦ exists_forall_norm_fderiv_comp_sq_le hω
    (φ i) (hφ i) (hJJ' i) (hW i) (hKs i) (hKt i) (hJc i) hD (hC i) (hCφ i) (hDCW i) (hJt i)
  choose ηi hηi hmarg using fun i ↦ exists_pos_forall_mem_interior (φ i) (hA i) (hAC i) (hCφ i)
  obtain ⟨⟨δ₀, hδ₀⟩, hδ₀i⟩ := Finite.exists_ge fun i ↦ (⟨δi i, hδi i⟩ : {x : ℝ // 0 < x})
  obtain ⟨⟨η, hη⟩, hηi'⟩ := Finite.exists_ge fun i ↦ (⟨ηi i, hηi i⟩ : {x : ℝ // 0 < x})
  obtain ⟨A₀, hA₀⟩ := Finite.exists_le Ai
  obtain ⟨L₀, hL₀⟩ := Finite.exists_le Li
  set A' := max A₀ 0
  set L' := max L₀ 0
  have hA' : ∀ i, Ai i ≤ A' := fun i ↦ (hA₀ i).trans (le_max_left _ _)
  have hL' : ∀ i, Li i ≤ L' := fun i ↦ (hL₀ i).trans (le_max_left _ _)
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hL'0 : 0 ≤ L' := le_max_right _ _
  refine ⟨min δ₀ (η ^ 2 / (16 * (A' + 1) * (L' + 1))), by positivity, 16 * (3 * A' + 1),
    by positivity, fun u z₀ r hr hrD hu hfl huA hint hsmall ↦ ?_⟩
  set e := ω.floerEnergyDensity Ks Kt u
  set E₀ := ∫ z in ball z₀ r, e z
  have hAC' (i : ι) : A i ⊆ C i := (hAC i).trans interior_subset
  have huA' {z : ℝ × ℝ} (hz : z ∈ ball z₀ r) : ∃ i, u z ∈ A i := mem_iUnion.1 (huA hz)
  have he0 : ∀ z ∈ ball z₀ r, 0 ≤ e z := fun z hz ↦ by
    obtain ⟨i, hi⟩ := huA' hz
    exact floerEnergyDensity_nonneg hω (hJt i z (hrD hz) _ (hAC' i hi)) (hfl z hz)
  have hI0 : 0 ≤ E₀ := setIntegral_nonneg measurableSet_ball he0
  have hIsmall : r ^ 2 + E₀ < δ₀ := hsmall.trans_le (min_le_left _ _)
  have hIη : E₀ ≤ η ^ 2 / (16 * (A' + 1) * (L' + 1)) := by
    have := hsmall.trans_le (min_le_right _ _)
    nlinarith [sq_nonneg r]
  have hcont : ContinuousOn e (ball z₀ r) := fun z hz ↦ by
    obtain ⟨i, hi⟩ := huA' hz
    exact (continuousAt_floerEnergyDensity hω (φ i) (hφ i) (hJJ' i) (hW i) (hKs i) (hKt i)
      (hCφ i) (hDCW i) isOpen_ball hrD hu hfl hz (hAC i hi)).continuousWithinAt
  -- Hofer's lemma for `e` at `z₀`, with `ε = r / 4`: a point `x'` and a radius `ε'` on which
  -- `e ≤ 4 e(x')`, with `ε² e(z₀) ≤ ε'² e(x')`.
  set ε := r / 4 with hε_def
  have hε : 0 < ε := by positivity
  have h3ε : closedBall z₀ (3 * ε) ⊆ ball z₀ r := closedBall_subset_ball (by linarith)
  obtain ⟨ε', hε', x', hε'ε, hx', hεe, hloc⟩ := hofer_sq_of_continuousOn_closedBall z₀ hε
    (hcont.mono h3ε) fun y hy ↦ he0 y (h3ε hy)
  have hsub : ball x' ε' ⊆ ball z₀ r := fun y hy ↦ by
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y x' z₀]
  have hx'r : x' ∈ ball z₀ r := hsub (mem_ball_self hε')
  have hex'0 : 0 ≤ e x' := he0 x' hx'r
  have hloc' : ∀ y ∈ ball x' ε', e y ≤ 4 * e x' := fun y hy ↦
    hloc y (by rw [dist_comm]; exact (mem_ball.1 hy).le)
  -- The chart of `u x'`, the derivative bound `κ` there, and the trapping radius `s`.
  obtain ⟨i, hi⟩ := huA' hx'r
  set κ := √(L' * (4 * e x' + 1))
  set t := η / (κ + 1)
  set s := min ε' t
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have ht : 0 < t := by positivity
  have hs : 0 < s := lt_min hε' ht
  have hsub' : ball x' s ⊆ ball z₀ r := (ball_subset_ball (min_le_left _ _)).trans hsub
  have hκs : κ * s ≤ η := by
    calc κ * s ≤ κ * t := mul_le_mul_of_nonneg_left (min_le_right _ _) hκ0
      _ ≤ (κ + 1) * t := by gcongr; linarith
      _ = η := mul_div_cancel₀ _ (by positivity)
  have htrap : MapsTo u (ball x' s) (C i) :=
    (φ i).mapsTo_ball_of_norm_fderiv_comp_le (by simp) (hC i).isClosed (hCφ i)
      ((hu.mdifferentiableOn (by norm_num)).mono hsub') (hAC' i hi)
      (fun x hx hlt ↦ hmarg i _ hi x hx (hlt.trans_le (Subtype.coe_le_coe.2 (hηi' i))))
      (fun y hy hyC ↦ by
        have hmd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u y :=
          (hu.contMDiffAt (isOpen_ball.mem_nhds (hsub' hy))).mdifferentiableAt (by norm_num)
        rw [← Real.sqrt_sq (norm_nonneg _)]
        refine Real.sqrt_le_sqrt ((hder i (hrD (hsub' hy)) hyC hmd (hfl y (hsub' hy))).trans ?_)
        have hy' : e y ≤ 4 * e x' := hloc' y (ball_subset_ball (min_le_left _ _) hy)
        exact mul_le_mul (hL' i) (by linarith) (by linarith [he0 y (hsub' hy)]) hL'0)
      hη hκs
  -- The mean-value inequality in the chart `i` on the square of radius `s` about `x'`.
  have hIs : ∫ z in ball x' s, e z ≤ E₀ :=
    setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_ball he0)
      hsub'.eventuallySubset
  have hsr : s ≤ r := (min_le_left _ _).trans (hε'ε.trans (by linarith))
  have hmv := hmean i (u := u) (z₀ := x') (r := s) hs (hsub'.trans hrD) (hu.mono hsub')
    (fun z hz ↦ hfl z (hsub' hz)) htrap (hint.mono_set hsub') (by
      have : s ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hs.le hsr 2
      linarith [Subtype.coe_le_coe.2 (hδ₀i i)])
  have hmv' : s ^ 2 * e x' ≤ A' * (s ^ 2 + E₀) :=
    hmv.trans (mul_le_mul (hA' i) (by linarith) (add_nonneg (sq_nonneg s)
      (setIntegral_nonneg measurableSet_ball fun z hz ↦ he0 z (hsub' hz))) hA'0)
  have hkey := sq_mul_le_of_min_sq_mul_le hex'0 hA'0 hL'0 hη hI0 hIη hε' hε'ε hmv'
  have hr2 : r ^ 2 = 16 * ε ^ 2 := by ring
  rw [hr2]
  nlinarith [hεe.trans hkey]

end TauCeti.SmoothTwoForm.IsNondegenerate
