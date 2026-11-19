/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Chart
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.Analysis.Hofer
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Topology.OpenPartialHomeomorph.ClosedBall

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
  (`TauCeti.SymplecticForm.exists_pos_forall_sq_mul_floerEnergyDensity_le`, in
  `TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`).
* Read in a symplectic chart `φ` of a manifold `M`, the same holds for solutions whose image lies
  in a compact subset `C` of the chart
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le`). There
  the derivative of the chart reading `φ ∘ u` is bounded by `e`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_comp_sq_le`, in
  `TauCeti.Geometry.Symplectic.Floer.Chart`).
* For finitely many such charts, into possibly different symplectic vector spaces, and compact sets
  `A i` in the interiors of the `C i`, the inequality holds for every solution with image in
  `⋃ A i`, whether or not the image of the square lies in a single chart
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

open Filter Function MeasureTheory Metric Real Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

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
  obtain ⟨δ, hδ, A, hA, hmean⟩ := ω₀.exists_pos_forall_sq_mul_floerEnergyDensity_le
    (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hW hKs hKt hJ' hD hφC
    hDCW fun z hz ↦ hω.tames_of_mem_image φ (by simp) hφ (hJJ' z hz) hCφ (hJt z hz)
  refine ⟨δ, hδ, A, hA, fun u z₀ r hr hrD hu hfl huC hint hsmall ↦ ?_⟩
  -- At each point of the square, the chart transports the Floer equation and the energy density.
  have hpt {z : ℝ × ℝ} (hz : z ∈ ball z₀ r) :
      ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u) z =
          ω.floerEnergyDensity Ks Kt u z ∧
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' z (φ (u z)))
          (ω₀.perturbedFDeriv (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u)
            z).toLinearMap := by
    have hzW : (z, φ (u z)) ∈ W := hDCW ⟨hrD hz, u z, huC hz, rfl⟩
    have hdu := (hu.contMDiffAt (isOpen_ball.mem_nhds hz)).mdifferentiableAt (by norm_num)
    have hdKs := (hKs.differentiableOn (by norm_num) _ hzW).differentiableAt (hW.mem_nhds hzW)
    have hdKt := (hKt.differentiableOn (by norm_num) _ hzW).differentiableAt (hW.mem_nhds hzW)
    exact ⟨hω.floerEnergyDensity_comp_of_mem_source φ (by simp) hdu (hCφ (huC hz))
      (hφ _ (huC hz)) hdKs hdKt,
      (hω.isComplexLinearMap_perturbedFDeriv_comp_iff_of_mem_source φ (by simp) hdu (hCφ (huC hz))
        (hφ _ (huC hz)) hdKs hdKt (hJJ' z (hrD hz) _ (huC hz))).2 (hfl z hz)⟩
  have hint_eq : ∫ z in ball z₀ r, ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y))
      (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u) z = ∫ z in ball z₀ r, ω.floerEnergyDensity Ks Kt u z :=
    setIntegral_congr_fun measurableSet_ball fun z hz ↦ (hpt hz).1
  have h := hmean (u := φ ∘ u) hr hrD
    (contMDiffOn_iff_contDiffOn.1 <| (φ.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp hu
      (huC.mono_right hCφ))
    (fun z hz ↦ (hpt hz).2) (fun z hz ↦ ⟨u z, huC hz, rfl⟩)
    (hint.congr_fun (fun z hz ↦ ((hpt hz).1).symm) measurableSet_ball) (hint_eq ▸ hsmall)
  rwa [hint_eq, (hpt (mem_ball_self hr)).1] at h

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
charts `φ i` into symplectic vector spaces `(V i, ω₀ i)` carry the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le` on compact
sets `C i ⊆ (φ i).source`, over a compact window `D` of the domain, and let `A i` be compact sets
with `A i` in the interior of `C i`; for a closed manifold, finitely many Darboux charts give such
sets with `⋃ A i = M`. There are a threshold `δ > 0` and a constant `B ≥ 0` with the following
property. Let `u` be a `C³` solution of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on
the square `B_r(z₀) ⊆ D`, with image in `⋃ A i` and integrable energy density
`e = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`. If `r² + ∫_{B_r(z₀)} e < δ`, then
`r² e(z₀) ≤ B (r² + ∫_{B_r(z₀)} e)`. The image of `B_r(z₀)` need not lie in a single chart. -/
theorem exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mapsTo_iUnion
    [T2Space M] (hω : ω.IsNondegenerate) {ι : Type*} [Finite ι] {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)] {ω₀ : (i : ι) → SymplecticForm (V i)}
    (φ : (i : ι) → PartialDiffeomorph I 𝓘(ℝ, V i) M (V i) (⊤ : ℕ∞))
    {Jc : (i : ι) → ℝ × ℝ → V i → AlmostComplexStructure (V i)}
    {W : (i : ι) → Set ((ℝ × ℝ) × V i)} {D : Set (ℝ × ℝ)} {A C : ι → Set M}
    (hφ : ∀ i, ∀ x ∈ C i, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ i (mvfderiv I (φ i) x v) (mvfderiv I (φ i) x w))
    (hJJ' : ∀ i, ∀ z ∈ D, ∀ x ∈ C i,
      IsComplexLinearMap (J z x) (Jc i z (φ i x)) (mvfderiv I (φ i) x).toLinearMap)
    (hW : ∀ i, IsOpen (W i))
    (hKs : ∀ i, ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V i ↦ Ks p.1 ((φ i).symm p.2)) (W i))
    (hKt : ∀ i, ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V i ↦ Kt p.1 ((φ i).symm p.2)) (W i))
    (hJc : ∀ i, ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V i ↦ (Jc i p.1 p.2).toLinearMap.toContinuousLinearMap) (W i))
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
  choose Li _ hder using fun i ↦ exists_forall_norm_fderiv_comp_sq_le hω (φ i) (by simp) (hφ i)
    (hJJ' i) (hW i) ((hKs i).of_le (by norm_num)) ((hKt i).of_le (by norm_num))
    ((hJc i).continuousOn.mono (hDCW i)) hD (hC i) (hCφ i) (hDCW i) (hJt i)
  choose ηi hηi hmarg using fun i ↦
    (φ i).toOpenPartialHomeomorph.exists_pos_forall_mem_interior (hA i) (hAC i) (hCφ i)
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
    exact (continuousAt_floerEnergyDensity hω (φ i) (by simp) (hφ i) (hW i)
      ((hKs i).of_le (by norm_num)) ((hKt i).of_le (by norm_num)) (hCφ i) (hDCW i) isOpen_ball
      hrD (hu.of_le (by norm_num)) hz (hAC i hi)).continuousWithinAt
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
    ((φ i).mapsTo_ball_of_norm_fderiv_comp_le (by simp) (hC i).isClosed (hCφ i)
      ((hu.mdifferentiableOn (by norm_num)).mono hsub') (hAC' i hi)
      (fun x hx hlt ↦ hmarg i _ hi x hx (by
        rw [dist_eq_norm]
        exact hlt.trans_le (Subtype.coe_le_coe.2 (hηi' i))))
      (fun y hy hyC ↦ by
        have hmd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u y :=
          (hu.contMDiffAt (isOpen_ball.mem_nhds (hsub' hy))).mdifferentiableAt (by norm_num)
        rw [← Real.sqrt_sq (norm_nonneg _)]
        refine Real.sqrt_le_sqrt ((hder i (hrD (hsub' hy)) (interior_subset hyC) hmd
          (hfl y (hsub' hy))).trans ?_)
        have hy' : e y ≤ 4 * e x' := hloc' y (ball_subset_ball (min_le_left _ _) hy)
        exact mul_le_mul (hL' i) (by linarith) (by linarith [he0 y (hsub' hy)]) hL'0)
      hη hκs).1.mono_right interior_subset
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
