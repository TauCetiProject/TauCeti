/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Limit
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit
import TauCeti.Order.Interval.Set.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Compactness along the ends of pairs of pants

Let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in a
symplectic vector space `(V, ω)`, equal to `H_q(t) dt` beyond a height `T₀` on each end `q`,
for period-one Hamiltonians `H_q`, such as the pair-of-pants perturbation
`TauCeti.Floer.pairOfPantsPerturbation` with `T₀ = 2`. Let `J(z, x)` be a family of almost
complex structures on `S × V` which is cylindrical on the end `q` beyond `T₀`:
`J(φ_q(±s, t), x) = J_q(t, x)` for `s ≥ T₀`, for a `C²` family `J_q` of `ω`-tame structures. The
compactness theorem for pairs of pants, in the namespace `TauCeti.SymplecticForm`,
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation`)
applies on a fixed compact window of `S`. Breaking along the end `q` concerns windows that move
off to the puncture instead: a sequence of solutions `uₖ` is read along the end at heights `Rₖ`,
through the translated ends

`vₖ(s, t) = uₖ(φ'_q(s + Rₖ, t))`,

where `φ'_q` is the positive end chart `TauCeti.Floer.positiveEndChart`, in which `s → ∞` along
every end. When `Rₖ → ∞` the limits of the `vₖ` are the Floer cylinders that break off at the
end `q`.

This file proves that the `vₖ` converge off finitely many bubbling points, uniformly in the
heights, from two facts about the translated ends proved in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit`.

* **One equation for all heights.** Beyond `T₀` the end `q` is a half-cylinder whose Floer datum
  is the cylindrical datum `H'_q(t) dt`, `J'_q(t, x)` of the positive end, with
  `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`) and
  `J'_q(t, x) = J_q(±t, x)`. It does not depend on `s`, so every translated end `vₖ` solves the
  same Floer equation, whatever the height
  (`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add`).
* **Energy.** The energy of a translated end over a window of angular width one is the energy of
  `uₖ` over the image of the translated window in `S`, so it is at most the energy of `uₖ`
  (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le`).
* **Compactness.** The compactness theorem for Floer solutions of bounded energy
  (`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`)
  therefore applies to the `vₖ` on a fixed window, with a threshold `δ` that does not depend on
  the heights. The main result, in the namespace `TauCeti.SymplecticForm`,
  (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart`) fixes
  a compact window `D ⊆ (max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end chart and a compact set
  `B ⊆ V`, and gives `δ > 0` such that for every open `Ω ⊆ D`, all heights `Rₖ ≥ 0` and every
  sequence of solutions with energy at most `E` and `vₖ(Ω) ⊆ B`, a subsequence of the `vₖ`
  converges locally uniformly on `Ω` off a finite set `Z` with `#Z * δ ≤ E`.

* **The limit is a Floer cylinder.** For smooth solutions the convergence holds in `C¹`
  (`exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_comp_positiveEndChart`):
  the derivatives of the `v_{φ n}` converge to that of `v` locally uniformly on `Ω \ Z`, `v` is a
  `C¹` solution there of the Floer equation of the positive end, for the cylindrical datum
  `H'_q(t) dt` and the structures `J'_q(t, x)`, and its energy over `Ω \ Z` is at most `E`. This is
  the `C¹` compactness theorem for fixed data
  (`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`)
  applied to the translated ends.

For the pair-of-pants perturbation with `|H_q| ≤ B_q`, the energy bound
`E = a(0) + a(1) - a(∞) + B_0 + B_1 + B_∞` in terms of the limiting end actions is
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_le`. The window has
angular width less than one so that the positive end chart is injective on it; two such windows
cover any compact part of the half-cylinder. The bubbles at the points of `Z`, and the assembly of
the levels into a broken configuration, are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on Floer breaking at the ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compactness of the moduli spaces of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- A translated end `v(z) = u(φ'_q(z + (R, 0)))` of a Floer solution on `S`, on an open window `Ω`
whose translate lies in a band `(max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end, solves the
cylindrical Floer equation of the positive end on `Ω`, with integrable energy density and energy
over `Ω` at most the energy `E` of `u`. -/
private theorem isComplexLinearMap_and_integral_le_comp_positiveEndChart_add
    (ω : SymplecticForm V) {K : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {q : Puncture}
    (hHq : ContDiff ℝ 3 (uncurry (H q))) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJqt : ∀ t x, ω.Tames (Jq t x))
    (hJ : ∀ s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq t x)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : ℝ × ℝ → V} {R E t₀ : ℝ}
    (hΩT : ∀ z ∈ Ω, z + (R, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal)
    (hfl : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (equivRealProdCLM.symm z) x I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE0 : 0 ≤ E)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (equivRealProdCLM.symm z) x 1) (fun z x ↦ K (equivRealProdCLM.symm z) x I)
      u z) ≤ ENNReal.ofReal E) :
    (∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq (q.endSign * z.2) (u (positiveEndChart q (z + (R, 0)))))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun z ↦ u (positiveEndChart q (z + (R, 0))))) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z ≤ E := by
  have hKt : ContDiff ℝ 3 (uncurry fun w : ℝ × ℝ ↦ positiveEndHamiltonian H q w.2) :=
    (contDiff_uncurry_positiveEndHamiltonian hHq).comp
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hvC : ContDiffOn ℝ 3 (fun z ↦ u (positiveEndChart q (z + (R, 0)))) Ω :=
    hu.comp ((contDiff_positiveEndChart q 3).comp (contDiff_id.add contDiff_const)).contDiffOn
      fun z hz ↦ positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt (hΩT z hz).1)
  have hvfl (z : ℝ × ℝ) (hz : z ∈ Ω) :=
    isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add hKH hH hHd
      (hu.differentiableOn (by norm_num)) hfl (fun s t hs ↦ hJ s t _ hs) R (hΩT z hz).1
  have hf0 := ae_restrict_of_forall_mem (μ := volume) hΩ.measurableSet fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJqt _ _) (hvfl z hz)
  -- The energy of the translated end over `Ω` is at most the energy of `u` over `S`.
  have hlin := (setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le hKH hH hHd
    (hu.differentiableOn (by norm_num)) q R hΩ.measurableSet hΩT).trans hE
  exact ⟨hvfl, integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le
    ((ω.continuousOn_floerEnergyDensity hΩ (hvC.of_le (by norm_num))
      contDiffOn_const (hKt.of_le (by norm_num)).contDiffOn).aestronglyMeasurable
        hΩ.measurableSet) hf0 subset_rfl hE0 hlin⟩

/-- **The translated ends of Floer solutions on `S` converge off finitely many bubbling points.**
Let `K` be equal to `H_r(t) dt` beyond `T₀` on each end `r`, for period-one Hamiltonians
`H_r` which are differentiable on `V`, and `C³` on the end `q`. Let `J(z, x)` be structures on
`S × V`, `S = ℂ ∖ {0, 1}` read in real coordinates, which on the end `q` beyond `T₀` are
`J(φ_q(±s, t), x) = J_q(t, x)` for a `C²` family `J_q` of `ω`-tame structures. Fix compact sets
`D ⊆ (max T₀ 0, ∞) × (t₀, t₀ + 1)` and `B ⊆ V`. There is a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` solutions of `(du - X_K)^{0,1} = 0` on `S`
for `J(z, u)` with energy at most `E ≥ 0`, let `Rₖ ≥ 0` be heights, and let the translated ends
`vₖ(z) = uₖ(φ'_q(z + (Rₖ, 0)))` map an open `Ω ⊆ D` into `B`. Then there are a subsequence `φ`,
a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous `v : Ω \ Z → B` such that along `φ`
every disc about a point of `Z` eventually carries energy at least `δ` for the cylindrical datum
`H'_q dt`, the differentials of the `vₖ` are uniformly bounded on every compact subset of
`Ω \ Z`, and `v_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart
    (ω : SymplecticForm V) {K : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {q : Puncture}
    (hHq : ContDiff ℝ 3 (uncurry (H q))) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJqt : ∀ t x, ω.Tames (Jq t x))
    (hJq : ContDiff ℝ 2 fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ : ∀ s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq t x)
    {D : Set (ℝ × ℝ)} {B : Set V} {t₀ : ℝ} (hD : IsCompact D)
    (hDT : D ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) (hB : IsCompact B) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedFDeriv (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (equivRealProdCLM.symm z) x I) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      0 ≤ E →
      (∀ k, ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (equivRealProdCLM.symm z) x 1) (fun z x ↦ K (equivRealProdCLM.symm z) x I)
        (u k) z) ≤ ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (positiveEndChart q (z + (R k, 0)))) Ω B) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C,
          ‖fderiv ℝ (fun z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) B ∧
        TendstoLocallyUniformlyOn (fun n z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) v
          atTop (Ω \ ↑Z) := by
  -- The cylindrical datum of the positive end is smooth.
  have hKt : ContDiff ℝ 3 (uncurry fun w : ℝ × ℝ ↦ positiveEndHamiltonian H q w.2) :=
    (contDiff_uncurry_positiveEndHamiltonian hHq).comp
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hJq' : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦
      (Jq (q.endSign * p.1.2) p.2).toLinearMap.toContinuousLinearMap :=
    hJq.comp ((contDiff_const.mul (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (J := fun z ↦ Jq (q.endSign * z.2)) isOpen_univ contDiffOn_const
    hKt.contDiffOn hJq'.contDiffOn hD hB (subset_univ _) fun _ _ x _ ↦ hJqt _ x
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huK ↦ ?_⟩
  -- The translated windows lie in the band `(max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end
  -- chart.
  have hΩT (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      z + (R k, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)
  have hvC (k : ℕ) : ContDiffOn ℝ 3 (fun z ↦ u k (positiveEndChart q (z + (R k, 0)))) Ω :=
    (hu k).comp ((contDiff_positiveEndChart q 3).comp (contDiff_id.add contDiff_const)).contDiffOn
      fun z hz ↦ positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt (hΩT k z hz).1)
  have h (k : ℕ) := isComplexLinearMap_and_integral_le_comp_positiveEndChart_add ω hKH hH hHd
    hHq hJqt hJ hΩ (hΩT k) (hu k) (hfl k) hE0 (hE k)
  exact hconv hΩ hΩD hvC (fun k ↦ (h k).1) huK (fun k ↦ (h k).2.1) fun k ↦ (h k).2.2

/-- **The translated ends of smooth Floer solutions on `S` converge in `C¹` off finitely many
bubbling points to a Floer cylinder.** Under the hypotheses of
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart`, there is a
threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions of
`(du - X_K)^{0,1} = 0` on `S` for `J(z, u)` with energy at most `E ≥ 0`, let `Rₖ ≥ 0` be heights,
and let the translated ends `vₖ(z) = uₖ(φ'_q(z + (Rₖ, 0)))` map an open `Ω ⊆ D` into `B`. Then
there are a subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a map `v : Ω \ Z → B`
such that along `φ` every disc about a point of `Z` eventually carries energy at least `δ` for the
cylindrical datum `H'_q dt`, `v_{φ n} → v` and `dv_{φ n} → dv` locally uniformly on `Ω \ Z`, `v` is
a `C¹` solution on `Ω \ Z` of the Floer equation of the positive end, for the datum `H'_q dt` and
the structures `J_q(±t)`, and the energy of `v` over `Ω \ Z` is finite and at most `E`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_comp_positiveEndChart
    (ω : SymplecticForm V) {K : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {q : Puncture}
    (hHq : ContDiff ℝ 3 (uncurry (H q))) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJqt : ∀ t x, ω.Tames (Jq t x))
    (hJq : ContDiff ℝ 2 fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ : ∀ s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq t x)
    {D : Set (ℝ × ℝ)} {B : Set V} {t₀ : ℝ} (hD : IsCompact D)
    (hDT : D ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) (hB : IsCompact B) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) →
      (∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedFDeriv (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (equivRealProdCLM.symm z) x I) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      0 ≤ E →
      (∀ k, ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (equivRealProdCLM.symm z) x 1) (fun z x ↦ K (equivRealProdCLM.symm z) x I)
        (u k) z) ≤ ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (positiveEndChart q (z + (R k, 0)))) Ω B) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) y) ∧
        ContDiffOn ℝ 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) B ∧
        TendstoLocallyUniformlyOn (fun n z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) v
          atTop (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn
          (fun n ↦ fderiv ℝ fun z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0))))
          (fderiv ℝ v) atTop (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (Jq (q.endSign * z.2) (v z))
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2) v z
            : ℝ × ℝ →ₗ[ℝ] V)) ∧
        IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          v) (Ω \ ↑Z) ∧
        ∫ z in Ω \ ↑Z, ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w ↦ positiveEndHamiltonian H q w.2) v z ≤ E := by
  -- The cylindrical datum of the positive end is smooth.
  have hKt : ContDiff ℝ 3 (uncurry fun w : ℝ × ℝ ↦ positiveEndHamiltonian H q w.2) :=
    (contDiff_uncurry_positiveEndHamiltonian hHq).comp
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hJq' : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦
      (Jq (q.endSign * p.1.2) p.2).toLinearMap.toContinuousLinearMap :=
    hJq.comp ((contDiff_const.mul (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (J := fun z ↦ Jq (q.endSign * z.2)) isOpen_univ contDiffOn_const
    hKt.contDiffOn hJq'.contDiffOn hD hB (subset_univ _) fun _ _ x _ ↦ hJqt _ x
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huK ↦ ?_⟩
  -- The translated windows lie in the band `(max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end
  -- chart.
  have hΩT (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      z + (R k, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)
  have hvC (k : ℕ) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ u k (positiveEndChart q (z + (R k, 0)))) Ω :=
    (hu k).comp ((contDiff_positiveEndChart q _).comp (contDiff_id.add contDiff_const)).contDiffOn
      fun z hz ↦ positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt (hΩT k z hz).1)
  have h (k : ℕ) := isComplexLinearMap_and_integral_le_comp_positiveEndChart_add ω hKH hH hHd
    hHq hJqt hJ hΩ (hΩT k) ((hu k).of_le (WithTop.coe_le_coe.2 le_top)) (hfl k) hE0 (hE k)
  exact hconv hΩ hΩD hvC (fun k ↦ (h k).1) huK (fun k ↦ (h k).2.1) fun k ↦ (h k).2.2

end TauCeti.SymplecticForm
