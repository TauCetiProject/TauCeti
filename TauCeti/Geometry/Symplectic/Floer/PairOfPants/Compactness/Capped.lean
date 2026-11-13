/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Capped

/-!
# Compactness of the comparison family over a compact parameter window

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes, and deforms the resulting
problem on the sphere with three poles `0`, `1` and `∞` through the one-parameter family of
perturbation data `K_R = TauCeti.Floer.cappedComparisonPerturbation H R`, `R ≥ 0`: the zero datum
at `R = 0`, and necks of length `R - 1` for `R ≥ 2`. Its moduli spaces are compactified over the
parameter `R`. This file proves the interior part of that compactness for a symplectic vector
space target `(V, ω)` and a compact window of parameters.

For period-one Hamiltonians `H_q` with `|H_q| ≤ B_q`, the Floer energy of a solution of
`(du - X_{K_R})^{0,1} = 0` on the plane chart `ℂ ≅ ℝ × ℝ` of the sphere differs from its
symplectic area `∫ u^* ω` by at most `2 (B₀ + B₁ + B_∞)`, uniformly in `R ≥ 0`
(`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`).
So solutions of symplectic area at most `A` have Floer energy at most `A + 2 (B₀ + B₁ + B_∞)`,
whatever the parameter, and compactness over compact parameter windows
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D` of the plane chart:
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison`.
For a map into a closed symplectic manifold that extends over the sphere, the symplectic area is
the energy `ω(A)` of its class.

The almost complex structures `J_R(z, x)` are any family which is `C²` jointly in `R`, the domain
point and the target point near the compact window, and tamed by `ω` for the parameters of the
window. The regularity of the limit, the bubbles at the points of `Z`, the pole `∞` outside the
plane chart, and the long-neck end `R → ∞` of the family are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J : ℝ → ℝ × ℝ → V → AlmostComplexStructure V}

/-- **Solutions along the comparison family converge off finitely many bubbling points.** Let
`K_R` be the comparison family of the capped three-pole sphere built from period-one `C³`
Hamiltonians `H_q` with `|H_q| ≤ B_q` on a symplectic vector space, read in the real coordinates
`z = (s, t)` of `ℂ`. Let `J_R(z, x)` be `C²` jointly in `R`, `z` and `x` on an open set `W`
containing `C × D × K` for compact `C ⊆ [0, ∞)`, `D ⊆ ℝ × ℝ` and `K ⊆ V`, and tamed by `ω` for
`R ∈ C`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`(du - X_{K_{Rₖ}})^{0,1} = 0` on the plane for `J_{Rₖ}(z, u)`, with `Rₖ ∈ C`, integrable energy
density, symplectic area `∫ ω(∂ₛuₖ, ∂ₜuₖ) ≤ A`, and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there
are a subsequence `φ`, a limit `R₀ ∈ C` of `R_{φ n}`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc
about a point of `Z` eventually carries Floer energy at least `δ`, the differentials are uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {W : Set (ℝ × ((ℝ × ℝ) × V))}
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × ((ℝ × ℝ) × V) ↦
      (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hC₀ : C ⊆ Ici 0) (hD : IsCompact D) (hK : IsCompact K)
    (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W) (hJt : ∀ R ∈ C, ∀ z x, ω.Tames (J R z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, R k ∈ C) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (R k) z (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (R₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ R₀ ∈ C ∧
        Tendsto (fun n ↦ R (φ n)) atTop (𝓝 R₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
    (Kt := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I) hW
    (contDiff_cappedComparisonPerturbation_apply (n := 3) hH hHs 1).contDiffOn
    (contDiff_cappedComparisonPerturbation_apply (n := 3) hH hHs I).contDiffOn hJ hC hD hK hCDKW
    fun R hR z _ x _ ↦ hJt R hR z x
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hRC hu hfl hE hA huK ↦ hconv hΩ hΩD hRC
    (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK (fun k ↦ (hE k).integrableOn)
    fun k ↦ ?_⟩
  -- The energy over `Ω` is at most the energy over the plane, which exceeds the symplectic area
  -- by at most `2 (B₀ + B₁ + B_∞)`.
  have hint := (setIntegral_le_integral (s := Ω) (hE k) (Eventually.of_forall fun z ↦
    ω.floerEnergyDensity_nonneg (hJt _ (hRC k) z _) (hfl k z))).trans
    (sub_le_iff_le_add'.1 (le_of_abs_le
      (ω.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le hH
        (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀ (hRC k)) ((hu k).of_le (by norm_num))
        (hE k))))
  linarith [hA k]

end TauCeti.SymplecticForm
