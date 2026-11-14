/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action

/-!
# Compactness of PSS planes with bounded end action

The Piunikhin–Salamon–Schwarz maps count solutions of the Floer equation `(du - X_K)^{0,1} = 0`
on the complex plane, for the perturbation `K = TauCeti.Floer.PSSPlane.perturbation` of a PSS
plane `p` built from a period-one Hamiltonian `H`. Here the target is a symplectic vector space
`(V, ω)`: a finite-dimensional real inner product space `V` with a linear symplectic form `ω`. The
value of the negative plane count on the fundamental cycle is the unit of the pair-of-pants
product, and both planes are the caps glued to the ends of the pair of pants in the comparison
with the quantum product. Counting them requires
compactness of their moduli spaces below every action level.

Let `ε = ±1` be the sign of the end of `p` at `∞`, and let `u` be a `C²` solution with `ω`-tame
almost complex structures whose end loops `ℓ_R(t) = u(φ(ε R + i t))` have actions converging to
`a` as `R → ∞`. If `|H| ≤ B`, the energy of `u` over the whole plane is at most `ε a + B`
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_le`). So a sequence of
such solutions with `ε aₖ` bounded above has uniformly bounded energy. If moreover `H` is `C³`,
the solutions `uₖ` are `C³`, and their almost complex structures come from a single `C²` family
`J(z, x)` of `ω`-tame structures on `(ℝ × ℝ) × V`, then the compactness theorem for Floer
solutions of bounded energy
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`) applies
on every compact window of the plane. For the negative plane, whose end is an output, the
hypothesis bounds the end action `aₖ` from below; for the positive plane, whose end is an input,
it bounds it from above.

The main result
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation` in
`TauCeti.SymplecticForm`) fixes compact sets `D ⊆ ℝ × ℝ ≃ ℂ` and `C ⊆ V`, and gives a threshold
`δ > 0`. For every open `Ω ⊆ D` and every sequence of solutions with image of `Ω` in `C` and
`ε aₖ ≤ A`, a subsequence converges locally uniformly on `Ω` off a finite set `Z` of bubbling
points with `#Z * δ ≤ A + B`, and every disc about a point of `Z` eventually carries energy at
least `δ`.
The window `D` may contain the pole disc, where the perturbation vanishes and the equation is the
Cauchy–Riemann equation for `J`. This is the interior part of Gromov–Floer compactness for PSS
planes, in the form proved for the pair of pants in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness`: the regularity of the limit, the
bubbles at the points of `Z`, breaking along the end, and symplectic manifold targets are not
treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points), Section 8.1 (the energy of solutions of the
  inhomogeneous equation) and Chapter 12 (the PSS isomorphism).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : ℝ → V → ℝ}

/-- **PSS planes with bounded end action converge off finitely many bubbling points.** Let `K` be
the perturbation of a PSS plane `p`, with end sign `ε`, built from a period-one `C³` Hamiltonian
`H` with `|H| ≤ B` on a symplectic vector space `(V, ω)`, that is, a finite-dimensional real inner
product space `V` with a linear symplectic form `ω`. Let `J(z, x)` be a `C²` family of `ω`-tame
structures on `(ℝ × ℝ) × V`, where the plane is read in real coordinates. Fix compact sets
`D ⊆ ℝ × ℝ` and `C ⊆ V`. There is a threshold `δ > 0` with the following property. Let `uₖ` be
`C³` solutions of `(du - X_K)^{0,1} = 0` on the plane for `J(z, u)`, whose end loops have
limiting actions `aₖ` with `ε aₖ ≤ A`, and with `uₖ(Ω) ⊆ C` for an open `Ω ⊆ D`. Then there
are a subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B`, and a continuous
`v : Ω \ Z → C` such that along `φ` every disc about a point of `Z` eventually carries energy at
least `δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation
    (ω : SymplecticForm V) (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    {B : ℝ} (hB : ∀ t x, |H t x| ≤ B) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap))
    (hJt : ∀ z x, ω.Tames (J z x)) {D : Set (ℝ × ℝ)} {C : Set V} (hD : IsCompact D)
    (hC : IsCompact C) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u k (equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * I))))) atTop (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) →
      (∀ k, MapsTo (u k) Ω C) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + B ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ L, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hK' (v : ℂ) :
      ContDiff ℝ 3 (uncurry fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x v) :=
    contDiff_uncurry_perturbation hH hHs v
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    isOpen_univ (hK' 1).contDiffOn (hK' I).contDiffOn hJ.contDiffOn hD hC (subset_univ _)
    fun z _ x _ ↦ hJt z x
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA huK ↦ ?_⟩
  set Ks : ℝ × ℝ → V → ℝ := fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → V → ℝ := fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hHs1 : ContDiff ℝ 1 (uncurry H) := hHs.of_le (by norm_num)
  have hf0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z :=
    ω.floerEnergyDensity_nonneg (hJt z _) (hfl k z)
  -- The action bound `-B ≤ ε a` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + B := by
    have h := neg_le_endSign_mul_of_tendsto_hamiltonianAction_pssPlanePerturbation
      (J := fun z ↦ J z (u 0 z)) ω hH hHs1 hB ((hu 0).of_le (by norm_num)) (fun z ↦ hJt z _)
      (hfl 0) (ha 0)
    linarith [hA 0]
  -- The energy over `Ω` is at most the energy over the plane, hence at most `A + B`.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z) ≤
      ENNReal.ofReal (A + B) :=
    setLIntegral_le_lintegral _ _ |>.trans <|
      (lintegral_floerEnergyDensity_pssPlanePerturbation_le (J := fun z ↦ J z (u k z)) ω hH hHs1
        hB ((hu k).of_le (by norm_num)) (fun z ↦ hJt z _) (hfl k) (ha k)).trans
        (ENNReal.ofReal_le_ofReal (by linarith [hA k]))
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_univ ((hu k).of_le (by norm_num)).contDiffOn
      ((hK' 1).of_le (by norm_num)).contDiffOn ((hK' I).of_le (by norm_num)).contDiffOn).mono
        (subset_univ Ω)).aestronglyMeasurable hΩm,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩm fun z _ ↦ hf0 k z)).2
        ((hlin k).trans_lt ENNReal.ofReal_lt_top)⟩
  exact hconv hΩ hΩD (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK hint fun k ↦ by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hΩm fun z _ ↦ hf0 k z)
      (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hE0 (hlin k)

end TauCeti.SymplecticForm
