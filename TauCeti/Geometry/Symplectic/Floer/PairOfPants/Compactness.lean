/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action

/-!
# Compactness of pairs of pants with bounded end actions

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
`C³` Hamiltonians `H_q` with `|H_q| ≤ B_q` on the three ends of `S = ℂ ∖ {0, 1}`, with values in a
symplectic vector space `(V, ω)`, and let `J(z, x)` be a `C²` family of `ω`-tame almost complex
structures on `S × V`. A Floer solution `u` on `S` whose end loops have limiting actions `a_q`
has energy at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_le`). So a sequence
of such solutions whose action differences `a_0 + a_1 - a_∞` are bounded above has uniformly
bounded energy, and the compactness theorem for Floer solutions of bounded energy
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`) applies
on every compact window of `S`.

The main result fixes compact sets `D ⊆ S` and `K ⊆ V`, and gives a threshold `δ > 0`. For every
open `Ω ⊆ D` and every sequence of solutions with image of `Ω` in `K` and action differences at
most `A`, a subsequence converges locally uniformly on `Ω` off a finite set `Z` of bubbling points
with `#Z * δ ≤ A + B_0 + B_1 + B_∞`, and every disc about a point of `Z` eventually carries energy
at least `δ`. This is the interior part of Gromov–Floer compactness for the pair of pants: the
regularity of the limit, the bubbles at the points of `Z`, and breaking along the three ends are
not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **Floer pairs of pants with bounded end actions converge off finitely many bubbling points.**
Let `K` be the pair-of-pants perturbation of period-one `C³` Hamiltonians `H_q` with
`|H_q| ≤ B_q`, and let `J(z, x)` be a `C²` family of `ω`-tame structures on `S × V`, where
`S = ℂ ∖ {0, 1}` is read in real coordinates. Fix compact sets `D ⊆ S` and `K ⊆ V`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`(du - X_K)^{0,1} = 0` on `S` for `J(z, u)`, with limiting end actions `aₖ(q)` satisfying
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ A`, and with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a
subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B_0 + B_1 + B_∞`, and a continuous
`v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries energy at
least `δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J z x))
    {D : Set (ℝ × ℝ)} {K : Set V} (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal)
    (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hS : IsOpen (thricePuncturedSphereReal ×ˢ (univ : Set V)) :=
    isOpen_thricePuncturedSphereReal.prod isOpen_univ
  have hK' {n : ℕ∞} (hn : (n : WithTop ℕ∞) ≤ 3) (v : ℂ) : ContDiffOn ℝ n
      (uncurry fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    exact (contDiffAt_uncurry_pairOfPantsPerturbation hH (fun q ↦ (hHs q).of_le hn) hz x
      v).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hS
    (hK' (by norm_num) 1) (hK' (by norm_num) I) hJ hD hK (prod_mono hDS (subset_univ K))
    fun z hz x _ ↦ hJt z (hDS hz) x
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA huK ↦ ?_⟩
  set Ks : ℝ × ℝ → V → ℝ := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → V → ℝ := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  -- The energy over `Ω` is at most the energy over `S`, hence at most `A + B_0 + B_1 + B_∞`.
  have hf0 (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity Ks Kt (u k) z :=
    ω.floerEnergyDensity_nonneg (hJt z hz _) (hfl k z hz)
  -- The action bound `a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + ∑ q, B q := by
    have h := le_add_add_sum_of_tendsto_hamiltonianAction ω hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu 0).of_le (by norm_num))
      (fun z hz ↦ hJt z hz _) (hfl 0) (ha 0)
    linarith [hA 0]
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z) ≤
      ENNReal.ofReal (A + ∑ q, B q) := by
    refine (lintegral_mono_set hΩS).trans <|
      (lintegral_floerEnergyDensity_pairOfPantsPerturbation_le ω hH
        (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu k).of_le (by norm_num))
        (fun z hz ↦ hJt z hz _) (hfl k) (ha k)).trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [Puncture.sum_univ, Puncture.endSign_zero, Puncture.endSign_one,
      Puncture.endSign_inf]
    linarith [hA k]
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal
      ((hu k).of_le (by norm_num)) (hK' (by norm_num) 1) (hK' (by norm_num) I)).mono
        hΩS).aestronglyMeasurable hΩm,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩm fun z hz ↦ hf0 k (hΩS hz))).2
        ((hlin k).trans_lt ENNReal.ofReal_lt_top)⟩
  exact hconv hΩ hΩD (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK hint
    fun k ↦ by
      rw [integral_eq_lintegral_of_nonneg_ae
        (ae_restrict_of_forall_mem hΩm fun z hz ↦ hf0 k (hΩS hz))
        (hint k).aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hE0 (hlin k)

end TauCeti.SymplecticForm
