/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.Plane.Compactness.End
import TauCeti.Order.Interval.Set.Prod

/-!
# Compactness of PSS planes in a closed manifold

Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed symplectic
manifold, and let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`
with end sign `ε`, given by a period-one `C³` Hamiltonian `H` with `|H| ≤ B`. The
Piunikhin–Salamon–Schwarz maps, and the unit cycle of the pair-of-pants product, count solutions
`u : ℂ → M` of `(du - X_K)^{0,1} = 0`. This file proves the interior part of Gromov–Floer
compactness for these solutions, on every compact window of the plane and along the end, with no
condition on where the solutions take their values. The theorems of
`TauCeti.Geometry.Symplectic.Floer.Plane.Compactness.Basic` and
`TauCeti.Geometry.Symplectic.Floer.Plane.Compactness.End` assume instead that the images stay in a
compact subset of one symplectic chart.

The general compactness theorem in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in the
namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`), applies
once its hypotheses are checked for the plane.

* **The data in the charts of `M`.** The components `z ↦ K_z(v)` of the perturbation are `C³`
  jointly in the point `z` of the plane and the target point
  (`TauCeti.Floer.PSSPlane.contMDiff_uncurry_perturbation`), so their Hamiltonian vector fields
  read in the chart at any point of `M` are `C²`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`). The almost
  complex structures read in the charts are assumed `C²`.
* **The energy bound.** If the capped actions of the end loops of `u`, each capped by the disc of
  the plane that it bounds, converge to `a` with `ε a ≤ A`, then the energy of `u` is at most
  `A + B` (`IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_le` in the
  namespace `TauCeti.SmoothTwoForm`), and `A + B ≥ 0`
  (`IsNondegenerate.neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation`).
* **Along the end.** Read in the end coordinates `ℓ(s, t) = exp (2π (s + i t))` of the positive
  plane, a translated end `vₖ(z) = uₖ(ℓ(z + (Rₖ, 0)))` solves the cylindrical Floer equation for
  the datum `ε H(ε t) dt`, with energy at most that of `uₖ`
  (`IsNondegenerate.contMDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add`
  in the namespace `TauCeti.SmoothTwoForm`), so the same theorem applies to the translated ends on
  a fixed window, with a threshold that does not depend on the heights `Rₖ`. When `Rₖ → ∞`, the
  limits are where the Floer cylinders breaking off at the end are found.

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pssPlanePerturbation`: on a
  compact window `D` of the plane, a sequence of solutions whose limiting capped end actions `aₖ`
  satisfy `ε aₖ ≤ A` has a subsequence converging off a finite set `Z` of bubbling points, with
  `#Z * δ ≤ A + B` for a threshold `δ > 0` depending only on the data and `D`.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_realChart_positive_add`:
  the same for the translated ends of solutions of energy at most `E`, on a compact window of the
  end coordinates, with `#Z * δ ≤ E`.

The regularity of the limits, the bubbles at the points of `Z` and the assembly of the limits at the
end into a broken configuration are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points), Section 8.1 (the energy of solutions of the inhomogeneous
  equation) and Chapter 12 (the PSS isomorphism).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on Floer breaking at the ends.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.Complex (realChart)
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer Floer.PSSPlane

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {e : M → F}

/-- **PSS planes in a closed manifold converge off finitely many bubbling points.** Let `ω` be a
nondegenerate two-form on a closed manifold `M`, let `K` be the perturbation of a PSS plane `p`
with end sign `ε` given by a period-one `C³` Hamiltonian `H` with `|H| ≤ B`, and let `J(z, x)` be
structures on the tangent spaces of `M`, tamed by `ω`. Let `D` be a compact window of the plane,
in real coordinates, contained in an open set `U` on which the structures are `C²` read in the chart
at every point of `M`. Let `e : M → F` be injective and differentiable, and over `D` let the
structures be uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and let the
pushforwards through `e` of the Hamiltonian vector fields of the two components of `K` be at most
`L`. There is a threshold `δ > 0` with the
following property. Let `uₖ` be `C³` solutions of `(du - X_K)^{0,1} = 0` on the plane for
`J(z, u)`, whose end loops along the circles `‖w‖ = exp (2πR)`, each capped by the disc
`uₖ ∘ endDisc R` of the plane that it bounds, have capped actions converging to `aₖ` as `R → ∞`,
with `ε aₖ ≤ A`, and let `Ω ⊆ D` be open. Then there are a subsequence `φ` and a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A + B` such that, along `φ`, every disc about a point of `Z` eventually
carries energy at least `δ`, the energy densities are uniformly bounded on every compact subset of
`Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous map `v`, locally uniformly after
applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {U D : Set (ℝ × ℝ)} (hU : IsOpen U) (hD : IsCompact D)
    (hDU : D ⊆ U)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J) (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hLs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ p.perturbation H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ p.perturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃a : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k)
          z).toLinearMap) →
      (∀ k, Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u k (equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u k ∘ p.endDisc R)) atTop
          (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + B ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hHs₁ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H) := hHs.of_le (by norm_num)
  -- Each component `z ↦ K_z(w)` of the perturbation is `C³` jointly in `z` and the target point,
  -- so its Hamiltonian vector field is `C²` in every chart.
  have hK (w : ℂ) := contMDiff_uncurry_perturbation (p := p) hH hHs w
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    he he_inj hU hD hDU hJ
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) fun _ _ _ ↦ (hK 1).contMDiffAt)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) fun _ _ _ ↦ (hK Complex.I).contMDiffAt)
    (fun z _ ↦ hJt z) hc hJc hLs hLt
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA ↦ ?_⟩
  -- The energy over the plane is at most `ε aₖ + B ≤ A + B`, and `-B ≤ ε a₀` makes `A + B ≥ 0`.
  have hE0 : 0 ≤ A + B := by
    linarith [hA 0, hω.neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation hH
      hHs₁ hB ((hu 0).of_le (by norm_num)) (fun z ↦ hJt z _) (hfl 0) (ha 0)]
  -- The Hamiltonian vector fields of the two components are continuous, so the energy densities
  -- are integrable over `Ω`, with integral at most `A + B`.
  have hX (w : ℂ) : ContinuousOn (fun q : (ℝ × ℝ) × M ↦ (⟨q.2, ω.hamiltonianVectorField
      (fun y ↦ p.perturbation H (equivRealProdCLM.symm q.1) y w) q.2⟩ : TangentBundle I M))
      (univ ×ˢ univ) :=
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
      ((hK w).of_le (by norm_num))).continuous.continuousOn
  have h (k : ℕ) := ω.integrableOn_and_setIntegral_floerEnergyDensity_le isOpen_univ
    hΩ.measurableSet (subset_univ Ω) ((hu k).of_le (by norm_num)).contMDiffOn (hX 1) (hX Complex.I)
    (fun z _ ↦ floerEnergyDensity_nonneg hω (hJt z _) (hfl k z)) hE0
    ((setLIntegral_univ _).trans_le
      ((hω.lintegral_floerEnergyDensity_pssPlanePerturbation_le hH hHs₁ hB
        ((hu k).of_le (by norm_num)) (fun z ↦ hJt z _) (hfl k) (ha k)).trans
        (ENNReal.ofReal_le_ofReal (by linarith [hA k]))))
  exact hconv hΩ hΩD (fun k ↦ (hu k).contMDiffOn) (fun k z _ ↦ hfl k z) (fun k ↦ (h k).1)
    fun k ↦ (h k).2

/-- **The translated ends of PSS planes in a closed manifold converge off finitely many bubbling
points.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `p` be a PSS plane with
end sign `ε`, `H` a period-one Hamiltonian which is `C³` on `ℝ × M`, and `J(z, x)` structures on
the tangent spaces of `M` which are cylindrical far out on the end, `J(ℓ(s, t), x) = J_∞(t, x)` for
`s ≥ T₀`, where `ℓ` is the end lift of the positive plane in real coordinates, for structures
`J_∞(t, x)` tamed by `ω` which are `C²` read in the chart at every point of `M`. Let `e : M → F` be
injective and differentiable, with the structures `J_∞` uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J_∞ v)` with `c > 0`, and the pushforwards through `e` of the Hamiltonian vector
fields of the end Hamiltonians `ε H(ε t)` at most `L`. Fix a compact window
`D ⊆ (max T₀ 2, ∞) × (t₀, t₀ + 1)` of the end coordinates. There is a threshold `δ > 0` with the
following property. Let `uₖ` be `C³` solutions on the plane of the Floer equation for `J(z, u)` and
the perturbation of `p` given by `H`, with energy at most `E ≥ 0`, let `Rₖ ≥ 0` be heights, and let
`Ω ⊆ D` be open. Then there are a subsequence `φ` and a finite set `Z ⊆ Ω` with `#Z * δ ≤ E` such
that, along `φ`, for the translated ends `vₖ(z) = uₖ(ℓ(z + (Rₖ, 0)))`, every disc about a point of
`Z` eventually carries energy at least `δ` for the cylindrical datum `ε H(ε t) dt`, the energy
densities are uniformly bounded on every compact subset of `Ω \ Z`, and the translated ends
converge on `Ω \ Z` to a continuous map `v`, locally uniformly after applying `e` and pointwise in
`M`. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_realChart_positive_add
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {T₀ : ℝ}
    {Jend : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s t x, T₀ ≤ s → J (realChart positive.cylindricalEndLift (s, t)) x = Jend t x)
    (hJend : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α Jend)
      (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ t x, (hω.symplecticFormAt x).Tames (Jend t x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jend t x v))
    (hL : ∀ t x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ p.endSign * H (p.endSign * t) y) x)‖ ≤ L)
    {D : Set (ℝ × ℝ)} {t₀ : ℝ} (hD : IsCompact D)
    (hDT : D ⊆ Ioi (max T₀ 2) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k)
          z).toLinearMap) →
      0 ≤ E →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤
          ENNReal.ofReal E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x)
          (fun z ↦ u (φ n) (realChart positive.cylindricalEndLift (z + (R (φ n), 0)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w x ↦ p.endSign * H (p.endSign * w.2) x)
          (fun z ↦ u (φ n) (realChart positive.cylindricalEndLift (z + (R (φ n), 0)))) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn
            (fun n z ↦ e (u (φ n) (realChart positive.cylindricalEndLift (z + (R (φ n), 0)))))
            (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto
            (fun n ↦ u (φ n) (realChart positive.cylindricalEndLift (z + (R (φ n), 0)))) atTop
            (𝓝 (v z)) := by
  -- In the chart at every point, the structure `J_∞(t)` is `C²`, and the Hamiltonian vector fields
  -- of the components `0` and `ε H(ε t)` of the end datum are `C²`.
  have hJ' (α : M) : ContDiffOn ℝ 2 (almostComplexInChartAt I α fun z : ℝ × ℝ ↦ Jend z.2)
      (univ ×ˢ (extChartAt I α).target) :=
    ((hJend α).comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (s := univ ×ˢ (extChartAt I α).target) fun _ hq ↦ ⟨mem_univ _, hq.2⟩).congr fun q _ ↦
        almostComplexInChartAt_comp _ q
  have hHs' := p.contMDiff_uncurry_endSign_mul hHs
  have hH' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
      (uncurry fun (w : ℝ × ℝ) x ↦ p.endSign * H (p.endSign * w.2) x) :=
    hHs'.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := fun w x ↦ p.endSign * H (p.endSign * w.2) x)
    (J := fun z ↦ Jend z.2) he he_inj isOpen_univ hD (subset_univ D) hJ'
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) fun _ _ _ ↦ contMDiffAt_const)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt fun _ _ _ ↦ hH'.contMDiffAt)
    (fun _ _ x ↦ hJt _ x) hc (fun _ _ x v ↦ hJc _ x v)
    (fun _ _ x ↦ by
      simp only [hamiltonianVectorField_const, Pi.zero_apply, map_zero]
      exact norm_zero.trans_le ((norm_nonneg _).trans (hL 0 x)))
    fun w _ x ↦ hL w.2 x
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE ↦ ?_⟩
  rw [perturbation_eq_positive p H] at hfl hE
  -- The translated windows lie in the band `(max T₀ 2, ∞) × (t₀, t₀ + 1)` of the end, where the
  -- translated ends solve the Floer equation of the end, with energy at most `E`.
  have h (k : ℕ) :=
    contMDiff_and_isComplexLinearMap_and_integral_le_comp_realChart_positive_add hω
      (p.periodic_endSign_mul hH) hHs' hJ (C := univ) (fun _ _ x _ ↦ hJt _ x) hΩ
      (fun z hz ↦ add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)) (hu k) (hfl k) hE0 (hE k)
      (mapsTo_univ _ _)
  exact hconv hΩ hΩD (fun k ↦ (h k).1.contMDiffOn) (fun k ↦ (h k).2.1) (fun k ↦ (h k).2.2.1)
    fun k ↦ (h k).2.2.2

end TauCeti.SmoothTwoForm.IsNondegenerate
