/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Manifold

/-!
# Compactness of Floer pairs of pants in a closed manifold

Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed symplectic
manifold, and let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of
period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q` on the three ends of `S = ℂ ∖ {0, 1}`. This
file proves the interior part of Gromov–Floer compactness for solutions `u : S → M` of
`(du - X_K)^{0,1} = 0`, on every compact window of the domain and along every end, with no
condition on where the solutions take their values. The theorems of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Manifold` assume instead that the images
stay in a compact subset of one symplectic chart.

The general compactness theorem in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in the
namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`), applies
once its hypotheses are checked for the pair of pants.

* **The data in the charts of `M`.** The Hamiltonian vector fields of the perturbation, read in the
  chart at any point of `M`, are `C²` on `S` times the chart target
  (`IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt_pairOfPantsPerturbation` in the
  namespace `TauCeti.SmoothTwoForm`), since the family `z ↦ K_z(v)` is `C³` jointly in `z ∈ S`
  and the target point (`TauCeti.Floer.contMDiffAt_uncurry_pairOfPantsPerturbation`). The
  almost complex structures read in the charts are assumed `C²`.
* **The energy bound.** The energy of a solution over any part of `S` is at most its topological
  energy `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` plus `B₀ + B₁ + B_∞`
  (`IsNondegenerate.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le` in the namespace
  `TauCeti.SmoothTwoForm`).
* **Along the ends.** A translated end `vₖ(z) = uₖ(φ'_q(z + (Rₖ, 0)))` solves the cylindrical Floer
  equation of the positive end `q`, with energy at most that of `uₖ`
  (`contMDiffOn_and_isComplexLinearMap_and_integral_le_comp_positiveEndChart_add` in the
  namespace `TauCeti.SmoothTwoForm.IsNondegenerate`), so the same theorem applies to the
  translated ends on a fixed window, with a threshold that does not depend on the heights `Rₖ`.
  When `Rₖ → ∞`, the limits are where the Floer cylinders breaking off at the end `q` are found.

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pairOfPantsPerturbation`: on
  a compact window `D ⊆ S`, a sequence of Floer pairs of pants of topological energy at most `A`
  has a subsequence converging off a finite set `Z` of bubbling points, with
  `#Z * δ ≤ A + B₀ + B₁ + B_∞` for a threshold `δ > 0` depending only on the data and `D`.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_positiveEndChart`: the
  same for the translated ends of Floer pairs of pants of energy at most `E`, on a compact window
  of the positive end chart, with `#Z * δ ≤ E`. The threshold depends only on the data of the end,
  so the perturbations and structures may change along the sequence away from that end.
* `exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le`: on a compact
  part of `S`, the bounds on the pushforwards of the Hamiltonian vector fields of the perturbation
  that the first theorem takes hold for every `C¹` map `e` and `C¹` Hamiltonians `H_q`, since each
  component of the perturbation is `C¹` jointly on `S × M`.

The regularity of the limits, the bubbles at the points of `Z` and the assembly of the limits at the
ends into a broken configuration are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on Floer breaking at the ends.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {e : M → F}

/-- **Floer pairs of pants in a closed manifold converge off finitely many bubbling points.** Let
`ω` be a nondegenerate two-form on a closed manifold `M`, let `K` be the pair-of-pants perturbation
of period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `J(z, x)` be structures on the
tangent spaces of `M`, tamed by `ω` over `S = ℂ ∖ {0, 1}` (read in real coordinates), which are `C²`
read in the chart at every point of `M`. Let `e : M → F` be injective and differentiable, let
`D ⊆ S` be compact, and over `D` let the structures be uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and let the pushforwards through `e` of the Hamiltonian
vector fields of the two components of `K` be at most `L`. There is a threshold `δ > 0` with the
following property. Let `uₖ` be `C³` solutions of `(du - X_K)^{0,1} = 0` on `S` for `J(z, u)`,
whose end loops `t ↦ uₖ(φ_q(±R + i t))` converge pointwise to loops `xₖ(q)` as `R → ∞`, with
integrable energy and area densities and topological energy
`∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ(q)(t)) dt ≤ A`, and let `Ω ⊆ D` be open. Then there are a
subsequence `φ` and a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B₀ + B₁ + B_∞` such that, along `φ`,
every disc about a point of `Z` eventually carries energy at least `δ`, the energy densities are
uniformly bounded on every compact subset of `Ω \ Z`, and the solutions converge on `Ω \ Z` to a
continuous map `v`, locally uniformly after applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hLs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- Each component `z ↦ K_z(w)` of the perturbation is `C³` jointly in `z ∈ S` and the target
  -- point, so its Hamiltonian vector field is `C²` in every chart.
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    he he_inj isOpen_thricePuncturedSphereReal hD hDS hJ
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt_pairOfPantsPerturbation hH hHs 1)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt_pairOfPantsPerturbation hH hHs Complex.I)
    (fun z hz ↦ hJt z (hDS hz)) hc hJc hLs hLt
  refine ⟨δ, hδ, fun Ω u x A hΩ hΩD hu hfl hx hE hA htop ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  -- The energy over `Ω` is at most the topological energy plus `B₀ + B₁ + B_∞`.
  refine hconv hΩ hΩD (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz))
    (fun k ↦ (hE k).mono_set hΩS) fun k ↦ ?_
  linarith [htop k, hω.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu k).of_le (by norm_num)) (hx k) (hE k) (hA k)
    (J := fun z ↦ J z (u k z)) (fun z hz ↦ hJt z hz _) (hfl k) hΩS]

/-- **The translated ends of Floer pairs of pants in a closed manifold converge off finitely many
bubbling points.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `H_q` be a
period-one Hamiltonian which is `C³` on `ℝ × M`, and let `J_q(t, x)` be structures on the tangent
spaces of `M`, tamed by `ω` and `C²` read in the chart at every point of `M`. Let `e : M → F` be
injective and differentiable, with the structures `J_q` uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J_q v)` with `c > 0`, and the pushforwards through `e` of the Hamiltonian
vector fields of the end Hamiltonians `H'_q(t)` at most `L`. Fix a compact window
`D ⊆ (max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end chart. There is a threshold `δ > 0` with
the following property. Let `Kₖ` be perturbations on `ℂ` equal to `H_q(t) dt` beyond
`T₀` on the end `q`, and `Jₖ(z, x)` structures on the tangent spaces of `M`, `z` read in real
coordinates, with `Jₖ(φ_q(±s, t), x) = J_q(t, x)` on the end `q` beyond `T₀`. Let `uₖ` be `C³`
solutions of `(du - X_{Kₖ})^{0,1} = 0` for `Jₖ(z, u)` with energy at most `E ≥ 0` on open sets
`Uₖ` containing the part `s > max T₀ 0` of the positive end chart, such as Floer pairs of pants on
`S = Uₖ`, let `Rₖ ≥ 0` be heights, and let `Ω ⊆ D` be open. Then there are a subsequence `φ` and a
finite set `Z ⊆ Ω` with `#Z * δ ≤ E` such that, along `φ`, for the translated ends
`vₖ(z) = uₖ(φ'_q(z + (Rₖ, 0)))`, every disc about a point of `Z` eventually carries energy at least
`δ` for the cylindrical datum `H'_q dt`, the energy densities are uniformly bounded on every
compact subset of `Ω \ Z`, and the translated ends converge on `Ω \ Z` to a continuous map `v`,
locally uniformly after applying `e` and pointwise in `M`. The threshold depends only on the end
data, so the perturbations and structures may vary along the sequence away from the end `q`, as
they do along a family. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_positiveEndChart
    (hω : ω.IsNondegenerate) {T₀ : ℝ} {q : Puncture} (hH : Periodic (H q) 1)
    (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJq : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α Jq) (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ t x, (hω.symplecticFormAt x).Tames (Jq t x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq t x v))
    (hL : ∀ t x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) x)‖ ≤ L)
    {D : Set (ℝ × ℝ)} {t₀ : ℝ} (hD : IsCompact D)
    (hDT : D ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∃ δ > 0, ∀ ⦃K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ⦄
      ⦃J : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)⦄
      ⦃Ω : Set (ℝ × ℝ)⦄ ⦃U : ℕ → Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      (∀ k w x, T₀ ≤ q.endSign * (q.endCoord w).re →
        K k w x = H q (q.endCoord w).im x • q.endAngularForm w) →
      (∀ k s t x, T₀ ≤ s → J k (endChart q (q.endSign * s, t)) x = Jq t x) →
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) → (∀ k, IsOpen (U k)) →
      (∀ k (ζ : ℝ × ℝ), max T₀ 0 < ζ.1 → positiveEndChart q ζ ∈ U k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) (U k)) →
      (∀ k, ∀ z ∈ U k,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z (u k z))
          (ω.perturbedMFDeriv (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap) →
      0 ≤ E →
      (∀ k, ∫⁻ z in U k, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ ENNReal.ofReal E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn
            (fun n z ↦ e (u (φ n) (positiveEndChart q (z + (R (φ n), 0))))) (e ∘ v) atTop
            (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z,
            Tendsto (fun n ↦ u (φ n) (positiveEndChart q (z + (R (φ n), 0)))) atTop (𝓝 (v z)) := by
  -- In the chart at every point, the structure `J_q(±t)` is `C²`, and the Hamiltonian vector
  -- fields of the components `0` and `H'_q(t)` of the end datum are `C²`.
  have hJ' (α : M) : ContDiffOn ℝ 2
      (almostComplexInChartAt I α fun z : ℝ × ℝ ↦ Jq (q.endSign * z.2))
      (univ ×ˢ (extChartAt I α).target) :=
    ((hJq α).comp ((contDiff_const.mul (contDiff_snd.comp contDiff_fst)).prodMk
      contDiff_snd).contDiffOn (s := univ ×ˢ (extChartAt I α).target)
      fun _ hp ↦ ⟨mem_univ _, hp.2⟩).congr fun p _ ↦
        almostComplexInChartAt_comp _ p
  have hH' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
      (uncurry fun (w : ℝ × ℝ) x ↦ positiveEndHamiltonian H q w.2 x) :=
    (contMDiff_uncurry_positiveEndHamiltonian hHq).comp
      ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ positiveEndHamiltonian H q w.2)
    (J := fun z ↦ Jq (q.endSign * z.2)) he he_inj isOpen_univ hD (subset_univ D) hJ'
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) fun _ _ _ ↦ contMDiffAt_const)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt fun _ _ _ ↦ hH'.contMDiffAt)
    (fun _ _ x ↦ hJt _ x) hc (fun _ _ x v ↦ hJc _ x v)
    (fun _ _ x ↦ by
      simp only [hamiltonianVectorField_const, Pi.zero_apply, map_zero]
      exact norm_zero.trans_le ((norm_nonneg _).trans (hL 0 x)))
    fun w _ x ↦ hL w.2 x
  refine ⟨δ, hδ, fun K J Ω U u R E hKH hJ hΩ hΩD hR hU hUq hu hfl hE0 hE ↦ ?_⟩
  -- The translated ends solve the Floer equation of the end, with energy at most `E`.
  have h (k : ℕ) :=
    contMDiffOn_and_isComplexLinearMap_and_integral_le_comp_positiveEndChart_add hω (hKH k) hH
      hHq (hJ k) (C := univ) (fun t x _ ↦ hJt t x) hΩ hΩD hDT (hR k) (hU k) (hUq k) (hu k)
      (hfl k) hE0 (hE k) fun _ _ ↦ mem_univ _
  exact hconv hΩ hΩD (fun k ↦ (h k).1) (fun k ↦ (h k).2.1) (fun k ↦ (h k).2.2.1)
    fun k ↦ (h k).2.2.2

omit [I.Boundaryless] in
/-- **The Hamiltonian vector fields of the perturbation are bounded on compact parts of `S`.** Let
`M` be compact and let `H_q` be period-one `C¹` Hamiltonians. On a compact part `D` of
`S = ℂ ∖ {0, 1}`, the pushforwards through a `C¹` map `e : M → F` of the Hamiltonian vector fields
of a component `K(v)` of the pair-of-pants perturbation are bounded, uniformly in the target point.
These are the bounds that
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pairOfPantsPerturbation` takes
on its window. -/
theorem exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {D : Set (ℝ × ℝ)} (hD : IsCompact D)
    (hDS : D ⊆ thricePuncturedSphereReal) (v : ℂ) :
    ∃ L, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y v) x)‖ ≤ L :=
  hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le_of_isCompact hD he
    fun _ hz x ↦ contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs (hDS hz) x v

end TauCeti.SmoothTwoForm.IsNondegenerate
