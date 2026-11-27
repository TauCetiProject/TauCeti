/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Infinity
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Capped
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Compactness of the capped comparison family

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes. The result is a sphere
with three poles `0`, `1` and `∞`, carrying the one-parameter family of Hamiltonian data
`K_R = TauCeti.Floer.cappedComparisonPerturbation H R` and of almost complex structures
`J_R = TauCeti.Floer.cappedComparisonAlmostComplex h₀ J hJ R`, for `R ≥ 0`. At `R = 0` the
problem is the unperturbed one for the domain-independent compatible structure `J₀`; as `R → ∞`
three necks of length `R - 1` grow along the ends.

This file proves the interior part of Gromov–Floer compactness for this family over a compact
window of parameters `C ⊆ [0, ∞)`, for a symplectic vector space target `(V, ω)`, in the plane
chart `ℂ ≅ ℝ × ℝ` of the complement of the pole `∞`. The datum `K_R` vanishes and `J_R` is `J₀`
near the poles `0` and `1`, so these are ordinary points of the chart, at which a solution is
`J₀`-holomorphic.

The input is the energy identity of the family
(`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`):
for `|H_q| ≤ B_q` and every `R ≥ 0`, the Floer energy of a map differs from its symplectic area
`∫ ω(∂ₛu, ∂ₜu)` by at most `2 (B₀ + B₁ + B_∞)`. For maps extending to the sphere in a class `A`,
the area is `ω(A)`. So solutions whose areas are bounded by `A`, for instance the solutions in a
fixed class, have Floer energy at most `A + 2 (B₀ + B₁ + B_∞)` for every member of the family.
The data `K_R` and `J_R` are smooth jointly in `R` and in the domain and target points
(`TauCeti.Floer.contMDiff_cappedComparisonPerturbation`,
`TauCeti.Floer.contMDiff_cappedComparisonAlmostComplex`), and `J_R` is tamed by `ω`
everywhere. Compactness over a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
then applies on every compact window `D` of the plane chart.

The main result, in the namespace `TauCeti.SymplecticForm`,
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison`)
gives a threshold `δ > 0` such that every sequence of solutions for parameters `Rₖ ∈ C`, with
areas at most `A` and images of an open `Ω ⊆ D` in a compact `K ⊆ V`, has a subsequence whose
parameters converge to some `R₀ ∈ C` and which converges locally uniformly on `Ω` off a finite set
`Z` of bubbling points, with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`.

**The pole `∞`.** The plane chart misses the pole `∞`, which is covered by the chart `y ↦ y⁻¹`.
Outside a disc whose radius depends only on a bound for the neck lengths over `C`, the datum `K_R`
vanishes and `J_R` is `J₀` (`TauCeti.Floer.cappedPerturbation_eq_zero_of_lt_norm`,
`TauCeti.Floer.cappedAlmostComplex_eq_base_of_lt_norm`), so the solutions are `J₀`-holomorphic
there and their area outside the disc is at most their energy
(`exists_pos_forall_isComplexLinearMap_and_setIntegral_le_cappedComparison`). The compactness
theorem at infinity of `TauCeti.Geometry.Symplectic.Floer.Compactness.Infinity` then applies
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_inv`): there are
a radius `ρ > 0` and a threshold `δ > 0` such that, for every sequence of solutions as above whose
expressions `wₖ(y) = uₖ(y⁻¹)` in the chart at `∞` are `C³` on an open `Ω ⊆ {‖y‖ < ρ}` with values
in a compact `K`, a subsequence of the `wₖ` converges locally uniformly on `Ω` off a finite set
`Z` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, the pole `0` of this chart included. Together with the
plane chart this covers the whole three-pole sphere.

The `C³` regularity of `wₖ` at the pole is the removal of the singularity of `uₖ` at `∞`. When the
inner product of `V` is the metric `⟪v, w⟫ = ω(v, J₀ w)` of `J₀` and the solutions take values in
`K` outside the disc of radius `ρ⁻¹`, it is a consequence rather than a hypothesis
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_update_inv`):
each `uₖ` has a limit `qₖ ∈ K` at `∞`, the expression `wₖ` filled with `qₖ` at the pole is smooth
on the disc `‖y‖ < ρ`, and these filled maps have a subsequence converging as above. The regularity
of the limit and the bubbles at the points of `Z` are not treated here. Interior compactness at
the long-neck end `R → ∞`, on the pair of pants and the caps of the PSS planes, is in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.LongNeck`.

**Manifold targets.** For a target manifold `M` with a nondegenerate two-form `ω`, such as a
closed symplectic manifold, the family is built from the structures
`TauCeti.SmoothTwoForm.Compatible.cappedComparisonAlmostComplex h₀ J hJ R` on the tangent bundle,
and the energy identity of the family (in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`,
`abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`) gives the same energy bound
in terms of the symplectic area `∫ u^* ω`. The compactness theorem over a compact parameter window
in a symplectic chart `φ : M ⊇ U → V`, such as a Darboux chart (in the same namespace,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`), then applies to
solutions whose images of `Ω` stay in a compact subset `K` of the chart source (in the same
namespace,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison`). The
Hamiltonians read in the chart, `K_R(z, φ⁻¹ y)`, are `C³` in `(R, z, y)` by the smoothness of the
family; the structures read in the chart are supplied, as for fixed data, by any family `J'_R`
with `dφ_x ∘ J_R(z, x) = J'_R(z, φ x) ∘ dφ_x` that is `C²` in `(R, z, y)` on an open set
containing `C × D × φ(K)`. The limit is read in `M`: the coordinate maps converge locally
uniformly off the bubbling points, and the maps themselves converge pointwise to a continuous
limit with values in `K`.

**Closed manifolds.** When `M` is closed, no chart condition is needed. Sizes in `M` are measured
through an injective differentiable map `e : M → F`, such as the Whitney embedding, and the
compactness theorem in a closed manifold over a compact parameter window (in the namespace
`TauCeti.SmoothTwoForm`,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset`)
applies to the family: the Hamiltonian vector fields of `K_R`, read in the charts of `M`, are `C²`
jointly in `(R, z)` and the chart coordinate
(`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`), and the
structures read in the charts are assumed `C²`, as for a single datum. The result (in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison`)
gives, for every sequence of solutions with parameters in a compact window `C ⊆ [0, ∞)` and areas
at most `A`, on every open `Ω` of a compact window of the plane chart, a subsequence whose
parameters converge in `C` and which converges off a finite set `Z` of bubbling points with
`#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, locally uniformly after applying `e` and pointwise in `M`, with
no condition on where the solutions take their values. For the structures of the family built
from period-one `C²` end structures this regularity holds over the whole plane chart, the poles
`0` and `1` included, since the family is smooth jointly in the parameter, the domain point and
the target point (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappedComparisonAlmostComplex`).
The same conclusion therefore holds with no regularity hypothesis on the structures (in the
namespace `TauCeti.SmoothTwoForm.Compatible`,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison`).
Near the pole `∞` the data are standard, and
the compactness theorem at infinity in a closed manifold (in the namespace `TauCeti.SmoothTwoForm`,
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_inv`) gives
the same conclusion in the chart `y ↦ y⁻¹`, the pole included
(`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_inv`, in
the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). Together the two charts cover the whole
three-pole sphere, for every member of the family with parameter in `C`. Removal of singularities
is not proved here for manifold targets, so the `C³` regularity of the maps at the pole `∞`
remains a hypothesis, and the bubbles at the points of `Z` and the regularity of the limit are not
treated.

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
open scoped Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → V → AlmostComplexStructure V}

/-- **Solutions of the capped comparison family converge off finitely many bubbling points.** Let
`H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let
`J_q(t, x)` be period-one `C²` families of `ω`-tame structures on the three ends. Fix a compact
window `C ⊆ [0, ∞)` of parameters and compact sets `D ⊆ ℝ × ℝ` and `K ⊆ V`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the
three-pole sphere solving the Floer equation `(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures
`J_{Rₖ}(z, u)` of the comparison family, with `Rₖ ∈ C`, integrable energy density, symplectic area
`∫ ω(∂ₛuₖ, ∂ₜuₖ) ≤ A`, and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence `φ`, a
limit `R₀ ∈ C` of `R_{φ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a
continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries
Floer energy at least `δ`, the differentials are uniformly bounded on every compact subset of
`Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hC₀ : C ⊆ Ici 0)
    (hD : IsCompact D) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, R k ∈ C) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
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
  -- The data of the family, read in the plane chart, are jointly smooth in `(R, z, x)`: they are
  -- the smooth data on `ℂ × (ℝ × V)` composed with `(R, z, x) ↦ (z, (R, x))`.
  have hg {n : WithTop ℕ∞} : ContMDiff 𝓘(ℝ, ℝ × ((ℝ × ℝ) × V))
      (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V))) n
      fun q : ℝ × ((ℝ × ℝ) × V) ↦ (equivRealProdCLM.symm q.2.1, (q.1, q.2.2)) :=
    (equivRealProdCLM.symm.contDiff.comp (contDiff_fst.comp contDiff_snd)).contMDiff.prodMk
      (contDiff_fst.contMDiff.prodMk (contDiff_snd.comp contDiff_snd).contMDiff)
  have hK' (v : ℂ) : ContDiffOn ℝ 3 (fun q : ℝ × ((ℝ × ℝ) × V) ↦
      cappedComparisonPerturbation H q.1 (equivRealProdCLM.symm q.2.1) q.2.2 v) univ :=
    (contDiff_cappedComparisonPerturbation_apply (n := 3) hH hHs v).contDiffOn
  have hJ' : ContDiffOn ℝ 2 (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (cappedComparisonAlmostComplex h₀ J hJ
      q.1 (equivRealProdCLM.symm q.2.1) q.2.2).toLinearMap.toContinuousLinearMap) univ :=
    ((contMDiff_cappedComparisonAlmostComplex h₀ hJp
      fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hJs q).contMDiff).comp hg
      ).contDiff.contDiffOn
  have hJt (R : ℝ) (w : ℂ) (x : V) : ω.Tames (cappedComparisonAlmostComplex h₀ J hJ R w x) := by
    rw [cappedComparisonAlmostComplex_def]
    exact tames_cappedAlmostComplex h₀ _ _ w x
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
    (Kt := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I)
    (J := fun R z x ↦ cappedComparisonAlmostComplex h₀ J hJ R (equivRealProdCLM.symm z) x)
    isOpen_univ (hK' 1) (hK' I) hJ' hC hD hK (subset_univ _) fun R _ z _ x _ ↦ hJt R _ x
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hRC hu hfl huK hint harea ↦ ?_⟩
  -- The Floer energy over `Ω` is at most the energy over the plane, which exceeds the area by at
  -- most `2 (B₀ + B₁ + B_∞)`.
  have hE (k : ℕ) :=
    ω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le h₀ hJ hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀ (hRC k)) ((hu k).of_le (by norm_num)) (hfl k)
      (hint k) (harea k) Ω
  exact hconv hΩ hΩD hRC (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK
    (fun k ↦ (hint k).integrableOn) hE

/-- **Solutions of the capped comparison family near the pole `∞`.** Let `H_q` be period-one `C¹`
Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible and let `J_q(t, x)` be `ω`-tame end
structures. Fix a compact window `C ⊆ [0, ∞)` of parameters. There is a radius `T > 0` with the
following property. Let `u` be a `C¹` map of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere
solving the Floer equation `(du - X_{K_R})^{0,1} = 0` for the structures `J_R(z, u)` of the
comparison family, with `R ∈ C`, integrable energy density and symplectic area
`∫ ω(∂ₛu, ∂ₜu) ≤ A`. Then outside the disc of radius `T`, in complex coordinates, `u` is
`J₀`-holomorphic, and its area density is integrable there, with integral at most
`A + 2 (B₀ + B₁ + B_∞)`. -/
theorem exists_pos_forall_isComplexLinearMap_and_setIntegral_le_cappedComparison
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {C : Set ℝ} (hC : IsCompact C)
    (hC₀ : C ⊆ Ici 0) :
    ∃ T > 0, ∀ ⦃R : ℝ⦄ ⦃u : ℝ × ℝ → V⦄ ⦃A : ℝ⦄, R ∈ C → ContDiff ℝ 1 u →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ R (equivRealProdCLM.symm z) (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) →
      Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I) u) →
      ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) ≤ A →
      (∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, IsComplexLinearMap
        (AlmostComplexStructure.product ℝ) J₀ (fderiv ℝ u z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      IntegrableOn (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal)
        (fderiv ℝ u z stdComplexLineImag)) (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ) ∧
      ∫ z in equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) ≤
          A + 2 * ∑ q, B q := by
  -- Outside the disc of radius `T` the data of the family are standard for every `R ∈ C`.
  obtain ⟨L₀, hL₀⟩ := hC.exists_bound_of_continuousOn
    (contDiff_comparisonNeckLength (n := 0)).continuous.continuousOn
  set T : ℝ := 2 * Real.exp (2 * Real.pi * (L₀ + 3))
  set S : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ
  have hstd {R : ℝ} (hR : R ∈ C) {z : ℝ × ℝ} (hz : z ∈ S) (x : V) :
      cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x = 0 ∧
        cappedComparisonAlmostComplex h₀ J hJ R (equivRealProdCLM.symm z) x = J₀ := by
    have hL : comparisonNeckLength R ≤ L₀ := (le_abs_self _).trans (by simpa using hL₀ R hR)
    have hz' : T < ‖equivRealProdCLM.symm z‖ := by simpa [S] using hz
    rw [cappedComparisonPerturbation_def, cappedComparisonAlmostComplex_def]
    exact ⟨cappedPerturbation_eq_zero_of_lt_norm hL hz' x,
      cappedAlmostComplex_eq_base_of_lt_norm h₀ _ hL hz' x⟩
  refine ⟨T, by positivity, fun R u A hR hu hfl hint harea ↦ ?_⟩
  -- On `S` the Floer equation and the energy density are those of the unperturbed problem.
  have hzero {z : ℝ × ℝ} (hz : z ∈ S) (v : ℂ) :
      (fun x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x v) =
        fun _ ↦ 0 := funext fun x ↦ by simp [(hstd hR hz x).1]
  have hdens {z : ℝ × ℝ} (hz : z ∈ S) :
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
        ω.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I)
          u z := by
    rw [ω.floerEnergyDensity_congr_perturbation u (Ks' := fun _ _ ↦ 0)
      (Kt' := fun _ _ ↦ 0) (hzero hz 1) (hzero hz I), floerEnergyDensity_zero]
  have hSm : MeasurableSet S := (isClosed_closedBall.isOpen_compl.preimage
    equivRealProdCLM.symm.continuous).measurableSet
  refine ⟨fun z hz ↦ ?_, hint.integrableOn.congr_fun (fun z hz ↦ (hdens hz).symm) hSm, ?_⟩
  · have h := hfl z
    rwa [(hstd hR hz _).2, ω.perturbedFDeriv_congr u (Ks' := fun _ _ ↦ 0)
      (Kt' := fun _ _ ↦ 0) (hzero hz 1) (hzero hz I),
      perturbedFDeriv_const ω (fun _ ↦ 0) (fun _ ↦ 0)] at h
  · -- The area outside the disc of radius `T` is at most the energy, which exceeds the total area
    -- by at most `2 (B₀ + B₁ + B_∞)`.
    rw [setIntegral_congr_fun hSm fun z hz ↦ hdens hz]
    exact ω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le h₀ hJ hH hHs hB
      (hC₀ hR) hu hfl hint harea S

open TauCeti.Complex (realChart) in
/-- **Solutions of the capped comparison family converge near the pole `∞`.** Let `H_q` be
period-one `C¹` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible and let `J_q(t, x)` be
`ω`-tame end structures. Fix a compact window `C ⊆ [0, ∞)` of parameters and a compact `K ⊆ V`.
There are a radius `ρ > 0` and a threshold `δ > 0` with the following property. Let `uₖ` be `C¹`
maps of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere solving the Floer equation
`(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the comparison family, with
`Rₖ ∈ C`, integrable energy density and symplectic area `∫ ω(∂ₛuₖ, ∂ₜuₖ) ≤ A`. Let `wₖ` be their
expressions in the chart `y ↦ y⁻¹` at the pole `∞`: `C³` maps on an open set `Ω` of the disc
`‖y‖ < ρ`, with `wₖ(y) = uₖ(y⁻¹)` for `y ≠ 0` and `wₖ(Ω) ⊆ K`. Then there are a subsequence `φ`,
a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a continuous `v : Ω \ Z → K`
such that along `φ` every disc about a point of `Z` eventually carries area of `wₖ` at least `δ`,
the differentials of the `wₖ` are uniformly bounded on every compact subset of `Ω \ Z`, and
`w_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_inv
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {C : Set ℝ} {K : Set V} (hC : IsCompact C) (hC₀ : C ⊆ Ici 0) (hK : IsCompact K) :
    ∃ ρ > 0, ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u w : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 ρ →
      (∀ k, R k ∈ C) → (∀ k, ContDiff ℝ 1 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
      (∀ k, ContDiffOn ℝ 3 (w k) Ω) →
      (∀ k, ∀ y ∈ Ω, y ≠ 0 → w k y = u k (realChart (fun ζ ↦ ζ⁻¹) y)) →
      (∀ k, MapsTo (w k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          ω (fderiv ℝ (w (φ n)) y stdComplexLineReal) (fderiv ℝ (w (φ n)) y stdComplexLineImag)) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (w (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ w (φ n)) v atTop (Ω \ ↑Z) := by
  obtain ⟨T, hT, hstd⟩ :=
    ω.exists_pos_forall_isComplexLinearMap_and_setIntegral_le_cappedComparison h₀ hJ hH hHs hB hC
      hC₀
  obtain ⟨δ, hδ, hconv⟩ :=
    ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_inv h₀.tames T hK
  refine ⟨T⁻¹, inv_pos.2 hT, δ, hδ,
    fun Ω R u w A hΩ hΩρ hRC hu hfl hint harea hw hwu hwK ↦ ?_⟩
  have h (k : ℕ) := hstd (hRC k) (hu k) (hfl k) (hint k) (harea k)
  exact hconv hΩ hΩρ (fun k z _ ↦ (hu k).differentiable one_ne_zero z) (fun k ↦ (h k).1)
    (fun k ↦ (h k).2.1) (fun k ↦ (h k).2.2) hw hwu hwK

open TauCeti.Complex (realChart) in
/-- **Solutions of the capped comparison family converge near the pole `∞`, the singularity
removed.** Let the inner product of `V` be the metric `⟪v, w⟫ = ω(v, J₀ w)` of the compatible
structure `J₀`, let `H_q` be period-one `C¹` Hamiltonians with `|H_q| ≤ B_q` and let `J_q(t, x)`
be `ω`-tame end structures. Fix a compact window `C ⊆ [0, ∞)` of parameters and a compact
`K ⊆ V`. There are a radius `ρ > 0` and a threshold `δ > 0` with the following property. Let `uₖ`
be `C¹` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere solving the Floer equation
`(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the comparison family, with
`Rₖ ∈ C`, integrable energy density, symplectic area `∫ ω(∂ₛuₖ, ∂ₜuₖ) ≤ A`, and values in `K`
outside the disc of radius `ρ⁻¹`. Then each `uₖ` has a limit `qₖ ∈ K` at the pole `∞`, and its
expression `wₖ(y) = uₖ(y⁻¹)` in the chart at `∞`, filled with `qₖ` at `0`, is smooth on the disc
`‖y‖ < ρ`. For every open set `Ω` of that disc there are a subsequence `φ`, a finite set `Z ⊆ Ω`
with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a continuous `v : Ω \ Z → K` such that along `φ` every
disc about a point of `Z` eventually carries area of `wₖ` at least `δ`, the differentials of the
`wₖ` are uniformly bounded on every compact subset of `Ω \ Z`, and `w_{φ n} → v` locally
uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_update_inv
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (hJ : ∀ q t x, ω.Tames (J q t x)) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {C : Set ℝ} {K : Set V} (hC : IsCompact C) (hC₀ : C ⊆ Ici 0) (hK : IsCompact K) :
    ∃ ρ > 0, ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 ρ →
      (∀ k, R k ∈ C) → (∀ k, ContDiff ℝ 1 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
      (∀ k, MapsTo (u k) (equivRealProdCLM.symm ⁻¹' (closedBall 0 ρ⁻¹)ᶜ) K) →
      ∃ (q : ℕ → V) (w : ℕ → ℝ × ℝ → V),
        (∀ k, q k ∈ K ∧ Tendsto (u k) (cocompact (ℝ × ℝ)) (𝓝 (q k))) ∧
        (∀ k, w k = update (fun y ↦ u k (realChart (fun ζ ↦ ζ⁻¹) y)) 0 (q k)) ∧
        (∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (w k) (equivRealProdCLM.symm ⁻¹' ball 0 ρ)) ∧
        ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
          ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
          (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
            ω (fderiv ℝ (w (φ n)) y stdComplexLineReal)
              (fderiv ℝ (w (φ n)) y stdComplexLineImag)) ∧
          (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
            ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (w (φ n)) y‖ ≤ M) ∧
          ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
          TendstoLocallyUniformlyOn (fun n ↦ w (φ n)) v atTop (Ω \ ↑Z) := by
  obtain ⟨T, hT, hstd⟩ :=
    ω.exists_pos_forall_isComplexLinearMap_and_setIntegral_le_cappedComparison h₀ hJ hH hHs hB hC
      hC₀
  obtain ⟨δ, hδ, hconv⟩ :=
    ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_update_inv hg T hK
  refine ⟨T⁻¹, inv_pos.2 hT, δ, hδ, fun Ω R u A hΩ hΩρ hRC hu hfl hint harea huK ↦ ?_⟩
  simp only [inv_inv] at huK
  have h (k : ℕ) := hstd (hRC k) (hu k) (hfl k) (hint k) (harea k)
  exact hconv hΩ hΩρ (fun k ↦ (hu k).contDiffOn) (fun k ↦ (h k).1) (fun k ↦ (h k).2.1)
    (fun k ↦ (h k).2.2) huK

end TauCeti.SymplecticForm

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {H : Puncture → ℝ → M → ℝ}
  {J₀ : SmoothAlmostComplexStructure I M} {J : Puncture → ℝ → SmoothAlmostComplexStructure I M}

/-- **Solutions of the capped comparison family in a symplectic chart of a manifold converge off
finitely many bubbling points.** Let `ω` be a nondegenerate two-form on `M`, let `H_q` be
period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible and let `J_q(t)` be
`ω`-tame end structures. Let `φ` be a smooth partial diffeomorphism from `M` onto an open subset
of `V` pulling the symplectic form `ω₀` back to `ω` on a compact set `K ⊆ φ.source`, such as a
Darboux chart, and let `J'_R(z, y)` be the structures `J_R` of the comparison family read in the
chart, `dφ_x ∘ J_R(z, x) = J'_R(z, φ x) ∘ dφ_x` for `R ∈ C`, `z ∈ D` and `x ∈ K`, and `C²` jointly
in `(R, z, y)` on an open set `W` containing `C × D × φ(K)`, where `C ⊆ [0, ∞)` is a compact
window of parameters and `D ⊆ ℝ × ℝ` is compact. There is a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` maps
of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere into `M` solving the Floer equation
`(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the comparison family, with
`Rₖ ∈ C`, integrable energy density and curvature term, symplectic area `∫ u^* ω ≤ A`, and
`uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence `ψ`, a limit `R₀ ∈ C` of
`R_{ψ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a map `v`, continuous on
`Ω \ Z` with values in `K`, such that along `ψ` every disc about a point of `Z` eventually carries
Floer energy at least `δ`, the differentials of the coordinate maps `φ ∘ u_{ψ n}` are uniformly
bounded on every compact subset of `Ω \ Z`, the coordinate maps converge to `φ ∘ v` locally
uniformly on `Ω \ Z`, and `u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison
    (hω : ω.IsNondegenerate) (h₀ : ω.Compatible J₀) (hJ : ∀ q t, ω.Tames (J q t))
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J' : ℝ → ℝ × ℝ → V → AlmostComplexStructure V} {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set M}
    (hφ : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ R ∈ C, ∀ z ∈ D, ∀ x ∈ K, IsComplexLinearMap
      ((h₀.cappedComparisonAlmostComplex J hJ R (equivRealProdCLM.symm z)).almostComplexStructureAt
        x) (J' R z (φ x)) (mvfderiv I φ x).toLinearMap)
    {W : Set (ℝ × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (J' q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hC₀ : C ⊆ Ici 0) (hD : IsCompact D) (hK : IsCompact K)
    (hKφ : K ⊆ φ.source) (hCDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, R k ∈ C) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (ω.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ (ψ : ℕ → ℕ) (R₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧ R₀ ∈ C ∧
        Tendsto (fun n ↦ R (ψ n)) atTop (𝓝 R₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R (ψ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R (ψ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (ψ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z →
          ∃ M', ∀ n, ∀ y ∈ L, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ M') ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  -- The Hamiltonians of the family, read in the chart, are jointly `C³` in `(R, z, y)` over the
  -- chart target: they are the smooth data on `ℂ × (ℝ × M)` composed with
  -- `(R, z, y) ↦ (z, (R, φ⁻¹ y))`.
  have hg : ContMDiffOn 𝓘(ℝ, ℝ × ((ℝ × ℝ) × V)) (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ).prod I)) 3
      (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (equivRealProdCLM.symm q.2.1, (q.1, φ.symm q.2.2)))
      (univ ×ˢ (univ ×ˢ φ.target)) :=
    (equivRealProdCLM.symm.contDiff.comp (contDiff_fst.comp contDiff_snd)).contMDiff.contMDiffOn
      |>.prodMk (contDiff_fst.contMDiff.contMDiffOn.prodMk
        ((φ.symm.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp
          (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn fun _ hq ↦ hq.2.2))
  have hK' (w : ℂ) : ContDiffOn ℝ 3 (fun q : ℝ × ((ℝ × ℝ) × V) ↦
      cappedComparisonPerturbation H q.1 (equivRealProdCLM.symm q.2.1) (φ.symm q.2.2) w)
      (univ ×ˢ (univ ×ˢ φ.target)) :=
    (contMDiffOn_iff_contDiffOn.1 ((contMDiff_cappedComparisonPerturbation (n := 3) hH hHs
      ).comp_contMDiffOn hg)).clm_apply contDiffOn_const
  have hJt (R : ℝ) (w : ℂ) (x : M) :=
    h₀.tames_almostComplexStructureAt_cappedComparisonAlmostComplex J hJ R w x
  have hWt : IsOpen (W ∩ univ ×ˢ (univ ×ˢ φ.target)) :=
    hW.inter (isOpen_univ.prod (isOpen_univ.prod φ.open_target))
  have hDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W ∩ univ ×ˢ (univ ×ˢ φ.target) :=
    subset_inter hCDKW (prod_mono (subset_univ _)
      (prod_mono (subset_univ _) (φ.toPartialEquiv.mapsTo.mono_left hKφ).image_subset))
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    φ (Ks := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
    (Kt := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I)
    (J := fun R z x ↦
      (h₀.cappedComparisonAlmostComplex J hJ R (equivRealProdCLM.symm z)).almostComplexStructureAt
        x) hφ hJJ' hWt ((hK' 1).mono inter_subset_right) ((hK' Complex.I).mono inter_subset_right)
        (hJ'.mono inter_subset_left) hC hD hK hKφ hDKW fun R _ z _ x _ ↦ hJt R _ x
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hRC hu hfl huK hint hcurv harea ↦ ?_⟩
  -- The Floer energy over `Ω` is at most the energy over the plane, which exceeds the area by at
  -- most `2 (B₀ + B₁ + B_∞)`.
  have hE (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
      (u k) z ≤
        A + 2 * ∑ q, B q :=
    hω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀ (hRC k)) ((hu k).of_le (by norm_num))
      (fun z ↦ hJt _ _ _) (hfl k) (hint k) (hcurv k) (harea k) Ω
  exact hconv hΩ hΩD hRC (fun k ↦ (hu k).contMDiffOn) (fun k z _ ↦ hfl k z) huK
    (fun k ↦ (hint k).integrableOn) hE

section Closed

variable [I.Boundaryless] [CompactSpace M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Solutions of the capped comparison family in a closed manifold converge off finitely many
bubbling points.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed
symplectic manifold, let `H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be
`ω`-compatible and let `J_q(t)` be `ω`-tame end structures. Let the structures `J_R(z, x)` of the
comparison family, read in the chart at every point of `M`, be `C²` jointly in `(R, z)` and the
chart coordinate, for `(R, z)` in an open set `W`. Let `e : M → F` be injective and differentiable,
such as the Whitney embedding of `M`, fix a compact window `C ⊆ [0, ∞)` of parameters and a compact
`D ⊆ ℝ × ℝ` with `C × D ⊆ W`, and over `C × D` let the structures be uniformly tame with respect
to `e`, `c ‖d e v‖² ≤ ω(v, J_R v)` with `c > 0`, and let the pushforwards through `e` of the
Hamiltonian vector fields of the two components of `K_R` be at most `L`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the
three-pole sphere into `M` solving the Floer equation `(du - X_{K_{Rₖ}})^{0,1} = 0` for the
structures `J_{Rₖ}(z, u)` of the comparison family, with `Rₖ ∈ C`, integrable energy density and
curvature term, and symplectic area `∫ u^* ω ≤ A`, and let
`Ω ⊆ D` be open. Then there are a subsequence `φ`, a limit `R₀ ∈ C` of `R_{φ n}`, and a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)` such that, along `φ`, every disc about a point of
`Z` eventually carries Floer energy at least `δ`, the energy densities are uniformly bounded on
every compact subset of `Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous map `v`,
locally uniformly after applying `e` and pointwise in `M`.

Unlike `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison`,
no condition is put on where the solutions take their values. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison
    (hω : ω.IsNondegenerate) (h₀ : ω.Compatible J₀) (hJ : ∀ q t, ω.Tames (J q t))
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {W : Set (ℝ × (ℝ × ℝ))} (hW : IsOpen W)
    (hJR : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry fun R z ↦
      (h₀.cappedComparisonAlmostComplex J hJ R (equivRealProdCLM.symm z)).almostComplexStructureAt))
      (W ×ˢ (extChartAt I α).target))
    {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} (hC : IsCompact C) (hC₀ : C ⊆ Ici 0) (hD : IsCompact D)
    (hCDW : C ×ˢ D ⊆ W) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ R ∈ C, ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v
      ((h₀.cappedComparisonAlmostComplex J hJ R (equivRealProdCLM.symm z)).almostComplexStructureAt
        x v))
    (hLs : ∀ R ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ R ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, R k ∈ C) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (ω.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ R₀ ∈ C, Tendsto (fun n ↦ R (φ n)) atTop (𝓝 R₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', ω.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- Each component `(R, z) ↦ K_R(z)(w)` of the family is `C³` jointly in the parameter, the
  -- domain point and the target point, so its Hamiltonian vector field is `C²` in every chart.
  have hK (w : ℂ) (p : ℝ × (ℝ × ℝ)) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1) (uncurry fun p x ↦
        cappedComparisonPerturbation H p.1 (equivRealProdCLM.symm p.2) x w) (p, x) :=
    (((contMDiff_cappedComparisonPerturbation (n := (2 : ℕ∞) + 1) hH
      fun q ↦ (hHs q).of_le (by norm_num)).comp
      (((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst).prodMk
        ((contDiff_fst.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))).clm_apply
      contMDiff_const).contMDiffAt
  have hJt (R : ℝ) (w : ℂ) (x : M) :=
    h₀.tames_almostComplexStructureAt_cappedComparisonAlmostComplex J hJ R w x
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
      (Kt := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I)
      (J := fun R z ↦ (h₀.cappedComparisonAlmostComplex J hJ R
        (equivRealProdCLM.symm z)).almostComplexStructureAt)
      he he_inj hW hC hD hCDW hJR
      (hω.contDiffOn_hamiltonianVectorFieldInChartAt fun p _ x ↦ hK 1 p x)
      (hω.contDiffOn_hamiltonianVectorFieldInChartAt fun p _ x ↦ hK Complex.I p x)
      (fun R _ z _ x ↦ hJt R _ x) hc hJc hLs hLt
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hRC hu hfl hint hcurv harea ↦ ?_⟩
  -- The Floer energy over `Ω` is at most the energy over the plane, which exceeds the area by at
  -- most `2 (B₀ + B₁ + B_∞)`.
  refine hconv hΩ hΩD hRC (fun k ↦ (hu k).contMDiffOn) (fun k z _ ↦ hfl k z)
    (fun k ↦ (hint k).integrableOn) fun k ↦
      hω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le hH
        (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀ (hRC k)) ((hu k).of_le (by norm_num))
        (fun z ↦ hJt _ _ _) (hfl k) (hint k) (hcurv k) (harea k) Ω

open TauCeti.Complex (realChart) in
/-- **Solutions of the capped comparison family in a closed manifold converge near the pole `∞`.**
Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `H_q` be period-one `C¹`
Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible and let `J_q(t)` be `ω`-tame end
structures. Let `e : M → F` be injective and differentiable, with `J₀` uniformly tame with respect
to `e`, `c ‖d e v‖² ≤ ω(v, J₀ v)` with `c > 0`, and fix a compact window `C ⊆ [0, ∞)` of
parameters. There are a radius `ρ > 0` and a threshold `δ > 0` with the following property. Let
`uₖ` be `C¹` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere into `M` solving the Floer
equation `(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the comparison family,
with `Rₖ ∈ C`, integrable energy density and curvature term, and symplectic area `∫ u^* ω ≤ A`. Let
`wₖ` be their expressions in the chart `y ↦ y⁻¹` at the pole `∞`: `C³` maps on an open set `Ω` of
the disc `‖y‖ < ρ`, with `wₖ(y) = uₖ(y⁻¹)` for `y ≠ 0`. Then there are a subsequence `φ` and a
finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)` such that, along `φ`, every disc about a
point of `Z` eventually carries area of `wₖ` at least `δ`, the area densities of the `wₖ` are
uniformly bounded on every compact subset of `Ω \ Z`, and the `wₖ` converge on `Ω \ Z` to a
continuous map `v`, locally uniformly after applying `e` and pointwise in `M`.

Together with
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison`
in the plane chart, this covers the whole three-pole sphere. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_inv
    (hω : ω.IsNondegenerate) (h₀ : ω.Compatible J₀) (hJ : ∀ q t, ω.Tames (J q t))
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ}
    (hc : 0 < c) (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v))
    {C : Set ℝ} (hC : IsCompact C) (hC₀ : C ⊆ Ici 0) :
    ∃ ρ > 0, ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u w : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 ρ →
      (∀ k, R k ∈ C) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (ω.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (w k) Ω) →
      (∀ k, ∀ y ∈ Ω, y ≠ 0 → w k y = u k (realChart (fun ζ ↦ ζ⁻¹) y)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          (SmoothBundleForm.eval₂ ω (w (φ n) y)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineImag) : ℝ)) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L',
          (SmoothBundleForm.eval₂ ω (w (φ n) y)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineImag) : ℝ) ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ w (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ w (φ n) z) atTop (𝓝 (v z)) := by
  -- Outside the disc of radius `T` the data of the family are standard for every `R ∈ C`.
  obtain ⟨L₀, hL₀⟩ := hC.exists_bound_of_continuousOn
    (contDiff_comparisonNeckLength (n := 0)).continuous.continuousOn
  set T : ℝ := 2 * Real.exp (2 * Real.pi * (L₀ + 3))
  set S : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ
  have hstd {R : ℝ} (hR : R ∈ C) {z : ℝ × ℝ} (hz : z ∈ S) :
      (∀ x, cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x = 0) ∧
        h₀.cappedComparisonAlmostComplex J hJ R (equivRealProdCLM.symm z) = J₀ := by
    have hL : comparisonNeckLength R ≤ L₀ := (le_abs_self _).trans (by simpa using hL₀ R hR)
    have hz' : T < ‖equivRealProdCLM.symm z‖ := by simpa [S] using hz
    rw [cappedComparisonPerturbation_def, h₀.cappedComparisonAlmostComplex_def J hJ R]
    exact ⟨cappedPerturbation_eq_zero_of_lt_norm hL hz',
      h₀.cappedAlmostComplex_eq_base_of_notMem_truncation J hJ _
        (notMem_truncation_of_lt_norm (by linarith) hz')⟩
  have hJt (R : ℝ) (w : ℂ) (x : M) :=
    h₀.tames_almostComplexStructureAt_cappedComparisonAlmostComplex J hJ R w x
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_inv
    J₀ (fun x ↦ (h₀.compatibleAt x).tames) he he_inj hc hJc T
  refine ⟨T⁻¹, inv_pos.2 (by positivity), δ, hδ,
    fun Ω R u w A hΩ hΩρ hRC hu hfl hint hcurv harea hw hwu ↦ ?_⟩
  -- On `S` the Floer equation and the energy density are those of the unperturbed problem.
  have hzero (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ S) (v : ℂ) :
      (fun x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x v) =
        fun _ ↦ 0 := funext fun x ↦ by simp [(hstd (hRC k) hz).1 x]
  have hdens (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ S) :
      (SmoothBundleForm.eval₂ ω (u k z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) =
        ω.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z := by
    rw [ω.floerEnergyDensity_congr_perturbation (u k) (Ks' := fun _ _ ↦ 0)
      (Kt' := fun _ _ ↦ 0) (hzero k hz 1) (hzero k hz Complex.I), floerEnergyDensity_zero]
  have hSm : MeasurableSet S := (isClosed_closedBall.isOpen_compl.preimage
    equivRealProdCLM.symm.continuous).measurableSet
  refine hconv hΩ hΩρ (fun k z _ ↦ (hu k).mdifferentiableAt one_ne_zero) (fun k z hz ↦ ?_)
    (fun k ↦ (hint k).integrableOn.congr_fun (fun z hz ↦ (hdens k z hz).symm) hSm)
    (fun k ↦ ?_) hw hwu
  · have h := hfl k z
    rwa [(hstd (hRC k) hz).2, ω.perturbedMFDeriv_congr_perturbation (u k) (Ks' := fun _ _ ↦ 0)
      (Kt' := fun _ _ ↦ 0) (hzero k hz 1) (hzero k hz Complex.I)] at h
  · -- The area outside the disc of radius `T` is at most the energy, which exceeds the total area
    -- by at most `2 (B₀ + B₁ + B_∞)`.
    exact (setIntegral_congr_fun hSm fun z hz ↦ hdens k z hz).trans_le
      (hω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le hH hHs hB (hC₀ (hRC k))
        (hu k) (fun z ↦ hJt _ _ _) (hfl k) (hint k) (hcurv k) (harea k) S)

end Closed

end TauCeti.SmoothTwoForm.IsNondegenerate

namespace TauCeti.SmoothTwoForm.Compatible

open Bundle Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  {H : Puncture → ℝ → M → ℝ} {e : M → F}

/-- **Solutions of the capped comparison family in a closed manifold converge off finitely many
bubbling points, for the structures of the family.** Let `σ` be a two-form on a closed manifold
`M` compatible with a smooth almost complex structure `J₀`, and let the end structures `J q t` be
tamed by `σ`, of period one in `t` and jointly `C²` on `ℝ × M`. Take the structures
`TauCeti.SmoothTwoForm.Compatible.cappedComparisonAlmostComplex` of the comparison family, and
otherwise the hypotheses of
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison` in
the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, for a compact window `C ⊆ [0, ∞)` of
parameters and a compact window `D` of the plane chart `ℝ × ℝ ≅ ℂ`: the structures of the family,
read in the charts of `M`, are `C²` jointly in the parameter, the domain point and the chart
coordinate, over the whole plane including the poles `0` and `1`, so only the uniform tameness
with respect to `e` and the bound on the Hamiltonian vector fields remain as hypotheses. Then there
is a threshold `δ > 0` such that every sequence of solutions for parameters in `C` with symplectic
area at most `A` has a subsequence whose parameters converge in `C` and which converges on an open
`Ω ⊆ D` off a finite set `Z` of bubbling points, with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison
    (h₀ : σ.Compatible J₀) (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ : ∀ q t, σ.Tames (J q t)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} (hC : IsCompact C) (hC₀ : C ⊆ Ici 0) (hD : IsCompact D)
    {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ R ∈ C, ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.cappedComparisonAlmostComplex J hJ R (equivRealProdCLM.symm z) x v))
    (hLs : ∀ R ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ R ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, R k ∈ C) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (σ.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (σ.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ σ.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ R₀ ∈ C, Tendsto (fun n ↦ R (φ n)) atTop (𝓝 R₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, σ.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', σ.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hω := h₀.isNondegenerate
  -- The structures of the family are `C²` jointly in `(R, z, x)`, at every parameter and every
  -- point of the plane.
  have hJ' (p : ℝ × (ℝ × ℝ)) (_ : p ∈ univ) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (2 : ℕ∞)
        (fun q : (ℝ × (ℝ × ℝ)) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
          ((h₀.cappedComparisonAlmostComplex J hJ q.1.1
            (equivRealProdCLM.symm q.1.2)).toEndomorphism q.2)) (p, x) :=
    (h₀.contMDiff_cappedComparisonAlmostComplex J hJ hJp hJs
      (contDiff_fst.contMDiff.comp contMDiff_fst)
      ((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst)
      contMDiff_snd).contMDiffAt
  exact
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison
    h₀ hJ hH hHs hB isOpen_univ
    (contDiffOn_almostComplexInChartAt_almostComplexStructureAt (n := 2)
      (J := fun q : ℝ × (ℝ × ℝ) ↦
        h₀.cappedComparisonAlmostComplex J hJ q.1 (equivRealProdCLM.symm q.2)) hJ')
    he he_inj hC hC₀ hD (subset_univ _) hc
    (fun R hR z hz x v ↦ by
      simpa only [IsNondegenerate.symplecticFormAt_apply,
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hJc R hR z hz x v)
    hLs hLt

end TauCeti.SmoothTwoForm.Compatible
