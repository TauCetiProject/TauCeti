/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
`Z` of bubbling points, with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`. The regularity of the limit, the
bubbles at the points of `Z` and the behaviour near the pole `∞` are not treated here. Interior
compactness at the long-neck end `R → ∞`, on the pair of pants and the caps of the PSS planes, is
in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.LongNeck`.

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
limit with values in `K`. Covering `M` by several charts is not treated here.

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
  have hJt (R : ℝ) (w : ℂ) (x : M) : (hω.symplecticFormAt x).Tames
      ((h₀.cappedComparisonAlmostComplex J hJ R w).almostComplexStructureAt x) := by
    rw [h₀.cappedComparisonAlmostComplex_def J hJ R]
    exact hω.tames_iff.1 (h₀.tames_cappedAlmostComplex J hJ _ _ w) x
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
        A + 2 * ∑ q, B q := by
    have habs := hω.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀ (hRC k)) ((hu k).of_le (by norm_num))
      (hint k) (hcurv k)
    refine (setIntegral_le_integral (hint k) (Eventually.of_forall fun z ↦
      floerEnergyDensity_nonneg hω (hJt _ _ _) (hfl k z))).trans ?_
    linarith [(abs_sub_le_iff.1 habs).1, harea k]
  exact hconv hΩ hΩD hRC (fun k ↦ (hu k).contMDiffOn) (fun k z _ ↦ hfl k z) huK
    (fun k ↦ (hint k).integrableOn) hE

end TauCeti.SmoothTwoForm.IsNondegenerate
