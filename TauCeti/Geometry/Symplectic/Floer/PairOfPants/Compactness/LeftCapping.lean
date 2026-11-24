/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.LeftCapping

/-!
# Compactness of the input-exchange family capped at `0`

The pair-of-pants product is unital on the left because gluing the negative PSS plane of `H_0`
into the input at `0` of the pair of pants `S = ℂ ∖ {0, 1}` gives a cylinder whose counts compare
with continuation maps. The comparison runs along the input-exchange family capped at `0`,
`K_c = TauCeti.Floer.cappedExchangePerturbation H L c` for `0 ≤ c ≤ 1`, at a fixed neck length
`L > 4`. Its domain is the capped surface `ℂ ∖ {1}`, with one input end at `1`, carrying `H_1`, and
the output end recentred at `c`, carrying `H_∞`; the capped puncture `0` is an interior point of
this domain. The one-parameter family of moduli spaces over `c` gives the left unit homotopy.

This file proves the interior part of Gromov–Floer compactness for this family over a compact
window `C ⊆ [0, 1]` of parameters, for a target which is a finite-dimensional manifold `M` with a
nondegenerate two-form `ω`, such as a closed symplectic manifold, on the part of the domain that a
sequence of solutions maps into a compact subset `K` of the source of a symplectic chart
`φ : M ⊇ U → V`, such as a Darboux chart. The compact windows `D` of the domain may contain the
capped puncture `0`, so that bubbling at the inserted plane is covered.

Two inputs combine.

* **The energy bound.** For a solution `u` whose loops along the input end at `1` and along the
  recentred output end converge to loops `x_1` and `x_∞`, with integrable energy and area
  densities, the energy identity of the family (in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`,
  `abs_integral_floerEnergyDensity_cappedExchangePerturbation_sub_le`) bounds the Floer energy
  over `S` by its topological part
  `∫_S u^*ω + ∫₀¹ H_1(t, x_1(t)) dt - ∫₀¹ H_∞(t, x_∞(t)) dt` plus `B_0 + (B_0 + B_1 + B_∞)`, for
  `|H_q| ≤ B_q`, uniformly in `c`. Since the energy density of a solution is nonnegative where the
  structures are tamed, and the capped puncture is a null set, this bounds the energy over every
  part of the capped domain.
* **Compactness in a symplectic chart.** The datum is `C³` jointly in the parameter `c`, the point
  of the capped domain and the target point
  (`TauCeti.Floer.contMDiffAt_cappedExchangePerturbation`), hence so are its Hamiltonians read in
  the chart (`TauCeti.Floer.contDiffOn_cappedExchangePerturbation_comp_symm`). The compactness
  theorem over a compact parameter window in a symplectic chart (in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`,
  `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`) then applies.

The main result, in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, is
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedExchange`. It takes
any family `J_c(z, x)` of structures on the tangent spaces of `M` tamed by `ω` on the capped
domain, read in the chart by a family `J'_c` that is `C²` jointly in `(c, z, y)`. It gives a
threshold `δ > 0` such that every sequence of solutions for parameters `cₖ ∈ C`, with topological
energy at most `A` and images of an open `Ω ⊆ D` in `K`, has a subsequence whose parameters
converge to some `c₀ ∈ C` and which converges off a finite set `Z ⊆ Ω` of bubbling points, with
`#Z * δ ≤ A + (B_0 + (B_0 + B_1 + B_∞))`: the coordinate maps converge locally uniformly with
locally bounded derivatives, and the maps converge pointwise in `M`.

The regularity of the limit, the bubbles at the points of `Z`, breaking along the two ends, and
covering `M` by several charts are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti

namespace Floer

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {H : Puncture → ℝ → M → ℝ} {L : ℝ}

/-- **The capped datum read in a chart is smooth.** For period-one Hamiltonians which are `C^n` on
`ℝ × M`, a neck length `L > 4` and a `C^n` partial diffeomorphism `φ` from `M` to a normed space
`V`, each component `K_c(z, φ⁻¹ y)(w)` of the input-exchange family capped at `0`, read in the
chart, is `C^n` jointly in the parameter `c`, the real coordinates `z` of the capped domain
`ℂ ∖ {1}` and the chart coordinate `y` in the target of `φ`. -/
theorem contDiffOn_cappedExchangePerturbation_comp_symm {n : ℕ∞} {m : WithTop ℕ∞}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q))) (hL : 4 < L)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hnm : (n : WithTop ℕ∞) ≤ m) (w : ℂ) :
    ContDiffOn ℝ n (fun q : ℝ × ((ℝ × ℝ) × V) ↦
        cappedExchangePerturbation H L q.1 (equivRealProdCLM.symm q.2.1) (φ.symm q.2.2) w)
      (univ ×ˢ ({z | equivRealProdCLM.symm z ≠ 1} ×ˢ φ.target)) := by
  rintro ⟨c, z, y⟩ ⟨-, hz, hy⟩
  refine ContDiffAt.contDiffWithinAt ?_
  -- The parameter, the point `z` of the capped domain and the chart inverse `φ⁻¹` are `C^n` into
  -- the product `ℝ × (ℂ × M)`.
  have hsymm : ContMDiffAt 𝓘(ℝ, V) I n φ.symm y :=
    (φ.symm.contMDiffOn.of_le hnm).contMDiffAt (φ.open_target.mem_nhds hy)
  have htriple : ContMDiffAt 𝓘(ℝ, ℝ × ((ℝ × ℝ) × V)) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) n
      (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (q.1, (equivRealProdCLM.symm q.2.1, φ.symm q.2.2)))
      (c, (z, y)) :=
    contDiff_fst.contMDiff.contMDiffAt.prodMk
      ((equivRealProdCLM.symm.contDiff.comp (contDiff_fst.comp contDiff_snd)).contMDiff.contMDiffAt
        |>.prodMk (hsymm.comp (c, (z, y)) (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffAt))
  have hK := (contMDiffAt_cappedExchangePerturbation hH hHs hL c hz (φ.symm y)).comp (c, (z, y))
    htriple
  exact (contMDiffAt_iff_contDiffAt.1 hK).clm_apply contDiffAt_const

end Floer

namespace SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {H : Puncture → ℝ → M → ℝ} {L : ℝ}

/-- **Solutions of the input-exchange family capped at `0` in a symplectic chart of a manifold
converge off finitely many bubbling points.** Let `ω` be a nondegenerate two-form on `M`, let
`H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, and fix a neck length `L > 4`. Let `φ` be
a smooth partial diffeomorphism from `M` onto an open subset of `V` pulling the symplectic form
`ω₀` back to `ω` on a compact set `K ⊆ φ.source`, such as a Darboux chart. Let `J_c(z, x)` be
structures on the tangent spaces of `M`, tamed by `ω` for `c ∈ C` and `z` in the capped domain
`ℂ ∖ {1}`, and let `J'_c(z, y)` be the same structures read in the chart,
`dφ_x ∘ J_c(z, x) = J'_c(z, φ x) ∘ dφ_x` for `c ∈ C`, `z ∈ D` and `x ∈ K`, and `C²` jointly in
`(c, z, y)` on an open set `W` containing `C × D × φ(K)`, where `C ⊆ [0, 1]` is a compact window of
parameters and `D` is a compact subset of the capped domain, in real coordinates. There is a
threshold `δ > 0` with the following property.

Let `uₖ` be `C³` maps of the capped domain into `M` solving the Floer equation
`(du - X_{K_{cₖ}})^{0,1} = 0` there for the structures `J_{cₖ}(z, u)` and the datum `K_{cₖ}` of the
input-exchange family capped at `0` with neck length `L`, with `cₖ ∈ C`. Suppose that the loops of
`uₖ` along the input end at `1` and along the output end recentred at `cₖ` converge pointwise to
loops `x₁ₖ` and `x_∞ₖ`, that the energy and area densities of `uₖ` are integrable over
`S = ℂ ∖ {0, 1}`, that the topological energy
`∫_S uₖ^*ω + ∫₀¹ H_1(t, x₁ₖ(t)) dt - ∫₀¹ H_∞(t, x_∞ₖ(t)) dt` is at most `A`, and that
`uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence `ψ`, a limit `c₀ ∈ C` of
`c_{ψ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + (B_0 + (B_0 + B_1 + B_∞))`, and a map `v`,
continuous on `Ω \ Z` with values in `K`, such that along `ψ` every disc about a point of `Z`
eventually carries Floer energy at least `δ`, the differentials of the coordinate maps
`φ ∘ u_{ψ n}` are uniformly bounded on every compact subset of `Ω \ Z`, the coordinate maps
converge to `φ ∘ v` locally uniformly on `Ω \ Z`, and `u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedExchange
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {J' : ℝ → ℝ × ℝ → V → AlmostComplexStructure V} {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set M}
    (hφ : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ c ∈ C, ∀ z ∈ D, ∀ x ∈ K,
      IsComplexLinearMap (J c z x) (J' c z (φ x)) (mvfderiv I φ x).toLinearMap)
    {W : Set (ℝ × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (J' q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hC₀₁ : C ⊆ Icc 0 1) (hD : IsCompact D)
    (hD₁ : ∀ z ∈ D, equivRealProdCLM.symm z ≠ 1) (hK : IsCompact K) (hKφ : K ⊆ φ.source)
    (hCDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W)
    (hJt : ∀ c ∈ C, ∀ z, equivRealProdCLM.symm z ≠ 1 → ∀ x,
      (hω.symplecticFormAt x).Tames (J c z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x₁ xinf : ℕ → ℝ → M⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, c k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | equivRealProdCLM.symm z ≠ 1}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 1 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (c k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k (t : ℝ), Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x₁ k t))) →
      (∀ k (t : ℝ), Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (↑(c k) + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xinf k t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
        (u k)) thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          (∫ t in (0 : ℝ)..1, H one t (x₁ k t)) - (∫ t in (0 : ℝ)..1, H inf t (xinf k t)) ≤
        A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (ψ : ℕ → ℕ) (c₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧ c₀ ∈ C ∧
        Tendsto (fun n ↦ c (ψ n)) atTop (𝓝 c₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + (B zero + ∑ q, B q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ cappedExchangePerturbation H L (c (ψ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L (c (ψ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (ψ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z →
          ∃ M', ∀ n, ∀ y ∈ L', ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ M') ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  -- The Hamiltonians of the family read in the chart are `C³` over the capped domain and the
  -- chart target.
  set T : Set (ℝ × ((ℝ × ℝ) × V)) := univ ×ˢ ({z | equivRealProdCLM.symm z ≠ 1} ×ˢ φ.target)
  have hT : IsOpen T := isOpen_univ.prod
    ((isOpen_ne_fun equivRealProdCLM.symm.continuous continuous_const).prod φ.open_target)
  have hK' (w : ℂ) := contDiffOn_cappedExchangePerturbation_comp_symm (n := 3) hH hHs hL φ
    (WithTop.coe_le_coe.2 le_top) w
  have hDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W ∩ T := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hq.2.2
    exact ⟨hCDKW hq, trivial, hD₁ _ hq.2.1, hxq ▸ φ.toPartialEquiv.map_source (hKφ hx)⟩
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    φ (Ks := fun c z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x 1)
    (Kt := fun c z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x Complex.I)
    hφ hJJ' (hW.inter hT) ((hK' 1).mono inter_subset_right)
    ((hK' Complex.I).mono inter_subset_right)
    (hJ'.mono inter_subset_left) hC hD hK hKφ hDKW fun c hc z hz x _ ↦ hJt c hc z (hD₁ z hz) x
  refine ⟨δ, hδ, fun Ω c u x₁ xinf A hΩ hΩD hcC hu hfl hx₁ hxinf hint harea hA huK ↦ ?_⟩
  -- The pair of pants `S` has null complement, so `Ω` lies in `S` up to a null set.
  have hΩS : Ω ≤ᵐ[volume] thricePuncturedSphereReal := by
    filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz _ using hz
  -- The Floer energy over `Ω` is at most the energy over `S`, which exceeds the topological
  -- energy by at most `B_0 + (B_0 + B_1 + B_∞)`.
  have hE (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
      (u k) z ≤
        A + (B zero + ∑ q, B q) := by
    have habs := hω.abs_integral_floerEnergyDensity_cappedExchangePerturbation_sub_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB hL (hC₀₁ (hcC k)).1 (hC₀₁ (hcC k)).2
      (((hu k).of_le (by norm_num)).mono fun _ hz ↦ hz.2) (hx₁ k) (hxinf k) (hint k) (harea k)
    refine (setIntegral_mono_set (hint k) (ae_restrict_of_forall_mem
      isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦ floerEnergyDensity_nonneg hω
        (hJt _ (hcC k) z hz.2 _) (hfl k z hz.2)) hΩS).trans ?_
    linarith [(abs_sub_le_iff.1 habs).1, hA k]
  exact hconv hΩ hΩD hcC (fun k ↦ (hu k).mono fun z hz ↦ hD₁ z (hΩD hz))
    (fun k z hz ↦ hfl k z (hD₁ z (hΩD hz))) huK (fun k ↦ (hint k).mono_set_ae hΩS) hE

end SmoothTwoForm.IsNondegenerate

end TauCeti
