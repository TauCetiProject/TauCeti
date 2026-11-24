/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.AssociativityPath
import TauCeti.Topology.Separation.Basic

/-!
# Compactness of spheres with moving input ends

The associativity of the pair-of-pants product compares the two broken products through a family
of four-punctured spheres: the inputs sit at moving punctures `c i` of `ℂ`, with scales `a i`, and
the output at `∞`. Its Hamiltonian datum is
`K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, and along the associativity path the
configuration is `(c, a) = (associativityCenter f τ, associativityScale f τ)` for a parameter
`τ ∈ ℝ` (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.AssociativityPath`). This file
proves the interior part of Gromov–Floer compactness for such families over a compact window of
parameters, for a symplectic vector space target `(V, ω)`, in the plane chart `ℝ × ℝ ≅ ℂ`.

The input is the energy bound on the truncations `Σ_R` of the sphere
(`SymplecticForm.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`):
for `|H i| ≤ B i` and `|Hout| ≤ Bout`, the Floer energy over `Σ_R` differs from its topological
part, the symplectic area over `Σ_R` plus `β(R - 1)` times the Hamiltonian terms of the boundary
circles, by at most `∑ i, B i + Bout`, whatever the configuration. For a solution of the Floer
equation on `Σ_R` with tame almost complex structures the energy density is nonnegative, so the
energy over any part of `Σ_R` is at most the topological part plus `∑ i, B i + Bout`
(`SymplecticForm.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le`). The datum is
smooth jointly in the configuration and in the domain and target points away from the centers
(`TauCeti.Floer.contDiffAt_puncturedSpherePerturbation_comp`), so for a smooth family of
configurations compactness over a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D` lying in `Σ_R` for all parameters of the window.

The almost complex structures `J_p(z, x)` are any family, jointly `C²` near the window and tamed
by `ω` on `Σ_R`; the moving centers are not points of the domain, so no condition is imposed
there.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere`: for a
  `C³` family of configurations `p ↦ (c p, a p)` over a real inner product space of parameters, a
  sequence of solutions with parameters in a compact window and topological energy on `Σ_R` at
  most `A` has a subsequence whose parameters converge and which converges locally uniformly off a
  finite set `Z` of bubbling points, with `#Z * δ ≤ A + ∑ i, B i + Bout`.
* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_associativity`: the case
  of the associativity path, for `0 < f` and `3 f ≤ 1`, with the parameter `τ ∈ ℝ`.

The regularity of the limit, the bubbles at the points of `Z`, the breaking of Floer cylinders
along the ends, and the collision of two inputs at the ends of the family are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product through families of
  four-punctured spheres.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Real Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Hout : ℝ → V → ℝ}

/-- **Solutions on spheres with moving input ends converge off finitely many bubbling points.**
Let `p ↦ (c p, a p)` be a `C³` family of configurations of input ends, over a real inner product
space `P` of parameters, and let `J_p(z, x)` be almost complex structures, jointly `C²` on an open
set `W ⊆ P × ((ℝ × ℝ) × V)` containing `C × D × K`, where `C ⊆ P`, `D ⊆ ℝ × ℝ` and `K ⊆ V` are
compact, and tamed by `ω` at the points of the truncation `Σ_R` of `(c p, a p)` for `p ∈ C`. Let
the input ends carry period-one `C³` Hamiltonians `H i` with `|H i| ≤ B i`, and the output end a
period-one `C³` Hamiltonian `Hout` with `|Hout| ≤ Bout`.
Suppose that for every `p ∈ C` the scales `a p i` are nonzero, the discs `‖w - c p i‖ < ‖a p i‖ / 2`
are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and the window `D` lies in the
truncation `Σ_R` of the configuration `(c p, a p)`, for some `R ≥ 1`.

There is a threshold `δ > 0` with the following property. Let `uₖ` be maps of the plane chart
`ℝ × ℝ ≅ ℂ`, `C³` off the centers `c pₖ i`, solving the Floer equation `(du - X_{K_{pₖ}})^{0,1} = 0`
for `J_{pₖ}(z, u)` on `Σ_R`, with `pₖ ∈ C`, with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`, and whose
topological energy on `Σ_R`, the symplectic area plus `β(R - 1)` times the Hamiltonian terms of the
boundary circles, is at most `A`. Then there are a subsequence `φ`, a limit `p₀ ∈ C` of `p_{φ n}`, a
finite set `Z ⊆ Ω` with `#Z * δ ≤ A + ∑ i, B i + Bout`, and a continuous `v : Ω \ Z → K` such that
along `φ` every disc about a point of `Z` eventually carries Floer energy at least `δ`, the
differentials are uniformly bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally
uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere
    (ω : SymplecticForm V) {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    {ι : Type*} [Fintype ι] {H : ι → ℝ → V → ℝ} {c a : P → ι → ℂ}
    (hc : ContDiff ℝ 3 c) (ha : ContDiff ℝ 3 a)
    {J : P → ℝ × ℝ → V → AlmostComplexStructure V} {W : Set (P × ((ℝ × ℝ) × V))}
    (hW : IsOpen W) (hJs : ContDiffOn ℝ 2
      (fun q : P × ((ℝ × ℝ) × V) ↦ (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 3 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 3 (uncurry Hout))
    {B : ι → ℝ} {Bout : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set V} {R : ℝ} (hC : IsCompact C) (hD : IsCompact D)
    (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c p) (a p) R,
      ∀ x, ω.Tames (J p z x))
    (ha₀ : ∀ p ∈ C, ∀ i, a p i ≠ 0)
    (hsep : ∀ p ∈ C, Pairwise fun i j => ‖a p i‖ / 2 + ‖a p j‖ / 2 ≤ ‖c p i - c p j‖)
    (hout : ∀ p ∈ C, ∀ i, ‖c p i‖ + ‖a p i‖ / 2 ≤ 2 * Real.exp (2 * π)) (hR : 1 ≤ R)
    (hDR : ∀ p ∈ C, D ⊆ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c p) (a p) R) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) {z | ∀ i, equivRealProdCLM.symm z ≠ c (p k) i}) →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c (p k)) (a (p k)) R,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ puncturedSpherePerturbation (c (p k)) (a (p k)) H Hout
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation (c (p k)) (a (p k)) H Hout
              (equivRealProdCLM.symm z) x I) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, (∫ z in equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c (p k)) (a (p k)) R,
          ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u k (equivRealProdCLM
            (c (p k) i + a (p k) i * Puncture.zero.cylindricalEndLift (↑R + ↑t * I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u k (equivRealProdCLM
            (Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * I))))) ≤ A) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + (∑ i, B i + Bout) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- The datum is smooth on the open set `W₀` of parameters with nonzero scales and domain points
  -- other than the centers.
  set W₀ : Set (P × ((ℝ × ℝ) × V)) :=
    {q | (∀ i, a q.1 i ≠ 0) ∧ ∀ i, equivRealProdCLM.symm q.2.1 ≠ c q.1 i} with hW₀
  have hW₀o : IsOpen W₀ := by
    simp only [hW₀, ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun
        ((continuous_apply i).comp (ha.continuous.comp continuous_fst)) continuous_const).inter
      (isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop)
        ((continuous_apply i).comp (hc.continuous.comp continuous_fst)))
  have hKs (v : ℂ) : ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦ puncturedSpherePerturbation
      (c q.1) (a q.1) H Hout (equivRealProdCLM.symm q.2.1) q.2.2 v) (W ∩ W₀) := fun q hq ↦
    (((contDiffAt_puncturedSpherePerturbation_comp (n := 3) hH hHs hHout hHouts
      hc.contDiffAt ha.contDiffAt hq.2.1 hq.2.2 q.2.2).comp q
      (contDiff_fst.prodMk ((equivRealProdCLM.symm.contDiff.comp
        (contDiff_fst.comp contDiff_snd)).prodMk (contDiff_snd.comp contDiff_snd))).contDiffAt
      ).clm_apply contDiffAt_const).contDiffWithinAt
  have hCDKW₀ : C ×ˢ (D ×ˢ K) ⊆ W₀ := fun q hq ↦ ⟨ha₀ q.1 hq.1, fun i ↦
    ne_of_mem_puncturedSphereTruncation (ha₀ q.1 hq.1 i) (hDR q.1 hq.1 hq.2.1)⟩
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z) x 1)
    (Kt := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z) x I)
    (J := J) (hW.inter hW₀o) (hKs 1) (hKs I) (hJs.mono inter_subset_left) hC hD hK
    (subset_inter hCDKW hCDKW₀) fun p hp z hz x _ ↦ hJt p hp z (hDR p hp hz) x
  refine ⟨δ, hδ, fun Ω p u A hΩ hΩD hpC hu hfl huK htop ↦ ?_⟩
  -- On the truncation `Σ_R` the energy density is integrable, and the energy over `Ω ⊆ Σ_R` is at
  -- most the topological energy plus `∑ i, B i + Bout`.
  have hUo (k : ℕ) : IsOpen {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠ c (p k) i} :=
    isOpen_forall_ne equivRealProdCLM.symm.continuous
  have hTU (k : ℕ) : equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c (p k)) (a (p k)) R ⊆
      {z | ∀ i, equivRealProdCLM.symm z ≠ c (p k) i} := fun z hz i ↦
    ne_of_mem_puncturedSphereTruncation (ha₀ _ (hpC k) i) hz
  have hΩT (k : ℕ) := hΩD.trans (hDR (p k) (hpC k))
  have hHs₁ (i : ι) : ContDiff ℝ 1 (uncurry (H i)) := (hHs i).of_le (by norm_num)
  have hHouts₁ : ContDiff ℝ 1 (uncurry Hout) := hHouts.of_le (by norm_num)
  have hint (k : ℕ) := ω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation
    hH hHs₁ hHout hHouts₁ (ha₀ _ (hpC k)) (hsep _ (hpC k)) (hout _ (hpC k)) (hUo k) (hTU k)
    ((hu k).of_le (by norm_num))
  refine hconv hΩ hΩD hpC (fun k ↦ (hu k).mono ((hΩT k).trans (hTU k)))
    (fun k z hz ↦ hfl k z (hΩT k hz)) huK (fun k ↦ (hint k).mono_set (hΩT k)) fun k ↦ ?_
  refine (ω.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le hH hHs₁ hHout hHouts₁
    (ha₀ _ (hpC k)) (hsep _ (hpC k)) (hout _ (hpC k)) hB hBout (hUo k) (hTU k)
    ((hu k).of_le (by norm_num)) hR (fun z hz ↦ hJt _ (hpC k) z hz _) (hfl k) (hΩT k)).trans ?_
  linarith [htop k]

/-- **Solutions along the associativity path converge off finitely many bubbling points.** This is
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere` for the
configurations `τ ↦ (associativityCenter f τ, associativityScale f τ)` joining the two broken
products, for a plumbing factor `0 < f` with `3 f ≤ 1` and a compact window `C ⊆ ℝ` of
parameters. Along this path the scales never vanish and the input discs stay disjoint inside the
disc `‖w‖ ≤ 2 exp (2π)`, so the only remaining condition on the window `D` is that it lies in the
truncation `Σ_R` of every configuration of the window. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_associativity
    (ω : SymplecticForm V) {H : Fin 3 → ℝ → V → ℝ} {f : ℝ} (hf : 0 < f) (hf₃ : 3 * f ≤ 1)
    {J : ℝ → ℝ × ℝ → V → AlmostComplexStructure V} {W : Set (ℝ × ((ℝ × ℝ) × V))}
    (hW : IsOpen W) (hJs : ContDiffOn ℝ 2
      (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 3 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 3 (uncurry Hout))
    {B : Fin 3 → ℝ} {Bout : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} {R : ℝ}
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ τ ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹'
      puncturedSphereTruncation (associativityCenter f τ) (associativityScale f τ) R,
      ∀ x, ω.Tames (J τ z x)) (hR : 1 ≤ R)
    (hDR : ∀ τ ∈ C, D ⊆ equivRealProdCLM.symm ⁻¹'
      puncturedSphereTruncation (associativityCenter f τ) (associativityScale f τ) R) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃τ : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, τ k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k)
        {z | ∀ i, equivRealProdCLM.symm z ≠ associativityCenter f (τ k) i}) →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation
          (associativityCenter f (τ k)) (associativityScale f (τ k)) R,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (τ k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ k))
              (associativityScale f (τ k)) H Hout (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ k))
              (associativityScale f (τ k)) H Hout (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, (∫ z in equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation
            (associativityCenter f (τ k)) (associativityScale f (τ k)) R,
          ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u k (equivRealProdCLM
            (associativityCenter f (τ k) i + associativityScale f (τ k) i *
              Puncture.zero.cylindricalEndLift (↑R + ↑t * I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u k (equivRealProdCLM
            (Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * I))))) ≤ A) →
      ∃ (φ : ℕ → ℕ) (τ₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ τ₀ ∈ C ∧
        Tendsto (fun n ↦ τ (φ n)) atTop (𝓝 τ₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + (∑ i, B i + Bout) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (φ n)))
            (associativityScale f (τ (φ n))) H Hout (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (φ n)))
            (associativityScale f (τ (φ n))) H Hout (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) :=
  ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere
    (contDiff_associativityCenter f) (contDiff_associativityScale f) hW hJs hH hHs hHout hHouts
    hB hBout hC hD hK hCDKW hJt (fun τ _ ↦ associativityScale_ne_zero hf τ)
    (fun τ _ ↦ pairwise_add_le_norm_associativityCenter_sub hf.le hf₃ τ)
    (fun τ _ ↦ norm_associativityCenter_add_le hf.le (by linarith) τ) hR hDR

end TauCeti.SymplecticForm
