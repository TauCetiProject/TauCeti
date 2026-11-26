/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Continuation

/-!
# Compactness of the pair-of-pants continuation family in a closed manifold

Pair-of-pants products for two choices of end Hamiltonians are compared by gluing continuation
cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The Floer data of this gluing are the
perturbations `K_L = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`, with continuation
necks at the positions `L_q` from the inner Hamiltonians `G_q` to the outer ones `H_q`, together
with almost complex structures `J_L`. Moving the neck positions along a path gives the
one-parameter families whose broken ends are the two compositions of continuation maps with
pair-of-pants products. This file proves the interior part of Gromov–Floer compactness for the
solutions of such families in a closed manifold `M`, uniformly over a compact window of
parameters, with no condition on where the solutions take their values. The theorems of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Continuation` assume instead that the
images stay in a compact subset of one symplectic chart.

The neck positions are given by a `C³` map `L : P → (Puncture → ℝ)` on a finite-dimensional real
normed space `P` of parameters, such as a path `P = ℝ` or the whole space of neck positions
`P = Puncture → ℝ`. The compactness theorem over a compact parameter window in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in
the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
applies once its hypotheses are checked for the family.

* **The data in the charts of `M`.** The perturbations are smooth jointly in the neck positions,
  the domain point of `S` and the target point
  (`TauCeti.Floer.contMDiffAt_pairOfPantsContinuationPerturbation`), so their Hamiltonian vector
  fields read in the chart at any point of `M` are `C²` in `(p, z, y)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`).
* **The energy bound.** If `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ Δ_q`, then whatever the neck
  positions, the Floer energy over any part of `S` exceeds the topological energy
  `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` by at most `∑ q, (B_q + Δ_q)`
  (`IsNondegenerate.setIntegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le` in the
  namespace `TauCeti.SmoothTwoForm`), although the necks become arbitrarily long.
* **The almost complex structures of the family.** The structures
  `TauCeti.SmoothTwoForm.Compatible.pairOfPantsContinuationAlmostComplex` of the family, built from
  a compatible base structure and period-one `C²` inner and outer end structures, are defined at
  the points of `S`. On the open set of parameters and points of `S` they are `C²` jointly with
  the target point
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_pairOfPantsContinuationAlmostComplex`, applied on
  that open set), hence `C²` read in the charts of `M`
  (`TauCeti.Floer.contDiffOn_almostComplexInChartAt_almostComplexStructureAt`), and they are tame.

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pantsContinuation`:
  for any family `J_p(z, x)` of tame structures which is `C²` read in the charts of `M` near the
  parameter and domain windows, there is a threshold `δ > 0` such that every sequence of solutions
  for parameters `pₖ` in a compact window `C ⊆ P`, with topological energy at most `A`, has a
  subsequence whose parameters converge to some `p₀ ∈ C` and which converges on an open `Ω ⊆ D`
  off a finite set `Z` of bubbling points, with `#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`.

In the namespace `TauCeti.SmoothTwoForm.Compatible`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pantsContinuation`
  is the same for the almost complex structures of the family.

The regularity of the limit, the bubbles at the points of `Z`, and breaking along the three ends
and along the necks are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Bundle Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E Y M F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace Y M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {ω : SmoothTwoForm I M} {G H : Puncture → ℝ → M → ℝ} {e : M → F}

namespace IsNondegenerate

/-- **Solutions of the pair-of-pants continuation family in a closed manifold converge off finitely
many bubbling points.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `G_q`,
`H_q` be period-one `C³` Hamiltonians with `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ Δ_q`, and let
`K_{L(p)}` be the perturbations with continuation necks from `G_q` to `H_q` at the neck positions
`L(p)`, for a `C³` map `L` on a finite-dimensional space `P` of parameters. Let `J_p(z, x)` be
structures on the tangent spaces of `M`, tamed by `ω` for `p` in a compact window `C ⊆ P` and
`z ∈ S = ℂ ∖ {0, 1}` (in real coordinates), which read in the chart at every point of `M` are `C²`
jointly in `(p, z, y)` on `W × (chart target)`, for an open `W` containing `C × D` with `D ⊆ S`
compact. Let `e : M → F` be injective and differentiable, with the structures uniformly tame with
respect to `e` over `C × D`, `κ ‖d e v‖² ≤ ω(v, J_p(z) v)` with `κ > 0`, and the pushforwards
through `e` of the Hamiltonian vector fields of the two components of `K_{L(p)}` at most `L'`
there. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps from `S` to
`M` solving the Floer equation `(du - X_{K_{L(pₖ)}})^{0,1} = 0` for the structures `J_{pₖ}(z, u)`,
with `pₖ ∈ C`, whose end loops converge pointwise to loops `xₖ q`, whose Floer energy and
symplectic area densities are integrable over `S`, and whose topological energy
`∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ q t) dt` is at most `A`, and let `Ω ⊆ D` be open. Then there are
a subsequence `φ`, a limit `p₀ ∈ C` of the parameters `p_{φ n}` and a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + ∑ q, (B_q + Δ_q)` such that, along `φ`, every disc about a point of `Z` eventually
carries energy at least `δ`, the energy densities are uniformly bounded on every compact subset of
`Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous map `v`, locally uniformly after
applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pantsContinuation
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B Δ : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hΔ : ∀ q t x, |H q t x - G q t x| ≤ Δ q) {L : P → Puncture → ℝ} (hL : ContDiff ℝ 3 L)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × (ℝ × ℝ))} {C : Set P} {D : Set (ℝ × ℝ)} (hW : IsOpen W) (hC : IsCompact C)
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J p z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L' : ℝ} (hκ : 0 < κ)
    (hJc : ∀ p ∈ C, ∀ z ∈ D, ∀ x v,
      κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p z x v))
    (hLs : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) y 1)
        x)‖ ≤ L')
    (hLt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) y
        Complex.I) x)‖ ≤ L') :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦
              pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k))
              (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x
          Complex.I) (u k)) thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p₀ ∈ C, Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, (B q + Δ q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (p (φ n))) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L'', IsCompact L'' → L'' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L'', ω.floerEnergyDensity
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (p (φ n))) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  set S := thricePuncturedSphereReal
  -- Each component `(p, z) ↦ K_{L(p)}(z)(w)` of the perturbations is `C³` jointly in the parameter,
  -- the domain point of `S` and the target point, so its Hamiltonian vector field is `C²` in
  -- every chart.
  have hg : ContMDiff (𝓘(ℝ, P × (ℝ × ℝ)).prod I) (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod I)) 3
      (fun p : (P × (ℝ × ℝ)) × M ↦ (L p.1.1, (equivRealProdCLM.symm p.1.2, p.2))) :=
    ((hL.comp contDiff_fst).contMDiff.comp contMDiff_fst).prodMk
      (((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst).prodMk
        contMDiff_snd)
  have hK (w : ℂ) (p : P × (ℝ × ℝ)) (hp : p ∈ univ ×ˢ S) (x : M) :
      ContMDiffAt (𝓘(ℝ, P × (ℝ × ℝ)).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
        (uncurry fun (p : P × (ℝ × ℝ)) x ↦
          pairOfPantsContinuationPerturbation G H (L p.1) (equivRealProdCLM.symm p.2) x w)
        (p, x) :=
    (((contMDiffAt_pairOfPantsContinuationPerturbation hG hH hGs hHs (L p.1)
      ⟨equivRealProdCLM.symm p.2, hp.2⟩ x).comp (p, x) hg.contMDiffAt).clm_apply
        contMDiffAt_const).of_le (by norm_num)
  have hWS : IsOpen (W ∩ univ ×ˢ S) := hW.inter (isOpen_univ.prod isOpen_thricePuncturedSphereReal)
  have hCDWS : C ×ˢ D ⊆ W ∩ univ ×ˢ S :=
    subset_inter hCDW (prod_mono (subset_univ _) hDS)
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun p z x ↦
        pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) x 1)
      (Kt := fun p z x ↦
        pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) x Complex.I)
      he he_inj hWS hC hD hCDWS
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).mono
        (prod_mono inter_subset_right subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).mono
        (prod_mono inter_subset_right subset_rfl))
      (fun p hp z hz ↦ hJt p hp z (hDS hz)) hκ hJc hLs hLt
  refine ⟨δ, hδ, fun Ω p u x A hΩ hΩD hpC hu hfl hx hint harea htop ↦ ?_⟩
  have hΩS : Ω ⊆ S := hΩD.trans hDS
  -- The Floer energy over `Ω` is at most the energy over `S`, which exceeds the topological energy
  -- by at most `∑ q, (B_q + Δ_q)`, whatever the neck positions.
  exact hconv hΩ hΩD hpC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz))
    (fun k ↦ (hint k).mono_set hΩS) fun k ↦
      hω.setIntegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le hG hH
        (fun q ↦ (hGs q).of_le (by norm_num)) (fun q ↦ (hHs q).of_le (by norm_num)) hGB hHB hΔ
        ((hu k).of_le (by norm_num)) (hx k) (hint k) (harea k)
        (fun z hz ↦ hJt _ (hpC k) z hz _) (hfl k) (htop k) hΩS

end IsNondegenerate

namespace Compatible

variable {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}

omit [I.Boundaryless] [CompactSpace M] [FiniteDimensional ℝ P] in
/-- Let `J_{(p, z)}` be structures on `M` indexed by parameters `p` and points `z` of the plane,
equal at every `z ∈ S` to the structure of the continuation family at the neck positions `L(p)`,
for a `C²` map `L`. Then `J` is `C²` jointly in `(p, z, x)` at every point with `z ∈ S`. -/
private theorem contMDiffAt_of_eq_pairOfPantsContinuationAlmostComplex (h₀ : σ.Compatible J₀)
    (J₁ J₂ : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ₁ : ∀ q t, σ.Tames (J₁ q t)) (hJ₂ : ∀ q t, σ.Tames (J₂ q t))
    (hJ₁p : ∀ q, Periodic (J₁ q) 1) (hJ₂p : ∀ q, Periodic (J₂ q) 1)
    (hJ₁s : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₁ q p.1).toEndomorphism p.2)))
    (hJ₂s : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₂ q p.1).toEndomorphism p.2)))
    {L : P → Puncture → ℝ} (hL : ContDiff ℝ 2 L)
    {Jf : P × (ℝ × ℝ) → SmoothAlmostComplexStructure I M}
    (hJf : ∀ q (hq : q.2 ∈ thricePuncturedSphereReal),
      Jf q = h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L q.1)
        ⟨equivRealProdCLM.symm q.2, hq⟩)
    {q : P × (ℝ × ℝ)} (hq : q.2 ∈ thricePuncturedSphereReal) (x : M) :
    ContMDiffAt (𝓘(ℝ, P × (ℝ × ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (2 : ℕ∞)
      (fun y : (P × (ℝ × ℝ)) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) y.2
        ((Jf y.1).toEndomorphism y.2)) (q, x) := by
  -- On the open set `U` of points `((p, z), x)` with `z ∈ S`, the family is that of
  -- `contMDiff_pairOfPantsContinuationAlmostComplex`.
  let U : TopologicalSpace.Opens ((P × (ℝ × ℝ)) × M) :=
    ⟨{y | y.1.2 ∈ thricePuncturedSphereReal},
      isOpen_thricePuncturedSphereReal.preimage (continuous_snd.comp continuous_fst)⟩
  have hU : ContMDiff (𝓘(ℝ, P × (ℝ × ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y : U ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) y.val.2
        ((Jf y.val.1).toEndomorphism y.val.2)) :=
    (h₀.contMDiff_pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ hJ₁p hJ₂p hJ₁s hJ₂s
      (L := fun y : U ↦ L y.val.1.1) (f := fun y : U ↦ equivRealProdCLM.symm y.val.1.2)
      (b := fun y : U ↦ y.val.2)
      (((hL.comp contDiff_fst).contMDiff.comp contMDiff_fst).comp contMDiff_subtypeVal)
      (((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst).comp
        contMDiff_subtypeVal)
      (contMDiff_snd.comp contMDiff_subtypeVal) fun y ↦ y.property).congr fun y ↦ by
        rw [hJf _ y.property]
  exact (contMDiffAt_subtype_iff (U := U) (x := ⟨(q, x), hq⟩)).1 (hU _)

/-- **Solutions of the pair-of-pants continuation family in a closed manifold converge off finitely
many bubbling points, for the structures of the family.** Let `σ` be a two-form on a closed
manifold `M` compatible with a smooth almost complex structure `J₀`, and let the inner and outer
end structures `J₁ q t`, `J₂ q t` be tamed by `σ`, of period one in `t` and jointly `C²` on
`ℝ × M`. Take the structures `TauCeti.SmoothTwoForm.Compatible.pairOfPantsContinuationAlmostComplex`
of the family at the neck positions `L(p)`, and otherwise the hypotheses of
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pantsContinuation` in
the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, for a compact window `C ⊆ P` of parameters
and a compact window `D ⊆ S`: the structures of the family are tame and regular in the charts of
`M`, so only the uniform tameness with respect to `e` and the bound on the Hamiltonian vector
fields remain as hypotheses. Then there is a threshold `δ > 0` such that every sequence of
solutions for parameters in `C` with topological energy at most `A` has a subsequence whose
parameters converge in `C` and which converges on an open `Ω ⊆ D` off a finite set `Z` of
bubbling points, with `#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pantsContinuation
    (h₀ : σ.Compatible J₀) (J₁ J₂ : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ₁ : ∀ q t, σ.Tames (J₁ q t)) (hJ₂ : ∀ q t, σ.Tames (J₂ q t))
    (hJ₁p : ∀ q, Periodic (J₁ q) 1) (hJ₂p : ∀ q, Periodic (J₂ q) 1)
    (hJ₁s : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₁ q p.1).toEndomorphism p.2)))
    (hJ₂s : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₂ q p.1).toEndomorphism p.2)))
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B Δ : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hΔ : ∀ q t x, |H q t x - G q t x| ≤ Δ q) {L : P → Puncture → ℝ} (hL : ContDiff ℝ 3 L)
    {C : Set P} {D : Set (ℝ × ℝ)} (hC : IsCompact C) (hD : IsCompact D)
    (hDS : D ⊆ thricePuncturedSphereReal)
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L' : ℝ} (hκ : 0 < κ)
    (hJc : ∀ p ∈ C, ∀ z (hz : z ∈ D), ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L p)
        ⟨equivRealProdCLM.symm z, hDS hz⟩ x v))
    (hLs : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) y 1)
        x)‖ ≤ L')
    (hLt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) y
        Complex.I) x)‖ ≤ L') :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k z (hz : z ∈ thricePuncturedSphereReal),
        IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          ((h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L (p k))
            ⟨equivRealProdCLM.symm z, hz⟩).almostComplexStructureAt (u k z))
          (σ.perturbedMFDeriv
            (fun z x ↦
              pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k))
              (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (σ.floerEnergyDensity
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x
          Complex.I) (u k)) thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p₀ ∈ C, Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, (B q + Δ q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, σ.floerEnergyDensity
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (p (φ n))) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L'', IsCompact L'' → L'' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L'', σ.floerEnergyDensity
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (p (φ n))) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  classical
  have hω := h₀.isNondegenerate
  set S := thricePuncturedSphereReal
  -- The structures of the family are defined at the points of `S`; extend them by `J₀`.
  let Jf : P × (ℝ × ℝ) → SmoothAlmostComplexStructure I M := fun q ↦
    if hq : q.2 ∈ S then
      h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L q.1) ⟨equivRealProdCLM.symm q.2, hq⟩
    else J₀
  have hJf {q : P × (ℝ × ℝ)} (hq : q.2 ∈ S) :
      Jf q = h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L q.1)
        ⟨equivRealProdCLM.symm q.2, hq⟩ :=
    dite_eq_left hq
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pantsContinuation
      (J := fun p z ↦ (Jf (p, z)).almostComplexStructureAt) hG hH hGs hHs hGB hHB hΔ hL
      (isOpen_univ.prod isOpen_thricePuncturedSphereReal) hC hD hDS
      (prod_mono (subset_univ C) hDS)
      (contDiffOn_almostComplexInChartAt_almostComplexStructureAt (n := 2) (J := Jf)
        fun q hq ↦ contMDiffAt_of_eq_pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ hJ₁p
          hJ₂p hJ₁s hJ₂s (hL.of_le (by norm_num)) (fun _ ↦ hJf) hq.2)
      (fun p _ z hz x ↦ hω.tames_iff.1
        (by rw [hJf (q := (p, z)) hz]
            exact h₀.tames_pairOfPantsContinuationAlmostComplex _ _ _ _ _ _) x)
      he he_inj hκ
      (fun p hp z hz x v ↦ by
        simpa only [hJf (q := (p, z)) (hDS hz), IsNondegenerate.symplecticFormAt_apply,
          SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hJc p hp z hz x v)
      hLs hLt
  exact ⟨δ, hδ, fun Ω p u x A hΩ hΩD hpC hu hfl ↦ hconv hΩ hΩD hpC hu fun k z hz ↦ by
    simpa only [hJf (q := (p k, z)) hz] using hfl k z hz⟩

end Compatible

end TauCeti.SmoothTwoForm
