/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Continuation
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Compactness of pairs of pants with continuation necks

Pair-of-pants products for two choices of end Hamiltonians are compared by the family of pairs of
pants `S = ℂ ∖ {0, 1}` with continuation necks on their ends: the Hamiltonian perturbation
`K_L = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L` interpolates, on each end `q`, from
the inner Hamiltonian `G_q` to the outer Hamiltonian `H_q` across a neck at the signed longitudinal
coordinate `L_q`. Moving the neck positions `L = (L_0, L_1, L_∞)` along a path gives the
one-parameter families whose rigid members count the chain homotopy between the two compositions
of continuation maps with pair-of-pants products. Here the neck positions are a point of the
Euclidean space `EuclideanSpace ℝ Puncture`, so that a compact set of them is a compact window of
parameters.

This file proves the interior part of Gromov–Floer compactness for this family over a compact
window `C` of neck positions, for a symplectic vector space target `(V, ω)`, on compact windows
`D ⊆ S` in the real coordinates of `S`. The input is the energy bound of the family
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`):
for `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ Δ_q`, a solution whose end loops have limiting actions
`a_q` has energy at most `a_0 + a_1 - a_∞ + ∑ q, (B_q + Δ_q)`, whatever the neck positions,
although the necks become arbitrarily long. The perturbation is smooth jointly in the neck
positions and the domain and target points
(`TauCeti.Floer.contDiffAt_pairOfPantsContinuationPerturbation_family_apply`), so compactness over
a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies.

The main result, in the namespace `TauCeti.SymplecticForm`,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation`,
allows any almost complex structures `J_L(z, x)` that are jointly `C²` near `C × D × K` and tamed
by `ω` on `S`, which is the form in which domain-dependent structures perturbed for transversality
enter; the structures of the family itself, `TauCeti.Floer.pairOfPantsContinuationAlmostComplex`,
are tame (`TauCeti.Floer.tames_pairOfPantsContinuationAlmostComplex`) and jointly smooth in the
neck positions (`TauCeti.Floer.contMDiffAt_pairOfPantsContinuationAlmostComplex`). It gives a
threshold `δ > 0` such that every sequence of solutions for neck positions `Lₖ ∈ C`, with action
differences `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A` and images of an open `Ω ⊆ D` in a compact `K ⊆ V`, has a
subsequence whose neck positions converge to some `L₀ ∈ C` and which converges locally uniformly on
`Ω` off a finite set `Z` of bubbling points, with `#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`. The regularity
of the limit, the bubbles at the points of `Z`, breaking along the three ends and the long-neck
limit of the family, where some `L_q → ∞`, are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {G H : Puncture → ℝ → V → ℝ}

/-- **Floer pairs of pants with continuation necks converge off finitely many bubbling points.**
Let `K_L` be the pair-of-pants perturbation with continuation necks at the positions `L` from
period-one `C³` inner Hamiltonians `G_q` to outer Hamiltonians `H_q`, with `|G_q|, |H_q| ≤ B_q` and
`|H_q - G_q| ≤ Δ_q`. Let `J_L(z, x)` be almost complex structures depending on the neck positions
`L`, jointly `C²` on an open set `W` containing `C × D × K` and tamed by `ω` on `S = ℂ ∖ {0, 1}` for
`L ∈ C`, where `S` is read in real coordinates, `C` is a compact window of neck positions, and
`D ⊆ S` and `K ⊆ V` are compact. There is a threshold `δ > 0` with the following property. Let
`uₖ` be `C³` solutions of `(du - X_{K_{Lₖ}})^{0,1} = 0` on `S` for `J_{Lₖ}(z, u)`, with `Lₖ ∈ C`,
with limiting end actions `aₖ(q)` satisfying `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A`, and with `uₖ(Ω) ⊆ K` for
an open `Ω ⊆ D`. Then there are a subsequence `φ`, a limit `L₀ ∈ C` of `L_{φ n}`, a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`, and a continuous `v : Ω \ Z → K` such that along `φ`
every disc about a point of `Z` eventually carries energy at least `δ`, the differentials are
uniformly bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on
`Ω \ Z`. -/
theorem
    exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 3 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B Δ : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hΔ : ∀ q t x, |H q t x - G q t x| ≤ Δ q)
    {J : EuclideanSpace ℝ Puncture → ℝ × ℝ → V → AlmostComplexStructure V}
    {W : Set (EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V) ↦
      (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) W)
    {C : Set (EuclideanSpace ℝ Puncture)} {D : Set (ℝ × ℝ)} {K : Set V}
    (hJt : ∀ L ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J L z x))
    (hC : IsCompact C) (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hK : IsCompact K)
    (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → EuclideanSpace ℝ Puncture⦄ ⦃u : ℕ → ℝ × ℝ → V⦄
      ⦃a : ℕ → Puncture → ℝ⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, L k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (L k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
        (fun t ↦ u k (endChart q (q.endSign * σ, t)))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (L₀ : EuclideanSpace ℝ Puncture) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V),
        StrictMono φ ∧ L₀ ∈ C ∧ Tendsto (fun n ↦ L (φ n)) atTop (𝓝 L₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, (B q + Δ q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (φ n)) (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  set S := thricePuncturedSphereReal
  -- The perturbation is jointly smooth in the neck positions and the points of `S × V`.
  have hKfam (v : ℂ) : ContDiffOn ℝ 3 (fun p : EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V) ↦
      pairOfPantsContinuationPerturbation G H p.1 (equivRealProdCLM.symm p.2.1) p.2.2 v)
      (univ ×ˢ (S ×ˢ univ)) := by
    rintro ⟨L, z, x⟩ ⟨-, hz, -⟩
    exact (ContDiffAt.comp (x := (L, z, x))
      (contDiffAt_pairOfPantsContinuationPerturbation_family_apply hG hH hGs hHs (⇑L) hz x v)
      (f := fun p : EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V) ↦ (⇑p.1, p.2))
      ((PiLp.contDiff_ofLp.comp contDiff_fst).prodMk contDiff_snd).contDiffAt).contDiffWithinAt
  have hW' : IsOpen (W ∩ univ ×ˢ (S ×ˢ univ)) :=
    hW.inter (isOpen_univ.prod (isOpen_thricePuncturedSphereReal.prod isOpen_univ))
  have hCDKW' : C ×ˢ (D ×ˢ K) ⊆ W ∩ univ ×ˢ (S ×ˢ univ) := fun p hp ↦
    ⟨hCDKW hp, trivial, hDS hp.2.1, trivial⟩
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun (L : EuclideanSpace ℝ Puncture) z x ↦
      pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
    (Kt := fun (L : EuclideanSpace ℝ Puncture) z x ↦
      pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I)
    hW' ((hKfam 1).mono inter_subset_right) ((hKfam I).mono inter_subset_right)
    (hJ.mono inter_subset_left) hC hD hK hCDKW' fun L hL z hz x _ ↦ hJt L hL z (hDS hz) x
  refine ⟨δ, hδ, fun Ω L u a A hΩ hΩD hLC hu hfl ha hA huK ↦ ?_⟩
  have hΩS : Ω ⊆ S := hΩD.trans hDS
  have hK' (k : ℕ) (v : ℂ) : ContDiffOn ℝ 1 (uncurry fun z x ↦
      pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x v)
      (S ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    exact (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH
      (fun q ↦ (hGs q).of_le (by norm_num)) (fun q ↦ (hHs q).of_le (by norm_num)) (L k) hz x
      v).contDiffWithinAt
  have hJt' (k : ℕ) : ∀ z ∈ S, ω.Tames (J (L k) z (u k z)) := fun z hz ↦ hJt _ (hLC k) z hz _
  -- The action bound `a_∞ ≤ a_0 + a_1 + ∑ q, (B_q + Δ_q)` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + ∑ q, (B q + Δ q) := by
    linarith [hA 0, le_add_add_sum_of_tendsto_hamiltonianAction_pairOfPantsContinuationPerturbation
      ω hG hH (fun q ↦ (hGs q).of_le (by norm_num)) (fun q ↦ (hHs q).of_le (by norm_num)) hGB hHB
      hΔ ((hu 0).of_le (by norm_num)) (hJt' 0) (hfl 0)
      fun q ↦ by simpa only [endChart_mk] using ha 0 q]
  -- Every solution has energy over `S` at most `A + ∑ q, (B_q + Δ_q)`.
  have hE (k : ℕ) := ω.integrableOn_and_setIntegral_floerEnergyDensity_le
    isOpen_thricePuncturedSphereReal ((hu k).of_le (by norm_num)) (hK' k 1) (hK' k I) (hJt' k)
    (hfl k) hE0 ((setLIntegral_le_lintegral _ _).trans <|
      (lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le ω hG hH
        (fun q ↦ (hGs q).of_le (by norm_num)) (fun q ↦ (hHs q).of_le (by norm_num)) hGB hHB hΔ
        (L k) ((hu k).of_le (by norm_num)) (hJt' k) (hfl k) (ha k)).trans
      (ENNReal.ofReal_le_ofReal (by
        simp only [Puncture.sum_univ, Puncture.endSign_zero, Puncture.endSign_one,
          Puncture.endSign_inf]
        linarith [hA k]))) hΩ.measurableSet hΩS
  exact hconv hΩ hΩD hLC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK
    (fun k ↦ (hE k).1) fun k ↦ (hE k).2

end TauCeti.SymplecticForm
