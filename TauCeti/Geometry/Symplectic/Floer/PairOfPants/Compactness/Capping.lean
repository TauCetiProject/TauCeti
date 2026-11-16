/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Compactness of the capping family

The unit of the pair-of-pants product is the count of negative PSS planes, and its unit property
is proved with the *capping family*: plumbing the negative plane with Hamiltonian `H_1` and end
structure `J_1` into the input end at `1` of the pair of pants `S = ℂ ∖ {0, 1}` with Hamiltonians
`H_0`, `H_1`, `H_∞` and end structures `J_0`, `J_1`, `J_∞`, along a neck of length `L`, gives the
datum `K_L = TauCeti.Floer.plumbedPerturbation (Pi.single ∞ H_1) H 1 L` and structures `J_L`
(`TauCeti.Floer.plumbedAlmostComplex`, over a compatible base structure `J₀` on both pieces) on
the capped plane `ℂ ∖ {0}`, a cylinder with the remaining input at `0` and the output at `∞`.

This file proves the interior part of Gromov–Floer compactness for this family over a compact
window `C ⊆ (4, ∞)` of neck lengths, for a symplectic vector space target `(V, ω)`, on compact
windows `D` of the capped plane, in real coordinates. The capped puncture `1` is an interior point
of the capped plane, where `K_L` vanishes and `J_L` is `J₀`.

The inputs are:

* the energy bound of the family
  (`TauCeti.SymplecticForm.setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le`): for
  `|H_r| ≤ B_r`, a solution whose loops in the coordinates of the end at `0` have limiting actions
  `a₀` for `H_0` as `s → ∞` and `a_∞` for `H_∞` as `s → -∞` has Floer energy at most
  `a₀ - a_∞ + B_1 + (B_0 + B_1 + B_∞)` over every compact window of the capped plane, for every
  neck length `L > 4`;
* the joint smoothness of `K_L` and `J_L` in `L`, the domain point and the target point
  (`TauCeti.Floer.contDiffAt_uncurry_plumbedPerturbation_single_inf_family`,
  `TauCeti.Floer.contMDiffAt_plumbedAlmostComplex_update_inf`), with `J_L` tamed by `ω`;
* compactness over a compact parameter window
  (`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`).

The main result, in the namespace `TauCeti.SymplecticForm`,
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_capping`) takes any family
`J_L(z, x)` of structures that is `C²` jointly in `(L, z, x)` near `C × D × K` and tamed by `ω` on
the capped plane for `L ∈ C`. It gives a threshold `δ > 0` such that every sequence of solutions
for neck lengths `Lₖ ∈ C`, with action differences `a₀ - a_∞ ≤ A` and images of an open `Ω ⊆ D` in
a compact `K ⊆ V`, has a subsequence whose neck lengths converge to some `L₀ ∈ C` and which
converges locally uniformly on `Ω` off a finite set `Z` of bubbling points, with
`#Z * δ ≤ A + B_1 + (B_0 + B_1 + B_∞)`.
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappingAlmostComplex`
applies it to the structures of the capping family. The regularity of the limit, the bubbles at
the points of `Z`, breaking at the two ends and the long-neck end `L → ∞` of the family are not
treated here.

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

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Hb : Puncture → ℝ → V → ℝ}

/-- **Solutions of the capping family converge off finitely many bubbling points.** Let `Hb` be
period-one `C³` Hamiltonians with `|Hb r| ≤ Bb r`. Fix compact sets `C ⊆ (4, ∞)` of neck lengths,
`D` in the capped plane `ℂ ∖ {0}`, in real coordinates, and `K ⊆ V`. Let `J_L(z, x)` be a family of
structures that is `C²` jointly in the neck length `L`, the point `z` and `x ∈ V` on an open set
`W` containing `C × D × K`, and tamed by `ω` for `L ∈ C` and `z` in the capped plane. There is a
threshold `δ > 0` with the following property.
Let `uₖ` be `C³` maps on the capped plane solving the Floer equation `(du - X_{K_{Lₖ}})^{0,1} = 0`
for the structures `J_{Lₖ}(z, u)` and the datum `K_{Lₖ}` obtained by plumbing the negative plane
with Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with Hamiltonians `Hb`,
along a neck of length `Lₖ ∈ C`. Suppose that in the coordinates `(s, t)` of the end at `0` the
actions for `Hb 0` of the loops of `uₖ` tend to `a₀ₖ` as `s → ∞` and their actions for `Hb ∞` tend
to `a_∞ₖ` as `s → -∞`, with `a₀ₖ - a_∞ₖ ≤ A`, and that `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there
are a subsequence `φ`, a limit `L₀ ∈ C` of `L_{φ n}`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + Bb 1 + ∑ r, Bb r`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc
about a point of `Z` eventually carries Floer energy at least `δ`, the differentials are uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_capping
    (ω : SymplecticForm V) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r))) {Bb : Puncture → ℝ}
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {J : ℝ → ℝ × ℝ → V → AlmostComplexStructure V}
    {W : Set (ℝ × ((ℝ × ℝ) × V))} {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2
      (fun p : ℝ × ((ℝ × ℝ) × V) ↦ (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hC₄ : C ⊆ Ioi 4) (hD : IsCompact D)
    (hDS : ∀ z ∈ D, equivRealProdCLM.symm z ≠ 0) (hK : IsCompact K)
    (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ L ∈ C, ∀ z, equivRealProdCLM.symm z ≠ 0 → ∀ x, ω.Tames (J L z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a₀ a_inf : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, L k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) {z | equivRealProdCLM.symm z ≠ 0}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 0 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (L k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero)
        (fun t ↦ u k (endChart zero (s, t)))) atTop (𝓝 (a₀ k))) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf)
        (fun t ↦ u k (endChart zero (s, t)))) atBot (𝓝 (a_inf k))) →
      (∀ k, a₀ k - a_inf k ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (L₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ L₀ ∈ C ∧
        Tendsto (fun n ↦ L (φ n)) atTop (𝓝 L₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + Bb one + ∑ r, Bb r ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  set S : Set (ℝ × ℝ) := {z | equivRealProdCLM.symm z ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun equivRealProdCLM.symm.continuous continuous_const
  have hW' : IsOpen (W ∩ Ioi (4 : ℝ) ×ˢ (S ×ˢ (univ : Set V))) :=
    hW.inter (isOpen_Ioi.prod (hS.prod isOpen_univ))
  -- The capped datum, read in real coordinates, is smooth jointly in the neck length.
  have hKf (v : ℂ) : ContDiffOn ℝ 3 (fun p : ℝ × ((ℝ × ℝ) × V) ↦ plumbedPerturbation
      (Pi.single inf (Hb one)) Hb one p.1 (equivRealProdCLM.symm p.2.1) p.2.2 v)
      (W ∩ Ioi 4 ×ˢ (S ×ˢ univ)) := by
    rintro ⟨L, z, x⟩ ⟨-, hL, hz, -⟩
    exact (contDiffAt_uncurry_plumbedPerturbation_single_inf_family (by simp) hHb hHbs hL
      (eq_endCenter_one_or_of_ne_zero hz) x v).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun L z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (equivRealProdCLM.symm z) x 1)
    (Kt := fun L z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (equivRealProdCLM.symm z) x I)
    hW' (hKf 1) (hKf I) (hJ.mono inter_subset_left) hC hD hK
    (subset_inter hCDKW (prod_mono hC₄ (prod_mono hDS (subset_univ K))))
    fun L hL z hz x _ ↦ hJt L hL z (hDS z hz) x
  refine ⟨δ, hδ, fun Ω L u a₀ a_inf A hΩ hΩD hLC hu hfl h₀ hinf hA huK ↦ ?_⟩
  have hΩS : Ω ⊆ S := fun z hz ↦ hDS z (hΩD hz)
  -- The Floer energy density is continuous on the capped plane, hence integrable on `D`.
  have hEc (k : ℕ) : ContinuousOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
        (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
        (equivRealProdCLM.symm z) x I) (u k)) S :=
    ω.continuousOn_floerEnergyDensity_plumbedPerturbation_single_inf hHb
      (fun r ↦ (hHbs r).of_le (by norm_num)) (hC₄ (hLC k)) ((hu k).of_le (by norm_num))
  have hintD (k : ℕ) : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
        (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
        (equivRealProdCLM.symm z) x I) (u k)) D :=
    ((hEc k).mono hDS).integrableOn_compact hD
  -- The energy over `Ω` is at most the energy over `D`, hence at most `A + Bb 1 + ∑ r, Bb r`.
  refine hconv hΩ hΩD hLC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK
    (fun k ↦ (hintD k).mono_set hΩD) fun k ↦ ?_
  have hE := setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le ω hHb
    (fun r ↦ (hHbs r).of_le (by norm_num)) (hC₄ (hLC k)) hBb ((hu k).of_le (by norm_num))
    (fun z hz ↦ hJt _ (hLC k) z hz _) (hfl k) (h₀ k) (hinf k) hD hDS
  refine (ω.setIntegral_floerEnergyDensity_mono_set hΩD hD.isClosed.measurableSet (hintD k)
    (fun z hz ↦ hJt _ (hLC k) z (hDS z hz) _) fun z hz ↦ hfl k z (hDS z hz)).trans ?_
  linarith [hA k]

/-- **Solutions of the capping family converge off finitely many bubbling points**, for the
structures of the capping family. Let `J₀` be `ω`-compatible and let `Jb r (t, x)` be period-one
`C²` families of `ω`-tame structures on the three ends, and let the structures `J_L` be obtained by
plumbing the negative plane with end structure `Jb 1` into the input end at `1` of the pair of
pants with end structures `Jb`, along a neck of length `L`, over the base structure `J₀`. Then the
conclusion of
`SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_capping`
holds for the solutions of the Floer equations of the capping family `(K_L, J_L)`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappingAlmostComplex
    (ω : SymplecticForm V) {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {Jb : Puncture → ℝ → V → AlmostComplexStructure V} (hJb : ∀ r t x, ω.Tames (Jb r t x))
    (hJbp : ∀ r, Periodic (Jb r) 1)
    (hJbs : ∀ r, ContDiff ℝ 2 fun p : ℝ × V ↦ (Jb r p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r)))
    {Bb : Puncture → ℝ} (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hC₄ : C ⊆ Ioi 4)
    (hD : IsCompact D) (hDS : ∀ z ∈ D, equivRealProdCLM.symm z ≠ 0) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a₀ a_inf : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, L k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) {z | equivRealProdCLM.symm z ≠ 0}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 0 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ ↦ J₀) inf (Jb one)) Jb
            (tames_update_inf h₀.tames (hJb one)) hJb one (L k) (equivRealProdCLM.symm z)
            (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero)
        (fun t ↦ u k (endChart zero (s, t)))) atTop (𝓝 (a₀ k))) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf)
        (fun t ↦ u k (endChart zero (s, t)))) atBot (𝓝 (a_inf k))) →
      (∀ k, a₀ k - a_inf k ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (L₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ L₀ ∈ C ∧
        Tendsto (fun n ↦ L (φ n)) atTop (𝓝 L₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + Bb one + ∑ r, Bb r ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  refine ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_capping hHb hHbs
    hBb (J := fun L z x ↦ plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ ↦ J₀) inf (Jb one)) Jb
      (tames_update_inf h₀.tames (hJb one)) hJb one L (equivRealProdCLM.symm z) x)
    (isOpen_Ioi.prod ((isOpen_ne_fun equivRealProdCLM.symm.continuous continuous_const).prod
      isOpen_univ)) ?_ hC hC₄ hD hDS hK (prod_mono hC₄ (prod_mono hDS (subset_univ K)))
    fun _ _ _ _ _ ↦ tames_plumbedAlmostComplex h₀ h₀ _ _
  -- The structures of the family, read in real coordinates, are smooth jointly in the neck length.
  rintro ⟨L, z, x⟩ ⟨hL, hz, -⟩
  have hfam := contMDiffAt_plumbedAlmostComplex_update_inf h₀ (n := 2) (q := one)
    (hJa := tames_update_inf h₀.tames (hJb one)) (hJb := hJb) (by simp) hJbp
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hJbs r).contMDiff) hL
    (eq_endCenter_one_or_of_ne_zero hz) x
  exact (hfam.comp (L, z, x)
    contMDiff_prodMap_equivRealProdCLM_symm.contMDiffAt).contDiffAt.contDiffWithinAt

end TauCeti.SymplecticForm
