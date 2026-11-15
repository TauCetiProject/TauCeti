/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm

/-!
# Compactness of the capping family of the unit

The unit property of the pair-of-pants product is proved with the capping family: a negative PSS
plane is glued into the input end `1` of the pair of pants `ℂ ∖ {0, 1}` along a neck of length
`L`, and the result is a cylinder with the remaining input at `0` and the output at `∞` as its two
ends. On the standard cylinder `ℝ × ℝ/ℤ`, in the end coordinates of `0`, its Hamiltonian datum is
`TauCeti.Floer.cappedCylinderComponent Hb L`, which is `H_0(t) dt` for `s ≥ 2` and `H_∞(t) dt` for
`s ≤ -3`. This file proves the interior part of Gromov–Floer compactness for this family over a
compact window `C ⊆ (4, ∞)` of neck lengths, for a symplectic vector space target `(V, ω)`.

The inputs are:

* the datum is smooth jointly in the neck length, the cylinder point and the target point
  (`TauCeti.Floer.contDiffOn_cappedCylinderComponent_family`);
* the energy of a Floer solution over one period `ℝ × [0, 1]` of the cylinder is at most
  `a_0 - a_∞ + (B_1 + B_0 + B_1 + B_∞)` when the actions of its loops tend to `a_0` at the input end
  and to `a_∞` at the output end, uniformly in the neck length
  (`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_cappedCylinderComponent_le`);
* a solution of period one in `t` has the same energy over every period, so its energy over a
  compact window of the cylinder covered by `k` periods is at most `k` times its energy over one
  period (`TauCeti.setLIntegral_prod_Ico_intCast_add_natCast`).

The almost complex structures `J_L(z, x)` may be any family which is `C²` jointly in `L`, `z` and
`x` near the window and tamed by `ω` for the neck lengths of the window. Compactness over a compact
parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
then applies on every compact window `D` of the cylinder, and the threshold is divided by the
number of periods meeting `D`, so that the count of bubbling points is bounded by the energy of a
single period.

The main result, in the namespace `TauCeti.SymplecticForm`,
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedCylinder`)
gives a threshold `δ > 0` such that every sequence of solutions of period one in `t`, for neck
lengths `Lₖ ∈ C`, with action differences `a_0 - a_∞` at most `A` and images of an open `Ω ⊆ D` in
a compact `K ⊆ V`, has a subsequence whose neck lengths converge to some `L₀ ∈ C` and which
converges locally uniformly on `Ω` off a finite set `Z` of bubbling points, with
`#Z * δ ≤ A + (B_1 + B_0 + B_1 + B_∞)`. The regularity of the limit, the bubbles at the points of
`Z`, breaking along the two ends of the cylinder and the long-neck end `L → ∞` of the family are
not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Hb : Puncture → ℝ → V → ℝ} {Bb : Puncture → ℝ}

/-- The Floer energy density of a map of period one in `t`, for the capped datum on the cylinder,
has period one in `t`. -/
private theorem floerEnergyDensity_cappedCylinderComponent_add_one (ω : SymplecticForm V) (L : ℝ)
    {u : ℝ × ℝ → V} (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) (s t : ℝ) :
    ω.floerEnergyDensity (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L I) u
        (s, t + 1) =
      ω.floerEnergyDensity (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L I) u
        (s, t) := by
  have hK (v : ℂ) : (fun w : ℝ × ℝ ↦ cappedCylinderComponent Hb L v (w + (0, 1))) =
      cappedCylinderComponent Hb L v :=
    funext fun ⟨a, b⟩ ↦ by simpa using periodic_cappedCylinderComponent Hb L v a b
  have hu : (fun w : ℝ × ℝ ↦ u (w + (0, 1))) = u := funext fun ⟨a, b⟩ ↦ by simpa using hper (a, b)
  have h := ω.floerEnergyDensity_comp_add_right (cappedCylinderComponent Hb L 1)
    (cappedCylinderComponent Hb L I) u (0, 1) (s, t)
  rw [hK, hK, hu] at h
  simpa using h.symm

/-- A bounded subset of `ℝ × ℝ` lies in the `2N` periods `ℝ × [-N, N)` of the cylinder, for some
`N > 0`. -/
private theorem exists_pos_subset_univ_prod_Ico {D : Set (ℝ × ℝ)} (hD : Bornology.IsBounded D) :
    ∃ N : ℕ, 0 < N ∧ D ⊆ (univ : Set ℝ) ×ˢ Ico (-(N : ℝ)) N := by
  obtain ⟨R, hR⟩ := hD.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_gt (max R 0)
  refine ⟨N, Nat.cast_pos.1 ((le_max_right R 0).trans_lt hN), fun z hz ↦ ?_⟩
  have h₂ : |z.2| ≤ R := by
    simpa [Prod.norm_def] using (mem_closedBall_zero_iff.1 (hR hz)).trans' (le_max_right _ _)
  have hRN : R < N := (le_max_left R 0).trans_lt hN
  exact ⟨mem_univ _, by linarith [neg_abs_le z.2], by linarith [le_abs_self z.2]⟩

/-- The Floer energy of a solution of period one in `t` for the capped datum, over the `2N` periods
`ℝ × [-N, N)` of the cylinder, is at most `2N` times the bound
`a₀ - a_∞ + (Bb 1 + ∑ r, Bb r)` of
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_cappedCylinderComponent_le` on one period. -/
private theorem lintegral_floerEnergyDensity_cappedCylinderComponent_Ico_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) {L : ℝ}
    (hL : 4 < L) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L I) u z :
        ℝ × ℝ →ₗ[ℝ] V))
    {a₀ a_inf : ℝ}
    (hinf : Tendsto (fun s ↦ ω.hamiltonianAction (Hb .inf) (fun t ↦ u (s, t))) atBot (𝓝 a_inf))
    (h₀ : Tendsto (fun s ↦ ω.hamiltonianAction (Hb .zero) (fun t ↦ u (s, t))) atTop (𝓝 a₀))
    (N : ℕ) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Ico (-(N : ℝ)) N, ENNReal.ofReal (ω.floerEnergyDensity
        (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L I) u z) ≤
      ENNReal.ofReal (2 * N * (a₀ - a_inf + (Bb .one + ∑ r, Bb r))) := by
  set e := ω.floerEnergyDensity (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L I) u
  have hsplit := setLIntegral_prod_Ico_intCast_add_natCast (g := fun z ↦ ENNReal.ofReal (e z))
    (fun s t ↦ by simp only [e, floerEnergyDensity_cappedCylinderComponent_add_one ω _ hper])
    MeasurableSet.univ (-(N : ℤ)) (2 * N)
  have hends : ((-(N : ℤ) : ℤ) : ℝ) + ((2 * N : ℕ) : ℝ) = N := by push_cast; ring
  rw [hends, Int.cast_neg, Int.cast_natCast] at hsplit
  rw [hsplit, ENNReal.ofReal_mul (by positivity)]
  push_cast
  gcongr
  · rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  refine (lintegral_mono_set (Set.prod_mono le_rfl Ico_subset_Icc_self)).trans ?_
  exact lintegral_floerEnergyDensity_cappedCylinderComponent_le ω hHb hHbs hL hBb isOpen_univ
    (hu.contDiffOn) (subset_univ _) (fun s ↦ by simpa using hper (s, 0)) (fun z _ ↦ hJ z)
    (fun z _ ↦ hfloer z) hinf h₀

/-- **Solutions of the capping family converge off finitely many bubbling points.** Let `Hb` be
period-one `C³` Hamiltonians with `|Hb r| ≤ Bb r`, let `J_L(z, x)` be a family of almost complex
structures on the cylinder which is `C²` jointly in `(L, z, x)` on an open set `W` and tamed by `ω`
for `L` in a compact window `C ⊆ (4, ∞)` of neck lengths, and fix compact sets `D ⊆ ℝ × ℝ` and
`K ⊆ V` with `C × D × K ⊆ W`. There is a threshold `δ > 0` with the following property. Let `uₖ`
be `C³` maps of period one in `t` solving the Floer equation `(du - X_{K_{Lₖ}})^{0,1} = 0` on the
cylinder for the capped datum `K_{Lₖ}` and the structures `J_{Lₖ}(z, u)`, with `Lₖ ∈ C`, whose
loop actions tend to `a₀(k)` at the input end `s → ∞` and to `a_∞(k)` at the output end `s → -∞`,
with `a₀(k) - a_∞(k) ≤ A`, and with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence
`φ`, a limit `L₀ ∈ C` of `L_{φ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + (Bb 1 + ∑ r, Bb r)`,
and a continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually
carries Floer energy at least `δ`, the differentials are uniformly bounded on every compact subset
of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedCylinder
    (ω : SymplecticForm V) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r))) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    {J : ℝ → ℝ × ℝ → V → AlmostComplexStructure V} {W : Set (ℝ × ((ℝ × ℝ) × V))}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2
      (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hC₄ : C ⊆ Ioi 4)
    (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ L ∈ C, ∀ z x, ω.Tames (J L z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a₀ a_inf : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, L k ∈ C) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k (z : ℝ × ℝ), u k (z.1, z.2 + 1) = u k z) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (L k) z (u k z))
        (ω.perturbedFDeriv (cappedCylinderComponent Hb (L k) 1)
          (cappedCylinderComponent Hb (L k) I) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb .inf) (fun t ↦ u k (s, t))) atBot
        (𝓝 (a_inf k))) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction (Hb .zero) (fun t ↦ u k (s, t))) atTop
        (𝓝 (a₀ k))) →
      (∀ k, a₀ k - a_inf k ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (L₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ L₀ ∈ C ∧
        Tendsto (fun n ↦ L (φ n)) atTop (𝓝 L₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + (Bb .one + ∑ r, Bb r) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (cappedCylinderComponent Hb (L (φ n)) 1) (cappedCylinderComponent Hb (L (φ n)) I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- The window `D` lies in `2N` periods `ℝ × [-N, N)` of the cylinder.
  obtain ⟨N, hN₀, hDN⟩ := exists_pos_subset_univ_prod_Ico hD.isBounded
  have h1N : (1 : ℝ) ≤ 2 * N := by linarith [Nat.one_le_cast (α := ℝ) |>.2 hN₀]
  -- Compactness over the window, for the capped data on `(4, ∞) × ((ℝ × ℝ) × V)`.
  have hW' : IsOpen (W ∩ Ioi 4 ×ˢ univ) := hW.inter (isOpen_Ioi.prod isOpen_univ)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun L ↦ cappedCylinderComponent Hb L 1) (Kt := fun L ↦ cappedCylinderComponent Hb L I)
    (J := J) hW' ((contDiffOn_cappedCylinderComponent_family hHb hHbs 1).mono inter_subset_right)
    ((contDiffOn_cappedCylinderComponent_family hHb hHbs I).mono inter_subset_right)
    (hJ.mono inter_subset_left) hC hD hK
    (subset_inter hCDKW (prod_mono hC₄ (subset_univ _))) fun L hL z _ x _ ↦ hJt L hL z x
  refine ⟨δ / (2 * N), by positivity, fun Ω L u a₀ a_inf A hΩ hΩD hLC hu hper hfl hinf h₀ hA huK ↦
    ?_⟩
  set c : ℝ := Bb .one + ∑ r, Bb r
  set e : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (cappedCylinderComponent Hb (L k) 1)
    (cappedCylinderComponent Hb (L k) I) (u k)
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have he0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ e k z :=
    ω.floerEnergyDensity_nonneg (hJt _ (hLC k) z _) (hfl k z)
  have hH1 : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)) := fun r ↦ (hHbs r).of_le (by norm_num)
  -- The energy over `Ω` is at most the energy over the `2N` periods covering `D`.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (e k z) ≤ ENNReal.ofReal (2 * N * (A + c)) :=
    (lintegral_mono_set (hΩD.trans hDN)).trans <|
      (lintegral_floerEnergyDensity_cappedCylinderComponent_Ico_le ω hHb hH1 (hC₄ (hLC k)) hBb
        ((hu k).of_le (by norm_num)) (hper k) (fun z ↦ hJt _ (hLC k) z _) (hfl k) (hinf k) (h₀ k)
        N).trans (ENNReal.ofReal_le_ofReal (by gcongr; linarith [hA k]))
  have hAc : 0 ≤ A + c := by
    have h := le_add_add_sum_of_tendsto_hamiltonianAction_cappedCylinderComponent ω hHb hH1
      (hC₄ (hLC 0)) hBb isOpen_univ ((hu 0).of_le (by norm_num)).contDiffOn (subset_univ _)
      (fun s ↦ by simpa using hper 0 (s, 0)) (fun z _ ↦ hJt _ (hLC 0) z _) (fun z _ ↦ hfl 0 z)
      (hinf 0) (h₀ 0)
    linarith [hA 0]
  have hint (k : ℕ) : IntegrableOn (e k) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_univ ((hu k).of_le (by norm_num)).contDiffOn
        (contDiff_uncurry_cappedCylinderComponent hHb hH1 (hC₄ (hLC k)) 1).contDiffOn
        (contDiff_uncurry_cappedCylinderComponent hHb hH1 (hC₄ (hLC k)) I).contDiffOn).mono
          (subset_univ Ω)).aestronglyMeasurable hΩm,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩm fun z _ ↦ he0 k z)).2
        ((hlin k).trans_lt ENNReal.ofReal_lt_top)⟩
  have hE (k : ℕ) : ∫ z in Ω, e k z ≤ 2 * N * (A + c) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (he0 k)) (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hlin k)
  obtain ⟨φ, L₀, Z, v, hφ, hL₀, hlim, hZΩ, hcard, hconc, hbd, hv⟩ := hconv hΩ hΩD hLC
    (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK hint hE
  -- Dividing the threshold by the number `2N` of periods bounds `#Z` by the energy of one period.
  refine ⟨φ, L₀, Z, v, hφ, hL₀, hlim, hZΩ, ?_, fun z hz ε hε ↦ (hconc z hz ε hε).mono
    fun n hn ↦ (div_le_self hδ.le h1N).trans hn, hbd, hv⟩
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  linarith

end TauCeti.SymplecticForm
