/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Limit
import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# Limits of Floer trajectories are Floer trajectories

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H` a `C²` Hamiltonian and `J_t(x)` a
`C¹` family of almost complex structures, both `1`-periodic in time. Let `u_k` be smooth Floer
trajectories, solutions of `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` with `1`-periodic loops, whose
derivatives are bounded on compact sets uniformly in `k`. When a breaking sequence of
trajectories converges, its translates converge locally uniformly to the *levels* of the broken
limit (`TauCeti.Geometry.Symplectic.Floer.Trajectory.Breaking`,
`TauCeti.Geometry.Symplectic.Floer.Trajectory.BrokenLimit`). There the trajectories need only be
`C²` or `C³`, and the levels are only continuous limits. This file shows that a locally uniform
limit `g` of *smooth* Floer trajectories as above is again a Floer trajectory, and computes its
energy; so it applies to the levels of a breaking sequence of smooth trajectories.

* **Regularity.** By periodicity the Floer equation of a trajectory on the fundamental strip
  `ℝ × [0, 1]` holds on the whole plane
  (`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_of_periodic`), and the convergence
  of the derivatives of Floer solutions
  (`TauCeti.SymplecticForm.tendstoLocallyUniformlyOn_fderiv_of_floer`) shows that `g` is
  `C¹`, that `du_k → dg` locally uniformly, and that `g` solves the Floer equation
  (`TauCeti.SymplecticForm.tendstoLocallyUniformly_fderiv_of_floer_of_periodic`).
* **Energy of windows.** The loops of the `u_k` converge in `C¹` to those of `g`, so their actions
  converge (`TauCeti.SymplecticForm.tendsto_hamiltonianAction` and
  `TauCeti.SymplecticForm.tendsto_hamiltonianAction_slice_of_tendstoLocallyUniformly`), and the
  energy densities converge uniformly on compact windows. Passing to the limit in the energy
  identity of the `u_k` gives the energy identity
  `∫_{[a, b] × [0, 1]} E(g) = A_H(g(b, ·)) - A_H(g(a, ·))` for `g`, although `g` is only known to
  be `C¹`
  (`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub_of_tendsto`).
* **Energy of a level.** If the `u_k` are moreover `L`-Lipschitz, then `‖dg‖ ≤ L`, and if the
  loops of `g` converge uniformly to closed `C¹` loops `x₀` as `s → -∞` and `x₁` as `s → ∞`, such
  as the orbits at which consecutive levels of a broken limit meet, then the actions of the loops
  of `g` converge to `A_H(x₀)` and `A_H(x₁)`
  (`TauCeti.SymplecticForm.tendsto_hamiltonianAction_slice_of_tendstoUniformly`, from
  `TauCeti.SymplecticForm.tendsto_hamiltonianAction_sub_hamiltonianAction`). If moreover `J` is
  tamed by `ω` along `g`, so that the energy density of `g` is nonnegative, then the energy of `g`
  is `A_H(x₁) - A_H(x₀)`
  (`setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub_of_tendstoUniformly`).

The results here do not sum the energies of the levels of a broken limit. Showing that no energy
is lost along the necks, i.e. that these energies add up to the energy of each trajectory, would
in addition need taming of `J` along every level, `C¹` neck orbits, uniform end convergence of
the first and last levels, the energy identity for the `u_k` themselves, and consecutive levels
meeting at an orbit rather than being translates of each other; this is not formalized here.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547, on the convergence of sequences of trajectories to broken trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on compactness up to breaking.
* M. Audin and M. Damian, *Morse theory and Floer homology*, Springer Universitext (2014),
  Chapter 9, on the compactness of spaces of Floer trajectories.
-/

public section

open Set Filter Topology Function MeasureTheory
open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V}
  {W : Set (ℝ × V)} {u : ℕ → ℝ × ℝ → V} {g : ℝ × ℝ → V}

/-- **Limits of Floer trajectories are Floer trajectories.** Let `H` be a `C²` Hamiltonian and
`J_t(x)` a family of almost complex structures, `C¹` on an open set `W ⊆ ℝ × V`, both `1`-periodic
in time. Let `u_k` be smooth solutions of the Floer equation
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on the strip `ℝ × [0, 1]` with `1`-periodic loops, whose
derivatives are bounded on each compact set uniformly in `k`, and which converge pointwise to a map
`g` with `(t, g(s, t)) ∈ W`. Then `g` is `C¹`, the derivatives of the `u_k` converge locally
uniformly to that of `g`, and `g` solves the Floer equation at every point. -/
theorem tendstoLocallyUniformly_fderiv_of_floer_of_periodic (hH : ContDiff ℝ 2 (uncurry H))
    (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hu : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hbd : ∀ C, IsCompact C → ∃ M, ∀ k, ∀ z ∈ C, ‖fderiv ℝ (u k) z‖ ≤ M)
    (hgW : ∀ z, (z.2, g z) ∈ W) (hlim : ∀ z, Tendsto (fun k ↦ u k z) atTop (𝓝 (g z))) :
    ContDiff ℝ 1 g ∧ TendstoLocallyUniformly (fun k ↦ fderiv ℝ (u k)) (fderiv ℝ g) atTop ∧
      ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (g z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) g z : ℝ × ℝ →ₗ[ℝ] V) := by
  -- The data `J_t(x)` and `H_t` are read as data on `(ℝ × ℝ) × V` through `((s, t), x) ↦ (t, x)`.
  have hp : ContDiff ℝ 1 fun q : (ℝ × ℝ) × V ↦ (q.1.2, q.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  obtain ⟨hg, hconv, heq⟩ := ω.tendstoLocallyUniformlyOn_fderiv_of_floer (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) (J := fun z ↦ J z.2) (hW.preimage hp.continuous) contDiffOn_const
    (contDiff_uncurry_cylindrical hH).contDiffOn (hJ.comp hp.contDiffOn fun _ h ↦ h)
    isOpen_univ (fun z _ ↦ hgW z) (fun k ↦ (hu k).contDiffOn)
    (fun k z _ ↦ isComplexLinearMap_perturbedFDeriv_of_periodic hHper hJper isOpen_univ
      (fun s _ ↦ hper k s) (hfloer k) (z := z) ⟨mem_univ _, mem_univ _⟩)
    (fun C hC _ ↦ hbd C hC) fun z _ ↦ hlim z
  exact ⟨contDiffOn_univ.1 hg, tendstoLocallyUniformlyOn_univ.1 hconv, fun z ↦ heq z (mem_univ z)⟩

/-- **The energy identity for limits of Floer trajectories.** In the situation of
`TauCeti.SymplecticForm.tendstoLocallyUniformly_fderiv_of_floer_of_periodic`, suppose that the
`u_k` converge to `g` locally uniformly. Then for `a ≤ b` the Floer energy of the `C¹` limit `g`
over the rectangle `[a, b] × [0, 1]` is the change `A_H(g(b, ·)) - A_H(g(a, ·))` of the action of
its loops. -/
theorem integral_floerEnergyDensity_eq_hamiltonianAction_sub_of_tendsto
    (hH : ContDiff ℝ 2 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hu : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hbd : ∀ C, IsCompact C → ∃ M, ∀ k, ∀ z ∈ C, ‖fderiv ℝ (u k) z‖ ≤ M)
    (hgW : ∀ z, (z.2, g z) ∈ W) (hlim : TendstoLocallyUniformly u g atTop) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) g z =
      ω.hamiltonianAction H (fun t ↦ g (b, t)) - ω.hamiltonianAction H (fun t ↦ g (a, t)) := by
  obtain ⟨hg, hdlim, -⟩ := tendstoLocallyUniformly_fderiv_of_floer_of_periodic hH hHper hW hJ
    hJper hu hper hfloer hbd hgW fun z ↦ hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le one_le_two
  have hKt := (contDiff_uncurry_cylindrical hH1).contDiffOn (s := univ ×ˢ (univ : Set V))
  have hu1 (k : ℕ) : ContDiff ℝ 2 (u k) := (hu k).of_le (WithTop.coe_le_coe.2 le_top)
  have hR : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  -- The energy densities converge uniformly on the rectangle, so their integrals converge.
  have hX : ∀ z ∈ (univ : Set (ℝ × ℝ)), ContinuousAt
      (uncurry (ω.hamiltonianOneForm (fun _ _ ↦ 0) fun w ↦ H w.2)) (z, g z) := fun z _ ↦
    (ω.contDiffOn_uncurry_hamiltonianOneForm (n := 0) isOpen_univ contDiffOn_const
      (by simpa using (contDiff_uncurry_cylindrical hH1).contDiffOn)).continuousOn.continuousAt
      (by simp)
  have hdens := ω.tendstoLocallyUniformlyOn_floerEnergyDensity isOpen_univ
    hg.continuous.continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn hX
    hlim.tendstoLocallyUniformlyOn hdlim.tendstoLocallyUniformlyOn
  have hLHS := ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hR).1
    (hdens.mono (subset_univ _))).tendsto_setIntegral_of_continuousOn (μ := volume) hR
    (measurableSet_Icc.prod measurableSet_Icc) (Eventually.of_forall fun k ↦
      (ω.continuousOn_floerEnergyDensity isOpen_univ ((hu1 k).of_le one_le_two).contDiffOn
        contDiffOn_const hKt).mono (subset_univ _))
  -- The actions of the boundary loops converge, and for each `u_k` the identity holds.
  have hRHS := (ω.tendsto_hamiltonianAction_slice_of_tendstoLocallyUniformly
    hH1.continuous (Eventually.of_forall fun k ↦ (hu1 k).of_le one_le_two) hg hlim hdlim b).sub
    (ω.tendsto_hamiltonianAction_slice_of_tendstoLocallyUniformly hH1.continuous
      (Eventually.of_forall fun k ↦ (hu1 k).of_le one_le_two) hg hlim hdlim a)
  refine tendsto_nhds_unique hLHS (hRHS.congr fun k ↦ ?_)
  exact (ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH1 isOpen_univ
    (hu1 k).contDiffOn hab (subset_univ _) fun s _ ↦ by simpa using hper k s 0).symm

/-- **The energy of a limit of Floer trajectories.** In the situation of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub_of_tendsto`, let the
`u_k` be `L`-Lipschitz and let `J` be tamed by `ω` along the limit `g`. If the loops `g(s, ·)`
converge uniformly to closed `C¹` loops `x₀` as `s → -∞` and `x₁` as `s → ∞`, such as the orbits
at which a level of a broken limit begins and ends, then the Floer energy of `g` over the strip
`ℝ × [0, 1]` is `A_H(x₁) - A_H(x₀)`. -/
theorem setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub_of_tendstoUniformly
    (hH : ContDiff ℝ 2 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hu : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    {L : ℝ≥0} (hL : ∀ k, LipschitzWith L (u k)) (hgW : ∀ z, (z.2, g z) ∈ W)
    (hJt : ∀ z, ω.Tames (J z.2 (g z))) (hlim : TendstoLocallyUniformly u g atTop)
    {x₀ x₁ : ℝ → V} (hx₀ : ContDiff ℝ 1 x₀) (hx₀per : x₀ 1 = x₀ 0) (hx₁ : ContDiff ℝ 1 x₁)
    (hx₁per : x₁ 1 = x₁ 0) (hbot : TendstoUniformly (fun s t ↦ g (s, t)) x₀ atBot)
    (htop : TendstoUniformly (fun s t ↦ g (s, t)) x₁ atTop) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) g z) =
      ENNReal.ofReal (ω.hamiltonianAction H x₁ - ω.hamiltonianAction H x₀) := by
  have hbd : ∀ C, IsCompact C → ∃ M, ∀ k, ∀ z ∈ C, ‖fderiv ℝ (u k) z‖ ≤ M :=
    fun _ _ ↦ ⟨L, fun k _ _ ↦ norm_fderiv_le_of_lipschitz ℝ (hL k)⟩
  obtain ⟨hg, hdlim, hgeq⟩ := tendstoLocallyUniformly_fderiv_of_floer_of_periodic hH hHper hW
    hJ hJper hu hper hfloer hbd hgW fun z ↦ hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le one_le_two
  -- The limit has closed loops and derivative bounded by `L`.
  have hgper (s : ℝ) : g (s, 1) = g (s, 0) := tendsto_nhds_unique
    ((hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (s, 1))).congr fun k ↦ by
      simpa using hper k s 0)
    (hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (s, 0)))
  have hgL (z : ℝ × ℝ) : ‖fderiv ℝ g z‖ ≤ L :=
    le_of_tendsto (hdlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)).norm
      (.of_forall fun k ↦ norm_fderiv_le_of_lipschitz ℝ (hL k))
  -- On each rectangle the energy is the change of action, with a nonnegative density.
  have hE (n : ℕ) : ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) g z) =
      ENNReal.ofReal (ω.hamiltonianAction H (fun t ↦ g (n, t)) -
        ω.hamiltonianAction H (fun t ↦ g (-n, t))) := by
    rw [← integral_floerEnergyDensity_eq_hamiltonianAction_sub_of_tendsto hH hHper hW hJ hJper
        hu hper hfloer hbd hgW hlim (neg_le_self n.cast_nonneg),
      ofReal_integral_eq_lintegral_ofReal
        (((ω.continuousOn_floerEnergyDensity isOpen_univ hg.contDiffOn contDiffOn_const
          (contDiff_uncurry_cylindrical hH1).contDiffOn).mono (subset_univ _)).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc))
        (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
          fun z _ ↦ ω.floerEnergyDensity_nonneg (hJt z) (hgeq z))]
  exact setLIntegral_univ_prod_eq_ofReal_of_tendsto hE
    (ω.tendsto_hamiltonianAction_slice_of_tendstoUniformly hH1.continuous hg hgper hgL hx₀ hx₀per
      hbot)
    (ω.tendsto_hamiltonianAction_slice_of_tendstoUniformly hH1.continuous hg hgper hgL hx₁ hx₁per
      htop)

end TauCeti.SymplecticForm
