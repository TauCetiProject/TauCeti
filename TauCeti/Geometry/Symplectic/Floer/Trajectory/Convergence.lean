/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.NoBubbling
public import TauCeti.Geometry.Symplectic.Floer.Trajectory.BrokenLimit
public import TauCeti.Geometry.Symplectic.Floer.Trajectory.Limit
import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Convergence of Floer trajectories to broken trajectories

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H` a `C³` Hamiltonian and `J_t(x)` a
`C²` family of almost complex structures, both `1`-periodic in time, with `J` tamed by `ω` on a
compact set `K`. Suppose that the suspended Hamiltonian vector field is globally Lipschitz, so that
`H` has a time-one map, and that every `1`-periodic orbit of `X_H` with values in `K` is
nondegenerate. This file proves **Floer–Gromov compactness up to breaking** for the Floer
trajectories between two fixed orbits `x₀` and `x₁`: smooth solutions `u_k : ℝ × ℝ → V` of

`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0`

with `1`-periodic loops in `K`, energy at most `E`, not stationary, and loops converging uniformly
to `x₀` as `s → -∞` and to `x₁` as `s → ∞`
(`TauCeti.SymplecticForm.exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_floer`). Along
a subsequence there are `ℓ + 1` levels `g_0, …, g_ℓ`, shifts `τ_j k` and orbits
`x₀ = y_0, y_1, …, y_{ℓ+1} = x₁` such that:

* the translates `(s, t) ↦ u_k(s + τ_j k, t)` converge locally uniformly to `g_j`, and the shifts
  of consecutive levels drift apart, `τ_{j+1} k - τ_j k → ∞`;
* each level `g_j` is a nonstationary `C¹` Floer trajectory running from `y_j` at `s → -∞` to
  `y_{j+1}` at `s → ∞`, uniformly in `t`;
* no energy is lost: the energy of `g_j` is `A_H(y_{j+1}) - A_H(y_j)`, the actions of the `y_j`
  increase, and the energies of the levels add up to `A_H(x₁) - A_H(x₀)`, which is the energy of
  each `u_k`.

In a symplectic vector space no sphere bubbles off, since the form is exact: the energy bound gives
a uniform Lipschitz bound
(`TauCeti.SymplecticForm.exists_lipschitzWith_of_setLIntegral_floerEnergyDensity_le`).
The levels are first located at regular action values separating the finitely many orbit actions
(`TauCeti.SymplecticForm.exists_subseq_forall_hamiltonianAction_eq_of_floer`); there are finitely
many because nondegenerate orbits in a compact set are finite in number
(`TauCeti.SymplecticForm.finite_setOf_periodic_hasDerivAt_of_isNondegenerateFixedPt`). Consecutive
normalized limits are translates of one another or meet at a neck orbit
(`exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_tendstoUniformly`), and
the first and the last ones reach the end orbits
(`TauCeti.SymplecticForm.tendstoUniformly_atBot_of_forall_tendstoUniformly_atBot`,
`TauCeti.SymplecticForm.tendstoUniformly_atTop_of_forall_tendstoUniformly_atTop`). Keeping one
limit out of each run of translates gives the levels. A locally uniform limit of smooth Floer
trajectories with a Lipschitz bound is a `C¹` Floer trajectory whose energy is the difference of
the actions at its ends
(`setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub_of_tendstoUniformly`).

## Main results

* `TauCeti.SymplecticForm.exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_floer`: a
  sequence of nonstationary Floer trajectories of bounded energy between fixed orbits has a
  subsequence converging to a broken trajectory, with no loss of energy.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547, on the convergence of sequences of trajectories to broken trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, §3.1, on compactness up to breaking.
* M. Audin and M. Damian, *Morse theory and Floer homology*, Springer Universitext (2014),
  Chapter 9, on the compactness of spaces of Floer trajectories.
-/

public section

open Set Filter Topology Function MeasureTheory
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V}
  {K : Set V} {L' : ℝ≥0} {u : ℕ → ℝ × ℝ → V}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Keeping one limit out of each run of translates.** Let `g_0, …, g_m` be maps normalized by
shifts `σ_i`, such that `g_0` starts at `x₀`, `g_m` ends at `x₁`, and any two consecutive ones are
either translates of each other, with converging difference of shifts, or meet at an orbit, with
diverging difference of shifts. Then some of the `g_i`, the levels `g_{r_0}, …, g_{r_ℓ}`, form a
chain from `x₀` to `x₁` through orbits `y_j`, with diverging differences of shifts; the first level
is a bounded shift away from `g_0`. -/
private theorem exists_levels {P : (ℝ → V) → Prop} :
    ∀ (m : ℕ) (σ : Fin (m + 1) → ℕ → ℝ) (g : Fin (m + 1) → ℝ × ℝ → V) (x₀ x₁ : ℝ → V),
      P x₀ → P x₁ → TendstoUniformly (fun s t ↦ g 0 (s, t)) x₀ atBot →
      TendstoUniformly (fun s t ↦ g (Fin.last m) (s, t)) x₁ atTop →
      (∀ i : Fin m, (∃ δ, Tendsto (fun n ↦ σ i.succ n - σ i.castSucc n) atTop (𝓝 δ) ∧
          ∀ z, g i.succ z = g i.castSucc (z + (δ, 0))) ∨
        (Tendsto (fun n ↦ σ i.succ n - σ i.castSucc n) atTop atTop ∧ ∃ x, P x ∧
          TendstoUniformly (fun s t ↦ g i.castSucc (s, t)) x atTop ∧
          TendstoUniformly (fun s t ↦ g i.succ (s, t)) x atBot)) →
      ∃ ℓ : ℕ, ∃ r : Fin (ℓ + 1) → Fin (m + 1), ∃ y : Fin (ℓ + 2) → ℝ → V,
        y 0 = x₀ ∧ y (Fin.last (ℓ + 1)) = x₁ ∧ (∀ i, P (y i)) ∧
        (∀ j, TendstoUniformly (fun s t ↦ g (r j) (s, t)) (y j.castSucc) atBot ∧
          TendstoUniformly (fun s t ↦ g (r j) (s, t)) (y j.succ) atTop) ∧
        (∀ j : Fin ℓ, Tendsto (fun n ↦ σ (r j.succ) n - σ (r j.castSucc) n) atTop atTop) ∧
        ∃ Δ, Tendsto (fun n ↦ σ (r 0) n - σ 0 n) atTop (𝓝 Δ)
  | 0, σ, g, x₀, x₁, hx₀, hx₁, h0, hm, _ =>
    ⟨0, id, ![x₀, x₁], rfl, rfl, fun i ↦ by fin_cases i <;> assumption,
      fun j ↦ by fin_cases j; exact ⟨h0, hm⟩, fun j ↦ j.elim0, 0, by simp⟩
  | m + 1, σ, g, x₀, x₁, hx₀, hx₁, h0, hm, hgap => by
    have hm' : TendstoUniformly (fun s t ↦ g (Fin.last m).succ (s, t)) x₁ atTop := by
      rwa [Fin.succ_last]
    have hgap' (i : Fin m) := hgap i.succ
    simp only [← Fin.succ_castSucc] at hgap'
    rcases hgap 0 with ⟨δ, hδ, hg1⟩ | ⟨hσ, y₁, hy₁, htop₀, hbot₁⟩
    · -- The first two maps are translates: drop the first one.
      have h1 : TendstoUniformly (fun s t ↦ g (0 : Fin (m + 1)).succ (s, t)) x₀ atBot := by
        simp only [hg1, Fin.castSucc_zero]
        intro U hU
        filter_upwards [(tendsto_atBot_add_const_right atBot δ tendsto_id).eventually (h0 U hU)]
          with s hs t
        simpa using hs t
      obtain ⟨ℓ, r, y, hy0, hyl, hyP, hlev, hdiv, Δ, hΔ⟩ :=
        exists_levels m (fun i ↦ σ i.succ) (fun i ↦ g i.succ) x₀ x₁ hx₀ hx₁ h1 hm' hgap'
      refine ⟨ℓ, fun j ↦ (r j).succ, y, hy0, hyl, hyP, hlev, hdiv, Δ + δ, ?_⟩
      refine (hΔ.add hδ).congr fun n ↦ ?_
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      ring
    · -- The first two maps meet at the orbit `y₁`: the first one is a level.
      obtain ⟨ℓ, r, y, hy0, hyl, hyP, hlev, hdiv, Δ, hΔ⟩ :=
        exists_levels m (fun i ↦ σ i.succ) (fun i ↦ g i.succ) y₁ x₁ hy₁ hx₁ hbot₁ hm' hgap'
      refine ⟨ℓ + 1, Fin.cons 0 fun j ↦ (r j).succ, Fin.cons x₀ y, rfl, ?_,
        Fin.cases hx₀ hyP, Fin.cases ?_ fun j ↦ ?_, Fin.cases ?_ fun j ↦ ?_, 0, by simp⟩
      · rw [← Fin.succ_last, Fin.cons_succ, hyl]
      · simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_one, hy0]
        exact ⟨h0, by simpa using htop₀⟩
      · simpa only [Fin.cons_succ, ← Fin.succ_castSucc] using hlev j
      · -- The shift of the second level is a bounded distance from that of the neck's far side.
        refine (hσ.atTop_add hΔ).congr fun n ↦ ?_
        simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_one]
        ring
      · simpa only [Fin.cons_succ, ← Fin.succ_castSucc] using hdiv j

/-- **A limit of translated trajectories is a level.** Let `v_n` be smooth Floer trajectories with
`1`-periodic loops in the compact set `K`, on which `J` is tamed by `ω`, and a common Lipschitz
constant, converging locally uniformly to `g`. If the loops of `g` converge uniformly to orbits
`x₀` as `s → -∞` and `x₁` as `s → ∞`, then `g` is a `C¹` Floer trajectory, the action does not
decrease from `x₀` to `x₁`, and the energy of `g` is `A_H(x₁) - A_H(x₀)`. -/
private theorem floer_and_energy_of_tendstoLocallyUniformly (hH : ContDiff ℝ 2 (uncurry H))
    (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJper : Periodic J 1) (hK : IsCompact K) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    {v : ℕ → ℝ × ℝ → V} (hv : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n))
    (hper : ∀ n s, Periodic (fun t ↦ v n (s, t)) 1) (hvK : ∀ n z, v n z ∈ K)
    (hfloer : ∀ n z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (v n z))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (v n) z : ℝ × ℝ →ₗ[ℝ] V))
    {L : ℝ≥0} (hL : ∀ n, LipschitzWith L (v n)) {g : ℝ × ℝ → V}
    (hlim : TendstoLocallyUniformly v g atTop) {x₀ x₁ : ℝ → V} (hx₀per : Periodic x₀ 1)
    (hx₀ : ∀ t, HasDerivAt x₀ (ω.hamiltonianVectorField (H t) (x₀ t)) t)
    (hx₁per : Periodic x₁ 1) (hx₁ : ∀ t, HasDerivAt x₁ (ω.hamiltonianVectorField (H t) (x₁ t)) t)
    (hbot : TendstoUniformly (fun s t ↦ g (s, t)) x₀ atBot)
    (htop : TendstoUniformly (fun s t ↦ g (s, t)) x₁ atTop) :
    ContDiff ℝ 1 g ∧
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (g z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) g z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ω.hamiltonianAction H x₀ ≤ ω.hamiltonianAction H x₁ ∧
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) g z) =
        ENNReal.ofReal (ω.hamiltonianAction H x₁ - ω.hamiltonianAction H x₀) := by
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le one_le_two
  have hfl : ∀ n, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (v n z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (v n) z : ℝ × ℝ →ₗ[ℝ] V) :=
    fun n z _ ↦ hfloer n z
  have hbd : ∀ C, IsCompact C → ∃ M, ∀ n, ∀ z ∈ C, ‖fderiv ℝ (v n) z‖ ≤ M :=
    fun _ _ ↦ ⟨L, fun n _ _ ↦ norm_fderiv_le_of_lipschitz ℝ (hL n)⟩
  -- The limit is a `C¹` Floer trajectory with closed loops and derivative bounded by `L`.
  obtain ⟨hg, hgeq, hgper, hgL⟩ :=
    contDiff_and_floer_and_periodic_and_norm_fderiv_le_of_tendstoLocallyUniformly hH hHper
      isOpen_univ hJ.contDiffOn hJper hv hper hfl hL (fun _ ↦ mem_univ _) hlim
  -- The limit takes values in `K`, where `J` is tamed, so its energy density is nonnegative.
  have hJg (z : ℝ × ℝ) : ω.Tames (J z.2 (g z)) :=
    hJt _ _ (hK.isClosed.mem_of_tendsto (hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
      (.of_forall fun n ↦ hvK n z))
  have hx₀1 := ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField hH1 hx₀
  have hx₁1 := ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField hH1 hx₁
  refine ⟨hg, hgeq, ?_,
    setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub_of_tendstoUniformly hH hHper
      isOpen_univ hJ.contDiffOn hJper hv hper hfl hL (fun _ ↦ mem_univ _) hJg hlim hx₀1
      (by simpa using hx₀per 0) hx₁1 (by simpa using hx₁per 0) hbot htop⟩
  -- The action of the loops of `g` increases, by the energy identity on rectangles.
  have hmono : Monotone fun s ↦ ω.hamiltonianAction H (fun t ↦ g (s, t)) := fun a b hab ↦ by
    have h := integral_floerEnergyDensity_eq_hamiltonianAction_sub_of_tendsto hH hHper isOpen_univ
      hJ.contDiffOn hJper hv hper hfl hbd (fun _ ↦ mem_univ _) hlim hab
    have h0 : 0 ≤ ∫ z in Icc a b ×ˢ Icc 0 1,
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) g z :=
      setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦
        ω.floerEnergyDensity_nonneg (hJg z) (hgeq z)
    linarith
  -- Its limits at the two ends are the actions of `x₀` and `x₁`.
  exact (hmono.le_of_tendsto (ω.tendsto_hamiltonianAction_slice_of_tendstoUniformly
      hH1.continuous hg hgper hgL hx₀1 (by simpa using hx₀per 0) hbot) 0).trans
    (hmono.ge_of_tendsto (ω.tendsto_hamiltonianAction_slice_of_tendstoUniformly
      hH1.continuous hg hgper hgL hx₁1 (by simpa using hx₁per 0) htop) 0)

/-- The levels of a sequence of Floer trajectories with a common Lipschitz bound between fixed
orbits: the statement of `exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_floer` without
the regularity and energy of the levels. -/
private theorem exists_subseq_levels (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJper : Periodic J 1) (hK : IsCompact K) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hu : ∀ k, ContDiff ℝ 3 (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    {L : ℝ≥0} (hL : ∀ k, LipschitzWith L (u k)) (hns : ∀ k, ∃ s t, u k (s, t) ≠ u k (0, t))
    {x₀ x₁ : ℝ → V} (hx₀per : Periodic x₀ 1)
    (hx₀ : ∀ t, HasDerivAt x₀ (ω.hamiltonianVectorField (H t) (x₀ t)) t)
    (hx₁per : Periodic x₁ 1) (hx₁ : ∀ t, HasDerivAt x₁ (ω.hamiltonianVectorField (H t) (x₁ t)) t)
    (hbot : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₀ atBot)
    (htop : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₁ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ℓ : ℕ, ∃ τ : Fin (ℓ + 1) → ℕ → ℝ,
      ∃ g : Fin (ℓ + 1) → ℝ × ℝ → V, ∃ y : Fin (ℓ + 2) → ℝ → V,
      y 0 = x₀ ∧ y (Fin.last (ℓ + 1)) = x₁ ∧
      (∀ i, Periodic (y i) 1 ∧ ∀ t, HasDerivAt (y i) (ω.hamiltonianVectorField (H t) (y i t)) t) ∧
      (∀ j, TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (τ j n, 0))) (g j) atTop) ∧
      (∀ j : Fin ℓ, Tendsto (fun n ↦ τ j.succ n - τ j.castSucc n) atTop atTop) ∧
      (∀ j, ∃ s t, g j (s, t) ≠ g j (0, t)) ∧
      ∀ j, TendstoUniformly (fun s t ↦ g j (s, t)) (y j.castSucc) atBot ∧
        TendstoUniformly (fun s t ↦ g j (s, t)) (y j.succ) atTop := by
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  -- The orbits in `K` are nondegenerate, so they have finitely many actions.
  have hfin := (ω.finite_setOf_periodic_hasDerivAt_of_isNondegenerateFixedPt hL' hK hnd).image
    (ω.hamiltonianAction H)
  -- Normalize the trajectories at regular action values `b 0 < ⋯ < b m` separating the orbit
  -- actions between the common end actions `a₀ < a₁`.
  obtain ⟨c, hc, M, hcM⟩ :=
    exists_pos_forall_mul_norm_sq_le_and_norm_le hK hJ.continuous.continuousOn hJper hJt
  obtain ⟨φ₀, hφ₀, a₀, a₁, -, hends, m, b, hb, hbC, h0, h1, hgaps, σ, hσ⟩ :=
    exists_subseq_forall_hamiltonianAction_eq_of_floer (J := fun k z ↦ J z.2 (u k z)) hH1 hHper
      hK hfin (fun k ↦ (hu k).of_le (by norm_num)) hper huK hc
      (fun k z _ v ↦ (hcM z.2 _ (huK k z) v).1) (fun k z _ v ↦ (hcM z.2 _ (huK k z) v).2) hfloer
      hL hns
  -- The normalized limits, consecutive ones being translates or meeting at a neck orbit.
  obtain ⟨φ₁, hφ₁, g, hg, hlev⟩ :=
    exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_tendstoUniformly
      (u := fun k ↦ u (φ₀ k)) (W := univ) hH hHper isOpen_univ hJ.contDiffOn hJper hK
      (subset_univ _) hJt hL' hnd (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _)
      (fun _ ↦ hfloer _) (fun _ ↦ hL _) hb hbC
      (fun i ↦ by obtain ⟨c', hc'⟩ := hgaps i; rw [hc']; exact subsingleton_singleton) hσ
  -- Along each trajectory the action increases from `a₀` to `a₁`.
  have hmono (k : ℕ) : Monotone fun s ↦ ω.hamiltonianAction H (fun t ↦ u k (s, t)) :=
    ω.monotone_hamiltonianAction_of_floer (J := fun z ↦ J z.2 (u k z)) hH1
      ((hu k).of_le (by norm_num)) (hper k) (fun z _ ↦ hJt z.2 _ (huK k z)) (hfloer k)
  -- The first normalized limit starts at `x₀`, and the last one ends at `x₁`.
  have hstart := tendstoUniformly_atBot_of_forall_tendstoUniformly_atBot
    (u := fun n ↦ u (φ₀ (φ₁ n))) (W := univ) hH hHper isOpen_univ hJ.contDiffOn hJper hK
    (subset_univ _) hJt hL' hnd (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _)
    (fun _ ↦ hfloer _) (fun _ ↦ hL _) (σ' := fun n ↦ σ 0 (φ₁ n)) (b := a₀)
    (fun n ↦ (hσ 0 (φ₁ n)).le) (fun n s ↦ (hmono _).le_of_tendsto (hends _).1 s)
    (by rw [h0]; exact subsingleton_singleton) (fun _ ↦ hbot _) fun z ↦ (hg 0).1.tendsto_at z
  have hend := tendstoUniformly_atTop_of_forall_tendstoUniformly_atTop
    (u := fun n ↦ u (φ₀ (φ₁ n))) (W := univ) hH hHper isOpen_univ hJ.contDiffOn hJper hK
    (subset_univ _) hJt hL' hnd (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _)
    (fun _ ↦ hfloer _) (fun _ ↦ hL _) (σ := fun n ↦ σ (Fin.last m) (φ₁ n)) (b' := a₁)
    (fun n ↦ (hσ _ (φ₁ n)).ge) (fun n s ↦ (hmono _).ge_of_tendsto (hends _).2 s)
    (by rw [h1]; exact subsingleton_singleton) (fun _ ↦ htop _)
    fun z ↦ (hg (Fin.last m)).1.tendsto_at z
  -- Keep one normalized limit out of each run of translates.
  obtain ⟨ℓ, r, y, hy0, hyl, hy, hends', hdiv, -⟩ :=
    exists_levels (P := fun x ↦ Periodic x 1 ∧
        ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) m
      (fun i n ↦ σ i (φ₁ n)) g x₀ x₁ ⟨hx₀per, hx₀⟩ ⟨hx₁per, hx₁⟩ hstart hend fun i ↦
      (hlev i).imp_right fun ⟨hd, x, hxper, hx, _, _, hxtop, hxbot⟩ ↦
        ⟨hd, x, ⟨hxper, hx⟩, hxtop, hxbot⟩
  exact ⟨φ₀ ∘ φ₁, hφ₀.comp hφ₁, ℓ, fun j n ↦ σ (r j) (φ₁ n), fun j ↦ g (r j), y, hy0, hyl, hy,
    fun j ↦ (hg (r j)).1, hdiv, fun j ↦ (hg (r j)).2, hends'⟩

/-- **Floer–Gromov compactness up to breaking.** Let `H` be a `C³` Hamiltonian and `J_t(x)` a
`C²` family of almost complex structures, both `1`-periodic in time, with `J` tamed by `ω` on a
compact set `K`. Suppose that the suspension of the Hamiltonian vector field is globally Lipschitz
and that every `1`-periodic orbit in `K` is nondegenerate. Let `u_k` be smooth Floer trajectories,
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0`, with `1`-periodic loops in `K`, energy at most `E`, not
stationary, whose loops converge uniformly to the `1`-periodic orbit `x₀` as `s → -∞` and to the
`1`-periodic orbit `x₁` as `s → ∞`.

Then there are a subsequence `u (φ n)`, a number `ℓ + 1` of levels `g j`, shifts `τ j n` and
`1`-periodic orbits `x₀ = y 0, y 1, …, y (ℓ + 1) = x₁` with nondecreasing actions, such that:

* the translates `(s, t) ↦ u (φ n) (s + τ j n, t)` converge locally uniformly to `g j`, and
  `τ (j + 1) n - τ j n → ∞`;
* each `g j` is a nonstationary `C¹` Floer trajectory whose loops converge uniformly to `y j` as
  `s → -∞` and to `y (j + 1)` as `s → ∞`;
* the energy of `g j` is `A_H(y (j + 1)) - A_H(y j)`, so that the energies of the levels add up to
  `A_H(x₁) - A_H(x₀)`, the energy of each `u_k`. -/
theorem exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_floer
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJper : Periodic J 1) (hK : IsCompact K) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hu : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    {E : ℝ} (hE : ∀ k, ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z) ≤
        ENNReal.ofReal E)
    (hns : ∀ k, ∃ s t, u k (s, t) ≠ u k (0, t)) {x₀ x₁ : ℝ → V} (hx₀per : Periodic x₀ 1)
    (hx₀ : ∀ t, HasDerivAt x₀ (ω.hamiltonianVectorField (H t) (x₀ t)) t)
    (hx₁per : Periodic x₁ 1) (hx₁ : ∀ t, HasDerivAt x₁ (ω.hamiltonianVectorField (H t) (x₁ t)) t)
    (hbot : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₀ atBot)
    (htop : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₁ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ℓ : ℕ, ∃ τ : Fin (ℓ + 1) → ℕ → ℝ,
      ∃ g : Fin (ℓ + 1) → ℝ × ℝ → V, ∃ y : Fin (ℓ + 2) → ℝ → V,
      y 0 = x₀ ∧ y (Fin.last (ℓ + 1)) = x₁ ∧
      (∀ i, Periodic (y i) 1 ∧ ∀ t, HasDerivAt (y i) (ω.hamiltonianVectorField (H t) (y i t)) t) ∧
      Monotone (fun i ↦ ω.hamiltonianAction H (y i)) ∧
      (∀ j, TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (τ j n, 0))) (g j) atTop) ∧
      (∀ j : Fin ℓ, Tendsto (fun n ↦ τ j.succ n - τ j.castSucc n) atTop atTop) ∧
      (∀ j, ContDiff ℝ 1 (g j) ∧
        (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (g j z))
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (g j) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
        ∃ s t, g j (s, t) ≠ g j (0, t)) ∧
      (∀ j, TendstoUniformly (fun s t ↦ g j (s, t)) (y j.castSucc) atBot ∧
        TendstoUniformly (fun s t ↦ g j (s, t)) (y j.succ) atTop) ∧
      (∀ j, ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (g j) z) =
        ENNReal.ofReal
          (ω.hamiltonianAction H (y j.succ) - ω.hamiltonianAction H (y j.castSucc))) ∧
      ∑ j, ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (g j) z) =
        ENNReal.ofReal (ω.hamiltonianAction H x₁ - ω.hamiltonianAction H x₀) ∧
      ∀ k, ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z) =
        ENNReal.ofReal (ω.hamiltonianAction H x₁ - ω.hamiltonianAction H x₀) := by
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have hH2 : ContDiff ℝ 2 (uncurry H) := hH.of_le (by norm_num)
  -- No bubbling: the energy bound gives a common Lipschitz constant.
  obtain ⟨L, hL⟩ := ω.exists_lipschitzWith_of_setLIntegral_floerEnergyDensity_le hH2 hHper hJ hK
    hJt E
  have hLu (k : ℕ) : LipschitzWith L (u k) :=
    hL (hu k) (fun s t ↦ hper k s t) (hfloer k) (huK k) (hE k)
  -- So the energy of `u k` is the difference of the actions of its end orbits.
  have hEu (k : ℕ) : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z) =
        ENNReal.ofReal (ω.hamiltonianAction H x₁ - ω.hamiltonianAction H x₀) := by
    have hukper (s : ℝ) : u k (s, 1) = u k (s, 0) := by simpa using hper k s 0
    have hu2 : ContDiff ℝ 2 (u k) := (hu k).of_le (WithTop.coe_le_coe.2 le_top)
    have hend {x : ℝ → V} {l : Filter ℝ} [l.IsCountablyGenerated] (hxper : Periodic x 1)
        (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
        (hl : TendstoUniformly (fun s t ↦ u k (s, t)) x l) :=
      ω.tendsto_hamiltonianAction_slice_of_tendstoUniformly hH1.continuous (hu2.of_le one_le_two)
        hukper (fun z ↦ norm_fderiv_le_of_lipschitz ℝ (hLu k))
        (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField hH1 hx) (by simpa using hxper 0) hl
    exact ω.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction
      (J := fun z ↦ J z.2 (u k z)) (fun z _ ↦ hJt _ _ (huK k z)) hH1 isOpen_univ hu2.contDiffOn
      (subset_univ _) hukper
      (fun z _ ↦ by
        simpa using (ω.isComplexLinearMap_perturbedFDeriv_iff _ _ _ _ z).1 (hfloer k z))
      (hend hx₀per hx₀ (hbot k)) (hend hx₁per hx₁ (htop k))
  obtain ⟨φ, hφ, ℓ, τ, g, y, hy0, hyl, hy, hconv, hdiv, hns', hends⟩ :=
    exists_subseq_levels hH hHper hJ hJper hK hJt hL' hnd
      (fun k ↦ (hu k).of_le (WithTop.coe_le_coe.2 le_top)) hper huK (fun k z _ ↦ hfloer k z) hLu
      hns hx₀per hx₀ hx₁per hx₁ hbot htop
  -- Each level is a limit of translated trajectories.
  have hlevel (j : Fin (ℓ + 1)) := floer_and_energy_of_tendstoLocallyUniformly hH2 hHper
    (hJ.of_le one_le_two) hJper hK hJt (v := fun n z ↦ u (φ n) (z + (τ j n, 0)))
    (fun n ↦ (hu _).comp (contDiff_id.add contDiff_const))
    (fun n s t ↦ by simpa using hper (φ n) (s + τ j n) t) (fun _ _ ↦ huK _ _)
    (fun n z ↦ isComplexLinearMap_perturbedFDeriv_comp_add_right (hfloer _) _ z)
    (fun n ↦ LipschitzWith.of_dist_le_mul (K := L) fun z w ↦ by
      have h := (hLu (φ n)).dist_le_mul (z + (τ j n, 0)) (w + (τ j n, 0))
      rwa [dist_add_right] at h)
    (hconv j) (hy _).1 (hy _).2 (hy _).1 (hy _).2 (hends j).1 (hends j).2
  refine ⟨φ, hφ, ℓ, τ, g, y, hy0, hyl, hy, Fin.monotone_iff_le_succ.2 fun j ↦ (hlevel j).2.2.1,
    hconv, hdiv, fun j ↦ ⟨(hlevel j).1, (hlevel j).2.1, hns' j⟩, hends,
    fun j ↦ (hlevel j).2.2.2, ?_, hEu⟩
  -- The energies of the levels telescope.
  simp only [fun j ↦ (hlevel j).2.2.2]
  have hsum := Fin.sum_Iic_sub (⊤ : Fin (ℓ + 1)) fun i ↦ ω.hamiltonianAction H (y i)
  rw [Finset.Iic_top, Fin.top_eq_last, Fin.succ_last, hyl, hy0] at hsum
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ sub_nonneg.2 (hlevel j).2.2.1, hsum]

end TauCeti.SymplecticForm
