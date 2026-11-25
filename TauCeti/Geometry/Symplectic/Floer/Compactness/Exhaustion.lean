/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.Compactness.SigmaCompact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of Floer solutions on a whole domain off a discrete set

The compactness theorem of `TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`) works on
a compact window `D` of the domain, with an energy threshold `δ > 0` depending on the window. On a
domain `Ω` that is not relatively compact, such as a punctured Riemann surface, it applies on each
window of a compact exhaustion of `Ω`, and a diagonal subsequence (`TauCeti.extraction_forall`)
converges on all of `Ω`
(`TauCeti.SymplecticForm.exists_tendstoLocallyUniformlyOn_subseq_off_discrete`). The limits on the
windows glue to one limit (`TauCeti.exists_tendstoLocallyUniformlyOn_iUnion`).

The solutions may live on open sets `Uₖ` that only eventually contain each compact subset of `Ω`,
as on domains whose necks stretch. The bubbling points are those of the first window containing
them, so they form a set meeting each compact subset of `Ω` in finitely many points, each carrying
a positive amount of energy. Without an energy threshold uniform over `Ω`, which on cylindrical
ends needs the translation invariance of the data there, this set is not shown to be finite.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points on a noncompact domain, through an exhaustion by compact
  sets).
-/

public section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V}

/-- The compactness theorem on countably many windows `O j ⊆ D j` of a domain `Ω`, for solutions on
open sets `Uₖ` which eventually contain each compact set `D j`: there are energy thresholds
`δ j > 0` and one subsequence `φ` converging on every window `O j` off a finite set of bubbling
points, through a diagonal extraction (`TauCeti.extraction_forall`). -/
private theorem exists_subseq_forall_window (ω : SymplecticForm V)
    {W : Set ((ℝ × ℝ) × V)} {Ω : Set (ℝ × ℝ)} {D O : ℕ → Set (ℝ × ℝ)} {K : Set V}
    (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (Function.uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (Function.uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hK : IsCompact K) (hΩKW : Ω ×ˢ K ⊆ W) (hJt : ∀ z ∈ Ω, ∀ x ∈ K, ω.Tames (J z x))
    (hD : ∀ j, IsCompact (D j)) (hDΩ : ∀ j, D j ⊆ Ω) (hO : ∀ j, IsOpen (O j))
    (hOD : ∀ j, O j ⊆ D j) {U : ℕ → Set (ℝ × ℝ)} {u : ℕ → ℝ × ℝ → V} {E : ℝ}
    (hU : ∀ k, IsOpen (U k)) (hDU : ∀ j, ∀ᶠ k in atTop, D j ⊆ U k)
    (hu : ∀ k, ContDiffOn ℝ 3 (u k) (U k))
    (hfl : ∀ k, ∀ z ∈ U k, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
      (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (huK : ∀ k, MapsTo (u k) (U k) K)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) (U k))
    (hE : ∀ k, ∫ z in U k, ω.floerEnergyDensity Ks Kt (u k) z ≤ E)
    (hf0 : ∀ k, ∀ z ∈ U k, 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z) :
    ∃ (δ : ℕ → ℝ) (φ : ℕ → ℕ), (∀ j, 0 < δ j) ∧ StrictMono φ ∧
      ∀ j, ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V),
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ j ≤ ∫ y in ball z ε ∩ O j, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ O j \ ↑Z →
          ∃ M, ∀ᶠ n in atTop, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (O j \ ↑Z) ∧ MapsTo v (O j \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (O j \ ↑Z) := by
  choose δ hδ hconv using fun j ↦ ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    hW hKs hKt hJ (hD j) hK ((prod_mono (hDΩ j) subset_rfl).trans hΩKW)
    (fun z hz x hx ↦ hJt z (hDΩ j hz) x hx)
  -- Every subsequence has a further subsequence converging on the window `j`, and a diagonal
  -- subsequence `φ` eventually runs through such a subsequence for each window.
  obtain ⟨φ, hφ, hψ⟩ := extraction_forall (P := fun j ψ ↦ ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V),
    (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
      δ j ≤ ∫ y in ball z ε ∩ O j, ω.floerEnergyDensity Ks Kt (u (ψ n)) y) ∧
    (∀ C, IsCompact C → C ⊆ O j \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (ψ n)) y‖ ≤ M) ∧
    ContinuousOn v (O j \ ↑Z) ∧ MapsTo v (O j \ ↑Z) K ∧
    TendstoLocallyUniformlyOn (fun n ↦ u (ψ n)) v atTop (O j \ ↑Z)) fun j ψ hψ ↦ by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hDU j)
    have hsub (n : ℕ) : O j ⊆ U (ψ (n + N)) :=
      (hOD j).trans (hN _ ((Nat.le_add_left N n).trans (hψ.id_le _)))
    obtain ⟨φ, Z, v, hφ, -, -, h⟩ := hconv j (hO j) (hOD j) (u := fun n ↦ u (ψ (n + N)))
      (E := E) (fun n ↦ (hu _).mono (hsub n)) (fun n z hz ↦ hfl _ z (hsub n hz))
      (fun n ↦ (huK _).mono_left (hsub n)) (fun n ↦ (hint _).mono_set (hsub n))
      (fun n ↦ (setIntegral_mono_set (hint _)
        (ae_restrict_of_forall_mem (hU _).measurableSet (hf0 _)) (hsub n).eventuallySubset).trans
          (hE _))
    exact ⟨fun n ↦ φ n + N, fun a b hab ↦ Nat.add_lt_add_right (hφ hab) N, Z, v, h⟩
  refine ⟨δ, φ, hδ, hφ, fun j ↦ ?_⟩
  obtain ⟨ψ, ⟨Z, v, hconc, hbd, hvc, hvK, hlim⟩, hψφ⟩ := hψ j
  obtain ⟨f, hf, hφf⟩ := exists_tendsto_eventuallyEq_comp_of_eq_apply_of_le hψφ
  refine ⟨Z, v, fun z hz ε hε ↦ ?_, fun C hC hCZ ↦ ?_, hvc, hvK,
    (hlim.comp_tendsto hf).congr_inseparable (hφf.mono fun n hn _ _ ↦ .of_eq (by simp [hn]))⟩
  · exact eventually_of_eq_apply_of_le (p := fun k ↦
      δ j ≤ ∫ y in ball z ε ∩ O j, ω.floerEnergyDensity Ks Kt (u k) y) hψφ (hconc z hz ε hε)
  · obtain ⟨M, hM⟩ := hbd C hC hCZ
    exact ⟨M, eventually_of_eq_apply_of_le (p := fun k ↦ ∀ y ∈ C, ‖fderiv ℝ (u k) y‖ ≤ M) hψφ
      (.of_forall hM)⟩

/-- **Floer solutions of bounded energy on a whole domain converge off a discrete set.** Let
`K = K_s ds + K_t dt` be `C³` and `J(z, x)` be `C²` on an open set `W ⊆ (ℝ × ℝ) × V` containing
`Ω × K` for an open domain `Ω ⊆ ℝ × ℝ` and a compact `K ⊆ V`, with `J(z, x)` tamed by `ω` on
`Ω × K`. Let `uₖ` be `C³` solutions of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on
open sets `Uₖ ⊆ Ω` which eventually contain every compact subset of `Ω`, with `uₖ(Uₖ) ⊆ K` and
Floer energy `∫_{Uₖ} ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ E`. Then there are a subsequence `φ`, a
set `Z ⊆ Ω` of bubbling points meeting every compact subset of `Ω` in a finite set, and a
continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries
energy at least some `δ > 0` depending on the point, the differentials are eventually uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_tendstoLocallyUniformlyOn_subseq_off_discrete (ω : SymplecticForm V)
    {W : Set ((ℝ × ℝ) × V)} {Ω : Set (ℝ × ℝ)} {K : Set V}
    (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (Function.uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (Function.uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩKW : Ω ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ Ω, ∀ x ∈ K, ω.Tames (J z x))
    {U : ℕ → Set (ℝ × ℝ)} {u : ℕ → ℝ × ℝ → V} {E : ℝ}
    (hU : ∀ k, IsOpen (U k)) (hUΩ : ∀ k, U k ⊆ Ω)
    (hUC : ∀ C, IsCompact C → C ⊆ Ω → ∀ᶠ k in atTop, C ⊆ U k)
    (hu : ∀ k, ContDiffOn ℝ 3 (u k) (U k))
    (hfl : ∀ k, ∀ z ∈ U k, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
      (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (huK : ∀ k, MapsTo (u k) (U k) K)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) (U k))
    (hE : ∀ k, ∫ z in U k, ω.floerEnergyDensity Ks Kt (u k) z ≤ E) :
    ∃ (φ : ℕ → ℕ) (Z : Set (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ Z ⊆ Ω ∧
      (∀ C, IsCompact C → C ⊆ Ω → (Z ∩ C).Finite) ∧
      (∀ z ∈ Z, ∃ δ > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        δ ≤ ∫ y in ball z ε ∩ U (φ n), ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
      (∀ C, IsCompact C → C ⊆ Ω \ Z →
        ∃ M, ∀ᶠ n in atTop, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
      ContinuousOn v (Ω \ Z) ∧ MapsTo v (Ω \ Z) K ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ Z) := by
  classical
  have hf0 (k : ℕ) : ∀ z ∈ U k, 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z := fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJt z (hUΩ k hz) _ (huK k hz)) (hfl k z hz)
  -- Open windows `O j` exhausting `Ω`, with compact closures in `Ω`, and a subsequence `φ`
  -- converging on each of them.
  have := hΩ.locallyCompactSpace
  obtain ⟨O, hO, hDc, hDΩ, hmono, hUn⟩ := hΩ.exists_iUnion_isOpen_isCompact_closure
  have hCO (C : Set (ℝ × ℝ)) (hC : IsCompact C) (hCΩ : C ⊆ Ω) : ∃ j, C ⊆ O j :=
    hC.elim_directed_cover O hO (hUn ▸ hCΩ) hmono.directed_le
  obtain ⟨δ, φ, hδ, hφ, hPφ⟩ := ω.exists_subseq_forall_window hW hKs hKt hJ hK hΩKW hJt hDc hDΩ hO
    (fun _ ↦ subset_closure) hU (fun j ↦ hUC _ (hDc j) (hDΩ j)) hu hfl huK hint hE hf0
  choose Zj vj hconc hbd hvc hvK hlim using hPφ
  -- The limits on the windows glue, and the bubbling points are those of the first window.
  set G : ℕ → Set (ℝ × ℝ) := fun j ↦ O j \ ↑(Zj j)
  have hG (j : ℕ) : IsOpen (G j) := (hO j).sdiff (Zj j).finite_toSet.isClosed
  obtain ⟨v, hv, hlimv⟩ := exists_tendstoLocallyUniformlyOn_iUnion hG hlim
  have hfirst (y : ℝ × ℝ) (hy : y ∈ Ω) : ∃ j, y ∈ O j ∧ ∀ i, y ∈ O i → j ≤ i := by
    have h : ∃ j, y ∈ O j := mem_iUnion.1 (hUn.symm ▸ hy)
    exact ⟨Nat.find h, Nat.find_spec h, fun i hi ↦ Nat.find_min' h hi⟩
  choose! j₀ hj₀ hj₀_le using hfirst
  set Z : Set (ℝ × ℝ) := {y | y ∈ Ω ∧ y ∈ Zj (j₀ y)}
  have hyG {y : ℝ × ℝ} (hy : y ∈ Ω \ Z) : y ∈ G (j₀ y) := ⟨hj₀ y hy.1, fun h ↦ hy.2 ⟨hy.1, h⟩⟩
  refine ⟨φ, Z, v, hφ, fun y hy ↦ hy.1, fun C hC hCΩ ↦ ?_, fun z hz ↦ ?_, fun C hC hCZ ↦ ?_,
    fun y hy ↦ ?_, fun y hy ↦ by rw [hv _ (hyG hy)]; exact hvK _ (hyG hy),
    hlimv.mono fun y hy ↦ mem_iUnion.2 ⟨_, hyG hy⟩⟩
  · -- A compact set lies in some window `O m`, so it only meets the bubbling points of the
    -- windows `j ≤ m`.
    obtain ⟨m, hm⟩ := hCO C hC hCΩ
    refine ((Finset.range (m + 1)).finite_toSet.biUnion fun j _ ↦ (Zj j).finite_toSet).subset ?_
    rintro y ⟨⟨hyΩ, hyZ⟩, hyC⟩
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le
      (hj₀_le y hyΩ m (hm hyC))))) hyZ
  · -- Energy concentrates at `z` on the window `j₀ z`, which eventually lies in `U (φ n)`.
    refine ⟨δ (j₀ z), hδ _, fun ε hε ↦ ?_⟩
    filter_upwards [hconc _ z hz.2 ε hε,
      hφ.tendsto_atTop.eventually (hUC _ (hDc (j₀ z)) (hDΩ _))] with n hn hDU
    exact hn.trans (setIntegral_mono_set ((hint _).mono_set inter_subset_right)
      (ae_restrict_of_forall_mem (measurableSet_ball.inter (hU _).measurableSet)
        fun y hy ↦ hf0 _ y hy.2)
      (inter_subset_inter_right _ (subset_closure.trans hDU)).eventuallySubset)
  · -- Bounds on closed balls about the points of `C`, from their windows, cover `C`.
    refine hC.exists_eventually_forall_le_of_forall fun y hy ↦ ?_
    obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.1 (hG (j₀ y)) y (hyG (hCZ hy))
    exact ⟨closedBall y (r / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds y (by positivity)),
      hbd _ _ (isCompact_closedBall y _) ((closedBall_subset_ball (by linarith)).trans hrG)⟩
  · exact (((hvc _).continuousAt ((hG _).mem_nhds (hyG hy))).congr
      (eventuallyEq_of_mem ((hG _).mem_nhds (hyG hy)) (hv _).symm)).continuousWithinAt

end TauCeti.SymplecticForm
