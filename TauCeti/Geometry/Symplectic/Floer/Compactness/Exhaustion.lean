/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.Order.Filter.AtTopBot
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
  -- Compact windows `D j ⊆ Ω` with open interiors `O j`, from a compact exhaustion of `Ω`.
  have := hΩ.locallyCompactSpace
  set Kx := CompactExhaustion.choice Ω
  set D : ℕ → Set (ℝ × ℝ) := fun j ↦ (↑) '' Kx j
  set O : ℕ → Set (ℝ × ℝ) := fun j ↦ (↑) '' interior (Kx j)
  have hDc (j : ℕ) : IsCompact (D j) := (Kx.isCompact j).image continuous_subtypeVal
  have hDΩ (j : ℕ) : D j ⊆ Ω := Subtype.coe_image_subset _ _
  have hO (j : ℕ) : IsOpen (O j) := hΩ.isOpenMap_subtypeVal _ isOpen_interior
  have hOD (j : ℕ) : O j ⊆ D j := image_mono interior_subset
  have hCO : ∀ C, IsCompact C → C ⊆ Ω → ∃ j, C ⊆ O j := by
    intro C hC hCΩ
    have hC' : IsCompact (((↑) : Ω → ℝ × ℝ) ⁻¹' C) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hCΩ]
      exact hC
    obtain ⟨n, hn⟩ := Kx.exists_superset_of_isCompact hC'
    exact ⟨n + 1, fun c hc ↦ ⟨⟨c, hCΩ hc⟩, Kx.subset_interior_succ n (hn hc), rfl⟩⟩
  -- The compactness theorem on each window.
  choose δ hδ hconv using fun j ↦ ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    hW hKs hKt hJ (hDc j) hK ((prod_mono (hDΩ j) subset_rfl).trans hΩKW)
    (fun z hz x hx ↦ hJt z (hDΩ j hz) x hx)
  -- The conclusion of that theorem on the window `j`, for a sequence `y`.
  set P : ℕ → (ℕ → ℝ × ℝ → V) → Prop := fun j y ↦ ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V),
    (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
      δ j ≤ ∫ y' in ball z ε ∩ O j, ω.floerEnergyDensity Ks Kt (y n) y') ∧
    (∀ C, IsCompact C → C ⊆ O j \ ↑Z →
      ∃ M, ∀ᶠ n in atTop, ∀ y' ∈ C, ‖fderiv ℝ (y n) y'‖ ≤ M) ∧
    ContinuousOn v (O j \ ↑Z) ∧ MapsTo v (O j \ ↑Z) K ∧
    TendstoLocallyUniformlyOn y v atTop (O j \ ↑Z)
  have hP : ∀ j (y z : ℕ → ℝ × ℝ → V) (ρ : ℕ → ℕ), P j y → Tendsto ρ atTop atTop →
      (∀ᶠ n in atTop, z n = y (ρ n)) → P j z := by
    rintro j y z ρ ⟨Z, v, hconc, hbd, hvc, hvK, hlim⟩ hρ hzy
    refine ⟨Z, v, fun c hc ε hε ↦ ?_, fun C hC hCZ ↦ ?_, hvc, hvK, fun s hs x hx ↦ ?_⟩
    · filter_upwards [hρ.eventually (hconc c hc ε hε), hzy] with n hn hzn
      rwa [hzn]
    · obtain ⟨M, hM⟩ := hbd C hC hCZ
      exact ⟨M, by filter_upwards [hρ.eventually hM, hzy] with n hn hzn; rwa [hzn]⟩
    · obtain ⟨t, ht, h⟩ := hlim s hs x hx
      exact ⟨t, ht, by filter_upwards [hρ.eventually h, hzy] with n hn hzn; rwa [hzn]⟩
  -- Every subsequence has a further subsequence converging on the window `j`.
  have hext : ∀ j (ψ : ℕ → ℕ), StrictMono ψ → ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
      P j (fun n ↦ u (ψ (ψ' n))) := by
    intro j ψ hψ
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hUC (D j) (hDc j) (hDΩ j))
    have hsub (n : ℕ) : O j ⊆ U (ψ (n + N)) :=
      (hOD j).trans (hN _ ((Nat.le_add_left N n).trans (hψ.id_le _)))
    obtain ⟨φ, Z, v, hφ, -, -, hconc, hbd, hvc, hvK, hlim⟩ := hconv j (hO j) (hOD j)
      (u := fun n ↦ u (ψ (n + N))) (E := E)
      (fun n ↦ (hu _).mono (hsub n)) (fun n z hz ↦ hfl _ z (hsub n hz))
      (fun n ↦ (huK _).mono_left (hsub n)) (fun n ↦ (hint _).mono_set (hsub n))
      (fun n ↦ (setIntegral_mono_set (hint _)
        (ae_restrict_of_forall_mem (hU _).measurableSet (hf0 _)) (hsub n).eventuallySubset).trans
          (hE _))
    refine ⟨fun n ↦ φ n + N, fun a b hab ↦ Nat.add_lt_add_right (hφ hab) N, Z, v, hconc,
      fun C hC hCZ ↦ ?_, hvc, hvK, hlim⟩
    obtain ⟨M, hM⟩ := hbd C hC hCZ
    exact ⟨M, Eventually.of_forall hM⟩
  -- A diagonal subsequence `φ` converges on every window.
  obtain ⟨φ, hφ, hPφ⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, P j (fun n ↦ u (φ n)) := by
    obtain ⟨φ, hφ, hPφ⟩ := extraction_forall (P := fun j ψ ↦ P j (fun n ↦ u (ψ n))) hext
    refine ⟨φ, hφ, fun j ↦ ?_⟩
    obtain ⟨ψ, hψ, hψφ⟩ := hPφ j
    obtain ⟨f, hf, hφf⟩ := exists_tendsto_eventuallyEq_comp_of_eq_apply_of_le hψφ
    exact hP j _ _ f hψ hf (hφf.mono fun n hn ↦ congrArg u hn)
  choose Zj vj hconc hbd hvc hvK hlim using hPφ
  -- The first window `j₀ y` whose interior contains `y`.
  have hex (y : ℝ × ℝ) (hy : y ∈ Ω) : ∃ j, y ∈ O j :=
    (hCO {y} isCompact_singleton (singleton_subset_iff.2 hy)).imp fun _ ↦ singleton_subset_iff.1
  set j₀ : ℝ × ℝ → ℕ := fun y ↦ if h : ∃ j, y ∈ O j then Nat.find h else 0
  have hj₀_eq {y : ℝ × ℝ} (h : ∃ j, y ∈ O j) : j₀ y = Nat.find h := by simp [j₀, h]
  have hj₀ {y : ℝ × ℝ} (hy : y ∈ Ω) : y ∈ O (j₀ y) := by
    rw [hj₀_eq (hex y hy)]
    exact Nat.find_spec (hex y hy)
  have hj₀_le {y : ℝ × ℝ} {j : ℕ} (hy : y ∈ O j) : j₀ y ≤ j := by
    rw [hj₀_eq ⟨j, hy⟩]
    exact Nat.find_min' _ hy
  -- The limits on the windows glue, and the bubbling points are those of the first window.
  set G : ℕ → Set (ℝ × ℝ) := fun j ↦ O j \ ↑(Zj j)
  have hG (j : ℕ) : IsOpen (G j) := (hO j).sdiff (Zj j).finite_toSet.isClosed
  obtain ⟨v, hv, hlimv⟩ := exists_tendstoLocallyUniformlyOn_iUnion hG hlim
  set Z : Set (ℝ × ℝ) := {y | y ∈ Ω ∧ y ∈ Zj (j₀ y)}
  have hyG {y : ℝ × ℝ} (hy : y ∈ Ω \ Z) : y ∈ G (j₀ y) := ⟨hj₀ hy.1, fun h ↦ hy.2 ⟨hy.1, h⟩⟩
  refine ⟨φ, Z, v, hφ, fun y hy ↦ hy.1, fun C hC hCΩ ↦ ?_, fun z hz ↦ ?_, fun C hC hCZ ↦ ?_,
    fun y hy ↦ ?_, fun y hy ↦ by rw [hv _ (hyG hy)]; exact hvK _ (hyG hy),
    hlimv.mono fun y hy ↦ mem_iUnion.2 ⟨_, hyG hy⟩⟩
  · -- A compact set lies in some window `O m`, so it only meets the bubbling points of the
    -- windows `j ≤ m`.
    obtain ⟨m, hm⟩ := hCO C hC hCΩ
    refine ((Finset.range (m + 1)).finite_toSet.biUnion fun j _ ↦ (Zj j).finite_toSet).subset ?_
    rintro y ⟨⟨-, hyZ⟩, hyC⟩
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le
      (hj₀_le (hm hyC))))) hyZ
  · -- Energy concentrates at `z` on the window `j₀ z`, which eventually lies in `U (φ n)`.
    refine ⟨δ (j₀ z), hδ _, fun ε hε ↦ ?_⟩
    filter_upwards [hconc _ z hz.2 ε hε, hφ.tendsto_atTop.eventually
      (hUC _ (hDc (j₀ z)) (hDΩ _))] with n hn hDU
    have hsub : ball z ε ∩ O (j₀ z) ⊆ ball z ε ∩ U (φ n) :=
      inter_subset_inter_right _ ((hOD _).trans hDU)
    exact hn.trans (setIntegral_mono_set ((hint _).mono_set inter_subset_right)
      (ae_restrict_of_forall_mem (measurableSet_ball.inter (hU _).measurableSet)
        fun y hy ↦ hf0 _ y hy.2) hsub.eventuallySubset)
  · -- Bounds on closed balls about the points of `C`, from their windows, cover `C`.
    refine hC.induction_on (p := fun s ↦ ∃ M, ∀ᶠ n in atTop, ∀ y ∈ s,
        ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ⟨0, by simp⟩
      (fun s t hst ⟨M, hM⟩ ↦ ⟨M, hM.mono fun n hn y hy ↦ hn y (hst hy)⟩)
      (fun s t ⟨M, hM⟩ ⟨M', hM'⟩ ↦ ⟨max M M', by
        filter_upwards [hM, hM'] with n hn hn' y hy
        rcases hy with hy | hy
        exacts [(hn y hy).trans (le_max_left _ _), (hn' y hy).trans (le_max_right _ _)]⟩)
      fun y hy ↦ ?_
    obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.1 (hG (j₀ y)) y (hyG (hCZ hy))
    refine ⟨closedBall y (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds y (by positivity)),
      hbd _ _ (isCompact_closedBall y _) ((closedBall_subset_ball (by linarith)).trans hrG)⟩
  · exact (((hvc _).continuousAt ((hG _).mem_nhds (hyG hy))).congr
      (eventuallyEq_of_mem ((hG _).mem_nhds (hyG hy)) (hv _).symm)).continuousWithinAt

end TauCeti.SymplecticForm
