/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
import TauCeti.MeasureTheory.Measure.BubblingSet
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.Compactness.SigmaCompact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of Floer solutions in a closed manifold on a whole domain

Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, such as a closed
symplectic manifold. The compactness theorem of
`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`
(`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in the
namespace `TauCeti.SmoothTwoForm`) works on a compact window `D` of the domain, with an energy
threshold `δ > 0` depending on the window. On a domain `Ω` that is not relatively compact, such
as a punctured Riemann surface, it applies on each window of an exhaustion of `Ω` by open sets
with compact closures, and a diagonal subsequence (`TauCeti.extraction_forall_of_antitone`)
converges on all of `Ω`
(`IsNondegenerate.exists_tendstoLocallyUniformlyOn_comp_subseq_off_discrete`). This is the
closed-manifold counterpart of the theorem for a symplectic vector space target in
`TauCeti.Geometry.Symplectic.Floer.Compactness.Exhaustion`, with no condition on the images of the
solutions.

As there, sizes in `M` are measured through an injective differentiable map `e : M → F` into a
normed space, such as the Whitney embedding of `M`, and the solutions may live on open sets `Uₖ`
that only eventually contain each compact subset of `Ω`, as on domains whose necks stretch. The
uniform tameness of the structures with respect to `e` and the bounds on the pushforwards of the
Hamiltonian vector fields are only required over each compact subset of `Ω`.

A point of `Ω` is a bubbling point when it is a bubbling point of every window containing it.
Off these points the limits on the windows agree, since `M` is Hausdorff, as `e` maps it
injectively and continuously into `F`, so they glue to one limit in `M`. The bubbling points form
a set meeting each compact subset of `Ω` in finitely many points, each carrying a positive amount
of energy (`TauCeti.exists_bubblingSet_of_forall_window`). Without an energy threshold uniform
over `Ω`, which on cylindrical ends needs the translation invariance of the data there, this set is
not shown to be finite.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points on a noncompact domain, through an exhaustion by compact
  sets).
-/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- The diagonal step of the exhaustion argument. For open windows `O j` with compact closures in
`Ω`, each eventually contained in the domains `Uₖ` of the solutions, there are thresholds
`δ j > 0` and one subsequence `φ` converging on every window `O j` off a finite set of bubbling
points, through a diagonal extraction (`TauCeti.extraction_forall_of_antitone`). -/
private theorem IsNondegenerate.exists_subseq_forall_window (hω : ω.IsNondegenerate) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (Ω ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (Ω ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (Ω ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ Ω, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    (hJc : ∀ C, IsCompact C → C ⊆ Ω → ∃ c > 0, ∀ z ∈ C, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hB : ∀ C, IsCompact C → C ⊆ Ω → ∃ B, ∀ z ∈ C, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B ∧
        ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    {O : ℕ → Set (ℝ × ℝ)} (hO : ∀ j, IsOpen (O j)) (hOc : ∀ j, IsCompact (closure (O j)))
    (hOΩ : ∀ j, closure (O j) ⊆ Ω) {U : ℕ → Set (ℝ × ℝ)} {u : ℕ → ℝ × ℝ → M} {E₀ : ℝ}
    (hU : ∀ k, IsOpen (U k)) (hOU : ∀ j, ∀ᶠ k in atTop, closure (O j) ⊆ U k)
    (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) (U k))
    (hfl : ∀ k, ∀ y ∈ U k, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u k y))
      (ω.perturbedMFDeriv Ks Kt (u k) y).toLinearMap)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) (U k))
    (hE : ∀ k, ∫ y in U k, ω.floerEnergyDensity Ks Kt (u k) y ≤ E₀)
    (hf0 : ∀ k, ∀ y ∈ U k, 0 ≤ ω.floerEnergyDensity Ks Kt (u k) y) :
    ∃ (δ : ℕ → ℝ) (φ : ℕ → ℕ), (∀ j, 0 < δ j) ∧ StrictMono φ ∧
      ∀ j, ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M),
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ j ≤ ∫ y in ball z ε ∩ O j, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ O j \ ↑Z →
          ∃ A, ∀ᶠ n in atTop, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ A) ∧
        ContinuousOn v (O j \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (O j \ ↑Z) ∧
        ∀ y ∈ O j \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y)) := by
  -- The thresholds of the compactness theorem on the windows.
  choose c hc hJc' using fun j ↦ hJc _ (hOc j) (hOΩ j)
  choose B hB' using fun j ↦ hB _ (hOc j) (hOΩ j)
  choose δ hδ hconv using fun j ↦
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset he he_inj hΩ (hOc j)
      (hOΩ j) hJ hXs hXt (fun z hz ↦ hJt z (hOΩ j hz)) (hc j) (hJc' j)
      (fun z hz x ↦ (hB' j z hz x).1) fun z hz x ↦ (hB' j z hz x).2
  -- The properties of the filter of a subsequence on the window `j`; they pass to finer filters.
  let P : ℕ → Filter ℕ → Prop := fun j l ↦ ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M),
    (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ k in l,
      δ j ≤ ∫ y in ball z ε ∩ O j, ω.floerEnergyDensity Ks Kt (u k) y) ∧
    (∀ C, IsCompact C → C ⊆ O j \ ↑Z →
      ∃ A, ∀ᶠ k in l, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u k) y ≤ A) ∧
    ContinuousOn v (O j \ ↑Z) ∧
    TendstoLocallyUniformlyOn (fun k ↦ e ∘ u k) (e ∘ v) l (O j \ ↑Z) ∧
    ∀ y ∈ O j \ ↑Z, Tendsto (fun k ↦ u k y) l (𝓝 (v y))
  -- Every subsequence has a further subsequence converging on the window `j`, so a diagonal
  -- subsequence `φ` converges on every window.
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_antitone (P := P)
    (fun j _ _ hl ⟨Z, v, hconc, hbd, hvc, hlim, hpt⟩ ↦ ⟨Z, v,
      fun z hz ε hε ↦ (hconc z hz ε hε).filter_mono hl,
      fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hA ↦ hA.filter_mono hl, hvc,
      hlim.comp_tendsto (tendsto_id'.2 hl), fun y hy ↦ (hpt y hy).mono_left hl⟩) fun j ψ hψ ↦ by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hOU j)
    have hsub (n : ℕ) : O j ⊆ U (ψ (n + N)) :=
      subset_closure.trans (hN _ ((Nat.le_add_left N n).trans (hψ.id_le _)))
    obtain ⟨φ, hφ, Z, -, -, hZ, hbd, v, hv, hlim, hpt⟩ := hconv j (hO j) subset_closure
      (u := fun n ↦ u (ψ (n + N))) (E₀ := E₀) (fun n ↦ (hu _).mono (hsub n))
      (fun n y hy ↦ hfl _ y (hsub n hy)) (fun n ↦ (hint _).mono_set (hsub n))
      (fun n ↦ (setIntegral_mono_set (hint _)
        (ae_restrict_of_forall_mem (hU _).measurableSet (hf0 _)) (hsub n).eventuallySubset).trans
          (hE _))
    exact ⟨fun n ↦ φ n + N, fun a b hab ↦ Nat.add_lt_add_right (hφ hab) N, Z, v,
      fun z hz ε hε ↦ eventually_map.2 (hZ z hz ε hε),
      fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hA ↦ eventually_map.2 (.of_forall hA), hv,
      tendstoLocallyUniformlyOn_map_iff.2 hlim, fun y hy ↦ tendsto_map'_iff.2 (hpt y hy)⟩
  refine ⟨δ, φ, hδ, hφ, fun j ↦ ?_⟩
  obtain ⟨Z, v, hconc, hbd, hvc, hlim, hpt⟩ := hP j
  exact ⟨Z, v, fun z hz ε hε ↦ eventually_map.1 (hconc z hz ε hε),
    fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hA ↦ eventually_map.1 hA, hvc,
    tendstoLocallyUniformlyOn_map_iff.1 hlim, fun y hy ↦ tendsto_map'_iff.1 (hpt y hy)⟩

/-- **Floer solutions of bounded energy on a whole domain in a closed manifold converge off a
discrete set.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, such as
a closed symplectic manifold. Let the structures `J(z, x)` and the Hamiltonian vector fields of
`K_s` and `K_t`, read in the chart at every point, be `C²` on `Ω × (extChartAt I α).target` for an
open domain `Ω ⊆ ℝ × ℝ`, with `J(z, x)` tamed by `ω` for `z ∈ Ω`. Let `e : M → F` be an injective
differentiable map into a normed space, such as the Whitney embedding, and over each compact subset
of `Ω` let the structures be uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with
`c > 0`, and the pushforwards `d e (X_{K_s})`, `d e (X_{K_t})` bounded. Let `uₖ` be `C³` solutions
of the Floer equation `(du - X_K)^{0,1} = 0` on open sets `Uₖ ⊆ Ω` which eventually contain every
compact subset of `Ω`, with integrable Floer energy densities `ρₖ` and Floer energy
`∫_{Uₖ} ρₖ ≤ E₀`. Then there are a subsequence `φ`, a set `Z ⊆ Ω` of bubbling points meeting every
compact subset of `Ω` in a finite set, and a map `v`, continuous on `Ω \ Z`, such that along `φ`

* every disc about a point of `Z` eventually carries energy at least some `δ > 0` depending on the
  point;
* the energy densities are eventually uniformly bounded on every compact subset of `Ω \ Z`;
* the solutions converge to `v` on `Ω \ Z`, locally uniformly after applying `e` and pointwise in
  `M`.

No condition is put on the images of the solutions. -/
theorem IsNondegenerate.exists_tendstoLocallyUniformlyOn_comp_subseq_off_discrete
    (hω : ω.IsNondegenerate) {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : Injective e) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (Ω ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (Ω ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (Ω ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ Ω, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    (hJc : ∀ C, IsCompact C → C ⊆ Ω → ∃ c > 0, ∀ z ∈ C, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hB : ∀ C, IsCompact C → C ⊆ Ω → ∃ B, ∀ z ∈ C, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B ∧
        ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    {U : ℕ → Set (ℝ × ℝ)} {u : ℕ → ℝ × ℝ → M} {E₀ : ℝ}
    (hU : ∀ k, IsOpen (U k)) (hUΩ : ∀ k, U k ⊆ Ω)
    (hUC : ∀ C, IsCompact C → C ⊆ Ω → ∀ᶠ k in atTop, C ⊆ U k)
    (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) (U k))
    (hfl : ∀ k, ∀ y ∈ U k, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u k y))
      (ω.perturbedMFDeriv Ks Kt (u k) y).toLinearMap)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) (U k))
    (hE : ∀ k, ∫ y in U k, ω.floerEnergyDensity Ks Kt (u k) y ≤ E₀) :
    ∃ (φ : ℕ → ℕ) (Z : Set (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono φ ∧ Z ⊆ Ω ∧
      (∀ C, IsCompact C → C ⊆ Ω → (Z ∩ C).Finite) ∧
      (∀ z ∈ Z, ∃ δ > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        δ ≤ ∫ y in ball z ε ∩ U (φ n), ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
      (∀ C, IsCompact C → C ⊆ Ω \ Z →
        ∃ A, ∀ᶠ n in atTop, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ A) ∧
      ContinuousOn v (Ω \ Z) ∧
      TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ Z) ∧
      ∀ y ∈ Ω \ Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y)) := by
  have hf0 (k : ℕ) : ∀ y ∈ U k, 0 ≤ ω.floerEnergyDensity Ks Kt (u k) y := fun y hy ↦
    floerEnergyDensity_nonneg hω (hJt y (hUΩ k hy) _) (hfl k y hy)
  -- Open windows `O j` exhausting `Ω`, with compact closures in `Ω`, and a subsequence `φ`
  -- converging on each of them.
  have := hΩ.locallyCompactSpace
  obtain ⟨O, hO, hOc, hOΩ, hmono, hUn⟩ := hΩ.exists_iUnion_isOpen_isCompact_closure
  obtain ⟨δ, φ, hδ, hφ, hPφ⟩ := hω.exists_subseq_forall_window he he_inj hΩ hJ hXs hXt hJt hJc hB
    hO hOc hOΩ hU (fun j ↦ hUC _ (hOc j) (hOΩ j)) hu hfl hint hE hf0
  choose Zj vj hconc hbd hvc hlim hpt using hPφ
  -- The bubbling points are the points of `Ω` lying off the regular part of every window.
  obtain ⟨Z, hZΩ, hΩZ, hZC, hZconc, hZbd⟩ := exists_bubblingSet_of_forall_window
    (U := fun n ↦ U (φ n)) (f := fun n ↦ ω.floerEnergyDensity Ks Kt (u (φ n)))
    (g := fun n ↦ ω.floerEnergyDensity Ks Kt (u (φ n))) hO hmono.directed_le hUn
    (fun _ ↦ (hU _).measurableSet) (fun _ ↦ hint _) (fun _ ↦ hf0 _)
    (fun j ↦ (hφ.tendsto_atTop.eventually (hUC _ (hOc j) (hOΩ j))).mono fun _ h ↦
      subset_closure.trans h) hδ hconc hbd
  have hG (j : ℕ) : IsOpen (O j \ ↑(Zj j)) := (hO j).sdiff (Zj j).finite_toSet.isClosed
  -- `M` is Hausdorff, since `e` maps it injectively into `F`, so the limits on the windows glue.
  have : T2Space M := .of_injective_continuous he_inj
    (continuous_iff_continuousAt.2 fun x ↦ (he x).continuousAt)
  have : Nonempty M := ⟨u 0 0⟩
  set v : ℝ × ℝ → M := fun y ↦ limUnder atTop fun n ↦ u (φ n) y
  have hv (j : ℕ) : EqOn v (vj j) (O j \ ↑(Zj j)) := fun y hy ↦ (hpt j y hy).limUnder_eq
  refine ⟨φ, Z, v, hφ, hZΩ, hZC, hZconc, hZbd,
    hΩZ ▸ ContinuousOn.iUnion_of_isOpen (fun j ↦ (hvc j).congr (hv j)) hG,
    hΩZ ▸ tendstoLocallyUniformlyOn_iUnion hG fun j ↦
      (hlim j).congr_right fun y hy ↦ by simp [hv j hy], fun y hy ↦ ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hΩZ ▸ hy)
  exact hv j hj ▸ hpt j y hj

end TauCeti.SmoothTwoForm
