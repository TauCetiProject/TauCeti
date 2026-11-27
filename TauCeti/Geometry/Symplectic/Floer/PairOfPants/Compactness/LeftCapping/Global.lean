/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Global
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.LeftCapping.Closed
import TauCeti.Data.ENNReal.NatCastDiv
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.MeasureTheory.Measure.BubblingSet
import TauCeti.Topology.Compactness.Compact

/-!
# Compactness of the input-exchange family capped at `0` on the whole capped domain

The pair-of-pants product is unital on the left because gluing the negative PSS plane of `H_0`
into the input at `0` of the pair of pants `S = ℂ ∖ {0, 1}` gives a cylinder whose counts compare
with continuation maps. The comparison runs along the input-exchange family capped at `0`: the
perturbations `K_c = TauCeti.Floer.cappedExchangePerturbation H L c`, `c ∈ [0, 1]`, at a fixed
neck length `L > 4`, on the capped domain `S₁ = ℂ ∖ {1}`, where `0` is an ordinary point. Its
solutions have one input end, at `1`, and one output end, the end at `∞` recentred at `c`.
Gromov–Floer compactness for this family is known on one compact window of `S₁` at a time
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedExchange` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). This file proves it on the whole capped domain,
in a closed manifold `M`: a sequence of solutions for parameters in a compact window
`C ⊆ [0, 1]`, of topological energy at most `A`, has a subsequence whose parameters converge in
`C` and which converges on all of `S₁` off a finite set `Z` of bubbling points, with
`#Z * δ ≤ A + (B₀ + (B₀ + B₁ + B_∞))` for a threshold `δ > 0` that depends only on the data. The
bubbling set may contain the point `0`, where the plane is inserted.

The domain `S₁` is the union of two windows, the pair of pants `S` and the disc `|w| < 1/4`
about the capped puncture.

* **On `S`.** The family is cylindrical on the three ends of `S`, with data independent of `c`,
  once the Hamiltonian of the capped end is set to `0`: beyond the height `L` of an input end it
  is `H_1(t) dt` on the end at `1` and `0` on the end at `0`
  (`TauCeti.Floer.cappedExchangePerturbation_eq_smul_endAngularForm`), and beyond the height `2`
  of the output end its translate `w ↦ K_c(w + c)` is `H_∞(t) dt`
  (`TauCeti.Floer.cappedExchangePerturbation_add_eq_smul_endAngularForm`). The whole-domain
  compactness theorem for families with a recentred output end,
  `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered` in
  the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, applies with the centre `a(c) = c`. The
  components of `K_c` are `C³` jointly in the parameter, the point of `S₁` and the target point
  (`TauCeti.Floer.contMDiffAt_uncurry_cappedExchangePerturbation_apply`), so their Hamiltonian
  vector fields are `C²` in every chart and bounded over compact parts of `C × S₁`.
* **On the disc.** The disc lies in a compact window of `S₁`, where the compactness theorem of the
  family on compact windows applies.

The energy over every part of `S₁` is at most the topological energy plus
`B₀ + (B₀ + B₁ + B_∞)`
(`IsNondegenerate.setIntegral_floerEnergyDensity_cappedExchangePerturbation_le`), and the
diagonal argument over the two windows
(`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le`) runs for the energy
measures of the solutions on `S₁`; the point `0` is a null set, so these are the energy measures
on `S`.

The structures `J_c` are taken cylindrical beyond some height `T₀` on each end of `S`: in the end
chart of an input end and in the end chart recentred at `c` of the output end, with end structures
independent of `c`. On the capped end this forces `J_c` to be constant near `0`, as the
structures of the family are near the pole of the inserted plane. The bubbles at the points of
`Z`, the regularity of the limit and the Floer cylinders breaking off along the two ends are not
treated here.

## Main results

* `exists_pos_forall_tendstoLocallyUniformlyOn_off_finset_cappedExchange_ne_one`, in the
  namespace `TauCeti.SmoothTwoForm.IsNondegenerate`: compactness off finitely many bubbling points
  on the whole capped domain `ℂ ∖ {1}` for the input-exchange family capped at `0` in a closed
  manifold.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points on a noncompact domain).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

/-- **Two windows.** Let `g n ≥ 0` be densities on an open set `S₁ = U₁ ∪ U₂` with integrals at
most `E` over `S₁`. Suppose that on each window `Uᵢ` every subsequence has a further subsequence
converging locally uniformly off a set `Zᵢ`, at whose points energy `δ > 0` of the densities over
`Uᵢ` concentrates, with the densities eventually bounded near every other point of `Uᵢ`. Then one
subsequence converges on `S₁` off a finite set `Z` with `#Z * δ ≤ E`, with the energy `δ` over `S₁`
concentrating at the points of `Z` and the densities eventually bounded near every point of
`S₁ \ Z`. -/
private theorem exists_subseq_off_finset_union {α : Type*} [UniformSpace α] [T2Space α]
    {U₁ U₂ S₁ : Set (ℝ × ℝ)} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : U₁ ∪ U₂ = S₁)
    {f : ℕ → ℝ × ℝ → α} {g : ℕ → ℝ × ℝ → ℝ} {δ E : ℝ} (hδ : 0 < δ)
    (hg0 : ∀ n, ∀ z ∈ S₁, 0 ≤ g n z) (hint : ∀ n, IntegrableOn (g n) S₁)
    (hE : ∀ n, ∫ z in S₁, g n z ≤ E)
    (h : ∀ b : Bool, ∀ ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set (ℝ × ℝ), (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
        δ ≤ ∫ y in ball z ε ∩ cond b U₁ U₂, g (ψ (φ n)) y) ∧
      (∀ y ∈ cond b U₁ U₂ \ Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, g (ψ (φ n)) x ≤ A) ∧
      ∃ v : ℝ × ℝ → α, TendstoLocallyUniformlyOn (fun n ↦ f (ψ (φ n))) v atTop
        (cond b U₁ U₂ \ Z)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → α), ↑Z ⊆ S₁ ∧
      Z.card * δ ≤ E ∧ (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ S₁, g (φ n) y) ∧
      (∀ y ∈ S₁ \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, g (φ n) x ≤ A) ∧
      TendstoLocallyUniformlyOn (fun n ↦ f (φ n)) v atTop (S₁ \ ↑Z) := by
  have hS₁ : MeasurableSet S₁ := (hU ▸ hU₁.union hU₂ : IsOpen S₁).measurableSet
  have hE0 : 0 ≤ E := (setIntegral_nonneg hS₁ (hg0 0)).trans (hE 0)
  have hUS (b : Bool) : cond b U₁ U₂ ⊆ S₁ := by
    cases b
    · exact hU ▸ subset_union_right
    · exact hU ▸ subset_union_left
  -- The diagonal argument for the energy measures of the densities on `S₁`.
  obtain ⟨φ, Z, v, hφ, hZ, hcard, hconc, hbd, hv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le (U := fun b ↦ cond b U₁ U₂)
      (fun b ↦ by cases b <;> assumption) (F := f) (G := g)
      (μ := fun n ↦ (volume.restrict S₁).withDensity fun y ↦ ENNReal.ofReal (g n y))
      (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top
      (fun n ↦ (measure_mono (subset_univ _)).trans (by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          ← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_restrict_of_forall_mem hS₁ (hg0 n))]
        exact ENNReal.ofReal_le_ofReal (hE n))) fun b ψ hψ ↦ by
      obtain ⟨φ, hφ, Z, hconc, hbd, v, hv⟩ := h b hψ
      refine ⟨φ, hφ, Z, fun z hz ↦ ?_, hbd, v, hv⟩
      exact eventually_ofReal_le_withDensity_of_forall_eventually_le_setIntegral_ball
        (by cases b <;> [exact hU₂.measurableSet; exact hU₁.measurableSet]) (hUS b) (hconc z hz)
  rw [← union_eq_iUnion, hU] at hZ hbd hv
  refine ⟨φ, hφ, Z, v, hZ, (ENNReal.natCast_mul_ofReal_le_ofReal_iff hE0).1 hcard,
    fun z hz ε hε ↦ ?_, hbd, hv⟩
  -- The energy measure of a disc is the energy over its part in `S₁`.
  filter_upwards [hconc z hz _ (ball_mem_nhds z hε)] with n hn
  exact TauCeti.MeasureTheory.le_setIntegral_of_ofReal_le_withDensity measurableSet_ball hS₁
    ((hint _).mono_set inter_subset_right) (fun y hy ↦ hg0 _ y hy.2) hn

/-- **Two windows, read back in a compact space.** As
`exists_subseq_off_finset_union`, for maps `uₙ` continuous on `S₁` with values in a compact
space `M`, read through a continuous injection `e : M → F` on the windows, where on the second
window the densities are bounded on compact subsets off its bubbling points. The limit is read
back in `M`: it is continuous on `S₁ \ Z`, and the maps converge to it locally uniformly after
applying `e` and pointwise in `M`. -/
private theorem exists_subseq_off_finset_union_comp {M F : Type*} [TopologicalSpace M]
    [CompactSpace M] [UniformSpace F] [T2Space F] {U₁ U₂ S₁ : Set (ℝ × ℝ)} (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂) (hU : U₁ ∪ U₂ = S₁) {u : ℕ → ℝ × ℝ → M} {e : M → F} (he : Continuous e)
    (he_inj : Injective e) (hu : ∀ n, ContinuousOn (u n) S₁) {g : ℕ → ℝ × ℝ → ℝ} {δ E : ℝ}
    (hδ : 0 < δ) (hg0 : ∀ n, ∀ z ∈ S₁, 0 ≤ g n z) (hint : ∀ n, IntegrableOn (g n) S₁)
    (hE : ∀ n, ∫ z in S₁, g n z ≤ E)
    (h₁ : ∀ ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ),
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ U₁, g (ψ (φ n)) y) ∧
      (∀ y ∈ U₁ \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, g (ψ (φ n)) x ≤ A) ∧
      ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (ψ (φ n))) v atTop (U₁ \ ↑Z))
    (h₂ : ∀ ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ),
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ U₂, g (ψ (φ n)) y) ∧
      (∀ K, IsCompact K → K ⊆ U₂ \ ↑Z → ∃ A, ∀ n, ∀ y ∈ K, g (ψ (φ n)) y ≤ A) ∧
      ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (ψ (φ n))) v atTop (U₂ \ ↑Z)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), ↑Z ⊆ S₁ ∧
      Z.card * δ ≤ E ∧ (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ S₁, g (φ n) y) ∧
      (∀ y ∈ S₁ \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, g (φ n) x ≤ A) ∧
      ContinuousOn v (S₁ \ ↑Z) ∧
      TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (S₁ \ ↑Z) ∧
      ∀ z ∈ S₁ \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- On the second window, bounds on compact sets give bounds near every point.
  have h₂' : ∀ ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set (ℝ × ℝ),
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ U₂, g (ψ (φ n)) y) ∧
      (∀ y ∈ U₂ \ Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, g (ψ (φ n)) x ≤ A) ∧
      ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (ψ (φ n))) v atTop (U₂ \ Z) := by
    intro ψ hψ
    obtain ⟨φ, hφ, Z, hconc, hbd, v, hv⟩ := h₂ hψ
    refine ⟨φ, hφ, Z, hconc, fun y hy ↦ ?_, v, hv⟩
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 (hU₂.sdiff Z.finite_toSet.isClosed) y hy
    obtain ⟨A, hA⟩ := hbd _ (isCompact_closedBall y (r / 2))
      ((closedBall_subset_ball (by linarith)).trans hrsub)
    exact ⟨_, closedBall_mem_nhds y (by positivity), A, .of_forall fun n x hx ↦ hA n x hx⟩
  obtain ⟨φ, hφ, Z, w, hZ, hcard, hconc, hbd, hconv⟩ :=
    exists_subseq_off_finset_union hU₁ hU₂ hU (f := fun n ↦ e ∘ u n) hδ hg0 hint hE
      fun b ↦ by
        cases b
        · exact h₂'
        · intro ψ hψ
          obtain ⟨φ, hφ, Z, hconc, hbd, v, hv⟩ := h₁ hψ
          exact ⟨φ, hφ, Z, hconc, hbd, v, hv⟩
  -- The limit is continuous, and it is read back in `M` through `e`.
  have hw : ContinuousOn w (S₁ \ ↑Z) :=
    hconv.continuousOn (Eventually.of_forall fun n ↦
      (he.comp_continuousOn (hu (φ n))).mono sdiff_subset).frequently
  obtain ⟨v, hv, -, hev, hpt⟩ := isCompact_univ.exists_tendsto_of_tendsto_comp
    he.continuousOn he_inj.injOn (fun _ _ ↦ .of_forall fun _ ↦ mem_univ _) hw
    fun z hz ↦ hconv.tendsto_at hz
  exact ⟨φ, hφ, Z, v, hZ, hcard, hconc, hbd, hv, hconv.congr_right hev.symm, hpt⟩

/-- **The two windows of the capped domain.** The capped domain `S₁ = ℂ ∖ {1}` is the union of
the pair of pants `S = ℂ ∖ {0, 1}` and the disc `|w| < 1/4` about the capped puncture, the closed
disc `|w| ≤ 1/4` is a compact part of `S₁`, and `S₁` lies in `S` up to a null set. -/
private theorem thricePuncturedSphereReal_union_ball_and_ae_le :
    thricePuncturedSphereReal ∪ equivRealProdCLM.symm ⁻¹' ball 0 (1 / 4) =
      {z | equivRealProdCLM.symm z ≠ 1} ∧
    thricePuncturedSphereReal ⊆ {z | equivRealProdCLM.symm z ≠ 1} ∧
    IsCompact (equivRealProdCLM.symm ⁻¹' closedBall (0 : ℂ) (1 / 4)) ∧
    equivRealProdCLM.symm ⁻¹' closedBall (0 : ℂ) (1 / 4) ⊆ {z | equivRealProdCLM.symm z ≠ 1} ∧
    {z | equivRealProdCLM.symm z ≠ 1} ≤ᵐ[volume] thricePuncturedSphereReal := by
  have hD : equivRealProdCLM.symm ⁻¹' closedBall (0 : ℂ) (1 / 4) ⊆
      {z | equivRealProdCLM.symm z ≠ 1} := fun z hz h ↦ by
    rw [mem_preimage, mem_closedBall_zero_iff, h, norm_one] at hz
    norm_num at hz
  refine ⟨?_, fun z hz ↦ (mem_thricePuncturedSphereReal_iff.1 hz).2,
    equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _), hD,
    by filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz _ using hz⟩
  ext z
  refine ⟨fun hz ↦ hz.elim (fun hz ↦ (mem_thricePuncturedSphereReal_iff.1 hz).2)
    fun hz ↦ hD (preimage_mono ball_subset_closedBall hz), fun hz ↦ ?_⟩
  by_cases h0 : equivRealProdCLM.symm z = 0
  · exact Or.inr (by rw [mem_preimage, mem_ball_zero_iff, h0, norm_zero]; norm_num)
  · exact Or.inl (mem_thricePuncturedSphereReal_iff.2 ⟨h0, hz⟩)

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {L : ℝ} {e : M → F}

omit [I.Boundaryless] in
/-- Over a compact window of parameters and a compact part of the capped domain, the pushforwards
through `e` of the Hamiltonian vector fields of the components of the family are bounded. -/
private theorem exists_forall_norm_mvfderiv_hamiltonianVectorField_cappedExchange_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q))) (hL : 4 < L)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} (hC : IsCompact C) (hD : IsCompact D)
    (hD₁ : ∀ z ∈ D, equivRealProdCLM.symm z ≠ 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    ∃ L', ∀ c ∈ C, ∀ z ∈ D, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) y 1) x)‖ ≤ L' ∧
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤
        L' := by
  have hL' (w : ℂ) := hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le_of_isCompact
    (hC.prod hD) he (f := fun (p : ℝ × (ℝ × ℝ)) y ↦
      cappedExchangePerturbation H L p.1 (equivRealProdCLM.symm p.2) y w)
    fun p hp x ↦
      (contMDiffAt_uncurry_cappedExchangePerturbation_apply hH hHs hL w (hD₁ _ hp.2) x).of_le
        (by norm_num)
  obtain ⟨Ls, hLs⟩ := hL' 1
  obtain ⟨Lt, hLt⟩ := hL' Complex.I
  exact ⟨max Ls Lt, fun c hc z hz x ↦ ⟨(hLs (c, z) ⟨hc, hz⟩ x).trans (le_max_left _ _),
    (hLt (c, z) ⟨hc, hz⟩ x).trans (le_max_right _ _)⟩⟩

/-- **On the pair of pants.** With the Hamiltonian of the capped end set to `0`, the family is
cylindrical on the three ends of `S = ℂ ∖ {0, 1}`, its output end recentred at the parameter, so
the whole-domain compactness theorem for families with a recentred output end applies on `S`. -/
private theorem exists_pos_forall_subseq_off_finset_thricePuncturedSphereReal_cappedExchange
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q))) (hL : 4 < L)
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (ℝ × (ℝ × ℝ))} {C : Set ℝ} (hW : IsOpen W) (hC : IsCompact C)
    (hC₀₁ : C ⊆ Icc 0 1) (hCW : C ×ˢ thricePuncturedSphereReal ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ c ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J c z x))
    (hJc : ∀ D, IsCompact D → D ⊆ thricePuncturedSphereReal → ∃ κ > 0, ∀ c ∈ C, ∀ z ∈ D,
      ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J c z x v))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ c ∈ C, ∀ q, q ≠ .inf → ∀ s t x, T₀ ≤ s →
      J c (endChart q (q.endSign * s, t)) x = Jq q t x)
    (hJe' : ∀ c ∈ C, ∀ s t x, T₀ ≤ s → J c (endChart .inf (-s, t) + (c, 0)) x = Jq .inf t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E : ℝ⦄, (∀ k, c k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (c k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
        (u k)) thricePuncturedSphereReal) →
      (∀ k, ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
        (u k) z ≤ E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c₀ ∈ C, Tendsto (fun n ↦ c (φ n)) atTop (𝓝 c₀) ∧
        ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), ↑Z ⊆ thricePuncturedSphereReal ∧
        Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ thricePuncturedSphereReal,
          ω.floerEnergyDensity
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x
              Complex.I) (u (φ n)) y) ∧
        (∀ y ∈ thricePuncturedSphereReal \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ w ∈ N,
          ω.floerEnergyDensity
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x
              Complex.I) (u (φ n)) w ≤ A) ∧
        ContinuousOn v (thricePuncturedSphereReal \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          (thricePuncturedSphereReal \ ↑Z) ∧
        ∀ z ∈ thricePuncturedSphereReal \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hS₁ (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) : equivRealProdCLM.symm z ≠ 1 :=
    (mem_thricePuncturedSphereReal_iff.1 hz).2
  -- Each component of the perturbations is `C³` jointly in the parameter, the domain point and
  -- the target point, so its Hamiltonian vector field is `C²` in every chart.
  have hK (w : ℂ) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ univ ×ˢ thricePuncturedSphereReal) (x : M) :=
    contMDiffAt_uncurry_cappedExchangePerturbation_apply (n := (2 : ℕ∞) + 1) hH hHs hL w
      (hS₁ _ hp.2) x
  have hWS : IsOpen (W ∩ univ ×ˢ thricePuncturedSphereReal) :=
    hW.inter (isOpen_univ.prod isOpen_thricePuncturedSphereReal)
  -- Beyond the height `max T₀ L` the family is `H_1(t) dt` and `0` on the input ends, and its
  -- translate by `c` is `H_∞(t) dt` on the output end.
  exact hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered
    (H := update H zero 0) (K := fun c ↦ cappedExchangePerturbation H L c) (J := J) hWS hC
    (subset_inter hCW (prod_mono (subset_univ _) subset_rfl))
    (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
    (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).mono
      (prod_mono inter_subset_right subset_rfl))
    (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).mono
      (prod_mono inter_subset_right subset_rfl))
    hJt hJc (fun D hD hDS ↦ exists_forall_norm_mvfderiv_hamiltonianVectorField_cappedExchange_le
      hω hH hHs hL hC hD (fun z hz ↦ hS₁ z (hDS hz)) he) (a := id) continuousOn_id
    (T₀ := max T₀ L)
    (fun c hc q hq w x hw ↦ cappedExchangePerturbation_eq_smul_endAngularForm (by linarith)
      (hC₀₁ hc).1 (hC₀₁ hc).2 hq ((le_max_right _ _).trans hw) x)
    (fun c hc w x hw ↦ by
      rw [update_of_ne (by decide)]
      exact cappedExchangePerturbation_add_eq_smul_endAngularForm (by linarith) (hC₀₁ hc).1
        (hC₀₁ hc).2 (by linarith [le_max_right T₀ L]) x)
    (forall_update_zero (P := fun f ↦ Periodic f 1) (fun _ ↦ rfl) hH zero)
    (forall_update_zero (P := fun f ↦ ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry f))
      contMDiff_const hHs zero)
    (fun c hc q hq s t x hs ↦ hJe c hc q hq s t x ((le_max_left _ _).trans hs))
    (fun c hc s t x hs ↦ hJe' c hc s t x ((le_max_left _ _).trans hs)) he he_inj

/-- **Solutions of the input-exchange family capped at `0` in a closed manifold converge off
finitely many bubbling points on the whole capped domain.** Let `ω` be a nondegenerate two-form on
a closed manifold `M`, let `H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, fix a neck
length `L > 4`, and let `K_c` be the perturbations of the input-exchange family capped at `0`. Let
`J_c(z, x)` be structures on the tangent spaces of `M`, tamed by `ω` for `c` in a compact window
`C ⊆ [0, 1]` of parameters and `z` in the capped domain `S₁ = ℂ ∖ {1}` (in real coordinates),
which read in the chart at every point of `M` are `C²` jointly in `(c, z, y)` on
`W × (chart target)` for an open `W ⊇ C × S₁`, and which beyond `T₀` are structures `J_q(t, x)`
independent of `c` in the end coordinates of each input end `q` of `S = ℂ ∖ {0, 1}` and of the
output end recentred at `c`. Let `e : M → F` be an injective `C¹` map into a normed space, such as
the Whitney embedding, and over every compact `D ⊆ S₁` let the structures `J_c`, `c ∈ C`, be
uniformly tame with respect to `e`. There is a threshold `δ > 0` with the following property. Let
`uₖ` be `C³` maps from `S₁` to `M` solving the Floer equation `(du - X_{K_{cₖ}})^{0,1} = 0` there
for the structures `J_{cₖ}(z, u)`, with `cₖ ∈ C`, whose loops along the input end at `1` and along
the output end recentred at `cₖ` converge pointwise to loops `x₁ₖ` and `x_∞ₖ`, whose Floer energy
and symplectic area densities are integrable over `S`, and whose topological energy
`∫_S uₖ^*ω + ∫₀¹ H_1(t, x₁ₖ(t)) dt - ∫₀¹ H_∞(t, x_∞ₖ(t)) dt` is at most `A`. Then there are a
subsequence `φ`, a limit `c₀ ∈ C` of the parameters `c_{φ n}`, a finite set `Z ⊆ S₁` with
`#Z * δ ≤ A + (B_0 + (B_0 + B_1 + B_∞))` and a map `v : S₁ \ Z → M`, continuous, such that along
`φ` every disc about a point of `Z` eventually carries energy at least `δ`, the energy densities
are eventually bounded near every point of `S₁ \ Z`, and the solutions converge to `v` on
`S₁ \ Z`, locally uniformly after applying `e` and pointwise in `M`. The point `0`, where the
plane is inserted, is treated like any other point of `S₁`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_off_finset_cappedExchange_ne_one
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hL : 4 < L)
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (ℝ × (ℝ × ℝ))} {C : Set ℝ} (hW : IsOpen W) (hC : IsCompact C)
    (hC₀₁ : C ⊆ Icc 0 1) (hCW : C ×ˢ {z | equivRealProdCLM.symm z ≠ 1} ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ c ∈ C, ∀ z, equivRealProdCLM.symm z ≠ 1 → ∀ x,
      (hω.symplecticFormAt x).Tames (J c z x))
    (hJc : ∀ D, IsCompact D → (∀ z ∈ D, equivRealProdCLM.symm z ≠ 1) → ∃ κ > 0, ∀ c ∈ C,
      ∀ z ∈ D, ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J c z x v))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ c ∈ C, ∀ q, q ≠ .inf → ∀ s t x, T₀ ≤ s →
      J c (endChart q (q.endSign * s, t)) x = Jq q t x)
    (hJe' : ∀ c ∈ C, ∀ s t x, T₀ ≤ s → J c (endChart .inf (-s, t) + (c, 0)) x = Jq .inf t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x₁ xinf : ℕ → ℝ → M⦄ ⦃A : ℝ⦄,
      (∀ k, c k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | equivRealProdCLM.symm z ≠ 1}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 1 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (c k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k (t : ℝ), Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x₁ k t))) →
      (∀ k (t : ℝ), Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (↑(c k) + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xinf k t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L (c k) (equivRealProdCLM.symm z) x Complex.I)
        (u k)) thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          (∫ t in (0 : ℝ)..1, H one t (x₁ k t)) - (∫ t in (0 : ℝ)..1, H inf t (xinf k t)) ≤
        A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c₀ ∈ C, Tendsto (fun n ↦ c (φ n)) atTop (𝓝 c₀) ∧
        ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), ↑Z ⊆ {z | equivRealProdCLM.symm z ≠ 1} ∧
        Z.card * δ ≤ A + (B zero + ∑ q, B q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ {z | equivRealProdCLM.symm z ≠ 1}, ω.floerEnergyDensity
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x
              Complex.I) (u (φ n)) y) ∧
        (∀ y ∈ {z | equivRealProdCLM.symm z ≠ 1} \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A', ∀ᶠ n in atTop, ∀ w ∈ N,
          ω.floerEnergyDensity
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L (c (φ n)) (equivRealProdCLM.symm z) x
              Complex.I) (u (φ n)) w ≤ A') ∧
        ContinuousOn v ({z | equivRealProdCLM.symm z ≠ 1} \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          ({z | equivRealProdCLM.symm z ≠ 1} \ ↑Z) ∧
        ∀ z ∈ {z | equivRealProdCLM.symm z ≠ 1} \ ↑Z,
          Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  obtain ⟨hU, hSS₁, hD₀, hD₀₁, hS₁le⟩ := thricePuncturedSphereReal_union_ball_and_ae_le
  -- The thresholds of the two windows: the pair of pants and the disc about the capped puncture.
  obtain ⟨δ₁, hδ₁, hS⟩ :=
    exists_pos_forall_subseq_off_finset_thricePuncturedSphereReal_cappedExchange hω hH hHs hL
      hW hC hC₀₁ ((prod_mono subset_rfl hSS₁).trans hCW) hJ (fun c hc z hz ↦ hJt c hc z (hSS₁ hz))
      (fun D hD hDS ↦ hJc D hD fun z hz ↦ hSS₁ (hDS hz)) hJe hJe' he he_inj
  obtain ⟨κ, hκ, hκD⟩ := hJc _ hD₀ fun z hz ↦ hD₀₁ hz
  obtain ⟨L', hL'⟩ :=
    exists_forall_norm_mvfderiv_hamiltonianVectorField_cappedExchange_le hω hH hHs hL hC hD₀
      (fun z hz ↦ hD₀₁ hz) he
  obtain ⟨δ₂, hδ₂, hdisc⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedExchange
      hH hHs hB hL hW hC hC₀₁ hD₀ (fun z hz ↦ hD₀₁ hz) ((prod_mono subset_rfl hD₀₁).trans hCW)
      hJ hJt (fun x ↦ (he x).mdifferentiableAt one_ne_zero) he_inj hκ hκD
      (fun c hc z hz x ↦ (hL' c hc z hz x).1) fun c hc z hz x ↦ (hL' c hc z hz x).2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun c u x₁ xinf A hcC hu hfl hx₁ hxinf hint harea htop ↦ ?_⟩
  -- The Floer energy over every part of `S₁` is at most `A + (B_0 + (B_0 + B_1 + B_∞))`.
  have hE (k : ℕ) := hω.setIntegral_floerEnergyDensity_cappedExchangePerturbation_le hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hB hL (hC₀₁ (hcC k)).1 (hC₀₁ (hcC k)).2
    (((hu k).of_le (by norm_num)).mono hSS₁) (hx₁ k) (hxinf k) (hint k) (harea k)
    (fun z hz ↦ hJt _ (hcC k) z (hSS₁ hz) _) (fun z hz ↦ hfl k z (hSS₁ hz)) (htop k)
  -- First make the parameters converge, then run the diagonal argument over the two windows.
  obtain ⟨c₀, hc₀, ψ, hψ, hcψ⟩ := hC.tendsto_subseq hcC
  obtain ⟨φ, hφ, Z, v, hZ, hcard, hconc, hbd, hv, hconv, hpt⟩ :=
    exists_subseq_off_finset_union_comp isOpen_thricePuncturedSphereReal
      (isOpen_ball.preimage equivRealProdCLM.symm.continuous) hU (u := fun k ↦ u (ψ k))
      he.continuous he_inj (fun k ↦ (hu _).continuousOn) (g := fun k ↦ ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L (c (ψ k)) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L (c (ψ k)) (equivRealProdCLM.symm z) x
          Complex.I) (u (ψ k))) (lt_min hδ₁ hδ₂)
      (fun k z hz ↦ floerEnergyDensity_nonneg hω (hJt _ (hcC _) z hz _) (hfl _ z hz))
      (fun k ↦ (hint _).mono_set_ae hS₁le) (fun k ↦ hE _ _)
      (fun ψ' _ ↦ by
        -- On the pair of pants.
        obtain ⟨φ, hφ, -, -, -, Z, v, -, -, hconc, hbd, -, hconv, -⟩ :=
          hS (c := fun k ↦ c (ψ (ψ' k))) (u := fun k ↦ u (ψ (ψ' k))) (fun k ↦ hcC _)
            (fun k ↦ (hu _).mono hSS₁) (fun k z hz ↦ hfl _ z (hSS₁ hz)) (fun k ↦ hint _)
            fun k ↦ hE _ _
        exact ⟨φ, hφ, Z, fun z hz ε hε ↦ (hconc z hz ε hε).mono fun n hn ↦
          (min_le_left _ _).trans hn, hbd, _, hconv⟩) fun ψ' _ ↦ by
        -- On the disc about the capped puncture.
        obtain ⟨φ, hφ, -, -, -, Z, -, -, hconc, hbd, v, -, hconv, -⟩ :=
          hdisc (isOpen_ball.preimage equivRealProdCLM.symm.continuous)
            (preimage_mono ball_subset_closedBall) (fun k ↦ hcC (ψ (ψ' k))) (fun k ↦ hu _)
            (fun k ↦ hfl _) (fun k ↦ hx₁ _) (fun k ↦ hxinf _) (fun k ↦ hint _)
            (fun k ↦ harea _) fun k ↦ htop _
        exact ⟨φ, hφ, Z, fun z hz ε hε ↦ (hconc z hz ε hε).mono fun n hn ↦
          (min_le_right _ _).trans hn, hbd, _, hconv⟩
  exact ⟨ψ ∘ φ, hψ.comp hφ, c₀, hc₀, hcψ.comp hφ.tendsto_atTop, Z, v, hZ, hcard, hconc, hbd, hv,
    hconv, hpt⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
