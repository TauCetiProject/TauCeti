/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.AdmissibleBoundaryPart
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.Sobolev.Trace.BoundaryPart
import TauCeti.Analysis.Sobolev.Trace.Extension
import TauCeti.Analysis.Sobolev.Trace.Tangential
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables

/-!
# Functions vanishing on a part of a Lipschitz graph over an admissible base region

Let `φ : E → ℝ` be Lipschitz and let `B ⊆ E` be an admissible base region
(`Set.IsAdmissibleBaseRegion`): all of `E`, empty, or, after a linear isometry
`f : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E')`, the region `{y | β (f y).snd < (f y).fst}` strictly above the
graph of a Lipschitz function `β` on `E'`. The part `Γ = {(φ y, y) | y ∈ B}` of the graph of `φ`
lying over `B` is the local model of an admissible boundary part of a Lipschitz domain
(`Set.IsBoundaryPartChart`). This file proves the trace characterization of the Sobolev functions
vanishing on `Γ` in this model: for `1 ≤ p < ∞`, a function `u` in `W^{1,p}` of the region
`{φ y < t}` above the graph lies in `W^{1,p}_Γ` (`TauCeti.w1pVanishingOnSubmodule`) if and only if
its trace on the graph vanishes almost everywhere on `B`
(`W1p.mem_w1pVanishingOnSubmodule_iff_normalEpigraphTrace_ae_eq_zero_of_isAdmissibleBaseRegion`).
The flat case, the half-space `{a < t}` with `Γ = {a} × B`, is
`W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero_of_isAdmissibleBaseRegion`.

## The argument

Two Lipschitz shears reduce the statement to a half-hyperplane `{a} × {ℓ < c}` in the boundary
of a half-space, where it is the characterization
`TauCeti.W1p.exists_seq_tendsto_restrictL_ofTestFunctionₗ_iff_halfSpaceTrace_ae_eq_zero`. The
shear `TauCeti.graphFlattening φ` carries the region above the graph onto the half-space
`{0 < t}` and `Γ` onto `{0} × B`; precomposition with it preserves `W^{1,p}_Γ`
(`TauCeti.W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule_iff`) and turns the trace on the
graph into the half-space trace (`TauCeti.W1p.normalEpigraphTrace`). For an interface region
`B = {β (f y).snd < (f y).fst}`, the shear `σ = f⁻¹ ∘ graphFlattening β ∘ f` of the base is a
volume-preserving bi-Lipschitz homeomorphism of `E` with `B = σ⁻¹ {0 < (f y).fst}`, and
`(t, y) ↦ (t, σ y)` preserves the half-space. Precomposition with it preserves `W^{1,p}_Γ` again,
and acts on traces by composition with `σ` (`TauCeti.W1p.halfSpaceTrace_compMeasurePreservingL`),
so both sides of the characterization pass from `{0 < (f y).fst}` to `B`. The cases `B = E` and
`B = ∅` are the kernel theorem `TauCeti.W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero` and the
density of restrictions of whole-space Sobolev functions.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. **48** (2016), 2912–2943, §2.1
  (strong Lipschitz pairs), Lemma 3.1 and Appendix A (the trace characterization for `p = 2` in
  dimension three, by flattening the boundary and the interface).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 2 (functions of zero
  trace).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Tangential changes of variables -/

/-- **Tangential homeomorphisms transport the trace characterization.** Let `σ` be a
volume-preserving homeomorphism of `E` such that `σ` and `σ⁻¹` are Lipschitz. If the functions in
`W^{1,p}` of the half-space `{a < t}` vanishing on `{a} × S` are those whose trace vanishes on `S`,
the same holds for `σ⁻¹(S)`. -/
private theorem mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero_preimage
    (hp : p ≠ ∞) (a : ℝ) (σ : E ≃ₜ E) {K K' : ℝ≥0} (hσ : LipschitzWith K σ)
    (hσ' : LipschitzWith K' σ.symm) (hσm : MeasurePreserving σ) {S : Set E} (hS : MeasurableSet S)
    (h : ∀ v : W1p volume (normalHalfSpace (E := E) a) p,
      v ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ x.snd ∈ S} ↔
        ∀ᵐ y ∂(volume : Measure E), y ∈ S → W1p.halfSpaceTrace hp a v y = 0)
    (u : W1p volume (normalHalfSpace (E := E) a) p) :
    u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ x.snd ∈ σ ⁻¹' S} ↔
      ∀ᵐ y ∂(volume : Measure E), y ∈ σ ⁻¹' S → W1p.halfSpaceTrace hp a u y = 0 := by
  -- Compose with `Φ (t, y) = (t, σ⁻¹ y)`, which carries `{a} × S` to `{a} × σ⁻¹(S)`.
  have hσm' : MeasurePreserving σ.symm := by
    rw [← σ.toMeasurableEquiv_symm_coe]
    exact MeasurePreserving.symm _ (by rwa [σ.toMeasurableEquiv_coe])
  let Φ : WithLp 2 (ℝ × E) ≃ₜ WithLp 2 (ℝ × E) := (WithLp.homeomorphProd 2 ℝ E).trans
    (((Homeomorph.refl ℝ).prodCongr σ.symm).trans (WithLp.homeomorphProd 2 ℝ E).symm)
  have hΦ : ⇑Φ = WithLp.map 2 (Prod.map id σ.symm) := by
    ext x
    simp [Φ, WithLp.homeomorphProd]
  have hΦs : ⇑Φ.symm = WithLp.map 2 (Prod.map id σ) := by
    ext x
    simp [Φ, WithLp.homeomorphProd]
  have hΦl : LipschitzWith (max 1 K') Φ := by
    rw [hΦ]
    exact LipschitzWith.id.withLpProdMap hσ'
  have hΦl' : LipschitzWith (max 1 K) Φ.symm := by
    rw [hΦs]
    exact LipschitzWith.id.withLpProdMap hσ
  have hΦm : MeasurePreserving Φ := by
    rw [hΦ]
    exact (MeasurePreserving.id volume).withLpProdMap hσm'
  have hUV : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      Φ ⁻¹' normalHalfSpace (E := E) a := by
    rw [hΦ, preimage_withLpMap_prodMap_id_normalHalfSpace]
  have hM : ∀ x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))),
      ‖fderiv ℝ Φ x‖ ≤ max 1 K' := fun _ _ => norm_fderiv_le_of_lipschitz ℝ hΦl
  have hΓ : Φ ⁻¹' {x | x.fst = a ∧ x.snd ∈ σ ⁻¹' S} = {x | x.fst = a ∧ x.snd ∈ S} := by
    ext x
    simp [hΦ]
  have hW := W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule_iff (p := p) hp Φ
    hΦl.locallyLipschitz hΦl'.locallyLipschitz hΦm hUV hΦl.locallyLipschitz.locallyLipschitzOn hM
    (fun _ _ => norm_fderiv_le_of_lipschitz ℝ hΦl') (Γ := {x | x.fst = a ∧ x.snd ∈ σ ⁻¹' S})
    (u := u)
  rw [hΓ] at hW
  rw [← hW, h, ← W1p.halfSpaceTrace_compMeasurePreservingL_ae_eq_zero_iff hp a hΦm hUV
    hΦl.locallyLipschitz.locallyLipschitzOn hM hΦl.continuous.continuousOn hσm'
    (fun y => by simp [hΦ]) u (hS.preimage σ.continuous.measurable)]
  simp

/-! ### The half-space -/

/-- The flat model with an affine interface: on the half-space `{a < t}`, for nonzero `ℓ`, the
functions vanishing on the half-hyperplane `{a} × {ℓ < c}` are those whose trace vanishes on
`{ℓ < c}`. This is the sequential characterization
`TauCeti.W1p.exists_seq_tendsto_restrictL_ofTestFunctionₗ_iff_halfSpaceTrace_ae_eq_zero`, read
through `TauCeti.mem_w1pVanishingOnSubmodule_iff_exists_seq_tendsto`. -/
private theorem mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero_setOf_lt
    (hp : p ≠ ∞) (a c : ℝ) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    (u : W1p volume (normalHalfSpace (E := E) a) p) :
    u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ x.snd ∈ {y | ℓ y < c}}
      ↔ ∀ᵐ y ∂(volume : Measure E), y ∈ {y | ℓ y < c} → W1p.halfSpaceTrace hp a u y = 0 := by
  rw [mem_w1pVanishingOnSubmodule_iff_exists_seq_tendsto]
  constructor
  · -- The closure of the half-hyperplane contains each `{a} × {ℓ ≤ c - 1 / (n + 1)}`, so the trace
    -- vanishes on each `{ℓ < c - 1 / (n + 1)}`, whose union is `{ℓ < c}`.
    rintro ⟨φ, hφ, hlim⟩
    have hn : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure E), ℓ y < c - 1 / (n + 1) →
        W1p.halfSpaceTrace hp a u y = 0 := fun n => by
      have hsub : {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd ≤ c - 1 / (n + 1)} ⊆
          closure {x | x.fst = a ∧ x.snd ∈ {y | ℓ y < c}} := fun x hx =>
        subset_closure ⟨hx.1, hx.2.trans_lt (sub_lt_self c Nat.one_div_pos_of_nat)⟩
      exact (W1p.exists_seq_tendsto_restrictL_ofTestFunctionₗ_iff_halfSpaceTrace_ae_eq_zero hp a _
        hℓ u).1 ⟨φ, fun k => (hφ k).mono_right hsub, hlim⟩
    filter_upwards [ae_all_iff.2 hn] with y hy hyc
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (by simpa using hyc))
    exact hy n (by linarith)
  · -- The closure of the half-hyperplane lies in the closed set `{a} × {ℓ ≤ c}`.
    intro htr
    obtain ⟨φ, hφ, hlim⟩ :=
      (W1p.exists_seq_tendsto_restrictL_ofTestFunctionₗ_iff_halfSpaceTrace_ae_eq_zero hp a c hℓ
        u).2 htr
    have hK : IsClosed {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd ≤ c} :=
      (isClosed_eq (WithLp.continuous_fst 2 ℝ E) continuous_const).inter
        (isClosed_le (ℓ.continuous.comp (WithLp.continuous_snd 2 ℝ E)) continuous_const)
    have hsub : {x : WithLp 2 (ℝ × E) | x.fst = a ∧ x.snd ∈ {y | ℓ y < c}} ⊆
        {x | x.fst = a ∧ ℓ x.snd ≤ c} := fun x hx => ⟨hx.1, le_of_lt hx.2⟩
    exact ⟨φ, fun k => (hφ k).mono_right (closure_minimal hsub hK), hlim⟩

/-- **The trace characterization on a half-space, for a boundary part over an admissible base
region.** Let `1 ≤ p < ∞`, let `H = {x | a < x.fst}` in `ℝ × E`, and let `B ⊆ E` be an admissible
base region whose interfaces are modelled on an inner product space `E'`. A
function `u ∈ W^{1,p}(H)` lies in `W^{1,p}_Γ(H)` for `Γ = {a} × B` if and only if its trace on
`{a} × E` vanishes almost everywhere on `B`. -/
theorem W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero_of_isAdmissibleBaseRegion
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [MeasurableSpace E'] [BorelSpace E'] (hp : p ≠ ∞) (a : ℝ) {B : Set E}
    (hB : B.IsAdmissibleBaseRegion E') (u : W1p volume (normalHalfSpace (E := E) a) p) :
    u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ x.snd ∈ B} ↔
      ∀ᵐ y ∂(volume : Measure E), y ∈ B → W1p.halfSpaceTrace hp a u y = 0 := by
  obtain rfl | rfl | ⟨f, β, K, hβ, rfl⟩ := isAdmissibleBaseRegion_iff.1 hB
  · -- `Γ` is the whole frontier: the kernel theorem.
    have hΓ : {x : WithLp 2 (ℝ × E) | x.fst = a ∧ x.snd ∈ univ} =
        frontier (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) := by
      rw [coe_normalHalfSpace, frontier_setOf_lt_fst (γ := fun _ : E => a) continuous_const]
      simp
    rw [hΓ, w1pVanishingOnSubmodule_frontier,
      W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero hp, Lp.eq_zero_iff_ae_eq_zero]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with y hy
    · exact fun _ => hy
    · exact hy (mem_univ y)
  · -- `Γ` is empty: `u` is the restriction of its reflection extension, a whole-space function.
    refine iff_of_true ?_ (Eventually.of_forall fun y hy => absurd hy (notMem_empty y))
    rw [← W1p.restrictL_extendByReflectionL a u]
    refine W1p.restrictL_mem_w1pVanishingOnSubmodule le_top
      (disjoint_left.2 fun x (hx : x.fst = a ∧ x.snd ∈ (∅ : Set E)) _ => notMem_empty _ hx.2) ?_
    rw [w1p0Submodule_top_eq_top hp]
    exact ClosedSubmodule.mem_top
  · -- `E'` is finite-dimensional, being a quotient of `ℝ × E' ≃ E`.
    have : FiniteDimensional ℝ (WithLp 2 (ℝ × E')) := f.toLinearEquiv.finiteDimensional
    have : FiniteDimensional ℝ E' := Module.Finite.of_surjective (WithLp.sndL 2 ℝ ℝ E').toLinearMap
      fun y => ⟨WithLp.toLp 2 (0, y), rfl⟩
    -- The base shear `σ = f⁻¹ ∘ graphFlattening β ∘ f` carries `B` onto `{0 < (f y).fst}`.
    let σ : E ≃ₜ E := (f.toHomeomorph.trans (graphFlattening β hβ.continuous)).trans
      f.symm.toHomeomorph
    have hσ : LipschitzWith (1 + K) σ := by
      have h := (f.symm.lipschitzWith.comp (lipschitzWith_graphFlattening hβ)).comp f.lipschitzWith
      rwa [one_mul, mul_one] at h
    have hσ' : LipschitzWith (1 + K) σ.symm := by
      have h := (f.symm.lipschitzWith.comp (lipschitzWith_graphFlattening_symm hβ)).comp
        f.lipschitzWith
      rwa [one_mul, mul_one] at h
    have hσm : MeasurePreserving σ :=
      (f.symm.measurePreserving.comp (measurePreserving_graphFlattening β hβ.continuous)).comp
        f.measurePreserving
    -- The target region is `{ℓ < 0}` for the nonzero functional `ℓ y = -(f y).fst`.
    let ℓ : E →L[ℝ] ℝ := -((WithLp.fstL 2 ℝ ℝ E').comp
      f.toLinearIsometry.toContinuousLinearMap)
    have hℓ : ℓ ≠ 0 := fun h => by
      simpa [ℓ] using congrArg (fun g : E →L[ℝ] ℝ => g (f.symm (WithLp.toLp 2 (1, 0)))) h
    have hBσ : f ⁻¹' {z | β z.snd < z.fst} = σ ⁻¹' {y | ℓ y < 0} := by
      ext y
      simp [σ, ℓ]
    rw [hBσ]
    exact mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero_preimage hp a σ hσ hσ' hσm
      (measurableSet_lt ℓ.continuous.measurable measurable_const)
      (mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero_setOf_lt hp a 0 hℓ) u

/-! ### The region above a Lipschitz graph -/

/-- **The trace characterization above a Lipschitz graph, for a boundary part over an admissible
base region.** Let `1 ≤ p < ∞`, let `φ` be Lipschitz, and let `B ⊆ E` be an admissible base region
whose interfaces are modelled on an inner product space `E'`. A function `u` in
`W^{1,p}` of the region `{φ y < t}` above the graph of `φ` lies in `W^{1,p}_Γ` for the part
`Γ = {(φ y, y) | y ∈ B}` of the graph over `B` if and only if its trace on the graph
(`TauCeti.W1p.normalEpigraphTrace`) vanishes almost everywhere on `B`. -/
theorem W1p.mem_w1pVanishingOnSubmodule_iff_normalEpigraphTrace_ae_eq_zero_of_isAdmissibleBaseRegion
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [MeasurableSpace E'] [BorelSpace E'] (hp : p ≠ ∞) {φ : C(E, ℝ)} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) {B : Set E} (hB : B.IsAdmissibleBaseRegion E')
    (u : W1p volume (normalEpigraph φ) p) :
    u ∈ w1pVanishingOnSubmodule volume (normalEpigraph φ) p {x | x.fst = φ x.snd ∧ x.snd ∈ B} ↔
      ∀ᵐ y ∂(volume : Measure E), y ∈ B → W1p.normalEpigraphTrace hp hφ u y = 0 := by
  -- Unflatten by `G = (graphFlattening φ)⁻¹`, which carries `{0} × B` onto `Γ`.
  let G := (graphFlattening φ φ.continuous).symm
  have hUV : (normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E))) =
      G ⁻¹' normalEpigraph φ := by
    ext x
    simp [G]
  have hM : ∀ x ∈ (normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E))),
      ‖fderiv ℝ G x‖ ≤ 1 + K := fun _ _ => by
    simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_graphFlattening_symm hφ)
  have hG := (lipschitzWith_graphFlattening_symm hφ).locallyLipschitz
  -- The flattened function is the composite of `u` with `G`.
  have hflat : W1p.normalEpigraphEquivL hφ u =
      W1p.compMeasurePreservingL (measurePreserving_graphFlattening_symm φ φ.continuous) hUV
        hG.locallyLipschitzOn hM u :=
    W1p.ext_value (Lp.ext ((W1p.value_normalEpigraphEquivL_ae hφ u).trans
      (W1p.value_compMeasurePreservingL_ae _ _ _ _ u).symm))
  have hΓ : G ⁻¹' {x | x.fst = φ x.snd ∧ x.snd ∈ B} = {x | x.fst = 0 ∧ x.snd ∈ B} := by
    ext x
    simp [G]
  rw [W1p.normalEpigraphTrace_apply, hflat,
    ← W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero_of_isAdmissibleBaseRegion hp 0
      hB, ← hΓ]
  exact (W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule_iff hp G hG
    (lipschitzWith_graphFlattening hφ).locallyLipschitz
    (measurePreserving_graphFlattening_symm φ φ.continuous) hUV hG.locallyLipschitzOn hM
    (fun _ _ => norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_graphFlattening hφ))).symm

end TauCeti
