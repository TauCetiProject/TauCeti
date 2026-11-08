/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Restriction and locality in the manifold weak Whitney topology

Restriction to an open source is continuous for the existing weak Whitney topology. Its
coordinate derivatives agree with the ambient derivatives in inherited charts.
-/

public section
noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

/-- Restriction of a native smooth map to an open source. -/
def restrict (f : C^n⟮I, M; J, N⟯) (U : Opens M) : C^n⟮I, U; J, N⟯ :=
  f.comp ⟨Subtype.val, contMDiff_subtype_val⟩

/-- Restricting a map does not change its value. -/
@[simp]
theorem restrict_apply (f : C^n⟮I, M; J, N⟯) (U : Opens M) (x : U) :
    f.restrict U x = f x := by
  rfl

/-- The underlying function of a restricted native map is ordinary composition with inclusion. -/
@[simp]
theorem coe_restrict (f : C^n⟮I, M; J, N⟯) (U : Opens M) :
    (f.restrict U : U → N) = f ∘ Subtype.val := by
  rfl

/-- Restriction to an open source is continuous for the native weak Whitney topologies. -/
theorem continuous_restrict [IsManifold I n M] [IsManifold J n N] [LocallyCompactSpace E]
    (U : Opens M) : Continuous (fun f : C^n⟮I, M; J, N⟯ ↦ f.restrict U) := by
  exact continuous_comp_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const)

/-- Taylor coefficients computed in an inherited chart agree with the ambient chart
coefficients at every order. The function need not be differentiable: both derivatives depend
only on the same germ on the model domain. -/
theorem ftaylorSeriesWithin_restrict_extChartAt (f : M → F) (U : Opens M) (x : U)
    {z : E} (hz : z ∈ (extChartAt I x).target) :
    ftaylorSeriesWithin 𝕜 ((f ∘ Subtype.val) ∘ (extChartAt I x).symm)
        (extChartAt I x).target z =
      ftaylorSeriesWithin 𝕜 (f ∘ (extChartAt I (x : M)).symm)
        (extChartAt I (x : M)).target z := by
  funext m
  simp only [ftaylorSeriesWithin]
  have heq : EqOn ((f ∘ Subtype.val) ∘ (extChartAt I x).symm)
      (f ∘ (extChartAt I (x : M)).symm) (extChartAt I x).target := by
    intro y hy
    simp only [Function.comp_apply, U.coe_extChartAt_symm_apply x hy]
  rw [iteratedFDerivWithin_congr heq hz]
  have hzU : (extChartAt I (x : M)).symm z ∈ U :=
    ((U.extChartAt_target_eq x).subset hz).2
  have hmem : (extChartAt I (x : M)).symm ⁻¹' (U : Set M) ∈
      𝓝[(extChartAt I (x : M)).target] z :=
    (continuousOn_extChartAt_symm (x : M) z
      (U.extChartAt_target_subset x hz)).preimage_mem_nhdsWithin (U.isOpen.mem_nhds hzU)
  rw [U.extChartAt_target_eq x]
  exact iteratedFDerivWithin_inter' hmem

/-- In an inherited chart, restriction preserves the ambient coordinate derivatives. -/
theorem chartIteratedFDeriv_restrict_apply [IsManifold I n M]
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (U : Opens M) (x : U) (m : ℕ) (hm : m ≤ n)
    (z : (extChartAt I x).target) :
    chartIteratedFDeriv (f.restrict U) x m hm z =
      chartIteratedFDeriv f (x : M) m hm ⟨z, U.extChartAt_target_subset x z.2⟩ := by
  rw [chartIteratedFDeriv_self_target_apply, chartIteratedFDeriv_self_target_apply]
  simpa only [ftaylorSeriesWithin, Function.comp_def, restrict_apply] using
    congrFun (ftaylorSeriesWithin_restrict_extChartAt f U x z.2) m

/-- Coordinate derivatives may be computed through a chart of an open restriction, using the
ordinary Faà di Bruno composition with the ambient coordinate change. -/
theorem iteratedFDerivWithin_eq_restrict_taylorComp [IsManifold I n M]
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (U : Opens M) (x : M) (y : U) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hy : (extChartAt I x).symm z ∈ U)
    (hys : (extChartAt I x).symm z ∈ (extChartAt I (y : M)).source)
    (m : ℕ) (hm : m ≤ n) :
    iteratedFDerivWithin 𝕜 m (f ∘ (extChartAt I x).symm) (extChartAt I x).target z =
      (ftaylorSeriesWithin 𝕜 ((f.restrict U) ∘ (extChartAt I y).symm)
        (extChartAt I y).target (extChartAt I (y : M) ((extChartAt I x).symm z))).taylorComp
        (ftaylorSeriesWithin 𝕜 (extChartAt I (y : M) ∘ (extChartAt I x).symm)
          (extChartAt I x).target z) m := by
  have hv : extChartAt I (y : M) ((extChartAt I x).symm z) ∈
      (extChartAt I y).target := by
    rw [U.extChartAt_target_eq y]
    exact ⟨(extChartAt I (y : M)).map_source hys, by
      simpa only [mem_preimage, (extChartAt I (y : M)).left_inv hys, SetLike.mem_coe] using hy⟩
  have h := iteratedFDerivWithin_extChartAt_comp f
    (ContMDiffMap.id : C^n⟮I, M; I, M⟯) hz hys (z := (0 : F)) (by simp) hm
  have hid : f.comp (ContMDiffMap.id : C^n⟮I, M; I, M⟯) = f := by
    ext w
    rfl
  have hidcoe : ((ContMDiffMap.id : C^n⟮I, M; I, M⟯) : M → M) = _root_.id := rfl
  rw [hid, hidcoe] at h
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp, id_eq] at h
  rw [← ftaylorSeriesWithin_restrict_extChartAt f U y hv] at h
  simpa only [coe_restrict] using h

/-- Convergence of the Taylor coefficients, computed in the inherited chart at `y`, of the
restrictions `g p`, jointly with the point moved into that chart. -/
private theorem tendsto_ftaylorSeriesWithin_restrict_extChartAt [IsManifold I n M]
    [LocallyCompactSpace E] {P : Type*} {l : Filter P} {g : P → C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    {g₀ : C^n⟮I, M; 𝓘(𝕜, F), F⟯} (U : Opens M)
    (hg : Tendsto (fun p ↦ (g p).restrict U) l (𝓝 (g₀.restrict U)))
    (x : M) {z : E} (y : U)
    (hv : extChartAt I (y : M) ((extChartAt I x).symm z) ∈ (extChartAt I y).target)
    (hτ : Tendsto (fun w ↦ extChartAt I (y : M) ((extChartAt I x).symm w))
      (𝓝[(extChartAt I x).target] z)
      (𝓝[(extChartAt I y).target] extChartAt I (y : M) ((extChartAt I x).symm z)))
    (m : ℕ) (hm : m ≤ n) (k : ℕ) (hk : k ≤ m) :
    Tendsto (fun q : P × E ↦ ftaylorSeriesWithin 𝕜
      ((g q.1).restrict U ∘ (extChartAt I y).symm) (extChartAt I y).target
        (extChartAt I (y : M) ((extChartAt I x).symm q.2)) k)
      (l ×ˢ 𝓝[(extChartAt I x).target] z)
      (𝓝 (ftaylorSeriesWithin 𝕜 ((g₀.restrict U) ∘ (extChartAt I y).symm)
        (extChartAt I y).target (extChartAt I (y : M) ((extChartAt I x).symm z)) k)) := by
  have h := (tendsto_iteratedFDerivWithin_extChartAt (f₀ := g₀.restrict U)
    (y := (0 : F)) hv (by simp) ((Nat.cast_le.mpr hk).trans hm)).comp (hg.prodMap hτ)
  simpa only [ftaylorSeriesWithin, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using h

/-- Convergence of an open restriction controls every ambient chart derivative near a point in
that open set, jointly with the source point. No regularity of the parameter is required. -/
theorem tendsto_iteratedFDerivWithin_of_restrict [IsManifold I n M] [LocallyCompactSpace E]
    {P : Type*} {l : Filter P} {g : P → C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    {g₀ : C^n⟮I, M; 𝓘(𝕜, F), F⟯} (U : Opens M)
    (hg : Tendsto (fun p ↦ (g p).restrict U) l (𝓝 (g₀.restrict U)))
    (x : M) {z : E} (hz : z ∈ (extChartAt I x).target)
    (hy : (extChartAt I x).symm z ∈ U) (m : ℕ) (hm : m ≤ n) :
    Tendsto (fun q : P × E ↦ iteratedFDerivWithin 𝕜 m
      (g q.1 ∘ (extChartAt I x).symm) (extChartAt I x).target q.2)
      (l ×ˢ 𝓝[(extChartAt I x).target] z)
      (𝓝 (iteratedFDerivWithin 𝕜 m (g₀ ∘ (extChartAt I x).symm)
        (extChartAt I x).target z)) := by
  let y : U := ⟨(extChartAt I x).symm z, hy⟩
  let τ : E → E := fun w ↦ extChartAt I (y : M) ((extChartAt I x).symm w)
  have hys : (extChartAt I x).symm z ∈ (extChartAt I (y : M)).source :=
    mem_extChartAt_source (y : M)
  have hv : τ z ∈ (extChartAt I y).target := by
    rw [U.extChartAt_target_eq y]
    exact ⟨(extChartAt I (y : M)).map_source hys, by
      simpa only [τ, mem_preimage, (extChartAt I (y : M)).left_inv hys, SetLike.mem_coe] using hy⟩
  have hτ : Tendsto τ (𝓝[(extChartAt I x).target] z) (𝓝[(extChartAt I y).target] τ z) :=
    U.tendsto_extChartAt_restrict x y hz hy hys
  have hgl := hg.prodMap hτ
  have hjg := fun k hk ↦
    tendsto_ftaylorSeriesWithin_restrict_extChartAt U hg x y hv hτ m hm k hk
  have hjp := fun k hk ↦
    tendsto_ftaylorSeriesWithin_extChartAt_comp_symm (P := P) (l := l) x y hz hys (k := k)
      ((Nat.cast_le.mpr hk).trans hm)
  have hφ := continuousOn_extChartAt_symm (I := I) x z hz
  have hU : ∀ᶠ q : P × E in l ×ˢ 𝓝[(extChartAt I x).target] z,
      (extChartAt I x).symm q.2 ∈ U :=
    tendsto_snd.eventually (hφ.eventually (U.isOpen.mem_nhds hy))
  have hS : ∀ᶠ q : P × E in l ×ˢ 𝓝[(extChartAt I x).target] z,
      (extChartAt I x).symm q.2 ∈ (extChartAt I (y : M)).source :=
    tendsto_snd.eventually
      (hφ.eventually ((isOpen_extChartAt_source (I := I) (y : M)).mem_nhds hys))
  have hfdb : ∀ᶠ q : P × E in l ×ˢ 𝓝[(extChartAt I x).target] z,
      (ftaylorSeriesWithin 𝕜 ((g q.1).restrict U ∘ (extChartAt I y).symm)
        (extChartAt I y).target (τ q.2)).taylorComp
        (ftaylorSeriesWithin 𝕜 (extChartAt I (y : M) ∘ (extChartAt I x).symm)
          (extChartAt I x).target q.2) m =
        iteratedFDerivWithin 𝕜 m (g q.1 ∘ (extChartAt I x).symm)
          (extChartAt I x).target q.2 := by
    filter_upwards [hU, hS, tendsto_snd.eventually self_mem_nhdsWithin] with q hU hS hq
    exact (iteratedFDerivWithin_eq_restrict_taylorComp (g q.1) U x y hq hU hS m hm).symm
  have h := (Filter.Tendsto.taylorComp hjg (fun k _ hk ↦ hjp k hk)).congr' hfdb
  rw [← iteratedFDerivWithin_eq_restrict_taylorComp g₀ U x y hz hy hys m hm] at h
  exact h

/-- Continuity in the native weak Whitney topology can be checked after restriction to an
arbitrary open cover. Compact chart tests use a finite subcover locally; no countability or
compactness of the whole manifold is required. -/
theorem continuous_of_forall_continuous_restrict [IsManifold I n M] [LocallyCompactSpace E]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i)
    {P : Type*} [TopologicalSpace P] {g : P → C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    (hg : ∀ i, Continuous (fun p ↦ (g p).restrict (U i))) : Continuous g := by
  refine continuous_iff_continuousAt.mpr fun p₀ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV h₀ ↦ ?_
  rw [chartJetSet_self_target x y m hm] at h₀ ⊢
  -- The chart-test rewrite leaves membership in a set-builder with a MapsTo predicate.
  -- Expose those two definitions under Eventually to apply compactness pointwise.
  change ∀ᶠ p in 𝓝 p₀, ∀ w ∈ K, chartIteratedFDeriv (g p) x m hm w ∈ V
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  obtain ⟨i, hi⟩ := hU ((extChartAt I x).symm w)
  have hlim := tendsto_iteratedFDerivWithin_of_restrict (U := U i)
    ((hg i).continuousAt (x := p₀)) x (z := w) w.2 hi m hm
  have hv : V ∈ 𝓝 (iteratedFDerivWithin 𝕜 m (g p₀ ∘ (extChartAt I x).symm)
      (extChartAt I x).target w) := by
    apply hV.mem_nhds
    simpa only [chartIteratedFDeriv_self_target_apply] using h₀ hw
  rw [nhds_prod_eq]
  have h := (tendsto_id.prodMap (map_nhds_subtype_val w).le).eventually
    (hlim.eventually_mem hv)
  simpa only [chartIteratedFDeriv_self_target_apply, Prod.map_fst, Prod.map_snd, id_eq] using h

/-- The native weak Whitney topology is local with respect to every genuine open cover. -/
theorem continuous_iff_forall_continuous_restrict [IsManifold I n M] [LocallyCompactSpace E]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i)
    {P : Type*} [TopologicalSpace P] {g : P → C^n⟮I, M; 𝓘(𝕜, F), F⟯} :
    Continuous g ↔ ∀ i, Continuous (fun p ↦ (g p).restrict (U i)) := by
  constructor
  · intro hg i
    exact (continuous_restrict (U i)).comp hg
  · exact continuous_of_forall_continuous_restrict U hU

end ContMDiffMap
