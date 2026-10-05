/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.InverseJet
public import TauCeti.Geometry.Diffeomorphism.Composition
public import TauCeti.Analysis.Calculus.ContDiff.TaylorInverse

/-!
# Continuity of inversion in the weak Whitney topology

For compact manifolds with a locally compact source model space, the inverse of a
diffeomorphism depends continuously on the diffeomorphism in the weak Whitney topology.
Together with continuity of composition, this makes the self-diffeomorphisms a topological
group. The result includes manifolds with boundary and corners and arbitrary differentiability
order, including smooth maps.

Higher inverse derivatives are recovered recursively from the Faà di Bruno formula for
`f.symm ∘ f = id`. The singleton-partition term is invertible; every remaining term uses a
strictly lower derivative of the inverse. Compactness then turns joint continuity of inverse
jets into openness of the defining chart tests.

The topology convention follows M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney TauCeti.ManifoldWeakWhitney

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- Composing the inverse and forward coordinate Taylor series gives the Taylor series of the
identity at the source point. -/
theorem taylorComp_symm_extChartAt (f : M ≃ₘ^n⟮I, J⟯ N) {x : M} {y : N} {w : F}
    (hw : w ∈ (extChartAt J y).target)
    (hf : f.symm ((extChartAt J y).symm w) ∈ (extChartAt I x).source)
    {m : ℕ} (hm : m ≤ n) :
    (ftaylorSeriesWithin 𝕜 (extChartAt I x ∘ f.symm ∘ (extChartAt J y).symm)
      (extChartAt J y).target w).taylorComp
      (ftaylorSeriesWithin 𝕜 (extChartAt J y ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x).target (extChartAt I x (f.symm ((extChartAt J y).symm w)))) m =
    iteratedFDerivWithin 𝕜 m (id : E → E) (extChartAt I x).target
      (extChartAt I x (f.symm ((extChartAt J y).symm w))) := by
  set φ := extChartAt I x with hφdef
  set ψ := extChartAt J y with hψdef
  have hfw : f (φ.symm (φ (f.symm (ψ.symm w)))) ∈ ψ.source := by
    simpa only [φ.left_inv hf, Diffeomorph.apply_symm_apply] using ψ.map_target hw
  have h := ContMDiffMap.iteratedFDerivWithin_extChartAt_comp
    f.symm.toContMDiffMap f.toContMDiffMap (x := x) (y := y) (z := x)
    (φ.map_source hf) hfw
    (by simpa only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk,
      ← hφdef, φ.left_inv hf, Diffeomorph.symm_apply_apply] using hf) hm
  simp only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk, ← hφdef, ← hψdef,
    φ.left_inv hf, Diffeomorph.apply_symm_apply, ψ.right_inv hw] at h
  have heq : φ ∘ f.symm ∘ f ∘ φ.symm
      =ᶠ[𝓝[φ.target] (φ (f.symm (ψ.symm w)))] id := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply, φ.right_inv hu, id_eq]
  have hid := heq.iteratedFDerivWithin_eq (𝕜 := 𝕜) (by
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply,
      φ.right_inv (φ.map_source hf), id_eq]) m
  exact h.symm.trans hid

end Diffeomorph

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}
  [CompactSpace M] [T2Space N] [LocallyCompactSpace E]
  [IsManifold I n M] [IsManifold J n N]

/-- Every inverse coordinate derivative varies continuously with the diffeomorphism and the
point of the target chart, including boundary and corner points. -/
theorem tendsto_iteratedFDerivWithin_diffeomorph_symm_extChartAt
    {f₀ : M ≃ₘ^n⟮I, J⟯ N} {x : M} {y : N} {w₀ : F}
    (hw₀ : w₀ ∈ (extChartAt J y).target)
    (hf₀ : f₀.symm ((extChartAt J y).symm w₀) ∈ (extChartAt I x).source)
    {m : ℕ} (hm : m ≤ n) :
    Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦
      iteratedFDerivWithin 𝕜 m (extChartAt I x ∘ p.1.symm ∘ (extChartAt J y).symm)
        (extChartAt J y).target p.2)
      (𝓝 f₀ ×ˢ 𝓝[(extChartAt J y).target] w₀)
      (𝓝 (iteratedFDerivWithin 𝕜 m (extChartAt I x ∘ f₀.symm ∘ (extChartAt J y).symm)
        (extChartAt J y).target w₀)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    set φ := extChartAt I x with hφdef
    set ψ := extChartAt J y with hψdef
    -- Track the inverse image in a fixed source chart; this also settles order zero.
    let z₀ := f₀.symm (ψ.symm w₀)
    let l := 𝓝 f₀ ×ˢ 𝓝[ψ.target] w₀
    let v := fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦ p.1.symm (ψ.symm p.2)
    have hpt : Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦ (p.1, ψ.symm p.2)) l
        (𝓝 (f₀, ψ.symm w₀)) := by
      rw [nhds_prod_eq]
      exact (tendsto_fst : Tendsto Prod.fst l (𝓝 f₀)).prodMk
        ((continuousOn_extChartAt_symm y w₀ hw₀).tendsto.comp tendsto_snd)
    have hv : Tendsto v l (𝓝 z₀) :=
      (continuous_diffeomorph_symm_eval.tendsto (f₀, ψ.symm w₀)).comp hpt
    have hsrc : ∀ᶠ p in l, v p ∈ φ.source :=
      hv.eventually ((isOpen_extChartAt_source x).mem_nhds hf₀)
    have hφ : Tendsto (fun p ↦ φ (v p)) l (𝓝[φ.target] (φ z₀)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(continuousOn_extChartAt x z₀ hf₀).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hv, hsrc⟩), hsrc.mono fun _ hp ↦ φ.map_source hp⟩
    rcases m with _ | m
    · have h := ((continuousMultilinearCurryFin0 𝕜 F E).symm.continuous.tendsto _).comp
        (tendsto_nhdsWithin_iff.mp hφ).1
      simpa only [iteratedFDerivWithin_zero_eq_comp, Function.comp_def] using h
    have h1 : (1 : ℕ∞ω) ≤ m + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have hn : 1 ≤ n := h1.trans hm
    have hn' : n ≠ 0 := by rintro rfl; simp at hn
    have hz₀ : f₀ z₀ ∈ ψ.source := by
      simpa only [z₀, Diffeomorph.apply_symm_apply] using ψ.map_target hw₀
    have hz₀' : z₀ ∈ φ.source := hf₀
    have hvis : f₀.toContMDiffMap (φ.symm (φ z₀)) ∈ ψ.source := by
      simpa only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk, φ.left_inv hz₀'] using hz₀
    -- All forward jets can be evaluated continuously at this moving inverse image.
    have hforward : Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦
        (p.1.toContMDiffMap, φ (v p))) l
        (𝓝 f₀.toContMDiffMap ×ˢ 𝓝[φ.target] (φ z₀)) :=
      (Diffeomorph.continuous_toContMDiffMap.continuousAt.tendsto.comp
        (tendsto_fst : Tendsto Prod.fst l (𝓝 f₀))).prodMk hφ
    let q := fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦
      ftaylorSeriesWithin 𝕜 (φ ∘ p.1.symm ∘ ψ.symm) ψ.target p.2
    let p := fun a : (M ≃ₘ^n⟮I, J⟯ N) × F ↦
      ftaylorSeriesWithin 𝕜 (ψ ∘ a.1 ∘ φ.symm) φ.target (φ (v a))
    let q₀ := ftaylorSeriesWithin 𝕜 (φ ∘ f₀.symm ∘ ψ.symm) ψ.target w₀
    let p₀ := ftaylorSeriesWithin 𝕜 (ψ ∘ f₀ ∘ φ.symm) φ.target (φ z₀)
    let A := fun a : (M ≃ₘ^n⟮I, J⟯ N) × F ↦
      fderivWithin 𝕜 (φ ∘ a.1.symm ∘ ψ.symm) ψ.target a.2
    let A₀ := fderivWithin 𝕜 (φ ∘ f₀.symm ∘ ψ.symm) ψ.target w₀
    -- The composite jet is the identity jet at the moving source point.
    have hcomp : Tendsto (fun a ↦ (q a).taylorComp (p a) (m + 1)) l
        (𝓝 (q₀.taylorComp p₀ (m + 1))) := by
      rw [Diffeomorph.taylorComp_symm_extChartAt f₀ hw₀ hf₀ hm]
      have hid := (contDiff_id.contDiffOn : ContDiffOn 𝕜 n (id : E → E) φ.target)
        |>.continuousOn_iteratedFDerivWithin hm (uniqueDiffOn_extChartAt_target x)
      apply (hid _ (φ.map_source hf₀)).tendsto.comp hφ |>.congr'
      filter_upwards [hsrc, tendsto_snd.eventually self_mem_nhdsWithin] with a ha hw
      exact (Diffeomorph.taylorComp_symm_extChartAt a.1 hw ha hm).symm
    -- The first inverse differential is a right inverse of the forward linear coefficient.
    have hright (f : M ≃ₘ^n⟮I, J⟯ N) {w : F} (hw : w ∈ ψ.target)
        (hf : f.symm (ψ.symm w) ∈ φ.source) :
        (continuousMultilinearCurryFin1 𝕜 E F
          (ftaylorSeriesWithin 𝕜 (ψ ∘ f ∘ φ.symm) φ.target
            (φ (f.symm (ψ.symm w))) 1)).comp
          (fderivWithin 𝕜 (φ ∘ f.symm ∘ ψ.symm) ψ.target w) = .id 𝕜 F := by
      have hc : continuousMultilinearCurryFin1 𝕜 E F
          (ftaylorSeriesWithin 𝕜 (ψ ∘ f ∘ φ.symm) φ.target
            (φ (f.symm (ψ.symm w))) 1) =
          fderivWithin 𝕜 (ψ ∘ f ∘ φ.symm) φ.target (φ (f.symm (ψ.symm w))) := by
        ext u
        exact iteratedFDerivWithin_one_apply
          ((uniqueDiffOn_extChartAt_target x) _ (φ.map_source hf)) _
      rw [hc]
      have hss : f.symm.symm = f := Diffeomorph.ext fun _ ↦ rfl
      simpa only [hss, ← hφdef, ← hψdef, ψ.right_inv hw] using
        fderivWithin_diffeomorph_chart_symm_comp f.symm hn' (ψ.map_target hw) hf
    -- Recover the next inverse coefficient from the lower ones and the identity composite.
    apply Filter.Tendsto.of_taylorComp (q := q) (p := p) (q₀ := q₀) (p₀ := p₀)
      (A := A) (A₀ := A₀) (Nat.zero_lt_succ m)
    · intro k _ hk
      have hk' : (k : ℕ∞ω) ≤ m + 1 := by exact_mod_cast Nat.le_of_lt hk
      exact ih k hk (hk'.trans hm)
    · intro k _ hk
      have hk' : (k : ℕ∞ω) ≤ m + 1 := by exact_mod_cast hk
      simpa only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk, Function.comp_def,
        ftaylorSeriesWithin, p, p₀, φ, ψ] using
        (ContMDiffMap.tendsto_iteratedFDerivWithin_extChartAt (φ.map_source hf₀) hvis
          (hk'.trans hm)).comp hforward
    · exact hcomp
    · exact tendsto_fderivWithin_diffeomorph_symm_extChartAt hn hw₀ hf₀
    · filter_upwards [hsrc, tendsto_snd.eventually self_mem_nhdsWithin] with a ha hw
      exact hright a.1 hw ha
    · exact hright f₀ hw₀ hf₀

end TauCeti

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

variable [CompactSpace M] [CompactSpace N] [T2Space N] [LocallyCompactSpace E]
  [IsManifold I n M] [IsManifold J n N]

/-- Inversion of diffeomorphisms is continuous for the weak Whitney topology on compact
manifolds whose source model space is locally compact, at every differentiability order. -/
theorem continuous_symm : Continuous (Diffeomorph.symm : (M ≃ₘ^n⟮I, J⟯ N) → N ≃ₘ^n⟮J, I⟯ M) := by
  refine continuous_weakWhitney_iff.mpr ?_
  refine continuous_iff_continuousAt.mpr fun f₀ ↦ ?_
  refine ContMDiffMap.tendsto_manifoldWeakWhitney_iff.mpr fun y x m hm K hK V hV h₀ ↦ ?_
  simp only [ContMDiffMap.mem_chartJetSet] at h₀ ⊢
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  have he : Continuous (fun p : (M ≃ₘ^n⟮I, J⟯ N) × (extChartAt J y).target ↦
      p.1.symm ((extChartAt J y).symm p.2)) :=
    TauCeti.continuous_diffeomorph_symm_eval.comp (continuous_fst.prodMk
      ((continuousOn_iff_continuous_domRestrict.mp
        (continuousOn_extChartAt_symm (I := J) y)).comp continuous_snd))
  have hsrc : ∀ᶠ p : (M ≃ₘ^n⟮I, J⟯ N) × (extChartAt J y).target in 𝓝 (f₀, w),
      p.1.symm ((extChartAt J y).symm p.2) ∈ (extChartAt I x).source :=
    he.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source x).mem_nhds (h₀ w hw).1)
  have hD := (TauCeti.tendsto_iteratedFDerivWithin_diffeomorph_symm_extChartAt
    w.2 (h₀ w hw).1 hm).eventually (hV.mem_nhds (h₀ w hw).2)
  rw [nhds_prod_eq] at hsrc ⊢
  simpa only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq, Membership.mem, Set.Mem] using
    hsrc.and ((tendsto_id.prodMap (map_nhds_subtype_val w).le).eventually hD)

variable [T2Space M]

/-- Self-diffeomorphisms of a compact Hausdorff manifold with a locally compact model space
form a topological group for the weak Whitney topology. -/
theorem isTopologicalGroup : IsTopologicalGroup (M ≃ₘ^n⟮I, I⟯ M) where
  continuous_mul := continuousMul.continuous_mul
  continuous_inv := continuous_symm

scoped[TauCeti.DiffeomorphWeakWhitney] attribute [instance] Diffeomorph.isTopologicalGroup

end Diffeomorph
