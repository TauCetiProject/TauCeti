/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Smooth families of manifold-valued maps are continuous

A jointly `C^n` map `P × M → N` between manifolds is a family of `C^n` maps `M → N` indexed by
`P`, and this file proves that the family is continuous for the weak Whitney topology on
`C^n⟮I, M; J, N⟯`. This is the direction that turns the object a proof produces, a smooth map on
a product, into the object a homotopy-theoretic statement needs, a map into a function space.
Nothing is claimed in the reverse direction: an arbitrary continuous family into the map space
need not be smooth on the product.

A weak Whitney basic set only constrains a map where it meets a fixed target chart, so the
coordinate representative of the family is defined only on the open set of parameters and chart
points at which the family is visible in that chart. The representative is differentiated there
by `ContMDiff.continuousOn_iteratedFDerivWithin_extChartAt`, and the continuity statement then
follows from a tube lemma turning pointwise membership in a derivative test into a parameter
neighbourhood. Taking `J = 𝓘(𝕜, F)` recovers the vector-valued case, the two topologies being
identified by `ContMDiffMap.manifoldWeakWhitneyTopology_self_target`.

Use `open scoped TauCeti.ManifoldWeakWhitney` to select the topology these statements are about.

## Main results

* `Continuous.isOpen_setOf_mem_extChartAt_source`: the parameters and chart points at which a
  continuous map on `P × M` is visible in a target chart form an open set.
* `ContMDiff.continuousOn_iteratedFDerivWithin_extChartAt`: there the coordinate derivative of
  the family depends continuously on the parameter and the chart point jointly.
* `ContMDiff.continuous_manifoldWeakWhitney`: joint `C^n` regularity gives continuity into the
  weak Whitney topology.
* `ContMDiffMap.manifoldWeakWhitneyCurry`: the resulting continuous family, bundled.

The weak topology convention follows M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Set Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold I' n P] [IsManifold J n N]

omit [ChartedSpace H' P] [IsManifold I n M] [IsManifold I' n P] [IsManifold J n N] in
/-- The parameters and source-chart points at which a continuous map on `P × M`, read as a
family of maps `M → N`, is visible in the extended chart around `y` form an open set. Exactly
there is the coordinate representative of the family, and hence the derivative tested by
`ContMDiffMap.chartJetSet`, defined. -/
theorem Continuous.isOpen_setOf_mem_extChartAt_source {g : P × M → N} (hg : Continuous g)
    (x : M) (y : N) :
    IsOpen {z : P × (extChartAt I x).target |
      g (z.1, (extChartAt I x).symm ↑z.2) ∈ (extChartAt J y).source} := by
  refine (isOpen_extChartAt_source (I := J) y).preimage (hg.comp (continuous_fst.prodMk ?_))
  exact ((continuousOn_extChartAt_symm x).domRestrict).comp continuous_snd

/-- On the open set where a jointly `C^n` map on `P × M`, read as a family of maps `M → N`, is
visible in the extended chart around `y`, the `m`-th coordinate derivative of the family depends
continuously on the parameter and the source-chart point jointly. The derivative is taken within
the whole extended source chart target, as the weak Whitney tests take it, so boundary and corner
points are covered. -/
theorem ContMDiff.continuousOn_iteratedFDerivWithin_extChartAt {g : P × M → N}
    (hg : ContMDiff (I'.prod I) J n g) (x : M) (y : N) (m : ℕ) (hm : m ≤ n) :
    ContinuousOn (fun z : P × (extChartAt I x).target ↦ iteratedFDerivWithin 𝕜 m
        (fun b ↦ extChartAt J y (g (z.1, (extChartAt I x).symm b))) (extChartAt I x).target ↑z.2)
      {z : P × (extChartAt I x).target |
        g (z.1, (extChartAt I x).symm ↑z.2) ∈ (extChartAt J y).source} := by
  set d : P × (extChartAt I x).target → E [×m]→L[𝕜] F := fun z ↦ iteratedFDerivWithin 𝕜 m
    (fun b ↦ extChartAt J y (g (z.1, (extChartAt I x).symm b))) (extChartAt I x).target ↑z.2
    with hd_def
  have hA := hg.continuous.isOpen_setOf_mem_extChartAt_source (I := I) (J := J) x y
  rintro ⟨p₀, z₀⟩ hp₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨W, U, hWo, hUo, hpW, hzU, hWU⟩ := isOpen_prod_iff.mp hA p₀ z₀ hp₀
  -- Move the chart neighbourhood `U` of `z₀` and the parameter neighbourhood `W` of `p₀` into
  -- the two model spaces, where the coordinate representative can be differentiated.
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hUo
  set O : Set P := (chartAt H' p₀).source ∩ W
  have hOo : IsOpen O := (chartAt H' p₀).open_source.inter hWo
  have hp₀O : p₀ ∈ O := ⟨mem_chart_source H' p₀, hpW⟩
  obtain ⟨W₁, hW₁o, hW₁⟩ :=
    continuousOn_iff'.mp (continuousOn_extChartAt_symm (I := I') p₀) O hOo
  set S : Set E' := (extChartAt I' p₀).target ∩ W₁
  set T : Set E := (extChartAt I x).target ∩ U' with hT_def
  -- The coordinate representative is `C^n` on `S ×ˢ T`.
  have hmapsTo : MapsTo
      (fun w : E' × E ↦ g ((extChartAt I' p₀).symm w.1, (extChartAt I x).symm w.2))
      (S ×ˢ T) (chartAt G y).source := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have hpa : (extChartAt I' p₀).symm a ∈ W := by
      have ha' : a ∈ (extChartAt I' p₀).symm ⁻¹' O ∩ (extChartAt I' p₀).target := by
        rw [hW₁]; exact ⟨ha.2, ha.1⟩
      exact ha'.1.2
    have hzb : (⟨b, hb.1⟩ : (extChartAt I x).target) ∈ U := by rw [← hU']; exact hb.2
    have := hWU (Set.mk_mem_prod hpa hzb)
    rw [Set.mem_ofPred_eq, extChartAt_source] at this
    exact this
  have h1 : ContMDiffOn 𝓘(𝕜, E' × E) J n
      (fun w : E' × E ↦ g ((extChartAt I' p₀).symm w.1, (extChartAt I x).symm w.2))
      ((extChartAt I' p₀).target ×ˢ (extChartAt I x).target) :=
    contMDiffOn_prod_modelWithCornersSelf_iff.mp <| hg.comp_contMDiffOn
      ((contMDiffOn_extChartAt_symm p₀).prodMap (contMDiffOn_extChartAt_symm x))
  have h2 : ContDiffOn 𝕜 n (fun w : E' × E ↦ extChartAt J y
      (g ((extChartAt I' p₀).symm w.1, (extChartAt I x).symm w.2))) (S ×ˢ T) :=
    ((contMDiffOn_extChartAt (I := J) (n := n) (x := y)).comp
      (h1.mono (prod_mono inter_subset_left inter_subset_left)) hmapsTo).contDiffOn
  have hST : UniqueDiffOn 𝕜 (S ×ˢ T) :=
    UniqueDiffOn.prod ((uniqueDiffOn_extChartAt_target p₀).inter hW₁o)
      ((uniqueDiffOn_extChartAt_target x).inter hU'o)
  have hcont := h2.continuousOn_iteratedFDerivWithin_prod_right hST m hm
  -- Read the derivative back on the parameter manifold and in the full source chart target.
  have hmapsTo2 : MapsTo (fun z : P × (extChartAt I x).target ↦ (extChartAt I' p₀ z.1, (↑z.2 : E)))
      (O ×ˢ U) (S ×ˢ T) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hpsource : p ∈ (extChartAt I' p₀).source := by rw [extChartAt_source]; exact hp.1
    refine ⟨⟨(extChartAt I' p₀).map_source hpsource, ?_⟩, ⟨z.2, ?_⟩⟩
    · have hp' : extChartAt I' p₀ p ∈ W₁ ∩ (extChartAt I' p₀).target := by
        rw [← hW₁]
        refine ⟨?_, (extChartAt I' p₀).map_source hpsource⟩
        rw [mem_preimage, (extChartAt I' p₀).left_inv hpsource]
        exact hp
      exact hp'.1
    · rw [← hU'] at hz; exact hz
  have hd : ContinuousOn d (O ×ˢ U) := by
    refine (hcont.comp ?_ hmapsTo2).congr ?_
    · exact ((continuousOn_extChartAt p₀).mono (fun p hp ↦ by
        rw [extChartAt_source]; exact hp.1)).comp continuousOn_fst
        (fun z hz ↦ hz.1) |>.prodMk (continuous_subtype_val.comp_continuousOn continuousOn_snd)
    · rintro ⟨p, z⟩ ⟨hp, hz⟩
      have hpsource : p ∈ (extChartAt I' p₀).source := by rw [extChartAt_source]; exact hp.1
      have hzU' : (↑z : E) ∈ U' := by rw [← hU'] at hz; exact hz
      simp only [Function.comp_apply, hd_def, (extChartAt I' p₀).left_inv hpsource]
      rw [hT_def, iteratedFDerivWithin_inter_open hU'o hzU']
  exact hd.continuousAt ((hOo.prod hUo).mem_nhds (Set.mk_mem_prod hp₀O hzU))

/-- Joint `C^n` regularity gives continuity into the weak Whitney topology on manifold-valued
`C^n` maps. Neither compactness nor absence of boundary is required of the parameter, the source
or the target. -/
theorem ContMDiff.continuous_manifoldWeakWhitney {f : P → C^n⟮I, M; J, N⟯}
    (hf : ContMDiff (I'.prod I) J n fun z : P × M ↦ f z.1 z.2) :
    Continuous f := by
  refine ContMDiffMap.continuous_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV ↦ ?_
  rw [isOpen_iff_forall_mem_open]
  intro p₀ hp₀
  rw [mem_preimage, ContMDiffMap.mem_chartJetSet] at hp₀
  -- A tube lemma turns pointwise membership in the open derivative test into a parameter
  -- neighbourhood on which the whole compact test set stays inside it.
  obtain ⟨u, v, huo, hvo, hpu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK
    ((hf.continuousOn_iteratedFDerivWithin_extChartAt x y m hm).isOpen_inter_preimage
      (hf.continuous.isOpen_setOf_mem_extChartAt_source (I := I) (J := J) x y) hV)
    (by
      rintro ⟨p, z⟩ ⟨hp, hz⟩
      obtain rfl := hp
      exact ⟨(hp₀ z hz).1, by
        simpa only [mem_preimage, Function.comp_def] using (hp₀ z hz).2⟩)
  refine ⟨u, fun p hp ↦ ?_, huo, hpu rfl⟩
  rw [mem_preimage, ContMDiffMap.mem_chartJetSet]
  intro z hz
  have hmem := huv (Set.mk_mem_prod hp (hKv hz))
  exact ⟨hmem.1, by simpa only [mem_preimage, Function.comp_def] using hmem.2⟩

namespace ContMDiffMap

/-- Curry a jointly `C^n` map on a product of manifolds into a continuous family of `C^n` maps,
for the weak Whitney topology on the space of manifold-valued `C^n` maps. -/
noncomputable def manifoldWeakWhitneyCurry (f : C^n⟮I'.prod I, P × M; J, N⟯) :
    C(P, C^n⟮I, M; J, N⟯) where
  toFun p := ⟨fun x ↦ f (p, x), f.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)⟩
  continuous_toFun := f.contMDiff.continuous_manifoldWeakWhitney

/-- Evaluating the curried family at `p` and `x` recovers `f (p, x)`. -/
@[simp]
theorem manifoldWeakWhitneyCurry_apply (f : C^n⟮I'.prod I, P × M; J, N⟯) (p : P) (x : M) :
    manifoldWeakWhitneyCurry f p x = f (p, x) := (rfl)

end ContMDiffMap
