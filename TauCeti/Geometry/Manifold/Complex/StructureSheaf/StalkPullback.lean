/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import TauCeti.Order.Filter.Germ

/-!
# Pullback of holomorphic stalks by local analytic maps

`stalkPullback` pulls back holomorphic germs along a map between complex manifolds analytic
near the chosen point. Unlike the sheaf morphism `stalkPrecomp`, this requires no globally
holomorphic extension of the map. Equality, evaluation and composition are characterized
through the injective comparison with function germs. The two pullbacks agree when both apply.
Pullback along a map with a local analytic inverse, such as a chart, is bijective
(`stalkPullback_bijective`), in particular pullback along a continuous linear equivalence
(`ContinuousLinearEquiv.holomorphicStalkPullback_bijective`) and along a chart followed by one
(`stalkPullback_comp_extChartAt_bijective`), which identifies a stalk of a manifold with a stalk
of its model.
On the complex line, `eventually_contMDiffAt_of_analyticAt` supplies the local hypothesis
from `AnalyticAt`.
-/

public noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]
  {f : X → Y} {a : X} (hf : ∀ᶠ y in 𝓝 a, ContMDiffAt I J ω f y)

private theorem exists_stalkPullback
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f a)) :
    ∃ t, toFilterGerm I X a (𝓝 a) le_rfl t =
      (toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl s).compTendsto f
        hf.self_of_nhds.continuousAt.tendsto := by
  obtain ⟨u, hu, hus⟩ := exists_toFilterGerm_eq (f a) s
  obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt
    ((hf.and (hf.self_of_nhds.continuousAt.tendsto.eventually hu)).mono
      fun z hz ↦ hz.2.comp z hz.1)
  exact ⟨t, by rw [ht, hus, Germ.coe_compTendsto]⟩

/-- Pullback of holomorphic germs by a map analytic near the base point. -/
def stalkPullback :
    (holomorphicStructureSheaf J Y).presheaf.stalk (f a) →+*
      (holomorphicStructureSheaf I X).presheaf.stalk a where
  toFun s := (exists_stalkPullback hf s).choose
  map_one' := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf 1).choose_spec, map_one, map_one]
    simpa only [Germ.compTendstoRingHom_apply] using
      (Germ.compTendstoRingHom (R := ℂ) f hf.self_of_nhds.continuousAt.tendsto).map_one
  map_mul' s t := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf (s * t)).choose_spec, map_mul, map_mul,
      (exists_stalkPullback hf s).choose_spec, (exists_stalkPullback hf t).choose_spec]
    simpa only [Germ.compTendstoRingHom_apply] using
      (Germ.compTendstoRingHom f hf.self_of_nhds.continuousAt.tendsto).map_mul
        (toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl s)
        (toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl t)
  map_zero' := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf 0).choose_spec, map_zero, map_zero]
    simpa only [Germ.compTendstoRingHom_apply] using
      (Germ.compTendstoRingHom (R := ℂ) f hf.self_of_nhds.continuousAt.tendsto).map_zero
  map_add' s t := by
    apply toFilterGerm_nhds_injective a
    rw [(exists_stalkPullback hf (s + t)).choose_spec, map_add, map_add,
      (exists_stalkPullback hf s).choose_spec, (exists_stalkPullback hf t).choose_spec]
    simpa only [Germ.compTendstoRingHom_apply] using
      (Germ.compTendstoRingHom f hf.self_of_nhds.continuousAt.tendsto).map_add
        (toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl s)
        (toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl t)

/-- The function germ of a pulled-back holomorphic germ is its composition with the map. -/
@[simp]
theorem toFilterGerm_stalkPullback
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f a)) :
    toFilterGerm I X a (𝓝 a) le_rfl (stalkPullback hf s) =
      (toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl s).compTendsto f
        hf.self_of_nhds.continuousAt.tendsto :=
  (exists_stalkPullback hf s).choose_spec

/-- Pullback preserves the value of a holomorphic germ. -/
@[simp]
theorem eval_stalkPullback
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f a)) :
    eval I X a (stalkPullback hf s) = eval J Y (f a) s := by
  obtain ⟨u, _, hus⟩ := exists_toFilterGerm_eq (f a) s
  have h := toFilterGerm_stalkPullback hf s
  rw [hus, Germ.coe_compTendsto] at h
  exact (eval_eq_of_toFilterGerm_eq h).trans (eval_eq_of_toFilterGerm_eq (hus _ le_rfl)).symm

/-- Local analytic pullback is a local ring homomorphism. -/
instance isLocalHom_stalkPullback : IsLocalHom (stalkPullback hf) where
  map_nonunit s hs := (isUnit_stalk_iff J Y s).mpr (by
    simpa only [eval_stalkPullback] using ((isUnit_stalk_iff I X _).mp hs))

/-- On globally analytic maps, local pullback is the structure-sheaf stalk map. -/
theorem stalkPullback_eq_stalkPrecomp (f : X → Y) (hf : ContMDiff I J ω f) (a : X) :
    stalkPullback (Eventually.of_forall fun _ ↦ hf.contMDiffAt) =
      stalkPrecomp I X f hf a := by
  ext s
  apply toFilterGerm_nhds_injective a
  rw [toFilterGerm_stalkPullback, toFilterGerm_stalkPrecomp]

/-- Pullback by the identity fixes every germ. -/
@[simp]
theorem stalkPullback_id (a : X) :
    stalkPullback (I := I) (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := I))
      (a := a) = RingHom.id _ := by
  rw [stalkPullback_eq_stalkPrecomp id contMDiff_id a, stalkPrecomp_id]

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- Pullback by a composite is the composite of the pullbacks, in reverse order. -/
theorem stalkPullback_comp {g : Y → Z} (hg : ∀ᶠ y in 𝓝 (f a), ContMDiffAt J K ω g y)
    (s : (holomorphicStructureSheaf K Z).presheaf.stalk (g (f a))) :
    stalkPullback ((hf.and (hf.self_of_nhds.continuousAt.tendsto.eventually hg)).mono
      fun z hz ↦ hz.2.comp z hz.1) s = stalkPullback hf (stalkPullback hg s) := by
  apply toFilterGerm_nhds_injective a
  simp only [toFilterGerm_stalkPullback]
  exact Germ.inductionOn
    (toFilterGerm K Z (g (f a)) (𝓝 (g (f a))) le_rfl s) fun _ ↦ rfl

/-- Pullback along a map with a local analytic inverse near the base point, such as a chart or a
biholomorphism, is bijective. -/
theorem stalkPullback_bijective {g : Y → X} (hg : ∀ᶠ y in 𝓝 (f a), ContMDiffAt J I ω g y)
    (hgf : ∀ᶠ x in 𝓝 a, g (f x) = x) (hfg : ∀ᶠ y in 𝓝 (f a), f (g y) = y) :
    Function.Bijective (stalkPullback hf) := by
  have hg_tendsto : Tendsto g (𝓝 (f a)) (𝓝 a) := by
    simpa only [hgf.self_of_nhds] using hg.self_of_nhds.continuousAt.tendsto
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, fun s ↦ ?_⟩
  · -- A germ whose composition with `f` vanishes near `a` vanishes near `f a = f (g (f a))`.
    obtain ⟨u, -, hu⟩ := exists_toFilterGerm_eq (f a) s
    apply toFilterGerm_nhds_injective (f a)
    have h0 := congrArg (toFilterGerm I X a (𝓝 a) le_rfl) hs
    rw [toFilterGerm_stalkPullback, hu, Germ.coe_compTendsto, map_zero, ← Germ.coe_zero,
      Germ.coe_eq] at h0
    rw [hu, map_zero, ← Germ.coe_zero, Germ.coe_eq]
    filter_upwards [hfg, hg_tendsto.eventually h0] with y hy hy0
    simpa [hy] using hy0
  · -- A germ `u` at `a` is the pullback of the germ `u ∘ g` at `f a`.
    obtain ⟨u, hu_an, hu⟩ := exists_toFilterGerm_eq a s
    obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt (x := f a) (f := u ∘ g)
      ((hg.and (hg_tendsto.eventually hu_an)).mono fun y hy ↦ hy.2.comp y hy.1)
    refine ⟨t, toFilterGerm_nhds_injective a ?_⟩
    rw [toFilterGerm_stalkPullback, ht _ le_rfl, hu, Germ.coe_compTendsto, Germ.coe_eq]
    filter_upwards [hgf] with x hx
    simp [hx]

variable [I.Boundaryless] [IsManifold I ω X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Pullback along the extended chart at `x`, followed by a continuous linear equivalence `e` of
the model onto a complex normed space `V`, is bijective on holomorphic stalks. The equivalence
lets the model stalk live in `Type` even when the model space `E` does not. -/
theorem stalkPullback_comp_extChartAt_bijective (x : X) (e : E ≃L[ℂ] V) :
    Function.Bijective (stalkPullback (J := 𝓘(ℂ, V)) (f := e ∘ extChartAt I x) (a := x)
      (((chartAt H x).open_source.eventually_mem (mem_chart_source H x)).mono fun _ hy ↦
        e.contDiff.contMDiff.contMDiffAt.comp _ (contMDiffAt_extChartAt' hy))) := by
  have hmem : ∀ᶠ z in 𝓝 (e (extChartAt I x x)), e.symm z ∈ (extChartAt I x).target := by
    have h := e.symm.continuous.tendsto (e (extChartAt I x x))
    rw [e.symm_apply_apply] at h
    exact h.eventually (extChartAt_target_mem_nhds x)
  refine stalkPullback_bijective _ (g := (extChartAt I x).symm ∘ e.symm) ?_ ?_ ?_
  · filter_upwards [hmem] with z hz
    exact ((contMDiffOn_extChartAt_symm (n := ω) x).contMDiffAt
      (extChartAt_target_mem_nhds' hz)).comp z e.symm.contDiff.contMDiff.contMDiffAt
  · filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
    simpa using (extChartAt I x).left_inv hy
  · filter_upwards [hmem] with z hz
    simp only [Function.comp_apply, (extChartAt I x).right_inv hz,
      ContinuousLinearEquiv.apply_symm_apply]

end TauCeti.holomorphicStructureSheaf

namespace ContinuousLinearEquiv

open TauCeti.holomorphicStructureSheaf

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- Pullback along a continuous linear equivalence is bijective on holomorphic stalks. -/
theorem holomorphicStalkPullback_bijective (e : V ≃L[ℂ] W) (x : V) :
    Function.Bijective (stalkPullback (I := 𝓘(ℂ, V)) (J := 𝓘(ℂ, W)) (a := x)
      (Eventually.of_forall fun _ ↦ e.contDiff.contMDiff.contMDiffAt)) :=
  stalkPullback_bijective _ (Eventually.of_forall fun _ ↦ e.symm.contDiff.contMDiff.contMDiffAt)
    (Eventually.of_forall e.symm_apply_apply) (Eventually.of_forall e.apply_symm_apply)

end ContinuousLinearEquiv
