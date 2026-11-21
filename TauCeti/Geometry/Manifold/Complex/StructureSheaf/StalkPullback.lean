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
Pullback along a map with a local analytic inverse, such as a chart, is an equivalence
(`stalkPullbackEquiv`), with evaluation and function-germ laws in both directions.
It is in particular bijective (`stalkPullback_bijective`), as is pullback along a continuous
linear equivalence (`ContinuousLinearEquiv.holomorphicStalkPullback_bijective`). For a boundaryless
model, `OpenPartialHomeomorph.holomorphicStalkEquivModelSpace` identifies a manifold stalk with a
stalk on a continuously linearly equivalent model space using any analytic chart;
`stalkEquivModelSpace` specializes this ring equivalence to the preferred chart, which identifies
a stalk of a finite-dimensional manifold with a stalk of a model space in `Type`
(`exists_ringEquiv_stalk_modelSpace`). Together with isolated-point evaluation in dimension zero,
this gives an induction principle on the complex dimension (`stalk_induction_modelSpace` on
`Fin n → ℂ`, and `stalk_induction` on finite-dimensional boundaryless complex manifolds) for
isomorphism-invariant ring properties of holomorphic stalks.
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

/-- Pullback is surjective if the map admits a holomorphic local left inverse near the
base point. -/
theorem stalkPullback_surjective_of_eventually_leftInverse {g : Y → X}
    (hg : ∀ᶠ y in 𝓝 (f a), ContMDiffAt J I ω g y)
    (hgf : (g ∘ f) =ᶠ[𝓝 a] id) : Function.Surjective (stalkPullback hf) := by
  intro s
  obtain ⟨u, hu, hus⟩ := exists_toFilterGerm_eq a s
  have hga : g (f a) = a := hgf.self_of_nhds
  have hnear : ∀ᶠ y in 𝓝 (f a), ContMDiffAt J 𝓘(ℂ) ω (u ∘ g) y := by
    filter_upwards [hg, hg.self_of_nhds.continuousAt.tendsto.eventually (by
      simpa only [hga] using hu)] with y hy huy
    exact huy.comp y hy
  obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt hnear
  refine ⟨t, toFilterGerm_nhds_injective a ?_⟩
  rw [toFilterGerm_stalkPullback, ht, Germ.coe_compTendsto, hus, Germ.coe_eq]
  filter_upwards [hgf] with z hz
  exact congrArg u hz

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
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_,
    stalkPullback_surjective_of_eventually_leftInverse hf hg hgf⟩
  -- A germ whose composition with `f` vanishes near `a` vanishes near `f a = f (g (f a))`.
  obtain ⟨u, -, hu⟩ := exists_toFilterGerm_eq (f a) s
  have h0 := (eq_zero_iff_of_toFilterGerm_eq (f := u ∘ f) (by
    rw [toFilterGerm_stalkPullback, hu, Germ.coe_compTendsto])).1 hs
  refine (eq_zero_iff_of_toFilterGerm_eq (hu _ le_rfl)).2 ?_
  filter_upwards [hfg, hg_tendsto.eventually h0] with y hy hy0
  simpa [hy] using hy0

section LocalInverse

variable {g : Y → X} (hg : ∀ᶠ y in 𝓝 (f a), ContMDiffAt J I ω g y)
  (hgf : ∀ᶠ x in 𝓝 a, g (f x) = x) (hfg : ∀ᶠ y in 𝓝 (f a), f (g y) = y)

/-- Pullback along a locally invertible analytic map is an equivalence of holomorphic stalks.
Only analyticity near the base points and the local inverse laws are required. -/
def stalkPullbackEquiv :
    (holomorphicStructureSheaf J Y).presheaf.stalk (f a) ≃+*
      (holomorphicStructureSheaf I X).presheaf.stalk a :=
  RingEquiv.ofBijective _ (stalkPullback_bijective hf hg hgf hfg)

/-- The local analytic equivalence acts by pullback. -/
theorem stalkPullbackEquiv_apply
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f a)) :
    stalkPullbackEquiv hf hg hgf hfg s = stalkPullback hf s := (rfl)

/-- Local analytic equivalence preserves evaluation. -/
@[simp]
theorem eval_stalkPullbackEquiv
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f a)) :
    eval I X a (stalkPullbackEquiv hf hg hgf hfg s) = eval J Y (f a) s := by
  rw [stalkPullbackEquiv_apply, eval_stalkPullback]

/-- Inverse local analytic equivalence preserves evaluation. -/
@[simp]
theorem eval_stalkPullbackEquiv_symm
    (s : (holomorphicStructureSheaf I X).presheaf.stalk a) :
    eval J Y (f a) ((stalkPullbackEquiv hf hg hgf hfg).symm s) = eval I X a s := by
  rw [← eval_stalkPullbackEquiv hf hg hgf hfg, RingEquiv.apply_symm_apply]

/-- On function germs, local analytic equivalence is composition with the map. -/
@[simp]
theorem toFilterGerm_stalkPullbackEquiv
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f a)) :
    toFilterGerm I X a (𝓝 a) le_rfl (stalkPullbackEquiv hf hg hgf hfg s) =
      (toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl s).compTendsto f
        hf.self_of_nhds.continuousAt.tendsto := by
  rw [stalkPullbackEquiv_apply, toFilterGerm_stalkPullback]

/-- On function germs, inverse local analytic equivalence is composition with the local
inverse. -/
@[simp]
theorem toFilterGerm_stalkPullbackEquiv_symm
    (s : (holomorphicStructureSheaf I X).presheaf.stalk a) :
    toFilterGerm J Y (f a) (𝓝 (f a)) le_rfl ((stalkPullbackEquiv hf hg hgf hfg).symm s) =
      (toFilterGerm I X a (𝓝 a) le_rfl s).compTendsto g
        (by simpa only [hgf.self_of_nhds] using hg.self_of_nhds.continuousAt.tendsto) := by
  have h := toFilterGerm_stalkPullbackEquiv hf hg hgf hfg
    ((stalkPullbackEquiv hf hg hgf hfg).symm s)
  rw [RingEquiv.apply_symm_apply] at h
  rw [h]
  generalize toFilterGerm J Y _ _ _ ((stalkPullbackEquiv hf hg hgf hfg).symm s) = t
  refine Germ.inductionOn t fun u ↦ ?_
  rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq]
  exact hfg.mono fun y hy ↦ congrArg u hy.symm

end LocalInverse

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- For a boundaryless model, an analytic chart identifies a holomorphic stalk with a stalk on a
continuously linearly equivalent model space `V : Type`. No global manifold instance is required. -/
def holomorphicStalkEquivModelSpace (c : OpenPartialHomeomorph X H)
    (hc : c ∈ IsManifold.maximalAtlas I ω X) (x : X) (hx : x ∈ c.source)
    (e : E ≃L[ℂ] V) :
    (holomorphicStructureSheaf I X).presheaf.stalk x ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (c.extend I x)) :=
  let hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℂ, V) ω (e ∘ c.extend I) y :=
    (c.open_source.eventually_mem hx).mono fun y hy ↦
      e.contDiff.contMDiff.contMDiffAt.comp y (c.contMDiffAt_extend hc hy)
  let hmem : ∀ᶠ z in 𝓝 (e (c.extend I x)), e.symm z ∈ (c.extend I).target := by
    have h := e.symm.continuous.tendsto (e (c.extend I x))
    rw [e.symm_apply_apply] at h
    exact h.eventually (c.isOpen_extend_target.mem_nhds
      ((c.extend I).map_source (by simpa only [c.extend_source] using hx)))
  (stalkPullbackEquiv hf (g := (c.extend I).symm ∘ e.symm)
    (by
      filter_upwards [hmem] with z hz
      exact ((contMDiffOn_extend_symm hc).contMDiffAt (by
        rw [← c.extend_target']
        exact c.isOpen_extend_target.mem_nhds hz)).comp z
          e.symm.contDiff.contMDiff.contMDiffAt)
    (by
      filter_upwards [c.open_source.eventually_mem hx] with y hy
      simp only [Function.comp_apply, e.symm_apply_apply, c.extend_left_inv hy])
    (by
      filter_upwards [hmem] with z hz
      simp only [Function.comp_apply, (c.extend I).right_inv hz, e.apply_symm_apply])).symm

variable (c : OpenPartialHomeomorph X H) (hc : c ∈ IsManifold.maximalAtlas I ω X)
  (x : X) (hx : x ∈ c.source) (e : E ≃L[ℂ] V)

/-- Inverse chart comparison is pullback along the extended chart followed by `e`. -/
theorem holomorphicStalkEquivModelSpace_symm_apply
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (c.extend I x))) :
    (c.holomorphicStalkEquivModelSpace hc x hx e).symm s =
      stalkPullback (J := 𝓘(ℂ, V)) (f := e ∘ c.extend I) (a := x)
        ((c.open_source.eventually_mem hx).mono fun y hy ↦
          e.contDiff.contMDiff.contMDiffAt.comp y (c.contMDiffAt_extend hc hy)) s := by
  -- Rewriting the constructor's extracted proofs requires unfolding neighborhood membership.
  erw [holomorphicStalkEquivModelSpace, RingEquiv.symm_symm, stalkPullbackEquiv_apply]

-- Unlike RingEquiv's post-order simp rules, these pre-order rules cancel before simp expands
-- the extended chart in the stalk's base point; without them, plain simp fails to cancel.
/-- Inverse chart comparison cancels chart comparison. -/
@[simp↓]
theorem holomorphicStalkEquivModelSpace_symm_apply_apply
    (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    (c.holomorphicStalkEquivModelSpace hc x hx e).symm
      (c.holomorphicStalkEquivModelSpace hc x hx e s) = s :=
  (c.holomorphicStalkEquivModelSpace hc x hx e).symm_apply_apply s

/-- Chart comparison cancels inverse chart comparison. -/
@[simp↓]
theorem holomorphicStalkEquivModelSpace_apply_symm_apply
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (c.extend I x))) :
    c.holomorphicStalkEquivModelSpace hc x hx e
      ((c.holomorphicStalkEquivModelSpace hc x hx e).symm s) = s :=
  (c.holomorphicStalkEquivModelSpace hc x hx e).apply_symm_apply s

-- Normalize chart comparison before simp expands the extended chart in the stalk's base point.
/-- Inverse chart comparison preserves evaluation. -/
@[simp↓]
theorem eval_holomorphicStalkEquivModelSpace_symm
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (c.extend I x))) :
    eval I X x ((c.holomorphicStalkEquivModelSpace hc x hx e).symm s) =
      eval 𝓘(ℂ, V) V (e (c.extend I x)) s := by
  simp only [c.holomorphicStalkEquivModelSpace_symm_apply, eval_stalkPullback,
    Function.comp_apply]

/-- Chart comparison preserves evaluation. -/
@[simp↓]
theorem eval_holomorphicStalkEquivModelSpace
    (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    eval 𝓘(ℂ, V) V (e (c.extend I x)) (c.holomorphicStalkEquivModelSpace hc x hx e s) =
      eval I X x s := by
  rw [← c.eval_holomorphicStalkEquivModelSpace_symm hc x hx e, RingEquiv.symm_apply_apply]

/-- On function germs, inverse chart comparison is composition with the chart and `e`. -/
@[simp↓]
theorem toFilterGerm_holomorphicStalkEquivModelSpace_symm
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (c.extend I x))) :
    toFilterGerm I X x (𝓝 x) le_rfl ((c.holomorphicStalkEquivModelSpace hc x hx e).symm s) =
      (toFilterGerm 𝓘(ℂ, V) V (e (c.extend I x)) (𝓝 (e (c.extend I x))) le_rfl s).compTendsto
        (e ∘ c.extend I) (e.continuous.continuousAt.comp (c.continuousAt_extend hx)).tendsto := by
  simp only [c.holomorphicStalkEquivModelSpace_symm_apply, toFilterGerm_stalkPullback,
    Function.comp_apply]

/-- On function germs, chart comparison is composition with the inverse chart and `e.symm`. -/
@[simp↓]
theorem toFilterGerm_holomorphicStalkEquivModelSpace
    (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    toFilterGerm 𝓘(ℂ, V) V (e (c.extend I x)) (𝓝 (e (c.extend I x))) le_rfl
        (c.holomorphicStalkEquivModelSpace hc x hx e s) =
      (toFilterGerm I X x (𝓝 x) le_rfl s).compTendsto ((c.extend I).symm ∘ e.symm)
        (by
          have he := e.symm.continuous.tendsto (e (c.extend I x))
          rw [e.symm_apply_apply] at he
          simpa only [c.extend_left_inv hx] using
            (c.continuousAt_extend_symm hx).tendsto.comp he) := by
  -- As above, unfold neighborhood membership in the constructor's extracted proofs.
  erw [holomorphicStalkEquivModelSpace,
    toFilterGerm_stalkPullbackEquiv_symm (f := e ∘ c.extend I)
      (g := (c.extend I).symm ∘ e.symm)]

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- For a boundaryless model, chart comparison identifies a holomorphic stalk with a stalk on a
chosen continuously linearly equivalent model space. The choice of `V : Type` also covers
higher-universe manifold models. -/
def stalkEquivModelSpace
    (x : X) (e : E ≃L[ℂ] V) :
    (holomorphicStructureSheaf I X).presheaf.stalk x ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (extChartAt I x x)) :=
  (chartAt H x).holomorphicStalkEquivModelSpace (IsManifold.chart_mem_maximalAtlas x)
    x (mem_chart_source H x) e

/-- The inverse chart comparison is pullback along the chart followed by `e`. -/
theorem stalkEquivModelSpace_symm_apply
    (x : X) (e : E ≃L[ℂ] V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (extChartAt I x x))) :
    (stalkEquivModelSpace x e).symm s =
      stalkPullback (J := 𝓘(ℂ, V)) (f := e ∘ extChartAt I x) (a := x)
        (((chartAt H x).open_source.eventually_mem (mem_chart_source H x)).mono fun _ hy ↦
          e.contDiff.contMDiff.contMDiffAt.comp _ (contMDiffAt_extChartAt' hy)) s :=
  (chartAt H x).holomorphicStalkEquivModelSpace_symm_apply
    (IsManifold.chart_mem_maximalAtlas x) x (mem_chart_source H x) e s

-- Pre-order cancellation is needed here too: post-order RingEquiv simp rules alone do not
-- cancel after simp traverses the chart-dependent stalk types.
/-- Inverse chart comparison cancels chart comparison. -/
@[simp↓]
theorem stalkEquivModelSpace_symm_apply_apply
    (x : X) (e : E ≃L[ℂ] V) (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    (stalkEquivModelSpace x e).symm (stalkEquivModelSpace x e s) = s :=
  (stalkEquivModelSpace x e).symm_apply_apply s

/-- Chart comparison cancels inverse chart comparison. -/
@[simp↓]
theorem stalkEquivModelSpace_apply_symm_apply
    (x : X) (e : E ≃L[ℂ] V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (extChartAt I x x))) :
    stalkEquivModelSpace x e ((stalkEquivModelSpace x e).symm s) = s :=
  (stalkEquivModelSpace x e).apply_symm_apply s

-- Normalize chart comparison before simp expands the extended chart in the stalk's base point.
/-- The inverse chart comparison preserves evaluation. -/
@[simp↓]
theorem eval_stalkEquivModelSpace_symm
    (x : X) (e : E ≃L[ℂ] V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (extChartAt I x x))) :
    eval I X x ((stalkEquivModelSpace x e).symm s) =
      eval 𝓘(ℂ, V) V (e (extChartAt I x x)) s := by
  simp only [stalkEquivModelSpace_symm_apply, eval_stalkPullback, Function.comp_apply]

/-- Chart comparison preserves evaluation. -/
@[simp↓]
theorem eval_stalkEquivModelSpace
    (x : X) (e : E ≃L[ℂ] V) (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    eval 𝓘(ℂ, V) V (e (extChartAt I x x)) (stalkEquivModelSpace x e s) =
      eval I X x s := by
  rw [← eval_stalkEquivModelSpace_symm, RingEquiv.symm_apply_apply]

/-- On function germs, the inverse chart comparison is composition with the chart and `e`. -/
@[simp↓]
theorem toFilterGerm_stalkEquivModelSpace_symm
    (x : X) (e : E ≃L[ℂ] V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk (e (extChartAt I x x))) :
    toFilterGerm I X x (𝓝 x) le_rfl ((stalkEquivModelSpace x e).symm s) =
      (toFilterGerm 𝓘(ℂ, V) V (e (extChartAt I x x))
        (𝓝 (e (extChartAt I x x))) le_rfl s).compTendsto (e ∘ extChartAt I x)
          (e.continuous.continuousAt.comp (continuousAt_extChartAt x)).tendsto := by
  simp only [stalkEquivModelSpace_symm_apply, toFilterGerm_stalkPullback, Function.comp_apply]

/-- On function germs, chart comparison is composition with the inverse chart and `e.symm`. -/
@[simp↓]
theorem toFilterGerm_stalkEquivModelSpace
    (x : X) (e : E ≃L[ℂ] V) (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    toFilterGerm 𝓘(ℂ, V) V (e (extChartAt I x x))
        (𝓝 (e (extChartAt I x x))) le_rfl (stalkEquivModelSpace x e s) =
      (toFilterGerm I X x (𝓝 x) le_rfl s).compTendsto ((extChartAt I x).symm ∘ e.symm)
        (by
          have he := e.symm.continuous.tendsto (e (extChartAt I x x))
          rw [e.symm_apply_apply] at he
          simpa only [extChartAt_to_inv] using
            (continuousAt_extChartAt_symm x).tendsto.comp he) := by
  exact (chartAt H x).toFilterGerm_holomorphicStalkEquivModelSpace
    (IsManifold.chart_mem_maximalAtlas x) x (mem_chart_source H x) e s

omit [IsManifold I ω X] in
/-- A chart at `x`, followed by a linear isomorphism onto a model in `Type`, identifies the
holomorphic stalk at `x` with a holomorphic stalk of a finite-dimensional complex vector space of
the same dimension. -/
theorem exists_ringEquiv_stalk_modelSpace [FiniteDimensional ℂ E] [IsManifold I 1 X] (x : X) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V) (_ : FiniteDimensional ℂ V)
      (v : V), Module.finrank ℂ V = Module.finrank ℂ E ∧
        Nonempty ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk v ≃+*
          (holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  -- The model `E` may live in any universe, while the stalks of model spaces are compared in
  -- `Type`: compose the chart at `x` with a linear isomorphism onto a space in `Type`.
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact ⟨Fin (Module.finrank ℂ E) → ℂ, inferInstance, inferInstance, inferInstance,
    e (extChartAt I x x), by simp, ⟨(stalkEquivModelSpace x e).symm⟩⟩

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

namespace TauCeti.holomorphicStructureSheaf

/-- An isomorphism-invariant property of commutative rings holds for every holomorphic stalk of
`Fin n → ℂ` as soon as it holds for `ℂ` and passes, for every `n : ℕ`, from the holomorphic stalks
of `Fin n → ℂ` to the holomorphic stalk of `(Fin n → ℂ) × ℂ` at `(0, 0)`. -/
theorem stalk_induction_modelSpace (P : ∀ (R : Type) [CommRing R], Prop)
    (hequiv : ∀ {A B : Type} [CommRing A] [CommRing B], (A ≃+* B) → P A → P B)
    (h₀ : P ℂ)
    (hprod : ∀ n : ℕ,
      (∀ x : Fin n → ℂ,
        P ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk x)) →
      P ((holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ)
        ((Fin n → ℂ) × ℂ)).presheaf.stalk (0, 0)))
    (n : ℕ) (y : Fin n → ℂ) :
    P ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk y) := by
  induction n with
  | zero =>
    exact hequiv
      (evalEquivOfNhdsEqPure 𝓘(ℂ, Fin 0 → ℂ) (congrFun (nhds_discrete _) y)).symm h₀
  | succ n ih =>
    let e : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin n → ℂ) × ℂ :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    let f : (Fin (n + 1) → ℂ) → (Fin n → ℂ) × ℂ := fun z ↦ e (z - y)
    let g : (Fin n → ℂ) × ℂ → Fin (n + 1) → ℂ := fun w ↦ e.symm w + y
    have hf : ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, (Fin n → ℂ) × ℂ) ω f :=
      (by fun_prop : ContDiff ℂ ω f).contMDiff
    have hg : ContMDiff 𝓘(ℂ, (Fin n → ℂ) × ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω g :=
      (by fun_prop : ContDiff ℂ ω g).contMDiff
    have hfy : f y = (0, 0) := by simp [f, Prod.mk_zero_zero]
    have hbij := stalkPullback_bijective (I := 𝓘(ℂ, Fin (n + 1) → ℂ))
      (J := 𝓘(ℂ, (Fin n → ℂ) × ℂ)) (a := y)
      (Eventually.of_forall fun _ ↦ hf.contMDiffAt)
      (Eventually.of_forall fun _ ↦ hg.contMDiffAt)
      (Eventually.of_forall fun z ↦ by simp [f, g])
      (Eventually.of_forall fun w ↦ by simp [f, g])
    exact hequiv ((RingEquiv.cast (R := fun p ↦
        (holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ) ((Fin n → ℂ) × ℂ)).presheaf.stalk p)
        hfy.symm).trans (RingEquiv.ofBijective _ hbij))
      (hprod n ih)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- An isomorphism-invariant property of commutative rings holds for every holomorphic stalk of a
finite-dimensional complex manifold without boundary as soon as it holds for `ℂ` and passes, for
every `n : ℕ`, from the holomorphic stalks of `Fin n → ℂ` to the holomorphic stalk of
`(Fin n → ℂ) × ℂ` at `(0, 0)`. -/
theorem stalk_induction (P : ∀ (R : Type) [CommRing R], Prop)
    (hequiv : ∀ {A B : Type} [CommRing A] [CommRing B], (A ≃+* B) → P A → P B)
    (h₀ : P ℂ)
    (hprod : ∀ n : ℕ,
      (∀ x : Fin n → ℂ,
        P ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk x)) →
      P ((holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ)
        ((Fin n → ℂ) × ℂ)).presheaf.stalk (0, 0)))
    (x : X) :
    P ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let e : E ≃L[ℂ] Fin (Module.finrank ℂ E) → ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact hequiv (stalkEquivModelSpace x e).symm
    (stalk_induction_modelSpace P hequiv h₀ hprod (Module.finrank ℂ E) (e (extChartAt I x x)))

end TauCeti.holomorphicStructureSheaf
