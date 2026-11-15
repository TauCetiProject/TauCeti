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
near the chosen point, and `stalkPullbackOfEq` handles an explicit target-point identification
`f a = b`. Unlike the sheaf morphism `stalkPrecomp`, this requires no globally holomorphic
extension of the map. Equality, evaluation and composition are characterized through the injective
comparison with function germs. The two pullbacks agree when both apply.
Pullback along a map with a local analytic inverse, such as a chart, is bijective
(`stalkPullback_bijective`, `stalkPullbackOfEq_bijective`), in particular pullback along a
continuous linear equivalence (`ContinuousLinearEquiv.holomorphicStalkPullback_bijective`, packaged
as the ring equivalence `ContinuousLinearEquiv.holomorphicStalkEquiv` and its centered automorphism
form `ContinuousLinearEquiv.holomorphicStalkCenteredEquiv` along `y ↦ x + e (y - x)`) and along a
chart followed by one (`stalkPullback_comp_extChartAt_bijective`), which identifies a stalk of a
manifold with a stalk of its model.
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

/-- Pullback of holomorphic germs along a map analytic near `a` sending `a` to `b`. -/
def stalkPullbackOfEq {b : Y} (hfa : f a = b) :
    (holomorphicStructureSheaf J Y).presheaf.stalk b →+*
      (holomorphicStructureSheaf I X).presheaf.stalk a :=
  hfa ▸ stalkPullback hf

/-- At `b = f a`, `stalkPullbackOfEq` is `stalkPullback`. -/
@[simp]
theorem stalkPullbackOfEq_rfl : stalkPullbackOfEq hf rfl = stalkPullback hf :=
  (rfl)

/-- The function germ of `stalkPullbackOfEq` is composition of the function germ with `f`. -/
@[simp]
theorem toFilterGerm_stalkPullbackOfEq {b : Y} (hfa : f a = b)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk b) :
    toFilterGerm I X a (𝓝 a) le_rfl (stalkPullbackOfEq hf hfa s) =
      (toFilterGerm J Y b (𝓝 b) le_rfl s).compTendsto f
        (hfa ▸ hf.self_of_nhds.continuousAt.tendsto) := by
  subst hfa
  exact toFilterGerm_stalkPullback hf s

/-- Pullbacks along maps that agree near `a` are equal. -/
theorem stalkPullbackOfEq_congr {f' : X → Y} (hf' : ∀ᶠ y in 𝓝 a, ContMDiffAt I J ω f' y)
    {b : Y} (hfa : f a = b) (hfa' : f' a = b) (hff' : f =ᶠ[𝓝 a] f') :
    stalkPullbackOfEq hf hfa = stalkPullbackOfEq hf' hfa' := by
  ext s
  apply toFilterGerm_nhds_injective a
  rw [toFilterGerm_stalkPullbackOfEq, toFilterGerm_stalkPullbackOfEq]
  refine Germ.inductionOn (toFilterGerm J Y b (𝓝 b) le_rfl s) fun φ ↦ ?_
  rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
  exact Germ.coe_eq.mpr (hff'.fun_comp φ)

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

/-- `stalkPullbackOfEq` preserves the value of a holomorphic germ. -/
@[simp]
theorem eval_stalkPullbackOfEq {b : Y} (hfa : f a = b)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk b) :
    eval I X a (stalkPullbackOfEq hf hfa s) = eval J Y b s := by
  subst hfa
  exact eval_stalkPullback hf s

/-- Local analytic pullback is a local ring homomorphism. -/
instance isLocalHom_stalkPullback : IsLocalHom (stalkPullback hf) where
  map_nonunit s hs := (isUnit_stalk_iff J Y s).mpr (by
    simpa only [eval_stalkPullback] using ((isUnit_stalk_iff I X _).mp hs))

/-- `stalkPullbackOfEq` is a local ring homomorphism. -/
instance isLocalHom_stalkPullbackOfEq {b : Y} (hfa : f a = b) :
    IsLocalHom (stalkPullbackOfEq hf hfa) := by
  subst hfa
  exact isLocalHom_stalkPullback hf

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

/-- `stalkPullbackOfEq` along a composite is the composite of the `stalkPullbackOfEq` maps, in
reverse order. -/
theorem stalkPullbackOfEq_comp {b : Y} {c : Z} {g : Y → Z} (hfa : f a = b)
    (hg : ∀ᶠ y in 𝓝 b, ContMDiffAt J K ω g y) (hgb : g b = c)
    (hgf : ∀ᶠ y in 𝓝 a, ContMDiffAt I K ω (g ∘ f) y :=
      (hf.and ((hfa ▸ hf.self_of_nhds.continuousAt.tendsto).eventually hg)).mono
        fun z hz ↦ hz.2.comp z hz.1)
    (hgfa : (g ∘ f) a = c := (congrArg g hfa).trans hgb) :
    stalkPullbackOfEq hgf hgfa = (stalkPullbackOfEq hf hfa).comp (stalkPullbackOfEq hg hgb) := by
  subst hfa hgb
  ext s
  rw [stalkPullbackOfEq_congr hgf
    ((hf.and (hf.self_of_nhds.continuousAt.tendsto.eventually hg)).mono
      fun z hz ↦ hz.2.comp z hz.1) hgfa rfl EventuallyEq.rfl,
    stalkPullbackOfEq_rfl, stalkPullbackOfEq_rfl, stalkPullbackOfEq_rfl, RingHom.comp_apply]
  exact stalkPullback_comp hf hg s

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

/-- `stalkPullbackOfEq` along a map with a local analytic inverse near `a` sending `a` to `b` is
bijective. -/
theorem stalkPullbackOfEq_bijective {b : Y} (hfa : f a = b) {g : Y → X}
    (hg : ∀ᶠ y in 𝓝 b, ContMDiffAt J I ω g y)
    (hgf : ∀ᶠ x in 𝓝 a, g (f x) = x) (hfg : ∀ᶠ y in 𝓝 b, f (g y) = y) :
    Function.Bijective (stalkPullbackOfEq hf hfa) := by
  subst hfa
  exact stalkPullback_bijective hf hg hgf hfg

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

open TauCeti TauCeti.holomorphicStructureSheaf

variable {V W U : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- Pullback along a continuous linear equivalence is bijective on holomorphic stalks. -/
theorem holomorphicStalkPullback_bijective (e : V ≃L[ℂ] W) (x : V) :
    Function.Bijective (stalkPullback (I := 𝓘(ℂ, V)) (J := 𝓘(ℂ, W)) (a := x)
      (Eventually.of_forall fun _ ↦ e.contDiff.contMDiff.contMDiffAt)) :=
  stalkPullback_bijective _ (Eventually.of_forall fun _ ↦ e.symm.contDiff.contMDiff.contMDiffAt)
    (Eventually.of_forall e.symm_apply_apply) (Eventually.of_forall e.apply_symm_apply)

/-- The contravariant ring equivalence on holomorphic stalks induced by pullback along a continuous
linear equivalence `e : V ≃L[ℂ] W`. -/
def holomorphicStalkEquiv (e : V ≃L[ℂ] W) (x : V) :
    (holomorphicStructureSheaf 𝓘(ℂ, W) W).presheaf.stalk (e x) ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x :=
  RingEquiv.ofBijective _ (e.holomorphicStalkPullback_bijective x)

/-- `holomorphicStalkEquiv` acts by `stalkPullback` along `e`. -/
theorem holomorphicStalkEquiv_apply (e : V ≃L[ℂ] W) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, W) W).presheaf.stalk (e x)) :
    e.holomorphicStalkEquiv x s =
      stalkPullback (I := 𝓘(ℂ, V)) (J := 𝓘(ℂ, W)) (a := x)
        (Eventually.of_forall fun _ ↦ e.contDiff.contMDiff.contMDiffAt) s := by
  rw [holomorphicStalkEquiv, RingEquiv.ofBijective_apply]

/-- `(e.holomorphicStalkEquiv x).symm` acts by `stalkPullbackOfEq` along `e.symm`. -/
theorem holomorphicStalkEquiv_symm_apply (e : V ≃L[ℂ] W) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) :
    (e.holomorphicStalkEquiv x).symm s =
      stalkPullbackOfEq (I := 𝓘(ℂ, W)) (J := 𝓘(ℂ, V)) (f := e.symm) (a := e x)
        (Eventually.of_forall fun _ ↦ e.symm.contDiff.contMDiff.contMDiffAt)
        (e.symm_apply_apply x) s := by
  rw [RingEquiv.symm_apply_eq, holomorphicStalkEquiv_apply, ← stalkPullbackOfEq_rfl,
    ← RingHom.comp_apply, ← stalkPullbackOfEq_comp,
    stalkPullbackOfEq_congr _ (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := 𝓘(ℂ, V)))
      _ rfl (Eventually.of_forall e.symm_apply_apply),
    stalkPullbackOfEq_rfl, stalkPullback_id]
  exact (RingHom.id_apply s).symm

/-- The function germ of `e.holomorphicStalkEquiv x s` is composition of the function germ of `s`
with `e`. -/
@[simp]
theorem toFilterGerm_holomorphicStalkEquiv (e : V ≃L[ℂ] W) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, W) W).presheaf.stalk (e x)) :
    toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl (e.holomorphicStalkEquiv x s) =
      (toFilterGerm 𝓘(ℂ, W) W (e x) (𝓝 (e x)) le_rfl s).compTendsto e
        (e.continuous.tendsto x) := by
  rw [holomorphicStalkEquiv_apply, toFilterGerm_stalkPullback]

/-- The function germ of `(e.holomorphicStalkEquiv x).symm s` is composition of the function germ
of `s` with `e.symm`. -/
@[simp]
theorem toFilterGerm_holomorphicStalkEquiv_symm (e : V ≃L[ℂ] W) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) :
    toFilterGerm 𝓘(ℂ, W) W (e x) (𝓝 (e x)) le_rfl ((e.holomorphicStalkEquiv x).symm s) =
      (toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl s).compTendsto e.symm
        (by simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e x)) := by
  rw [holomorphicStalkEquiv_symm_apply, toFilterGerm_stalkPullbackOfEq]

/-- If `F` represents the holomorphic germ `s` at `e x`, then `F ∘ e` represents
`e.holomorphicStalkEquiv x s` at `x`. -/
theorem toFilterGerm_holomorphicStalkEquiv_of_eq (e : V ≃L[ℂ] W) {x : V}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, W) W).presheaf.stalk (e x)} {F : W → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, W) W (e x) (𝓝 (e x)) le_rfl s = F) :
    toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl (e.holomorphicStalkEquiv x s) =
      (F ∘ e : V → ℂ) := by
  rw [toFilterGerm_holomorphicStalkEquiv, hs, Germ.coe_compTendsto]

/-- If `F` represents the holomorphic germ `s` at `x`, then `F ∘ e.symm` represents
`(e.holomorphicStalkEquiv x).symm s` at `e x`. -/
theorem toFilterGerm_holomorphicStalkEquiv_symm_of_eq (e : V ≃L[ℂ] W) {x : V}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x} {F : V → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl s = F) :
    toFilterGerm 𝓘(ℂ, W) W (e x) (𝓝 (e x)) le_rfl ((e.holomorphicStalkEquiv x).symm s) =
      (F ∘ e.symm : W → ℂ) := by
  rw [toFilterGerm_holomorphicStalkEquiv_symm, hs, Germ.coe_compTendsto]

/-- `holomorphicStalkEquiv` preserves evaluation at the base point. -/
@[simp]
theorem eval_holomorphicStalkEquiv (e : V ≃L[ℂ] W) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, W) W).presheaf.stalk (e x)) :
    eval 𝓘(ℂ, V) V x (e.holomorphicStalkEquiv x s) = eval 𝓘(ℂ, W) W (e x) s := by
  rw [holomorphicStalkEquiv_apply, eval_stalkPullback]

/-- `(e.holomorphicStalkEquiv x).symm` preserves evaluation at the base point. -/
@[simp]
theorem eval_holomorphicStalkEquiv_symm (e : V ≃L[ℂ] W) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) :
    eval 𝓘(ℂ, W) W (e x) ((e.holomorphicStalkEquiv x).symm s) = eval 𝓘(ℂ, V) V x s := by
  rw [holomorphicStalkEquiv_symm_apply, eval_stalkPullbackOfEq]

/-- Pullback along the identity continuous linear equivalence is the identity ring equivalence. -/
@[simp]
theorem holomorphicStalkEquiv_refl (x : V) :
    (ContinuousLinearEquiv.refl ℂ V).holomorphicStalkEquiv x = RingEquiv.refl _ := by
  refine RingEquiv.ext fun s ↦
    (((ContinuousLinearEquiv.refl ℂ V).holomorphicStalkEquiv_apply x s).trans ?_).trans
      (RingEquiv.refl_apply _ s).symm
  have h := (stalkPullbackOfEq_congr (b := x)
    (Eventually.of_forall fun _ ↦
      (ContinuousLinearEquiv.refl ℂ V).contDiff.contMDiff.contMDiffAt)
    (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := 𝓘(ℂ, V)))
    rfl rfl (Eventually.of_forall fun _ ↦ rfl)).trans
    ((stalkPullbackOfEq_rfl _).trans (stalkPullback_id x))
  exact (DFunLike.congr_fun h s).trans (RingHom.id_apply s)

/-- `holomorphicStalkEquiv` is contravariant with respect to composition of continuous linear
equivalences. -/
@[simp]
theorem holomorphicStalkEquiv_trans (e : V ≃L[ℂ] W) (e' : W ≃L[ℂ] U) (x : V) :
    (e.trans e').holomorphicStalkEquiv x =
      (e'.holomorphicStalkEquiv (e x)).trans (e.holomorphicStalkEquiv x) :=
  RingEquiv.ext fun s ↦
    ((e.trans e').holomorphicStalkEquiv_apply x s).trans <|
      (stalkPullback_comp
        (Eventually.of_forall fun _ ↦ e.contDiff.contMDiff.contMDiffAt)
        (Eventually.of_forall fun _ ↦ e'.contDiff.contMDiff.contMDiffAt) s).trans <|
        ((e.holomorphicStalkEquiv_apply x _).symm.trans
          (congrArg (e.holomorphicStalkEquiv x)
            (e'.holomorphicStalkEquiv_apply (e x) s).symm)).trans
          (RingEquiv.trans_apply (e'.holomorphicStalkEquiv (e x))
            (e.holomorphicStalkEquiv x) s).symm

private def holomorphicStalkCenteredHom (e : V ≃L[ℂ] V) (x : V) :
    (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x →+*
      (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x :=
  stalkPullbackOfEq (I := 𝓘(ℂ, V)) (J := 𝓘(ℂ, V)) (f := fun y ↦ x + e (y - x)) (a := x)
    (Eventually.of_forall fun _ ↦
      (contDiff_const.add (e.contDiff.comp (contDiff_id.sub contDiff_const))).contMDiff.contMDiffAt)
    (by simp)

private theorem holomorphicStalkCenteredHom_refl (x : V) :
    (ContinuousLinearEquiv.refl ℂ V).holomorphicStalkCenteredHom x = RingHom.id _ := by
  rw [holomorphicStalkCenteredHom,
    stalkPullbackOfEq_congr _ (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := 𝓘(ℂ, V)))
      _ rfl (Eventually.of_forall fun y ↦ by simp),
    stalkPullbackOfEq_rfl, stalkPullback_id]
  rfl

private theorem holomorphicStalkCenteredHom_trans (e e' : V ≃L[ℂ] V) (x : V) :
    (e.trans e').holomorphicStalkCenteredHom x =
      (e.holomorphicStalkCenteredHom x).comp (e'.holomorphicStalkCenteredHom x) := by
  rw [holomorphicStalkCenteredHom, holomorphicStalkCenteredHom, holomorphicStalkCenteredHom,
    ← stalkPullbackOfEq_comp]
  exact stalkPullbackOfEq_congr _ _ _ _ (Eventually.of_forall fun y ↦ by simp)

private theorem holomorphicStalkCenteredHom_comp_symm (e : V ≃L[ℂ] V) (x : V) :
    (e.holomorphicStalkCenteredHom x).comp (e.symm.holomorphicStalkCenteredHom x) =
      RingHom.id _ := by
  rw [← holomorphicStalkCenteredHom_trans, e.self_trans_symm, holomorphicStalkCenteredHom_refl]

private theorem holomorphicStalkCenteredHom_symm_comp (e : V ≃L[ℂ] V) (x : V) :
    (e.symm.holomorphicStalkCenteredHom x).comp (e.holomorphicStalkCenteredHom x) =
      RingHom.id _ := by
  rw [← holomorphicStalkCenteredHom_trans, e.symm_trans_self, holomorphicStalkCenteredHom_refl]

/-- The ring automorphism of the holomorphic stalk at `x : V` induced by pullback along the
centered affine automorphism `y ↦ x + e (y - x)`. -/
def holomorphicStalkCenteredEquiv (e : V ≃L[ℂ] V) (x : V) :
    (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x :=
  RingEquiv.ofRingHom (e.holomorphicStalkCenteredHom x) (e.symm.holomorphicStalkCenteredHom x)
    (e.holomorphicStalkCenteredHom_comp_symm x) (e.holomorphicStalkCenteredHom_symm_comp x)

/-- `holomorphicStalkCenteredEquiv` acts by `stalkPullbackOfEq` along the centered affine map
`y ↦ x + e (y - x)`. -/
theorem holomorphicStalkCenteredEquiv_apply (e : V ≃L[ℂ] V) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) :
    e.holomorphicStalkCenteredEquiv x s =
      stalkPullbackOfEq (I := 𝓘(ℂ, V)) (J := 𝓘(ℂ, V)) (f := fun y ↦ x + e (y - x)) (a := x)
        (Eventually.of_forall fun _ ↦
          (contDiff_const.add
            (e.contDiff.comp (contDiff_id.sub contDiff_const))).contMDiff.contMDiffAt)
        (by simp) s := by
  rw [holomorphicStalkCenteredEquiv, RingEquiv.ofRingHom_apply, holomorphicStalkCenteredHom]

/-- The function germ of `e.holomorphicStalkCenteredEquiv x s` is composition of the function germ
of `s` with the centered affine map `y ↦ x + e (y - x)`. -/
@[simp]
theorem toFilterGerm_holomorphicStalkCenteredEquiv (e : V ≃L[ℂ] V) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) :
    toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl (e.holomorphicStalkCenteredEquiv x s) =
      (toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl s).compTendsto (fun y ↦ x + e (y - x))
        (by
          have : Continuous fun y : V ↦ x + e (y - x) := by fun_prop
          simpa using this.tendsto x) := by
  rw [holomorphicStalkCenteredEquiv_apply, toFilterGerm_stalkPullbackOfEq]

/-- If `F` represents the holomorphic germ `s` at `x`, then `y ↦ F (x + e (y - x))` represents
`e.holomorphicStalkCenteredEquiv x s`. -/
theorem toFilterGerm_holomorphicStalkCenteredEquiv_of_eq (e : V ≃L[ℂ] V) {x : V}
    {s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x} {F : V → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl s = F) :
    toFilterGerm 𝓘(ℂ, V) V x (𝓝 x) le_rfl (e.holomorphicStalkCenteredEquiv x s) =
      (fun y ↦ F (x + e (y - x)) : V → ℂ) := by
  rw [toFilterGerm_holomorphicStalkCenteredEquiv, hs, Germ.coe_compTendsto]
  rfl

/-- `holomorphicStalkCenteredEquiv` preserves evaluation at `x`. -/
@[simp]
theorem eval_holomorphicStalkCenteredEquiv (e : V ≃L[ℂ] V) (x : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) :
    eval 𝓘(ℂ, V) V x (e.holomorphicStalkCenteredEquiv x s) = eval 𝓘(ℂ, V) V x s := by
  rw [holomorphicStalkCenteredEquiv_apply, eval_stalkPullbackOfEq]

/-- Centered pullback along the identity continuous linear equivalence is the identity ring
automorphism. -/
@[simp]
theorem holomorphicStalkCenteredEquiv_refl (x : V) :
    (ContinuousLinearEquiv.refl ℂ V).holomorphicStalkCenteredEquiv x = RingEquiv.refl _ := by
  ext s
  rw [holomorphicStalkCenteredEquiv, RingEquiv.ofRingHom_apply, holomorphicStalkCenteredHom_refl,
    RingHom.id_apply, RingEquiv.refl_apply]

/-- The inverse of `e.holomorphicStalkCenteredEquiv x` is
`e.symm.holomorphicStalkCenteredEquiv x`. -/
@[simp]
theorem holomorphicStalkCenteredEquiv_symm (e : V ≃L[ℂ] V) (x : V) :
    (e.holomorphicStalkCenteredEquiv x).symm = e.symm.holomorphicStalkCenteredEquiv x := by
  simp [holomorphicStalkCenteredEquiv]

/-- `holomorphicStalkCenteredEquiv` is contravariant with respect to composition of continuous
linear equivalences. -/
@[simp]
theorem holomorphicStalkCenteredEquiv_trans (e e' : V ≃L[ℂ] V) (x : V) :
    (e.trans e').holomorphicStalkCenteredEquiv x =
      (e'.holomorphicStalkCenteredEquiv x).trans (e.holomorphicStalkCenteredEquiv x) := by
  ext s
  rw [RingEquiv.trans_apply, holomorphicStalkCenteredEquiv, holomorphicStalkCenteredEquiv,
    holomorphicStalkCenteredEquiv, RingEquiv.ofRingHom_apply, RingEquiv.ofRingHom_apply,
    RingEquiv.ofRingHom_apply, holomorphicStalkCenteredHom_trans, RingHom.comp_apply]

end ContinuousLinearEquiv
