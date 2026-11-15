/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import TauCeti.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Order.Filter.Germ

/-!
# Pullback of holomorphic stalks by local analytic maps

`stalkPullback` pulls back holomorphic germs along a map between complex manifolds analytic
near the chosen point, with `ℂ`-algebra homomorphism upgrade `stalkPullbackAlgHom` and
base-point-explicit form `stalkPullbackAt` (whose domain stalk at `y` is decoupled from `f x` via
an explicit equality `f x = y`, enabling congruence `stalkPullbackAt_congr` across locally equal
maps). Unlike the sheaf morphism `stalkPrecomp`, this requires no globally holomorphic extension of
the map. Equality, evaluation, `ℂ`-linearity, and composition are characterized through the
injective comparison with function germs. The two pullbacks agree when both apply.
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
    (eventually_contMDiffAt_comp hu hf rfl)
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
  obtain ⟨t, ht⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt
    (eventually_contMDiffAt_comp hu hg hgf.self_of_nhds)
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

/-- Local analytic pullback on stalks fixes `ℂ`-scalars. -/
@[simp]
theorem stalkPullback_algebraMap (c : ℂ) :
    stalkPullback hf (algebraMap ℂ _ c) = algebraMap ℂ _ c :=
  toFilterGerm_nhds_injective a <| by
    rw [toFilterGerm_stalkPullback, toFilterGerm_algebraMap, toFilterGerm_algebraMap,
      Germ.algebraMap_eq, Germ.algebraMap_eq, Germ.coe_compTendsto, Function.comp_def]

/-- Local analytic pullback on stalks, bundled as a `ℂ`-algebra homomorphism. -/
def stalkPullbackAlgHom :
    (holomorphicStructureSheaf J Y).presheaf.stalk (f a) →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk a where
  __ := stalkPullback hf
  commutes' := stalkPullback_algebraMap hf

/-- Coercing `stalkPullbackAlgHom` to a ring homomorphism recovers `stalkPullback`. -/
@[simp]
theorem toRingHom_stalkPullbackAlgHom :
    (stalkPullbackAlgHom hf :
      (holomorphicStructureSheaf J Y).presheaf.stalk (f a) →+*
        (holomorphicStructureSheaf I X).presheaf.stalk a) = stalkPullback hf := (rfl)

/-- `stalkPullbackAlgHom` acts on germs by `stalkPullback`. -/
@[simp]
theorem stalkPullbackAlgHom_apply
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f a)) :
    stalkPullbackAlgHom hf s = stalkPullback hf s := (rfl)

/-- On globally analytic maps, local pullback is the structure-sheaf stalk map. -/
theorem stalkPullback_eq_stalkPrecomp (f : X → Y) (hf : ContMDiff I J ω f) (a : X) :
    stalkPullback (Eventually.of_forall fun _ ↦ hf.contMDiffAt) =
      stalkPrecomp I X f hf a := by
  ext s
  apply toFilterGerm_nhds_injective a
  rw [toFilterGerm_stalkPullback, toFilterGerm_stalkPrecomp]

/-- On a globally analytic map, `stalkPullbackAlgHom` agrees with `stalkPrecompAlgHom`. -/
theorem stalkPullbackAlgHom_eq_stalkPrecompAlgHom (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    stalkPullbackAlgHom (Eventually.of_forall fun _ ↦ hf.contMDiffAt) =
      stalkPrecompAlgHom I X f hf x :=
  AlgHom.ext fun s ↦ by
    rw [stalkPullbackAlgHom_apply, stalkPrecompAlgHom_apply, stalkPullback_eq_stalkPrecomp]

/-- Pullback by the identity fixes every germ. -/
@[simp]
theorem stalkPullback_id (a : X) :
    stalkPullback (I := I) (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := I))
      (a := a) = RingHom.id _ := by
  rw [stalkPullback_eq_stalkPrecomp id contMDiff_id a, stalkPrecomp_id]

/-- Pullback along `fun y ↦ y` is the identity `ℂ`-algebra homomorphism on the stalk. -/
@[simp]
theorem stalkPullbackAlgHom_id (x : X) :
    stalkPullbackAlgHom (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := I) :
        ∀ᶠ w in 𝓝 x, ContMDiffAt I I ω (fun y : X ↦ y) w) =
      AlgHom.id ℂ ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  AlgHom.ext fun s ↦ by simp [stalkPullbackAlgHom_apply]

/-! ### Base-point-explicit local analytic pullback -/

/-- Pullback of holomorphic germs from `y` to `x` along a map `f` analytic near `x` with explicit
image hypothesis `f x = y`. Keeping `y` independent of `f x` in the domain type allows two locally
equal maps `f₁ =ᶠ[𝓝 x] f₂` to induce literally equal `ℂ`-algebra homomorphisms
(`stalkPullbackAt_congr`). -/
def stalkPullbackAt {y : Y} (hfx : f a = y) :
    (holomorphicStructureSheaf J Y).presheaf.stalk y →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk a :=
  hfx ▸ stalkPullbackAlgHom hf

/-- The function germ of `stalkPullbackAt hf hfx s` is composition of the function germ of `s`
with `f`. -/
@[simp]
theorem toFilterGerm_stalkPullbackAt {y : Y} (hfx : f a = y)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk y) :
    toFilterGerm I X a (𝓝 a) le_rfl (stalkPullbackAt hf hfx s) =
      (toFilterGerm J Y y (𝓝 y) le_rfl s).compTendsto f
        (hfx ▸ hf.self_of_nhds.continuousAt.tendsto) := by
  subst hfx; exact toFilterGerm_stalkPullback hf s

/-- At `y = f x`, `stalkPullbackAt` agrees with `stalkPullbackAlgHom`. -/
@[simp]
theorem stalkPullbackAt_rfl : stalkPullbackAt hf rfl = stalkPullbackAlgHom hf := (rfl)

/-- Locally equal analytic maps induce the same `ℂ`-algebra homomorphism on stalks. -/
theorem stalkPullbackAt_congr {f₁ f₂ : X → Y} {x : X} {y : Y}
    (hf₁ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₁ w) (hfx₁ : f₁ x = y)
    (hf₂ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₂ w) (hfx₂ : f₂ x = y) (h : f₁ =ᶠ[𝓝 x] f₂) :
    stalkPullbackAt hf₁ hfx₁ = stalkPullbackAt hf₂ hfx₂ :=
  AlgHom.ext fun s ↦ toFilterGerm_nhds_injective x <| by
    obtain ⟨u, -, hus⟩ := exists_toFilterGerm_eq y s
    rw [toFilterGerm_stalkPullbackAt, toFilterGerm_stalkPullbackAt, hus,
      Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq]
    exact h.mono fun w hw ↦ congrArg u hw

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- Pullback by a composite is the composite of the pullbacks, in reverse order. -/
theorem stalkPullback_comp {g : Y → Z} (hg : ∀ᶠ y in 𝓝 (f a), ContMDiffAt J K ω g y)
    (s : (holomorphicStructureSheaf K Z).presheaf.stalk (g (f a))) :
    stalkPullback (eventually_contMDiffAt_comp hg hf rfl) s =
      stalkPullback hf (stalkPullback hg s) := by
  apply toFilterGerm_nhds_injective a
  simp only [toFilterGerm_stalkPullback]
  exact Germ.inductionOn
    (toFilterGerm K Z (g (f a)) (𝓝 (g (f a))) le_rfl s) fun _ ↦ rfl

/-- Pullback along a composite of locally analytic maps is the reverse composite of their
`ℂ`-algebra stalk pullbacks. -/
theorem stalkPullbackAlgHom_comp {g : Y → Z} {f : X → Y} {x : X}
    (hg : ∀ᶠ v in 𝓝 (f x), ContMDiffAt J K ω g v) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) :
    stalkPullbackAlgHom (eventually_contMDiffAt_comp hg hf rfl) =
      (stalkPullbackAlgHom hf).comp (stalkPullbackAlgHom hg) :=
  AlgHom.ext (stalkPullback_comp hf hg)

/-- Pullback along a composite of locally analytic maps with explicit base points is the reverse
composite of their `ℂ`-algebra stalk pullbacks. -/
theorem stalkPullbackAt_comp {g : Y → Z} {f : X → Y} {x : X} {y : Y} {z : Z}
    (hg : ∀ᶠ v in 𝓝 y, ContMDiffAt J K ω g v) (hgy : g y = z)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    stalkPullbackAt (eventually_contMDiffAt_comp hg hf hfx) ((congrArg g hfx).trans hgy) =
      (stalkPullbackAt hf hfx).comp (stalkPullbackAt hg hgy) := by
  subst hfx hgy; exact stalkPullbackAlgHom_comp hg hf

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
