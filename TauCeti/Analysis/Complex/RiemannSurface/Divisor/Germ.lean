/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf
public import TauCeti.Analysis.Meromorphic.OrderFiltration
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Coordinate germs of divisor sections

Local divisor sections are normalized to zero at permitted poles. This file compares them
with meromorphic coordinate germs, whose values at their centre are discarded. The comparison
is linear, satisfies the divisor order bound, and commutes with restriction and native divisor
inclusions despite their normalization of newly permitted poles.

The local divisor-section condition persists on a neighbourhood. Every meromorphic function
satisfying its order bound has a normalized representative at the centre: allowed poles are
pinned to zero, and otherwise the removable singularity is filled holomorphically. Two normalized
representatives of the same punctured germ have the same full germ.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§1 and16.
-/

public noncomputable section

open CategoryTheory Filter IsManifold Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

section LocalSections

variable [IsManifold 𝓘(ℂ) 1 X] {D : WeilDivisor X} {f : X → ℂ} {x : X}

/-- The local divisor-section predicate holds throughout some neighbourhood. -/
theorem IsDivisorSectionAt.eventually (hf : IsDivisorSectionAt D f x) :
    ∀ᶠ y in 𝓝 x, IsDivisorSectionAt D f y := by
  have := ChartedSpace.t1Space ℂ X
  have hp : ∀ᶠ y in 𝓝[≠] x, IsDivisorSectionAt D f y := by
    filter_upwards [hf.meromorphicAt.eventually_contMDiffAt, D.eventually_eq_zero_nhdsNE x]
      with y hy hD
    exact (isDivisorSectionAt_iff_of_eq_zero hD).2 hy
  rw [eventually_nhdsWithin_iff] at hp
  filter_upwards [hp] with y hy
  by_cases h : y = x
  · simpa only [h] using hf
  · exact hy h


/-- Every meromorphic germ satisfying the order bound has a normalized local divisor-section
representative. At an allowed pole its centre value is set to zero; otherwise removability
supplies the holomorphic centre value. -/
theorem exists_isDivisorSectionAt (hf : MeromorphicAt f x)
    (hord : ((-D x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f x) :
    ∃ g : X → ℂ, IsDivisorSectionAt D g x ∧ f =ᶠ[𝓝[≠] x] g := by
  classical
  have := ChartedSpace.t1Space ℂ X
  rcases lt_or_ge 0 (D x) with hD | hD
  · have heq := Function.update_eventuallyEq_nhdsNE f x x 0
    refine ⟨Function.update f x 0, ?_, heq.symm⟩
    exact
    { meromorphicAt := hf.congr heq.symm
      neg_le_meromorphicOrderAt := by rwa [meromorphicOrderAt_congr heq]
      contMDiffAt := fun h ↦ False.elim (not_le_of_gt hD h)
      apply_eq_zero := fun _ ↦ by simp }
  · have : IsManifold 𝓘(ℂ) ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
    have hn : (0 : WithTop ℤ) ≤ meromorphicOrderAt f x :=
      (by exact_mod_cast neg_nonneg.2 hD : (0 : WithTop ℤ) ≤ (-D x : ℤ)).trans hord
    have hnc : (0 : WithTop ℤ) ≤ _root_.meromorphicOrderAt
        (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
      simpa only [meromorphicOrderAt_def] using hn
    obtain ⟨g, hg, heq⟩ :=
      (((meromorphicAt_def _ _).1 hf).meromorphicOrderAt_nonneg_iff).1 hnc
    have heq' : f =ᶠ[𝓝[≠] x] g ∘ chartAt ℂ x := by
      filter_upwards [(tendsto_chartAt_nhdsNE x).eventually heq,
        nhdsWithin_le_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))]
        with y hy hys
      simpa only [Function.comp_apply, (chartAt ℂ x).left_inv hys] using hy
    have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ chartAt ℂ x) x := by
      apply (contMDiffAt_omega_iff_analyticAt_of_mem_maximalAtlas
        (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)).2
      apply hg.congr
      filter_upwards [(chartAt ℂ x).open_target.mem_nhds
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with z hz
      -- Composition with the chart inverse exposes the two scalar function values.
      change g z = g (chartAt ℂ x ((chartAt ℂ x).symm z))
      rw [(chartAt ℂ x).right_inv hz]
    refine ⟨g ∘ chartAt ℂ x, ?_, heq'⟩
    exact
    { meromorphicAt := hf.congr heq'
      neg_le_meromorphicOrderAt := by rwa [← meromorphicOrderAt_congr heq']
      contMDiffAt := fun _ ↦ hc
      apply_eq_zero := fun h ↦ False.elim (not_lt_of_ge hD h) }


omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Normalized divisor representatives with the same punctured germ have the same full germ. -/
theorem IsDivisorSectionAt.eventuallyEq_of_nhdsNE {g : X → ℂ}
    (hf : IsDivisorSectionAt D f x) (hg : IsDivisorSectionAt D g x)
    (hfg : f =ᶠ[𝓝[≠] x] g) : f =ᶠ[𝓝 x] g := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg
  rcases lt_or_ge 0 (D x) with hD | hD
  · rw [hf.apply_eq_zero hD, hg.apply_eq_zero hD]
  · have := (tendsto_chartAt_symm_nhdsNE (H := ℂ) x).neBot
    exact tendsto_nhds_unique_of_eventuallyEq
      ((hf.contMDiffAt hD).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hg.contMDiffAt hD).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hfg

end LocalSections

namespace divisorSections

variable {D : WeilDivisor X} {U : Opens X} {x : X}

/-- The meromorphic coordinate germ of a divisor section at a point in its domain. Values
assigned at a pole are discarded, as required for the native meromorphic germ field. -/
def toChartGerm (D : WeilDivisor X) (U : Opens X) (x : U) :
    divisorSections D U →ₗ[ℂ] meromorphicGerms ℂ (chartAt ℂ x.1 x.1) where
  toFun f := meromorphicGerms.mk
    ((Subtype.val.extend f.1 0) ∘ (chartAt ℂ x.1).symm)
    ((meromorphicAt_def _ _).1 (isDivisorSectionAt_extend f.2 x).meromorphicAt)
  map_add' f g := by
    apply Subtype.ext
    rw [meromorphicGerms.coe_mk, Subring.coe_add, meromorphicGerms.coe_mk,
      meromorphicGerms.coe_mk, ← Germ.coe_add]
    apply Germ.coe_eq.2
    have he := Function.extend_add Subtype.val f.1 g.1 (0 : X → ℂ) (0 : X → ℂ)
    simp only [add_zero] at he
    rw [Submodule.coe_add, he]
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  map_smul' c f := by
    apply Subtype.ext
    rw [meromorphicGerms.coe_mk, meromorphicGerms.coe_smul,
      meromorphicGerms.coe_mk, ← Germ.coe_smul]
    apply Germ.coe_eq.2
    have he := Function.extend_smul c Subtype.val f.1 (0 : X → ℂ)
    simp only [smul_zero] at he
    rw [Submodule.coe_smul, he, RingHom.id_apply]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The coordinate germ is represented by the extension of the section in the preferred chart. -/
@[simp]
theorem coe_toChartGerm (f : divisorSections D U) (x : U) :
    (toChartGerm D U x f : Germ (𝓝[≠] (chartAt ℂ x.1 x.1)) ℂ) =
      (Subtype.val.extend f.1 (0 : X → ℂ) ∘ (chartAt ℂ x.1).symm) := by
  simp only [toChartGerm, LinearMap.coe_mk, AddHom.coe_mk, meromorphicGerms.coe_mk]

/-- The coordinate germ has the meromorphic order of its normalized section representative. -/
theorem order_toChartGerm (f : divisorSections D U) (x : U) :
    meromorphicGerms.order (toChartGerm D U x f) =
      meromorphicOrderAt (Subtype.val.extend f.1 (0 : X → ℂ)) x.1 := by
  simp only [toChartGerm, LinearMap.coe_mk, AddHom.coe_mk, meromorphicGerms.order_mk,
    meromorphicOrderAt_def]

/-- The coordinate germ satisfies the divisor's prescribed order bound. -/
theorem toChartGerm_mem_orderGE (f : divisorSections D U) (x : U) :
    toChartGerm D U x f ∈ meromorphicGerms.orderGE (chartAt ℂ x.1 x.1) (-D x.1) := by
  rw [meromorphicGerms.mem_orderGE, toChartGerm, LinearMap.coe_mk, AddHom.coe_mk,
    meromorphicGerms.order_mk]
  simpa only [meromorphicOrderAt_def] using
    (isDivisorSectionAt_extend f.2 x).neg_le_meromorphicOrderAt

/-- Restricting a section does not change its meromorphic coordinate germ. -/
theorem toChartGerm_restrict {V : Opens X} (h : V ≤ U) (hx : x ∈ V)
    (f : divisorSections D U) :
    toChartGerm D V ⟨x, hx⟩
      ⟨f.1 ∘ Opens.inclusion h, comp_inclusion_mem_divisorSections h f.2⟩ =
        toChartGerm D U ⟨x, h hx⟩ f := by
  apply Subtype.ext
  simp only [toChartGerm, LinearMap.coe_mk, AddHom.coe_mk, meromorphicGerms.coe_mk]
  apply Germ.coe_eq.2
  filter_upwards [(tendsto_chartAt_symm_nhdsNE x).eventually
    (eventually_nhdsWithin_of_eventually_nhds (V.isOpen.mem_nhds hx))] with z hz
  exact (Subtype.val_injective.extend_apply (f.1 ∘ Opens.inclusion h)
    (0 : X → ℂ) ⟨_, hz⟩).trans
      (Subtype.val_injective.extend_apply f.1 (0 : X → ℂ) ⟨_, h hz⟩).symm

/-- Divisor inclusions preserve meromorphic coordinate germs despite the change in normalized
values at newly permitted poles. -/
theorem toChartGerm_mapOfLE {A : WeilDivisor X} (h : D ≤ A)
    (f : (divisorSheaf D).obj.obj (op U)) (x : U) :
    toChartGerm A U x (divisorSheafSectionsEquiv A U
      ((divisorSheafMapOfLE h).hom.app (op U) f)) =
      toChartGerm D U x (divisorSheafSectionsEquiv D U f) := by
  have := ChartedSpace.t1Space ℂ X
  apply Subtype.ext
  simp only [toChartGerm, LinearMap.coe_mk, AddHom.coe_mk, meromorphicGerms.coe_mk]
  apply Germ.coe_eq.2
  filter_upwards [(tendsto_chartAt_symm_nhdsNE x.1).eventually
      (nhdsWithin_le_nhds (U.isOpen.mem_nhds x.2)),
    (tendsto_chartAt_symm_nhdsNE x.1).eventually (A.eventually_eq_zero_nhdsNE x.1)]
    with z hzU hzA
  simp only [Function.comp_apply]
  calc
    Subtype.val.extend (divisorSheafSectionsEquiv A U
        ((divisorSheafMapOfLE h).hom.app (op U) f)).1 0 ((chartAt ℂ x.1).symm z) =
        (divisorSheafSectionsEquiv A U
          ((divisorSheafMapOfLE h).hom.app (op U) f)).1 ⟨_, hzU⟩ :=
      Subtype.val_injective.extend_apply
        (divisorSheafSectionsEquiv A U ((divisorSheafMapOfLE h).hom.app (op U) f)).1
        (0 : X → ℂ) (⟨_, hzU⟩ : U)
    _ = (divisorSheafSectionsEquiv D U f).1 ⟨_, hzU⟩ := by
      rw [divisorSheafMapOfLE_app]
      exact Set.indicator_of_mem (s := {y : U | A y ≤ 0}) hzA.le _
    _ = Subtype.val.extend (divisorSheafSectionsEquiv D U f).1 0
        ((chartAt ℂ x.1).symm z) :=
      (Subtype.val_injective.extend_apply (divisorSheafSectionsEquiv D U f).1
        (0 : X → ℂ) (⟨_, hzU⟩ : U)).symm



end divisorSections

section Representation

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Every coordinate meromorphic germ with the prescribed order is represented by an actual
local section of the divisor sheaf. -/
theorem exists_section_toChartGerm_eq (D : WeilDivisor X) (x : X)
    (φ : meromorphicGerms ℂ (chartAt ℂ x x))
    (hφ : φ ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-D x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (f : divisorSections D U),
      divisorSections.toChartGerm D U ⟨x, hx⟩ f = φ := by
  obtain ⟨f, hf, rfl⟩ := meromorphicGerms.exists_mk φ
  let F : X → ℂ := f ∘ chartAt ℂ x
  have hchart : F ∘ (chartAt ℂ x).symm =ᶠ[𝓝[≠] (chartAt ℂ x x)] f := by
    filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))] with z hz
    simp only [F, Function.comp_apply, (chartAt ℂ x).right_inv hz]
  have hF : MeromorphicAt F x := (meromorphicAt_def _ _).2 (hf.congr hchart.symm)
  have hord : ((-D x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F x := by
    rw [meromorphicOrderAt_def, _root_.meromorphicOrderAt_congr hchart]
    simpa only [meromorphicGerms.mem_orderGE, meromorphicGerms.order_mk] using hφ
  obtain ⟨g, hg, hFg⟩ := exists_isDivisorSectionAt hF hord
  obtain ⟨v, hv, hvo, hxv⟩ := eventually_nhds_iff.1 hg.eventually
  let U : Opens X := ⟨v, hvo⟩
  let s : divisorSections D U :=
    ⟨g ∘ Subtype.val, comp_val_mem_divisorSections fun z hz ↦ hv z hz⟩
  refine ⟨U, hxv, s, ?_⟩
  apply Subtype.ext
  refine (divisorSections.coe_toChartGerm s ⟨x, hxv⟩).trans ?_
  rw [meromorphicGerms.coe_mk]
  apply Germ.coe_eq.2
  have he : Subtype.val.extend s.1 (0 : X → ℂ) =ᶠ[𝓝 x] g := by
    filter_upwards [U.isOpen.mem_nhds hxv] with y hy
    exact Subtype.val_injective.extend_apply (g ∘ Subtype.val) (0 : X → ℂ) (⟨y, hy⟩ : U)
  exact ((he.filter_mono nhdsWithin_le_nhds).comp_tendsto
    (tendsto_chartAt_symm_nhdsNE x)).trans
      ((hFg.symm.comp_tendsto (tendsto_chartAt_symm_nhdsNE x)).trans hchart)


end Representation

end TauCeti.RiemannSurface
