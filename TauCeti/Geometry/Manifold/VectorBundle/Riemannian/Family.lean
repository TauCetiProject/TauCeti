/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smooth metric families on time sets

`TauCeti.IsSmoothMetricFamilyOn g s` expresses joint smoothness in time and space of a family
of native smooth Riemannian metrics. Its coefficient field takes values in the tangent
bilinear-form bundle, and is smooth within `s × M`. In particular, this condition is stronger
than smoothness of each individual metric. The time set may be an interval, including its
endpoints, without choosing an extension of the family as part of the data.

The API supplies restriction, equality on the time set, smooth changes of time, and positive
time-dependent rescaling using `Bundle.ContMDiffRiemannianMetric.rescale`. Pairing the metric with
smooth tangent fields gives a jointly smooth scalar function.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A family of native smooth Riemannian metrics is smooth on a time set if its coefficient
field is jointly smooth in time and space within that set. No condition is imposed on the
family outside the time set. -/
def IsSmoothMetricFamilyOn
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (s : Set ℝ) : Prop :=
  ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      q.2 ((g q.1).inner q.2)) (s ×ˢ univ)

variable {g h : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
  {s r : Set ℝ}

/-- The characteristic criterion for joint smoothness of a metric family on a time set. -/
theorem isSmoothMetricFamilyOn_iff :
    IsSmoothMetricFamilyOn g s ↔
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          q.2 ((g q.1).inner q.2)) (s ×ˢ univ) :=
  Iff.rfl

namespace IsSmoothMetricFamilyOn

/-- The coefficient field of a smooth metric family is jointly smooth on its time set. -/
theorem contMDiffOn (hg : IsSmoothMetricFamilyOn g s) :
    ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        q.2 ((g q.1).inner q.2)) (s ×ˢ univ) :=
  isSmoothMetricFamilyOn_iff.mp hg

/-- Restricting the time set preserves joint smoothness. -/
theorem mono (hg : IsSmoothMetricFamilyOn g s) (hrs : r ⊆ s) :
    IsSmoothMetricFamilyOn g r :=
  isSmoothMetricFamilyOn_iff.mpr (hg.contMDiffOn.mono (prod_mono_left hrs))

/-- A family agreeing with a smooth family on the time set is smooth there, regardless of its
values outside that set. -/
theorem congr (hg : IsSmoothMetricFamilyOn g s) (heq : EqOn h g s) :
    IsSmoothMetricFamilyOn h s := by
  apply isSmoothMetricFamilyOn_iff.mpr
  exact hg.contMDiffOn.congr fun q hq ↦ by rw [heq hq.1]

/-- Smooth reparametrization preserves smooth metric families when it maps the new time set
into the original one. -/
theorem comp (hg : IsSmoothMetricFamilyOn g s) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c r) (hcs : MapsTo c r s) :
    IsSmoothMetricFamilyOn (g ∘ c) r := by
  apply isSmoothMetricFamilyOn_iff.mpr
  exact hg.contMDiffOn.comp
    ((hc.contMDiffOn.comp (contMDiffOn_fst (s := r ×ˢ (univ : Set M)))
      (fun _ hq ↦ hq.1)).prodMk contMDiffOn_snd)
    (fun _ hq ↦ ⟨hcs hq.1, mem_univ _⟩)

/-- A smooth change of time restricts a family to the preimage of its time set. -/
theorem comp_preimage (hg : IsSmoothMetricFamilyOn g s) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) : IsSmoothMetricFamilyOn (g ∘ c) (c ⁻¹' s) :=
  hg.comp hc.contDiffOn (fun _ ht ↦ ht)

/-- Translating time preserves joint smoothness on the translated time set. -/
theorem translate (hg : IsSmoothMetricFamilyOn g s) (a : ℝ) :
    IsSmoothMetricFamilyOn (fun t ↦ g (t + a)) ((fun t : ℝ ↦ t + a) ⁻¹' s) :=
  hg.comp_preimage (contDiff_id.add contDiff_const)

/-- Pairing a smooth metric family with two jointly smooth tangent fields gives a jointly
smooth real-valued function. -/
theorem inner (hg : IsSmoothMetricFamilyOn g s)
    {v w : (q : ℝ × M) → TangentSpace I q.2}
    (hv : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q ↦ TotalSpace.mk' E q.2 (v q)) (s ×ˢ univ))
    (hw : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q ↦ TotalSpace.mk' E q.2 (w q)) (s ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun q ↦ (g q.1).inner q.2 (v q) (w q)) (s ×ˢ univ) := by
  intro q hq
  exact (contMDiffWithinAt_totalSpace_iff.mp
    ((hg.contMDiffOn q hq).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
      (hv q hq) (hw q hq))).2

/-- At a fixed spatial point, pairing with fixed tangent vectors is smooth in time within
the time set. This lets time derivatives be taken without choosing local coordinates. -/
theorem contDiffOn_inner (hg : IsSmoothMetricFamilyOn g s) (x : M)
    (v w : TangentSpace I x) :
    ContDiffOn ℝ ∞ (fun t ↦ (g t).inner x v w) s := by
  have hcoeff := hg.contMDiffOn.comp
    (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
    (fun _ ht ↦ ⟨ht, mem_univ x⟩)
  intro t ht
  exact (contMDiffWithinAt_totalSpace_iff.mp
    ((hcoeff t ht).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
      (contMDiffWithinAt_const (c := TotalSpace.mk' E x v))
      (contMDiffWithinAt_const (c := TotalSpace.mk' E x w)))).2.contDiffWithinAt

/-- Multiplying a metric family by a positive scalar depending smoothly on time preserves
joint smoothness. Positivity is global because each value is a native metric on all of `M`;
regularity of the scalar is required only on the time set. -/
theorem rescale (hg : IsSmoothMetricFamilyOn g s) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a s) (hapos : ∀ t, 0 < a t) :
    IsSmoothMetricFamilyOn
      (fun t ↦ (g t).rescale (fun _ ↦ a t) contMDiff_const (fun _ ↦ hapos t)) s := by
  apply isSmoothMetricFamilyOn_iff.mpr
  have hscaled := (ha.contMDiffOn.comp
    (contMDiffOn_fst (s := s ×ˢ (univ : Set M))) (fun _ hq ↦ hq.1)).smul_totalSpace
    hg.contMDiffOn
  apply hscaled.congr
  intro q _
  congr 1
  ext v w
  simp

end IsSmoothMetricFamilyOn

/-- Joint smoothness depends only on the metrics at times in the time set. -/
theorem isSmoothMetricFamilyOn_congr (heq : EqOn g h s) :
    IsSmoothMetricFamilyOn g s ↔ IsSmoothMetricFamilyOn h s :=
  ⟨fun hg ↦ hg.congr heq.symm, fun hh ↦ hh.congr heq⟩

/-- Every constant family of smooth metrics is jointly smooth on every time set. -/
theorem isSmoothMetricFamilyOn_const
    (g₀ : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) (s : Set ℝ) :
    IsSmoothMetricFamilyOn (fun _ ↦ g₀) s :=
  isSmoothMetricFamilyOn_iff.mpr (g₀.contMDiff.comp contMDiff_snd).contMDiffOn

end TauCeti
