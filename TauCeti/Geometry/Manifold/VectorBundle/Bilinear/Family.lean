/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.Parametric

/-!
# Families of fields of bilinear forms on the tangent bundle

This file collects regularity results for a one-parameter family `b_s` of fields of bilinear forms
on `TM`, jointly `C^n` in `(s, x)` as a map into the bundle of bilinear forms on `TM`. No metric,
symmetry or nondegeneracy is assumed.

## Main results

* `TauCeti.Manifold.contMDiffAt_uncurry_apply_apply`: pairing two `C^n` vector fields with a jointly
  `C^n` family of fields of bilinear forms gives a jointly `C^n` family of functions.
* `TauCeti.Manifold.differentiableAt_apply_apply_of_contMDiffAt`: the parameter curves at `x` of a
  jointly `C¹` family are differentiable.
* `TauCeti.Manifold.hasDerivAt_mvfderiv_apply_apply`: for a jointly `C²` family, the parameter
  derivative commutes with the differential of the pairing with two vector fields.
* `TauCeti.Manifold.contMDiffAt_of_hasDerivAt_family`: the parameter derivative of a jointly `C^n`
  family of fields of bilinear forms is a `C^m` field for `m + 1 ≤ n`.
* `TauCeti.Manifold.mdifferentiableAt_apply_apply_of_hasDerivAt_family`: the parameter derivative
  of a jointly `C²` family pairs differentiable vector fields to a differentiable function.
-/

public section

noncomputable section

open Bundle FiberBundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {h : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {t : ℝ} {x : M}

variable [IsManifold I ∞ M]

/-- Pairing two `C^n` vector fields with a jointly `C^n` family of fields of bilinear forms gives
a jointly `C^n` family of functions. -/
theorem contMDiffAt_uncurry_apply_apply {n : WithTop ℕ∞}
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2)) (t, x))
    {V W : Π x : M, TangentSpace I x} (hV : CMDiffAt n (T% V) x) (hW : CMDiffAt n (T% W) x) :
    ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) n (Function.uncurry fun s y ↦ b s y (V y) (W y)) (t, x) := by
  have hV' : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (V q.2)) (t, x) := hV.comp (t, x) contMDiffAt_snd
  have hW' : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.2)) (t, x) := hW.comp (t, x) contMDiffAt_snd
  have h := ContMDiffAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ) hb hV' hW'
  simpa [Function.uncurry_def] using (contMDiffAt_totalSpace.mp h).2

/-- The parameter curve `s ↦ b s x u w` of a family of fields of bilinear forms, jointly `C¹` at
`(t, x)`, is differentiable at `t`. -/
theorem differentiableAt_apply_apply_of_contMDiffAt {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    (u w : TangentSpace I x) : DifferentiableAt ℝ (fun s ↦ b s x u w) t := by
  have hpair := contMDiffAt_uncurry_apply_apply hb (contMDiffAt_extend I E u)
    (contMDiffAt_extend I E w)
  have hcurve := ((hpair.of_le hn).comp t (contMDiffAt_id.prodMk contMDiffAt_const)
    |>.mdifferentiableAt one_ne_zero).differentiableAt
  simpa [Function.uncurry_def, Function.comp_def] using hcurve

/-- For a family of fields of bilinear forms, jointly `C²` at `(t, x)`, and vector fields `V`, `W`
that are `C²` at `x`, the parameter derivative of the differential at `x` of the pairing
`y ↦ b_s(V, W)` is the differential of the parameter derivative of the pairing. -/
theorem hasDerivAt_mvfderiv_apply_apply
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    {V W : Π x : M, TangentSpace I x} (hV : CMDiffAt 2 (T% V) x) (hW : CMDiffAt 2 (T% W) x)
    (u : TangentSpace I x) :
    HasDerivAt (fun s ↦ mvfderiv I (fun y ↦ b s y (V y) (W y)) x u)
      (mvfderiv I (fun y ↦ deriv (fun s ↦ b s y (V y) (W y)) t) x u) t := by
  refine hasDerivAt_mvfderiv_apply ?_ u
  rw [minSmoothness_of_isRCLikeNormedField]
  exact contMDiffAt_uncurry_apply_apply hb hV hW

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Regularity of the parameter derivative of a family of bilinear forms.** Let `b_s` be a family
of fields of bilinear forms on `TM`, jointly `C^n` in `(s, y)` at `(t, x)`, and let `h` be its
parameter derivative at `s = t` near `x`. Then `h` is a `C^m` field of bilinear forms at `x`
whenever `m + 1 ≤ n`. -/
theorem contMDiffAt_of_hasDerivAt_family {m n : WithTop ℕ∞}
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    (hmn : m + 1 ≤ n) (hh : ∀ᶠ y in 𝓝 x, ∀ v w, HasDerivAt (fun s ↦ b s y v w) (h y v w) t) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (h y)) x := by
  rw [contMDiffAt_hom_bundle] at hb ⊢
  refine ⟨contMDiffAt_id, ?_⟩
  -- `B s y` is `b s y` read in the tangent trivialization at `x`.
  set B : ℝ → M → E →L[ℝ] E →L[ℝ] ℝ := fun s y ↦ ContinuousLinearMap.inCoordinates E
    (TangentSpace I) (E →L[ℝ] ℝ) (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) x y x y (b s y)
  have hreg := contMDiffAt_deriv_of_contMDiffAt_uncurry (F := B) (t := t) (x := x) hb.2 hmn
  refine hreg.congr_of_eventuallyEq ?_
  filter_upwards [hh, (chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy hyx
  have key (φ : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (a c : E) :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) x y x y φ a c =
        φ ((trivializationAt E (TangentSpace I) x).symm y a)
          ((trivializationAt E (TangentSpace I) x).symm y c) := by
    rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ)
      (by simpa using hyx) (by simpa using hyx) (by simp)]
    simp
  -- Each evaluation of `B · y` is a parameter curve of `b` at `y`, with derivative given by `h`.
  have hcurve (a c : E) : HasDerivAt (fun s ↦ B s y a c)
      (h y ((trivializationAt E (TangentSpace I) x).symm y a)
        ((trivializationAt E (TangentSpace I) x).symm y c)) t := by
    simpa only [B, key] using hy _ _
  have hD := (differentiableAt_clm_apply.mpr fun a ↦
    differentiableAt_clm_apply.mpr fun c ↦ (hcurve a c).differentiableAt).hasDerivAt
  ext a c
  rw [key]
  exact (hcurve a c).unique (hasDerivAt_clm_apply₂.mp hD a c)

/-- The parameter derivative `h` of a family of fields of bilinear forms, jointly `C²` at `(t, x)`,
pairs vector fields differentiable at `x` to a function differentiable at `x`. -/
theorem mdifferentiableAt_apply_apply_of_hasDerivAt_family
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    (hh : ∀ᶠ y in 𝓝 x, ∀ v w, HasDerivAt (fun s ↦ b s y v w) (h y v w) t)
    {V W : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    MDiffAt (fun y ↦ h y (V y) (W y)) x := by
  have hreg := (contMDiffAt_of_hasDerivAt_family (m := 1) hb (by norm_num) hh).mdifferentiableAt
    one_ne_zero
  simpa [mdifferentiableAt_section] using hreg.clm_bundle_apply₂ hV hW

end FiniteDimensional

end TauCeti.Manifold
