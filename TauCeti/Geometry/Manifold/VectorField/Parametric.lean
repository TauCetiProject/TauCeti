/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic

/-!
# Parameter derivatives of one-parameter families of vector fields

Let `W_s` be a one-parameter family of vector fields on `M` which is jointly `C^n` in `(s, y)` at
`(t, x)`, as a map into the tangent bundle. This file shows that the parameter derivative
`y ↦ ∂ₛ W_s(y)` at `s = t` is read, in the tangent-bundle trivialization at `x`, by the parameter
derivative of the coordinates of `W_s`, and deduces that it is a `C^m` vector field at `x` for
`m + 1 ≤ n`. It also shows that the segment `s ↦ (1 - s) • X₀ + s • X₁` between two `C^n` vector
fields is such a family, jointly `C^n` in `(s, y)`.

## Main results

* `TauCeti.Manifold.eventually_deriv_eq_trivializationAt_symm`: near `x`, the parameter derivative
  of `W_s` is the vector with coordinates the parameter derivative of the coordinates of `W_s`.
* `TauCeti.Manifold.contMDiffAt_deriv_vectorField_of_contMDiffAt`: the parameter derivative of a
  jointly `C^n` family of vector fields is `C^m` for `m + 1 ≤ n`.
* `ContMDiff.one_sub_smul_add_smul_vectorField`: the segment `s ↦ (1 - s) • X₀ + s • X₁` between
  two `C^n` vector fields is jointly `C^n`.
-/

public section

noncomputable section

open Bundle Filter Function
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {W : ℝ → Π y : M, TangentSpace I y} {t : ℝ} {x : M}

/-- Near `x`, the parameter derivative of a family of vector fields which is jointly `C¹` at
`(t, x)` is read, in the trivialization at `x`, by the parameter derivative of its coordinates. -/
theorem eventually_deriv_eq_trivializationAt_symm {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hW : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.1 q.2)) (t, x)) :
    ∀ᶠ y in 𝓝 x, deriv (fun s ↦ W s y) t = (trivializationAt E (TangentSpace I) x).symm y
      (deriv (fun s ↦ (trivializationAt E (TangentSpace I) x ⟨y, W s y⟩).2) t) := by
  set e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hG : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) 1
      (uncurry fun s y ↦ (e (TotalSpace.mk' E y (W s y))).2) (t, x) :=
    (contMDiffAt_totalSpace_iff.mp (hW.of_le hn)).2
  have hG1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hG
  have hcurve : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun s ↦ (e ⟨y, W s y⟩).2) t :=
    ((continuous_const.prodMk continuous_id).continuousAt.eventually hG1).mono fun y hy ↦
      ((hy.comp t (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
        one_ne_zero).differentiableAt
  filter_upwards [hcurve, e.open_baseSet.mem_nhds hx] with y hy hyb
  -- The fibre `T_y M` is read as the model space `E`.
  let L : E →L[ℝ] E := e.symmL ℝ y
  have hd := (L.hasFDerivAt.comp_hasDerivAt t hy.hasDerivAt).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦
      (e.symm_apply_apply_mk hyb (W s y)).symm.trans (e.symmL_apply (R := ℝ) hyb _).symm)
  exact hd.deriv.trans (e.symmL_apply (R := ℝ) hyb _)

/-- **Regularity of the parameter derivative of a family of vector fields.** If a family `W_s` of
vector fields is jointly `C^n` in `(s, y)` at `(t, x)` as a map into the tangent bundle, then its
parameter derivative `y ↦ ∂ₛ W_s(y)` at `s = t` is a `C^m` vector field at `x` whenever
`m + 1 ≤ n`. -/
theorem contMDiffAt_deriv_vectorField_of_contMDiffAt {m n : WithTop ℕ∞}
    (hW : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.1 q.2)) (t, x)) (hmn : m + 1 ≤ n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) m
      (fun y ↦ TotalSpace.mk' E y (deriv (fun s ↦ W s y) t)) x := by
  set e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hG' := contMDiffAt_deriv_of_contMDiffAt_uncurry
    (F := fun s y ↦ (e ⟨y, W s y⟩).2) (contMDiffAt_totalSpace_iff.mp hW).2 hmn
  refine (contMDiffAt_section_iff x).2 (hG'.congr_of_eventuallyEq ?_)
  filter_upwards [eventually_deriv_eq_trivializationAt_symm (le_trans le_add_self hmn) hW,
    e.open_baseSet.mem_nhds hx] with y hy hyb
  rw [hy, e.apply_mk_symm hyb]

end TauCeti.Manifold

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {X₀ X₁ : Π y : M, TangentSpace I y} {n : WithTop ℕ∞}

/-- **The segment between two vector fields is a jointly smooth family.** If `X₀` and `X₁` are
`C^n` vector fields, then `(s, y) ↦ (1 - s) • X₀ y + s • X₁ y` is `C^n` as a map from `ℝ × M` to
the tangent bundle. -/
theorem ContMDiff.one_sub_smul_add_smul_vectorField
    (hX₀ : ContMDiff I I.tangent n (fun y ↦ (⟨y, X₀ y⟩ : TangentBundle I M)))
    (hX₁ : ContMDiff I I.tangent n (fun y ↦ (⟨y, X₁ y⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, (1 - p.1) • X₀ p.2 + p.1 • X₁ p.2⟩ : TangentBundle I M)) := by
  rintro ⟨s, x⟩
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_snd, ?_⟩
  -- In the trivialization at `x`, the coordinates of the segment are the segment of the
  -- coordinates, since the trivialization is linear on the fibres over its base set.
  set e := trivializationAt E (TangentSpace I) x
  have h₀ : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) n (fun p : ℝ × M ↦ (e ⟨p.2, X₀ p.2⟩).2) (s, x) :=
    (contMDiffAt_totalSpace_iff.1 (hX₀ x)).2.comp (f := Prod.snd) (s, x) contMDiffAt_snd
  have h₁ : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) n (fun p : ℝ × M ↦ (e ⟨p.2, X₁ p.2⟩).2) (s, x) :=
    (contMDiffAt_totalSpace_iff.1 (hX₁ x)).2.comp (f := Prod.snd) (s, x) contMDiffAt_snd
  have hc : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) n (fun p : ℝ × M ↦ 1 - p.1) (s, x) :=
    contMDiffAt_const.sub contMDiffAt_fst
  refine ((hc.smul h₀).add (contMDiffAt_fst.smul h₁)).congr_of_eventuallyEq ?_
  filter_upwards [(e.open_baseSet.preimage continuous_snd).mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with p hp
  have hlin := e.linear ℝ hp
  rw [hlin.map_add, hlin.map_smul, hlin.map_smul, Pi.add_apply, Pi.smul_apply', Pi.smul_apply']

end Segment
