/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
public import TauCeti.Topology.PathSpace.Prepend
import TauCeti.Geometry.Manifold.ContMDiff.Curve

/-!
# Collared concatenation of paths

The concatenation `γ₁.trans γ₂` of two paths runs through each of them at double speed, so even
when `γ₁` and `γ₂` are smooth it is in general not smooth where they meet, nor, for loops, where it
closes up. The **collared concatenation** `Path.collaredTrans γ₁ γ₂` reparametrizes it by the map
`Path.collaredTransReparam` of the unit interval: it runs through `γ₁` as `t ↦ γ₁ (β (6 t - 1))` on
`[0, 1/2]` and through `γ₂` as `t ↦ γ₂ (β (6 t - 4))` on `[1/2, 1]`, with
`β = Real.smoothTransition` (`Path.collaredTrans_apply_of_le`, `Path.collaredTrans_apply_of_lt`).
So it rests at its start, at the junction and at its end on the collars `[0, 1/6]`, `[1/3, 2/3]`
and `[5/6, 1]`, and the collared concatenation of two smooth loops based at a point is smooth as a
periodic map. The collared concatenation of two constant paths is constant
(`Path.collaredTrans_refl`). The map `unitInterval.smoothTransition` is `β` as a map into the unit
interval.

Being a reparametrization, the collared concatenation is joined to the concatenation by the
straight-line reparametrization homotopy `Path.reparamHomotopy`, which is continuous on the whole
path space. Its trace at `γ₁.trans γ₂` gives the isomorphism
`Path.collaredTransHom γ₁ γ₂ : γ₁.trans γ₂ ⟶ γ₁.collaredTrans γ₂` in the fundamental groupoid of
the path space, an identity for constant paths (`Path.collaredTransHom_refl`).

## Main definitions

* `unitInterval.smoothTransition`: `Real.smoothTransition` as a map into the unit interval.
* `Path.collaredTransReparam`: the reparametrization of the unit interval.
* `Path.collaredTrans γ₁ γ₂`: the collared concatenation of two paths.
* `Path.collaredTransHom γ₁ γ₂`: the class joining the concatenation to the collared
  concatenation in the fundamental groupoid of the path space.
-/

public section

noncomputable section

open Set CategoryTheory
open scoped Manifold

namespace unitInterval

/-- `Real.smoothTransition` as a map into the unit interval. -/
def smoothTransition (s : ℝ) : I :=
  ⟨Real.smoothTransition s, Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s⟩

@[simp]
theorem coe_smoothTransition (s : ℝ) : (smoothTransition s : ℝ) = Real.smoothTransition s :=
  (rfl)

theorem continuous_smoothTransition : Continuous smoothTransition :=
  Real.smoothTransition.continuous.subtype_mk _

@[simp]
theorem smoothTransition_zero : smoothTransition 0 = 0 :=
  Subtype.ext Real.smoothTransition.zero

@[simp]
theorem smoothTransition_one : smoothTransition 1 = 1 :=
  Subtype.ext Real.smoothTransition.one

end unitInterval

namespace Path

variable {X : Type*} [TopologicalSpace X] {a b c : X}

/-- The real function underlying `Path.collaredTransReparam`: the curve concatenation
`TauCeti.curveConcat` of `r ↦ β (2 r - 1) / 2` and `r ↦ (1 + β (2 r)) / 2`, where
`β = Real.smoothTransition`. -/
private def collaredTransReparamAux : ℝ → ℝ :=
  TauCeti.curveConcat (fun r ↦ Real.smoothTransition (2 * r - 1) / 2)
    (fun r ↦ (1 + Real.smoothTransition (2 * r)) / 2)

private theorem collaredTransReparamAux_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    collaredTransReparamAux t = Real.smoothTransition (6 * t - 1) / 2 := by
  rw [collaredTransReparamAux, TauCeti.curveConcat_of_le (by linarith), ← mul_assoc]
  norm_num

private theorem collaredTransReparamAux_of_lt {t : ℝ} (ht : 1 / 2 < t) :
    collaredTransReparamAux t = (1 + Real.smoothTransition (6 * t - 4)) / 2 := by
  rw [collaredTransReparamAux, TauCeti.curveConcat_of_lt (by linarith), mul_sub, ← mul_assoc]
  norm_num

private theorem continuous_collaredTransReparamAux : Continuous collaredTransReparamAux :=
  (ContMDiff.curveConcat (I := 𝓘(ℝ, ℝ)) (n := 0) (y := 1 / 2)
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).div_const 2).contMDiff
    ((contDiff_const.add (Real.smoothTransition.contDiff.comp (by fun_prop))).div_const
      2).contMDiff
    (fun r hr ↦ by
      rw [Function.comp_apply, Real.smoothTransition.one_of_one_le (by linarith)])
    (fun r hr ↦ by
      rw [Function.comp_apply, Real.smoothTransition.zero_of_nonpos (by linarith)]
      norm_num)).continuous

private theorem collaredTransReparamAux_mem (t : ℝ) : collaredTransReparamAux t ∈ unitInterval := by
  have h₀ := Real.smoothTransition.nonneg (6 * t - 1)
  have h₁ := Real.smoothTransition.le_one (6 * t - 1)
  have h₂ := Real.smoothTransition.nonneg (6 * t - 4)
  have h₃ := Real.smoothTransition.le_one (6 * t - 4)
  rcases le_or_gt t (1 / 2) with ht | ht
  · rw [collaredTransReparamAux_of_le ht]
    constructor <;> linarith
  · rw [collaredTransReparamAux_of_lt ht]
    constructor <;> linarith

/-- The reparametrization of the unit interval under which the concatenation of two paths becomes
their collared concatenation `Path.collaredTrans`: `t ↦ β (6 t - 1) / 2` on `[0, 1/2]` and
`t ↦ (1 + β (6 t - 4)) / 2` on `(1/2, 1]`, where `β = Real.smoothTransition`. -/
def collaredTransReparam (t : unitInterval) : unitInterval :=
  ⟨collaredTransReparamAux t, collaredTransReparamAux_mem t⟩

private theorem coe_collaredTransReparam (t : unitInterval) :
    (collaredTransReparam t : ℝ) = collaredTransReparamAux t :=
  (rfl)

/-- On `[0, 1/2]` the reparametrization of the collared concatenation is `t ↦ β (6 t - 1) / 2`. -/
theorem coe_collaredTransReparam_of_le {t : unitInterval} (ht : (t : ℝ) ≤ 1 / 2) :
    (collaredTransReparam t : ℝ) = Real.smoothTransition (6 * t - 1) / 2 := by
  rw [coe_collaredTransReparam, collaredTransReparamAux_of_le ht]

/-- On `(1/2, 1]` the reparametrization of the collared concatenation is
`t ↦ (1 + β (6 t - 4)) / 2`. -/
theorem coe_collaredTransReparam_of_lt {t : unitInterval} (ht : 1 / 2 < (t : ℝ)) :
    (collaredTransReparam t : ℝ) = (1 + Real.smoothTransition (6 * t - 4)) / 2 := by
  rw [coe_collaredTransReparam, collaredTransReparamAux_of_lt ht]

/-- The reparametrization of the collared concatenation is continuous. -/
theorem continuous_collaredTransReparam : Continuous collaredTransReparam :=
  (continuous_collaredTransReparamAux.comp continuous_subtype_val).subtype_mk _

/-- The reparametrization of the collared concatenation fixes `0`. -/
@[simp]
theorem collaredTransReparam_zero : collaredTransReparam 0 = 0 :=
  Subtype.ext <| by
    rw [coe_collaredTransReparam, Icc.coe_zero, collaredTransReparamAux_of_le (by norm_num),
      Real.smoothTransition.zero_of_nonpos (by norm_num), zero_div]

/-- The reparametrization of the collared concatenation fixes `1`. -/
@[simp]
theorem collaredTransReparam_one : collaredTransReparam 1 = 1 :=
  Subtype.ext <| by
    rw [coe_collaredTransReparam, Icc.coe_one, collaredTransReparamAux_of_lt (by norm_num),
      Real.smoothTransition.one_of_one_le (by norm_num)]
    norm_num

/-- The **collared concatenation** of two paths: their concatenation `γ₁.trans γ₂`,
reparametrized so that it runs through `γ₁` as `t ↦ γ₁ (β (6 t - 1))` on `[0, 1/2]` and through
`γ₂` as `t ↦ γ₂ (β (6 t - 4))` on `[1/2, 1]`, with `β = Real.smoothTransition`. It rests at its
start, at the junction and at its end on the collars `[0, 1/6]`, `[1/3, 2/3]` and `[5/6, 1]`, so
that the collared concatenation of two smooth loops based at a point is smooth, unlike their
concatenation. It is joined to the concatenation by `Path.collaredTransHom`. -/
@[expose]
def collaredTrans (γ₁ : Path a b) (γ₂ : Path b c) : Path a c :=
  (γ₁.trans γ₂).reparam collaredTransReparam continuous_collaredTransReparam
    collaredTransReparam_zero collaredTransReparam_one

theorem collaredTrans_def (γ₁ : Path a b) (γ₂ : Path b c) :
    γ₁.collaredTrans γ₂ = (γ₁.trans γ₂).reparam collaredTransReparam
      continuous_collaredTransReparam collaredTransReparam_zero collaredTransReparam_one :=
  (rfl)

/-- On `[0, 1/2]` the collared concatenation runs through the first path. -/
theorem collaredTrans_apply_of_le (γ₁ : Path a b) (γ₂ : Path b c) {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 2) :
    γ₁.collaredTrans γ₂ t = γ₁.extend (Real.smoothTransition (6 * t - 1)) := by
  have hβ₀ := Real.smoothTransition.nonneg (6 * (t : ℝ) - 1)
  have hβ₁ := Real.smoothTransition.le_one (6 * (t : ℝ) - 1)
  have hc : (collaredTransReparam t : ℝ) ≤ 1 / 2 := by
    rw [coe_collaredTransReparam, collaredTransReparamAux_of_le ht]
    linarith
  rw [collaredTrans_def, coe_reparam, Function.comp_apply, trans_apply, dite_eq_left hc,
    extend_apply _ ⟨hβ₀, hβ₁⟩]
  congr 1
  ext
  simp only [coe_collaredTransReparam, collaredTransReparamAux_of_le ht]
  ring

/-- On `(1/2, 1]` the collared concatenation runs through the second path. -/
theorem collaredTrans_apply_of_lt (γ₁ : Path a b) (γ₂ : Path b c) {t : unitInterval}
    (ht : 1 / 2 < (t : ℝ)) :
    γ₁.collaredTrans γ₂ t = γ₂.extend (Real.smoothTransition (6 * t - 4)) := by
  have hβ₀ := Real.smoothTransition.nonneg (6 * (t : ℝ) - 4)
  have hβ₁ := Real.smoothTransition.le_one (6 * (t : ℝ) - 4)
  rw [collaredTrans_def, coe_reparam, Function.comp_apply, trans_apply, extend_apply _ ⟨hβ₀, hβ₁⟩]
  split_ifs with h
  · -- While `γ₂` has not started, the concatenation rests at the junction point.
    rw [coe_collaredTransReparam, collaredTransReparamAux_of_lt ht] at h
    have hz : Real.smoothTransition (6 * (t : ℝ) - 4) = 0 := by linarith
    have h₂ : 2 * (collaredTransReparam t : ℝ) = 1 := by
      rw [coe_collaredTransReparam, collaredTransReparamAux_of_lt ht, hz]
      norm_num
    rw [← extend_apply, h₂, extend_one]
    exact ((congrArg γ₂ (Subtype.ext hz : (⟨_, hβ₀, hβ₁⟩ : unitInterval) = 0)).trans
      γ₂.source).symm
  · congr 1
    ext
    simp only [coe_collaredTransReparam, collaredTransReparamAux_of_lt ht]
    ring

/-- The collared concatenation of two constant paths is constant. -/
@[simp]
theorem collaredTrans_refl (a : X) : (refl a).collaredTrans (refl a) = refl a :=
  Path.ext <| funext fun t ↦ by simp [collaredTrans_def]

/-- The class of the straight-line path, in the space of paths from `a` to `c`, from the
concatenation of two paths to their collared concatenation, through the paths
`t ↦ (γ₁.trans γ₂) ((1 - r) t + r f(t))` for the reparametrization `f` of `Path.collaredTrans`. It
is an isomorphism in the fundamental groupoid of the path space. -/
def collaredTransHom (γ₁ : Path a b) (γ₂ : Path b c) :
    (⟨γ₁.trans γ₂⟩ : FundamentalGroupoid (Path a c)) ⟶ ⟨γ₁.collaredTrans γ₂⟩ :=
  Homotopic.Quotient.mk <| (reparamHomotopy collaredTransReparam continuous_collaredTransReparam
    collaredTransReparam_zero collaredTransReparam_one).evalAt (γ₁.trans γ₂)

theorem collaredTransHom_def (γ₁ : Path a b) (γ₂ : Path b c) :
    collaredTransHom γ₁ γ₂ = Homotopic.Quotient.mk ((reparamHomotopy collaredTransReparam
      continuous_collaredTransReparam collaredTransReparam_zero collaredTransReparam_one).evalAt
        (γ₁.trans γ₂)) :=
  (rfl)

/-- For constant paths, the path from the concatenation to the collared concatenation is
constant, so its class is an identity, read along the equality of the two constant paths. -/
theorem collaredTransHom_refl (a : X) :
    collaredTransHom (refl a) (refl a) = eqToHom (by rw [collaredTrans_refl, refl_trans_refl]) := by
  rw [collaredTransHom_def]
  -- Every path in this family is a reparametrization of a constant path, hence constant.
  have h (r : unitInterval) : (reparamHomotopy collaredTransReparam continuous_collaredTransReparam
      collaredTransReparam_zero collaredTransReparam_one).evalAt ((refl a).trans (refl a)) r =
        (refl a).trans (refl a) :=
    Path.ext <| funext fun t ↦ by
      rw [ContinuousMap.Homotopy.evalAt_apply, reparamHomotopy_apply, Homotopy.eval_apply,
        ContinuousMap.Homotopy.curry_apply, ContinuousMap.HomotopyWith.coe_toHomotopy,
        Homotopy.reparam_apply]
      simp only [refl_trans_refl, refl_extend, ContinuousMap.const_apply, refl_apply]
  exact Homotopic.Quotient.mk_eq_eqToHom_of_forall_apply_eq _ h

end Path
