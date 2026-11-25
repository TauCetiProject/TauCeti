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
(`Path.collaredTrans_refl`).

Being a reparametrization, the collared concatenation is joined to the concatenation by the
straight-line reparametrization homotopy `Path.reparamHomotopy`, which is continuous on the whole
path space. Its trace at `γ₁.trans γ₂` gives the isomorphism
`Path.collaredTransHom γ₁ γ₂ : γ₁.trans γ₂ ⟶ γ₁.collaredTrans γ₂` in the fundamental groupoid of
the path space, an identity for constant paths (`Path.collaredTransHom_refl`).

## Main definitions

* `Path.transReparam f g`: a reparametrization of the unit interval under which the
  concatenation of two paths runs through them along `Real.smoothTransition ∘ f` and
  `Real.smoothTransition ∘ g`.
* `Path.collaredTransReparam`: the reparametrization of the unit interval.
* `Path.collaredTrans γ₁ γ₂`: the collared concatenation of two paths.
* `Path.collaredTransHom γ₁ γ₂`: the class joining the concatenation to the collared
  concatenation in the fundamental groupoid of the path space.
-/

public section

noncomputable section

open Set CategoryTheory
open scoped Manifold

namespace Path

variable {X : Type*} [TopologicalSpace X] {a b c : X}

/-- The reparametrization of the unit interval that is `t ↦ β (f (3 t)) / 2` on `[0, 1/2]` and
`t ↦ (1 + β (g (3 t - 2))) / 2` on `(1/2, 1]`, where `β = Real.smoothTransition`
(`Path.coe_transReparam_of_le`, `Path.coe_transReparam_of_lt`): the curve concatenation
`TauCeti.curveConcat` of `r ↦ β (f r) / 2` and `r ↦ (1 + β (g r)) / 2`. Under it the
concatenation `γ₁.trans γ₂` of two paths runs through `γ₁` along `β ∘ f` and then through `γ₂`
along `β ∘ g`, each at triple speed. It is continuous and fixes `0` and `1` when `β ∘ f` rests at
`1` from time `1` on, `β ∘ g` rests at `0` up to time `0`, `β (f 0) = 0` and `β (g 1) = 1`
(`Path.continuous_transReparam`, `Path.transReparam_zero`, `Path.transReparam_one`). -/
def transReparam (f g : ℝ → ℝ) (t : unitInterval) : unitInterval :=
  ⟨TauCeti.curveConcat (fun r ↦ Real.smoothTransition (f r) / 2)
    (fun r ↦ (1 + Real.smoothTransition (g r)) / 2) t, by
    rcases le_or_gt (t : ℝ) 2⁻¹ with ht | ht
    · rw [TauCeti.curveConcat_of_le ht]
      have h₀ := Real.smoothTransition.nonneg (f (3 * t))
      have h₁ := Real.smoothTransition.le_one (f (3 * t))
      constructor <;> linarith
    · rw [TauCeti.curveConcat_of_lt ht]
      have h₀ := Real.smoothTransition.nonneg (g (3 * t - 2))
      have h₁ := Real.smoothTransition.le_one (g (3 * t - 2))
      constructor <;> linarith⟩

variable {f g : ℝ → ℝ}

private theorem coe_transReparam (t : unitInterval) :
    (transReparam f g t : ℝ) = TauCeti.curveConcat (fun r ↦ Real.smoothTransition (f r) / 2)
      (fun r ↦ (1 + Real.smoothTransition (g r)) / 2) t :=
  (rfl)

/-- On `[0, 1/2]` the reparametrization `Path.transReparam f g` is `t ↦ β (f (3 t)) / 2`. -/
theorem coe_transReparam_of_le {t : unitInterval} (ht : (t : ℝ) ≤ 1 / 2) :
    (transReparam f g t : ℝ) = Real.smoothTransition (f (3 * t)) / 2 := by
  rw [coe_transReparam, TauCeti.curveConcat_of_le (by linarith)]

/-- On `(1/2, 1]` the reparametrization `Path.transReparam f g` is
`t ↦ (1 + β (g (3 t - 2))) / 2`. -/
theorem coe_transReparam_of_lt {t : unitInterval} (ht : 1 / 2 < (t : ℝ)) :
    (transReparam f g t : ℝ) = (1 + Real.smoothTransition (g (3 * t - 2))) / 2 := by
  rw [coe_transReparam, TauCeti.curveConcat_of_lt (by linarith)]

/-- The reparametrization `Path.transReparam f g` is continuous when `f` and `g` are, `f` is at
least `1` from time `1` on and `g` is at most `0` up to time `0`. -/
theorem continuous_transReparam (hf : Continuous f) (hg : Continuous g)
    (hf₁ : ∀ r, 1 ≤ r → 1 ≤ f r) (hg₀ : ∀ r ≤ 0, g r ≤ 0) : Continuous (transReparam f g) :=
  ((ContMDiff.curveConcat (I := 𝓘(ℝ, ℝ)) (n := 0) (y := 1 / 2)
    (γ₁ := fun r ↦ Real.smoothTransition (f r) / 2)
    (γ₂ := fun r ↦ (1 + Real.smoothTransition (g r)) / 2)
    (contMDiff_zero_iff.2 ((Real.smoothTransition.continuous.comp hf).div_const 2))
    (contMDiff_zero_iff.2
      ((continuous_const.add (Real.smoothTransition.continuous.comp hg)).div_const 2))
    (fun r hr ↦ by rw [Real.smoothTransition.one_of_one_le (hf₁ r hr)])
    (fun r hr ↦ by
      rw [Real.smoothTransition.zero_of_nonpos (hg₀ r hr)]
      norm_num)).continuous.comp continuous_subtypeVal).subtype_mk _

/-- The reparametrization `Path.transReparam f g` fixes `0` when `f 0 ≤ 0`. -/
theorem transReparam_zero (hf : f 0 ≤ 0) : transReparam f g 0 = 0 :=
  Subtype.ext <| by
    rw [coe_transReparam_of_le (by norm_num), Icc.coe_zero, mul_zero,
      Real.smoothTransition.zero_of_nonpos hf, zero_div]

/-- The reparametrization `Path.transReparam f g` fixes `1` when `1 ≤ g 1`. -/
theorem transReparam_one (hg : 1 ≤ g 1) : transReparam f g 1 = 1 :=
  Subtype.ext <| by
    rw [coe_transReparam_of_lt (by norm_num), Icc.coe_one]
    norm_num [Real.smoothTransition.one_of_one_le hg]

/-- The reparametrization of the unit interval under which the concatenation of two paths becomes
their collared concatenation `Path.collaredTrans`: `t ↦ β (6 t - 1) / 2` on `[0, 1/2]` and
`t ↦ (1 + β (6 t - 4)) / 2` on `(1/2, 1]`, where `β = Real.smoothTransition`. It is
`Path.transReparam` for `r ↦ 2 r - 1` and `r ↦ 2 r`. -/
def collaredTransReparam : unitInterval → unitInterval :=
  transReparam (fun r ↦ 2 * r - 1) (fun r ↦ 2 * r)

/-- On `[0, 1/2]` the reparametrization of the collared concatenation is `t ↦ β (6 t - 1) / 2`. -/
theorem coe_collaredTransReparam_of_le {t : unitInterval} (ht : (t : ℝ) ≤ 1 / 2) :
    (collaredTransReparam t : ℝ) = Real.smoothTransition (6 * t - 1) / 2 := by
  rw [collaredTransReparam, coe_transReparam_of_le ht, ← mul_assoc]
  norm_num

/-- On `(1/2, 1]` the reparametrization of the collared concatenation is
`t ↦ (1 + β (6 t - 4)) / 2`. -/
theorem coe_collaredTransReparam_of_lt {t : unitInterval} (ht : 1 / 2 < (t : ℝ)) :
    (collaredTransReparam t : ℝ) = (1 + Real.smoothTransition (6 * t - 4)) / 2 := by
  rw [collaredTransReparam, coe_transReparam_of_lt ht, mul_sub, ← mul_assoc]
  norm_num

/-- The reparametrization of the collared concatenation is continuous. -/
theorem continuous_collaredTransReparam : Continuous collaredTransReparam :=
  continuous_transReparam (by fun_prop) (by fun_prop) (fun _ hr ↦ by linarith)
    fun _ hr ↦ by linarith

/-- The reparametrization of the collared concatenation fixes `0`. -/
@[simp]
theorem collaredTransReparam_zero : collaredTransReparam 0 = 0 :=
  transReparam_zero (by norm_num)

/-- The reparametrization of the collared concatenation fixes `1`. -/
@[simp]
theorem collaredTransReparam_one : collaredTransReparam 1 = 1 :=
  transReparam_one (by norm_num)

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
    rw [coe_collaredTransReparam_of_le ht]
    linarith
  rw [collaredTrans_def, coe_reparam, Function.comp_apply, trans_apply, dite_eq_left hc,
    extend_apply _ ⟨hβ₀, hβ₁⟩]
  congr 1
  ext
  simp only [coe_collaredTransReparam_of_le ht]
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
    rw [coe_collaredTransReparam_of_lt ht] at h
    have hz : Real.smoothTransition (6 * (t : ℝ) - 4) = 0 := by linarith
    have h₂ : 2 * (collaredTransReparam t : ℝ) = 1 := by
      rw [coe_collaredTransReparam_of_lt ht, hz]
      norm_num
    rw [← extend_apply, h₂, extend_one]
    exact ((congrArg γ₂ (Subtype.ext hz : (⟨_, hβ₀, hβ₁⟩ : unitInterval) = 0)).trans
      γ₂.source).symm
  · congr 1
    ext
    simp only [coe_collaredTransReparam_of_lt ht]
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
